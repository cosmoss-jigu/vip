
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/ValueSymbolTable.h"

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <utility>
#include <vector>
#include <unordered_map>
#include <tuple>
#include <string>
#include <cxxabi.h>

//#define CFI
#define MPK
#define SAFESTACK
#define FUNCTION_COALESING

//#define COUNTER

using namespace llvm;

using std::vector;
using std::unordered_map;
using std::string;
using std::tuple;
using std::get;
using std::pair;

StringRef aASSERT8B("sm_assert_8b");
StringRef aREGISTER8B("sm_register_8b");
StringRef aWRITE8B_ONCE8B("sm_write_once_8b");
StringRef aWRITE8B("sm_write_8b");
StringRef aDEREGISTER8B("sm_deregister_8b");
StringRef aDEREGISTER("sm_deregister");
StringRef aLOCK("sm_lock_safe_region");
StringRef aUNLOCK("sm_unlock_safe_region");

unordered_map<string, tuple<vector<vector<int>>, int, bool>> globalStructList;
unordered_map<string, tuple<int, int, int, int>> sm_counter;  // register, write, assert, deregister
unordered_map<Value*, bool> assertedVal;
unordered_map<string, int> functionToKeyLookup;
unordered_map<int, tuple<vector<int>, bool>> sensitiveFunctions; // Key = Function Name; Value = tuple<Sensitive List & isMPKClosed>

// For Safestack
unordered_map<Function*, SmallVector<AllocaInst *, 50>> safestackAllocasList;

// For instrumentation counter
int sm_assert_counter;
int sm_register_counter;
int sm_write_counter;
int sm_deregister_counter;


bool isMPKLocked; 
vector<vector<int>> getProtectList(Type *Ty, vector<int> currTrace = vector<int>());

namespace {	

	int getNextGlobalStructListKey () {
		int lowest = -1;
		for (auto structEntry: globalStructList) {
			int num = get<1>(structEntry.second);
			// Always convert keys to negative
			if (num > 0) {
				num = -1 * num;
			}

			if (num < lowest) {
				lowest = num;
			}
		}
		return lowest - 1;
	}

	int getNextSensitiveFunctionsKey () {
		int lowest = -1;
		for (auto entry: sensitiveFunctions) {
			int num = entry.first;
			// Always convert keys to negative
			if (num > 0) {
				num = -1 * num;
			}

			if (num < lowest) {
				lowest = num;
			}
		}
		return lowest - 1;
	}

	string getStructName (StructType *sty) {
		string structName = sty->getName();

		// if it ends in .# take it out
		int i = structName.size() - 1;
		while (i >= 0 && isdigit(structName[i])) {
			i--;
		}
		if (i >= 0 && structName[i] == '.') {
			structName = structName.substr(0,i);
		}

		return structName;
	}
	
	void fixStructListBasedOnNewEntry (vector<vector<int>> &fixList, int fixListKey, string baseEntryName) {

		// INITIAL PHASE
		// get the base entry
		auto baseEntry = globalStructList.find(baseEntryName); 
		
		// return if doesn't exists 
		if (baseEntry == globalStructList.end()) {
			return;
		}
		
		// get lookupKey (HAVE TO BE negative!!)
		int lookupKey = get<1>(baseEntry->second) * -1;
		// return if it hasn't been observed yet
		if (lookupKey > 0) {
			return;
		}

		// get baseList
		vector<vector<int>> &baseList = get<0>(baseEntry->second);

		// is it definitely not sensitive?
		bool isEmpty = (baseList.size() == 0); 
		
		// is it definitely sensitive?
		bool isSensitive = false;
		bool hasVTPtr = false;
		bool pending = false;
		for (int i = 0; i < baseList.size(); i++) {
			int lastVal = baseList[i][baseList[i].size() - 1];
			// if it contains a call chain that ends on -1, it's definitely sensitive
			if (lastVal == -1) {
				isSensitive = true;
			} else if (lastVal == INT_MIN) {
				hasVTPtr = true;
			} else {
				pending = true;
			}
		}

		// FIXING PHASE
		for (int i = fixList.size() - 1; i >= 0; i--) {
			vector<int> &currChain = fixList[i];
			int lastIndex = currChain.size() - 1;
			int indexBefore = lastIndex - 1;
	
			// find the call chain that ends on this lookup key (dependent pointer & struct vars)
			if (currChain[lastIndex] == lookupKey) {
				if (isEmpty) {
					// DEFINITELY NOT sensitive
					fixList.erase(fixList.begin() + i);
				} else if (isSensitive) {
					// DEFINITELY sensitive
					// first, need to take out the lookup key
					currChain.erase(currChain.begin() + lastIndex);
					// if its just a struct, fixup the struct
					if (indexBefore < 0 || currChain[indexBefore] != -1) {
						for (vector<int> singleChain: baseList) {
							vector<int> tempChain = fixList[i];
							singleChain.insert(singleChain.begin(), tempChain.begin(), tempChain.end());
							fixList.push_back(singleChain);
						}
						// erase the current template list
						fixList.erase(fixList.begin() + i);
					}
				} else {
					if (hasVTPtr && !pending) {
						// only has VTPtrs	
						for (vector<int> singleChain: baseList) {
							vector<int> tempChain = fixList[i];
							singleChain.insert(singleChain.begin(), tempChain.begin(), tempChain.end());
							fixList.push_back(singleChain);
						}
						// erase the current template list
						fixList.erase(fixList.begin() + i);
						
					} else {
						// UNDECIDED!
						if (lookupKey != fixListKey) {
							// if it's NOT a self fix
							if (indexBefore < 0 || currChain[indexBefore] != -1) {
								// if its just a struct. fixup the struct
								currChain.erase(currChain.begin() + lastIndex);
								for (auto singleChain: baseList) {
									vector<int> tempChain = fixList[i];
									singleChain.insert(singleChain.begin(), tempChain.begin(), tempChain.end());
									fixList.push_back(singleChain);
								}
								// erase the current template list
								fixList.erase(fixList.begin() + i);
							}
						} else {
							// if it is a self fix
							// check to see if further dependency exists
							bool hasDependency = false;
							for (auto currChain: fixList) {
								if (currChain[currChain.size() - 1] != fixListKey) {
									hasDependency = true;
									break;
								}
							}
		
							// if no more dependencies exists, remove all self pointers
							if (!hasDependency) {
								fixList.erase(fixList.begin() + i);
							}
						}
					}
				}
			}
		}
		
	}

	// returns a list of indices for drilling down to the sensitive element -1 when found
	vector<vector<int>> getProtectList(Type *Ty, vector<int> currTrace = vector<int>()) {
		vector<vector<int>> result = vector<vector<int>>();
		vector<int> newList = vector<int>();
		
		if (currTrace.empty()) {
			currTrace = newList;
		}

		// function pointer
		if (Ty->isPointerTy() && cast<PointerType>(Ty)->getElementType()->isFunctionTy()) {
			currTrace.push_back(-1);
			result.push_back(currTrace);
			return result;
		} 

#ifdef CFI
		// struct pointer - ONLY FOR CFI
		else if (Ty->isPointerTy() && cast<PointerType>(Ty)->getElementType()->isStructTy()) {
			return vector<vector<int>>();
		}
#endif
		// generic pointer
		else if (PointerType *PTy = dyn_cast<PointerType>(Ty)) {
			// get this pointer's element's result
			Type *elementType = PTy->getElementType();
			vector<vector<int>> thisResult = getProtectList(elementType);

			// Look for -1. if found, mark this pointer sensitive!	
			for (vector<int> callChain : thisResult) {
				int lastIndex = callChain.size() - 1;

				if (callChain[lastIndex] == -1) {
					vector<int> tempTrace = currTrace;
					tempTrace.push_back(-1);
					result.push_back(tempTrace);
					break;
				}
			}
			return result;	
		}

		// Array
		else if (ArrayType *ATy = dyn_cast<ArrayType>(Ty)) {
			vector<vector<int>> thisResult = getProtectList(ATy->getElementType());
			// Add to list
			for (int i = 0; i < ATy->getNumElements(); i++) {
				for (vector<int> callChain : thisResult) {
					vector<int> tempTrace = currTrace;
					tempTrace.push_back(i);
					tempTrace.insert(tempTrace.end(), callChain.begin(), callChain.end());
					result.push_back(tempTrace);
				}
			}
			return result;
		}

		// struct
		else if (StructType *STy = dyn_cast<StructType>(Ty)) {
			if (STy->isOpaque()) {
				return result;
			}

			string structName;
			if (STy->isLiteral()) {
				structName = "Literal_" + std::to_string(STy->getStructNumElements());
			} else {
				structName = STy->getName();
			}
			
			auto entry = globalStructList.find(structName);	

			// Entry Exists in the globalStructList && if it's NOT open for examination
			if (entry != globalStructList.end() && (get<2>(entry->second) == false)) {
				if (get<1>(entry->second) < 0) {
					// observing - attach the negative Key at the end of CurrTrace and return result
					currTrace.push_back(get<1>(entry->second));
					result.push_back(currTrace);
				} else {
					// sensitive/not sensitive/undecided - For each CallChain, build onto CurrTrace and return result
					vector<vector<int>> structResult = get<0>(entry->second);
					for (int i = 0; i < structResult.size(); i++) {
						structResult[i].insert(structResult[i].begin(), currTrace.begin(), currTrace.end());
						result.push_back(structResult[i]);
					}
				}
				
				return result;
			}
			
			// Entry DOES NOT Exists in the globalStructList
			// Create new Entry if entry does not exists
			if (entry == globalStructList.end()) {
				globalStructList[structName] = make_tuple(vector<vector<int>>(), getNextGlobalStructListKey(), false);
			}
			
			tuple<vector<vector<int>>, int, bool> &currTuple = globalStructList[structName];
			int lookupKey = get<1>(currTuple);
			get<2>(currTuple) = false; // this entry is no longer open for examption
	
			// Collect results for all of its elements
			for (unsigned i = 0; i < STy->getNumElements(); ++i) {
				vector<int> tempTrace = currTrace;

				Type *ElTy = STy->getElementType(i);
				vector<vector<int>> thisResult = getProtectList(ElTy);

				for (auto &callChain: thisResult) {
					callChain.insert(callChain.begin(), i);
				}

				// Mark C++'s VTPtrs differently
				if (structName.rfind("class.", 0) == 0) {
					for (vector<vector<int>>::iterator lists_it = thisResult.begin(); lists_it != thisResult.end(); ++lists_it) {
						bool firstIdx = true;
						for (vector<int>::iterator list_it = (*lists_it).begin(); list_it != (*lists_it).end(); ++list_it) {
							if (firstIdx) {
								firstIdx = false;
								if ((*list_it) != 0) {
									break;
								}
							} else if ((*list_it) == 0) {
								continue;
							} else if ((*list_it) == -1) {
								*list_it = INT_MIN;
							} else {
								break;
							}
						}
					}
				}

				// update current contents inside of result before inserting thisResult using up-to-date globalStructList
				for (auto structEntry: globalStructList) {
					// if the structEntry is still observing, skip it
					if (get<1>(structEntry.second) < 0) {
						continue;
					}
					fixStructListBasedOnNewEntry(result, lookupKey, structEntry.first);
				}
				result.insert(result.end(), thisResult.begin(), thisResult.end());
			}

			// Update this Enry from Global Struct List
			get<1>(currTuple) = lookupKey * -1; // make the key positive
			get<0>(currTuple) = result;

			// FIX SELF
			fixStructListBasedOnNewEntry(get<0>(currTuple), lookupKey, structName);
			
			// update non-observing structs inside of globalStructLists
			for (auto &structEntry: globalStructList) {
				// if the structEntry is still observing, skip it
				if (get<1>(structEntry.second) < 0) {
					continue;
				}

				fixStructListBasedOnNewEntry(get<0>(structEntry.second), -1 * get<1>(structEntry.second), structName);
			}	

			return get<0>(currTuple);
		}

		// OTHERWISE UNKNOWN
		return vector<vector<int>>();
	}
	
	void printCallChain (vector<int> callChain) {
		for (vector<int>::iterator list_it = callChain.begin(); list_it != callChain.end(); ++list_it) {
			outs() << " " << *list_it;
		}
		outs() << "\n";
	}

	void printProtectLists (vector<vector<int>> lists) {
		for (vector<vector<int>>::iterator lists_it = lists.begin(); lists_it != lists.end(); ++lists_it) {
			printCallChain(*lists_it);
		}
	}	

	bool isSensitive (Type *type) {
		vector<vector<int>> pLists = getProtectList(type);
		for (vector<vector<int>>::iterator lists_it = pLists.begin(); lists_it != pLists.end(); ++lists_it) {
			if ((*lists_it).size() == 1) {
				return true;
			}
		}
		return false;
	}


	// From Safe Stack ------
	class AllocaOffsetRewriter : public SCEVRewriteVisitor<AllocaOffsetRewriter> {
		const Value *AllocaPtr;
	public:
  		AllocaOffsetRewriter(ScalarEvolution &SE, const Value *AllocaPtr)
			: SCEVRewriteVisitor(SE), AllocaPtr(AllocaPtr) {}

		const SCEV *visitUnknown(const SCEVUnknown *Expr) {
			if (Expr->getValue() == AllocaPtr)
				return SE.getZero(Expr->getType());
			return Expr;
		}
	};

	class SafeStack {
		Function &F;
		const DataLayout &DL;
		ScalarEvolution &SE;

  		// Calculate the allocation size of a given alloca. Returns 0 if the
  		// size can not be statically determined.
  		uint64_t getStaticAllocaAllocationSize(const AllocaInst* AI);
		bool IsSafeStackAlloca(const Value *AllocaPtr, uint64_t AllocaSize);
		bool IsMemIntrinsicSafe(const MemIntrinsic *MI, const Use &U,
                    const Value *AllocaPtr, uint64_t AllocaSize);
		bool IsAccessSafe(Value *Addr, uint64_t Size, const Value *AllocaPtr,
                    uint64_t AllocaSize);

	public:
		SafeStack(Function &F, const DataLayout &DL,
            ScalarEvolution &SE) : F(F), DL(DL), SE(SE) {}
		
		void findInsts(Function &F, 
				 SmallVectorImpl<AllocaInst *> &SafeStackAllocas);
	};

	uint64_t SafeStack::getStaticAllocaAllocationSize(const AllocaInst* AI) {
		uint64_t Size = DL.getTypeAllocSize(AI->getAllocatedType());
		if (AI->isArrayAllocation()) {
			auto C = dyn_cast<ConstantInt>(AI->getArraySize());
			if (!C)
				return 0;
			Size *= C->getZExtValue();
		}
		return Size;
	}

	bool SafeStack::IsAccessSafe(Value *Addr, uint64_t AccessSize,
    		const Value *AllocaPtr, uint64_t AllocaSize) {
		AllocaOffsetRewriter Rewriter(SE, AllocaPtr);
		const SCEV *Expr = Rewriter.visit(SE.getSCEV(Addr));
		uint64_t BitWidth = SE.getTypeSizeInBits(Expr->getType());
		ConstantRange AccessStartRange = SE.getUnsignedRange(Expr);
		ConstantRange SizeRange =
      		ConstantRange(APInt(BitWidth, 0), APInt(BitWidth, AccessSize));
		ConstantRange AccessRange = AccessStartRange.add(SizeRange);
		ConstantRange AllocaRange =
			ConstantRange(APInt(BitWidth, 0), APInt(BitWidth, AllocaSize));
		bool Safe = AllocaRange.contains(AccessRange);

		return Safe;
	}

	bool SafeStack::IsMemIntrinsicSafe(const MemIntrinsic *MI, const Use &U,	
			const Value *AllocaPtr, uint64_t AllocaSize) {
		if (auto MTI = dyn_cast<MemTransferInst>(MI)) {
			if (MTI->getRawSource() != U && MTI->getRawDest() != U)
				return true;
		} else {
			if (MI->getRawDest() != U)
      			return true;
  		}

  		const auto *Len = dyn_cast<ConstantInt>(MI->getLength());
  		if (!Len) {
			return false;
		}
  		return IsAccessSafe(U, Len->getZExtValue(), AllocaPtr, AllocaSize);
	}
	
	bool SafeStack::IsSafeStackAlloca(const Value *AllocaPtr, uint64_t AllocaSize) {
		SmallPtrSet<const Value *, 16> Visited;
		SmallVector<const Value *, 8> WorkList;
		WorkList.push_back(AllocaPtr);

		// A DFS search through all uses of the alloca in bitcasts/PHI/GEPs/etc.
		while (!WorkList.empty()) {
			const Value *V = WorkList.pop_back_val();
			for (const Use &UI : V->uses()) {
				auto I = cast<const Instruction>(UI.getUser());
				assert(V == UI.get());

				switch (I->getOpcode()) {
					case Instruction::Load:
						if (!IsAccessSafe(UI, DL.getTypeStoreSize(I->getType()), AllocaPtr, AllocaSize))
							return false;
					break;
					case Instruction::VAArg:
						// "va-arg" from a pointer is safe.
					break;
					case Instruction::Store:
						if (V == I->getOperand(0)) {
							return false;
						}

						if (!IsAccessSafe(UI, DL.getTypeStoreSize(I->getOperand(0)->getType()), AllocaPtr, AllocaSize))
							return false;
					break;

					case Instruction::Ret:
						// Information leak.
						return false;
					case Instruction::Call:
					case Instruction::Invoke: {
						ImmutableCallSite CS(I);
						if (I->isLifetimeStartOrEnd())
							continue;
						if (const MemIntrinsic *MI = dyn_cast<MemIntrinsic>(I)) {
							if (!IsMemIntrinsicSafe(MI, UI, AllocaPtr, AllocaSize)) {
								return false;
							}
							continue;
						}
						ImmutableCallSite::arg_iterator B = CS.arg_begin(), E = CS.arg_end();
						for (ImmutableCallSite::arg_iterator A = B; A != E; ++A)
							if (A->get() == V)
								if (!(CS.doesNotCapture(A - B) && (CS.doesNotAccessMemory(A - B) ||
												   CS.doesNotAccessMemory()))) {
									return false;
								}
						continue;
					}

					default:
						if (Visited.insert(I).second)
							WorkList.push_back(cast<const Instruction>(I));
				}
			}
		}

		// All uses of the alloca are safe, we can place it on the safe stack.
		return true;
	}

	void SafeStack::findInsts(Function &F,
						SmallVectorImpl<AllocaInst *> &SafeStackAllocas) {
		for (Instruction &I : instructions(&F)) {
			if (auto AI = dyn_cast<AllocaInst>(&I)) {
				uint64_t Size = getStaticAllocaAllocationSize(AI);
				if (IsSafeStackAlloca(AI, Size)) {
					SafeStackAllocas.push_back(AI);
					continue;
				}
			}
		}
	}
	
	struct OTWMAnnotate : public ModulePass {
		static char ID; // Pass identification, replacement for typeid
		OTWMAnnotate() : ModulePass(ID) {
			initializeOTWMAnnotatePass(*PassRegistry::getPassRegistry());
		}

		void getAnalysisUsage(AnalysisUsage &AU) const override {
			AU.addRequired<TargetLibraryInfoWrapperPass>();
			AU.addRequired<AssumptionCacheTracker>();
		}	

		vector<int> combine(vector<int> a, vector<int> b) {
			if (a.size() > b.size()) {
				a.insert(a.end(), b.begin(), b.end());
				return a;
			} else {
				b.insert(b.end(), a.begin(), a.end());
				return b;
			}
		}	

		void printStructEntry (string structName, tuple<vector<vector<int>>, int, bool> entry) {
			outs() << "struct Name: " << structName << "\n";
			outs() << "  list: <";
			vector<vector<int>> &list = get<0>(entry);
			int i = 0;
			while (i < list.size()) {
				int j = 0;
				outs() << "<";
				while (j < list[i].size()) {
					outs() << list[i][j];
					if (j < list[i].size() - 1) {
						outs() << " ";
					}
					j++;
				}
				outs() << ">";
				if (i < list.size() - 1) {
					outs() << " ";
				}
				i++;
			}
			outs() << ">  |  key: " << get<1>(entry) << "  |  isTemporary: ";
			if (get<2>(entry)) {
				outs() << "true\n";
			} else {
				outs() << "false\n";
			}

		}

		void printSensitiveFunctionEntry (StringRef func_name, tuple<vector<int>,bool> &entry, int key) {
			outs() << "Function Name: " << func_name << "\n";
			outs() << " list: <";
			vector<int> list = get<0>(entry);
			int i = 0;
			while (i < list.size()) {
				outs() << list[i];

				if (i < list.size() - 1) {
					outs() << ", ";
				}
				i++;
			}
			outs() << ">  |  key: " << key << " | instrumented: ";
			if (get<1>(entry)) 
				outs() << "true\n";
			else 
				outs() << "false\n";
		}

		void printGlobalStructList () {
			outs() << "\nGLOBAL STRUCT LIST:\n";
			for(auto structEntry : globalStructList) {
				printStructEntry(structEntry.first, structEntry.second);
			}
			outs() << "\n";
		}

		void printSensitiveFunctionsList () {
			outs() << "\nSENSITIVE FUNCTIONS LIST:\n";
			for (auto keyEntry: functionToKeyLookup) {
				printSensitiveFunctionEntry(keyEntry.first, sensitiveFunctions[keyEntry.second], keyEntry.second);
			}
			outs() << "\n";
		}	

		int getEntryLookupKey (string baseEntryName) {
			// get the base entry
			auto baseEntry = globalStructList.find(baseEntryName); 
			
			// return if doesn't exists
			if (baseEntry == globalStructList.end()) {
				outs() << "ERROR: entry not found. NEVER SHOULD COME IN HERE!\n";
				return -999;
			} else {
				int lookupNum = get<1>(baseEntry->second);
				if (lookupNum > 0) {
					lookupNum = -1 * lookupNum;
				}
				return lookupNum;
			}
		}

		void insertMallocx (Instruction *vf_call, Instruction *insert_point) {
			//https://nxmnpg.lemoda.net/3/mallocx
			//Probably to do with arena preference
			int flag_val = 5243136; // 0x500100 == 0b 0101-0000 0000-0001 0000-0000
			LLVMContext &ctx = insert_point->getFunction()->getContext();
			Value *currOperand = vf_call->getOperand(0);
			Type *currType = const_cast<Type*> (currOperand->getType());
			ConstantInt *const_int = ConstantInt::get(ctx, llvm::APInt(32, flag_val, false));
				
			ArrayRef<Type*> params = { 
				currType,
				const_int->getType()
			};
			
			PointerType *returnType	= Type::getInt8PtrTy (ctx);
			FunctionType *func_type = FunctionType::get(returnType, params, false);
			FunctionCallee mallocx = insert_point->getModule()->getOrInsertFunction("mallocx", func_type);
			
			ArrayRef<Value*> args = {
				currOperand,
				(Value *) const_int
			};
			
			CallInst *oldInst = dyn_cast<CallInst>(vf_call);
			BasicBlock::iterator ii(oldInst);
			ReplaceInstWithInst(oldInst, CallInst::Create(mallocx, args, vf_call->getName()));
		}

		int insert8BLibCall (Value *sm_arg_val, Instruction *curr_inst, StringRef function_name) {
			Type *currType = const_cast<Type*> (sm_arg_val->getType());

			LLVMContext &ctx = curr_inst->getFunction()->getContext();
			IRBuilder<> builder(ctx);

			//By defaut insert point is instruction BEFORE target instruction
			builder.SetInsertPoint(curr_inst);

			ArrayRef<Type*> params = {
				currType->getPointerTo()
			};
			Type *result = Type::getVoidTy(ctx);
			FunctionType *func_type = FunctionType::get(result, params, false);

			FunctionCallee sm_func = curr_inst->getModule()->getOrInsertFunction(function_name, func_type);
			ArrayRef<Value*> args = {
				builder.CreatePointerCast(sm_arg_val, currType->getPointerTo())
			};
			builder.CreateCall(sm_func, args);

			if (!function_name.equals("sm_assert_8b")) {
				isMPKLocked = false;
			}

			return 0;
		}

		int insertLibCall (Value *sm_arg_val, Instruction *curr_inst, StringRef function_name, Value *size) {
		
			Type *currType = const_cast<Type*> (sm_arg_val->getType());

			LLVMContext &ctx = curr_inst->getFunction()->getContext();
			IRBuilder<> builder(ctx);

			//By defaut insert point is instruction BEFORE target instruction
			builder.SetInsertPoint(curr_inst);

			ArrayRef<Type*> params = {
				currType->getPointerTo(),
				size->getType()
			};
			Type *result = Type::getVoidTy(ctx);
			FunctionType *func_type = FunctionType::get(result, params, false);

			FunctionCallee sm_func = curr_inst->getModule()->getOrInsertFunction(function_name, func_type);
			ArrayRef<Value*> args = {
				builder.CreatePointerCast(sm_arg_val, currType->getPointerTo()),
				size
			};
			builder.CreateCall(sm_func, args);

			if (!function_name.equals("sm_assert_8b")) {
				isMPKLocked = false;
			}

			return 0;
		}

		void insertMPKCall (Instruction *insert_point, StringRef function_name) {
#ifndef MPK
			return;
#endif	
			LLVMContext &ctx = insert_point->getFunction()->getContext();
			IRBuilder<> builder(ctx);

			builder.SetInsertPoint(insert_point);
			FunctionType *func_type = FunctionType::get(Type::getVoidTy(ctx), false);
			FunctionCallee mpk_func = insert_point->getModule()->getOrInsertFunction(function_name, func_type);
			builder.CreateCall(mpk_func);
		}

		Value* insertGEP (Instruction *insert_point, int idx, Type *type, Value *value) {
			
			LLVMContext &ctx = insert_point->getFunction()->getContext();
			IRBuilder<> builder(ctx);
			builder.SetInsertPoint(insert_point);
			
			vector<Value*> indices(2);
			indices[0] = ConstantInt::get(ctx, llvm::APInt(32, 0, true));
			indices[1] = ConstantInt::get(ctx, APInt(32, idx, true));

			return builder.CreateInBoundsGEP(type, value, indices, "memberptr");
		}

		Value* insertArrayGEP (Instruction *insert_point, int idx, Type *type, Value *value) {

			LLVMContext &ctx = insert_point->getFunction()->getContext();
			IRBuilder<> builder(ctx);
			builder.SetInsertPoint(insert_point);
			
			Value *idx_val = ConstantInt::get(ctx, APInt(64, idx, true));
			
			return builder.CreateInBoundsGEP(type, value, idx_val, "arrayidx");
		}

		Value* insertBitcast (Instruction *insert_point, Value *val, Type* destType) {
			LLVMContext &ctx = insert_point->getFunction()->getContext();
			IRBuilder<> builder(ctx);
			builder.SetInsertPoint(insert_point);
			return builder.CreateBitCast(val, destType);
		}	

		vector<int> getIndicesFromGetElementPtr (GetElementPtrInst *gep_inst) {
			vector<int> result;

			for (auto it = gep_inst->idx_begin(); it != gep_inst->idx_end(); ++it) {
				Constant *c = dyn_cast<Constant>(*it);
				if (c == nullptr) {
					return vector<int>();
				}
				ConstantInt *ci = dyn_cast<ConstantInt>(c);
				int i = ci->getValue().roundToDouble();
				result.push_back(i);
			}

			return result;
		}

		bool isSensitiveElement (Type *inspectType, int idx) {

				if (StructType *STy = dyn_cast<StructType>(inspectType)) {
				Type *ElTy = STy->getElementType(idx);
				vector<vector<int>> pList = getProtectList(ElTy);
				
				for (auto lists_it = pList.begin(); lists_it != pList.end(); ++lists_it) {
					if ((*lists_it).size() == 1) {
						return true;
					}
				}
			} else if (ArrayType *ATy = dyn_cast<ArrayType>(inspectType)) {
				Type *ElTy = ATy->getElementType();
				vector<vector<int>> pList = getProtectList(ElTy);
			
				for (auto lists_it = pList.begin(); lists_it != pList.end(); ++lists_it) {
					if ((*lists_it).size() == 1) {
						return true;
					}
				}
			}
			return false;
		}
		
		Value *getLoadVal (Instruction *insert_point, Value *val) {
			LLVMContext &ctx = insert_point->getFunction()->getContext();
			IRBuilder<> builder(ctx);
			builder.SetInsertPoint(insert_point);
			return builder.CreateLoad(val, "gep_load");
		}

		Value *insertBitCast (Instruction *insert_point, Value *val, Type *toType) {
			LLVMContext &ctx = insert_point->getFunction()->getContext();
			IRBuilder<> builder(ctx);
			builder.SetInsertPoint(insert_point);
			return builder.CreateBitCast(val, toType, "bitcast_inst");
		}

		bool checkRecursiveDeregister (Instruction *insert_point) {
			CallInst *ci = dyn_cast<CallInst>(insert_point);
			Value *protectVal = ci->getArgOperand(0);
			Type *actualTy = getOperandsActualType(protectVal);
			
			if (Instruction *I = dyn_cast<Instruction>(protectVal)) {
				if (BitCastInst *bci = dyn_cast<BitCastInst>(I)) {
					if (Instruction *tempI = dyn_cast<LoadInst>(bci->getOperand(0))) {
						if (dyn_cast<LoadInst>(bci->getOperand(0))) {
							protectVal = I->getOperand(0);
						}
					} else {
						return false;
					}
				}
			}
			
			if (PointerType *pt = dyn_cast<PointerType>(actualTy)) {
				Type *protectType = pt->getElementType();
				vector<vector<int>> protectList = getProtectList(protectType);
				if (protectList.size() > 0) {
					return true;
				}
			}
			return false;
		}

		void recursiveDeregister (Instruction *insert_point) {
			CallInst *ci = dyn_cast<CallInst>(insert_point);
			Value *protectVal = ci->getArgOperand(0);
			Type *actualTy = getOperandsActualType(protectVal);
			
			if (Instruction *I = dyn_cast<Instruction>(protectVal)) {
				if (BitCastInst *bci = dyn_cast<BitCastInst>(I)) {
					if (Instruction *tempI = dyn_cast<LoadInst>(bci->getOperand(0))) {
						if (dyn_cast<LoadInst>(bci->getOperand(0))) {
							protectVal = I->getOperand(0);
						}
					} else {
						return;
					}
				}
			}
			
			if (PointerType *pt = dyn_cast<PointerType>(actualTy)) {
				Type *protectType = pt->getElementType();
				vector<vector<int>> protectList = getProtectList(protectType);
				recursiveInsertions (insert_point, protectVal, protectType, protectList, aDEREGISTER8B);
			}
		}

		void incrementCounters(StringRef s) {
			if (s == aREGISTER8B) {
				sm_register_counter++;
			} else if (s == aWRITE8B) {
				sm_write_counter++;
			} else if (s == aASSERT8B) {
				sm_assert_counter++;
			} else if (s == aDEREGISTER8B) {
				sm_deregister_counter++;
			}
		}

		void recursiveInsertions (Instruction *insert_point, Value *original_val, Type *original_ty, vector<vector<int>> pList, StringRef libcall) {
			for (vector<vector<int>>::iterator lists_it = pList.begin(); lists_it != pList.end(); ++lists_it) {
				Value *val = original_val;
				Type *ty = original_ty;
				for(vector<int>::iterator list_it = (*lists_it).begin(); list_it != (*lists_it).end(); ++list_it) {
					StructType *sty = dyn_cast<StructType>(ty);
					ArrayType *aty = dyn_cast<ArrayType>(ty);

					if (*list_it == -1 || *list_it == INT_MIN) {
						insert8BLibCall(val, insert_point, libcall);
						incrementCounters(libcall);
					} else {
						if (!sty && !aty) {
							while (dyn_cast<PointerType>(val->getType()) && dyn_cast<PointerType>(ty)) {
								val = getLoadVal(insert_point, val);
								ty = dyn_cast<PointerType>(ty)->getElementType();
							}

							if (dyn_cast<PointerType>(val->getType())) {
								sty = dyn_cast<StructType>(ty);
								aty = dyn_cast<ArrayType>(ty);
							}
						}
							
						if (sty && sty->isOpaque()) {
							insert8BLibCall(val, insert_point, libcall);
							incrementCounters(libcall);
						} if (sty) {
							val = insertGEP(insert_point, *list_it, sty, val);
							ty = sty->getStructElementType(*list_it);
						} else if (aty) {
							val = insertGEP (insert_point, *list_it, aty, val);
							ty = aty->getElementType();
							
							if (dyn_cast<PointerType>(val->getType())->getElementType() != ty) {
								val = insertBitCast(insert_point, val, ty->getPointerTo());
							}
						} else {
							return;
						}
					}
				}
			}
		}

		bool checkSensitiveFunctionCall (Instruction *I) {

			Instruction *insert_point = I;
			CallInst *ci = dyn_cast<CallInst>(I);

			// check to see if current call is sensitive 
			Value *protectVal; 
			Type *inspectType;

			LoadInst*load_inst;
			if (insert_point->getPrevNode() && dyn_cast<LoadInst>(insert_point->getPrevNode())) {
				load_inst = dyn_cast<LoadInst>(insert_point->getPrevNode());
				protectVal = load_inst->getPointerOperand();
				inspectType = protectVal->getType();
			} else {
				return false;
			}

			// Checking for function ptr call. they usaully needs to load the function first
			if (!isSensitive(inspectType)) {
				return false;
			}

			return true;
		}

		void assertSensitiveFunctionCall (Instruction *I) {
			Value *protectVal;
			Instruction *insert_point = I;
			CallInst *ci = dyn_cast<CallInst>(I);
			Instruction *inst;
			Instruction *calledValue = dyn_cast<Instruction>(ci->getCalledValue());
			// protect the function ptr
			if (LoadInst *li = dyn_cast<LoadInst>(calledValue)) {
				protectVal = li->getPointerOperand();
				if (protectVal->getName().startswith("vfn")) {		
					return;
				}
				// check for vtble
				auto find_it = assertedVal.find(protectVal);
				if (find_it == assertedVal.end()) {	
					// insert assert
					insert8BLibCall(protectVal, insert_point, aASSERT8B);
					incrementCounters(aASSERT8B);
					assertedVal[protectVal] = true;
				}
			} else {
				return;
			}

#ifndef CFI
			inst = dyn_cast<Instruction>(protectVal);
			
			while (inst) {
				if (BitCastInst *bci = dyn_cast<BitCastInst>(inst)) {
					inst = dyn_cast<Instruction>(inst->getOperand(0));
				} else if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(inst)) {
					inst = dyn_cast<Instruction>(gepi->getPointerOperand());
				} else if (LoadInst *li = dyn_cast<LoadInst>(inst)) {
					protectVal = li->getPointerOperand();
					if (protectVal->getName().startswith("vfn")) {		
						return;
					}
					// check for vtble
					if (isSensitive(protectVal->getType())) {
						// avoid redundant check
						auto find_it = assertedVal.find(protectVal);
						if (find_it == assertedVal.end()) {
							// insert assert
							insert8BLibCall(protectVal, inst->getNextNode(), aASSERT8B);
							incrementCounters(aASSERT8B);
							assertedVal[protectVal] = true;
						}
					}
					inst = dyn_cast<Instruction>(inst->getOperand(0));			
				} else if (AllocaInst *ai = dyn_cast<AllocaInst>(inst)) {
					inst = NULL;
				} else {
					inst = NULL;
				}
			}
#endif
		}

		Instruction* findValueAssignmentInstruction (Value *v, Instruction *i) {
			Instruction *curr = i->getPrevNode();
			while (curr != nullptr) {
				Value *curr_val = curr;
				if (v == curr_val) {
					return curr;
				}
				curr = curr->getPrevNode();
			}
			return nullptr;
		}

		Type *getOperandsActualType (Value *v) {
			Type *result_ty = v->getType();
			if (Instruction *i = dyn_cast<Instruction>(v)) {
				if (BitCastInst *bci = dyn_cast<BitCastInst>(i)) {
					Instruction *temp_i = dyn_cast<Instruction>(i->getOperand(0));
					if (!temp_i) {
						return i->getOperand(0)->getType();
					}
					if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(temp_i)) {
						// check source elementType to see if it's struct or array
						Type *src_element_ty = gepi->getSourceElementType();
						if (dyn_cast<StructType>(src_element_ty)) {
							result_ty = gepi->getType();
						} else if (dyn_cast<ArrayType>(src_element_ty)) {
							result_ty = gepi->getPointerOperandType();
						} else {
							result_ty = src_element_ty;
						}
					} else if (LoadInst *li = dyn_cast<LoadInst>(temp_i)) {
						result_ty = li->getType();
					} else if (AllocaInst *ai = dyn_cast<AllocaInst>(temp_i)) {
						result_ty = ai->getType();
					}
				} else if (LoadInst *li = dyn_cast<LoadInst>(i)) {
					result_ty = li->getType();
				} else {
					result_ty = v->getType();
				}
			} else {
				if (Constant *C = dyn_cast<Constant>(v)) {
					if (ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
						if (CE->isCast()) {
							for (auto oi = CE->op_begin(); oi != CE->op_end(); ++oi) {
								result_ty = (*oi)->getType();
								break;
							}
						}
					}
				}
			}
			return result_ty;
		}

		Value *getOperandsActualValue (Value *v) {
			Value *result_val = nullptr;
			if (Instruction *i = dyn_cast<Instruction>(v)) {
				if (BitCastInst *bci = dyn_cast<BitCastInst>(i)) {
					Instruction *temp_i = dyn_cast<Instruction>(i->getOperand(0));
					if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(temp_i)) {
						// check source elementType to see if it's struct or array
						Type *src_element_ty = gepi->getSourceElementType();
						if (dyn_cast<StructType>(src_element_ty)) {
							result_val = gepi;
						} else if (dyn_cast<ArrayType>(src_element_ty)) {
							result_val = gepi->getPointerOperand();
						} else {
							outs() << "UNRECOGNIZED SOURCE ELEMENT TYPE!\n";
						}
					} else if (LoadInst *li = dyn_cast<LoadInst>(temp_i)) {
						result_val = li->getPointerOperand();
					} else if (AllocaInst *ai = dyn_cast<AllocaInst>(temp_i)) {
						result_val = ai;
					}
				} else if (LoadInst *li = dyn_cast<LoadInst>(i)) {
					result_val = li->getPointerOperand();
				} else {
					outs() << "UNRECOGNIZED INSTRUCTION!!\n";
				}
			}

			return result_val;
		}

		bool checkMemcpyInst (Instruction *memcpyInst, SmallVectorImpl<AllocaInst *> &SafeStackAllocas) {

			// Source vals
			Value *src = memcpyInst->getOperand(1);
			Type *realSrcPtrType = getOperandsActualType(src);
			Type *realSrcType;
			Value *dst = memcpyInst->getOperand(0);

			Instruction *dst_inst = dyn_cast<Instruction>(dst);
			if (dst_inst && isOriginInSafeStack (dst_inst, SafeStackAllocas)) {
				return false;
			}

			if (PointerType *pt = dyn_cast<PointerType>(realSrcPtrType)) {
				realSrcType = pt->getElementType();
			} else {
				return false;
			}

			vector<vector<int>> protectList = getProtectList(realSrcType);
			if (protectList.size() == 0) {
				return false;
			}
			return true;
		}

		void protectMemcpyInst (Instruction *memcpyInst, SmallVectorImpl<AllocaInst *> &SafeStackAllocas) {
			Instruction *insert_point = memcpyInst->getNextNode();
			Value *src = memcpyInst->getOperand(1);
			Value *dst = memcpyInst->getOperand(0);

			Instruction *dst_inst = dyn_cast<Instruction>(dst);
			if (dst_inst && isOriginInSafeStack (dst_inst, SafeStackAllocas)) {
				return;
			}

			// Source vals	
			Type *realSrcPtrType = getOperandsActualType(src);
			Type *realSrcType;
			if (PointerType *pt = dyn_cast<PointerType>(realSrcPtrType)) {
				realSrcType = pt->getElementType();
			} else {
				return;
			}

			// Destination vals	
			Type *realDstPtrType = getOperandsActualType(dst);
			Type *realDstType;
			if (PointerType *pt = dyn_cast<PointerType>(realDstPtrType)) {
				realDstType = dyn_cast<PointerType>(realDstPtrType)->getElementType();
			} else {
				return;
			}

			// Check to see if we need to protect this type
			vector<vector<int>> protectList = getProtectList(realSrcType);
			if (protectList.size() == 0) {
				return;
			}

			// Inserts a bitcast, (if needed insert registers), write everything
			Value *v = insertBitCast(insert_point, dst, realSrcPtrType);
			BitCastInst *bci = dyn_cast<BitCastInst>(memcpyInst->getNextNode());

			if (realSrcType != realDstType && bci) {
				//outs() << "types does not match\n";
				// insert bitcast first, so that everything will be properly registered	
				registerBitCastedVal(bci);
			}

			Value *protectVal;
			Type *protectType;
			
			if (bci) {
				protectVal = bci;
				protectType = bci->getDestTy();
			} else {
				protectVal = v;
				protectType = v->getType();
			}


			PointerType *ptrTy = dyn_cast<PointerType>(protectType);
			protectType = ptrTy->getElementType();
				
			recursiveInsertions(insert_point, protectVal, protectType, protectList, aWRITE8B);
			
			return;
		}

		bool checkMunmapInst (Instruction *munmapInst) {
			Instruction *insert_point = munmapInst;	

			Type *realOperandPtrType = getOperandsActualType(munmapInst->getOperand(0));
			if (realOperandPtrType == nullptr)
				return false;

			if (isSensitive(realOperandPtrType)) {
				return true;
			}
		}

		void protectMunmapInst (Instruction *munmapInst) {
			Instruction *insert_point = munmapInst;	

			Type *realOperandPtrType = getOperandsActualType(munmapInst->getOperand(0));
			if (realOperandPtrType == nullptr)
				return;
			Type *realOperandType = dyn_cast<PointerType>(realOperandPtrType)->getElementType();
			
			if (isSensitive(realOperandPtrType)) {
				Value *protectVal = getOperandsActualValue(munmapInst->getOperand(0));
				insertLibCall(protectVal, insert_point, aDEREGISTER, munmapInst->getOperand(1));
				incrementCounters(aDEREGISTER8B);
			}
		}

		 bool checkBitCastedVal (BitCastInst *bci) {
			Value *val = bci;
			Type *ty = bci->getDestTy();

			Instruction *insert_point = bci->getNextNode();	
			// if it is pointer of a sensitive structure, protect the inners
			if (PointerType *PTy = dyn_cast<PointerType>(ty)) {
				Type *pointed_type = PTy->getElementType();
				if (dyn_cast<StructType>(pointed_type) || dyn_cast<ArrayType>(pointed_type)) {
					// get the protectList
					vector<vector<int>> protectList = getProtectList(pointed_type);
					StructType *sty = dyn_cast<StructType>(pointed_type);
					if (protectList.size() == 0 || (sty && sty->isOpaque())) {
						return false;
					}
					
					if (sty) {
						if (PointerType *src_PTy = dyn_cast<PointerType>(bci->getSrcTy())) {
							Type *src_pointed_type = src_PTy->getElementType();
							if(StructType *src_element_struct = dyn_cast<StructType>(src_PTy->getElementType())) {
								for (unsigned i = 0; i < src_element_struct->getNumElements(); ++i) {
									Type *elementTy = src_element_struct->getElementType(i);
									StructType *elementSTy = dyn_cast<StructType>(elementTy);
									
									if (!elementSTy || elementSTy->isLiteral()) {
										continue;
									}

									// detect downcast in CPP
									if (elementSTy->getStructName().equals(sty->getStructName()) || (elementSTy->getStructName().startswith(sty->getStructName()) && elementSTy->getStructName().endswith(".base"))) {
										return 0;
									}
								}
							}
						}
					}

					return true;
				}
			}

			return false;
		}

		
		void registerBitCastedVal (BitCastInst *bci) {	
			Value *val = bci;
			Type *ty = bci->getDestTy();

			Instruction *insert_point = bci->getNextNode();	
			// if it is pointer of a sensitive structure, protect the inners
			if (PointerType *PTy = dyn_cast<PointerType>(ty)) {
				Type *pointed_type = PTy->getElementType();
				if (dyn_cast<StructType>(pointed_type) || dyn_cast<ArrayType>(pointed_type)) {
					// get the protectList
					vector<vector<int>> dest_protectList = getProtectList(pointed_type);
					StructType *sty = dyn_cast<StructType>(pointed_type);
					if (dest_protectList.size() == 0 || (sty && sty->isOpaque())) {
						return;
					}
					// Check to see if it's a downcast
					if (sty) {
						if (PointerType *src_PTy = dyn_cast<PointerType>(bci->getSrcTy())) {
							Type *src_pointed_type = src_PTy->getElementType();
							if (StructType *src_element_struct = dyn_cast<StructType>(src_PTy->getElementType())) {
								for (unsigned i = 0; i < src_element_struct->getNumElements(); ++i) {
									Type *elementTy = src_element_struct->getElementType(i);
									StructType *elementSTy = dyn_cast<StructType>(elementTy);

									if (!elementSTy || elementSTy->isLiteral()) {
										continue;
									}

									// detect downcast in CPP
									if (sty->hasName() && (elementSTy->getStructName().equals(sty->getStructName()) || (elementSTy->getStructName().startswith(sty->getStructName()) && elementSTy->getStructName().endswith(".base")))) {
										return;
									}
								}
							}
						}
					}
					
					// getting type size
					DataLayout dl = DataLayout(insert_point->getModule());
					int pointed_type_size = dl.getTypeAllocSize(pointed_type);
					int arraySize = 1;
					Value *src_val = bci->getOperand(0);
					if (Instruction *src_inst = dyn_cast<Instruction>(src_val)) {
						if (CallInst *src_ci = dyn_cast<CallInst>(src_inst)) {
							Function *fp = src_ci->getCalledFunction();
							// For Malloc
							if (fp && isMallocFunction(fp->getName())) {
								// get allocated size
								unsigned alloc_size = getIntValue(src_ci->getArgOperand(0));

								// array size
								arraySize = alloc_size / pointed_type_size;
							}
							// For Calloc
							else if (fp && isCallocFunction(fp->getName())) {
								
								// get allocated size
								unsigned count_size = getIntValue(src_ci->getArgOperand(0)); 
								unsigned obj_size = getIntValue(src_ci->getArgOperand(1));	
								unsigned alloc_size = count_size * obj_size;

								// array size
								arraySize = alloc_size / pointed_type_size;
							} 
							// For Mmap
							else if (fp && isMmapFunction(fp->getName())) {
								// get allocated size
								unsigned alloc_size = getIntValue(src_ci->getArgOperand(1));
								
								// array size
								arraySize = alloc_size / pointed_type_size;
							} else {
							}
						}
					}

					for (int x = 0; x < arraySize; x++) {
						// insert GEP
						Value *gepVal = insertArrayGEP(insert_point, x, pointed_type, val);
						// insert protection
						recursiveInsertions(insert_point, gepVal, pointed_type, dest_protectList, aREGISTER8B);
					}
						
					return;
				} else {
					if (isSensitive(pointed_type)) {
						insert8BLibCall(val,insert_point, aWRITE8B);
						incrementCounters(aWRITE8B);
					}
				}
			}
			return;
		}

		unsigned getIntValue(Value *v) {
			ConstantInt *ci = dyn_cast<ConstantInt>(v);
			while (!dyn_cast<ConstantInt>(v)) {
				if (SExtInst *sei = dyn_cast<SExtInst>(v)) {
					v = sei->getOperand(0);
				} else if (LoadInst *li = dyn_cast<LoadInst>(v)) {
					v = li->getOperand(0);
				} else {
					outs() << "don't know what the number is!\n";
					return 0;
				}
			}
			return ci->getZExtValue();
		}

		bool isVTablePointer (Value *v) {
			// Check if it's a pointer
			if (!isa<PointerType>(v->getType())) {
				return false;
			}

			// Check the contents of the pointer
			v = v->stripPointerCasts();

			if (ConstantExpr *CE = dyn_cast<ConstantExpr>(v)) {
				if (!isa<GEPOperator>(CE)) {
					return false;
				}
				for (auto OI=CE->op_begin(); OI != CE->op_end(); ++OI) {
					if ((*OI)->hasName()) {
						string demangledName = demangle((*OI)->getName().str().c_str());

						if (isVTable(StringRef(demangledName))) {
							return true;
						}
					}
				}
			}

			return false;	
		}
		

		inline string demangle(const char* name) {
				int status = -1; 
			std::unique_ptr<char, void(*)(void*)> res { abi::__cxa_demangle(name, NULL, NULL, &status), std::free };
			return (status == 0) ? res.get() : string(name);
		}
		
		Value* getOriginVal(Instruction *I) {
			Instruction *curr_inst = I;
			while (curr_inst) {
				if (BitCastInst *bci = dyn_cast<BitCastInst>(curr_inst)) {
					curr_inst = dyn_cast<Instruction>(curr_inst->getOperand(0));
				} else if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(curr_inst)) {
					curr_inst = dyn_cast<Instruction>(curr_inst->getOperand(0));
				} else if (LoadInst *li = dyn_cast<LoadInst>(curr_inst)) {
					// exit condition
					if (!dyn_cast<Instruction>(curr_inst->getOperand(0))) {
						return curr_inst->getOperand(0);
					}
					curr_inst = dyn_cast<Instruction>(curr_inst->getOperand(0));			
				} else if (AllocaInst *ai = dyn_cast<AllocaInst>(curr_inst)) {
					return curr_inst;
				} else {
					return curr_inst;
				}
			}

			return curr_inst;
		}

		bool isOriginInSafeStack (Instruction *I, SmallVectorImpl<AllocaInst *> &SafeStackAllocas) {
			Value *val = getOriginVal(I);
			if (val) {
				if (AllocaInst *AI = dyn_cast<AllocaInst>(val)) {
					for (auto &ai : SafeStackAllocas) {
						if (ai == val) {
							return true;
						}
					} 
				} else if (isa<PHINode>(val) || isa<LandingPadInst>(val)) {
					return true;
				} else if (CallInst *CI = dyn_cast<CallInst>(val)) {
					return true;
				}
				else {
				}
			}
			return false;
		}

		Type* isBitcastIntoSensitiveType(Value *v, Instruction *ignore_Inst) {
			for (const Use &UI : v->uses()) {
				auto I = cast<Instruction>(UI.getUser());
				if (!I || I == ignore_Inst)	{
					continue;
				}
				if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)) {
					Type *destTy = BCI->getDestTy();
					vector<vector<int>> protectList = getProtectList(destTy);
					if (protectList.size() > 0) {
						return destTy;
					}
				} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
					if (SI->getValueOperand()) {
						for (const Use &UI : SI->getValueOperand()->uses()) {
							auto I = dyn_cast<Instruction>(UI.getUser());
							if (!I)	{
								continue;
							}
							if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)) {
								Type *destTy = BCI->getDestTy();
								vector<vector<int>> protectList = getProtectList(destTy);
								if (protectList.size() > 0) {
									return destTy;
								}
							}
						}
					}
				} else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
					if (dyn_cast<Value>(LI)) {
						for (const Use &UI : dyn_cast<Value>(LI)->uses()) {
							auto I = cast<Instruction>(UI.getUser());
							if (!I)	{
								continue;
							}
							if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)) {
								Type *destTy = BCI->getDestTy();
								vector<vector<int>> protectList = getProtectList(destTy);
								if (protectList.size() > 0) {
									return destTy;
								}
							}
						}
					}
				}
			}

			return nullptr;
		}

		void functionCheck (Function &F, bool isCPP, 
						SmallVectorImpl<AllocaInst *> &SafeStackAllocas,
						tuple<vector<int>,bool> &entry) {
			bool instrumented = false;			
			bool firstInstruction = true;
			bool instrumentGlobals;
			if (isCPP) {
				instrumentGlobals = (F.getName().startswith("_GLOBAL__"))? true : false;
			} else {
				instrumentGlobals = (F.getName().equals("main") || F.getName().equals("toplev_main")) ? true : false;
			}

			// Looks to instrument function calls, returns, and store instruction
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				isMPKLocked = true;

				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt) {	
					Instruction *I = &*BBIt;
					Instruction *nextInst = I->getNextNode();
					
					if (isa<PHINode>(I) || isa<LandingPadInst>(I)) {
						continue;
					}

					// Instrucment registers for all sensitive global variables
					if (instrumentGlobals) {
						if (isCPP) {
							// want to make sure that globals are being written as last instructions in cpp modules
							if (!dyn_cast<ReturnInst>(I)) {
								continue;
							}
						}
						Module *M = BB->getModule();
						for (auto gvarIt = M->global_value_begin(); gvarIt != M->global_value_end(); ++gvarIt) {	
							if (Value *v = dyn_cast<Value>(&*gvarIt)) {
								string demangledName = demangle(v->getName().str().c_str());
								if (isVTable(StringRef(demangledName))) {
									continue;
								}

								if (v->getName().startswith("llvm.")) {
									continue;
								}

								Type *ty = (*gvarIt).getValueType();
								vector<vector<int>> protectList = getProtectList(ty);
								if (protectList.size() == 0) {
									continue;
								}

								instrumented = true;
							}
						}
						instrumentGlobals = false;
					}

					if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {	
						if (!isOriginInSafeStack (I, SafeStackAllocas)) {
							Value *val = &*AI;
							Type *ty = AI->getAllocatedType();
							vector<vector<int>> protectList = getProtectList(ty);

							// Set insertion point
							Instruction *insert_point = I->getNextNode();

							// if its a sensitive type, protect it
							if (protectList.size() > 0) {
								instrumented = true;
							} else {
								// if it is typecasted later to a sensitive variable, protect it
								Type *ty = isBitcastIntoSensitiveType(val, I);	
								if (ty) {
									instrumented = true;
								}
							}
						}
					} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
						Instruction *src_val = dyn_cast<Instruction>(SI->getPointerOperand());
						if (isOriginInSafeStack (src_val, SafeStackAllocas)) {
							continue;
						}

						Type *operandType = SI->getPointerOperandType();

						if (isSensitive (operandType)) {
							instrumented = true;
						}				
					} else if (CallInst *ci = dyn_cast<CallInst>(I)) {
						Function *fp = ci->getCalledFunction();
						Instruction *calledValue = dyn_cast<Instruction>(ci->getCalledValue());
						
						if (fp && isLLVMFunction(fp->getName())) {
							continue;	
						} else if (fp && isMemcpyFunction(fp->getName())) {
							if (checkMemcpyInst (I, SafeStackAllocas)) {
								instrumented = true;
							}
						} else if (fp && isMunmapFunction(fp->getName())) {
							if (checkMunmapInst(I)) {
								instrumented = true;
							}
						} else {	
							if (ci->isIndirectCall ()) {
								addToSensitiveFunctionList(F.getName().str(), "");
								break;
							} else {
								if (ci->isInlineAsm()) {
									continue;
								}

								if (!isFreeFunction(ci->getCalledValue()->stripPointerCasts()->getName())) {
									if (fp && fp->isDeclaration()){
										addToSensitiveFunctionList(F.getName().str(), "");
									}
								}								
							}
						}
					} 
				}	
			}
			get<1>(entry) = instrumented;
		}

		void functionInstrumentation (Function &F, bool isCPP, 
						SmallVectorImpl<AllocaInst *> &SafeStackAllocas) {
			bool firstInstruction = true;
			bool instrumentGlobals;
			if (isCPP) {
				instrumentGlobals = (F.getName().startswith("_GLOBAL__"))? true : false;
			} else {
				instrumentGlobals = (F.getName().equals("main") || F.getName().equals("toplev_main")) ? true : false;
			}

			// Looks to instrument function calls, returns, and store instruction
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				isMPKLocked = true;

				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt) {	
					Instruction *I = &*BBIt;
					Instruction *nextInst = I->getNextNode();
					
					if (isa<PHINode>(I) || isa<LandingPadInst>(I)) {
						continue;
					}

					// Instrucment registers for all sensitive global variables
					if (instrumentGlobals) {
						if (isCPP) {
							// want to make sure that globals are being written as last instructions in cpp modules
							if (!dyn_cast<ReturnInst>(I)) {
								continue;
							}
						}
						Module *M = BB->getModule();
						for (auto gvarIt = M->global_value_begin(); gvarIt != M->global_value_end(); ++gvarIt) {	
							if (Value *v = dyn_cast<Value>(&*gvarIt)) {
								string demangledName = demangle(v->getName().str().c_str());
								if (isVTable(StringRef(demangledName))) {
									continue;
								}

								if (v->getName().startswith("llvm.")) {
									continue;
								}

								Type *ty = (*gvarIt).getValueType();
								vector<vector<int>> protectList = getProtectList(ty);
								if (protectList.size() == 0) {
									continue;
								}

								recursiveInsertions(I, v, ty, protectList, aWRITE8B);
								incrementCounters(aWRITE8B);
							}
						}
						instrumentGlobals = false;
					}

					if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {	
						if (!isOriginInSafeStack (I, SafeStackAllocas)) {
							Value *val = &*AI;
							Type *ty = AI->getAllocatedType();
							vector<vector<int>> protectList = getProtectList(ty);

							// Set insertion point
							Instruction *insert_point = I->getNextNode();

							// if its a sensitive type, protect it
							if (protectList.size() > 0) {	
								recursiveInsertions(insert_point, val, ty, protectList, aREGISTER8B);
							} else {
								// if it is typecasted later to a sensitive variable, protect it
								Type *ty = isBitcastIntoSensitiveType(val, I);	

								if (ty) {
									protectList = getProtectList(ty);
									Value *v = insertBitCast(insert_point, val, ty);
									recursiveInsertions(insert_point, v, ty, protectList, aREGISTER8B);
								}
							}
						}
					} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
						Instruction *src_val = dyn_cast<Instruction>(SI->getPointerOperand());
						if (isOriginInSafeStack (src_val, SafeStackAllocas)) {
							continue;
						}

						Type *operandType = SI->getPointerOperandType();
						Value* stored_val = SI->getOperand(0);

						if (isSensitive (operandType)) {
							// Set insertion point
							Instruction *insert_point = I->getNextNode();
							Value *pointerOperand = SI->getPointerOperand();

							if (isVTablePointer(stored_val)) {
								insert8BLibCall(pointerOperand, insert_point, aWRITE8B);
							} else {
								insert8BLibCall(pointerOperand, insert_point, aWRITE8B);	
							}
							incrementCounters(aWRITE8B);
						}				
					} else if (LoadInst *li = dyn_cast<LoadInst>(I)) {

						Value *protectVal = nullptr;
						Instruction *insertPoint = nullptr;

						// for vtbptrs
						if (li->getName().startswith("vtable")) {
							protectVal = li->getPointerOperand();
							if (Instruction *inst = dyn_cast<Instruction>(protectVal)) {
								insertPoint = inst->getNextNode();
							}
						} 	

						if (protectVal && insertPoint) {
							auto find_it = assertedVal.find(protectVal);
							if (find_it == assertedVal.end()) {	
								insert8BLibCall(protectVal, I, aASSERT8B);
								incrementCounters(aASSERT8B);
								assertedVal[protectVal] = true;
							}
						}
					} else if (CallInst *ci = dyn_cast<CallInst>(I)) {
						Function *fp = ci->getCalledFunction();	

						if (fp && isLLVMFunction(fp->getName())) {
							continue;	
						} else if (fp && isMemcpyFunction(fp->getName())) {
							protectMemcpyInst(I, SafeStackAllocas);	
						} else if (fp && isMunmapFunction(fp->getName())) {
							protectMunmapInst(I);
						} else {
							Value *calledVal = ci->getCalledValue();
							Instruction *loadInst = dyn_cast<Instruction>(calledVal);
							
							bool shouldLock = false;
							if (loadInst) {
								if (!isOriginInSafeStack (loadInst, SafeStackAllocas)) {
									assertSensitiveFunctionCall(I);
								}
								shouldLock = true;
							} else {
								if (ci->isInlineAsm()) {
									continue;
								}
								
								if (isFreeFunction(ci->getCalledValue()->stripPointerCasts()->getName())) {
									continue;
								}

								if (fp && isFunctionSensitive(fp->getName())) {
									shouldLock = true;
								}
							}

							if (shouldLock && !isMPKLocked && !isMPKOptAvailableForFunction(F.getName())) {
								insertMPKCall(I, aLOCK);
								isMPKLocked = true;	
							}
						}
					} else if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
						if (isMPKOptAvailableForFunction(F.getName())) {
							insertMPKCall(I, aLOCK);
						}
					}

					if (nextInst == nullptr && !isMPKLocked) {
						if (!isMPKOptAvailableForFunction(F.getName())) {
							insertMPKCall(I, aLOCK);
							isMPKLocked = true;
						}
					}

					Instruction *tempCurrInst = I;
					while (tempCurrInst->getNextNode() != nextInst) {
						tempCurrInst = tempCurrInst->getNextNode();
						BBIt++;
					}
				}	
			}
		}

		void mallocxInstrumentation (Function &F) {
			unordered_map<string, bool> typeList;
			vector<Instruction*> mallocCalls = vector<Instruction*>();
		 		
			// iterate function and collect all malloc calls and build typeList
			for (auto &BB : F) {
				for (auto &I : BB) {
					if (CallInst *ci = dyn_cast<CallInst>(&I)) {
						Function *fcn = ci->getCalledFunction();
						if (fcn == NULL) {
							continue;
						}

						if (isMallocFunction(fcn->getName())) {
							mallocCalls.push_back(&I);
						}
					} else if (BitCastInst *bci = dyn_cast<BitCastInst>(&I)) {
						Value *src_val = bci->getOperand(0);
						if (!src_val->hasName()) {
							continue;
						}
						
						string src_val_name = src_val->getName().str();
						
						// check if it's already in the list
						auto entry = typeList.find(src_val_name);
						
						// if it exits
						if (entry != typeList.end()) {
							continue;
						}

						// Otherwise, check if it is sensitive
						vector<vector<int>> protectList = getProtectList(bci->getDestTy());
						if (protectList.size() == 0) {
							continue;
						}
		
						// Add to the list
						typeList[src_val_name] = true;
					}
				}
			}


			// Go through every mallocs and change to x call if necessary
			for (auto mallocCall : mallocCalls) {
				string valName = mallocCall->getName().str();
				auto entry = typeList.find(valName);
				if (entry != typeList.end()) {
					insertMallocx(mallocCall, mallocCall->getNextNode());
				}	
			}
		}
		
		void printSmCounters() {
			outs() << " ****************************************************************************************** \n";
			outs() << " *************************************    SM COUNTER    *********************************** \n";
			outs() << " ****************************************************************************************** \n";

			outs() << " Function Nmae | sm_register count | sm_write count | sm_assert count | sm_deregister count\n";
			outs() << " ------------------------------------------------------------------------------------------ \n";
			for (auto entry: sm_counter) {
				if(get<0>(entry.second) == 0 && get<1>(entry.second) == 0 && get<2>(entry.second) == 0 && get<3>(entry.second) == 0){
					//Skip completely empty sets to minimize raw data output
					continue;
				}

				outs() << entry.first << "\t| " << get<0>(entry.second) << "\t| " << get<1>(entry.second) << "\t| " << get<2>(entry.second) << "\t| " << get<3>(entry.second) << "\n";
			}
			outs() << " *************************************************************************************************** \n";
		}
			
		bool isMPKOptAvailableForFunction(string function_name) {
			auto lookupEntry = functionToKeyLookup.find(function_name);
			if (lookupEntry == functionToKeyLookup.end()) {	
				return false;
			}

			auto functionDetailTuple = sensitiveFunctions[lookupEntry->second];
			vector<int> functionSensitiveList = get<0>(functionDetailTuple);

			return functionSensitiveList.size() == 0 && get<1>(functionDetailTuple);
		}
		
		bool isFunctionSensitive(string s) {
			// function is sensitive if: it's key is positive Number (finished inspection) AND it's list vector is not empty
			// first find the key
			auto lookupEntry = functionToKeyLookup.find(s);
			if (lookupEntry == functionToKeyLookup.end()) {	
				return false;
			}

			// next find the function sensitive List
			vector<int> functionSensitiveList = get<0>(sensitiveFunctions[lookupEntry->second]);
			
			return functionSensitiveList.size() > 0;
		}

		void markEntryAsDone(int key) {

			if (key > 0) {
				return; // return if already marked as done
			}
			
			// First mark the key as done
			for (auto it = functionToKeyLookup.begin(); it != functionToKeyLookup.end(); ++it) {
				if (it->second == key) {
					key *= -1;
					it->second = key;
					break;
				}
			}

			// Then update the sensitiveFunctions list accordingly
			sensitiveFunctions[key] = sensitiveFunctions[key * -1]; // copy from old entry
			sensitiveFunctions.erase(key * -1);						// delete old entry
		}

		// insert srcF into dstF if it doesn't already exist
		int addToSensitiveFunctionList(string dstF, string srcF) {
			if (!doesSensitiveFunctionEntryExist(dstF))
				return false;
			
			auto dstLookupEntry = functionToKeyLookup.find(dstF);
			auto &dstTupleEntry = sensitiveFunctions[dstLookupEntry->second];
			auto &dstList = get<0>(dstTupleEntry);

			// get new key to add
			int srcKey = 0;
			
			// if we are not adding a dummy
			if (srcF != "") {
				srcKey = createAndGetSensitiveFunctionEntryKey(srcF);
			}

			// MAKE SURE WE ARE NOT ADDING IT'S OWN KEY
			if (dstLookupEntry->second == srcKey)
				return false;		

			// if this src key is Already complete, determine if it's sensitive
			if (srcKey > 0) {
				auto srcTupleEntry = sensitiveFunctions.find(srcKey);
				auto srcList = get<0>(srcTupleEntry->second);

				// update the list	
				if (srcList.size() > 0) {
					// sensitive
					srcKey = 0;	
				} else {
					// not sensitive, so don't need to add anything
					return false;
				}
			}

			// insert if doesn't already exists
			if (find(dstList.begin(), dstList.end(), srcKey) == dstList.end()) {
				dstList.push_back(srcKey);
			}
			

			if (srcKey == 0) {
				get<1>(dstTupleEntry) = true;
				return true;
			}

			return false;
		}

		// Creates a new sensitive function entry if it doesn't exist. returns the lookup key
		int createAndGetSensitiveFunctionEntryKey(string s) {

			// Only add if it doesn't exist already
			if (!doesSensitiveFunctionEntryExist(s)) {
				int key = getNextSensitiveFunctionsKey(); 
				functionToKeyLookup[s] = key;
				sensitiveFunctions[key] = make_tuple(vector<int>(), false);
			}

			return functionToKeyLookup[s];
		}
		
		bool doesSensitiveFunctionEntryExist(string s) {
			auto entry = functionToKeyLookup.find(s);
			return entry != functionToKeyLookup.end();
		}

		void updateSensitiveFunctions(int srcEntryKey) {
			auto &srcEntry = sensitiveFunctions[srcEntryKey];

			bool sensitive = false;
			bool pending = false;
			bool notSensitive = get<0>(srcEntry).size() == 0;

			for (int key : get<0>(srcEntry)) {
				if (key == 0) {
					sensitive = true;
					break;
				} else if (key < 0) {
					pending = true;
				}
			}
		
			if (sensitive) {
				get<0>(srcEntry).clear();
				get<0>(srcEntry).push_back(0);
			}
			
			vector<int> recursiveUpdateKeys = vector<int>();
			for (auto &entry : sensitiveFunctions) {
				if (entry.first == srcEntryKey)
					continue;
				auto &updateList = get<0>(entry.second);

				if (find(updateList.begin(), updateList.end(), srcEntryKey) != updateList.end()) {
					if (sensitive) {
						get<0>(entry.second) = vector<int>();
						get<0>(entry.second).push_back(0);
						get<1>(entry.second) = true;
						
						recursiveUpdateKeys.push_back(entry.first);
					}	
					else if (notSensitive) {
						updateList.erase(std::remove(updateList.begin(), updateList.end(), srcEntryKey), updateList.end());
						
						if (updateList.size() == 0) {
							recursiveUpdateKeys.push_back(entry.first);
						}
					}
				}
			}
				 
			if (sensitive || notSensitive)
				markEntryAsDone(srcEntryKey);
				
			for (int key : recursiveUpdateKeys)
				updateSensitiveFunctions(key);
		}	

		bool runOnModule (Module &M) override {
			// Build all struct protect lists
			llvm::TypeFinder StructTypes;
			StructTypes.run(M, true);
			for (auto *STy : StructTypes) {
				getProtectList(STy);
			}

			bool isCPP = false;
			for (auto &F : M) {
				if (F.getName().startswith("_GLOBAL__")) {
					isCPP = true;
					break;
				}
			}
		
			// build safestack lists per functions
			for (auto &F :M) {	
				if (F.isDeclaration() || isLLVMFunction(F.getName())) {
						continue;
				}
				safestackAllocasList[&F] = SmallVector<AllocaInst *, 50>();
#ifdef SAFESTACK		
				if (F.hasFnAttribute(Attribute::SafeStack)) {
					auto *DL = &F.getParent()->getDataLayout();
					TargetLibraryInfo &TLI = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
					AssumptionCache &ACT = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
					DominatorTree DT(F);
					LoopInfo LI(DT);
					ScalarEvolution SE(F, TLI, ACT, DT, LI);	

					SafeStack(F, *DL, SE).findInsts(F, safestackAllocasList[&F]);	
				}
#endif
			}

			// build sensitive function list
			for (auto &F : M) {
				if (isLLVMFunction(F.getName())) {
						continue;
				}

				string function_name = F.getName().str();
				// create entry
				int key = createAndGetSensitiveFunctionEntryKey(function_name);
#ifdef FUNCTION_COALESING			
				if (F.isDeclaration()) {
					addToSensitiveFunctionList(function_name, "");
				} else {
					sensitiveFunctions[key] = make_tuple(vector<int>(), false);
					functionCheck(F, isCPP, safestackAllocasList[&F], sensitiveFunctions[key]);
				}
#else
				addToSensitiveFunctionList(function_name, "");
#endif

			}

			for (auto &F : M) {
				sm_register_counter = 0;
				sm_write_counter = 0;
				sm_assert_counter = 0;	
				sm_deregister_counter = 0;
				
				if (F.isDeclaration() || isLLVMFunction(F.getName())) {
						continue;
				}	
				
				functionInstrumentation(F, isCPP, safestackAllocasList[&F]);
				
				mallocxInstrumentation(F);

				assertedVal.clear();

				// for instrumentation counter
				string func_name = F.getName().str();
				if (isCPP) {
					func_name = demangle(F.getName().str().c_str());
				}

				sm_counter[func_name] = std::make_tuple(
					sm_register_counter,
					sm_write_counter,
					sm_assert_counter,
					sm_deregister_counter
				);
			}
			
#ifdef COUNTER
			printSmCounters();
#endif
			return true;
		}

		bool isLLVMFunction(StringRef s) {
			return s.startswith("llvm.") || s.startswith("__llvm__");
		}

		bool isMemcpyFunction(StringRef s) {
			return s.startswith("llvm.memcpy");	
		}

		bool isFreeFunction(StringRef s) {
			return s.equals("free");	
		}

		bool isMunmapFunction(StringRef s) {
			return s.equals("munmap");
		}

		bool isCallocFunction(StringRef s) {
			return s.equals("calloc");
		}

		bool isMallocFunction(StringRef s) {
			return s.equals("malloc");
		}

		bool isReallocFunction(StringRef s) {
			return s.equals("realloc");
		}

		bool isMmapFunction(StringRef s) {
			return s.equals("mmap");
		}
		bool isVTable(StringRef s) {
			return s.startswith("vtable for ");
		}
		bool isCommonSafeLibcall(StringRef s) {
			return isMmapFunction(s) || isCallocFunction(s) || isMallocFunction(s) || isReallocFunction(s);
		}

	};
}


char OTWMAnnotate::ID = 0;
INITIALIZE_PASS(OTWMAnnotate, // Name of pass class, e.g., MyAnalysis
		"otwm-annotate", // Command-line argument to invoke pass
		"OTWM MODULE ", // Short description of pass
		false, // Does this pass modify the control-flow graph?
		false) // Is this an analysis pass?

namespace llvm {
	ModulePass* createOTWMAnnotatePass() {
		return new OTWMAnnotate();
	}
}
