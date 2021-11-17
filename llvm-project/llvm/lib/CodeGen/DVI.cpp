#include "llvm/CodeGen/TargetLowering.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <vector>
#include <unordered_map>
#include <tuple>
#include <string>
#include <cxxabi.h>

#define CPI


using namespace llvm;
/*
using std::vector;
using std::unordered_map;
using std::string;
using std::tuple;
using std::get;
using std::pair;

//TODO NEED HEADER FOR GENERAL OTWM macros like this below
StringRef SM_ASSERT("sm_assert_8b");
StringRef SM_REGISTER("sm_register_8b");
StringRef SM_WRITE_ONCE("sm_write_once_8b");
StringRef SM_WRITE("sm_write_8b");
StringRef SM_DEREGISTER("sm_deregister_8b");
StringRef SM_LOCK("sm_lock_safe_region");
StringRef SM_UNLOCK("sm_unlock_safe_region");

unordered_map<string, tuple<vector<vector<int>>, int, bool>> globalStructList;
unordered_map<string, Value*> sensitiveGlobalsList;

*/
namespace {
class DVIPass : public ModulePass {

public:
        static char ID; // Pass identification, replacement for typeid..

        DVIPass() : ModulePass(ID) {
            initializeDVIPassPass(*PassRegistry::getPassRegistry());
        }
/*
	vector<int> combine(vector<int> a, vector<int> b) {
		if (a.size() > b.size()) {
			a.insert(a.end(), b.begin(), b.end());
			return a;
		} else {
			b.insert(b.end(), a.begin(), a.end());
			return b;
		}
	}

	bool isFunctionPtr (Type *Ty) {
		return Ty->isPointerTy() && cast<PointerType>(Ty)->getElementType()->isFunctionTy();
	}
	
	// returns a list of indices for drilling down to the sensitive element -1 when found
	vector<vector<int>> getProtectList(Type *Ty, vector<int> currTrace = vector<int>()) {
	    	//outs() << "insdie of getProtectList. Type:\n";
		//Ty->dump();
		vector<vector<int>> result = vector<vector<int>>();
		vector<int> newList = vector<int>();
		
		if (currTrace.empty()) {
			currTrace = newList;
		}

		// function pointer
		if (isFunctionPtr(Ty)) {
			//outs() << "function ptr type\n";
			currTrace.push_back(-1);
			result.push_back(currTrace);
			return result;
		} 

		// generic pointer
		else if (PointerType *PTy = dyn_cast<PointerType>(Ty)) {
			//outs() << "generic ptr type\n";
			
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
					return result;
				} else if (callChain[lastIndex] == -1) {
					vector<int> tempTrace = currTrace;
					tempTrace.push_back(-1);
					tempTrace.push_back(callChain[lastIndex]);
					result.push_back(tempTrace);
				}
			}
			return result;	
		}

		// Array
		else if (ArrayType *ATy = dyn_cast<ArrayType>(Ty)) {
			//outs() << "array type\n";

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
			//outs() << "struct type!\n";
			// Literal type don't even have names so they are fine, just skip it
			if (STy->isLiteral() || STy->isOpaque()) {
				return result;
			}
			string structName = STy->getName();
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
			fixStructListBasedOnNewEntry(get<0>(currTuple), lookupKey, structName); // <- this doesn't work. need to fix it	
			
			// update non-observing structs inside of globalStructLists
			for (auto &structEntry: globalStructList) {
				// if the structEntry is still observing, skip it
				if (get<1>(structEntry.second) < 0) {
					continue;
			        }

				fixStructListBasedOnNewEntry(get<0>(structEntry.second), -1 * get<1>(structEntry.second), structName);
			}

			// TODO: probably need to implement something using the dependency list to make sure that the returned result is complete.
			return get<0>(currTuple);
		}

	    // OTHERWISE UNKNOWN
            return vector<vector<int>>();
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
		bool isNotSensitive = (baseList.size() == 0);	

		// is it definitely sensitive?
		bool isSensitive = false;
		for (int i = 0; i < baseList.size(); i++) {
			// if it contains a call chain that ends on -1, it's definitely sensitive
			if (baseList[i][baseList[i].size() - 1] == -1) {
				isSensitive = true;
			}
		}

		// FIXING PHASE
		for (int i = fixList.size() - 1; i >= 0; i--) {
			vector<int> &currChain = fixList[i];
			int lastIndex = currChain.size() - 1;
			int indexBefore = lastIndex - 1;
	
			// find the call chain that ends on this lookup key (dependent pointer & struct vars)
			if (currChain[lastIndex] == lookupKey) {
				if (isNotSensitive) {
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

	void printGlobalStructList () {
		outs() << "\nGLOBAL STRUCT LIST:\n";
		for(auto structEntry : globalStructList) {
			printStructEntry(structEntry.first, structEntry.second);
		}
		outs() << "\n";
	}	

	int getNextGlobalStructListKey () {
		int lowest = -1;
		for (auto structEntry: globalStructList) {
			int num = get<1>(structEntry.second);
		        // always convert keys to negative
			if (num > 0) {
				num = -1 * num;
			}

			if (num < lowest) {
				lowest = num;
			}
		}
		return lowest - 1;
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
		int flag_val = 5243136;
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

    	int insertLibCall (Value *sm_arg_val, Instruction *curr_inst, StringRef function_name) {
	
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

		return 0;
	}

	void insertMPKCall (Instruction *insert_point, StringRef function_name) {
	
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

	Value* insertSafeStackGEP (Instruction *insert_point, int idx, Type *type, Value *value) {
		
		LLVMContext &ctx = insert_point->getFunction()->getContext();
		IRBuilder<> builder(ctx);
		builder.SetInsertPoint(insert_point);
		
		return builder.CreateGEP(type, value, ConstantInt::get(Type::getInt32Ty(ctx), idx), "memberptr");
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

	bool isSensitive (Type *type) {
		vector<vector<int>> pLists = getProtectList(type);
		for (vector<vector<int>>::iterator lists_it = pLists.begin(); lists_it != pLists.end(); ++lists_it) {
			if ((*lists_it).size() == 1) {
				return true;
			}
		}
		return false;
	}

	void printProtectLists (vector<vector<int>> lists) {
		for (vector<vector<int>>::iterator lists_it = lists.begin(); lists_it != lists.end(); ++lists_it) {
			printCallChain(*lists_it);
		}
	}

	void printCallChain (vector<int> callChain) {
		for (vector<int>::iterator list_it = callChain.begin(); list_it != callChain.end(); ++list_it) {
			outs() << " " << *list_it;
		}
		outs() << "\n";
	}

	vector<int> getIndicesFromGetElementPtr (GetElementPtrInst *gep_inst) {
		vector<int> result;

		for (auto it = gep_inst->idx_begin(); it != gep_inst->idx_end(); ++it) {
			Constant *c = dyn_cast<Constant>(*it);
			if (c == nullptr) {
				return vector<int>();
			}
			ConstantInt *ci = dyn_cast<ConstantInt>(c);
			ci->dump();
			int i = ci->getValue().roundToDouble();
			outs() << "num:" << i << "\n";
			outs() << "sign extended: " << ci->getSExtValue() << "\n";
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
		// insert point setup
		LLVMContext &ctx = insert_point->getFunction()->getContext();
		IRBuilder<> builder(ctx);
		builder.SetInsertPoint(insert_point);

		// loading
		return builder.CreateLoad(val, "gep_load");
	}

	Value *insertBitCast (Instruction *insert_point, Value *val, Type *toType) {
		// insert point setup
		LLVMContext &ctx = insert_point->getFunction()->getContext();
		IRBuilder<> builder(ctx);
		builder.SetInsertPoint(insert_point);

		// loading
		return builder.CreateBitCast(val, toType, "bitcast_inst");
	}

	int checkRecursiveDeregister (Instruction *insert_point) {
		int skipNum = 0;

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
			recursiveInsertions (insert_point, protectVal, protectType, protectList, SM_DEREGISTER);
		}
	}

	int recursiveInsertions (Instruction *insert_point, Value *original_val, Type *original_ty, vector<vector<int>> pList, StringRef libcall) {
		int skipNum = 0;

		// Insert GEP and Register call instructions
		for (vector<vector<int>>::iterator lists_it = pList.begin(); lists_it != pList.end(); ++lists_it) {
			Value *val = original_val;
			Type *ty = original_ty;
		   	for(vector<int>::iterator list_it = (*lists_it).begin(); list_it != (*lists_it).end(); ++list_it) {
				StructType *sty = dyn_cast<StructType>(ty);
				ArrayType *aty = dyn_cast<ArrayType>(ty);

				if (*list_it == -1) {
					// Insert Register
					skipNum += insertLibCall(val, insert_point, libcall);
				} else {
					// derve1 till we find actual struct or Array type
					if (!sty && !aty) {
						while (dyn_cast<PointerType>(val->getType()) && dyn_cast<PointerType>(ty)) {
							val = getLoadVal(insert_point, val);
							ty = dyn_cast<PointerType>(ty)->getElementType();
							skipNum += 1;
						}

						if (dyn_cast<PointerType>(val->getType())) {
							sty = dyn_cast<StructType>(ty);
							aty = dyn_cast<ArrayType>(ty);
						}
					}
						
					// Insert GEP
					if (sty && sty->isOpaque()) {
						// Insert Register
						skipNum += insertLibCall(val, insert_point, libcall);
					} if (sty) {
						val = insertGEP(insert_point, *list_it, sty, val);
						skipNum++;
						ty = sty->getStructElementType(*list_it);
					} else if (aty) {
						val = insertGEP (insert_point, *list_it, aty, val);
						skipNum++;
						ty = aty->getElementType();
						
						// If the returned type is confused on Array of array vs actual type pointer, type cast it
						if (dyn_cast<PointerType>(val->getType())->getElementType() != ty) {
							val = insertBitCast(insert_point, val, ty->getPointerTo());
							skipNum++;
						}
					} else {
						// TODO: union type comes here and is skipped!
						return skipNum;
					}
				}
			}
		}

		return skipNum;
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
			return;
		}

		// Checking for function ptr call. they usaully needs to load the function first
		if (!isSensitive(inspectType)) {
			return;
		}

#ifndef CPI	
		insertLibCall(protectVal, insert_point, SM_ASSERT);
#else
		GetElementPtrInst *gep_inst;
		
		if (insert_point->getPrevNode()->getPrevNode() == nullptr || !dyn_cast<GetElementPtrInst>(insert_point->getPrevNode()->getPrevNode())) {
		// lone function ptr call
			insertLibCall(protectVal, insert_point, SM_ASSERT);
			return;
		}

		gep_inst = dyn_cast<GetElementPtrInst>(insert_point->getPrevNode()->getPrevNode());
		
		while (gep_inst) {
			inspectType = gep_inst->getSourceElementType();
			protectVal = gep_inst; // <-- doesn't need to be referenced. this is good to be protected
			
			vector<int> checkIndices = getIndicesFromGetElementPtr(gep_inst);
			
			if (checkIndices.size() == 0 || isSensitiveElement(inspectType, checkIndices.back())) {
				insertLibCall(protectVal, insert_point, SM_ASSERT);
			}

			// set new insert point
			insert_point = gep_inst;
			Instruction *one_before_insert_point = insert_point->getPrevNode();
			Instruction *two_before_insert_point = nullptr;
		        if (one_before_insert_point) {
				two_before_insert_point	= one_before_insert_point->getPrevNode();
			}

			if (one_before_insert_point && dyn_cast<GetElementPtrInst>(one_before_insert_point)) {
				gep_inst = dyn_cast<GetElementPtrInst>(one_before_insert_point);
			} else if (one_before_insert_point && dyn_cast<LoadInst>(one_before_insert_point) &&
				       	two_before_insert_point && dyn_cast<GetElementPtrInst>(two_before_insert_point)) {
				gep_inst = dyn_cast<GetElementPtrInst>(two_before_insert_point);
			} else {
				if (one_before_insert_point && dyn_cast<LoadInst>(one_before_insert_point)) {
					// insert the last object ptr assert
					load_inst = dyn_cast<LoadInst>(one_before_insert_point);
					protectVal = load_inst->getPointerOperand();
					insertLibCall(protectVal, insert_point, SM_ASSERT);
				} else if (Instruction *temp_inst = dyn_cast<Instruction>(gep_inst->getOperand(0))) {
					inspectType = nullptr;
					if (dyn_cast<BitCastInst>(temp_inst) && temp_inst->getPrevNode() && dyn_cast<LoadInst>(temp_inst->getPrevNode())) {
						BitCastInst *bci = dyn_cast<BitCastInst>(temp_inst); 
						load_inst = dyn_cast<LoadInst>(temp_inst->getPrevNode());
						PointerType *pt = dyn_cast<PointerType>(load_inst->getPointerOperandType());	
						Type *loadTy = pt->getElementType();
						Type *bitcastSrcTy = bci->getSrcTy(); // compare 

						if (loadTy == bitcastSrcTy) {
							protectVal = load_inst->getPointerOperand();
							inspectType = load_inst->getPointerOperandType();
							// TODO continue here?
						}
						 
					} else if (AllocaInst *ai = dyn_cast<AllocaInst>(temp_inst)) {
						inspectType = ai->getAllocatedType();
						protectVal = gep_inst->getOperand(0);
						// TODO continue here?
					} else if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(temp_inst)) {
						//TODO: maybe i need to continue on the traversing here
						// just skip this for now
						break;
					}

					if (inspectType != nullptr && isSensitive(inspectType)) {
						insertLibCall(protectVal, insert_point, SM_ASSERT);
					}
				}

				break;
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

	bool checkMemcpyInst (Instruction *memcpyInst) {
		Instruction *insert_point = memcpyInst->getNextNode();

		// Source vals
		Value *src = memcpyInst->getOperand(1);
		Type *realSrcPtrType = getOperandsActualType(src);
		Type *realSrcType;
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

	int protectMemcpyInst (Instruction *memcpyInst) {
		int skipNum = 0;
		Instruction *insert_point = memcpyInst->getNextNode();

		// Source vals
		Value *src = memcpyInst->getOperand(1);
		Type *realSrcPtrType = getOperandsActualType(src);
		Type *realSrcType;
		if (PointerType *pt = dyn_cast<PointerType>(realSrcPtrType)) {
			realSrcType = pt->getElementType();
		} else {
			return skipNum;
		}	

		// Destination vals
		Value *dst = memcpyInst->getOperand(0);
		Type *realDstPtrType = getOperandsActualType(dst);
		Type *realDstType;
		if (PointerType *pt = dyn_cast<PointerType>(realDstPtrType)) {
			realDstType = dyn_cast<PointerType>(realDstPtrType)->getElementType();
		} else {
			return skipNum;
		}

		// Check to see if we need to protect this type
		vector<vector<int>> protectList = getProtectList(realSrcType);
		//printProtectLists(protectList);
		if (protectList.size() == 0) {
			return skipNum;
		}

		// Inserts a bitcast, (if needed insert registers), write everything
		Value *v = insertBitCast(insert_point, dst, realSrcPtrType);
		skipNum++;
		BitCastInst *bci = dyn_cast<BitCastInst>(memcpyInst->getNextNode());

		if (realSrcType != realDstType && bci) {
			// insert bitcast first, so that everything will be properly registered	
			skipNum += registerBitCastedVal(bci);
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
			
		skipNum += recursiveInsertions(insert_point, protectVal, protectType, protectList, SM_WRITE);
		
		return skipNum;
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
			insertLibCall(protectVal, insert_point, SM_DEREGISTER);
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

	bool isAGlobal(Value *v) {
	        if (sensitiveGlobalsList[v->getName().str()]) {
			return true;
		}
		return false;
	}

	bool hasSensitiveOrigin(Instruction *I) {
		Instruction *curr_inst = I;
		while (curr_inst) {
			if (BitCastInst *bci = dyn_cast<BitCastInst>(curr_inst)) {
				curr_inst = dyn_cast<Instruction>(curr_inst->getOperand(0));
			} else if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(curr_inst)) {
				curr_inst = dyn_cast<Instruction>(curr_inst->getOperand(0));
			} else if (LoadInst *li = dyn_cast<LoadInst>(curr_inst)) {
				
				// exit condition
				if (!dyn_cast<Instruction>(curr_inst->getOperand(0)) && isAGlobal(curr_inst->getOperand(0))) {
					// check if it's a global value
					return true;
				}
				
				curr_inst = dyn_cast<Instruction>(curr_inst->getOperand(0));			
			} else if (CallInst *ci = dyn_cast<CallInst>(curr_inst)) {
				
			} else {
				outs() << "instruction not recognized!!\n";
				curr_inst->dump();
			}
		}

		return false;
	}

	void registerBitCastedVal2 (Instruction *I) {
		BitCastInst *bci = dyn_cast<BitCastInst>(I);
		Value *val = I;
		Type *dest_ty = bci->getDestTy();

		Instruction *insert_point = I->getNextNode();

		// is the destination type sensitive?
		vector<vector<int>> dest_protectList = getProtectList(dest_ty);
		if (dest_protectList.size() == 0) {
			return;
		}
		//printProtectLists (dest_protectList);

		// find origin: is it from unsafe stack/dynamic allocation/static or global?
		if (hasSensitiveOrigin(I)) {
			insertLibCall(val, insert_point, SM_REGISTER);
			I->dump();
			outs() << "protect this!\n";
		}

//		if (!sty && !aty && !(Ty->isPointerTy() && cast<PointerType>(Ty)->getElementType()->isFunctionTy())) {
//			
//
//			// dig through and find the actual type of all of the nested pointers
//			while (dyn_cast<PointerType>(dest_ty) && dyn_cast<PointerType>(dest_ty)->getElementType()) {
//				val = getLoadVal(insert_point, val);
//				dest_ty = dyn_cast<PointerType>(dest_ty)->getElementType();
//			
//				if (dyn_cast<PointerType>(val->getType())) {
//					sty = dyn_cast<StructType>(ty);
//					aty = dyn_cast<ArrayType>(ty);
//				}
//			}
//
//		}

	}

	int registerBitCastedVal (BitCastInst *bci) {	
		// for mmap, malloc and calloc -> need to get the allocated size and divide by current bitcasted size.
		// that should give us an answer to if it's an array or not.

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
					return 0;
				}
				// Check to see if it's a downcast
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
				
				// getting type size
				DataLayout dl = DataLayout(insert_point->getModule());
				int pointed_type_size = dl.getTypeAllocSize(pointed_type);

				// TODO seperate out allocated memory??
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
							//outs() << "not handled yet!\n";
						}
					}
				}

				int skipNum = 0;

				for (int x = 0; x < arraySize; x++) {
					// insert GEP
					Value *gepVal = insertArrayGEP(insert_point, x, pointed_type, val);
					skipNum++;
					// insert protection
					skipNum += recursiveInsertions(insert_point, gepVal, pointed_type, dest_protectList, SM_REGISTER);
				}
					
				return skipNum;
			}
		}
		return 0;
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

	bool isMPKNecesary(Instruction *I) {
		if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
			// Initialize value and Type
			Value *val = &*AI;
			Type *ty = AI->getAllocatedType();
			vector<vector<int>> protectList = getProtectList(ty);
			if (protectList.size() > 0) {
				return true;
			}
			return false;	
		} else if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)) {
			return checkBitCastedVal (BCI);
		} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {	
			Type *operandType = SI->getPointerOperandType();
			Value* stored_val = SI->getOperand(0);

			vector<vector<int>> protectList = getProtectList(operandType);
			if (protectList.size() == 0) {
				return false;
			}
			return true;
		} else if (CallInst *ci = dyn_cast<CallInst>(I)) {
			Function *fp = ci->getCalledFunction();
			
			if (fp && isMemcpyFunction(fp->getName())) {
				return checkMemcpyInst(I);
			} else if (fp && isMunmapFunction(fp->getName())) {
				return checkMunmapInst(I);
			} else if (fp && isLLVMFunction(fp->getName())) {
				return false;
			} else if (!isa<Constant>(ci->getCalledValue())) {
				//outs() << "Checking if we need to assert\n";
				return false;
			} else {
				Value *calledVal = ci->getCalledValue();
				Value *sv = calledVal->stripPointerCasts();
				if (isFreeFunction(sv->getName())) {
					//outs() << "is free!\n";
					return checkRecursiveDeregister(I);	
				} else {
					return false;
				}
			}
		}
		return false;
	}

	Value *isUnsafeStackLoadInst(Instruction *I) {
		if (LoadInst *li = dyn_cast<LoadInst>(I)) {
			if (I->getOperand(0)->getName().equals("__safestack_unsafe_stack_ptr")) {
				return I->getOperand(0);
			}
		}
		return nullptr;
	}

	bool isLoadingUnsafeStack(Instruction *I) {
		if (I && dyn_cast<LoadInst>(I) && isAGlobal(I->getOperand(0)))
			return true;
		return false;
	}

	int getLastIndexOfGEPI(GetElementPtrInst *gepi) {
		int offset = 0;
		for (auto it = gepi->idx_begin(); it != gepi->idx_end(); ++it) {
			offset = (dyn_cast<ConstantInt>(dyn_cast<Constant>(*it)))->getSExtValue();
		}
		return offset;
	}

    void registerUnsafeStack(Function &F) {

		bool isFirstInst = true;
		unordered_map<int, Type*> unSafeStackVars;
		Value *safeStackVal = nullptr;
		Instruction *unSafeStackProtectionLoc = nullptr;		

		// building table phase
		for (auto &BB : F) {
			for (auto &I : BB) {

				// exit if safestack doesn't exists
				if (isFirstInst) {
					safeStackVal = isUnsafeStackLoadInst(&I);
					if(safeStackVal == nullptr) {
						return;	
					}
				}
				isFirstInst = false;

				// unordered map building phase
				if (BitCastInst *bci = dyn_cast<BitCastInst>(&I)) {
					I.dump();
					if (Instruction *inst = dyn_cast<Instruction>(I.getOperand(0))) {
						if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(inst)) {
							if (!isLoadingUnsafeStack(dyn_cast<Instruction>(inst->getOperand(0)))) {
								continue;
							}
							
							int offset = getLastIndexOfGEPI(gepi);
								
							if (unSafeStackVars.find(offset) == unSafeStackVars.end()) {
								unSafeStackVars[offset] = bci->getDestTy();
							}
							//TODO: do we need to collect list of all type this var can be bitcasted into and register a union list of it's protection list?
						}
					}
				} else if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(&I)) {
					I.dump();

//					// check if getElement instruction is coming from loaded unsafe_stack
//					if (!isLoadingUnsafeStack(dyn_cast<Instruction>(I.getOperand(0)))) {
//						continue;
//					}
					
//					// create a new unsafestack entry if the key doesn't exists
//					int offset = getLastIndexOfGEPI(gepi);
//					if (unSafeStackVars.find(offset) == unSafeStackVars.end()) {
//						unSafeStackVars[offset] = nullptr;
//					}

					
				} else if (StoreInst *si = dyn_cast<StoreInst>(&I)) {
					I.dump();
					// check to see if it's storing into the unsafe stack
					if (!I.getOperand(1)->getName().equals("__safestack_unsafe_stack_ptr")) {
						continue;
					}

					// IF: what's being stored is an unsafe entry, add to the instrumentation table
					if (Instruction *inst = dyn_cast<Instruction>(I.getOperand(0))) {
						if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(inst)) {
							if (!isLoadingUnsafeStack(dyn_cast<Instruction>(inst->getOperand(0)))) {
								continue;
							}

							int offset = getLastIndexOfGEPI(gepi);
							if (unSafeStackProtectionLoc == nullptr) {
								unSafeStackProtectionLoc = I.getNextNode(); 
							} else {
								outs() << "multiple unSafeStack store is detected!!!\n";
							}
						}
					}
				}
			}
		}
	
		outs() << "unsafe stack exists!\n";
		F.dump();

		// register phase
		for(auto unSafeStackVar : unSafeStackVars) {

			outs() << " >> " << unSafeStackVar.first << " :\n";
			if (unSafeStackVar.second) {
				unSafeStackVar.second->dump();
			} else {
				outs() << "\tnullptr\n";
			}
			
			vector<vector<int>> dest_protectList = getProtectList(unSafeStackVar.second);
			if (dest_protectList.size() == 0) {
				return;
			}

			
			outs() << "sm instrumentation!\n";
			// find origin: is it from unsafe stack/dynamic allocation/static or global?
			outs() << "here0\n";
			safeStackVal->dump();
			Value *gepVal = insertSafeStackGEP (unSafeStackProtectionLoc, unSafeStackVar.first, Type::getInt8Ty(F.getContext())->getPointerTo(), safeStackVal);
			outs() << "here1\n";
			Value *bitcastVal = insertBitcast(unSafeStackProtectionLoc, gepVal, unSafeStackVar.second);
			outs() << "here2\n";
			recursiveInsertions (unSafeStackProtectionLoc, bitcastVal, bitcastVal->getType(), dest_protectList, SM_REGISTER);
			outs() << "here3\n";
		}
	}

	void deepRegisterInstrumentation(Instruction *insert_point, Value *val, Type *real_ty) {

		// Insert the real type bitcast instruction at right below the variable allocation
		Value *curr_val = insertBitcast(insert_point, val, real_ty);
		Type *curr_ty = curr_val->getType(); 	

		// Unrevel any possible nested pointers
		while (dyn_cast<PointerType>(curr_ty) && dyn_cast<PointerType>(dyn_cast<PointerType>(curr_ty)->getElementType())) {
			curr_val = getLoadVal(insert_point, curr_val);
			curr_ty = curr_val->getType();
		}


		if (dyn_cast<PointerType>(curr_ty)) {
			// function ptr
			// ptr of struct
			// ptr of array
		}
		
	}

	void functionInstrumentation (Function &F, bool isCPP) {
//		outs() << "\n\nFN Name: " << F.getName() << "\n";
		
		vector<Value*> sensitive_vars;
		bool instrumentGlobals;
		bool has_unsafe_stack = false;

		if (isCPP) {
			instrumentGlobals = (F.getName().startswith("_GLOBAL__"))? true : false;
		} else {
			instrumentGlobals = (F.getName().equals("main"))? true : false;
		}

		// iterate through each lines of instructions to analyze and instrument
		for (auto &BB : F) {
			bool isMPKLocked = true;

			for (BasicBlock::iterator BBIt = BB.begin(); BBIt != BB.end(); ++BBIt) {	
				Instruction *I = &*BBIt;
				Instruction *nextInst = I->getNextNode();
				//I->dump();
				
				int skipNum = 0;

				if (isa<PHINode>(I) || isa<LandingPadInst>(I)) {
					continue;
				}

				// Instrucment registers for all sensitive global variables
				if (instrumentGlobals) {
					Module *M = BB.getModule();
					for (auto gvarIt = M->global_value_begin(); gvarIt != M->global_value_end(); ++gvarIt) {
						if (Value *v = dyn_cast<Value>(&*gvarIt)) {
							
							// TODO: DO WE NEED THIS? this is registering vtable's ACTUAL address
							string demangledName = demangle(v->getName().str().c_str());
							if (isVTable(StringRef(demangledName))) {
								if (isMPKLocked) {
									isMPKLocked = false;
								}
								insertLibCall(v, I, SM_REGISTER);
								continue;
							}

							Type *ty = (*gvarIt).getValueType();
							vector<vector<int>> protectList = getProtectList(ty);
							if (protectList.size() == 0) {
								continue;
							}

							if (isMPKLocked) {
								isMPKLocked = false;
							}
							recursiveInsertions(I, v, ty, protectList, SM_REGISTER);
						}
					}	
					instrumentGlobals = false;
				}

				// Step 3
				if (isMPKNecesary(I)) {
					isMPKLocked = false;
				}


				if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)) {
					// if casted to a pointer of a struct,
					// check the struct to see what all needs to be protected inside of it.
					// Protect in a similar way to alloca instruction
					// outs() << "Found BITCAST INSTRUCTION:\n";
					//registerBitCastedVal2(I);
					//registerBitCastedVal(BCI);
									
				} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
					// WRITE DURING STORE
					//outs() << "Found STORE INSTRUCTION:\n";
					Type *operandType = SI->getPointerOperandType();
					Value* stored_val = SI->getOperand(0);

					vector<vector<int>> protectList = getProtectList(operandType);
					if (protectList.size() > 0) {
						// Set insertion point
						Instruction *insert_point = I->getNextNode();
						Value *pointerOperand = SI->getPointerOperand();
						StringRef func_name = SM_WRITE;

						//outs() << "write inserted\n";
						skipNum += insertLibCall(pointerOperand, insert_point, func_name);
					}				
				} else if (CallInst *ci = dyn_cast<CallInst>(I)) {
					//outs() << "Found CALL INSTRUCTION:\n";
					Function *fp = ci->getCalledFunction();
					
					if (fp && isMemcpyFunction(fp->getName())) {
						//outs() << "Memcpy function!\n";
						skipNum += protectMemcpyInst(I);	
					} else if (fp && isMunmapFunction(fp->getName())) {
						//outs() << "isMunmap!\n";
						protectMunmapInst(I);
					} else if (fp && isLLVMFunction(fp->getName())) {
						// filter out llvm call functions && filter out constant calls
						//outs() << " - LLVM function\n";
						skipNum += 0;
					} else if (!isa<Constant>(ci->getCalledValue())) {
						//outs() << " - NON-CONSTANT  CALLED VALUE\n";
						assertSensitiveFunctionCall(I);
						if (!isMPKLocked) {
							//outs() << " [x] MPK LOCK INSERT!\n";
							insertMPKCall(I, SM_LOCK);
							isMPKLocked = true;	
						}
					} else {
						//outs() << " - ELSE!!\n";
						Value *calledVal = ci->getCalledValue();
						Value *sv = calledVal->stripPointerCasts();
						if (isFreeFunction(sv->getName())) {
							//outs() << "FREE!\n";
							recursiveDeregister(I);	
						} else {
							//outs() << " - ALL OTHER CALLS\n";
							assertSensitiveFunctionCall(I);
							if (!isMPKLocked) {
								//outs() << " [x] MPK LOCK INSERT!\n";
								insertMPKCall(I, SM_LOCK);
								isMPKLocked = true;	
							}
						}
					}
				} else if (isa<InvokeInst>(I)) {
					//outs() << "invoke inst!\n";
					if (!isMPKLocked) {
						//outs() << " [x] MPK LOCK INSERT!\n";
						insertMPKCall(I, SM_LOCK);
						isMPKLocked = true;	
					}
				}

				// Step 5
				Instruction *checkInst = I;	
				if (nextInst == nullptr && !isMPKLocked) {
					//outs() << " [x] MPK LOCK INSERT! - END OF BASIC BLOCK\n";
					insertMPKCall(checkInst, SM_LOCK);
					isMPKLocked = true;
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

*/	
        bool runOnModule(Module &M) override {
            //outs() << "\n > WORKING ON this module ["<< M.getName() <<"]\n";
/*
	    // Collect all global struct's protect lists
	    llvm::TypeFinder StructTypes;
	    StructTypes.run(M, true);
	    
	    for (auto *STy : StructTypes) {
	        getProtectList(STy);
	    }
	    printGlobalStructList();

	    // Save a list of all sensitive globals
	    for (auto gvarIt = M.global_value_begin(); gvarIt != M.global_value_end(); ++gvarIt) {
	        if (Value *v = dyn_cast<Value>(&*gvarIt)) {
//				v->dump();
				sensitiveGlobalsList[v->getName().str()] = v;
			}
	    }
	    outs() << "end of globals======\n";

	    // Check if it's CPP file
            bool isCPP = false;
	    for (auto &F : M) {
	        if (F.getName().startswith("_GLOBAL__")) {
		    	isCPP = true;
		    	break;
			}
	    }

	    for (auto &F : M) {	
	        if (F.isDeclaration() || isLLVMFunction(F.getName())) {
          	    continue;
			}

	    	if (!F.getName().startswith("sm_")) {
				outs() << "\n > WORKING ON this Function: \n";
				F.dump();
				outs() << "---- END OF FUNCTION -----\n";
	   	 	}

	   		registerUnsafeStack(F);
//	    	functionInstrumentation(F, isCPP);
			
//	    	mallocxInstrumentation(F);

			if (!F.getName().startswith("sm_")) {
				outs() << "\n --------- AFTER INSTRUMENTATION: \n";
				F.dump();
				outs() << "---- END OF FUNCTION -----\n";
			}
		
	    }
*/	
	    return true;
	}
/*
	
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
*/
    };
} // end anonymous namespace


char DVIPass::ID = 0;
INITIALIZE_PASS(DVIPass, 
		"dvi-pass",
                "DVI pass",
		false,
		false)

namespace llvm {
ModulePass *createDVIPass() { 
	return new DVIPass(); 
}}

