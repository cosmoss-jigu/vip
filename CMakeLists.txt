cmake_minimum_required(VERSION 3.11)
project(otwm VERSION 1.0.0)

# Configuration variables
## Directory paths
SET(PROJ_DIR 	${PROJECT_SOURCE_DIR})
SET(UTILS_DIR 	${PROJ_DIR}/utils)
SET(BUILD_DIR 	${PROJ_DIR}/build)
SET(LIB_DIR 	${PROJ_DIR}/lib)
SET(LLVM_DIR	${PROJ_DIR}/llvm-project)
SET(INC_DIR 	${PROJ_DIR}/include)
SET(KNL_DIR 	${PROJ_DIR}/kernel/vip-linux-5.0)
SET(JMC_DIR	${PROJ_DIR}/jemalloc)
SET(PTM_DIR ${PROJ_DIR}/ptmalloc/ptmalloc3)
SET(BINUTILS_DIR ${PROJ_DIR}/binutils)
SET(KNL_IMG	${KNL_DIR}/arch/x86/boot/bzImage)
## Other configs
execute_process(COMMAND nproc OUTPUT_VARIABLE NJOB)
SET(MAKE	make)

# Add sub CMake files
add_subdirectory(lib)
add_subdirectory(example)

## PTMALLOC targets
add_custom_target(ptmalloc
    COMMAND echo -e " Build ptmalloc..."
	COMMAND cd ${PTM_DIR} && make clean
	COMMAND cd ${PTM_DIR} && make libptmalloc3.so
	COMMAND cp ${PTM_DIR}/libptmalloc3.so ${BUILD_DIR}/lib
)

## JEMALLOC targets
add_custom_target(jemalloc
    COMMAND echo -e " Build jemalloc..."
    COMMAND ${MAKE} -C ${JMC_DIR} -j${NJOB}
    COMMAND ${MAKE} -C ${JMC_DIR} -j${NJOB}
    COMMAND ${MAKE} -C ${JMC_DIR} -j${NJOB} install
	COMMAND cp ${JMC_DIR}/lib/libjemalloc* ${BUILD_DIR}/lib
)


## KERNEL targets
add_custom_target(kernel
    COMMAND echo -e " Build kernel..."
    COMMAND ${MAKE} -C ${KNL_DIR} -j${NJOB} bzImage modules
)

add_custom_target(kernel-install
    DEPENDS kernel
    COMMAND echo -e " Install kernel..."
    COMMAND sudo ${MAKE} -C ${KNL_DIR} -j${NJOB} modules_install
    COMMAND sudo ${MAKE} -C ${KNL_DIR} -j${NJOB} install
)

add_custom_target(kernel-clean
    COMMAND echo -e " Cleaning kernel..."
    ${MAKE} -C ${KNL_DIR} -j${NJOB} clean
)

## LLVM targets
add_custom_target(llvm
	COMMAND cd ${LLVM_DIR}/ && rm -rf build
	COMMAND mkdir ${LLVM_DIR}/build
	COMMAND cd ${LLVM_DIR}/build && cmake -DBUILD_SHARED_LIBS=ON -DLLVM_BINUTILS_INCDIR=\"${BINUTILS_DIR}/include\"  -DLLVM_ENABLE_PROJECTS=\"clang\;compiler-rt\" -G \"Unix Makefiles\" ../llvm
	COMMAND cd ${LLVM_DIR}/build && make -j${NJOB}
	COMMAND cd ${LLVM_DIR}/build && sudo make install -j${NJOB}
)

add_custom_target(llvm-remake
	COMMAND cd ${LLVM_DIR}/build && make -j${NJOB}
)

add_custom_target(llvm-clean
	COMMAND cd ${LLVM_DIR}/ && rm -rf build
)

add_custom_command(OUTPUT ~/.gdbinit
    COMMAND echo -e " Create a default .gdbinit"
    COMMAND echo "set auto-load safe-path ~/" > ~/.gdbinit
)

