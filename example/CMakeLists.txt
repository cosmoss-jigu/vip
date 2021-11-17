SET(CMAKE_C_COMPILER ${PROJECT_SOURCE_DIR}/llvm-project/build/bin/clang)
SET(CMAKE_CXX_COMPILER ${PROJECT_SOURCE_DIR}/llvm-project/build/bin/clang++)  
SET(GCC_COVERAGE_COMPILE_FLAGS "-Wall -fPIC -flto -O2 -g -fsanitize=safe-stack")
SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${GCC_COVERAGE_COMPILE_FLAGS}")
SET(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${GCC_COVERAGE_COMPILE_FLAGS}")
SET(CMAKE_SHARED_LINKER_FLAGS "-Wl,-rpath,${PROJECT_SOURCE_DIR}/build/lib")
SET(CMAKE_EXE_LINKER_FLAGS "-Wall -fPIC -pie -O2 -flto -g -fsanitize=safe-stack ${CMAKE_EXE_LINKER_FLAGS}")
    
SET(llvm_c_test_files "")
SET(llvm_cpp_test_files "")

LIST(APPEND llvm_c_test_files "example")
LIST(APPEND llvm_cpp_test_files "example_cpp")

foreach(file IN LISTS llvm_c_test_files)
	add_executable(${file} ${file}.c)
	target_link_libraries(${file} PRIVATE
		sm
	)
endforeach()

foreach(file IN LISTS llvm_cpp_test_files)
	add_executable(${file} ${file}.cpp)
	target_link_libraries(${file} PRIVATE
		sm
	)
endforeach()

foreach(file IN LISTS llvm_c_test_files)
	target_link_libraries(${file} PRIVATE
		${PROJECT_SOURCE_DIR}/build/lib/libjemalloc.so
	)

	add_custom_command(TARGET ${file}
		POST_BUILD
		COMMAND ${PROJECT_SOURCE_DIR}/utils/imprinter.py -f ${PROJECT_SOURCE_DIR}/build/manual-tests/llvm_tests/${file}
	)
endforeach()

foreach(file IN LISTS llvm_cpp_test_files)
	target_link_libraries(${file} PRIVATE
		${PROJECT_SOURCE_DIR}/build/lib/libjemalloc.so
	)

	add_custom_command(TARGET ${file}
		POST_BUILD
		COMMAND ${PROJECT_SOURCE_DIR}/utils/imprinter.py -f ${PROJECT_SOURCE_DIR}/build/manual-tests/llvm_tests/${file}
	)
endforeach()	
