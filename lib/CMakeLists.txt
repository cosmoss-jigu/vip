SET(CMAKE_C_COMPILER gcc)
SET(CMAKE_CXX_COMPILER g++)
    

SET(CMAKE_C_FLAGS "-Wall -fPIC -pie -flto -march=native -O3")

add_library(sm OBJECT
	libsm.c
	"${PROJECT_SOURCE_DIR}/include/libsm.h"
)

target_include_directories(sm PUBLIC
	${PROJECT_SOURCE_DIR}/include/
	${PROJECT_SOURCE_DIR}/lib/
)
