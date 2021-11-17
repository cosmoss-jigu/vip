add_custom_target(otwm)

set(OTWM_SOURCES otwm.c)
set(OTWM_FLAGS ${SANITIZER_COMMON_FLAGS} "-pthread")

include_directories(..)

add_compiler_rt_runtime(clang_rt.otwm
        STATIC 
        ARCHS x86_64 
	SOURCES ${OTWM_SOURCES}
	CFLAGS ${OTWM_FLAGS}
PARENT_TARGET otwm)
