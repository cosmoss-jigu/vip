#ifdef __cplusplus
extern "C" {
#endif
   	#ifndef libsm_h__
   	#define libsm_h__
	
	#include <stdio.h>
	#include <stdlib.h>
	#include <errno.h>
	#include <stdbool.h>
	#include <string.h>

	#define NON_REPETITIVE
	#define BB_COALESING
	#define MPK // toggles whether MPK is used (for non-mpk machine development)


	#define SM_MEMORY_RATIO	    32
	#define EIGHT_BYTES             64

	#define USER_START		((void*)0x0ul)
	#define HYPR_START		((void*)0x3F03F03EF000ul)
	#define HYPR_END		((void*)0x7FFFFFFFE000ul)
	#define BITMAP_START		((void*)0x7E07E07DE000ul)
	#define AREA_SIZE		((void*)0x3F03F03EF000ul)
	#define BITMAP_SIZE		((void*)0x01F81F81F780ul)
/*

		|--------------| <- USER_START = 0x0
		|              |
		|              |
		|  User space  |   AREA_SIZE: 0x3F03F03EF000
		|              |
		|              |
		|--------------| <- HYPR_START = 0x3F03F03EF000	     ---
		|              |					|
		|              |					|
		|  Hyperspace  |   AREA_SIZE: 0x3F03F03EF000		|
		|              |					|
		|              |					| <- pkey protected region
		|--------------| <- BITMAP_START = 0x7E07E07DE000	|
		|              |					|
		|    Bitmap    |   BITMAP_SIZE: 0x01F81F81F780		|  2 bits: (is_locked | is_registered)
		|              |					|
		|--------------| <- BITMAP_END = 0x7FFFFFFFD780       ---
*/

    typedef unsigned long u64;

    extern void sm_assert(void *user_vaddr, unsigned int size);
    extern void sm_register(void *user_vaddr, unsigned int size);
    extern void sm_write(void *user_vaddr, unsigned int size);
    extern void sm_write_once(void *user_vaddr, unsigned int size);
    extern void sm_deregister(void *user_vaddr, unsigned int size);

    extern void sm_assert_8b(void *user_vaddr);
    extern void sm_register_8b(void *user_vaddr);
    extern void sm_write_8b(void *user_vaddr);
    extern void sm_write_once_8b(void *user_vaddr);
    extern void sm_deregister_8b(void *user_vaddr);

    extern void sm_lock_safe_region (void);
    extern void sm_unlock_safe_region (void);
    #endif
#ifdef __cplusplus
}
#endif


#ifdef OTWM_DEBUG
#define otwm_debug(fmt, ...)                                                   \
        do {                                                                   \
                printf("[OTWM DEBUG] " fmt, ##__VA_ARGS__);          \
        } while (0)
#else
#define otwm_debug(fmt, ...)
#endif
