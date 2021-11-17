#define _GNU_SOURCE
#include <sys/mman.h>
#include <asm/prctl.h>
#include <sys/prctl.h>

#include "libsm.h"

#ifndef likely
#define likely(x) __builtin_expect((unsigned long)(x), 1)
#endif
#ifndef unlikely
#define unlikely(x) __builtin_expect((unsigned long)(x), 0)
#endif

// helper functions
void otwm_die(const char *msg) {
     fprintf(stderr, "[errno: %d] %s\n", errno, msg);

     //Code that will cause segfault crash
     //This intentional crash works better for getting GDB backtrace.
     volatile int *p = NULL;
     *p = 0;
     exit(EXIT_FAILURE);
}

#define area_sz()         ((u64)AREA_SIZE)                     /* shadow region size */
#define bitmap_addr(addr) ((u64)((((u64)(addr)) >> 5) & ~0x3)) /* address in status bitmap */
#define bitmap_idx(addr)  ((u64)((((u64)(addr)) & 0xf8) >> 2)) /* index in a 8-byte chunk  */
#define SLOT32_SZ         256
#define SLOT32_MASK       ~0xFF

// uninit: 00
// reg:    01
// wrt:    11
// wrtf:   10


static inline u64 __attribute__((always_inline)) rd_shadow_value(void *pos)
{
	u64 val;
	asm volatile (
		"mov %%gs:0x0(%[pos]), %[val]\n\t"
		: [val] "=r" (val)
		: [pos] "r" ((u64)pos)
	);
	return val;
}

static inline void __attribute__((always_inline)) set_shadow_value(void *pos, u64 val)
{
	asm volatile (
		"movq %[val], %%gs:0x0(%[pos])\n\t"
		:
		: [val] "r" (val),
		  [pos] "r" ((u64)pos)
	);
}

static inline unsigned char __attribute__((always_inline)) rd_bit(u64 nr, u64 *addr)
{
	unsigned char bit;

	asm volatile (
		"btq %[nr], %[addr]\n\t"
		:
		: [addr] "rm" (*addr),
		  [nr] "r" (nr));
	asm volatile (
		"setc %[bit]\n\t"
		: [bit] "+rm" (bit));
	return bit;
}

static inline unsigned char __attribute__((always_inline)) rd_shadow_bit0(u64 *addr)
{
	unsigned char bit;

	asm volatile (
		"btq %[bitmap_idx], %%gs:(%[bitmap_addr],%[area_sz])\n\t"
		:
		: [bitmap_idx]  "r" (bitmap_idx(addr)),
		  [bitmap_addr] "r" (bitmap_addr(addr)),
		  [area_sz]     "Ir" (area_sz()));
	asm volatile (
		"setc %[bit]\n\t"
		: [bit] "+rm" (bit));
	return bit;
}

static inline unsigned char __attribute__((always_inline)) rd_shadow_bit1(u64 *addr)
{
	unsigned char bit;

	asm volatile (
		"btq %[bitmap_idx], %%gs:(%[bitmap_addr],%[area_sz])\n\t"
		:
		: [bitmap_idx]  "r" (bitmap_idx(addr)+1),
		  [bitmap_addr] "r" (bitmap_addr(addr)),
		  [area_sz]     "Ir" (area_sz()));
	asm volatile (
		"setc %[bit]\n\t"
		: [bit] "+rm" (bit));
	return bit;
}

static inline void __attribute__((always_inline)) set_bit(u64 nr, u64 *addr)
{
	asm volatile (
		"btsq %[nr], %[addr]\n\t"
		: [addr] "+rm" (*addr)
		: [nr] "Ir" (nr)
		: "memory");
}

static inline void __attribute__((always_inline)) set_shadow_bit0(u64 *addr)
{
	asm volatile (
		"btsq %[bitmap_idx], %%gs:(%[bitmap_addr],%[area_sz])\n\t"
		:
		: [bitmap_idx]  "r" (bitmap_idx(addr)),
		  [bitmap_addr] "r" (bitmap_addr(addr)),
		  [area_sz]     "Ir" (area_sz())
		: "memory");
}

static inline void __attribute__((always_inline)) set_shadow_bit1(u64 *addr)
{
	asm volatile (
		"btsq %[bitmap_idx], %%gs:(%[bitmap_addr],%[area_sz])\n\t"
		:
		: [bitmap_idx]  "r" (bitmap_idx(addr)+1),
		  [bitmap_addr] "r" (bitmap_addr(addr)),
		  [area_sz]     "Ir" (area_sz())
		: "memory");
}

static inline void __attribute__((always_inline)) clear_bit(u64 nr, u64 *addr)
{
	asm volatile (
		"btrq %[nr],%[addr]\n\t"
		: [addr] "+rm" (*addr)
		: [nr] "Ir" (nr));
}

static inline void __attribute__((always_inline)) clear_shadow_bit0(u64 *addr)
{
	asm volatile (
		"btrq %[bitmap_idx], %%gs:(%[bitmap_addr],%[area_sz])\n\t"
		:
		: [bitmap_idx]  "r" (bitmap_idx(addr)),
		  [bitmap_addr] "r" (bitmap_addr(addr)),
		  [area_sz]     "Ir" (area_sz())
		: "memory");
}

static inline void __attribute__((always_inline)) clear_shadow_bit1(u64 *addr)
{
	asm volatile (
		"btrq %[bitmap_idx], %%gs:(%[bitmap_addr],%[area_sz])\n\t"
		:
		: [bitmap_idx]  "r" (bitmap_idx(addr)+1),
		  [bitmap_addr] "r" (bitmap_addr(addr)),
		  [area_sz]     "Ir" (area_sz())
		: "memory");
}


static inline void __attribute__((always_inline)) set_registered(void *user_vaddr)
{
	// 00 -> 01
	set_shadow_bit1(user_vaddr);

// COMPLETING THE FULL REGISTER
	clear_shadow_bit0(user_vaddr);
}

static inline void __attribute__((always_inline)) set_written(void *user_vaddr)
{
	// 01 -> 11
	set_shadow_bit0(user_vaddr);

// COMPELETING FULL WRITE
	set_shadow_bit1(user_vaddr);
}

static inline void __attribute__((always_inline)) set_written_once(void *user_vaddr)
{
	// 01 -> 10
	// 11 -> 10
	set_shadow_bit0(user_vaddr);
	clear_shadow_bit1(user_vaddr);
}

static inline void __attribute__((always_inline)) set_unregistered(void *user_vaddr)
{
	// * -> 00
	clear_shadow_bit0(user_vaddr);
	clear_shadow_bit1(user_vaddr);
}


static inline bool __attribute__((always_inline)) is_registered(void *user_vaddr)
{
	// 01, 11, 10
	return rd_shadow_bit1(user_vaddr) || rd_shadow_bit0(user_vaddr);
}

static inline bool __attribute__((always_inline)) is_locked(void *user_vaddr)
{
	// 10
	return rd_shadow_bit0(user_vaddr) && !rd_shadow_bit1(user_vaddr);
}


static inline bool __attribute__((always_inline)) is_written(void *user_vaddr)
{
	// 10, 11
	return rd_shadow_bit0(user_vaddr);
}

static inline bool __attribute__((always_inline)) is_writable(void *user_vaddr)
{
	// 01, 11
	return rd_shadow_bit1(user_vaddr);
}

inline bool __attribute__((always_inline)) is_safe_region_locked (void)
{
	#ifdef MPK
	unsigned int edx, pkru;

	asm volatile (
		".byte 0x0f, 0x01, 0xee"
		: "=a" (pkru), "=d" (edx)
		: "c" (0)
	);

	return pkru == 0x8;
	#else
	return false;
	#endif
}

// MPK operations
inline void __attribute__((always_inline)) sm_lock_safe_region (void) {
	#ifdef MPK
	if (!is_safe_region_locked()) {
		asm volatile (
			".byte 0x0f, 0x01, 0xef"
			: /* No Outputs */
			: "a" (0x8), "c" (0), "d" (0) /* Inputs */ // "a" is (PKEY_DISABLE_WRITE (a.k.a 0x2) << 2) = 0x8
		);
	}
	#endif
}

inline void __attribute__((always_inline)) sm_unlock_safe_region (void) {
	#ifdef MPK
	if (is_safe_region_locked()) {
		asm volatile (
			".byte 0x0f, 0x01, 0xef"
			: /* No Outputs */
			: "a" (0), "c" (0), "d" (0) /* Inputs */   // "a" is (rights << 2)
		);
	}
	#endif
}


// API calls
inline void __attribute__((always_inline)) sm_register(void *user_vaddr, unsigned int size) {
	for (u64 i = 0; i < size; i += EIGHT_BYTES) {
		if (!is_registered(user_vaddr + i)) {
			sm_unlock_safe_region();
			set_registered(user_vaddr + i);
		}
	}
}

inline void __attribute__((always_inline)) sm_register_8b(void *user_vaddr) {
#ifdef NON_REPETITIVE
	if (!is_registered(user_vaddr)) {
		sm_unlock_safe_region();
		set_registered(user_vaddr);
	}
#else
	sm_unlock_safe_region();
	set_registered(user_vaddr);
#endif

#ifndef BB_COALESING
	sm_lock_safe_region ();
#endif	
}

inline void __attribute__((always_inline)) sm_assert(void *user_vaddr, unsigned int size) {
	if (unlikely(!is_written(user_vaddr))) {
		otwm_die("Asserted value is never written\n");
	}

	if (memcmp(user_vaddr + (u64)AREA_SIZE, user_vaddr, size) != 0) {
		otwm_die("secure memory value mismatched\n");
	}
}

inline void __attribute__((always_inline)) sm_assert_8b(void *user_vaddr) {
	if (!is_written(user_vaddr) || rd_shadow_value(user_vaddr) != *((u64 *) user_vaddr)) {
		return;
	}

}



inline void __attribute__((always_inline)) sm_write(void *user_vaddr, unsigned int size) {
	sm_unlock_safe_region();
	memcpy(user_vaddr, (unsigned long*)(((unsigned long) HYPR_START) + ((unsigned long) user_vaddr)), size);
	for (u64 i = 0; i < size; i += EIGHT_BYTES) {
		if (!is_registered(user_vaddr + i)) {
			set_registered(user_vaddr + i);
		}
		set_written(user_vaddr + i);
	}
}

inline void __attribute__((always_inline)) sm_write_8b(void *user_vaddr) {
#ifdef NON_REPETITIVE
	if (is_written(user_vaddr)) {
		// updating write
		if (rd_shadow_value((u64) user_vaddr) != *((unsigned long *) user_vaddr)) {
			sm_unlock_safe_region();
			unsigned long hyperspace_addr = ((unsigned long) HYPR_START) + ((unsigned long) user_vaddr);
			*((unsigned long*)hyperspace_addr) = *((unsigned long*) user_vaddr);
		}
	}
	else {
		// first time writing
		sm_unlock_safe_region();
		unsigned long hyperspace_addr = ((unsigned long) HYPR_START) + ((unsigned long) user_vaddr);
		*((unsigned long*)hyperspace_addr) = *((unsigned long*) user_vaddr);
		set_written(user_vaddr);
	}
#else
	sm_unlock_safe_region();
	unsigned long hyperspace_addr = ((unsigned long) HYPR_START) + ((unsigned long) user_vaddr);
	*((unsigned long*)hyperspace_addr) = *((unsigned long*) user_vaddr);
	set_written(user_vaddr);
#endif

#ifndef BB_COALESING
	sm_lock_safe_region ();
#endif
}

inline void __attribute__((always_inline)) sm_write_once(void *user_vaddr, unsigned int size) {
	sm_unlock_safe_region();
	memcpy(user_vaddr, (unsigned long*)(((unsigned long) HYPR_START) + ((unsigned long) user_vaddr)), size);
	for (u64 i = 0; i < size; i += EIGHT_BYTES) {
		if (unlikely(!is_writable(user_vaddr + i))) {
			otwm_die("secure memory address is either not registered and/or is locked\n");
		}
		set_written_once(user_vaddr + i);
	}
}

inline void __attribute__((always_inline)) sm_write_once_8b(void *user_vaddr) {
	if (!is_locked(user_vaddr)) {
		sm_register_8b(user_vaddr);
	}

	if (is_locked(user_vaddr)) {
		otwm_die("Secure memory address is locked\n");
	}

	set_written_once(user_vaddr);
	unsigned long hyperspace_addr = ((unsigned long) HYPR_START) + ((unsigned long) user_vaddr);
	*((unsigned long*)hyperspace_addr) = *((unsigned long*) user_vaddr);
}

inline void __attribute__((always_inline)) sm_deregister(void *user_vaddr, unsigned int size) {
	void *aligned_start, *aligned_end, *end;
	unsigned int aligned_size;

	if (unlikely(size == 0))
		return;

	aligned_start = (void*)(((u64)user_vaddr + (SLOT32_SZ - 1)) & SLOT32_MASK);
	end = user_vaddr + size;
	aligned_end = (void *)((u64)end & SLOT32_MASK);
	// sanity check
	if (aligned_end > HYPR_END || aligned_start > HYPR_END) {
		return;
	}
	aligned_size = aligned_end - aligned_start + 1;

	sm_unlock_safe_region();
	if (aligned_size != 0) {
		void *hyperspace = ((void *)bitmap_addr(user_vaddr)) + (2 * area_sz());
		void *hyperspace_end = hyperspace + (aligned_size >> 5);
		// sanity check
		if (hyperspace < BITMAP_START || hyperspace_end > HYPR_END) {
			return;
		}
		memset(hyperspace, 0, aligned_size >> 5);
	}

	if (aligned_start != user_vaddr) {
		u64 *addr = user_vaddr;
		for (; addr < aligned_start; addr++) {
			set_unregistered(addr);
		}
	}

	if (aligned_end != end) {
		u64 *addr = aligned_end;
		for (; addr < end; addr++) {
			set_unregistered(addr);
		}
	}
#ifndef BB_COALESING
	sm_lock_safe_region ();
#endif
}

inline void __attribute__((always_inline)) sm_deregister_8b(void *user_vaddr) {
	if (is_registered(user_vaddr)) {
		sm_unlock_safe_region();
		set_unregistered(user_vaddr);
	}

#ifndef BB_COALESING
	sm_lock_safe_region ();
#endif
}
