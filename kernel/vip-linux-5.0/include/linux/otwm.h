#ifdef CONFIG_OTWM
#ifndef _LINUX_OTWM_H
#define _LINUX_OTWM_H
#include <linux/printk.h>

#include <linux/mm.h>
#include <linux/kernel.h>

//#define OTWM_INFO
//#define OTWM_DEBUG
//#define OTWM_REPORT
#define CONFIG_OTWM_ENABLE_XOM

#define SHADOW_ADDR 0x00003F03F03EF000
#define SHADOW_SIZE 0x00003F03F03EF000
#define BITMAP_ADDR 0x00007E07E07DE000
#define BITMAP_SIZE 0x000001F81F81F780

//USER code region - DO NOTHING - LEAVE ALONE
//start 0x0000 0000 0000 1000 >> PAGE_ALIGN >> 0x0000 0000 0000 1000
//size  0x0000 3F03 F03E F6B0 >> PAGE_ALIGN >> 0x0000 3F03 F03F 1000
// DO NOTHING - LEAVE ALONE

//map SHADOW region
//start 0x0000 3F03 F03E F6B0 >> PAGE_ALIGN >> 0x0000 3F03 F03F 1000
//size  0x0000 3F03 F03E F6B0 >> PAGE_ALIGN >> 0x0000 3F03 F03E F000
//end   0x0000 7E07 E07E 0000

//map BITMAP region
//start 0x0000 7E07 E07E 0000
//size  0x0000 01F8 1F82 0000
//end   0x0000 7FFF FFFF F000

//map BITMAP region
//XXX do we need MAP_ANONYMOUS | MAP_PRIVATE ?
//mmap_region(file,addr,len,flag,pgoff,uf)
//otwm_ret = vm_mmap(NULL, 0x00003F03F03F1000, 0x1F81F820000, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, 0);

// unused variables - delete later if we really don't need it
//static unsigned long otwm_stack_offset = 0x3ffe00000000;
//static unsigned long otwm_shared_lib_offset = 0x1fff00000000;


/* Set %gs to start of static SHADOW REGION */
int otwm_set_gs_shadow_region(struct task_struct *tsk);

#ifdef OTWM_REPORT
#define otwm_report(fmt, ...)                                                   \
        do {                                                                   \
                printk(KERN_INFO "[OTWM REPORT] " fmt, ##__VA_ARGS__);          \
        } while (0)
#else
#define otwm_report(fmt, ...) no_printk(fmt, ##__VA_ARGS__)
#endif

#ifdef OTWM_INFO
#define otwm_info(fmt, ...)                                                   \
        do {                                                                   \
                printk(KERN_INFO "[OTWM INFO] " fmt, ##__VA_ARGS__);          \
        } while (0)
#else
#define otwm_info(fmt, ...) no_printk(fmt, ##__VA_ARGS__)
#endif

#ifdef OTWM_DEBUG
#define otwm_debug(f, a...)                                                   \
        do {                                                                   \
                printk(KERN_DEBUG "[OTWM DEBUG (%s, %d): %s:] ", __FILE__,    \
                       __LINE__, __func__);                                    \
                printk(KERN_DEBUG f, ##a);                                     \
        } while (0)
#else
#define otwm_debug(fmt, ...) no_printk(fmt, ##__VA_ARGS__)
#endif

#endif /* __LINUX_OTWM_H */
#endif /* CONFIG_OTWM */

