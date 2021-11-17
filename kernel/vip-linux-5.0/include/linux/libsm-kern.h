#ifndef __LINUX_LIBSM_KERN_H
#define __LINUX_LIBSM_KERN_H
#include <linux/otwm.h>
#include <linux/kernel.h>
#include <linux/fs.h>

int has_imprinted_elf_eflag(struct file *file);
int is_imprinted_mmap(struct file *file, unsigned long addr, unsigned long prot,
				      unsigned long flags);
int is_otwm(struct file *file);


#endif /* __LINUX_LIBSM_KERN_H */
