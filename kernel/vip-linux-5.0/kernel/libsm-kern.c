#include <linux/libsm-kern.h>

int has_imprinted_elf_eflag(struct file *file)
{
    unsigned char buf[64];
    size_t flag_idx;
    loff_t pos = 0;

    if(kernel_read(file, buf, 64, &pos) != 64)
        return 0;
    
    if (buf[0] != 0x7f || buf[1] != 'E' || buf[2] != 'L' || buf[3] != 'F')
        return false;

    if (buf[4] == 0x01)
        flag_idx = 36;
    else
	flag_idx = 48;

    return buf[flag_idx] == (unsigned char)0xBE;
}

int is_imprinted_mmap(struct file *file, unsigned long addr, unsigned long prot,unsigned long flags)
{
    if (file == NULL)
      return 0;

    //printk(KERN_INFO "%s => %lx\n", file->f_path.dentry->d_iname, addr);
    //printk(KERN_INFO "start_brk => %lx\n", current->mm->start_brk);
    //printk(KERN_INFO "brk => %lx\n", current->mm->brk);
    //printk(KERN_INFO "start_stack => %lx\n", current->mm->start_stack);
    if (has_imprinted_elf_eflag(file)) {
      return 1;
    } 

    return 0;
}

int is_otwm(struct file *file)
{
    if (file == NULL)
      return 0;

    if (has_imprinted_elf_eflag(file)) {
      return 1;
    }

    return 0;
}
