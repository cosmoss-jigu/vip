#include <linux/otwm.h>
#include <linux/syscalls.h>

#define SYSCALL_OTWM_TEST_XMMAP_PROTO 0
unsigned long __sys_otwm_test_xmmap_proto(unsigned long **p_kaddr){
	otwm_info("calling syscall test %s\n",__func__);
	return -1;
}

SYSCALL_DEFINE1(otwm_test, unsigned long, cmd)
{
        static unsigned long uaddr;
	static unsigned long *kaddr;
	char *exe_path_name;
	struct file *f;
	unsigned long ret;

	exe_path_name = "/home/kjelesnianski/host/manual-tests/a.out";
	ret = 0;
	otwm_info("cmd = %ld\n", cmd);

        switch (cmd) {
        case SYSCALL_OTWM_TEST_XMMAP_PROTO:
                ret = __sys_otwm_test_xmmap_proto(&kaddr);
                if (ret != -1)
                        uaddr = ret;
                break;
	}
	return ret;
}


/* Assign Shadow Region start to %gs register of process */
int otwm_set_gs_shadow_region(struct task_struct *tsk){
	unsigned long sr_base;
	int cpu, err;

	/* Set %gs register */
        cpu = get_cpu();
        tsk->thread.gsindex = 0;
        tsk->thread.gsbase = SHADOW_ADDR;
        load_gs_index(0);
        err = wrmsrl_safe(MSR_KERNEL_GS_BASE, SHADOW_ADDR);
        put_cpu();

	//otwm_info("shadow region  PID[%d] SR_base[%#llx]\n", tsk->pid, SHADOW_ADDR);
	//otwm_info("shadow PID[%d] tsk->thread.gsbas[%#llx]  err[%d[\n", tsk->pid, tsk->thread.gsbase, err);
	return err;
}
EXPORT_SYMBOL(otwm_set_gs_shadow_region);
