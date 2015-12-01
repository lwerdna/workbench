#include <linux/module.h>
#include <linux/kernel.h>

static int __init hello_init(void)
{
    printk("%s()\n", __func__);
    return 0;
}

static void __exit hello_exit(void)
{
    printk("%s()\n", __func__);
}

module_init(hello_init);
module_exit(hello_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("andrewl");
