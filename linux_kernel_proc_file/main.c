#include <linux/module.h>
#include <linux/proc_fs.h>
#include <linux/printk.h> /* for printk() */
#include <asm/uaccess.h> /* for put_user() */

struct proc_dir_entry *pde = NULL;

//-----------------------------------------------------------------------------
// file ops
//-----------------------------------------------------------------------------
static int 
test_open(struct inode *inode, struct file *file) 
{
    printk("%s(inode=%p, file=%p)\n", __func__, inode, file);
    return 0;
}

static loff_t 
test_llseek(struct file *file, loff_t offset, int whence)
{
    printk("%s(file=%p, offs=%lld, whence=%d)\n", __func__, file, offset, 
        whence);

    loff_t newpos;

    switch(whence) {
      case 0: /* SEEK_SET - */
        newpos = offset;
        break;

      case 1: /* SEEK_CUR - seek relative */
        newpos = file->f_pos + offset;
        break;

      case 2: /* SEEK_END */
        //newpos = dev->size + offset;
        break;

      default: /* can't happen */
        return -EINVAL;
    }

    if (newpos < 0) return -EINVAL;
    file->f_pos = newpos;
    return newpos;
}

static ssize_t 
test_read(struct file *file, char __user *buf, size_t len, 
    loff_t *offset)
{
    printk("%s(file=%p, buf=%p, len=%zu, offs=%lld)\n", __func__, file, buf, len, 
        *offset);

    if(len >= 1) {
        copy_to_user(buf, "A", 1);
    }

    return 1;
}

static ssize_t 
test_write(struct file *file, const char __user *buf, size_t len, loff_t *offset)
{
    printk("%s(file=%p, buf=%p, len=%zu, offs=%lld)\n", __func__, file, buf, 
        len, *offset);
    return 0;
}
	
static int *test_release(struct inode *inode, struct file *file)
{
    printk("%s(inode=%p, file=%p)\n", __func__, inode, file);
    return 0;
}

static const struct file_operations test_fops = 
{
    .owner = THIS_MODULE, /* AKA __this_module, see export.h (inc by module.h) */
    .open = test_open,
    .read = test_read,
    .write = test_write,
    .llseek = test_llseek,
    .release = test_release
};

//-----------------------------------------------------------------------------
// driver entry/exit
//-----------------------------------------------------------------------------
static int __init test_init(void) 
{
    pde = proc_create(  "test", /* name */
            0, NULL, /* mode, parent */
            &test_fops /* file operations */
            );

    if(pde) return 0;
    else return -1;
}

static void __exit test_exit(void) 
{
    if(pde) {
        proc_remove(pde);
        pde = NULL;
    }
}

MODULE_LICENSE("GPL");
module_init(test_init);
module_exit(test_exit);
