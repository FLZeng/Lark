#include <linux/init.h>
#include <linux/module.h>
#include <linux/fs.h>
#include <linux/cdev.h>
#include <linux/device.h>
#include <linux/slab.h>
#include <linux/uaccess.h>


MODULE_LICENSE("GPL");
#define DEBUG		false
#define CDD_MAJOR	200    //cat /proc/devices and find one unused
#define CDD_MINOR	0
#define CDD_COUNT	10
dev_t dev = 0;
u32 cdd_major = 0;
u32 cdd_minor = 0;

struct class *dev_class = NULL;
#define BUF_SIZE	100
struct cdd_cdev{
	struct cdev cdev;
	struct device *dev_device;
	u8 led;
	
	char kbuf[BUF_SIZE];
};

struct cdd_cdev *cdd_cdevp = NULL;


int cdd_open(struct inode* inode, struct file *filp)
{
	struct cdd_cdev *pcdevp = NULL;
	printk("enter cdd_open!\n");
	
	pcdevp = container_of(inode->i_cdev, struct cdd_cdev, cdev);
	printk("led = %d\n", pcdevp->led);
	
	filp->private_data = pcdevp;
	
	return 0;
}

ssize_t cdd_read(struct file *filp, char __user *buf, size_t count, loff_t *offset)
{
	int ret = 0;
	
	struct cdd_cdev *cdevp = filp->private_data;
	if (DEBUG) {

		printk("enter cdd_read!\n");
		printk("driver call: memcpy kbuf -> rbuf\n");
		printk("[cdd_read] buf addr: %p\n", buf);
	}
	// #define ARM64_ALT_PAN_NOT_UAO			10
	// asm(ALTERNATIVE("nop", SET_PSTATE_PAN(0), ARM64_ALT_PAN_NOT_UAO, CONFIG_ARM64_PAN));
	//ret = copy_to_user(buf, cdevp->kbuf, count);
	ret = memcpy(buf, cdevp->kbuf, count);
	return ret;
}

ssize_t cdd_write(struct file *filp, const char __user *buf, size_t count, loff_t *offset)
{
	int ret = 0;
	struct cdd_cdev *cdevp = filp->private_data;	
	if (DEBUG) {
		printk("enter cdd_write!\n");
		printk("driver call: memcpy wbuf -> kbuf\n");
		printk("[cdd_write] buf addr: %p\n", buf);
	}
	
	//ret = copy_from_user(cdevp->kbuf, buf, count);
	ret = memcpy(cdevp->kbuf, buf, count);
	
	return ret;
}

int cdd_release(struct inode *inode, struct file *filp)
{
	printk("enter cdd_release!\n");
	return 0;
}

struct file_operations cdd_fops = {
	.owner = THIS_MODULE,
	.open = cdd_open,
	.read = cdd_read,
	.write = cdd_write,
	.release = cdd_release,
	};

int __init cdd_init(void)
{
	int ret = 0;
	int i = 0;
	
	if(cdd_major){
		dev = MKDEV(CDD_MAJOR, CDD_MINOR);
		ret = register_chrdev_region(dev, CDD_COUNT, "cdd_demo");
	}else{
		ret = alloc_chrdev_region(&dev, cdd_minor, CDD_COUNT, "cdd_demo02");
	}
	
	if(ret < 0){
		printk("register_chrdev_region failed!\n");
		goto failure_register_chrdev;
	}
	cdd_major = MAJOR(dev);
	printk("cdd_major = %d\n", cdd_major);
	
	cdd_cdevp = kzalloc(sizeof(struct cdd_cdev)*CDD_COUNT, GFP_KERNEL);
	if(IS_ERR(cdd_cdevp)){
		printk("kzalloc failed!\n");
		goto failure_kzalloc;
	}
	dev_class = class_create(THIS_MODULE, "cdd_class");
	if(IS_ERR(dev_class)){
		printk("class_create failed!\n");
		goto failure_dev_class;
	}
	for(i=0; i<CDD_COUNT; i++){
		cdev_init(&(cdd_cdevp[i].cdev), &cdd_fops);
		cdev_add(&(cdd_cdevp[i].cdev), dev+i, 1);
		device_create(dev_class, NULL, dev+i, NULL, "cdd%d", i);
		cdd_cdevp[i].led = i;
		
	}
	
	return 0;
failure_dev_class:
	kfree(cdd_cdevp);
failure_kzalloc:
	unregister_chrdev_region(dev, CDD_COUNT);
failure_register_chrdev:
	return ret;
}

void __exit cdd_exit(void)
{
	int i = 0;
	for(; i < CDD_COUNT; i++){
		device_destroy(dev_class, dev+i);
		cdev_del(&(cdd_cdevp[i].cdev));
	}
	class_destroy(dev_class);
	kfree(cdd_cdevp);
	unregister_chrdev_region(dev, CDD_COUNT);
	
}	

module_init(cdd_init);
module_exit(cdd_exit);
