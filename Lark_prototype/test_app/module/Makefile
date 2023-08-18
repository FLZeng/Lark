ifneq ($(KERNELRELEASE),)
obj-m :=test_driver.o
else
KDIR := ../../linux
all:
	make -C $(KDIR) M=$(PWD) modules
clean:
	rm -f *.ko *.o *.mod *.mod.o *.mod.c *.symvers *.order .*cmd
endif
