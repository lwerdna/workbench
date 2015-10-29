# IF KERNELRELEASE IS NON-EMPTY, WE'RE BUILDING IN-KERNEL
ifneq ($(KERNELRELEASE),)

# we specify obj-m, the m meaning "build as a module" and list the name of resulting object
# (which gets changed from .o -> .ko)
obj-m  := proctest.o
# now we name <module>-objs to list the modules involved to make <module>
proctest-objs := main.o

# ELSE KERNELRELEASE IS EMPTY, WE'RE BUILDING OUT-KERNEL
else
all: module 

module:
	KBUILD_VERBOSE=1 $(MAKE) -C $(KERNEL_DIR) M=`pwd`

clean:
	$(MAKE) -C $(KERNEL_DIR) M=`pwd` clean
endif

