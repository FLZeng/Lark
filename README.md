# Lark: Verified Cross-Domain Access Control for TEE

## 1 Artifact Description

The artifact of the *Lark paper* includes the Lark module, the source code of Lark prototype, and experimental data. The directory structure is as follows:

```
|-- Lark
    |-- Lark_model
        |-- Lark.thy				# Lark formal model in Isabelle/HOL
    |-- Lark_prototype
        |-- patches
            |-- apply_patches.sh	# scripts for applying patches
            |-- xxx.patch			# patches of OP-TEE components
        |-- test_app
            |-- test_app.c			# source code of test applicaton
            |-- module				# source code of test driver
        |-- qemu_v8.xml				# manifest specifing the revision of OP-TEE components
    |-- sharefs						# shared filesystem for evaluation
        |-- test_app				# binary of test applicaton
        |-- ubuntu-focal			# ubuntu-focal root filesystem
        |-- chroot_ubuntu.sh		# chroot script
        |-- un_chroot.sh			# unchroot script
    |-- results						# experimental results data
```

## 2 Environment Setup

The environment can be a physical or virtual machine in the following minimal configuration:

- OS: Ubuntu 20.04 LTS with GUI
- CPU: 4-core Intel® Core™ i7-10700 CPU @ 2.90GHz
- RAM: 4GB
- Disk: 30GB

Notes:

- The GUI must be installed on the Ubuntu because OP-TEE starts xterm when it runs.
- For faster compilation, we recommend a processor with 8 cores or more.

### 2.1 Pre-configured VM image

A configured VM image is provided and can be downloaded from: https://zenodo.org/record/8265887/files/Ubuntu_Lark.vmdk

Create a VM in VMWare Workstation that meets the minimum configuration requirements and use the provided image as the disk for the VM. The username for the VM is `root` and password is `123456`.

This README file exists on the desktop of the `root` user of the VM.

## 3 Getting Started

You can start from scratch or use the VM image we provide.

If you are using the provided VM image, the first 6 steps below are not required and you can skip to the **compile and run** step.

The following commands can be executed in the ssh text interface, but remember to log into the GUI with the same user first.

### 3.1 Install dependency packages

```
# apt-get install android-tools-adb android-tools-fastboot autoconf \
        automake bc bison build-essential ccache codespell \
        cscope curl device-tree-compiler expect flex ftp-upload gdisk iasl \
        libattr1-dev libcap-dev libcap-ng-dev \
        libfdt-dev libftdi-dev libglib2.0-dev libgmp-dev libhidapi-dev \
        libmpc-dev libncurses5-dev libpixman-1-dev libssl-dev libtool make \
        mtools netcat ninja-build python-crypto python3-crypto python-pyelftools \
        python3-pycryptodome python3-pyelftools python-serial python3-serial \
        rsync unzip uuid-dev xdg-utils xterm xz-utils zlib1g-dev
```

### 3.2 Clone Lark

```
# export LARK_DIR="/data/Lark"
# mkdir /data
# git clone https://github.com/FLZeng/Lark.git ${LARK_DIR}
```

### 3.3 Sync OP-TEE source code

```
# cd ${LARK_DIR}/Lark_prototype
# repo init -u https://github.com/OP-TEE/manifest.git -m qemu_v8.xml
# cp qemu_v8.xml .repo/manifests/qemu_v8.xml
# repo sync
```

### 3.4 Download toolchains

```
# cd ${LARK_DIR}/Lark_prototype/build
# make toolchains
```

### 3.5 Apply Lark pathes

```
# cd ${LARK_DIR}/Lark_prototype
# sh patches/apply_patches.sh
```

If you are using **Ubuntu 22.04 LTS or newer release**, an additional patch related to brotli is required:

```
# cd ${LARK_DIR}/Lark_prototype/edk2
# git apply ${LARK_DIR}/Lark_prototype/patches/edk2.diff
```

### 3.6 Download ubuntu-focal rootfs

A ubuntu-focal root filesystem with pre-installed evaluation applications is available for download: https://zenodo.org/record/8265887/files/ubuntu-focal-arm64-root.tar.xz

Note that this is for the normal world OS, and is different from the VM image mentioned above.

Unpack it to the `sharefs` directory:

```
# tar xf ubuntu-focal-arm64-root.tar.xz -C ${LARK_DIR}/sharefs
```



The steps below are the same for both using the VM image and from scratch.

### 3.7 Compile and run

```
# export LARK_DIR="/data/Lark"
# cd ${LARK_DIR}/Lark_prototype/build
# make run QEMU_VIRTFS_ENABLE=y QEMU_VIRTFS_HOST_DIR=${LARK_DIR}/sharefs/ -j $(nproc)
```

Once the compilation is complete, a QEMU VM will be launched to run OP-TEE. When you see the following message, type a `c` and `enter`:

```
cd /data/Lark/Lark_prototype/build/../out/bin && /data/Lark/Lark_prototype/build/../qemu/build/aarch64-softmmu/qemu-system-aarch64 \
        -nographic \
        -serial tcp:localhost:54320 -serial tcp:localhost:54321 \
        -smp 2 \
        -s -S -machine virt,secure=on,gic-version=3,virtualization=false \
        -cpu max,sve=off \
        -d unimp -semihosting-config enable=on,target=native \
        -m 1057 \
        -bios bl1.bin           \
        -initrd rootfs.cpio.gz \
        -kernel Image -no-acpi \
        -append 'console=ttyAMA0,38400 keep_bootcon root=/dev/vda2 ' \
         \
        -object rng-random,filename=/dev/urandom,id=rng0 -device virtio-rng-pci,rng=rng0,max-bytes=1024,period=1000 -fsdev local,id=fsdev0,path=/data/Lark/sharefs/,security_model=none -device virtio-9p-device,fsdev=fsdev0,mount_tag=host -netdev user,id=vmnic -device virtio-net-device,netdev=vmnic
QEMU 6.0.0 monitor - type 'help' for more information
(qemu)
```

Then in the GUI, you can see that two xterms are launched, one for normal world and the other for secure world.

When the following prompt appears in the normal world terminal, enter root to log in without a password:

```
Welcome to Buildroot, type root or test to login
buildroot login:
```

### 3.8 Examine basic functionality

Execute the following command in normal world terminal to mount sharefs:

```
# mkdir sharefs && mount -t 9p -o trans=virtio host sharefs && cd sharefs && ls -l
```

Run the test application:

```
# insmod test_app/test_driver.ko
# ./test_app/test_app
```

Note: Use `test_driver.ko` in patched OP-TEE and  `test_driver_native.ko` in native OP-TEE.

*test_app* accepts the following input commands:

- r/w: Read/write the buffer in the kernel mode
- ro/wo/rw/rwn: Set the buffer as kernel read-only/write-only/read-write/inaccessible
- t: Run micro-benchmark tests
- q: Exit the test application

Enter the following commands `r`, `w`, `wo`, `r` in sequence, and you can see that the kernel can no longer read the buffer when it is set to write-only:

```
# ./test_app/test_app
page size: 4096
rbuf addr: 0xffff83aaf000
wbuf addr: 0xffff83aae000
[  169.694769] enter cdd_open!
[  169.695052] led = 5
open successed fd = 3
starting to test /dev/cdd...
waiting for cmd [r/w/ro/wo/rw/rwn/t/q]: r
kernel copy from user
waiting for cmd [r/w/ro/wo/rw/rwn/t/q]: w
kernel copy to user
waiting for cmd [r/w/ro/wo/rw/rwn/t/q]: wo
mprotect set rbuf PROT_WRITE, ret = 0
mprotect set wbuf PROT_WRITE, ret = 0
waiting for cmd [r/w/ro/wo/rw/rwn/t/q]: r
[  178.291834] Unable to handle kernel access to user memory outside uaccess routines at virtual address 0000ffff83aae000
```

You can also chroot to the ubuntu-focal distribution to run pre-installed real-world applications:

```
# ./chroot_ubuntu.sh
```

The detailed evaluation experiments are described in the next section.

## 4 Reproducibility Instructions

The evaluation experiments include micro-benchmark, xtest, TAs, and real-world applications. The following commands are all executed in the normal world terminal.

The [`results/`](results/) directory contains all the experimental results data.

### 4.1 Micro-benchmarks

Run *test_app* and enter the `t` command to test the time to perform 10,000 read/write operations respectively:

```
# ./test_app/test_app
waiting for cmd [r/w/ro/wo/rw/rwn/t/q]: t

test rounds: 10000
test type [0-read, 1-write]: 0
test rounds: 10000, time = 0.400119s

waiting for cmd [r/w/ro/wo/rw/rwn/t/q]: t

test rounds: 10000
test type [0-read, 1-write]: 1
test rounds: 10000, time = 0.402743s
```

### 4.2 xtest suite

The execution time of the following test cases was tested: Basic OS features, TEE Internal client API, TEE Internal API, Global platform TEEC, Storage, Key derivation, and mbedTLS.

All tests take `real time (s)` in the results.

**Basic OS features**

```
# time xtest -t regression 1006
```

**TEE Internal client API**

```
# time xtest -t regression 1008
```

**TEE Internal client API**

```
# time xtest -t regression _40 _41
```

**Global platform TEEC**

```
# time xtest -t regression 5006
```

**Storage**

```
# time xtest -t regression _60
```

**Key derivation**

```
# time xtest -t regression 8001
```

**mbedTLS**

```
# time xtest -t regression _81
```

### 4.3 TAs

The performance of **SHA256**, **AES-256**, and **Secure Storage** are tested under different buffer sizes. For all TAs, the values of `buffer size` are: 256, 512, 1024, 2048, 4096, 8192, and 16384 in Byte.

**SHA256**

```
# xtest --sha-perf -n 1000 -a SHA256 -s BUFFER_SIZE
```

Take the `mean time (μs)` in the result.

**AES-256**

```
# xtest --aes-perf -n 1000 -k 256 -s BUFFER_SIZE
```

Take the `mean time (μs)` in the result.

**Secure Storage**

```
# xtest -t benchmark 1001 1002
```

Take the `Speed (kB/s)` in the result.

### 4.4 Real-world applications

Before running the application tests, mount sharefs and chroot to ubuntu-focal in the normal world terminal:

```
# mkdir sharefs && mount -t 9p -o trans=virtio host sharefs && cd sharefs && ls -l
# ./chroot_ubuntu.sh
```

**Memcached**

```
# service memcached start
# mcperf --conn-rate=1000 --call-rate=1000 --num-calls=10 --num-conns=1000 --sizes=d4096 --method=get
# mcperf --conn-rate=1000 --call-rate=1000 --num-calls=10 --num-conns=1000 --sizes=d4096 --method=set
```

Take the ` Response rate (rsp/s)` in the result.

**Redis**

```
# service redis-server start
# redis-benchmark -n 10000 -P 16 -c 100 -d 4096 -t set,get -q
```

Take the `Requests per second` in the result.

**sysbench**

```
# sysbench --test=memory --memory-block-size=4096K --memory-total-size=100G --memory-access-mode=rnd --num-threads=2 --memory-oper=read run
# sysbench --test=memory --memory-block-size=4096K --memory-total-size=100G --memory-access-mode=rnd --num-threads=2 --memory-oper=write run
```

Take the `Throughput (MiB/sec)` in the results.

**MBW**

```
# mbw -q -n 10 128
```

Take the `AVG bandwidth (MiB/s)` for each of the **MEMCPY**, **DUMB**, and **MCBLOCK** operations in the result.

**Bandwidth**

```
# bandwidth64 --faster
```

Take the `bandwidth (MB/s)` of **sequential read (64-bit)**, **sequential write (64-bit)**, and **random read (64-bit)** for `size=128 MB` in the result.

**STREAM**

```
# stream
```

Take the `Best Rate (MB/s)` of each operation of **Copy**, **Scale**, **Add** and **Triad** in the result.

### 4.5 Normalization

For each test, obtain the results in native OP-TEE (`a`) and OP-TEE with Lark (`b`) separately, and then take `b/a` as the normalized value.

Execute the following commands to restore the native OP-TEE environment:

```
# cd ${LARK_DIR}/Lark_prototype
# sh patches/revert_patches.sh
```

Then redo the **compile and run** and subsequent steps.