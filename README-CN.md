# Lark: Verified Cross-Domain Access Control for TEE

## 1 说明

Lark 论文的 artifact 包括 Lark module、Lark 原型源码以及实验数据。整体目录结构如下：

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

## 2 环境设置

运行环境可以是以下最小配置的物理机或虚拟机：

- OS: Ubuntu 20.04 LTS with GUI
- CPU: 4-core Intel® Core™ i7-10700 CPU @ 2.90GHz
- RAM: 4GB
- Disk: 30GB

注意：

- Ubuntu 系统必须安装图形界面，因为 OP-TEE 运行时要启动 xterm。
- 为了加快编译速度，我们推荐8核以上的处理器。

### 2.1 预配置的 VM 镜像

预配置好的虚拟机镜像，可以从以下连接下载：https://zenodo.org/record/8265887/files/Ubuntu_Lark.vmdk

在 VMWare Workstation 中创建一个满足最小配置要求的虚拟机，并使用提供的镜像作为虚拟机的磁盘。虚拟机的用户名：`root`，密码：`123456`。

这份 README 文件存在于 VM 的 `root` 用户的桌面上。

## 3 Getting Started

可以从头开始或使用我们提供的 VM 镜像。

如果使用提供的 VM 镜像，以下前 6 个步骤不需要执行，直接跳到**编译与运行**步骤。

可以在 ssh 文本界面中执行下面的命令，但记得要先使用相同的用户登录图形界面。

### 3.1 安装依赖包

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

### 3.2 克隆 Lark

```
# export LARK_DIR="/data/Lark"
# mkdir /data
# git clone https://github.com/FLZeng/Lark.git ${LARK_DIR}
```

### 3.3 同步 OP-TEE 源码

```
# cd ${LARK_DIR}/Lark_prototype
# repo init -u https://github.com/OP-TEE/manifest.git -m qemu_v8.xml
# cp qemu_v8.xml .repo/manifests/qemu_v8.xml
# repo sync
```

### 3.4 下载 toolchains

```
# cd ${LARK_DIR}/Lark_prototype/build
# make toolchains
```

### 3.5 应用 Lark 补丁

```
# cd ${LARK_DIR}/Lark_prototype
# sh patches/apply_patches.sh
```

如果你使用的是 **Ubuntu 22.04 LTS 及以上的版本**，还需要额外打一个与 brotli 相关的补丁：

```
# cd ${LARK_DIR}/Lark_prototype/edk2
# git apply ${LARK_DIR}/Lark_prototype/patches/edk2.diff
```

### 3.6 下载 ubuntu-focal 根文件系统

我们提供了一个预装了性能评估应用程序的 ubuntu-focal 根文件系统，下载地址：https://zenodo.org/record/8265887/files/ubuntu-focal-arm64-root.tar.xz

请注意，这是给 normal world OS 使用的，不同于前面提到的 VM 镜像。

将它解压到 `sharefs` 目录下：

```
# tar xf ubuntu-focal-arm64-root.tar.xz -C ${LARK_DIR}/sharefs
```



从以下步骤开始，对于使用 VM 镜像和 from scratch 方法都是一样的。

### 3.7 编译与运行

```
# export LARK_DIR="/data/Lark"
# cd ${LARK_DIR}/Lark_prototype/build
# make run QEMU_VIRTFS_ENABLE=y QEMU_VIRTFS_HOST_DIR=${LARK_DIR}/sharefs/ -j $(nproc)
```

编译完成后，会启动一个 QEMU 虚拟机运行 OP-TEE，当你看到以下信息时，键入一个 `c` 和 `回车`：

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

然后在图形界面中，可以看到启动了两个 xterm，一个是 normal world，另一个是 secure world。

当 normal world terminal 出现以下提示信息时，输入 root 登录，不需要密码：

```
Welcome to Buildroot, type root or test to login
buildroot login:
```

### 3.8 检查基本功能

在 normal world terminal 中执行以下命令挂载 sharefs：

```
# mkdir sharefs && mount -t 9p -o trans=virtio host sharefs && cd sharefs && ls -l
```

运行测试应用程序：

```
# insmod test_app/test_driver.ko
# ./test_app/test_app
```

注：在 patch 过的 OP-TEE 中使用 `test_driver.ko`，在 native OP-TEE 中使用 `test_driver_native.ko`。

*test_app* 接受以下输入指令：

- r/w: 在内核态读/写 buffer
- ro/wo/rw/rwn: 将 buffer 设为内核只读/只写/可读写/不可读写
- t: 执行 micro-benchmark 测试
- q: 退出测试程序

依次输入以下指令 `r`、`w`、`wo`、`r`，可以看到，当 buffer 被设为只写后，内核无法再读取 buffer：

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

还可以 chroot 到 ubuntu-focal 发行版运行预安装的 real-world 应用：

```
# ./chroot_ubuntu.sh
```

详细的评估实验见下一节。

## 4 性能评估

评估实验包括 micro-benchmark、xtest suite、TAs 和 real-world applications。以下命令都在 normal world terminal 中执行。

在 [`results/`](results/) 目录中包含了所有实验结果数据。

### 4.1 Micro-benchmarks

运行 *test_app*，输入 `t` 命令，测试分别执行 10,000 次读/写操作的时间：

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

测试以下测试用例的运行时间：Basic OS features、 TEE Internal client API、TEE Internal API、Global platform TEEC、Storage、Key derivation、mbedTLS。

所有测试取结果中的 `real time (s)`。

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

测试 **SHA256**、AES-256、和 **Secure Storage** 在不同 buffer size下的性能。对于所有 TA，`buffer size` 的取值为：256、512、1024、2048、4096、8192、16384，单位为Byte。

**SHA256**

```
# xtest --sha-perf -n 1000 -a SHA256 -s BUFFER_SIZE
```

取结果中的 `mean time (μs)`。

**AES-256**

```
# xtest --aes-perf -n 1000 -k 256 -s BUFFER_SIZE
```

取结果中的 `mean time (μs)`。

**Secure Storage**

```
# xtest -t benchmark 1001 1002
```

取结果中的 Speed (kB/s)。

### 4.4 Real-world applications

在执行应用程序测试前，先在 normal world terminal 挂载 sharefs 并 chroot 到 ubuntu-focal：

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

取结果中的 `Response rate (rsp/s)`。

**Redis**

```
# service redis-server start
# redis-benchmark -n 10000 -P 16 -c 100 -d 4096 -t set,get -q
```

取结果中的 `Requests per second`。

**sysbench**

```
# sysbench --test=memory --memory-block-size=4096K --memory-total-size=100G --memory-access-mode=rnd --num-threads=2 --memory-oper=read run
# sysbench --test=memory --memory-block-size=4096K --memory-total-size=100G --memory-access-mode=rnd --num-threads=2 --memory-oper=write run
```

取结果中的 `Throughput (MiB/sec)`。

**MBW**

```
# mbw -q -n 10 128
```

取结果中  **MEMCPY**、**DUMB**、**MCBLOCK** 每个操作的 `AVG bandwidth (MiB/s)`。

**Bandwidth**

```
# bandwidth64 --faster
```

取结果中 `size=128 MB` 时的 **sequential read (64-bit)**、**sequential write (64-bit)**、和 **random read (64-bit)** 的 `bandwidth (MB/s)`。

**STREAM**

```
# stream
```

取结果中 **Copy**、**Scale**、**Add**、**Triad** 每个操作的 `Best Rate (MB/s)`。
