# VIP

This repository contains the source code for the CCS'21 paper:

*"VIP: Safeguard Value Invariant Property for Thwarting Critical Memory Corruption Attacks
Mohannad Ismail, Jinwoo Yom, Christopher Jelesnianski, Yeongjin Jang, Changwoo Min
In Proceedings of the 2021 ACM SIGSAC Conference on Computer and Communications Security (ACM CCS 2021)*

## Directory structure
```{.sh}
vip
├── CMakeLists.txt    # CMake file for building VIP
├── example           # Example code
├── include           # Headers for VIP
├── jemalloc          # Jemalloc source code
├── kernel            # VIP Linux Kernel
├── lib               # VIP library code
├── llvm-project      # VIP compiler
├── ptmalloc          # Ptmalloc source code
├── utils             # Misc build tools
```


## How to compile VIP
### Set up VIP compiler for LTO
```bash
cd ~/vip
git clone --depth 1 git://sourceware.org/git/binutils-gdb.git binutils

mkdir binutils-build
cd binutils-build
../binutils/configure --enable-gold --enable-plugins --disable-werror
make
```

### Initial setup and compiling the library
```bash
$ mkdir build
$ cd build
$ cmake ..
$ make
```

### Compiling VIP components (run in vip/build)
#### Building the kernel 
```bash
$ make kernel
$ make kernel-install
```
Note: In order to run the examples and use VIP, the VIP kernel needs to be installed on your machine.

#### Building jemalloc
```bash
$ cd ../jemalloc
$ ./autogen.sh
$ ./configure
$ cd ../build
$ make jemalloc
```

#### Building ptmalloc
```bash
$ make ptmalloc
```

#### Building VIP compiler
```bash
$ make llvm
```

#### Setting the linker executables
```bash
cd ~
mkdir sys-backup
cd /usr/bin/
cp ar ~/sys-backup/
cp nm ~/sys-backup/
cp ld ~/sys-backup/
cp ranlib ~/sys-backup/

cd /usr/bin/
sudo cp ~/vip/binutils-build/binutils/ar ./
sudo rm nm
sudo cp ~/vip/binutils-build/binutils/nm-new ./nm
sudo cp ~/vip/binutils-build/binutils/ranlib ./
sudo cp ~/vip/binutils-build/gold/ld-new ./ld

cd /usr/lib
sudo mkdir bfd-plugins
cd bfd-plugins
sudo cp ~/vip/llvm-project/build/lib/LLVMgold.so ./
sudo cp ~/vip/llvm-project/build/lib/libLTO.\* ./

export RANLIB=/bin/true
```

#### Running examples
```bash
$ cd examples
$ make examples
$ ./example
$ ./example_cpp
```
If you wish to use the VIP compiler, please check vip/examples/CMakeLists.txt for all the flags necessary. You can copy the CMakeLists file and modify it to add your source files to it.
