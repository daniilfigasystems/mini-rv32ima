# riscv_emufun (mini-rv32ima-gdi)

## About fork
This fork contain emulator ported to windows gdi api so it can run directly on the screen.

Click below for the YouTube video introducing this project:

[![Writing a Really Tiny RISC-V Emulator](https://img.youtube.com/vi/YT5vB3UqU_E/0.jpg)](https://www.youtube.com/watch?v=YT5vB3UqU_E) [![But Will It Run Doom?](https://img.youtube.com/vi/uZMNK17VCMU/0.jpg)](https://www.youtube.com/watch?v=uZMNK17VCMU) 

## What

mini-rv32ima is a single-file-header, [mini-rv32ima.h](https://github.com/cnlohr/riscv_emufun/blob/master/mini-rv32ima/mini-rv32ima.h), in the [STB Style library](https://github.com/nothings/stb) that:
 * Implements a RISC-V **rv32ima/Zifencei†+Zicsr** (and partial su), with CLINT and MMIO.
 * Is about **400 lines** of actual code.
 * Has **no dependencies**, not even libc.
 * Is **easily extensible**.  So you can easily add CSRs, instructions, MMIO, etc!
 * Is pretty **performant**. (~450 coremark on my laptop, about 1/2 the speed of QEMU)
 * Is human-readable and in **basic C** code.
 * Is "**incomplete**" in that it didn't implement the tons of the spec that Linux doesn't (and you shouldn't) use.
 * Is trivially **embeddable** in applications.

It has a [demo wrapper](https://github.com/cnlohr/riscv_emufun/blob/master/mini-rv32ima/mini-rv32ima.c) that:
 * Implements a CLI, SYSCON, UART, DTB and Kernel image loading.
 * And it only around **250 lines** of code, itself.
 * Compiles down to a **~18kB executable** and only relies on libc.

†: Zifence+RV32A are stubbed.  So, tweaks will need to be made if you want to emulate a multiprocessor system with this emulator.

Just see the `mini-rv32ima` folder.

It's "fully functional" now in that I can run Linux, apps, etc.  Compile flat binaries and drop them in an image.

## Why

I'm working on a really really simple C Risc-V emulator. So simple it doesn't even have an MMU (Memory Management Unit). I have a few goals, they include:
 * Furthering RV32-NOMMU work to improve Linux support for RV32-NOMMU.  (Imagine if we could run Linux on the $1 ESP32-C3)
 * Learning more about RV32 and writing emulators.
 * Being further inspired by @pimaker's amazing work on [Running Linux in a Pixel Shader](https://blog.pimaker.at/texts/rvc1/) and having the sneaking suspicion performance could be even better!
 * Hoping to port it to some weird places.
 * Understand the *most simplistic* system you can run Linux on and trying to push that boundary.
 * Continue to include my [education of people about assembly language](https://www.youtube.com/watch?v=Gelf0AyVGy4).

## How

Windows instructions (Just playing with the image)
 * Clone this repo.
 * Install or have TinyCC.  [Powershell Installer](https://github.com/cntools/Install-TCC) or [Regular Windows Installer](https://github.com/cnlohr/tinycc-win64-installer/releases/tag/v0_0.9.27)
 * Run `winrun.ps` in the `windows` folder.

WSL (For full toolchain and image build:
 * You will need to remove all spaces from your path i.e. `export PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/mnt/c/Windows/system32:/snap/bin` and continue the instructions.  P.S. What in the world was Windows thinking, putting a space between "Program" and "Files"??!?

Linux instructions (both): 
 * Clone this repo.
 * Install `git build-essential` and/or whatever other requirements are in place for [buildroot](https://buildroot.org/).
 * `make testdlimage`
 * It automatically downloads the image (~1MB) and runs the emulator.
 * Should be up and running in about 2.5s depending on internet speed.

You can do in-depth work on Linux by:
 * `make everything`

If you want to play with the bare metal system, see below, or if you have the toolchain installed, just:
 * `make testbare`

If you just want to play emdoom, and use the prebuilt image:
 * On Windows, run `windows\winrundoom.ps1`
 * On Linux, `cd mini-rv32ima`, and type `make testdoom`

## Questions?
 * Why not rv64?
   * Because then I can't run it as easily in a pixel shader if I ever hope to.
 * Can I add an MMU?
   * Yes.  It actually probably wouldn't be too difficult.
 * Should I add an MMU?
   * No.  It is important to further support for nommu systems to empower minimal Risc-V designs!

Everything else: Contact us on my Discord: https://discord.com/invite/CCeyWyZ

## How do I use this in my own project?

You shoud not need to modify `mini-rv32ima.h`, but instead, use `mini-rv32ima.c` as a template for what you are trying to do in your own project.

You can override all functionality by defining the following macros. Here are examples of what `mini-rv32ima.c` does with them.  You can see the definition of the functions, or augment their definitions, by altering `mini-rv32ima.c`.

| Macro | Definition / Comment |
| --- | --- |
| `MINIRV32WARN( x... )` | `printf( x );` <br> Warnings emitted from mini-rv32ima.h |
| `MINIRV32_DECORATE` | `static` <br> How to decorate the functions. |
| `MINI_RV32_RAM_SIZE` | `ram_amt` <br> A variable, how big is system RAM? |
| `MINIRV32_IMPLEMENTATION` | If using mini-rv32ima.h, need to define this. |
| `MINIRV32_POSTEXEC( pc, ir, retval )` | `{ if( retval > 0 ) { if( fail_on_all_faults ) { printf( "FAULT\n" ); return 3; } else retval = HandleException( ir, retval ); } }` <br> If you want to execute something every time slice. |
| `MINIRV32_HANDLE_MEM_STORE_CONTROL( addy, val )` | `if( HandleControlStore( addy, val ) ) return val;` <br> Called on non-RAM memory access. |
| `MINIRV32_HANDLE_MEM_LOAD_CONTROL( addy, rval )` | `rval = HandleControlLoad( addy );` <br> Called on non-RAM memory access return a value. |
| `MINIRV32_OTHERCSR_WRITE( csrno, value )` | `HandleOtherCSRWrite( image, csrno, value );` <br> You can use CSRs for control requests. |
| `MINIRV32_OTHERCSR_READ( csrno, value )` |  `value = HandleOtherCSRRead( image, csrno );` <br> You can use CSRs for control requests. |

## Hopeful goals?
 * Further drive down needed features to run Linux.
   * Remove need for RV32A extension on systems with only one CPU.
   * Support for relocatable ELF executables.
   * Add support for an unreal UART.  One that's **much** simpler than the current 8250 driver.
 * Maybe run this in a pixelshader too!
 * Get opensbi working with this.
 * Be able to "embed" rv32 emulators in random projects.
 * Can I use early console to be a full system console?
 * Can I increase the maximum contiguous memory allocatable?

## Special Thanks
 * For @regymm and their [patches to buildroot](https://github.com/regymm/buildroot) and help!
   * callout: Regymm's [quazisoc project](https://github.com/regymm/quasiSoC/).
 * Buildroot (For being so helpful).
 * @vowstar and their team working on [k210-linux-nommu](https://github.com/vowstar/k210-linux-nommu).
 * This [guide](https://jborza.com/emulation/2020/04/09/riscv-environment.html)
 * [rvcodecjs](https://luplab.gitlab.io/rvcodecjs/) I probably went through over 1,000 codes here.
 * @splinedrive from the [KianV RISC-V noMMU SoC](https://github.com/splinedrive/kianRiscV/tree/master/linux_socs/kianv_harris_mcycle_edition?s=09) project.
 
## More details

If you want to build the kernel yourself:
 * `make everything`
 * About 20 minutes.  (Or 4+ hours if you're on [Windows Subsytem for Linux 2](https://github.com/microsoft/WSL/issues/4197))
 * And you should be dropped into a Linux busybox shell with some little tools that were compiled here.

## Emdoom notes
 * Emdoom building is in the `experiments/emdoom` folder
 * You *MUST* build your kernel with `MAX_ORDER` set to >12 in `buildroot/output/build/linux-5.19/include/linux/mmzone.h` if you are building your own image.
 * You CAN use the pre-existing image that is described above.
 * On Windows, it will be very slow.  Not sure why.

If you want to use bare metal to build your binaries so you don't need buildroot, you can use the rv64 gcc in 32-bit mode built into Ubuntu 20.04 and up.
```
sudo apt-get install gcc-multilib gcc-riscv64-unknown-elf make
```

## Links
 * "Hackaday Supercon 2022: Charles Lohr - Assembly in 2022: Yes! We Still Use it and Here's Why" : https://www.youtube.com/watch?v=Gelf0AyVGy4
 
## Attic


## General notes:
 * https://github.com/cnlohr/riscv_emufun/commit/2f09cdeb378dc0215c07eb63f5a6fb43dbbf1871#diff-b48ccd795ae9aced07d022bf010bf9376232c4d78210c3113d90a8d349c59b3dL440


(These things don't currently work)

### Building Tests

(This does not work, now)
```
cd riscv-tests
export CROSS_COMPILE=riscv64-linux-gnu-
export PLATFORM_RISCV_XLEN=32
CC=riscv64-linux-gnu-gcc ./configure
make XLEN=32 RISCV_PREFIX=riscv64-unknown-elf- RISCV_GCC_OPTS="-g -O1 -march=rv32imaf -mabi=ilp32f -I/usr/include"
```

### Building OpenSBI

(This does not currently work!)
```
cd opensbi
export CROSS_COMPILE=riscv64-unknown-elf-
export PLATFORM_RISCV_XLEN=32
make
```

### Extra links
 * Clear outline of CSRs: https://five-embeddev.com/riscv-isa-manual/latest/priv-csrs.html
 * Fonts used in videos: https://audiolink.dev/

### Using custom build

Where yminpatch is the patch from the mailing list.
```
rm -rf buildroot
git clone git://git.buildroot.net/buildroot
cd buildroot
git am < ../yminpatch.txt
make qemu_riscv32_nommu_virt_defconfig
make
# Or use our configs.
```

Note: For emdoom you will need to modify include/linux/mmzone.h and change MAX_ORDER to 13.

### Buildroot Notes

Add this:
https://github.com/cnlohr/buildroot/pull/1/commits/bc890f74354e7e2f2b1cf7715f6ef334ff6ed1b2

Use this:
https://github.com/cnlohr/buildroot/commit/e97714621bfae535d947817e98956b112eb80a75

