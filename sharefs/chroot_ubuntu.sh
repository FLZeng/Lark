mount -t proc none ubuntu-focal/proc
mount -o ro -t sysfs none ubuntu-focal/sys
mount -t tmpfs tmpfs ubuntu-focal/tmp
mount --rbind /dev ubuntu-focal/dev
mount --bind /run ubuntu-focal/run

mount --make-rslave ubuntu-focal/proc
mount --make-rslave ubuntu-focal/dev
mount --make-rslave ubuntu-focal/sys
mount --make-slave ubuntu-focal/run
mount --make-slave ubuntu-focal/tmp

chroot ubuntu-focal /bin/bash
