/*-*- mode:c;indent-tabs-mode:nil;c-basic-offset:2;tab-width:8;coding:utf-8 -*-│
│ vi: set et ft=c ts=2 sts=2 sw=2 fenc=utf-8                               :vi │
╞══════════════════════════════════════════════════════════════════════════════╡
│ Copyright 2022 Justine Alexandra Roberts Tunney                              │
│                                                                              │
│ Permission to use, copy, modify, and/or distribute this software for         │
│ any purpose with or without fee is hereby granted, provided that the         │
│ above copyright notice and this permission notice appear in all copies.      │
│                                                                              │
│ THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL                │
│ WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED                │
│ WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE             │
│ AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL         │
│ DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR        │
│ PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER               │
│ TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR             │
│ PERFORMANCE OF THIS SOFTWARE.                                                │
╚─────────────────────────────────────────────────────────────────────────────*/
#include "libc/assert.h"
#include "libc/calls/blockcancel.internal.h"
#include "libc/calls/calls.h"
#include "libc/calls/cp.internal.h"
#include "libc/calls/internal.h"
#include "libc/calls/state.internal.h"
#include "libc/calls/struct/sigset.internal.h"
#include "libc/calls/struct/stat.internal.h"
#include "libc/calls/syscall-sysv.internal.h"
#include "libc/dce.h"
#include "libc/errno.h"
#include "libc/fmt/itoa.h"
#include "libc/fmt/magnumstrs.internal.h"
#include "libc/intrin/describeflags.h"
#include "libc/intrin/kprintf.h"
#include "libc/intrin/safemacros.h"
#include "libc/intrin/strace.h"
#include "libc/intrin/weaken.h"
#include "libc/limits.h"
#include "libc/paths.h"
#include "libc/proc/execve.internal.h"
#include "libc/str/str.h"
#include "libc/sysv/consts/f.h"
#include "libc/sysv/consts/map.h"
#include "libc/sysv/consts/mfd.h"
#include "libc/sysv/consts/o.h"
#include "libc/sysv/consts/prot.h"
#include "libc/sysv/consts/s.h"
#include "libc/sysv/consts/shm.h"
#include "libc/sysv/errfuns.h"
#include "libc/zip.h"

static bool IsAPEFd(const int fd) {
  char buf[8];
  return (sys_pread(fd, buf, 8, 0, 0) == 8) && IsApeMagic(buf);
}

static int fexecve_impl(const int fd, char *const argv[], char *const envp[]) {
  int rc;
  if (IsLinux()) {
    char path[14 + 12];
    FormatInt32(stpcpy(path, "/proc/self/fd/"), fd);
    rc = __sys_execve(path, argv, envp);
  } else if (IsFreebsd()) {
    rc = sys_fexecve(fd, argv, envp);
  } else {
    rc = enosys();
  }
  return rc;
}

#define defer(fn) __attribute__((cleanup(fn)))

void cleanup_close(int *pFD) {
  STRACE("time to close");
  if (*pFD != -1) {
    close(*pFD);
  }
}
#define defer_close defer(cleanup_close)

void cleanup_unlink(const char **path) {
  STRACE("time to unlink");
  if (*path != NULL) {
    sys_unlink(*path);
  }
}
#define defer_unlink defer(cleanup_unlink)

#undef defer_unlink
#undef defer_close
#undef defer

static inline int isZipFile(const void *data, size_t data_size) {
  if (!_weaken(GetZipEocd)) {
    return enosys();
  }
  int ziperror;
  return _weaken(GetZipEocd)(data, data_size, &ziperror) != NULL;
}

static int isFdAZipFile(const int fd) {
  if (!_weaken(GetZipEocd)) {
    return enosys();
  }

  struct stat st;
  if (fstat(fd, &st) == -1) {
    return -1;
  }
  void *space = __sys_mmap(0, st.st_size, PROT_READ, MAP_SHARED, fd, 0, 0);
  if (space == MAP_FAILED) {
    return -1;
  }
  int rc = isZipFile(space, st.st_size);
  if(__sys_munmap(space, st.st_size) == -1) {
    return -1;
  }
  return rc;
}

typedef enum {
  FEXEF_ZIP = 1 << 0,
  FEXEF_APE = 1 << 1
} FEXEF;

static inline int getFexeFlags(const void *data, size_t data_size) {
  if (!_weaken(GetZipEocd)) {
    return enosys();
  }
  int rc = isZipFile(data, data_size);
  if (rc == -1) {
    return -1;
  }
  int flags = rc << 0;
  if (data_size >= 8) {
    flags |= (int)IsApeMagic(data) << 1;
  }
  return flags;
}

/**
 * Creates a memfd and copies fd to it.
 *
 * If file is a zip file or ape file, FD_CLOEXEC is NOT set, however the file
 * descriptor number will be over 9000 to keep it out of the way of the new
 * process. If the file is not a zip file and not a ape file, FD_CLOEXEC will be
 * set unless executing under aarch64 QEMU user. These transformations are
 * applied to make executing from zipos work as expected, avoid leaking file
 * descriptors when possible, but when not possible, avoid conflicts with
 * programs that assume file descriptor numbers are available.
 *
 * FD_CLOEXEC is always set on zipos file descriptors, however, FD_CLOEXEC
 * makes the program inaccessible to the APE loader as when the APE loader
 * starts, the fd descriptor is closed. Additionally, closing the file
 * descriptor prevents it from being usable in COSMOPOLITAN_INIT_ZIPOS=,
 * preventing working zipos in the newly executed. Therefore, FD_CLOEXEC cannot
 * be set on APEs or zip files. Likewise with the APE loader, FD_CLOEXEC
 * prevents the qemu aarch64 user interpreter from accessing the ELF, so we
 * don't set it then either.
 *
 */
static int fd_to_mem_fd(const int infd, FEXEF *flags) {
  if ((!IsLinux() && !IsFreebsd()) || !_weaken(mmap) || !_weaken(munmap)) {
    return enosys();
  } else if(__vforked) {
    return enotsup();
  }

  struct stat st;
  if (fstat(infd, &st) == -1) {
    return -1;
  }
  int fd;
  if (IsLinux()) {
    fd = sys_memfd_create(__func__, 0);
  } else if (IsFreebsd()) {
    fd = sys_shm_open(SHM_ANON, O_CREAT | O_RDWR, 0);
  } else {
    return enosys();
  }
  if (fd == -1) {
    return -1;
  }
  void *space;
  if ((sys_ftruncate(fd, st.st_size, st.st_size) != -1) &&
      ((space = _weaken(mmap)(0, st.st_size, PROT_READ | PROT_WRITE, MAP_SHARED,
                              fd, 0)) != MAP_FAILED)) {
    ssize_t readRc;
    readRc = pread(infd, space, st.st_size, 0);
    bool success = readRc != -1;
    if (success) {
      int fexe_flags = getFexeFlags(space, st.st_size);
      success = fexe_flags != -1;
      *flags = fexe_flags;
    }
    const int e = errno;
    if ((_weaken(munmap)(space, st.st_size) != -1) && success) {
      if (*flags & (FEXEF_ZIP | FEXEF_APE)) {
        // The dup isn't strickly required, don't fail if it does
        const int highfd = fcntl(fd, F_DUPFD, 9001);
        if (highfd != -1) {
          close(fd);
          fd = highfd;
        }
      } else if (!IsAarch64() || !IsQemuUser()) {
        // setting cloexec isn't trickly required, don't fail if it does
        int flags = fcntl(fd, F_GETFD);
        if (flags != -1) {
          fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
        }
      }
      unassert(readRc == st.st_size);
      return fd;
    } else if (!success) {
      errno = e;
    }
  }
  const int e = errno;
  close(fd);
  errno = e;
  return -1;
}

/**
 * Executes binary executable at file descriptor.
 *
 * This is only supported on Linux and FreeBSD. APE binaries are
 * supported. Zipos is supported. Zipos fds are copied to a new memfd. Zip files
 * and APE files are F_DUPFD to a high number with FD_CLOEXEC turned off. APE
 * files are ran with execve.
 *
 * @param fd is opened executable and current file position is ignored
 * @return doesn't return on success, otherwise -1 w/ errno
 * @raise ENOEXEC if file at `fd` isn't an assimilated ELF executable
 * @raise ENOSYS on Windows, XNU, OpenBSD, NetBSD, and Metal
 */
int fexecve(int fd, char *const argv[], char *const envp[]) {
  int rc = 0;
  if (!argv || !envp) {
    rc = efault();
  } else {
    STRACE("fexecve(%d, %s, %s) → ...", fd, DescribeStringList(argv),
           DescribeStringList(envp));
    int newfd = fd;
    do {
      if (!IsLinux() && !IsFreebsd()) {
        rc = enosys();
        break;
      }
      FEXEF fflags = 0;
      if (__isfdkind(fd, kFdZip)) {
        BLOCK_SIGNALS;
        BLOCK_CANCELATION;
        strace_enabled(-1);
        newfd = fd_to_mem_fd(fd, &fflags);
        strace_enabled(+1);
        ALLOW_CANCELATION;
        ALLOW_SIGNALS;
        if (newfd == -1) {
          break;
        }
      } else {
        int fl_flags;
        BLOCK_SIGNALS;
        BLOCK_CANCELATION;
        fl_flags = fcntl(newfd, F_GETFL);
        ALLOW_CANCELATION;
        ALLOW_SIGNALS;
        if (fl_flags == -1) {
          break;
        }
        bool execute_only = IsLinux() && fl_flags & _O_PATH;
        if (!execute_only) {
          int fd_flags;
          BLOCK_SIGNALS;
          BLOCK_CANCELATION;
          strace_enabled(-1);
          fd_flags = fcntl(newfd, F_GETFD);
          strace_enabled(+1);
          ALLOW_CANCELATION;
          ALLOW_SIGNALS;
          if (fd_flags == -1) {
            break;
          }
          if ((fd_flags & FD_CLOEXEC) == 0) {
            int isFdAZipFileRc;
            BLOCK_SIGNALS;
            BLOCK_CANCELATION;
            strace_enabled(-1);
            isFdAZipFileRc = isFdAZipFile(newfd);
            strace_enabled(+1);
            ALLOW_CANCELATION;
            ALLOW_SIGNALS;
            if (isFdAZipFileRc == -1) {
              break;
            }
            fflags = isFdAZipFileRc << 0;
          }
          bool isAPE;
          BLOCK_SIGNALS;
          BLOCK_CANCELATION;
          isAPE = IsAPEFd(newfd);
          ALLOW_CANCELATION;
          ALLOW_SIGNALS;
          fflags |= (int)isAPE << 1;
        }
      }
      if (fflags & FEXEF_ZIP) {
        char *path = alloca(PATH_MAX);
        FormatInt32(stpcpy(path, "COSMOPOLITAN_INIT_ZIPOS="), newfd);
        size_t numenvs;
        for (numenvs = 0; envp[numenvs];) ++numenvs;
        static _Thread_local char *envs[500];
        memcpy(envs, envp, numenvs * sizeof(char *));
        envs[numenvs] = path;
        envs[numenvs + 1] = NULL;
        envp = envs;
      }
      fexecve_impl(newfd, argv, envp);
      if (fflags & FEXEF_APE) {
        char path[14 + 12];
        FormatInt32(stpcpy(path, "/dev/fd/"), newfd);
        STRACE("execve(%#s, %s) due to %s", path, DescribeStringList(argv),
               _strerrno(errno));
        sys_execve(path, argv, envp);
      }
    } while (0);
    if (newfd != fd) {
      int keepErrno = errno;
      BLOCK_SIGNALS;
      BLOCK_CANCELATION;
      strace_enabled(-1);
      close(newfd);
      strace_enabled(+1);
      ALLOW_CANCELATION;
      ALLOW_SIGNALS;
      errno = keepErrno;
    }
    rc = -1;
  }
  STRACE("fexecve(%d) failed %d% m", fd, rc);
  return rc;
}
