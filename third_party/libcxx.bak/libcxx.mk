#-*-mode:makefile-gmake;indent-tabs-mode:t;tab-width:8;coding:utf-8-*-┐
#───vi: set et ft=make ts=8 tw=8 fenc=utf-8 :vi───────────────────────┘

PKGS += THIRD_PARTY_LIBCXX

THIRD_PARTY_LIBCXX_ARTIFACTS += THIRD_PARTY_LIBCXX_A
THIRD_PARTY_LIBCXX = $(THIRD_PARTY_LIBCXX_A_DEPS) $(THIRD_PARTY_LIBCXX_A)
THIRD_PARTY_LIBCXX_A = o/$(MODE)/third_party/libcxx/libcxx.a
THIRD_PARTY_LIBCXX_A_FILES := $(wildcard third_party/libcxx/*)
THIRD_PARTY_LIBCXX_A_HDRS = $(filter %.h,$(THIRD_PARTY_LIBCXX_A_FILES))
THIRD_PARTY_LIBCXX_A_INCS = $(filter %.inc,$(THIRD_PARTY_LIBCXX_A_FILES))
THIRD_PARTY_LIBCXX_A_SRCS_S = $(filter %.S,$(THIRD_PARTY_LIBCXX_A_FILES))
THIRD_PARTY_LIBCXX_A_SRCS_C = $(filter %.c,$(THIRD_PARTY_LIBCXX_A_FILES))
THIRD_PARTY_LIBCXX_A_SRCS_CC = $(filter %.cc,$(THIRD_PARTY_LIBCXX_A_FILES))

THIRD_PARTY_LIBCXX_A_SRCS =					\
	$(THIRD_PARTY_LIBCXX_A_SRCS_S)				\
	$(THIRD_PARTY_LIBCXX_A_SRCS_C)

THIRD_PARTY_LIBCXX_A_OBJS =					\
	$(THIRD_PARTY_LIBCXX_A_SRCS_S:%.S=o/$(MODE)/%.o)	\
	$(THIRD_PARTY_LIBCXX_A_SRCS_C:%.c=o/$(MODE)/%.o)	\
	$(THIRD_PARTY_LIBCXX_A_SRCS_CC:%.cc=o/$(MODE)/%.o)

THIRD_PARTY_LIBCXX_A_CHECKS =					\
	$(THIRD_PARTY_LIBCXX_A).pkg				\
	$(THIRD_PARTY_LIBCXX_A_HDRS:%=o/$(MODE)/%.okk)

THIRD_PARTY_LIBCXX_A_DIRECTDEPS =				\
	LIBC_INTRIN						\
	LIBC_NEXGEN32E						\
	LIBC_MEM						\
	LIBC_STUBS						\
	LIBC_TINYMATH

THIRD_PARTY_LIBCXX_A_DEPS :=					\
	$(call uniq,$(foreach x,$(THIRD_PARTY_LIBCXX_A_DIRECTDEPS),$($(x))))

$(THIRD_PARTY_LIBCXX_A):					\
		third_party/libcxx/				\
		$(THIRD_PARTY_LIBCXX_A).pkg			\
		$(THIRD_PARTY_LIBCXX_A_OBJS)

$(THIRD_PARTY_LIBCXX_A).pkg:					\
		$(THIRD_PARTY_LIBCXX_A_OBJS)			\
		$(foreach x,$(THIRD_PARTY_LIBCXX_A_DIRECTDEPS),$($(x)_A).pkg)

THIRD_PARTY_LIBCXX_LIBS = $(foreach x,$(THIRD_PARTY_LIBCXX_ARTIFACTS),$($(x)))
THIRD_PARTY_LIBCXX_SRCS = $(foreach x,$(THIRD_PARTY_LIBCXX_ARTIFACTS),$($(x)_SRCS))
THIRD_PARTY_LIBCXX_HDRS = $(foreach x,$(THIRD_PARTY_LIBCXX_ARTIFACTS),$($(x)_HDRS))
THIRD_PARTY_LIBCXX_INCS = $(foreach x,$(THIRD_PARTY_LIBCXX_ARTIFACTS),$($(x)_INCS))
THIRD_PARTY_LIBCXX_CHECKS = $(foreach x,$(THIRD_PARTY_LIBCXX_ARTIFACTS),$($(x)_CHECKS))
THIRD_PARTY_LIBCXX_OBJS = $(foreach x,$(THIRD_PARTY_LIBCXX_ARTIFACTS),$($(x)_OBJS))

.PHONY: o/$(MODE)/third_party/libcxx
o/$(MODE)/third_party/libcxx: $(THIRD_PARTY_LIBCXX_CHECKS)
