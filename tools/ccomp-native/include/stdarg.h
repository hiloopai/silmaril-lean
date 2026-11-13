#ifndef __CCOMP_NATIVE_STDARG_H
#define __CCOMP_NATIVE_STDARG_H

/* System V AMD64 LP64, x86-64 psABI 3.5.7. This record is shared with
 * Silmaril.Machine.SystemV.Abi.VaList; it is not Cerberus's integer cursor. */
typedef struct __ccomp_sysv_va_record {
  unsigned int gp_offset;
  unsigned int fp_offset;
  void *overflow_arg_area;
  void *reg_save_area;
} __ccomp_sysv_va_list[1];

typedef __ccomp_sysv_va_list va_list;
typedef __ccomp_sysv_va_list __gnuc_va_list;
#define __GNUC_VA_LIST 1
#define __builtin_va_list __ccomp_sysv_va_list
#define __builtin_va_start(ap, last) ((void)__cerb_va_start((ap), last))
#define __builtin_va_arg(ap, type) __cerb_va_arg((ap), type)
#define __builtin_va_copy(destination, source) \
  ((void)__cerb_va_copy((destination), (source)))
#define __builtin_va_end(ap) ((void)__cerb_va_end((ap)))
#define va_start(ap, last) __builtin_va_start(ap, last)
#define va_arg(ap, type) __builtin_va_arg(ap, type)
#define va_copy(destination, source) __builtin_va_copy(destination, source)
#define va_end(ap) __builtin_va_end(ap)

#endif
