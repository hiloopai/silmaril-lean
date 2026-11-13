module

public import Silmaril.Cerberus.Frontend.Typing.Ctype.Defs
public import Silmaril.Cerberus.Ail.Syntax.Defs

/-! # Builtin type names and variables: `Builtins`

A port of `frontend/model/builtins.lem` at `b3e11ea3`: the `__cerbty_*` typedef names of
the standard headers, which the desugaring resolves before any scope lookup
(`cabs_to_ail.lem:1719-1735`), and the `__cerbvar_*` variables, which it resolves when
no declaration is in scope (`cabs_to_ail.lem:2288`).
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus

/-- `Builtins.translate_builtin_typenames` (`builtins.lem:7-86`). `__cerbty_ptraddr_t` is
CHERI-specific (`Ctype.ptraddr_t` fails elsewhere, a crash the oracle does not score) and
gives `none` here. -/
def translateBuiltinTypenames : String → Option Ctype
  -- stdint.h
  | "__cerbty_int8_t" => some (mkCtypeInteger (.signed (.intN 8)))
  | "__cerbty_int16_t" => some (mkCtypeInteger (.signed (.intN 16)))
  | "__cerbty_int32_t" => some (mkCtypeInteger (.signed (.intN 32)))
  | "__cerbty_int64_t" => some (mkCtypeInteger (.signed (.intN 64)))
  | "__cerbty_int128_t" => some (mkCtypeInteger (.signed (.intN 128)))
  | "__cerbty_int_fast8_t" => some (mkCtypeInteger (.signed (.intFastN 8)))
  | "__cerbty_int_fast16_t" => some (mkCtypeInteger (.signed (.intFastN 16)))
  | "__cerbty_int_fast32_t" => some (mkCtypeInteger (.signed (.intFastN 32)))
  | "__cerbty_int_fast64_t" => some (mkCtypeInteger (.signed (.intFastN 64)))
  | "__cerbty_int_least8_t" => some (mkCtypeInteger (.signed (.intLeastN 8)))
  | "__cerbty_int_least16_t" => some (mkCtypeInteger (.signed (.intLeastN 16)))
  | "__cerbty_int_least32_t" => some (mkCtypeInteger (.signed (.intLeastN 32)))
  | "__cerbty_int_least64_t" => some (mkCtypeInteger (.signed (.intLeastN 64)))
  | "__cerbty_intmax_t" => some intmax_t
  | "__cerbty_intptr_t" => some intptr_t
  | "__cerbty_ptrdiff_t" => some ptrdiff_t
  | "__cerbty_uint8_t" => some (mkCtypeInteger (.unsigned (.intN 8)))
  | "__cerbty_uint16_t" => some (mkCtypeInteger (.unsigned (.intN 16)))
  | "__cerbty_uint32_t" => some (mkCtypeInteger (.unsigned (.intN 32)))
  | "__cerbty_uint64_t" => some (mkCtypeInteger (.unsigned (.intN 64)))
  | "__cerbty_uint128_t" => some (mkCtypeInteger (.unsigned (.intN 128)))
  | "__cerbty_uint_fast8_t" => some (mkCtypeInteger (.unsigned (.intFastN 8)))
  | "__cerbty_uint_fast16_t" => some (mkCtypeInteger (.unsigned (.intFastN 16)))
  | "__cerbty_uint_fast32_t" => some (mkCtypeInteger (.unsigned (.intFastN 32)))
  | "__cerbty_uint_fast64_t" => some (mkCtypeInteger (.unsigned (.intFastN 64)))
  | "__cerbty_uint_least8_t" => some (mkCtypeInteger (.unsigned (.intLeastN 8)))
  | "__cerbty_uint_least16_t" => some (mkCtypeInteger (.unsigned (.intLeastN 16)))
  | "__cerbty_uint_least32_t" => some (mkCtypeInteger (.unsigned (.intLeastN 32)))
  | "__cerbty_uint_least64_t" => some (mkCtypeInteger (.unsigned (.intLeastN 64)))
  | "__cerbty_uintmax_t" => some uintmax_t
  | "__cerbty_uintptr_t" => some uintptr_t
  -- stddef.h
  | "__cerbty_size_t" => some size_t
  | "__cerbty_wchar_t" => some wchar_t
  | _ => none

/-- `Builtins.translate_errno` (`builtins.lem:88-172`): the `errno.h` values, chosen
arbitrarily by Cerberus. -/
def translateErrno : String → Option Int
  | "__cerbvar_EDOM" => some 1
  | "__cerbvar_EILSEQ" => some 2
  | "__cerbvar_ERANGE" => some 3
  | "__cerbvar_E2BIG" => some 4
  | "__cerbvar_EACCES" => some 5
  | "__cerbvar_EADDRINUSE" => some 6
  | "__cerbvar_EADDRNOTAVAIL" => some 7
  | "__cerbvar_EAFNOSUPPORT" => some 8
  | "__cerbvar_EAGAIN" => some 9
  | "__cerbvar_EALREADY" => some 10
  | "__cerbvar_EBADF" => some 11
  | "__cerbvar_EBADMSG" => some 12
  | "__cerbvar_EBUSY" => some 13
  | "__cerbvar_ECANCELED" => some 14
  | "__cerbvar_ECHILD" => some 15
  | "__cerbvar_ECONNABORTED" => some 16
  | "__cerbvar_ECONNREFUSED" => some 17
  | "__cerbvar_ECONNRESET" => some 18
  | "__cerbvar_EDEADLK" => some 19
  | "__cerbvar_EDESTADDRREQ" => some 20
  | "__cerbvar_EDQUOT" => some 21
  | "__cerbvar_EEXIST" => some 22
  | "__cerbvar_EFAULT" => some 23
  | "__cerbvar_EFBIG" => some 24
  | "__cerbvar_EHOSTUNREACH" => some 25
  | "__cerbvar_EIDRM" => some 26
  | "__cerbvar_EINPROGRESS" => some 27
  | "__cerbvar_EINTR" => some 28
  | "__cerbvar_EINVAL" => some 29
  | "__cerbvar_EIO" => some 30
  | "__cerbvar_EISCONN" => some 31
  | "__cerbvar_EISDIR" => some 32
  | "__cerbvar_ELOOP" => some 33
  | "__cerbvar_EMFILE" => some 34
  | "__cerbvar_EMLINK" => some 35
  | "__cerbvar_EMSGSIZE" => some 36
  | "__cerbvar_EMULTIHOP" => some 37
  | "__cerbvar_ENAMETOOLONG" => some 38
  | "__cerbvar_ENETDOWN" => some 39
  | "__cerbvar_ENETRESET" => some 40
  | "__cerbvar_ENETUNREACH" => some 41
  | "__cerbvar_ENFILE" => some 42
  | "__cerbvar_ENOBUFS" => some 43
  | "__cerbvar_ENODATA" => some 44
  | "__cerbvar_ENODEV" => some 45
  | "__cerbvar_ENOENT" => some 46
  | "__cerbvar_ENOEXEC" => some 47
  | "__cerbvar_ENOLCK" => some 48
  | "__cerbvar_ENOLINK" => some 49
  | "__cerbvar_ENOMEM" => some 50
  | "__cerbvar_ENOMSG" => some 51
  | "__cerbvar_ENOPROTOOPT" => some 52
  | "__cerbvar_ENOSPC" => some 53
  | "__cerbvar_ENOSR" => some 54
  | "__cerbvar_ENOSTR" => some 55
  | "__cerbvar_ENOSYS" => some 56
  | "__cerbvar_ENOTCONN" => some 57
  | "__cerbvar_ENOTDIR" => some 58
  | "__cerbvar_ENOTEMPTY" => some 59
  | "__cerbvar_ENOTRECOVERABLE" => some 60
  | "__cerbvar_ENOTSOCK" => some 61
  | "__cerbvar_ENOTSUP" => some 62
  | "__cerbvar_ENOTTY" => some 63
  | "__cerbvar_ENXIO" => some 64
  | "__cerbvar_EOPNOTSUPP" => some 65
  | "__cerbvar_EOVERFLOW" => some 66
  | "__cerbvar_EOWNERDEAD" => some 67
  | "__cerbvar_EPERM" => some 68
  | "__cerbvar_EPIPE" => some 69
  | "__cerbvar_EPROTO" => some 70
  | "__cerbvar_EPROTONOSUPPORT" => some 71
  | "__cerbvar_EPROTOTYPE" => some 72
  | "__cerbvar_EROFS" => some 73
  | "__cerbvar_ESPIPE" => some 74
  | "__cerbvar_ESRCH" => some 75
  | "__cerbvar_ESTALE" => some 76
  | "__cerbvar_ETIME" => some 77
  | "__cerbvar_ETIMEDOUT" => some 78
  | "__cerbvar_ETXTBSY" => some 79
  | "__cerbvar_EWOULDBLOCK" => some 80
  | "__cerbvar_EXDEV" => some 81
  | _ => none

/-- `Implementation.max_alignment` (`ocaml_implementation.ml:151`). -/
def maxAlignment : Nat := 8

/-- `Builtins.translate_builtin_varnames` (`builtins.lem:196-484`): the `__cerbvar_*`
variables of the standard headers, which the desugaring resolves when no declaration is
in scope. A memory order is `encode_memory_order` (`builtins.lem:175`). -/
def translateBuiltinVarnames (ident : Identifier) : Option (Ail.ExpressionNode Unit) :=
  let constInt (ic : Ail.IntegerConstant) : Option (Ail.ExpressionNode Unit) := some (.const (.integer ic))
  let constIc (n : Int) := constInt (.iconstant n .decimal none)
  match translateErrno ident.name with
  | some n => constIc n
  | none =>
    match ident.name with
    | "__cerbvar_NULL" => some (.const .null)
    | "__cerbvar_MAX_ALIGNMENT" => constIc maxAlignment
    | "__cerbvar_memory_order_relaxed" => constIc 0
    | "__cerbvar_memory_order_consume" => constIc 1
    | "__cerbvar_memory_order_acquire" => constIc 2
    | "__cerbvar_memory_order_release" => constIc 3
    | "__cerbvar_memory_order_acq_rel" => constIc 4
    | "__cerbvar_memory_order_seq_cst" => constIc 5
    | "__cerbvar_atomic_thread_fence" => some (.builtin (.atomic .threadFence))
    | "__cerbvar_atomic_store_explicit" => some (.builtin (.atomic .store))
    | "__cerbvar_atomic_load_explicit" => some (.builtin (.atomic .load))
    | "__cerbvar_atomic_exchange_explicit" => some (.builtin (.atomic .exchange))
    | "__cerbvar_atomic_compare_exchange_strong_explicit" => some (.builtin (.atomic .compareExchangeStrong))
    | "__cerbvar_atomic_compare_exchange_weak_explicit" => some (.builtin (.atomic .compareExchangeWeak))
    | "__cerbvar_atomic_fetch_key_explicit" => some (.builtin (.atomic .fetchKey))
    | "__cerbvar_linux_fence" => some (.builtin (.linux .fence))
    | "__cerbvar_linux_read" => some (.builtin (.linux .read))
    | "__cerbvar_linux_write" => some (.builtin (.linux .write))
    | "__cerbvar_linux_rmw" => some (.builtin (.linux .rmw))
    | "__cerbvar_CHAR_BIT" => constIc 8
    | "__cerbvar_SCHAR_MIN" => constInt (.min (.signed .ichar))
    | "__cerbvar_SCHAR_MAX" => constInt (.max (.signed .ichar))
    | "__cerbvar_UCHAR_MAX" => constInt (.max (.unsigned .ichar))
    | "__cerbvar_CHAR_MIN" => constInt (.min .char)
    | "__cerbvar_CHAR_MAX" => constInt (.max .char)
    | "__cerbvar_SHRT_MIN" => constInt (.min (.signed .short))
    | "__cerbvar_SHRT_MAX" => constInt (.max (.signed .short))
    | "__cerbvar_USHRT_MAX" => constInt (.max (.unsigned .short))
    | "__cerbvar_INT_MIN" => constInt (.min (.signed .int))
    | "__cerbvar_INT_MAX" => constInt (.max (.signed .int))
    | "__cerbvar_UINT_MAX" => constInt (.max (.unsigned .int))
    | "__cerbvar_LONG_MIN" => constInt (.min (.signed .long))
    | "__cerbvar_LONG_MAX" => constInt (.max (.signed .long))
    | "__cerbvar_ULONG_MAX" => constInt (.max (.unsigned .long))
    | "__cerbvar_LLONG_MIN" => constInt (.min (.signed .longLong))
    | "__cerbvar_LLONG_MAX" => constInt (.max (.signed .longLong))
    | "__cerbvar_ULLONG_MAX" => constInt (.max (.unsigned .longLong))
    | "__cerbvar_INT8_MIN" => constInt (.min (.signed (.intN 8)))
    | "__cerbvar_INT16_MIN" => constInt (.min (.signed (.intN 16)))
    | "__cerbvar_INT32_MIN" => constInt (.min (.signed (.intN 32)))
    | "__cerbvar_INT64_MIN" => constInt (.min (.signed (.intN 64)))
    | "__cerbvar_INT8_MAX" => constInt (.max (.signed (.intN 8)))
    | "__cerbvar_INT16_MAX" => constInt (.max (.signed (.intN 16)))
    | "__cerbvar_INT32_MAX" => constInt (.max (.signed (.intN 32)))
    | "__cerbvar_INT64_MAX" => constInt (.max (.signed (.intN 64)))
    | "__cerbvar_UINT8_MAX" => constInt (.max (.unsigned (.intN 8)))
    | "__cerbvar_UINT16_MAX" => constInt (.max (.unsigned (.intN 16)))
    | "__cerbvar_UINT32_MAX" => constInt (.max (.unsigned (.intN 32)))
    | "__cerbvar_UINT64_MAX" => constInt (.max (.unsigned (.intN 64)))
    | "__cerbvar_INTPTR_MIN" => constInt (.min (.signed .intptr))
    | "__cerbvar_INTPTR_MAX" => constInt (.max (.signed .intptr))
    | "__cerbvar_UINTPTR_MAX" => constInt (.max (.unsigned .intptr))
    | "__cerbvar_INTMAX_MIN" => constInt (.min (.signed .intmax))
    | "__cerbvar_INTMAX_MAX" => constInt (.max (.signed .intmax))
    | "__cerbvar_UINTMAX_MAX" => constInt (.max (.unsigned .intmax))
    | "__cerbvar_PTRDIFF_MIN" => constInt (.min .ptrdiff)
    | "__cerbvar_PTRDIFF_MAX" => constInt (.max .ptrdiff)
    | "__cerbvar_PTRADDR_MIN" => constInt (.min .ptraddr)
    | "__cerbvar_PTRADDR_MAX" => constInt (.max .ptraddr)
    | "__cerbvar_INT_LEAST8_MIN" => constInt (.min (.signed (.intLeastN 8)))
    | "__cerbvar_INT_LEAST16_MIN" => constInt (.min (.signed (.intLeastN 16)))
    | "__cerbvar_INT_LEAST32_MIN" => constInt (.min (.signed (.intLeastN 32)))
    | "__cerbvar_INT_LEAST64_MIN" => constInt (.min (.signed (.intLeastN 64)))
    | "__cerbvar_INT_LEAST8_MAX" => constInt (.max (.signed (.intLeastN 8)))
    | "__cerbvar_INT_LEAST16_MAX" => constInt (.max (.signed (.intLeastN 16)))
    | "__cerbvar_INT_LEAST32_MAX" => constInt (.max (.signed (.intLeastN 32)))
    | "__cerbvar_INT_LEAST64_MAX" => constInt (.max (.signed (.intLeastN 64)))
    | "__cerbvar_UINT_LEAST8_MAX" => constInt (.max (.unsigned (.intLeastN 8)))
    | "__cerbvar_UINT_LEAST16_MAX" => constInt (.max (.unsigned (.intLeastN 16)))
    | "__cerbvar_UINT_LEAST32_MAX" => constInt (.max (.unsigned (.intLeastN 32)))
    | "__cerbvar_UINT_LEAST64_MAX" => constInt (.max (.unsigned (.intLeastN 64)))
    | "__cerbvar_INT_FAST8_MIN" => constInt (.min (.signed (.intFastN 8)))
    | "__cerbvar_INT_FAST16_MIN" => constInt (.min (.signed (.intFastN 16)))
    | "__cerbvar_INT_FAST32_MIN" => constInt (.min (.signed (.intFastN 32)))
    | "__cerbvar_INT_FAST64_MIN" => constInt (.min (.signed (.intFastN 64)))
    | "__cerbvar_INT_FAST8_MAX" => constInt (.max (.signed (.intFastN 8)))
    | "__cerbvar_INT_FAST16_MAX" => constInt (.max (.signed (.intFastN 16)))
    | "__cerbvar_INT_FAST32_MAX" => constInt (.max (.signed (.intFastN 32)))
    | "__cerbvar_INT_FAST64_MAX" => constInt (.max (.signed (.intFastN 64)))
    | "__cerbvar_UINT_FAST8_MAX" => constInt (.max (.unsigned (.intFastN 8)))
    | "__cerbvar_UINT_FAST16_MAX" => constInt (.max (.unsigned (.intFastN 16)))
    | "__cerbvar_UINT_FAST32_MAX" => constInt (.max (.unsigned (.intFastN 32)))
    | "__cerbvar_UINT_FAST64_MAX" => constInt (.max (.unsigned (.intFastN 64)))
    | "__cerbvar_SIZE_MAX" => constInt (.max .size)
    | "__cerbvar_WCHAR_MIN" => constInt (.min .wchar)
    | "__cerbvar_WCHAR_MAX" => constInt (.max .wchar)
    | "__cerbvar_WINT_MIN" => constInt (.min .wint)
    | "__cerbvar_WINT_MAX" => constInt (.max .wint)
    | "__cerbvar_copy_alloc_id" => some (.builtin .copyAllocId)
    | "__cerbvar_strfcap" => some (.builtin (.cheri "strfcap"))
    | "__cerbvar_cheri_bounds_set" => some (.builtin (.cheri "cheri_bounds_set"))
    | "__cerbvar_cheri_perms_and" => some (.builtin (.cheri "cheri_perms_and"))
    | "__cerbvar_cheri_address_get" => some (.builtin (.cheri "cheri_address_get"))
    | "__cerbvar_cheri_base_get" => some (.builtin (.cheri "cheri_base_get"))
    | "__cerbvar_cheri_offset_get" => some (.builtin (.cheri "cheri_offset_get"))
    | "__cerbvar_cheri_length_get" => some (.builtin (.cheri "cheri_length_get"))
    | "__cerbvar_cheri_tag_get" => some (.builtin (.cheri "cheri_tag_get"))
    | "__cerbvar_cheri_tag_clear" => some (.builtin (.cheri "cheri_tag_clear"))
    | "__cerbvar_cheri_is_equal_exact" => some (.builtin (.cheri "cheri_is_equal_exact"))
    | "__cerbvar_cheri_representable_length" => some (.builtin (.cheri "cheri_representable_length"))
    | "__cerbvar_cheri_representable_alignment_mask" => some (.builtin (.cheri "cheri_representable_alignment_mask"))
    | "__cerbvar_cheri_revoke" => some (.builtin (.cheri "cheri_revoke"))
    | _ => none

end Silmaril.Cerberus.Frontend.Desugar
