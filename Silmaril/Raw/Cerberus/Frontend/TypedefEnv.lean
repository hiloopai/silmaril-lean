module

public import Std.Data.TreeSet

/-! # The typedef names in scope: `Lexer_feedback`

Cerberus's lexer hack (`parsers/c/lexer_feedback.ml`, after Jourdan and Pottier) keeps
one global set of the names that are typedef names, which decides whether the lexer
emits `TYPE` or `VARIABLE` after a name. The parser adds a name when it reduces a
declarator of a `typedef` and removes it when it reduces any other declarator or an
enumeration constant. Scopes save and restore the whole set.

Here the set is a value of the parser state. It is a persistent tree, so a saved
context shares structure with the current one, and saving costs nothing.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

/-- `Lexer_feedback.context`: the names that are typedef names. -/
structure TypedefEnv where
  names : Std.TreeSet String compare

namespace TypedefEnv

/-- `cerb_builtin_types` (`lexer_feedback.ml:14-48`), with its duplicate `nlink_t` and its
typo `pthread_rwloc_t`. -/
def builtinTypes : List String :=
  ["jmp_buf", "sig_atomic_t", "va_list", "ptrdiff_t", "ptraddr_t", "wchar_t",
   "int8_t", "int16_t", "int32_t", "int64_t", "int128_t",
   "uint8_t", "uint16_t", "uint32_t", "uint64_t", "uint128_t",
   "int_least8_t", "int_least16_t", "int_least32_t", "int_least64_t",
   "uint_least8_t", "uint_least16_t", "uint_least32_t", "uint_least64_t",
   "int_fast8_t", "int_fast16_t", "int_fast32_t", "int_fast64_t",
   "uint_fast8_t", "uint_fast16_t", "uint_fast32_t", "uint_fast64_t",
   "intptr_t", "uintptr_t", "intmax_t", "uintmax_t", "size_t", "ssize_t",
   "FILE", "fpos_t", "cnd_t", "thrd_t", "tss_t", "mtx_t", "once_flag",
   "time_t", "timer_t", "clock_t", "clockid_t", "suseconds_t", "blkcnt_t", "blksize_t",
   "dev_t", "fsblkcnt_t", "fsfilcnt_t", "gid_t", "id_t", "uid_t", "pid_t",
   "key_t", "mode_t", "ino_t", "nlink_t", "nlink_t", "off_t",
   "pthread_attr_t", "pthread_barrier_t", "pthread_barrierattr_t",
   "pthread_cond_t", "pthread_condattr_t", "pthread_key_t",
   "pthread_mutex_t", "pthread_mutexattr_t", "pthread_once_t",
   "pthread_rwloc_t", "pthread_rwlockattr_t", "pthread_spinlock_t", "pthread_t",
   "trace_attr_t", "trace_event_id_t", "trace_event_set_t", "trace_id_t",
   "max_align_t"]

/-- `Lexer_feedback.current` at start: `__cerbty_` and each builtin type. -/
def builtin : TypedefEnv :=
  ⟨builtinTypes.foldl (fun s n => s.insert ("__cerbty_" ++ n)) ∅⟩

/-- `declare_typedefname`. -/
def declareTypedef (e : TypedefEnv) (x : String) : TypedefEnv := ⟨e.names.insert x⟩

/-- `declare_varname`. -/
def declareVar (e : TypedefEnv) (x : String) : TypedefEnv := ⟨e.names.erase x⟩

/-- `is_typedefname`: whether the lexer emits `TYPE` after the name `x`. -/
def isTypedef (e : TypedefEnv) (x : String) : Bool := e.names.contains x

end TypedefEnv

end Silmaril.Cerberus.Frontend
