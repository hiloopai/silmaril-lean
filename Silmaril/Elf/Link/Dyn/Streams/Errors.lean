module

public import Silmaril.Elf.Link.Dyn.Streams.Table

/-! # Diagnostics: `errno`, `strerror` and GNU `error`

The contracts a program needs to report a failed operation on `stderr`:

* `errnoLocStep`: `__errno_location ()` returns the address of the calling thread's `errno`
  (`Env.errnoA`), keeps its bytes and permissions, and the cell is readable, writable and outside
  the executable's image (`ErrnoCell`): gnulib's `quotearg` saves and restores `errno` through it;
* `errorMsgStep`: GNU `error (status, errnum, "%s", arg)`. glibc's `error` (`misc/error.c`)
  flushes `stdout`, writes `program_invocation_name`, `": "`, the argument, `": "` and
  `strerror (errnum)` and a newline to `stderr` (unbuffered), and returns when `status` is 0
  (it calls `exit (status)` otherwise). The program name is read from memory, from the variable
  `program_invocation_name` at `pinA`, as glibc does; `stdout`'s flush is left open (the bytes
  handed to `stdout` stay the same, `Streams.Appended … []`).
* `strerrorC`: the C-locale `strerror` texts of glibc 2.39 (`sysdeps/gnu/errlist.h`) for the
  error numbers of `Silmaril.Apps.Sha256sum.Errno`, by number. `strerrorC_errno` checks that they
  are the texts of the specification's `Errno.text`.

`mbCurMaxStep` (`MB_CUR_MAX` is 1 in the C locale) and `memcmpStep` are what gnulib's `quotef`
calls on a name that needs no quoting (besides `__errno_location`).

`fileTable` is the import table of the file-operand tiers: these four in front of
`Streams.Table.shaTable` (a by-name lookup takes the first entry, so the
message-less `Streams.errorStep` is shadowed).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Streams

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Imports

/-- glibc 2.39's C-locale `strerror` text of an error number (`_sys_errlist_internal`), for the
numbers the file-operand tiers can meet; `none` for the others (no claim). -/
def strerrorC : Nat → Option String
  | 2 => some "No such file or directory"
  | 5 => some "Input/output error"
  | 9 => some "Bad file descriptor"
  | 13 => some "Permission denied"
  | 20 => some "Not a directory"
  | 21 => some "Is a directory"
  | 28 => some "No space left on device"
  | 36 => some "File name too long"
  | 40 => some "Too many levels of symbolic links"
  | _ => none

/-- The table agrees with the specification's `Errno.text`. -/
theorem strerrorC_errno (e : Silmaril.Apps.Sha256sum.Errno) : strerrorC (errnoCode e) = some e.text := by
  cases e <;> rfl

/-- The error numbers are distinct, so `errno` determines the `Errno`. -/
theorem errnoCode_inj {e e' : Silmaril.Apps.Sha256sum.Errno} (h : errnoCode e = errnoCode e') : e = e' := by
  cases e <;> cases e' <;> first | rfl | (simp [errnoCode] at h)

/-- Every error number is small (below 64). -/
theorem errnoCode_lt (e : Silmaril.Apps.Sha256sum.Errno) : errnoCode e < 64 := by
  cases e <;> decide

/-- The line `error (status, errnum, "%s", arg)` writes: `prog: arg: strerror (errnum)\n`. -/
def errorMsg (prog arg : List Byte) (e : Silmaril.Apps.Sha256sum.Errno) : List Byte :=
  prog ++ ofSpec (Silmaril.Apps.Sha256sum.lit ": ") ++ arg ++ ofSpec (Silmaril.Apps.Sha256sum.lit ": ") ++
    ofSpec (Silmaril.Apps.Sha256sum.lit e.text) ++ [10]

/-- The message is the specification's `diagE` (`toSpec` of it). -/
theorem toSpec_errorMsg (prog arg : List Byte) (e : Silmaril.Apps.Sha256sum.Errno) :
    toSpec (errorMsg prog arg e) = Silmaril.Apps.Sha256sum.diagE (toSpec prog) (toSpec arg) e := by
  simp [errorMsg, Silmaril.Apps.Sha256sum.diagE, toSpec, ofSpec, Function.comp_def]

/-- `"%s"` -/
def fmtS : List Byte := [0x25#8, 0x73#8]

/-- `program_invocation_name` (the variable at `pinA`) points to the C string `prog`. -/
def ProgName (m : Memory) (pinA : Word) (prog : List Byte) : Prop :=
  ∃ pa, loadN m pinA 8 = some pa ∧ CStr m pa prog

/-- The four bytes of the calling thread's `errno`. -/
def ErrnoR (E : Env) (a : Nat) : Prop := E.errnoA.toNat ≤ a ∧ a < E.errnoA.toNat + 4

/-- What a program may do with `*__errno_location ()`: the cell is readable and writable (the
thread's TLS block is a read-write mapping) and lies outside the executable's image (ld.so
allocates the main thread's TLS block; it is not part of the program's `PT_LOAD` segments). -/
def ErrnoCell (E : Env) (W : World) (m : Memory) : Prop :=
  m.Permitted .read E.errnoA.toNat 4 ∧ m.Permitted .write E.errnoA.toNat 4 ∧
    ∀ j, j < 4 → ¬ W.InImage (E.errnoA.toNat + j)

/-- **`__errno_location ()`**: the address of `errno`, which it keeps (glibc's
`csu/errno-loc.c` returns `&errno` and writes nothing: the cell's bytes and permissions are
kept, whether or not the cell is the library's private memory), and which the caller may read
and write (`ErrnoCell`). -/
def errnoLocStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧
      t.m.core.read .rax = E.errnoA ∧ (∀ e, ErrnoIs E s.m.memory e → ErrnoIs E t.m.memory e) ∧
      Keeps (ErrnoR E) s.m.memory t.m.memory ∧ ErrnoCell E W t.m.memory

/-- **`error (status, errnum, "%s", arg)`** (GNU, C locale) for an `errnum` among the
specification's error numbers. With `status = 0` it returns: the message is appended to
`Ghost.err`, everything handed to `stdout` stays as it was (its buffer may be written), the other
streams (`stderr` included: unbuffered) keep their states. Otherwise the message is written and
the process exits with `status`. -/
def errorMsgStep (E : Env) (pinA : Word) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ CStr s.m.memory (s.m.core.read .rdx) fmtS ∧
      (∃ a, CStr s.m.memory (s.m.core.read .rcx) a) ∧ (∃ prog, ProgName s.m.memory pinA prog) ∧
      ∃ e, low32 (s.m.core.read .rsi) = BitVec.ofNat 32 (errnoCode e))
    fun t => ∀ a prog e, CStr s.m.memory (s.m.core.read .rcx) a → ProgName s.m.memory pinA prog →
      low32 (s.m.core.read .rsi) = BitVec.ofNat 32 (errnoCode e) →
      if low32 (s.m.core.read .rdi) = 0#32 then
        LibRet E W (fun _ => False) s t ∧ OthersKept E s t [E.stdoutF] ∧ Appended E W s t [] ∧
          t.g = { s.g with out := t.g.out, err := s.g.err ++ errorMsg prog a e }
      else AtGate W s t ∧
        t.g = { s.g with jobs := [.exit (s.m.core.read .rdi)], err := s.g.err ++ errorMsg prog a e }

/-- **`__ctype_get_mb_cur_max ()`** (`MB_CUR_MAX`): 1 in the C locale. glibc's
`ctype/ctype-info.c`/`locale` code only reads the locale data: it keeps `errno`'s bytes and
permissions (which `LibRet` alone does not promise when `errno` is private memory). -/
def mbCurMaxStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧ t.m.core.read .rax = 1#64 ∧
      Keeps (ErrnoR E) s.m.memory t.m.memory

/-- **`memcmp (a, b, n)`**: zero iff the two `n`-byte blocks are equal. -/
def memcmpStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧
      (∃ x, s.m.memory.readBytes (s.m.core.read .rdi).toNat (s.m.core.read .rdx).toNat = some x) ∧
      ∃ y, s.m.memory.readBytes (s.m.core.read .rsi).toNat (s.m.core.read .rdx).toNat = some y)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧
      ∀ x y, s.m.memory.readBytes (s.m.core.read .rdi).toNat (s.m.core.read .rdx).toNat = some x →
        s.m.memory.readBytes (s.m.core.read .rsi).toNat (s.m.core.read .rdx).toNat = some y →
        (low32 (t.m.core.read .rax) = 0#32 ↔ x = y)

/-- **The import table of the file-operand tiers**, by name. -/
def fileTable (E : Env) (R : ShaRep) (pinA : Word) (W : World) : List (Name × (PState → Res PState → Prop)) :=
  [(nm "__errno_location", errnoLocStep E W), (nm "error", errorMsgStep E pinA W),
   (nm "__ctype_get_mb_cur_max", mbCurMaxStep E W), (nm "memcmp", memcmpStep E W)] ++ shaTable E R W

end Silmaril.Elf.Link.Dyn.Streams
