module

public import Silmaril.Elf.Link.Dyn.Proc.Defs
public import Silmaril.Elf.Link.Dyn.Stdio.Defs

/-! # `stdio` contracts: `scanf("%d %d", &a, &b)` and `printf("%d\n", x)`

Named contracts (`Proc.Fn.named`, `World.named`) for the C library's formatted I/O, over the
library state's `stdin` (`Ghost.inp`) and `stdout` (`Ghost.out`). `Stdio.scanDD` and
`Stdio.decStr` give the bytes. The frame is that of `Proc.Returns` over the kept addresses
`kept` (the executable's image and argument area), except `scanf`'s output objects; `fsBase`
and the stack protector's guard at `%fs:0x28` are kept (glibc never writes the guard after
start-up), again except `scanf`'s output objects. `scanf` is specified only for two disjoint,
readable and writable `int` objects. Every contract has an outcome from every state
(`NonVacuous.stdioNamed_total`): none of them assumes more of glibc than it can do. Trusted: that glibc 2.39's `__isoc99_scanf`, `printf`, `__printf_chk` behave so for
these two formats. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte Reg)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)


/-- The frame of a stdio call entered at `s`: System V return, `fsBase` kept, the kept
addresses and the stack at and above the entry `rsp` and the guard `%fs:0x28` unchanged,
except the bytes of the output objects `ex`, which stay mapped and backed; the stack page
below the entry `rsp` keeps its permissions. -/
def StdioFrame (kept : Nat → Prop) (s t : PState) (ex : Nat → Prop) : Prop :=
  AbiReturn s.m.core s.m.memory t.m.core ∧ t.m.core.fsBase = s.m.core.fsBase ∧
  Keeps (fun a => (kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ ex a) s.m.memory t.m.memory ∧
  (∀ a, ex a → (t.m.memory.bytes.get? a).isSome ∧
    ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a) ∧
  Keeps (fun a => (s.m.core.fsBase.toNat + 0x28 ≤ a ∧ a < s.m.core.fsBase.toNat + 0x30) ∧ ¬ ex a)
    s.m.memory t.m.memory ∧
  (∀ a acc, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat →
    t.m.memory.permits acc a = s.m.memory.permits acc a)

/-- The 4-byte object at `p`. -/
def In4 (p : Word) (a : Nat) : Prop := p.toNat ≤ a ∧ a < p.toNat + 4

/-- **`scanf("%d %d", rsi, rdx)`** (`__isoc99_scanf`): under its precondition, by
`Stdio.scanDD` of `stdin`: both converted, it stores them, returns `2` and consumes them; a
matching failure returns something else; an `int` overflow is undefined. -/
def scanfStep (kept : Nat → Prop) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ CStr s.m.memory (s.m.core.read .rdi) Stdio.fmtDD ∧
      s.m.memory.Permitted .write (s.m.core.read .rsi).toNat 4 ∧
      s.m.memory.Permitted .write (s.m.core.read .rdx).toNat 4 ∧
      s.m.memory.Permitted .read (s.m.core.read .rsi).toNat 4 ∧
      s.m.memory.Permitted .read (s.m.core.read .rdx).toNat 4 ∧
      ((s.m.core.read .rsi).toNat + 4 ≤ (s.m.core.read .rdx).toNat ∨
        (s.m.core.read .rdx).toNat + 4 ≤ (s.m.core.read .rsi).toNat))
    fun t => match Stdio.scanDD s.g.inp with
      | .ub => True
      | .ok a b rest =>
        StdioFrame kept s t (fun x => In4 (s.m.core.read .rsi) x ∨ In4 (s.m.core.read .rdx) x) ∧
        low32 (t.m.core.read .rax) = 2#32 ∧ t.g = { s.g with inp := rest } ∧
        t.m.memory.readBytes (s.m.core.read .rsi).toNat 4 = some (Stdio.le32 a) ∧
        t.m.memory.readBytes (s.m.core.read .rdx).toNat 4 = some (Stdio.le32 b)
      | .fail =>
        StdioFrame kept s t (fun x => In4 (s.m.core.read .rsi) x ∨ In4 (s.m.core.read .rdx) x) ∧
        low32 (t.m.core.read .rax) ≠ 2#32 ∧ t.g.jobs = s.g.jobs ∧ t.g.atexit = s.g.atexit ∧
        t.g.done = none ∧ t.g.out = s.g.out

/-- `printf("%d\n", x)` with the format in `fr` and `x` in the low half of `vr`: it appends
the decimal digits of `x` and a newline to `stdout` (a prefix of them unless `rel`, writes to
fd 1 do not fail). -/
def printfStepWith (fr vr : Reg) (kept : Nat → Prop) (rel : Bool) (s : PState) :
    Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ CStr s.m.memory (s.m.core.read fr) Stdio.fmtDN)
    fun t => StdioFrame kept s t (fun _ => False) ∧ t.g.jobs = s.g.jobs ∧
      t.g.atexit = s.g.atexit ∧ t.g.done = none ∧ t.g.inp = s.g.inp ∧
      (t.g.out = s.g.out ++ Stdio.decStr (low32 (s.m.core.read vr)).toInt ++ [10] ∨
       (rel = false ∧ ∃ p, p <+: Stdio.decStr (low32 (s.m.core.read vr)).toInt ++ [10] ∧
         t.g.out = s.g.out ++ p))

/-- **The named stdio contracts**: `__isoc99_scanf`, `printf`, `__printf_chk`
(`__printf_chk(flag, fmt, x)`) and `__stack_chk_fail` (anything: it aborts). -/
def stdioNamed (kept : Nat → Prop) (rel : Bool) (n : Name) : PState → Res PState → Prop :=
  if n = nm "__isoc99_scanf" then scanfStep kept
  else if n = nm "printf" then printfStepWith .rdi .rsi kept rel
  else if n = nm "__printf_chk" then printfStepWith .rsi .rdx kept rel
  else if n = nm "__stack_chk_fail" then fun _ _ => True
  else fun _ r => r = .stop

end Silmaril.Elf.Link.Dyn.Proc
