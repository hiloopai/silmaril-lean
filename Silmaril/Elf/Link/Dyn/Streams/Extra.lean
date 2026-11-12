module

public import Silmaril.Elf.Link.Dyn.Streams.Defs

/-! # Two more stream contracts for `sha256sum`'s output path (to be added to `shaContracts`)

`sha256sum` prints a result line with `print_filename` (`0x41a0`), which, when the name needs
no escaping, tail-calls **`fputs_unlocked (name, stdout)`**; before that, `main` tests whether
the name needs escaping with **`strcspn (name, "\\\n")`** (when the line delimiter is `\n`).
Neither is in `shaContracts`. Same frame (`LibRet`) and stream conventions as `Streams.Defs`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Streams

open Silmaril.X86 (Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc

/-- **`strcspn (s, reject)`**: the length of the longest prefix of `s` with no byte of
`reject`. -/
def strcspnStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ a, CStr s.m.memory (s.m.core.read .rdi) a) ∧
      ∃ b, CStr s.m.memory (s.m.core.read .rsi) b)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧
      ∀ a b, CStr s.m.memory (s.m.core.read .rdi) a → CStr s.m.memory (s.m.core.read .rsi) b →
        t.m.core.read .rax = BitVec.ofNat 64 (a.takeWhile (fun c => !b.contains c)).length

/-- **`fputs_unlocked (str, stdout)`**: appends the string (without its `NUL`) to `stdout`;
non-negative on success when writes do not fail. -/
def fputsStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ s.m.core.read .rsi = E.stdoutF ∧
      (∃ st, StdoutIs E s.m.memory st) ∧ ∃ str, CStr s.m.memory (s.m.core.read .rdi) str)
    fun t => LibRet E W (fun _ => False) s t ∧ GhostOut s t ∧ OthersKept E s t [E.stdoutF] ∧
      ∀ str, CStr s.m.memory (s.m.core.read .rdi) str → Appended E W s t str ∧
        (W.reliable = true → (low32 (t.m.core.read .rax)).msb = false)

end Silmaril.Elf.Link.Dyn.Streams
