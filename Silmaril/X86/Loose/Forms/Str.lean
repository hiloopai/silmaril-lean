module

public import Silmaril.X86.Loose.Forms.Span
public import Silmaril.X86.Str9.Defs

/-!
# Loose forms: the string operations

Loose `EffSpec`s for the three string forms of `Str9`: `movsb` (`A4`), `rep movsq`
(`F3 48 A5`) and `rep stosq` (`F3 48 AB`). The form index is `Str9.Str`.

* **One element per step**, as `Str9`: with `rcx = 0`, `rep movsq`/`rep stosq` only advance
  `rip`; otherwise one quadword is moved or stored, `rsi`/`rdi` advance by 8, `rcx` decreases
  by one, and `rip` stays on the instruction unless the new `rcx` is `0`. So the spec of one
  instruction is the spec of one element, and a `k`-element `rep` is `k` loose steps.
* **Unspecified** where the element's read or write is not permitted (the machine may fault;
  `Str9` faults with `dataFault` before any register changes), and, for `rep movsq` with
  `rcx ≠ 0`, where the remaining source range `[rsi, rsi + 8 rcx)` and destination range
  `[rdi, rdi + 8 rcx)` overlap or either of them wraps past `2^64` (`strOverlap`). The overlap
  case is where fast-string hardware and the element-by-element reading could be told apart
  (`Str9/Defs.lean`); the spec does not choose.
* **The direction flag.** `Silmaril.X86.State` has no DF, so "unspecified when DF = 1" cannot
  be stated here: the spec, like `Str9`, is the DF = 0 spec (System V: DF is clear on entry and
  exit).
* No flag is read or written.

`strSpan i : Span` is the span of each form and `strSpec i := (strSpan i).toEffSpec`.
-/

@[expose] public section

namespace Silmaril.X86.Loose.Forms.Str

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Str9 (Str)

/-- The address of the next instruction. -/
def next (c : State) (l : Nat) : Word := c.rip + BitVec.ofNat 64 l

/-- The remaining `rep movsq` ranges overlap, or one of them wraps past `2^64`. -/
def strOverlap (c : State) : Bool :=
  let n := 8 * (c.read .rcx).toNat
  let s := (c.read .rsi).toNat
  let d := (c.read .rdi).toNat
  decide (s < d + n ∧ d < s + n) || decide (2 ^ 64 < s + n) || decide (2 ^ 64 < d + n)

/-- The core after one element of `rep movsq` (`src`) or `rep stosq` (`rcx ≠ 0`). -/
def elemCore (src : Bool) (c : State) (nx : Word) : State :=
  let t := ((if src then c.write .rsi (c.read .rsi + 8) else c).write .rdi
    (c.read .rdi + 8)).write .rcx (c.read .rcx - 1)
  { t with rip := if c.read .rcx - 1 = 0 then nx else c.rip }

/-- The span of `movsb`. -/
def movsbSpan : Span where
  rd c _ := some (c.read .rsi, 1)
  wr c _ x := some (c.read .rdi, 1, x)
  post c l _ :=
    { (c.write .rsi (c.read .rsi + 1)).write .rdi (c.read .rdi + 1) with rip := next c l }
  ws := [.rsi, .rdi]
  setsFlags := false

/-- The span of one element of `rep movsq`. -/
def repMovsqSpan : Span where
  extra c _ := decide (c.read .rcx ≠ 0) && strOverlap c
  rd c _ := if c.read .rcx = 0 then none else some (c.read .rsi, 8)
  wr c _ x := if c.read .rcx = 0 then none else some (c.read .rdi, 8, x)
  post c l _ := if c.read .rcx = 0 then { c with rip := next c l } else elemCore true c (next c l)
  ws := [.rsi, .rdi, .rcx]
  setsFlags := false

/-- The span of one element of `rep stosq`. -/
def repStosqSpan : Span where
  rd _ _ := none
  wr c _ _ := if c.read .rcx = 0 then none else some (c.read .rdi, 8, c.read .rax)
  post c l _ := if c.read .rcx = 0 then { c with rip := next c l } else elemCore false c (next c l)
  ws := [.rdi, .rcx]
  setsFlags := false

/-- The span of a string form. -/
def strSpan : Str → Span
  | .movsb => movsbSpan
  | .repMovsq => repMovsqSpan
  | .repStosq => repStosqSpan

/-- **The loose `EffSpec` of a string form.** -/
def strSpec (i : Str) : EffSpec := (strSpan i).toEffSpec

end Silmaril.X86.Loose.Forms.Str
