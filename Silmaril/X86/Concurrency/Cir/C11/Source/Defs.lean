module

public import Silmaril.X86.Concurrency.Cir.C11.Defs

/-!
# C11 tests on CIR: the modes against the source's variant

`C11Test.check` checks that the modes on the CIR program are *implementable* by the
x86 instructions (`modesOk`) and computes RC11 for them. It does not check that they are the
modes of the **C source**: the untrusted proposer puts them there from the sidecar and a
structural matcher. A proposer or matcher bug that strengthens a mode (an `acq` load labelled
`sc`, a result-slot store labelled `rlx`) can leave the RC11 verdict unchanged and pass `check`.

The C sources make that checkable without the sidecar. Every program is compiled once per
variant (`-DMODE=n`, `examples/litmus-c/c11.h`), and the variant fixes every mode:

| variant | `LD` | `ST` | `FADD` |
| --- | --- | --- | --- |
| 0 `na` | `na` | `na` | `na` load and `na` store |
| 1 `rlx` | `rlx` | `rlx` | `rlx` |
| 2 `ra` | `acq` | `rel` | `acqRel` |
| 3 `sc` | `sc` | `sc` (an `xchg`, an `sc` RMW in CIR) | `sc` |

The result globals `r0, r1, ...` are plain (`na`), and `F_SC()` is a seq_cst fence. So
`C11Test.srcModesOk` reads the variant from the test's `source` (`...#MODE=n`) and checks every
access of the CIR program: an access to a location named `r...` is `na`; an access to another
location has the variant's mode for its kind (a store in variant 3 must be an `sc` RMW: no plain
store is `sc`); an access to no location is the fence idiom (a locked `or 0`) with mode `sc`.
Addresses must be literals, except for the fence idiom's stack address. This is independent of
the sidecar and of the matcher (it uses only the C macros and the location names).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.C11

open Silmaril.X86.Concurrency.Cir

/-- The variant of a test from its source (`...#MODE=n`). -/
def variantOf (src : String) : Option Nat :=
  match src.toList.reverse with
  | d :: '=' :: 'E' :: 'D' :: 'O' :: 'M' :: '#' :: _ =>
    if d.isDigit then some (d.toNat - '0'.toNat) else none
  | _ => none

/-- The mode of a load (`LD`) in a variant. -/
def ldModeOf : Nat → Mode
  | 0 => .na
  | 1 => .rlx
  | 2 => .acq
  | _ => .sc

/-- The mode of a plain store (`ST`) in a variant (variant 3 has no plain store). -/
def stModeOf : Nat → Option Mode
  | 0 => some .na
  | 1 => some .rlx
  | 2 => some .rel
  | _ => none

/-- The mode of a read-modify-write (`FADD`, or `ST` as `xchg` in variant 3) in a variant
(variant 0 has none: its `FADD` is a plain load and store). -/
def rmwModeOf : Nat → Option Mode
  | 1 => some .rlx
  | 2 => some .acqRel
  | 3 => some .sc
  | _ => none

/-- The location containing an address, if any. -/
def locOf (locs : List Silmaril.X86.MemoryModel.Litmus.Loc) (a : Nat) :
    Option Silmaril.X86.MemoryModel.Litmus.Loc :=
  locs.find? fun l => decide (l.addr ≤ a ∧ a < l.addr + l.size)

/-- A result global (`r0`, `r1`, ...). -/
def isResult (l : Silmaril.X86.MemoryModel.Litmus.Loc) : Bool := l.name.toList.head? == some 'r'

/-- **The modes of a statement are the source's**, in variant `v` over locations `locs`. -/
def srcOk (locs : List Silmaril.X86.MemoryModel.Litmus.Loc) (v : Nat) : Stmt → Bool
  | .load _ m _ _ (.lit a) =>
    match locOf locs a with
    | some l => if isResult l then m == .na else m == ldModeOf v
    | none => false
  | .store m _ _ (.lit a) _ =>
    match locOf locs a with
    | some l => if isResult l then m == .na else some m == stModeOf v
    | none => false
  | .rmw _ m _ op (.lit a) _ =>
    match locOf locs a with
    | some l => !isResult l && some m == rmwModeOf v && op != .op .or
    | none => false
  | .rmw _ m _ op _ arg =>
    -- the fence idiom `lock or $0, d(%rsp)` on the private stack slot (`F_SC()`)
    op == .op .or && arg == .lit 0 && m == .sc
  | .load .. | .store .. => false
  | .seq s t => srcOk locs v s && srcOk locs v t
  | _ => true

/-- **Every mode of the test's CIR program is the one its source variant fixes.** -/
def C11Test.srcModesOk (c : C11Test) : Bool :=
  match variantOf c.tv.test.source with
  | some v => decide (v < 4) && c.tv.certs.all fun ct => srcOk c.tv.test.locs v ct.body
  | none => false

end Silmaril.X86.Concurrency.Cir.C11
