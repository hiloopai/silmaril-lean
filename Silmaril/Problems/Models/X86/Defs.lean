module

public import Silmaril.Problems.Core.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Str9.Thms
public import Silmaril.X86.Loose.Sv1
public import Silmaril.X86.Loose.Listing.Defs

/-!
# Machine models for problem statements

Statement modules import only `Defs` headers, but `Open9.isa` and `Str9.isa` are declared in
`Silmaril.X86.Open9.Thms` and `Silmaril.X86.Str9.Thms`. This header re-exports them and names
the loose top, so that a statement can use these machines while importing only this header.

* `looseSv1 D`: the **loose top** over an image listing's table `D : DTable LForm`
  (`Silmaril.X86.Loose.Listing`): the loose machine over the `Str9` part of `D`
  (`str9Part D`, the integer and string entries over `Str9.Instr`) with the form
  specifications `Σ v1` (`Silmaril.X86.Loose.Sv1`), on the open machine state. It is the top
  of the x86 signature `Exact.Sig.sv1 (str9Part D)` (`looseSv1_eq_top` in `Thms`). Its
  down-set `Class.below (looseSv1 D)` is the class of a "loose" problem; SSE, floating-point
  and unmodelled entries of `D` are unconstrained there.
* A deterministic machine enters a statement as `RelIsa.ofIsa Open9.isa` (or `Str9.isa`),
  written out rather than named, so that the machine's declaration appears literally in a
  some-model refutation's reference member.
* `RegStep F l W`: the common shape of a register-only form in a function proof: specified
  everywhere, and every admitted successor keeps memory, retires to the next instruction and
  writes only the registers `W`.

Nothing here is proved, and nothing new is assumed.
-/

@[expose] public section

namespace Silmaril.Problems.Models.X86

open Silmaril.X86 (MState RelIsa)
open Silmaril.X86.Loose (Sv1)
open Silmaril.X86.Loose.Listing (LForm str9Part)

/-- **The loose top** over a listing table `D`: the loose x86 machine over the `Str9` part
of `D`, with the form specifications `Σ v1`, on the open machine state. -/
def looseSv1 (D : Silmaril.X86.Loose.DTable LForm) : RelIsa MState :=
  Silmaril.X86.Loose.X86Loose.rel (str9Part D) Sv1 RelIsa.Views.mstate

/-- **A register-only step**: the form is specified everywhere, and an admitted successor
keeps memory, retires to the next instruction (at length `l`) and writes only the registers
`W`. -/
def RegStep (F : Silmaril.X86.Loose.EffSpec) (l : Nat) (W : List Silmaril.X86.Reg) : Prop :=
  ∀ c m, ¬ F.unspecified c m l ∧ ∀ c' m', (F.eff c m l).Admits c m c' m' →
    m' = m ∧ c'.rip = c.rip + BitVec.ofNat 64 l ∧ ∀ r, r ∉ W → c'.read r = c.read r

end Silmaril.Problems.Models.X86
