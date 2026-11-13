module

public import Silmaril.Wasm.Atlas.Defs
public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs

/-!
# The program-logic charts

Code-level charts. Points are code fragments in context: a store, a frame, an operand stack and
structured instructions. Sentences are postconditions `Q : Post H`.

* `Logic.hoareChart P host`: `Q` holds when `vals vs ++ expression is` is safe for `Q` under
  Core (`Hoare.HWP`, partial correctness, every run). This is the Core semantics read at code
  level.
* `Logic.vcChart`: `Q` holds when the verification-condition generator's condition
  `VC.wpc inv k is Q s f vs` holds for some loop invariants `inv`. This is a syntactic chart:
  `wpc` unfolds by `simp`, and the tactic `wat_vc` decides most of it.

The transition `Logic.vcToHoare` (in `Thms`) is `VC.wpc_sound`.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Logic

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Core (Post)

/-- A code fragment in context: store, frame, operand stack, instructions. -/
abbrev Code (H : Type) : Type := Store H × Frame × List Val × List Instr

/-- **The Hoare chart**: partial correctness under Core. -/
def hoareChart (P : Profile) {H : Type} (host : HostSemantics H) : Chart where
  Pt := Code H
  Sen := Post H
  dom _ := True
  Sat x Q := Silmaril.Wasm.Logic.Hoare.HWP P host x.1 x.2.1 (vals x.2.2.1 ++ expression x.2.2.2) Q

/-- **The VC chart**: the generator's condition, for some loop invariants. -/
def vcChart (H : Type) : Chart where
  Pt := Code H
  Sen := Post H
  dom _ := True
  Sat x Q := ∃ (inv : Silmaril.Wasm.Logic.VC.Invs H) (k : Nat),
    Silmaril.Wasm.Logic.VC.wpc inv k x.2.2.2 Q x.1 x.2.1 x.2.2.1

end Silmaril.Wasm.Atlas.Logic
