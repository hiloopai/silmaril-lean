module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxDer.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.NxDer.Fwd

/-!
# Round 8, REH route 2: derivations go to the erased side without a swap set (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round8.NxDer`; see `docs/projects/spectec/README.md`. Definitions are in `Round8/NxDer/Defs.lean`; the proof is unrefined, in
`Silmaril/Raw/…/Round8/NxDer/Fwd.lean`, and the kernel check in `Silmaril/Proofs/…/Round8/NxDer/`.

* **`derFwdN`**: in `utf8Env B`, with primitives that conform (`NxSound.BuiltinsVT`) and commute
  with erasure on `EraseAll.gdE`, every `DDerivesB` derivation of a `grE` relation goes to the
  erased side, given that `otherwise` read through `O₁` goes across to `O'` (`hO`). This is round
  7's `EraseDer.dderivesB_fwd` without the swap set: no `DDerivesBQ`, no `TypFwd Q`, no `QInj`.
* **`derFwdN_BI`**: the same at round 4's primitives, with only `hO` as hypothesis.
* **`iterRels_fixed`** (kernel): every iterated premise of a `grE` rule iterates over a list.
* The hypothesis `hO` is not discharged. With SpecTec's `otherwise` (`Round6.Reading.otherwiseB`)
  on both sides it says that no earlier rule fires at the erased input when none fires at the
  original one, which is the backward direction. Seven rules of `Step_pure` have an `otherwise`
  premise.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxDer

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

/-- **Derivations of checked relations go to the erased side**, given conforming primitives that
commute with erasure on `gdE`, and `otherwise` going across. -/
theorem derFwdN {B : Builtins} (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) {O₁ O' : ElseI}
    (hO : ∀ x args i v, O₁ x args i v → O' x (args.map Swap.eraseA) i (Swap.eraseV v)) :
    DerFwdN (utf8Env B) O₁ O' :=
  fun hx hd => dderivesB_fwd hB H hO hx hd

/-- **`derFwdN` at round 4's primitives**, with `otherwise` going across as the only hypothesis. -/
theorem derFwdN_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {O₁ O' : ElseI}
    (hO : ∀ x args i v, O₁ x args i v → O' x (args.map Swap.eraseA) i (Swap.eraseV v)) :
    DerFwdN (NxPrims.envBI P hn host) O₁ O' :=
  derFwdN (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hO

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxDer.derFwdN_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms derFwdN_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxDer.iterRels_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms iterRels_fixed

end Silmaril.Wasm.SpecTec.Sim.Round8.NxDer
