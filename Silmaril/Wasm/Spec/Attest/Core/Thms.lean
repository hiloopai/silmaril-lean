module

public import Silmaril.Wasm.Spec.Attest.Core.Defs
public import Silmaril.Wasm.Spec.Attest.Thms
public import Silmaril.Proofs.Wasm.Spec.Attest.CoreKit

/-!
# "May attest" for Core 3.0 modules: theorems

Every profile `P` (any `$ND`, relaxed choices, NaN and grow policy); no determinism; the plays
are those of `Silmaril.Wasm.Game.Strategy`, defined by Core `Step P` reduction.

* `mayCall_iff_not_neverCall`: a Core program `L` (only import `attest`) may attest iff
  `¬ Models neverCall (wasmSem P) L.prog attest`: "may attest" is the negation of the `neverCall`
  sentence of the specification institution `inst neverCall (wasmSem P)`.
* `leaf_trapProp`: Core programs propagate traps (`strategy_trapProp`: a trap answer to an
  import call ends the export call with a trap, by Core's trap rules through every context).
* `coreKit_ok`: the gate is trap-propagating; it calls `attest` only in plays where both
  `attestL` and `attestR` were asked (`gate_safe`, proved in the every-run program logic through
  `GameLink.strategy_sound`, from the invariants "`gL = 0`" with `attestL` forbidden and
  "`gR = 0`" with `attestR` forbidden); `attestL` trapped then `attestR` reaches `attest`
  (`gate_live`, explicit Core runs); `true` may attest (`tt_play`, an explicit Core run);
  `false` never does (the verifier: `check_sound` on `ffMod`).
* **`mayAttest_or`, `mayAttest_and`**: for all Core programs `L` and `R`,
  - `L` and `R` side by side may attest iff `L` or `R` may;
  - `L` and `R` linked to the gate may attest iff `L` and `R` may.
* **`mayAttest_enc`**: for every valuation of the variables by Core programs, the encoding of a
  positive formula may attest iff the formula holds when "`x`" means "`μ x` violates
  `neverCall attest`".
* `coreCorridor`, `core_entails_iff`: the corridor from positive logic, and borrowing.

New (no source).
-/

public section

namespace Silmaril.Wasm.Spec.Attest.Core

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm.Spec.Attest
  Silmaril.Logic.Institution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Execution.Core (Val)

/-- The import `attest` of a Core leaf. -/
abbrev attest {exps : List FnType} : (⟨[unitFn], exps⟩ : WIface).Imp :=
  Silmaril.Proofs.Wasm.Spec.Attest.attImp

/-- "`L` violates `neverCall attest`" in the specification institution of `wasmSem P`. -/
abbrev Attests (P : Profile) (L : CoreLeaf) : Prop :=
  ¬ Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) L.prog attest

/-- **May attest is the negation of `neverCall attest`** (every profile). -/
theorem mayCall_iff_not_neverCall (P : Profile) (L : CoreLeaf) :
    MayCall (L.toAMod P).σ ↔ Attests P L :=
  Silmaril.Proofs.Wasm.Spec.Attest.mayCall_iff_not_neverCall P L

/-- **Core programs propagate traps** (every profile, every store). -/
theorem strategy_trapProp (I : ScalarInstance) (P : Profile) (s : Silmaril.Wasm.Execution.Core.Store Nat) :
    TrapProp (I.strategy P s) trapAns trapAns :=
  Silmaril.Proofs.Wasm.Spec.Attest.strategy_trapProp I P s

/-- Core leaves propagate traps. -/
theorem leaf_trapProp (P : Profile) (L : CoreLeaf) :
    TrapProp (L.toAMod P).σ trapAns (L.toAMod P).stop :=
  Silmaril.Proofs.Wasm.Spec.Attest.leaf_trapProp P L

/-- **Gate safety** (every profile, every run): a play of the gate that calls `attest` asks both
`attestL` and `attestR`. -/
theorem gate_safe (P : Profile) : ∀ s ∈ gateI.strategy P gateI.store,
    (∃ m : Att.Op, (.inl (.ask m) : Move Att GateSig) ∈ s) →
      (∃ a, (.inr (.ask (ιL.op a)) : Move Att GateSig) ∈ s) ∧
        (∃ a, (.inr (.ask (ιR.op a)) : Move Att GateSig) ∈ s) :=
  Silmaril.Proofs.Wasm.Spec.Attest.gate_safe P

/-- **Gate liveness** (every profile): `attestL` trapped, then `attestR`, calls `attest`. -/
theorem gate_live (P : Profile) : ∃ e, [.inr (.ask (gateOp 0)), .inr (.ans (gateOp 0) .trap),
    .inr (.ask (gateOp 1)), .inl (.ask e)] ∈ gateI.strategy P gateI.store :=
  Silmaril.Proofs.Wasm.Spec.Attest.gate_live P

/-- **The Core 3.0 kit satisfies the kit laws** (every profile). -/
theorem coreKit_ok (P : Profile) : (coreKit P).Ok trapAns :=
  Silmaril.Proofs.Wasm.Spec.Attest.coreKit_ok P

/-- **`true` attests**: its export `fire` reaches the call of `attest` (every profile). -/
theorem tt_attests (P : Profile) : Attests P (leafOf ttMod) :=
  (mayCall_iff_not_neverCall P _).1 (coreKit_ok P).tt_may

/-- **`false` never attests**, by the verifier (every profile). -/
theorem ff_neverCall (P : Profile) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (leafOf ffMod).prog attest :=
  Silmaril.Proofs.Wasm.Spec.Attest.ff_neverCall P

/-- **Disjunction of Core programs**: side by side, they may attest iff one of them does. -/
theorem mayAttest_or (P : Profile) (L R : CoreLeaf) :
    MayCall (orM (L.toAMod P) (R.toAMod P)).σ ↔ Attests P L ∨ Attests P R := by
  rw [mayCall_or, mayCall_iff_not_neverCall, mayCall_iff_not_neverCall]

/-- **Conjunction of Core programs**: linked to the gate, they may attest iff both do. -/
theorem mayAttest_and (P : Profile) (L R : CoreLeaf) :
    MayCall (andM (coreKit P) (L.toAMod P) (R.toAMod P)).σ ↔ Attests P L ∧ Attests P R := by
  rw [mayCall_and (coreKit P) (coreKit_ok P) _ _ (leaf_trapProp P L), mayCall_iff_not_neverCall,
    mayCall_iff_not_neverCall]

/-- **Soundness and completeness of the encoding over Core programs** (every profile): for every
valuation `μ` of the variables by Core programs, the encoding of `φ` may call `attest` iff `φ`
holds when each variable `x` means "`μ x` violates `neverCall attest`". -/
theorem mayAttest_enc (P : Profile) {V : Type} (μ : V → CoreLeaf) (φ : PForm V) :
    MayCall (enc (coreKit P) (fun x => (μ x).toAMod P) φ).σ ↔ φ.Holds (fun x => Attests P (μ x)) := by
  have h := mayCall_enc (coreKit_ok P) (fun x => leaf_trapProp P (μ x)) φ
  have hv : valOf (fun x => (μ x).toAMod P) = fun x => Attests P (μ x) :=
    funext fun x => propext (mayCall_iff_not_neverCall P (μ x))
  rw [hv] at h
  exact h

/-- The corridor from positive logic to attesting Core-based modules at `V`. -/
noncomputable def coreCorridor (P : Profile) (V : Type) : Corridor (plRoom V) (attRoom (coreKit P) trapAns V) :=
  corridor (coreKit P) (coreKit_ok P) V

/-- **Borrowing over Core 3.0**: consequence between positive formulas is the same for
valuations and for attesting modules. -/
theorem core_entails_iff (P : Profile) {V : Type} (Γ : Set (PForm V)) (φ : PForm V) :
    (plRoom V).Entails Γ φ ↔ (attRoom (coreKit P) trapAns V).Entails Γ φ :=
  entails_iff (coreKit P) (coreKit_ok P) Γ φ

end Silmaril.Wasm.Spec.Attest.Core
