module

public import Silmaril.Wasm.Component.Adapter.Defs
public import Silmaril.Wasm.Component.Wiring.Thms
public import Silmaril.Wasm.Component.ABI.Thms

/-!
# Adapters: fusion laws

* `runChain_fuse`: two adjacent adapters can be replaced by one whose argument
  and result transformations are the (Kleisli) composites.
* **Adapter fusion** (`fuse_lower_lift`, `fuse_lift_lower`): a `canon lower` on
  top of a `canon lift` of the same function type is the fused
  canonicalisation `canon ft`; a `canon lift` on top of a `canon lower` is a
  type check `check ft`. The first uses that lifted values are well typed
  (`checkList_of_liftArgs`); the second is the canonical ABI round trip
  (`liftArgs_lowerArgs`).
* `canon_trivial`: for trivially represented types, `canon ft` is a flat type
  check (`canonFlat_trivial`).
* `runChain_append`, `runChain_interp`, `Impl.prog_interp`: wiring programs
  compose by concatenating chains (used by inlining and flattening).
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

/-! ## Chains -/

/-- Fusing two adjacent adapters. -/
theorem runChain_fuse {E : Sig.{0}} {a₁ a₂ a₁₂ : Adapter}
    (hd : ∀ x, a₁₂.down x = (a₁.down x).bind a₂.down)
    (hu : ∀ y, a₁₂.up y = (a₂.up y).bind a₁.up) (c : List Adapter)
    (k : Payload → Prog E (Option Payload)) :
    runChain (a₁ :: a₂ :: c) k = runChain (a₁₂ :: c) k := by
  funext x
  simp only [runChain, hd]
  cases a₁.down x with
  | none => rfl
  | some x' =>
    simp only [Option.bind_some]
    cases a₂.down x' with
    | none => rfl
    | some x'' =>
      simp only [Prog.bind_assoc, Prog.pure_bind, hu, Option.bind_assoc]

/-- Chains compose by concatenation. -/
theorem runChain_append {E : Sig.{0}} (c₁ c₂ : List Adapter)
    (k : Payload → Prog E (Option Payload)) :
    runChain (c₁ ++ c₂) k = runChain c₁ (runChain c₂ k) := by
  induction c₁ with
  | nil => rfl
  | cons ad c₁ ih => funext x; simp only [List.cons_append, runChain, ih]

/-- Interpreting a chain interprets its target. -/
theorem runChain_interp {E F : Sig.{0}} (θ : Handler E F) (c : List Adapter)
    (k : Payload → Prog F (Option Payload)) (x : Payload) :
    (runChain c k x).interp θ = runChain c (fun y => (k y).interp θ) x := by
  induction c generalizing x with
  | nil => rfl
  | cons ad c ih =>
    simp only [runChain]
    cases ad.down x with
    | none => rfl
    | some x' => simp only [Prog.interp_bind, ih, Prog.interp_pure]

/-! ## Adapter fusion -/

/-- **Fusion of `canon lower ∘ canon lift`**: the core caller and the core
callee are connected directly, through the canonicalisation `canonFlat`. -/
theorem fuse_lower_lift {E : Sig.{0}} (ft : FuncTy) (c : List Adapter)
    (k : Payload → Prog E (Option Payload)) :
    runChain (.lower ft :: .lift ft :: c) k = runChain (.canon ft :: c) k := by
  apply runChain_fuse
  · rintro (xs | vs)
    · simp only [Adapter.down, Option.bind_map]
      cases e : liftArgs ft.params xs with
      | none => simp [canonFlat, e]
      | some vs =>
        simp [canonFlat, e, checkLower, checkList_of_liftArgs e, Adapter.down]
    · rfl
  · rintro (ys | ws)
    · simp only [Adapter.up, Option.bind_map]
      cases e : liftArgs ft.results ys with
      | none => simp [canonFlat, e]
      | some ws =>
        simp [canonFlat, e, checkLower, checkList_of_liftArgs e, Adapter.up]
    · rfl

/-- **Fusion of `canon lift ∘ canon lower`**: by the canonical ABI round trip,
a component caller and callee are connected through a type check. -/
theorem fuse_lift_lower {E : Sig.{0}} (ft : FuncTy) (c : List Adapter)
    (k : Payload → Prog E (Option Payload)) :
    runChain (.lift ft :: .lower ft :: c) k = runChain (.check ft :: c) k := by
  apply runChain_fuse
  · rintro (xs | vs)
    · rfl
    · simp only [Adapter.down, Option.bind_map]
      unfold checkLower checkVals
      split_ifs with h
      · simp [Adapter.down, liftArgs_lowerArgs h]
      · rfl
  · rintro (ys | ws)
    · rfl
    · simp only [Adapter.up, Option.bind_map]
      unfold checkLower checkVals
      split_ifs with h
      · simp [Adapter.up, liftArgs_lowerArgs h]
      · rfl

/-- For trivially represented types the fused canonicalisation is a flat type
check. -/
theorem canon_trivial {E : Sig.{0}} (ft : FuncTy) (hp : ValTy.trivialList ft.params = true)
    (hr : ValTy.trivialList ft.results = true) (c : List Adapter)
    (k : Payload → Prog E (Option Payload)) :
    runChain (.canon ft :: c) k = runChain (.flatCheck ft.flat.params ft.flat.results :: c) k := by
  funext x
  have hd : (Adapter.canon ft).down x = (Adapter.flatCheck ft.flat.params ft.flat.results).down x := by
    rcases x with xs | vs
    · simp [Adapter.down, canonFlat_trivial hp, FuncTy.flat]
    · rfl
  have hu : (Adapter.canon ft).up = (Adapter.flatCheck ft.flat.params ft.flat.results).up := by
    funext y
    rcases y with ys | ws
    · simp [Adapter.up, canonFlat_trivial hr, FuncTy.flat]
    · rfl
  simp only [runChain, hd, hu]

/-! ## Interpreting wiring programs -/

/-- Interpreting a target call by a handler. -/
theorem Target.prog_call_interp {E : Sig.{0}} (θ : Handler E sigU) {e r : Nat} (hr : r < e)
    (x : Payload) : ((Target.call r).prog e x).interp θ = θ (r, x) := by
  simp only [Target.prog, hr, ↓reduceIte]
  exact Prog.bind_pure _

end Silmaril.Wasm.Component
