module

public import Silmaril.Proofs.Wasm.Models.V2Core.Behaviours
public import Silmaril.Proofs.Wasm.Models.V2Core.CallInv

/-!
# Behaviours are not equal at the deterministic profile without a hypothesis

A counterexample to equality of 2.0 and Core behaviours at `Profile.deterministic g` for every
host. A 2.0 null carries its reference type, but a Core null does not
(`Ref.toCore (.null _) = .null`). So `ref.null func` and `ref.null extern` have the same Core
image. The induced host `liftHost src` answers a Core call with the outcome `src` gives to
*some* 2.0 preimage of the arguments.

* `st`: a store with one host function of type `[funcref] → []`;
* `src`: on the argument `ref.null extern` the host returns nothing; on `ref.null func` it
  diverges;
* `stuck_or_loop`: invoking the function on `ref.null func` steps only to itself;
* `core_returns`: Core, invoked on the common image `[ref.null]`, returns `[]`. This is the
  2.0 run on `ref.null extern`, sent forward by `behaviours_sub`;
* **`det_eq_false`**: the 2.0 behaviours on `ref.null func`, read in Core values, are not the
  Core behaviours of the image.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.DetFalse

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Proofs.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Execution (Admin Config Step Steps vals Result)

/-- A host function of type `[funcref] → []`. -/
def fi : Silmaril.Wasm.V2.Execution.FuncInst Unit :=
  { type := ⟨[Silmaril.Wasm.V2.ValType.funcref], []⟩, module := {}, code := .host () }

/-- The store holding `fi` at address `0`. -/
def st : VStore Unit := { funcs := [fi] }

/-- `ref.null func`. -/
def vFunc : VVal := .ref (.null .funcref)

/-- `ref.null extern`. -/
def vExt : VVal := .ref (.null .externref)

/-- The host: return on `ref.null extern`, diverge on `ref.null func`. -/
def src : VHost Unit := fun _ s vs out =>
  (vs = [vExt] ∧ out = .returned s (.values [])) ∨ (vs = [vFunc] ∧ out = .diverged)

theorem vFunc_toCore : [vFunc].map Silmaril.Wasm.V2.Execution.Val.toCore =
    [vExt].map Silmaril.Wasm.V2.Execution.Val.toCore := rfl

theorem st_wf : Silmaril.Wasm.V2.Execution.StoreWF st := by
  refine ⟨fun i x h => ?_, fun i x h => by simp [st] at h, fun i x h => by simp [st] at h,
    fun i x h => by simp [st] at h⟩
  rcases i with _ | i <;> simp [st] at h
  subst h
  intro a ha
  simp [fi] at ha

theorem st_toCore : ∃ X, Silmaril.Wasm.V2.Execution.Store.toCore st = some X := ⟨_, rfl⟩

theorem src_preserves : Silmaril.Wasm.V2.Execution.HostPreserves src := by
  rintro _ s _ s' _ (⟨-, h⟩ | ⟨-, h⟩) hwf
  · cases h
    exact ⟨hwf, Silmaril.ListExt.refl _ _⟩
  · cases h

theorem src_keeps : HostKeepsV src := by
  rintro _ s _ s' _ (⟨-, h⟩ | ⟨-, h⟩)
  · cases h
    rfl
  · cases h

/-- The configuration invoking `fi` on `ref.null func`. -/
abbrev c₀ : Config Unit := Silmaril.Wasm.V2.Execution.invoke st 0 [vFunc]

/-- **`c₀` steps only to itself.** -/
theorem stuck_or_loop {P : Profile} {c' : Config Unit} (h : Step P src c₀ c') : c' = c₀ := by
  obtain ⟨fi', hf, pre, args, hvs, hk, hcase⟩ := step_callAddr_inv h rfl
  simp only [Silmaril.Wasm.V2.Execution.Store.funcInst?, c₀,
    Silmaril.Wasm.V2.Execution.invoke, st, List.getElem?_cons_zero, Option.some.injEq] at hf
  subst hf
  have hpre : pre = [] := by
    have hl := congrArg List.length hvs
    simp only [List.length_cons, List.length_nil, List.length_append, hk, fi] at hl
    exact List.eq_nil_of_length_eq_zero (by simpa using hl)
  subst hpre
  simp only [List.nil_append] at hvs
  subst hvs
  rcases hcase with ⟨fn, hcode⟩ | ⟨hh, -, ⟨s', r, hr, -⟩ | ⟨-, heq⟩⟩
  · simp [fi] at hcode
  · rcases hr with ⟨hv, -⟩ | ⟨-, hout⟩
    · simp [vFunc, vExt] at hv
    · cases hout
  · exact heq

theorem steps_stay {P : Profile} {c' : Config Unit} (h : Steps P src c₀ c') : c' = c₀ := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    exact stuck_or_loop hs

/-- Core, invoked on the common image, returns `[]`. -/
theorem core_returns (P : Profile) {X : CStore Unit}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore st = some X) :
    Behaviour.returns [] ∈ Silmaril.Wasm.Execution.Core.behaviours P (liftHost src) X 0
      ([vFunc].map Silmaril.Wasm.V2.Execution.Val.toCore) := by
  have hsub := behaviours_sub P st_wf hX src_preserves src_keeps (a := 0) (by simp [st]) [vExt]
  rw [← vFunc_toCore] at hsub
  have hs : Step P src ⟨st, {}, vals [vExt] ++ [.callAddr 0]⟩
      ⟨st, {}, Result.toAdmin (.values [])⟩ :=
    Step.callAddrHost (fi := fi) (h := ()) (s := st) (s' := st) (r := .values []) rfl rfl rfl
      (Or.inl ⟨rfl, rfl⟩)
  have h2 : Behaviour.returns [] ∈
      Silmaril.Wasm.V2.Execution.behaviours P src st 0 [vExt] :=
    Or.inl ⟨_, .values [], .single hs, rfl, rfl⟩
  exact hsub ⟨_, h2, rfl⟩

/-- **Equality fails** at `Profile.deterministic g` for this store, host and argument. -/
theorem det_eq_false (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {X : CStore Unit} (hX : Silmaril.Wasm.V2.Execution.Store.toCore st = some X) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) src st 0 [vFunc]) ≠
      Silmaril.Wasm.Execution.Core.behaviours (Profile.deterministic g) (liftHost src) X 0
        ([vFunc].map Silmaril.Wasm.V2.Execution.Val.toCore) := by
  intro heq
  have hcore := core_returns (Profile.deterministic g) hX
  rw [← heq] at hcore
  obtain ⟨b, hb, hbmap⟩ := hcore
  rcases hb with ⟨c', r, hrun, hcode, rfl⟩ | ⟨rfl, -⟩
  · obtain rfl := steps_stay hrun
    exact callAddr_not_result r hcode
  · simp at hbmap

end Silmaril.Proofs.Wasm.Models.V2Core.DetFalse
