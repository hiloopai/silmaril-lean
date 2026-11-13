module

public import Silmaril.Wasm.Component.Lime1RT.Defs
public import Silmaril.Wasm.Models.Runtime.Thms
public import Silmaril.Wasm.Component.Param.Thms
public import Silmaril.Wasm.SingleThreaded.Agreement

/-!
# Core 3.0 restricted to Lime1 at runtime: the invariant

* `codeIn_fill`: replacing the hole of a callout context by runtime code of `S` keeps the code
  in `S`;
* `closed`: the runtime invariant of `lime1` is closed under the internal step `InternalP P`
  (`Rt.step_rtInFeat` at the host that refuses every call);
* `invoke_rtL`, `resume_rtL`: invocation from a store of `lime1` and resumption of a thread of
  the invariant stay in it;
* `respects`: an instance whose store is of `lime1` respects `lime1RT P`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1RT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
  Silmaril.Wasm.Component.Lime1RT
open Silmaril.Wasm.Numerics (Profile)

/-- Replacing the hole of a callout context by code of `S` keeps the filled code in `S`. -/
theorem codeIn_fill {S : FeatureSet} :
    ∀ (E : SingleThreaded.Ctx) {xs ys : List Admin}, Rt.CodeIn S (E.fill xs) →
      Rt.CodeIn S ys → Rt.CodeIn S (E.fill ys)
  | .top pre rest, xs, ys, h, hy => by
    simp only [SingleThreaded.Ctx.fill, Silmaril.Proofs.Wasm.Models.Rt.codeIn_append] at h ⊢
    exact ⟨⟨h.1.1, hy⟩, h.2⟩
  | .label pre n cont E rest, xs, ys, h, hy => by
    simp only [SingleThreaded.Ctx.fill, Silmaril.Proofs.Wasm.Models.Rt.codeIn_append,
      Silmaril.Proofs.Wasm.Models.Rt.codeIn_cons, Silmaril.Proofs.Wasm.Models.Rt.admIn_label] at h ⊢
    exact ⟨⟨h.1.1, ⟨h.1.2.1.1, codeIn_fill E h.1.2.1.2 hy⟩, trivial⟩, h.2⟩
  | .handler pre n cs E rest, xs, ys, h, hy => by
    simp only [SingleThreaded.Ctx.fill, Silmaril.Proofs.Wasm.Models.Rt.codeIn_append,
      Silmaril.Proofs.Wasm.Models.Rt.codeIn_cons, Silmaril.Proofs.Wasm.Models.Rt.admIn_handler] at h ⊢
    exact ⟨⟨h.1.1, ⟨h.1.2.1.1, codeIn_fill E h.1.2.1.2 hy⟩, trivial⟩, h.2⟩
  | .frame pre n f E rest, xs, ys, h, hy => by
    simp only [SingleThreaded.Ctx.fill, Silmaril.Proofs.Wasm.Models.Rt.codeIn_append,
      Silmaril.Proofs.Wasm.Models.Rt.codeIn_cons, Silmaril.Proofs.Wasm.Models.Rt.admIn_frame] at h ⊢
    exact ⟨⟨h.1.1, ⟨codeIn_fill E h.1.2.1 hy, trivial⟩⟩, h.2⟩

/-- The host that refuses every call keeps every store in `S`. -/
theorem hostIn_none {S : FeatureSet} {H : Type} :
    Rt.HostIn S (fun _ _ _ _ => False : HostSemantics H) :=
  fun _ _ _ _ _ h => h.elim

/-- **The runtime invariant of `lime1` is closed under the Core 3.0 internal step.** -/
theorem closed (P : Profile) : (lime1RT P).Closed := by
  intro H c c' hc hstep
  obtain ⟨f', code', he, hs⟩ := hstep
  obtain ⟨s', t'⟩ := c'
  simp only at he
  subst he
  exact Rt.step_rtInFeat hostIn_none hs hc

/-- Invoking a function of a store of `lime1` starts in the runtime invariant. -/
theorem invoke_rtL (P : Profile) {s : Store Nat} (hs : Rt.StoreIn lime1 s) (a : Nat)
    (xs : List Silmaril.Wasm.Execution.Runtime.Value) :
    RtL (H := Nat) (s, (core3P P).invoke (H := Nat) a xs) :=
  Rt.invoke_rtInFeat hs a _

/-- Resuming a thread of the runtime invariant stays in it. -/
theorem resume_rtL (P : Profile) {s : Store Nat} {t : SingleThreaded.Thread}
    (ht : RtL (H := Nat) (s, t)) (res : Silmaril.Wasm.Component.Engine.CallResult) :
    RtL (H := Nat) (s, (core3P P).resume s t res) := by
  show Rt.InFeat lime1 ((SingleThreaded.resume s t _).config s)
  simp only [SingleThreaded.resume]
  split
  · rename_i E a h args hd
    obtain ⟨fi, yy, ps, rs, _, _, _, _, _, hcode⟩ := SingleThreaded.decompose?_sound hd
    have hst := ht.2
    rw [SingleThreaded.Thread.config_store] at hst
    refine ⟨?_, by simpa [SingleThreaded.Thread.config] using hst⟩
    have hc : Rt.CodeIn lime1 (E.fill (vals args ++ [.ref (.func a), yy])) := hcode ▸ ht.1
    refine codeIn_fill E hc ?_
    cases (Silmaril.Wasm.Component.Engine.Core3.toCR res) with
    | values vs => exact Silmaril.Proofs.Wasm.Models.Rt.codeIn_vals vs
    | trap => exact ⟨trivial, trivial⟩
  · exact ht

/-- **An instance whose store is of `lime1` respects the runtime restriction to `lime1`.** -/
theorem respects (P : Profile) {I : EInstance (core3P P)}
    (hI : Rt.StoreIn lime1 (H := Nat) I.store) :
    Silmaril.Proofs.Wasm.Component.Param.Respects (lime1RT P) I (Rt.StoreIn lime1) where
  closed := closed P
  init := hI
  invoke s hs a _ xs := invoke_rtL P hs a xs
  store s t h := by
    have h2 := h.2
    rwa [SingleThreaded.Thread.config_store] at h2
  resume s t _ _ res h _ := resume_rtL P h res

/-- **The core semantics of a restriction agrees with the engine's on a module each of whose
instances respects the restriction.** -/
theorem engineSem_restrict_eq {E : Engine} {r : Restriction E} {M : Type} [CoreModule M]
    (emb : M → E.Module) (m : M)
    (hm : ∀ I, instOf E (emb m) (CoreModule.imports m) (CoreModule.exports m) = some I →
      ∃ Sto, Silmaril.Proofs.Wasm.Component.Param.Respects r I Sto) :
    (engineSem (restrict E r) M emb).sem m = (engineSem E M emb).sem m := by
  simp only [engineSem, Silmaril.Proofs.Wasm.Component.Param.instOf_restrict]
  cases h : instOf E (emb m) (CoreModule.imports m) (CoreModule.exports m) with
  | none => rfl
  | some I =>
    obtain ⟨Sto, hR⟩ := hm I h
    exact engineStrategy_restrict_eq hR _ _

end Silmaril.Proofs.Wasm.Component.Lime1RT
