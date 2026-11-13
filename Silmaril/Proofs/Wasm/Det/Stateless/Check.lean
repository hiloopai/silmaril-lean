module

public import Silmaril.Proofs.Wasm.Det.Stateless.Runs

/-!
# Stateless code: soundness of the executable checks (proofs)

`checkSet_sound`: `checkSet s A R W = true` gives `GoodFuns A.contains R W s.funcs`. The checks
of the tactics (`statelessCheck`, `crCheck`, `moduleCheck`, `moduleStatelessCheck`, `detCheck`)
then give statelessness and determinism through `Silmaril.Proofs.Wasm.Det.Stateless.Runs`. The
closure computation (`closure`) and the read and write sets are not trusted: only the final
`checkSet` is. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Stateless

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.Stateless Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem checkSet_sound {s : Store H} {A : List Nat} {R W : Nat → Bool}
    (h : checkSet s A R W = true) : GoodFuns A.contains R W s.funcs := by
  intro a ha
  have hm : a ∈ A := by simpa using ha
  have h' := List.all_eq_true.mp h a hm
  cases hf : s.funcs[a]? with
  | none => simp [hf] at h'
  | some fi => exact ⟨fi, rfl, by simpa [hf] using h'⟩

theorem allAddrs_contains {s : Store H} {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
    (allAddrs s).contains a = true := by
  have hlt : a < s.funcs.length := (List.getElem?_eq_some_iff.mp h).1
  simpa [allAddrs] using hlt

theorem statelessCheck_spec {s : Store H} {a : Nat} (h : statelessCheck s a = true) :
    (closure s [a]).contains a = true ∧
      GoodFuns (closure s [a]).contains (readsOf s (closure s [a])).contains (fun _ => false)
        s.funcs := by
  simp only [statelessCheck, Bool.and_eq_true] at h
  exact ⟨h.1, checkSet_sound h.2⟩

/-- **Stateless check ⇒ statelessness** over the stores agreeing with `s` on the functions and on
the globals the function's call closure reads, at every profile. -/
theorem statelessFn_of_check {P : Profile} {s : Store Nat} {a : Nat}
    (h : statelessCheck s a = true) :
    StatelessFn P (fun t => Agree (readsOf s (closure s [a])).contains t s) a :=
  statelessFn_of_good (statelessCheck_spec h).2 (statelessCheck_spec h).1

/-- **Stateless check over call states ⇒ statelessness over the call states of every module
instance in `s₀`** (any entry functions), at every profile. -/
theorem statelessFn_callReach_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    {a : Nat} (h : crCheck s₀ a = true) : StatelessFn P (CallReach P Entry s₀) a := by
  simp only [crCheck, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hs, hr | ⟨hm, hdis⟩⟩ := h
  · have hR : (readsOf s₀ (closure s₀ [a])).contains = fun _ => false := by
      funext g
      simp [List.isEmpty_iff.mp hr]
    have hg := (statelessCheck_spec hs).2
    rw [hR] at hg
    exact statelessFn_callReach_funcs hg (statelessCheck_spec hs).1
  · have hRW : ∀ g, (readsOf s₀ (closure s₀ [a])).contains g = true →
        (writesOf s₀ (allAddrs s₀)).contains g = false := by
      intro g hg
      have hmem : g ∈ readsOf s₀ (closure s₀ [a]) := by simpa using hg
      simpa using List.all_eq_true.mp hdis g hmem
    exact statelessFn_callReach (checkSet_sound hm) (fun _ _ _ hf => allAddrs_contains hf)
      (statelessCheck_spec hs).2 (statelessCheck_spec hs).1 hRW

/-- **Stateless module check ⇒ the module is stateless** (any entry functions), at every
profile. -/
theorem statelessModule_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : moduleStatelessCheck s₀ = true) : StatelessModule P Entry s₀ :=
  statelessModule_of_good (checkSet_sound h) fun _ _ _ hf => allAddrs_contains hf

/-- **Determinism check ⇒ determinism**, at every profile. -/
theorem detFn_of_check {P : Profile} {s : Store Nat} {a : Nat} (h : detCheck s a = true) :
    DetFn P s a := by
  simp only [detCheck, Bool.and_eq_true] at h
  exact detFn_of_good (checkSet_sound h.2) h.1

/-- **Determinism check ⇒ determinism at every call state of a module**, at every profile. -/
theorem detFn_callReach_of_check {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat} {a : Nat}
    (h : detCheck s₀ a = true) (hs : CallReach P Entry s₀ s) : DetFn P s a := by
  simp only [detCheck, Bool.and_eq_true] at h
  exact detFn_of_good ((CallReach.funcs_eq hs).symm ▸ checkSet_sound h.2) h.1

/-- **Module check ⇒ the module is deterministic** (any entry functions), at every profile. -/
theorem detModule_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : moduleCheck s₀ = true) : DetModule P Entry s₀ :=
  detModule_of_good (checkSet_sound h) fun _ _ _ hf => allAddrs_contains hf

end Silmaril.Proofs.Wasm.Det.Stateless
