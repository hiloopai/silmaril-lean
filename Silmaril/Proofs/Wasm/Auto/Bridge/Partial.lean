module

public import Silmaril.Proofs.Wasm.Auto.Bridge.Beh
public import Silmaril.Wasm.Verify.Check.Thms

/-!
# Partial correctness at the module level

`meets_orDiv_of_fspecValid`: a valid every-run specification (`FSpecValid`, partial correctness,
for instance from the VC generator's `genFunc_sound`) whose postcondition only allows returning
results the reference specification allows gives `Equiv.Meets` **up to divergence**
(`OrDiv R`: a behaviour diverges, or is `R`-related to an allowed one). Excluding divergence needs
total correctness (`behaviours_eq_of_tfspec`), which the VC generator does not prove yet.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile}

/-- The outcome of a finite run of `$invoke` to a result, under a valid specification. -/
theorem post_of_run {a : Nat} {S : FSpec Nat} {s : Store Nat} {args : List Val}
    (h : FSpecValid P SingleThreaded.Det.noHost a S) (hpre : S.pre s args) {c' : Config Nat}
    {r : Result} (hs : Steps P SingleThreaded.Det.noHost (invoke s a args) c')
    (hfin : c'.code = r.toAdmin) :
    ∃ o, Exits o c'.code ∧ callPost {} [] (S.post s args) c'.store c'.frame o := by
  have hw : HWP P SingleThreaded.Det.noHost s {} (invoke s a args).code
      (callPost {} [] (S.post s args)) := h.hwp_invoke hpre
  have hs' : Steps P SingleThreaded.Det.noHost ⟨s, {}, (invoke s a args).code⟩ c' := by
    rw [invoke_code] at hs ⊢
    exact hs
  rcases hw.sound hs' with ⟨c'', hc⟩ | hex
  · exact absurd hc (SingleThreaded.Exec.BehaviourRefinement.not_step_of_terminal ⟨r, hfin⟩)
  · exact hex

/-- An outcome of the top-level call postcondition, under a postcondition that only allows
results `σ` allows. -/
theorem normal_of_callPost {S : FSpec Nat} {s : Store Nat} {vs : List Val}
    {σ : Equiv.ImportSpec Val}
    (hpost : ∀ s' o, S.post s vs s' o → ∃ res, o = .normal res ∧ Behaviour.returns res ∈ σ vs)
    {s' : Store Nat} {f : Frame} {o : Outcome} (hq : callPost {} [] (S.post s vs) s' f o) :
    ∃ res, o = .normal res ∧ Behaviour.returns res ∈ σ vs := by
  obtain ⟨-, hq⟩ := hq
  rcases hq with ⟨res, rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨x, rfl, hr⟩
  · obtain ⟨res', hres, hm⟩ := hpost _ _ hr
    exact ⟨res', by rw [List.nil_append]; exact hres, hm⟩
  · obtain ⟨res', hres, -⟩ := hpost _ _ hr
    cases hres
  · obtain ⟨res', hres, -⟩ := hpost _ _ hr
    cases hres

/-- **Partial correctness against a reference specification** `σ`: every finite behaviour is
allowed by `σ` (`R`-related, `R` reflexive), divergence aside. -/
theorem meets_orDiv_of_fspecValid {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {s : Store Nat} {a : Nat} {S : FSpec Nat} {σ : Equiv.ImportSpec Val}
    (h : FSpecValid P SingleThreaded.Det.noHost a S)
    (hpre : ∀ vs, InvokeOk s a vs → S.pre s vs)
    (hpost : ∀ vs s' o, InvokeOk s a vs → S.post s vs s' o →
      ∃ res, o = .normal res ∧ Behaviour.returns res ∈ σ vs)
    (hne : ∀ vs, (σ vs).Nonempty) :
    Equiv.Meets (entryPoints P SingleThreaded.Det.noHost) (OrDiv R) s a σ := by
  intro vs hvs b hb
  by_cases hd : b = .diverges
  · obtain ⟨b', hb'⟩ := hne vs
    exact ⟨b', hb', Or.inl hd⟩
  · obtain ⟨c', r, hs, hfin, rfl⟩ : ∃ (c' : Config Nat) (r : Result),
        Steps P SingleThreaded.Det.noHost (invoke s a vs) c' ∧ c'.code = r.toAdmin ∧
          b = r.toBehaviour := exists_result_of_mem hb hd
    obtain ⟨o, he, hq⟩ := post_of_run h (hpre vs hvs) hs hfin
    obtain ⟨res, rfl, hm⟩ : ∃ res, o = .normal res ∧ Behaviour.returns res ∈ σ vs :=
      normal_of_callPost (hpost vs · · hvs) hq
    have hv : r.toAdmin = vals res := hfin.symm.trans he
    rw [result_eq_of_vals hv]
    exact ⟨_, hm, Or.inr (hR _)⟩

end Silmaril.Proofs.Wasm.Auto.Bridge