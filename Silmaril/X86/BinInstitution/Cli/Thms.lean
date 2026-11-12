module

public import Silmaril.X86.BinInstitution.Cli.Defs
public import Silmaril.Cli.Institution.Thms

/-!
# Process sentences and CLI models: theorems

PROVED (standard axioms):

* `must_reach`: a `Must` claim holds at every stopping state a finite run reaches, when the
  goal's states take no step;
* **`procModel_sat`**: when ended states stop, a satisfied process sentence `(T.sen φ).Sat C`
  makes `procModel C T` a model of `φ`;
* `procModel_mono`: on live states, a machine with fewer steps (`RelIsa.Le`: a finer ISA model)
  gives a model with fewer runs, so it satisfies whatever the coarser one does.
-/

@[expose] public section

namespace Silmaril.X86.BinInstitution

open Silmaril.X86 (Word Byte RelIsa)
open Silmaril.X86.RelIsa (Must)
open Silmaril.Cli.Institution (Level Out1)

variable {σ : Type}

/-- **Partial correctness from `Must`.** -/
theorem must_reach {A : RelIsa σ} {R Q : σ → Prop} {s u : σ} (hm : Must A R Q s)
    (hp : Relation.ReflTransGen (OkStep A) s u) (hstop : A.step u .stop)
    (hQ : ∀ x, Q x → ∀ t, ¬ OkStep A x t) : Q u := by
  induction hm generalizing u with
  | done hq =>
    rcases hp.cases_head with rfl | ⟨t, ht, -⟩
    · exact hq
    · exact (hQ _ hq t ht).elim
  | step _ hns _ ih =>
    rcases hp.cases_head with rfl | ⟨t, ht, hp'⟩
    · exact (hns hstop).elim
    · exact ih t ht hp' hstop

/-- **A satisfied process sentence makes the template's model satisfy the CLI sentence.** -/
theorem procModel_sat {C : RelIsa σ} {T : ProcTmpl σ} {φ : Silmaril.Cli.Institution.Sen Level.stream.sig}
    (hE : T.EndsStop C) (h : (T.sen φ).Sat C) : (procModel C T).Sat φ := by
  rintro s o ⟨rfl, r, st, u, e, out, hs, hl, hres, hp, hu, rfl⟩
  have hm := h r st hs hl hres
  have hend : (T.obs.ended u).isSome := by simp [hu]
  obtain ⟨e', out', he, hpost⟩ := must_reach hm hp ((hE r u hend .stop).mpr rfl)
    (fun x ⟨_, _, hx, _⟩ t ht => by
      change T.obs.ended x = _ at hx
      have := (hE r x (by simp [hx]) (.ok t)).mp ht
      cases this)
  change T.obs.ended u = some (e', out') at he
  rw [hu] at he
  cases he
  exact hpost

/-- A machine below `C'` on live states, with the same views, steps as `C'` with the imports
linked in. -/
theorem withImports_le {C C' : RelIsa σ} (hle : RelIsa.Le C C') {r : DynLoad}
    {Γ : Imports σ} {s : σ} {x : Silmaril.X86.RelIsa.Res σ} (hl : C.live s)
    (h : (withImports C r Γ).step s x) : (withImports C' r Γ).step s x := by
  obtain ⟨h1, h2⟩ := h
  have hv := hle.views
  have vc : C'.core = C.core := by show C'.toViews.core = C.toViews.core; rw [hv]
  have vm : C'.mem = C.mem := by show C'.toViews.mem = C.toViews.mem; rw [hv]
  have vl : C'.live = C.live := by show C'.toViews.live = C.toViews.live; rw [hv]
  refine ⟨?_, fun t ht => vl ▸ h2 t ht⟩
  show (match importAt r Γ (C'.core s).rip with
      | some X => C'.live s → Silmaril.X86.FnContract.AbiEntry (C'.core s) (C'.mem s) →
          X.entry s → ∃ t, x = .ok t ∧ X.ResultX C'.toViews s t
      | none => C'.step s x)
  rw [vc, vm, vl, ← hv]
  revert h1
  generalize importAt r Γ (C.core s).rip = I
  cases I with
  | some X => exact id
  | none => exact hle.step hl

/-- Runs of a machine with fewer steps are runs of the coarser one. -/
theorem reach_le {C C' : RelIsa σ} (hle : RelIsa.Le C C') {r : DynLoad} {Γ : Imports σ}
    {s u : σ} (hl : C.live s) (hp : Relation.ReflTransGen (OkStep (withImports C r Γ)) s u) :
    Relation.ReflTransGen (OkStep (withImports C' r Γ)) s u := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hst _ ih =>
    exact .head (withImports_le hle hl hst) (ih (hst.2 _ rfl))

/-- **A finer ISA model has fewer runs** (`RelIsa.Le`), so it satisfies what the coarser one
does (`Model.Sat.anti`). -/
theorem procModel_mono {C C' : RelIsa σ} (hle : RelIsa.Le C C') (T : ProcTmpl σ) :
    procModel C T ≤ procModel C' T := by
  rintro s o ⟨hs, r, st, u, e, out, hst, hl, hres, hp, hu, ho⟩
  have vl : C'.live = C.live := by show C'.toViews.live = C.toViews.live; rw [hle.views]
  exact ⟨hs, r, st, u, e, out, hst, vl ▸ hl, hres, reach_le hle hl hp, hu, ho⟩

end Silmaril.X86.BinInstitution
