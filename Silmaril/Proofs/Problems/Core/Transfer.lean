module

public import Silmaril.Problems.Core.Defs
public import Silmaril.X86.RelIsa.Thms
public import Silmaril.X86.FnContract.Thms

/-!
# Proofs of the problem-template transfer theorems

The longer proofs behind `Silmaril/Problems/Core/Thms.lean`: spec implication
(`mustTotal_mono_sub`, `specImplies_trans`), the deterministic reading of `MustTotal`
(`total_of_mustTotal_ofIsa`), and refutation from one invariant (`never_refutes_core`,
`never_refutes`, `refutesAll_of_never`).
-/

@[expose] public section

namespace Silmaril.Proofs.Problems.Core

open Silmaril.Problems
open Silmaril.X86 (RelIsa Word)
open Silmaril.X86.FnContract (Spec AbiEntry)
open Silmaril.X86.RelIsa (Must Le Views)

variable {σ : Type}

/-- `Spec.MustTotal` is monotone along `Spec.Sub`. -/
theorem mustTotal_mono_sub {A : RelIsa σ} {S T : Spec σ} (hst : S.Sub T) (h : S.MustTotal A) :
    T.MustTotal A := by
  intro s hl habi hT
  exact RelIsa.Must.mono (fun _ h => h)
    (fun t ht => ⟨ht.silent, ht.abi,
      Silmaril.Process.Memory.WritesWithin.mono ht.frame (fun a ha => hst.footprint s a hT ha),
      hst.post s t hT ht.post⟩)
    (h s hl habi (hst.entry s hT))

/-- Spec implication is transitive. -/
theorem specImplies_trans {A B D : Word → Spec σ} (hab : SpecImplies A B)
    (hbd : SpecImplies B D) : SpecImplies A D := fun e =>
  ⟨fun s h => (hab e).entry s ((hbd e).entry s h),
   fun s a h ha => (hbd e).footprint s a h ((hab e).footprint s a ((hbd e).entry s h) ha),
   fun s t h hp => (hbd e).post s t h ((hab e).post s t ((hbd e).entry s h) hp)⟩

/-- On a deterministic machine, demonic total correctness is total correctness. -/
theorem total_of_mustTotal_ofIsa {I : Silmaril.X86.SegVC.Isa σ} {S : Spec σ}
    (h : S.MustTotal (RelIsa.ofIsa I)) : S.Total I := by
  intro s hl habi he
  obtain ⟨t, hr, hres⟩ := RelIsa.must_ofIsa_iff.1 (h s hl habi he)
  exact ⟨t, Silmaril.X86.FnContract.runsIn_reaches hr,
    ⟨hres.silent, hres.abi, hres.frame, hres.post⟩⟩

/-- On a deterministic machine, total correctness is demonic total correctness. -/
theorem mustTotal_ofIsa_of_total {I : Silmaril.X86.SegVC.Isa σ} {S : Spec σ} (h : S.Total I) :
    S.MustTotal (RelIsa.ofIsa I) := by
  intro s hl ha he
  obtain ⟨t, ⟨n, hn⟩, hr⟩ := h s hl ha he
  exact RelIsa.must_ofIsa_iff.2
    ⟨t, Silmaril.X86.FnContract.RunsIn.of_run hn, ⟨hr.silent, hr.abi, hr.frame, hr.post⟩⟩

/-- An invariant of the top `A` that excludes `Q`, is closed under `A`'s ok-steps and lies
inside `C.live` refutes `Must C R Q` for every `C` below `A` with `Progress`. -/
theorem never_refutes_core {A C : RelIsa σ} {R Q Inv : σ → Prop}
    (hQ : ∀ s, Inv s → ¬ Q s) (hstep : ∀ s t, Inv s → A.step s (.ok t) → Inv t)
    (hlive : ∀ s, Inv s → C.live s) (hle : Le C A) (hprog : C.Progress) :
    ∀ s, Inv s → ¬ Must C R Q s := by
  intro s hs hm
  induction hm with
  | done hq => exact hQ _ hs hq
  | step _ hns _ ih =>
    rename_i s' _ _
    obtain ⟨r, hr⟩ := hprog s' (hlive s' hs)
    cases r with
    | stop => exact hns hr
    | ok t => exact ih t hr (hstep s' t hs (hle.step (hlive s' hs) hr))

/-- If the loose top `A` never reaches `Q` from a live state `s`, then no admissible
refinement `C` can demonically reach `Q` from `s`. -/
theorem never_refutes {A C : RelIsa σ} {R Q : σ → Prop} {s : σ} (hA : Never A Q s)
    (hl : A.live s) (hC : Admissible A C) : ¬ Must C R Q s := by
  obtain ⟨I, hI, hcl⟩ := hA
  have hlv : C.live = A.live := hC.1.live_iff
  exact never_refutes_core (Inv := fun x => I x ∧ A.live x)
    (fun x hx => (hcl x hx.1).1)
    (fun x t hx ht => ⟨(hcl x hx.1).2 t ht, A.live_step hx.2 ht⟩)
    (fun x hx => hlv ▸ hx.2) hC.1 hC.2 s ⟨hI, hl⟩

/-- Every-model refutation of a function problem from one invariant. -/
theorem refutesAll_of_never {A : RelIsa σ} {S : Word → Spec σ} (hp : A.Progress) (entry : Word)
    (s : σ) (hl : A.live s) (habi : AbiEntry (A.core s) (A.mem s)) (he : (S entry).entry s)
    (hN : Never A ((S entry).ResultV A.toViews s) s) :
    RefutesAll (Class.below A) (FnJ S) := by
  refine ⟨⟨A, Le.refl A, hp⟩, fun C hC hJ => ?_⟩
  have hv : C.toViews = A.toViews := hC.1.views
  have hlC : C.live s := hC.1.live_iff ▸ hl
  have habiC : AbiEntry (C.core s) (C.mem s) := by
    rw [show C.core = A.core from congrArg Views.core hv,
      show C.mem = A.mem from congrArg Views.mem hv]
    exact habi
  have hm := hJ entry s hlC habiC he
  rw [hv] at hm
  exact never_refutes hN hl hC hm

end Silmaril.Proofs.Problems.Core
