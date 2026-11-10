module

public import Silmaril.X86.RelIsa.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Str9.Thms
import Silmaril.Proofs.X86.RelIsa.Must

/-!
# Relational x86 machines: what is proved

Proofs of more than a few lines are in `Silmaril/Proofs/X86/RelIsa/Must.lean`.

* `Must`: `Must.step_iff_outcomes`, `Must.ofOutcomes`, `Must.mono`, `Must.bind`,
  `Must.of_le` (transfer along `Le`, from a live state), `Must.of_sim` (transfer along a
  simulation), `Must.exists_run` (a run, on a machine with `Progress`), `not_must_of_stop`;
* `Le.refl`, `Le.trans`, `Le.live_iff`; `Sim.of_le`, `Sim.refl`, `Sim.comp`;
* the deterministic case: `ofIsa_step_ok`, `ofIsa_step_stop`, `progress_ofIsa`,
  `must_ofIsa_iff` (on `ofIsa I`, `Must` is a `RunsIn` run);
* `FnContract.Spec.MustTotalIn.of_le`: demonic total correctness moves down along `Le`;
* the view equations `views_ofIsa_open9`, `views_ofIsa_str9`, and
  `ExtFrame.views_upd_keeps_ext`.
-/

@[expose] public section

namespace Silmaril.X86.RelIsa

open Silmaril.X86 (State MState)
open Silmaril.Process (Memory)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.FnContract (RunsIn)

variable {σ τ υ : Type} {A C B : RelIsa σ} {R R' Q Q' Q₁ Q₂ : σ → Prop} {s : σ}

/-! ## `Must` -/

/-- The step case of `Must`: every outcome is an `ok` whose state satisfies `Must`. -/
theorem Must.step_iff_outcomes :
    (¬ A.step s .stop ∧ ∀ t, A.step s (.ok t) → Must A R Q t) ↔
      ∀ r, A.step s r → ∃ t, r = .ok t ∧ Must A R Q t :=
  Proofs.X86.RelIsa.Must.step_iff_outcomes

/-- Build a step of `Must` from the outcome form. -/
theorem Must.ofOutcomes (hR : R s) (h : ∀ r, A.step s r → ∃ t, r = .ok t ∧ Must A R Q t) :
    Must A R Q s :=
  let h' := Must.step_iff_outcomes.2 h
  .step hR h'.1 h'.2

/-- Weaken the step condition and the target. -/
theorem Must.mono (hR : ∀ s, R s → R' s) (hQ : ∀ s, Q s → Q' s) (h : Must A R Q s) :
    Must A R' Q' s :=
  Proofs.X86.RelIsa.Must.mono hR hQ h

/-- **Sequential composition.** -/
theorem Must.bind (h : Must A R Q₁ s) (k : ∀ t, Q₁ t → Must A R Q₂ t) : Must A R Q₂ s :=
  Proofs.X86.RelIsa.Must.bind h k

/-- **Transfer along refinement**: a `Must` property of `A` holds for every live `C` with
fewer behaviours. -/
theorem Must.of_le (h : Le C A) (hl : C.live s) (hm : Must A R Q s) : Must C R Q s :=
  Proofs.X86.RelIsa.Must.of_le h hl hm

/-- **Extract a run** from a `Must` property of a machine that always has an outcome. -/
theorem Must.exists_run (hp : Progress C) (hl : C.live s) (hm : Must C R Q s) :
    ∃ t, RunsInR C R s t ∧ Q t :=
  Proofs.X86.RelIsa.Must.exists_run hp hl hm

/-- A machine that may stop at `s` cannot be shown to reach `Q` from `s` unless `Q s`. -/
theorem not_must_of_stop (hQ : ¬ Q s) (hs : A.step s .stop) : ¬ Must A R Q s :=
  Proofs.X86.RelIsa.not_must_of_stop hQ hs

/-! ## `Le` and `Sim` -/

theorem Le.refl (A : RelIsa σ) : Le A A := ⟨rfl, fun _ h => h⟩

theorem Le.live_iff (h : Le C A) : C.live = A.live := Proofs.X86.RelIsa.Le.live_iff h

theorem Le.trans (h₁ : Le C B) (h₂ : Le B A) : Le C A := Proofs.X86.RelIsa.Le.trans h₁ h₂

/-- Same-state refinement is a simulation along equality. -/
theorem Sim.of_le (h : Le C A) : Sim C A Eq := Proofs.X86.RelIsa.Sim.of_le h

theorem Sim.refl (A : RelIsa σ) : Sim A A Eq := Sim.of_le (Le.refl A)

/-- Simulations compose. -/
theorem Sim.comp {C : RelIsa υ} {B : RelIsa τ} {A : RelIsa σ} {R₁ : υ → τ → Prop}
    {R₂ : τ → σ → Prop} (h₁ : Sim C B R₁) (h₂ : Sim B A R₂) :
    Sim C A (fun c a => ∃ b, R₁ c b ∧ R₂ b a) :=
  Proofs.X86.RelIsa.Sim.comp h₁ h₂

/-- **Transfer along a simulation.** If the abstract machine `A` must reach `Q` from `a`,
every live concrete state `c` related to `a` must reach a state related to a `Q`-state; its
steps are taken from `R'`-states as long as `R'` follows from `R` along the relation. -/
theorem Must.of_sim {C : RelIsa τ} {A : RelIsa σ} {Rel : τ → σ → Prop} {R : σ → Prop}
    {R' : τ → Prop} {Q : σ → Prop} (h : Sim C A Rel) (hR : ∀ c a, Rel c a → R a → R' c)
    {c : τ} {a : σ} (hr : Rel c a) (hl : C.live c) (hm : Must A R Q a) :
    Must C R' (fun c' => ∃ a', Rel c' a' ∧ Q a') c :=
  Proofs.X86.RelIsa.Must.of_sim h hR hr hl hm

/-! ## Deterministic machines -/

section
variable {I : Isa σ}

theorem ofIsa_step_ok {t : σ} : (ofIsa I).step s (.ok t) ↔ I.step s = some t :=
  Proofs.X86.RelIsa.ofIsa_step_ok

theorem ofIsa_step_stop : (ofIsa I).step s .stop ↔ I.step s = none :=
  Proofs.X86.RelIsa.ofIsa_step_stop

/-- A deterministic machine always has an outcome. -/
theorem progress_ofIsa : Progress (ofIsa I) := Proofs.X86.RelIsa.progress_ofIsa

/-- On a deterministic machine, `Must` is exactly a run. -/
theorem must_ofIsa_iff : Must (ofIsa I) R Q s ↔ ∃ t, RunsIn I R s t ∧ Q t :=
  ⟨Proofs.X86.RelIsa.runsIn_of_must_ofIsa,
    fun ⟨_, h, hq⟩ => Proofs.X86.RelIsa.must_ofIsa_of_runsIn h hq⟩
end

/-! ## Views of the open machines -/

/-- The views of `Open9.isa` are the `MState` views. -/
theorem views_ofIsa_open9 : Views.ofIsa Silmaril.X86.Open9.isa = Views.mstate := rfl

/-- The views of `Str9.isa` are the `MState` views. -/
theorem views_ofIsa_str9 : Views.ofIsa Silmaril.X86.Str9.isa = Views.mstate := rfl

/-- An extension frame is kept by the view update. -/
theorem ExtFrame.views_upd_keeps_ext {E : Type} {V : Views σ} (F : ExtFrame V E) (s : σ)
    (c : State) (m : Memory) : F.ext (V.upd s c m) = F.ext s :=
  F.ext_upd s c m

end Silmaril.X86.RelIsa

namespace Silmaril.X86.FnContract

/-- **Demonic total correctness moves down along refinement.** -/
theorem Spec.MustTotalIn.of_le {σ : Type} {C A : RelIsa σ} {S : Spec σ} {P : σ → σ → Prop}
    (hle : RelIsa.Le C A) (h : S.MustTotalIn A P) : S.MustTotalIn C P :=
  Proofs.X86.RelIsa.mustTotalIn_of_le hle h

end Silmaril.X86.FnContract
