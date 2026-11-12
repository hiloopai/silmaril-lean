module

public import Silmaril.Raw.SSA.Isotope.Institution.Observational.Basic
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIterIsomorphism
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.External
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Fault
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.ObservationTheory

/-!
# The observational institutions of let-case, let-iter and lambda-SSA

Each calculus gets a behavioural semantics in the sense of
`Silmaril.Isotope.Institution.Observational.Basic`, hence an observational institution over the
discrete category of scopes:

* `letCase Φ`: positional let-case terms `LetCase.LocallyNameless.Tm Empty Φ n`, behaviours read off
  `LetCase.Semantics.Eval`, `LetCase.Semantics.Fault` and
  `LetCase.Semantics.External.Diverges`;
* `letIter Φ`: positional let-iter terms `LetIter.LocallyNameless.Tm Empty Φ n`, behaviours read off
  `LetIter.Semantics.Eval`, `LetIter.Semantics.Fault` and
  `LetIter.Semantics.External.Diverges`;
* `lambdaSSA Φ labels`: lambda-SSA regions scoped with `labels` exits and `n` variables
  (`Morphism.SSAIter.ScopedRegion`), run in the environment `envOfBound` of the model's bound
  values; a finite result is an exit label together with a value.

All three share the same models (`Model Φ n`), so compilations can be comorphisms whose model
translation is the identity.

The bridges `iter_obs_iff` and `ssa_obs_iff` say that the existing observational equivalences
`LetIter.LocallyNameless.Tm.Obs` and `LambdaSSA.Region.Obs` are exactly validity of the
observational equation in every model, i.e. consequence from the empty theory. Let-case had no
observational equivalence before; `(letCase Φ).ObsEq` is that notion.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Institution.Observational

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (ScopedRegion envOfBound envOfBound_agrees)

variable {Φ : Type u}

/-- The empty free environment of positional terms. -/
def noFree {α : Type v} : Empty → Value α := fun e => e.elim

theorem eq_noFree {α : Type v} (free : Empty → Value α) : free = noFree :=
  funext fun e => e.elim

/-! ## Let-iter -/

/-- The behaviour of a positional let-iter term at a model. -/
def iterBeh {n : Nat} (M : Model.{u, v, w} Φ n) (t : LetIter.LocallyNameless.Tm Empty Φ n) :
    Set (Observation (Value M.α) M.σ) :=
  {o | o.Holds
    (fun s value s' => LetIter.Semantics.Eval M.instr noFree M.bound t s value s')
    (fun s s' => LetIter.Semantics.Fault M.instr M.faults noFree M.bound t s s')
    (fun s => LetIter.Semantics.External.Diverges M.instr noFree M.prim (.term M.bound t s))}

section IterMem

variable {n : Nat} {M : Model.{u, v, w} Φ n} {t : LetIter.LocallyNameless.Tm Empty Φ n}

@[simp] theorem ret_mem_iterBeh {s s' : M.σ} {value : Value M.α} :
    Observation.ret s value s' ∈ iterBeh M t ↔
      LetIter.Semantics.Eval M.instr noFree M.bound t s value s' := Iff.rfl

@[simp] theorem fault_mem_iterBeh {s s' : M.σ} :
    Observation.fault s s' ∈ iterBeh M t ↔
      LetIter.Semantics.Fault M.instr M.faults noFree M.bound t s s' := Iff.rfl

@[simp] theorem diverge_mem_iterBeh {s : M.σ} :
    Observation.diverge s ∈ iterBeh M t ↔
      LetIter.Semantics.External.Diverges M.instr noFree M.prim (.term M.bound t s) := Iff.rfl

end IterMem

/-- The behavioural semantics of positional let-iter terms. -/
def letIter (Φ : Type u) : Behaviour.{u, v, w} Φ where
  Prog n := LetIter.LocallyNameless.Tm Empty Φ n
  Out := Value
  beh M t := iterBeh M t

/-- **Bridge.** Let-iter observational equivalence (`LetIter.LocallyNameless.Tm.Obs`) is
validity of the observational equation in every model of the let-iter observational
institution. -/
theorem iter_obs_iff {n : Nat} (t t' : LetIter.LocallyNameless.Tm Empty Φ n) :
    LetIter.LocallyNameless.Tm.Obs.{u, v, w, 0} t t' ↔ (letIter.{u, v, w} Φ).ObsEq t t' := by
  refine Iff.trans ?_ ((letIter.{u, v, w} Φ).obsEq_iff t t').symm
  constructor
  · intro h M
    refine Observation.set_eq_iff.mpr ⟨fun s x s' => ?_, fun s s' => ?_, fun s => ?_⟩
    · exact h.eval
    · exact h.fault
    · exact h.diverges
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro α σ instr free bound s s' value
      obtain rfl := eq_noFree free
      exact (Observation.set_eq_iff.mp
        (h ⟨α, σ, instr, fun _ _ _ _ => False, fun _ _ _ => False, bound⟩)).1 s value s'
    · intro α σ instr faults free bound s s'
      obtain rfl := eq_noFree free
      exact (Observation.set_eq_iff.mp
        (h ⟨α, σ, instr, faults, fun _ _ _ => False, bound⟩)).2.1 s s'
    · intro α σ instr prim free bound s
      obtain rfl := eq_noFree free
      exact (Observation.set_eq_iff.mp
        (h ⟨α, σ, instr, fun _ _ _ _ => False, prim, bound⟩)).2.2 s

/-- Observationally equivalent let-iter terms have the same behaviour at every model. -/
theorem iterBeh_eq_of_obs {n : Nat} {t t' : LetIter.LocallyNameless.Tm Empty Φ n}
    (h : LetIter.LocallyNameless.Tm.Obs.{u, v, w, 0} t t') (M : Model.{u, v, w} Φ n) :
    iterBeh M t = iterBeh M t' :=
  ((letIter.{u, v, w} Φ).obsEq_iff t t').mp ((iter_obs_iff t t').mp h) M

/-- Every equation of the operationally sound let-iter fragment
`LetIter.LocallyNameless.ObsTheory` is valid in the let-iter observational institution, by
`LetIter.LocallyNameless.ObsTheory.sound`. -/
theorem iter_obsEq_of_obsTheory {n : Nat} {t t' : LetIter.LocallyNameless.Tm Empty Φ n}
    (h : LetIter.LocallyNameless.ObsTheory t t') : (letIter.{u, v, w} Φ).ObsEq t t' :=
  (iter_obs_iff t t').mp (LetIter.LocallyNameless.ObsTheory.sound h)

/-! ## Lambda-SSA -/

/-- The behaviour of a scoped lambda-SSA region at a model: results are exit labels with
values, and the region runs in the environment of the model's bound values. -/
def ssaBeh (labels : Nat) {n : Nat} (M : Model.{u, v, w} Φ n) (r : ScopedRegion Φ labels n) :
    Set (Observation (Nat × Value M.α) M.σ) :=
  {o | o.Holds
    (fun s x s' => LambdaSSA.Semantics.Region.Eval M.instr (envOfBound M.bound) r.val s x.1 x.2 s')
    (fun s s' => LambdaSSA.Semantics.Region.Fault M.instr M.faults (envOfBound M.bound) r.val s s')
    (fun s => LambdaSSA.Semantics.External.Diverges M.instr M.prim
      (.region (envOfBound M.bound) r.val s))}

section SSAMem

variable {labels n : Nat} {M : Model.{u, v, w} Φ n} {r : ScopedRegion Φ labels n}

@[simp] theorem ret_mem_ssaBeh {s s' : M.σ} {x : Nat × Value M.α} :
    Observation.ret s x s' ∈ ssaBeh labels M r ↔
      LambdaSSA.Semantics.Region.Eval M.instr (envOfBound M.bound) r.val s x.1 x.2 s' := Iff.rfl

@[simp] theorem fault_mem_ssaBeh {s s' : M.σ} :
    Observation.fault s s' ∈ ssaBeh labels M r ↔
      LambdaSSA.Semantics.Region.Fault M.instr M.faults (envOfBound M.bound) r.val s s' :=
  Iff.rfl

@[simp] theorem diverge_mem_ssaBeh {s : M.σ} :
    Observation.diverge s ∈ ssaBeh labels M r ↔
      LambdaSSA.Semantics.External.Diverges M.instr M.prim
        (.region (envOfBound M.bound) r.val s) := Iff.rfl

end SSAMem

/-- The behavioural semantics of lambda-SSA regions with `labels` exits. -/
def lambdaSSA (Φ : Type u) (labels : Nat) : Behaviour.{u, v, w} Φ where
  Prog n := ScopedRegion Φ labels n
  Out α := Nat × Value α
  beh M r := ssaBeh labels M r

section Agreement

variable {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}

/-- A scoped region evaluates the same way in any two environments that agree on its scope;
proved from `Morphism.SSAIter.encodeRegion_eval_iff`. -/
theorem scoped_eval_congr {labels n : Nat} {r : LambdaSSA.Region Φ} (h : r.Scoped labels n)
    {env env' : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    (agree : Morphism.CaseSSA.EnvAgrees env bound)
    (agree' : Morphism.CaseSSA.EnvAgrees env' bound) {s s' : σ} {label : Nat}
    {out : Value α} :
    LambdaSSA.Semantics.Region.Eval instr env r s label out s' ↔
      LambdaSSA.Semantics.Region.Eval instr env' r s label out s' := by
  by_cases hl : label < labels
  · have key : ∀ {e : LambdaSSA.Semantics.Env α}, Morphism.CaseSSA.EnvAgrees e bound →
        (LambdaSSA.Semantics.Region.Eval instr e r s label out s' ↔
          LetIter.Semantics.Eval instr noFree bound (Morphism.SSAIter.encodeRegion r h) s
            (Morphism.SSAIter.tagValue ⟨label, hl⟩ out) s') := by
      intro e ag
      rw [Morphism.SSAIter.encodeRegion_eval_iff h ag]
      constructor
      · intro run
        exact ⟨⟨label, hl⟩, out, run, rfl⟩
      · rintro ⟨i, value, run, heq⟩
        obtain ⟨rfl, rfl⟩ := (Morphism.SSAIter.tagValue_eq_iff _ _ _ _).mp heq
        exact run
    exact (key agree).trans (key agree').symm
  · exact ⟨fun run => absurd (h.eval_label_lt run) hl, fun run => absurd (h.eval_label_lt run) hl⟩

/-- Faults of a scoped region depend only on its scope; proved from
`Morphism.SSAIter.encodeRegion_fault_iff`. -/
theorem scoped_fault_congr {labels n : Nat} {r : LambdaSSA.Region Φ} (h : r.Scoped labels n)
    {env env' : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    (agree : Morphism.CaseSSA.EnvAgrees env bound)
    (agree' : Morphism.CaseSSA.EnvAgrees env' bound) {s s' : σ} :
    LambdaSSA.Semantics.Region.Fault instr faults env r s s' ↔
      LambdaSSA.Semantics.Region.Fault instr faults env' r s s' :=
  (Morphism.SSAIter.encodeRegion_fault_iff (free := noFree) h agree).symm.trans
    (Morphism.SSAIter.encodeRegion_fault_iff h agree')

/-- Divergences of a scoped region depend only on its scope; proved from
`Morphism.SSAIter.External.encodeRegion_diverges_iff`. -/
theorem scoped_diverges_congr {labels n : Nat} {r : LambdaSSA.Region Φ} (h : r.Scoped labels n)
    {env env' : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    (agree : Morphism.CaseSSA.EnvAgrees env bound)
    (agree' : Morphism.CaseSSA.EnvAgrees env' bound) {s : σ} :
    LambdaSSA.Semantics.External.Diverges instr prim (.region env r s) ↔
      LambdaSSA.Semantics.External.Diverges instr prim (.region env' r s) :=
  (Morphism.SSAIter.External.encodeRegion_diverges_iff (free := noFree) h agree).symm.trans
    (Morphism.SSAIter.External.encodeRegion_diverges_iff h agree')

end Agreement

/-- **Bridge.** Lambda-SSA observational equivalence of scoped regions
(`LambdaSSA.Region.Obs`) is validity of the observational equation in every model of the
lambda-SSA observational institution. The models carry only the `n` bound values; the regions
are scoped, so the values of the remaining variables are unobservable
(`scoped_eval_congr`, `scoped_fault_congr`, `scoped_diverges_congr`). -/
theorem ssa_obs_iff {labels n : Nat} (r r' : ScopedRegion Φ labels n) :
    LambdaSSA.Region.Obs.{u, v, w} r.val r'.val ↔ (lambdaSSA.{u, v, w} Φ labels).ObsEq r r' := by
  refine Iff.trans ?_ ((lambdaSSA.{u, v, w} Φ labels).obsEq_iff r r').symm
  constructor
  · intro h M
    refine Observation.set_eq_iff.mpr ⟨fun s x s' => ?_, fun s s' => ?_, fun s => ?_⟩
    · exact h.eval
    · exact h.fault
    · exact h.diverges
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro α σ instr env s s' label out
      have agree : Morphism.CaseSSA.EnvAgrees env (fun i : Fin n => env i.val) := fun _ => rfl
      have hM := (Observation.set_eq_iff.mp
        (h ⟨α, σ, instr, fun _ _ _ _ => False, fun _ _ _ => False,
          fun i : Fin n => env i.val⟩)).1 s (label, out) s'
      exact (scoped_eval_congr r.property agree (envOfBound_agrees _)).trans
        (hM.trans (scoped_eval_congr r'.property agree (envOfBound_agrees _)).symm)
    · intro α σ instr faults env s s'
      have agree : Morphism.CaseSSA.EnvAgrees env (fun i : Fin n => env i.val) := fun _ => rfl
      have hM := (Observation.set_eq_iff.mp
        (h ⟨α, σ, instr, faults, fun _ _ _ => False, fun i : Fin n => env i.val⟩)).2.1 s s'
      exact (scoped_fault_congr r.property agree (envOfBound_agrees _)).trans
        (hM.trans (scoped_fault_congr r'.property agree (envOfBound_agrees _)).symm)
    · intro α σ instr prim env s
      have agree : Morphism.CaseSSA.EnvAgrees env (fun i : Fin n => env i.val) := fun _ => rfl
      have hM := (Observation.set_eq_iff.mp
        (h ⟨α, σ, instr, fun _ _ _ _ => False, prim, fun i : Fin n => env i.val⟩)).2.2 s
      exact (scoped_diverges_congr r.property agree (envOfBound_agrees _)).trans
        (hM.trans (scoped_diverges_congr r'.property agree (envOfBound_agrees _)).symm)

/-- Observationally equivalent scoped regions have the same behaviour at every model. -/
theorem ssaBeh_eq_of_obs {labels n : Nat} {r r' : ScopedRegion Φ labels n}
    (h : LambdaSSA.Region.Obs.{u, v, w} r.val r'.val) (M : Model.{u, v, w} Φ n) :
    ssaBeh labels M r = ssaBeh labels M r' :=
  ((lambdaSSA.{u, v, w} Φ labels).obsEq_iff r r').mp ((ssa_obs_iff r r').mp h) M

/-! ## Let-case -/

/-- The behaviour of a positional let-case term at a model. Let-case has no loops, so all
divergence is primitive divergence. -/
def caseBeh {n : Nat} (M : Model.{u, v, w} Φ n) (t : LetCase.LocallyNameless.Tm Empty Φ n) :
    Set (Observation (Value M.α) M.σ) :=
  {o | o.Holds
    (fun s value s' => LetCase.Semantics.Eval M.instr noFree M.bound t s value s')
    (fun s s' => LetCase.Semantics.Fault M.instr M.faults noFree M.bound t s s')
    (fun s => LetCase.Semantics.External.Diverges M.instr M.prim noFree M.bound t s)}

section CaseMem

variable {n : Nat} {M : Model.{u, v, w} Φ n} {t : LetCase.LocallyNameless.Tm Empty Φ n}

@[simp] theorem ret_mem_caseBeh {s s' : M.σ} {value : Value M.α} :
    Observation.ret s value s' ∈ caseBeh M t ↔
      LetCase.Semantics.Eval M.instr noFree M.bound t s value s' := Iff.rfl

@[simp] theorem fault_mem_caseBeh {s s' : M.σ} :
    Observation.fault s s' ∈ caseBeh M t ↔
      LetCase.Semantics.Fault M.instr M.faults noFree M.bound t s s' := Iff.rfl

@[simp] theorem diverge_mem_caseBeh {s : M.σ} :
    Observation.diverge s ∈ caseBeh M t ↔
      LetCase.Semantics.External.Diverges M.instr M.prim noFree M.bound t s := Iff.rfl

end CaseMem

/-- The behavioural semantics of positional let-case terms. -/
def letCase (Φ : Type u) : Behaviour.{u, v, w} Φ where
  Prog n := LetCase.LocallyNameless.Tm Empty Φ n
  Out := Value
  beh M t := caseBeh M t

end Silmaril.Isotope.Institution.Observational
