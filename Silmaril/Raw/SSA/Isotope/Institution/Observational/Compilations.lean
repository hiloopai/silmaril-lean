module

public import Silmaril.Raw.SSA.Isotope.Institution.Observational.Calculi

/-!
# Compilations as comorphisms of observational institutions

The three compilations between the Isotope calculi are translations of behavioural semantics,
hence comorphisms of observational institutions whose signature and model functors are
identities:

* `caseIter : letCase → letIter`, the constructor-preserving inclusion `Morphism.CaseIter.embed`;
  the satisfaction condition is `CaseIter.embed_eval`/`of_embed_eval`,
  `embed_fault`/`of_embed_fault` and `embed_diverges_iff`;
* `iterSSA : letIter → lambdaSSA 1`, the CPS compiler `IterSSA.compile` at the identity variable
  assignment and the single-exit continuation (`Morphism.SSAIter.compileSingle`); the
  satisfaction condition is `compileSingle_eval_iff`, `compileSingle_fault_iff` and
  `compileSingle_diverges_iff` (themselves `IterSSA.compile_return_*_iff`);
* `ssaIter labels : lambdaSSA labels → letIter`, the region encoding `SSAIter.encodeRegion`,
  whose results are exit-tagged (`SSAIter.tagValue`); the satisfaction condition is
  `encodeRegion_eval_iff`, `encodeRegion_fault_iff` and `External.encodeRegion_diverges_iff`;
* `ssaIterSingle : lambdaSSA 1 → letIter`, the untagged single-exit encoding
  `SSAIter.encodeSingle`, from `encodeSingle_eval_iff`, `encodeSingle_fault_iff` and
  `encodeSingle_diverges_iff`.

In each case the result translation is injective on the results that can occur (exit labels of a
scoped region are in range, `LambdaSSA.Region.Scoped.eval_label_lt`), and that is all the
satisfaction condition needs (`Behaviour.Translation.holds_map_iff`). All the comorphisms are
model-expansive, so observational consequence (equations and refinements, under hypotheses) is
borrowed along them.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Institution.Observational

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (ScopedRegion envOfBound envOfBound_agrees compileSingle
  compileSingle_scoped encodeSingle)

variable {Φ : Type u}

/-! ## Let-case into let-iter -/

/-- The inclusion of let-case into let-iter has exactly the behaviours of its source. Proved
from `Morphism.CaseIter.embed_eval`, `of_embed_eval`, `embed_fault`, `of_embed_fault` and
`embed_diverges_iff`. -/
theorem iterBeh_embed {n : Nat} (M : Model.{u, v, w} Φ n)
    (t : LetCase.LocallyNameless.Tm Empty Φ n) :
    iterBeh M (Morphism.CaseIter.embed t) = caseBeh M t := by
  ext o
  cases o with
  | ret s value s' =>
      rw [ret_mem_iterBeh, ret_mem_caseBeh]
      exact ⟨Morphism.CaseIter.of_embed_eval, Morphism.CaseIter.embed_eval⟩
  | fault s s' =>
      rw [fault_mem_iterBeh, fault_mem_caseBeh]
      exact ⟨Morphism.CaseIter.of_embed_fault, Morphism.CaseIter.embed_fault⟩
  | diverge s =>
      rw [diverge_mem_iterBeh, diverge_mem_caseBeh]
      exact Morphism.CaseIter.embed_diverges_iff

theorem injOn_id_univ {X : Type v} : Set.InjOn (id : X → X) Set.univ := Set.injOn_id _

theorem pair0_injOn {α : Type v} :
    Set.InjOn (fun value : Value α => ((0 : Nat), value)) Set.univ :=
  fun _ _ _ _ h => (Prod.mk.inj h).2

theorem image_mapValue_id {V : Type v} {σ : Type w} (S : Set (Observation V σ)) :
    Observation.mapValue id '' S = S := by
  rw [Observation.mapValue_id, Set.image_id]

/-- The inclusion `CaseIter.embed` as a translation of behavioural semantics. -/
def caseIter (Φ : Type u) : Behaviour.Translation (letCase.{u, v, w} Φ) (letIter.{u, v, w} Φ) where
  prog := Morphism.CaseIter.embed
  out := id
  dom := Set.univ
  injOn := fun {_} => @injOn_id_univ _
  beh_sub := fun _ _ o _ => by cases o <;> trivial
  beh_prog := fun M t => (iterBeh_embed M t).trans (image_mapValue_id _).symm

/-! ## Let-iter into lambda-SSA -/

/-- Compiling a let-iter term to a single-exit region tags every result with exit label `0`
and keeps faults and divergences. Proved from `Morphism.SSAIter.compileSingle_eval_iff`,
`compileSingle_fault_iff` and `compileSingle_diverges_iff`. -/
theorem ssaBeh_compileSingle {n : Nat} (M : Model.{u, v, w} Φ n)
    (t : LetIter.LocallyNameless.Tm Empty Φ n) :
    ssaBeh 1 M ⟨compileSingle t, compileSingle_scoped t⟩ =
      Observation.mapValue (fun value => ((0 : Nat), value)) '' iterBeh M t := by
  ext o
  cases o with
  | ret s x s' =>
      obtain ⟨label, out⟩ := x
      simp only [Observation.ret_mem_image_iff, ret_mem_iterBeh]
      refine (ret_mem_ssaBeh).trans ?_
      show LambdaSSA.Semantics.Region.Eval M.instr (envOfBound M.bound) (compileSingle t) s label
        out s' ↔ _
      rw [Morphism.SSAIter.compileSingle_eval_iff (free := noFree) (envOfBound_agrees M.bound)]
      constructor
      · rintro ⟨rfl, run⟩
        exact ⟨out, rfl, run⟩
      · rintro ⟨value, hv, run⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
        exact ⟨rfl, run⟩
  | fault s s' =>
      rw [Observation.fault_mem_image_iff, fault_mem_iterBeh]
      exact Morphism.SSAIter.compileSingle_fault_iff (envOfBound_agrees M.bound)
  | diverge s =>
      rw [Observation.diverge_mem_image_iff, diverge_mem_iterBeh]
      exact Morphism.SSAIter.compileSingle_diverges_iff (envOfBound_agrees M.bound)

/-- The CPS compiler `IterSSA.compile` (single-exit form) as a translation of behavioural
semantics. -/
def iterSSA (Φ : Type u) :
    Behaviour.Translation (letIter.{u, v, w} Φ) (lambdaSSA.{u, v, w} Φ 1) where
  prog t := ⟨compileSingle t, compileSingle_scoped t⟩
  out value := ((0 : Nat), value)
  dom := Set.univ
  injOn := @pair0_injOn
  beh_sub := fun _ _ o _ => by cases o <;> trivial
  beh_prog := fun M t => ssaBeh_compileSingle M t

/-! ## Lambda-SSA into let-iter -/

/-- Exit-tag a labelled result as `SSAIter.encodeRegion` does; out-of-range labels (which no
scoped region produces) go to `unit`. -/
def tagOut (labels : Nat) {α : Type v} (x : Nat × Value α) : Value α :=
  if h : x.1 < labels then Morphism.SSAIter.tagValue ⟨x.1, h⟩ x.2 else .unit

theorem tagOut_of_lt {labels : Nat} {α : Type v} {x : Nat × Value α} (h : x.1 < labels) :
    tagOut labels x = Morphism.SSAIter.tagValue ⟨x.1, h⟩ x.2 := by
  unfold tagOut
  split
  · rfl
  · exact absurd h ‹_›

theorem tagOut_injOn (labels : Nat) {α : Type v} :
    Set.InjOn (tagOut labels (α := α)) {x | x.1 < labels} := by
  intro x hx y hy heq
  rw [tagOut_of_lt hx, tagOut_of_lt hy] at heq
  obtain ⟨hi, hv⟩ := (Morphism.SSAIter.tagValue_eq_iff _ _ _ _).mp heq
  exact Prod.ext (congrArg Fin.val hi) hv

/-- Encoding a scoped region tags each exit with its label and keeps faults and divergences.
Proved from `Morphism.SSAIter.encodeRegion_eval_iff`, `encodeRegion_fault_iff` and
`External.encodeRegion_diverges_iff`. -/
theorem iterBeh_encodeRegion {labels n : Nat} (M : Model.{u, v, w} Φ n)
    (r : ScopedRegion Φ labels n) :
    iterBeh M (Morphism.SSAIter.encodeRegion r.val r.property) =
      Observation.mapValue (tagOut labels) '' ssaBeh labels M r := by
  ext o
  cases o with
  | ret s y s' =>
      simp only [Observation.ret_mem_image_iff, ret_mem_ssaBeh, ret_mem_iterBeh]
      rw [Morphism.SSAIter.encodeRegion_eval_iff r.property (envOfBound_agrees M.bound)]
      constructor
      · rintro ⟨i, value, run, rfl⟩
        exact ⟨(i.val, value), tagOut_of_lt (x := (i.val, value)) i.isLt, run⟩
      · rintro ⟨x, rfl, run⟩
        have hx : x.1 < labels := r.property.eval_label_lt run
        exact ⟨⟨x.1, hx⟩, x.2, run, tagOut_of_lt hx⟩
  | fault s s' =>
      rw [Observation.fault_mem_image_iff, fault_mem_ssaBeh, fault_mem_iterBeh]
      exact Morphism.SSAIter.encodeRegion_fault_iff r.property (envOfBound_agrees M.bound)
  | diverge s =>
      rw [Observation.diverge_mem_image_iff, diverge_mem_ssaBeh, diverge_mem_iterBeh]
      exact Morphism.SSAIter.External.encodeRegion_diverges_iff r.property
        (envOfBound_agrees M.bound)

/-- The exit labels a scoped region produces are in range. From
`LambdaSSA.Region.Scoped.eval_label_lt`. -/
theorem ssaBeh_sub {labels n : Nat} (M : Model.{u, v, w} Φ n) (r : ScopedRegion Φ labels n) :
    ssaBeh labels M r ⊆ {o | o.ValuesIn {x : Nat × Value M.α | x.1 < labels}} := by
  intro o ho
  cases o with
  | ret s x s' => exact r.property.eval_label_lt ((ret_mem_ssaBeh).mp ho)
  | fault _ _ => trivial
  | diverge _ => trivial

/-- The region encoding `SSAIter.encodeRegion` as a translation of behavioural semantics, at
any number of exits. -/
def ssaIter (Φ : Type u) (labels : Nat) :
    Behaviour.Translation (lambdaSSA.{u, v, w} Φ labels) (letIter.{u, v, w} Φ) where
  prog r := Morphism.SSAIter.encodeRegion r.val r.property
  out := tagOut labels
  dom := {x | x.1 < labels}
  injOn := @tagOut_injOn labels
  beh_sub := ssaBeh_sub
  beh_prog := iterBeh_encodeRegion

/-- The untagged single-exit encoding has exactly the results of the region at label `0`.
Proved from `Morphism.SSAIter.encodeSingle_eval_iff`, `encodeSingle_fault_iff` and
`encodeSingle_diverges_iff`. -/
theorem iterBeh_encodeSingle {n : Nat} (M : Model.{u, v, w} Φ n) (r : ScopedRegion Φ 1 n) :
    iterBeh M (encodeSingle r.val r.property) =
      Observation.mapValue Prod.snd '' ssaBeh 1 M r := by
  ext o
  cases o with
  | ret s y s' =>
      simp only [Observation.ret_mem_image_iff, ret_mem_ssaBeh, ret_mem_iterBeh]
      rw [Morphism.SSAIter.encodeSingle_eval_iff r.property (envOfBound_agrees M.bound)]
      constructor
      · intro run
        exact ⟨(0, y), rfl, run⟩
      · rintro ⟨x, rfl, run⟩
        have h0 : x.1 = 0 := Nat.lt_one_iff.mp (r.property.eval_label_lt run)
        rw [h0] at run
        exact run
  | fault s s' =>
      rw [Observation.fault_mem_image_iff, fault_mem_ssaBeh, fault_mem_iterBeh]
      exact Morphism.SSAIter.encodeSingle_fault_iff r.property (envOfBound_agrees M.bound)
  | diverge s =>
      rw [Observation.diverge_mem_image_iff, diverge_mem_ssaBeh, diverge_mem_iterBeh]
      exact Morphism.SSAIter.encodeSingle_diverges_iff r.property (envOfBound_agrees M.bound)

theorem snd_injOn {α : Type v} : Set.InjOn (Prod.snd : Nat × Value α → Value α) {x | x.1 = 0} :=
  fun x hx y hy h => Prod.ext ((show x.1 = 0 from hx).trans (show y.1 = 0 from hy).symm) h

/-- A single-exit region only exits at label `0`. -/
theorem ssaBeh_single_sub {n : Nat} (M : Model.{u, v, w} Φ n) (r : ScopedRegion Φ 1 n) :
    ssaBeh 1 M r ⊆ {o | o.ValuesIn {x : Nat × Value M.α | x.1 = 0}} := by
  intro o ho
  cases o with
  | ret s x s' => exact Nat.lt_one_iff.mp (r.property.eval_label_lt ((ret_mem_ssaBeh).mp ho))
  | fault _ _ => trivial
  | diverge _ => trivial

/-- The untagged single-exit encoding `SSAIter.encodeSingle` as a translation of behavioural
semantics. -/
def ssaIterSingle (Φ : Type u) :
    Behaviour.Translation (lambdaSSA.{u, v, w} Φ 1) (letIter.{u, v, w} Φ) where
  prog r := encodeSingle r.val r.property
  out := Prod.snd
  dom := {x | x.1 = 0}
  injOn := @snd_injOn
  beh_sub := ssaBeh_single_sub
  beh_prog := iterBeh_encodeSingle

/-! ## The comorphisms -/

/-- `CaseIter` as a comorphism of observational institutions. -/
def caseIterCoHom (Φ : Type u) :
    Inst.CoHom (letCase.{u, v, w} Φ).inst (letIter.{u, v, w} Φ).inst :=
  (caseIter Φ).coHom

/-- `IterSSA` as a comorphism of observational institutions. -/
def iterSSACoHom (Φ : Type u) :
    Inst.CoHom (letIter.{u, v, w} Φ).inst (lambdaSSA.{u, v, w} Φ 1).inst :=
  (iterSSA Φ).coHom

/-- `SSAIter` as a comorphism of observational institutions, at any number of exits. -/
def ssaIterCoHom (Φ : Type u) (labels : Nat) :
    Inst.CoHom (lambdaSSA.{u, v, w} Φ labels).inst (letIter.{u, v, w} Φ).inst :=
  (ssaIter Φ labels).coHom

/-- The composite compilation let-case → let-iter → lambda-SSA, composed in `CoIns`. -/
def caseSSACoHom (Φ : Type u) :
    Inst.CoHom (letCase.{u, v, w} Φ).inst (lambdaSSA.{u, v, w} Φ 1).inst :=
  (caseIterCoHom Φ).comp (iterSSACoHom Φ)

/-! ## Consequences: transfer of observational equivalence and refinement -/

/-- Let-case observational equivalence is let-iter observational equivalence of the embedded
terms, via the comorphism and the bridge `iter_obs_iff`. -/
theorem letCase_obsEq_iff_obs {n : Nat} (a b : LetCase.LocallyNameless.Tm Empty Φ n) :
    (letCase.{u, v, w} Φ).ObsEq a b ↔
      LetIter.LocallyNameless.Tm.Obs.{u, v, w, 0} (Morphism.CaseIter.embed a)
        (Morphism.CaseIter.embed b) :=
  ((caseIter Φ).obsEq_iff a b).symm.trans (iter_obs_iff _ _).symm

/-- Every equation of `LetIter.LocallyNameless.ObsTheory` between embedded let-case terms
transfers to an observational equation of let-case. -/
theorem letCase_obsEq_of_obsTheory {n : Nat} {a b : LetCase.LocallyNameless.Tm Empty Φ n}
    (h : LetIter.LocallyNameless.ObsTheory (Morphism.CaseIter.embed a)
      (Morphism.CaseIter.embed b)) : (letCase.{u, v, w} Φ).ObsEq a b :=
  ((caseIter Φ).obsEq_iff a b).mp (iter_obsEq_of_obsTheory h)

/-- Compilation preserves and reflects observational equivalence; this is the satisfaction
condition of `iterSSACoHom` at equations. -/
theorem iterSSA_obsEq_iff {n : Nat} (t t' : LetIter.LocallyNameless.Tm Empty Φ n) :
    (lambdaSSA.{u, v, w} Φ 1).ObsEq ⟨compileSingle t, compileSingle_scoped t⟩
        ⟨compileSingle t', compileSingle_scoped t'⟩ ↔ (letIter.{u, v, w} Φ).ObsEq t t' :=
  (iterSSA Φ).obsEq_iff t t'

/-- The same statement, restated from the existing Isotope result
`Morphism.SSAIter.compileSingle_obs_iff` through the two bridges. -/
theorem iterSSA_obsEq_iff_of_compileSingle_obs_iff {n : Nat}
    (t t' : LetIter.LocallyNameless.Tm Empty Φ n) :
    (lambdaSSA.{u, v, w} Φ 1).ObsEq ⟨compileSingle t, compileSingle_scoped t⟩
        ⟨compileSingle t', compileSingle_scoped t'⟩ ↔ (letIter.{u, v, w} Φ).ObsEq t t' :=
  (ssa_obs_iff _ _).symm.trans
    ((Morphism.SSAIter.compileSingle_obs_iff t t').trans (iter_obs_iff t t'))

/-- Encoding preserves and reflects observational equivalence, at any number of exits; this is
the satisfaction condition of `ssaIterCoHom` at equations. -/
theorem ssaIter_obsEq_iff {labels n : Nat} (r r' : ScopedRegion Φ labels n) :
    (letIter.{u, v, w} Φ).ObsEq (Morphism.SSAIter.encodeRegion r.val r.property)
        (Morphism.SSAIter.encodeRegion r'.val r'.property) ↔
      (lambdaSSA.{u, v, w} Φ labels).ObsEq r r' :=
  (ssaIter Φ labels).obsEq_iff r r'

/-- The same statement, restated from the existing Isotope result
`Morphism.SSAIter.encodeRegion_obs_iff` through the two bridges. -/
theorem ssaIter_obsEq_iff_of_encodeRegion_obs_iff {labels n : Nat}
    (r r' : ScopedRegion Φ labels n) :
    (letIter.{u, v, w} Φ).ObsEq (Morphism.SSAIter.encodeRegion r.val r.property)
        (Morphism.SSAIter.encodeRegion r'.val r'.property) ↔
      (lambdaSSA.{u, v, w} Φ labels).ObsEq r r' :=
  (iter_obs_iff _ _).symm.trans
    ((Morphism.SSAIter.encodeRegion_obs_iff r.property r'.property).trans (ssa_obs_iff r r'))

/-- Encoding preserves and reflects observational refinement of regions: refinement of
lambda-SSA regions can be checked on their let-iter encodings. -/
theorem ssaIter_obsLe_iff {labels n : Nat} (r r' : ScopedRegion Φ labels n) :
    (letIter.{u, v, w} Φ).ObsLe (Morphism.SSAIter.encodeRegion r.val r.property)
        (Morphism.SSAIter.encodeRegion r'.val r'.property) ↔
      (lambdaSSA.{u, v, w} Φ labels).ObsLe r r' :=
  (ssaIter Φ labels).obsLe_iff r r'

/-- Every `ObsTheory` equation between encodings of single-exit regions transfers to an
observational equation of lambda-SSA regions. -/
theorem lambdaSSA_obsEq_of_obsTheory {n : Nat} {r r' : ScopedRegion Φ 1 n}
    (h : LetIter.LocallyNameless.ObsTheory (encodeSingle r.val r.property)
      (encodeSingle r'.val r'.property)) : (lambdaSSA.{u, v, w} Φ 1).ObsEq r r' :=
  ((ssaIterSingle Φ).obsEq_iff r r').mp (iter_obsEq_of_obsTheory h)

/-- **Retraction at any number of exits**, as a valid observational equation: decoding the
encoding of a scoped region gives back the region. Restated from
`Morphism.SSAIter.roundTrip_region`. -/
theorem lambdaSSA_obsEq_decode_encode {labels n : Nat} (r : ScopedRegion Φ labels n) :
    (lambdaSSA.{u, v, w} Φ labels).ObsEq
      ⟨Morphism.SSAIter.decode labels (Morphism.SSAIter.encodeRegion r.val r.property),
        Morphism.SSAIter.decode_scoped labels _⟩ r :=
  (ssa_obs_iff _ r).mp (Morphism.SSAIter.roundTrip_region r.val r.property)

/-- Borrowing along `CaseIter`: observational consequence in let-case, under arbitrary
hypotheses (equations and refinements), is observational consequence of the embedded sentences
in let-iter. -/
theorem letCase_entails_iff {n : Nat}
    (Γ : Set (Sentence (LetCase.LocallyNameless.Tm Empty Φ n)))
    (φ : Sentence (LetCase.LocallyNameless.Tm Empty Φ n)) :
    ((letCase.{u, v, w} Φ).room n).Entails Γ φ ↔
      ((letIter.{u, v, w} Φ).room n).Entails (Sentence.map Morphism.CaseIter.embed '' Γ)
        (φ.map Morphism.CaseIter.embed) :=
  (caseIter Φ).entails_iff n Γ φ

/-- Borrowing along `SSAIter`: observational consequence in lambda-SSA is observational
consequence of the encoded sentences in let-iter. -/
theorem lambdaSSA_entails_iff {labels n : Nat} (Γ : Set (Sentence (ScopedRegion Φ labels n)))
    (φ : Sentence (ScopedRegion Φ labels n)) :
    ((lambdaSSA.{u, v, w} Φ labels).room n).Entails Γ φ ↔
      ((letIter.{u, v, w} Φ).room n).Entails (Sentence.map (ssaIter Φ labels).prog '' Γ)
        (φ.map (ssaIter Φ labels).prog) :=
  (ssaIter Φ labels).entails_iff n Γ φ

/-- Borrowing along `IterSSA`: observational consequence in let-iter is observational
consequence of the compiled sentences in lambda-SSA. -/
theorem letIter_entails_iff {n : Nat}
    (Γ : Set (Sentence (LetIter.LocallyNameless.Tm Empty Φ n)))
    (φ : Sentence (LetIter.LocallyNameless.Tm Empty Φ n)) :
    ((letIter.{u, v, w} Φ).room n).Entails Γ φ ↔
      ((lambdaSSA.{u, v, w} Φ 1).room n).Entails (Sentence.map (iterSSA Φ).prog '' Γ)
        (φ.map (iterSSA Φ).prog) :=
  (iterSSA Φ).entails_iff n Γ φ

end Silmaril.Isotope.Institution.Observational
