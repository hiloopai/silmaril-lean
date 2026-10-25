module

public import Silmaril.Logic.Metamath.Peano.SetLang
public import Silmaril.Logic.SetTheory.ZFSetModel

@[expose] public section

/-!
# set.mm's ZFC as tree axioms, and its `ZFSet` model

The axioms of set.mm's ZFC, transcribed as
tree assertions over `Peano.ZF.grammar` with set.mm's mandatory hypotheses in
database order and its disjoint-variable conditions:

* predicate calculus: `ax-mp`, `ax-1` to `ax-3`, `ax-gen`, `ax-4` to `ax-13`;
* the definitions `df-bi`, `df-an`, `df-or`, `df-ex` of the defined
  connectives, which set.mm's ZFC axioms use;
* set theory: `ax-ext`, `ax-rep`, `ax-sep`, `ax-nul`, `ax-pow`, `ax-pr`,
  `ax-un`, `ax-reg`, `ax-inf`, `ax-ac`.

`ZFC` is the set of these 29 axioms (`Peano.ZF.axiomList` lists them with
their labels), and `ZF0` is ZF, the same without `ax-ac`.
They are well formed, and the environment model over Mathlib's `ZFSet` is a
model of them (`Peano.ZF.isModel_ZFC`): the predicate calculus holds over any
extensional membership structure, and the set-theoretic axioms hold in
`ZFSet` by `Silmaril.Logic.SetTheory.ZFSetModel`. Hence ZFC is consistent
(`Peano.ZF.tConsistent_ZFC`).
-/

namespace Silmaril.Logic.Metamath.Peano.ZF

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion Silmaril.Logic.SetTheory Function Env
open Silmaril.Logic.Metamath.Model.SetMM (opNot opImp opIff opAnd opOr opAll opEx opCv opEq opEl
  termEq termMem opEq_cv opEl_cv Extensional)
open T

/-- A floating hypothesis `wff v`. -/
abbrev fw (a : V) : THyp L C V := .float .wff a
/-- A floating hypothesis `setvar v`. -/
abbrev fs (a : V) : THyp L C V := .float .setvar a

/-- The pairs of distinct members of a list, as set.mm expands `$d x y z`. -/
def dvs : List V → List (V × V)
  | [] => []
  | a :: as => as.map (a, ·) ++ dvs as

open V

/-! ## Predicate calculus -/

/-- `ax-mp`. -/
def axMp : TAssertion L C V :=
  ⟨[], [fw ph, fw ps, .ess (pf (mv ph)), .ess (pf (wi (mv ph) (mv ps)))], pf (mv ps)⟩
/-- `ax-1`. -/
def ax1 : TAssertion L C V := ⟨[], [fw ph, fw ps], pf (wi (mv ph) (wi (mv ps) (mv ph)))⟩
/-- `ax-2`. -/
def ax2 : TAssertion L C V := ⟨[], [fw ph, fw ps, fw ch],
  pf (wi (wi (mv ph) (wi (mv ps) (mv ch))) (wi (wi (mv ph) (mv ps)) (wi (mv ph) (mv ch))))⟩
/-- `ax-3`. -/
def ax3 : TAssertion L C V := ⟨[], [fw ph, fw ps],
  pf (wi (wi (wn (mv ph)) (wn (mv ps))) (wi (mv ps) (mv ph)))⟩
/-- `df-bi`. -/
def dfBi : TAssertion L C V := ⟨[], [fw ph, fw ps],
  pf (wn (wi (wi (wb (mv ph) (mv ps)) (wn (wi (wi (mv ph) (mv ps)) (wn (wi (mv ps) (mv ph))))))
    (wn (wi (wn (wi (wi (mv ph) (mv ps)) (wn (wi (mv ps) (mv ph))))) (wb (mv ph) (mv ps))))))⟩
/-- `df-an`. -/
def dfAn : TAssertion L C V := ⟨[], [fw ph, fw ps],
  pf (wb (wa (mv ph) (mv ps)) (wn (wi (mv ph) (wn (mv ps)))))⟩
/-- `df-or`. -/
def dfOr : TAssertion L C V := ⟨[], [fw ph, fw ps],
  pf (wb (wo (mv ph) (mv ps)) (wi (wn (mv ph)) (mv ps)))⟩
/-- `df-ex`. -/
def dfEx : TAssertion L C V := ⟨[], [fw ph, fs x],
  pf (wb (wex x (mv ph)) (wn (wal x (wn (mv ph)))))⟩
/-- `ax-gen`. -/
def axGen : TAssertion L C V := ⟨[], [fw ph, fs x, .ess (pf (mv ph))], pf (wal x (mv ph))⟩
/-- `ax-4`. -/
def ax4 : TAssertion L C V := ⟨[], [fw ph, fw ps, fs x],
  pf (wi (wal x (wi (mv ph) (mv ps))) (wi (wal x (mv ph)) (wal x (mv ps))))⟩
/-- `ax-5`, with `$d x ph`. -/
def ax5 : TAssertion L C V := ⟨[(x, ph)], [fw ph, fs x], pf (wi (mv ph) (wal x (mv ph)))⟩
/-- `ax-6`. -/
def ax6 : TAssertion L C V := ⟨[], [fs x, fs y], pf (wn (wal x (wn (weq x y))))⟩
/-- `ax-7`. -/
def ax7 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (weq x y) (wi (weq x z) (weq y z)))⟩
/-- `ax-8`. -/
def ax8 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (weq x y) (wi (wel x z) (wel y z)))⟩
/-- `ax-9`. -/
def ax9 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (weq x y) (wi (wel z x) (wel z y)))⟩
/-- `ax-10`. -/
def ax10 : TAssertion L C V := ⟨[], [fw ph, fs x],
  pf (wi (wn (wal x (mv ph))) (wal x (wn (wal x (mv ph)))))⟩
/-- `ax-11`. -/
def ax11 : TAssertion L C V := ⟨[], [fw ph, fs x, fs y],
  pf (wi (wal x (wal y (mv ph))) (wal y (wal x (mv ph))))⟩
/-- `ax-12`. -/
def ax12 : TAssertion L C V := ⟨[], [fw ph, fs x, fs y],
  pf (wi (weq x y) (wi (wal y (mv ph)) (wal x (wi (weq x y) (mv ph)))))⟩
/-- `ax-13`. -/
def ax13 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (wn (weq x y)) (wi (weq y z) (wal x (weq y z))))⟩

/-! ## Set theory -/

/-- `ax-ext`, with `$d x y z`. -/
def axExt : TAssertion L C V := ⟨dvs [x, y, z], [fs x, fs y, fs z],
  pf (wi (wal z (wb (wel z x) (wel z y))) (weq x y))⟩
/-- `ax-rep`, with `$d x y z w`. -/
def axRep : TAssertion L C V := ⟨dvs [x, y, z, w], [fw ph, fs x, fs y, fs z, fs w],
  pf (wi (wal w (wex y (wal z (wi (wal y (mv ph)) (weq z y)))))
    (wex y (wal z (wb (wel z y) (wex w (wa (wel w x) (wal y (mv ph))))))))⟩
/-- `ax-sep`, with `$d x y z` and `$d y z ph`. -/
def axSep : TAssertion L C V := ⟨dvs [x, y, z] ++ dvs [y, z, ph], [fw ph, fs x, fs y, fs z],
  pf (wex y (wal x (wb (wel x y) (wa (wel x z) (mv ph)))))⟩
/-- `ax-nul`, with `$d x y`. -/
def axNul : TAssertion L C V := ⟨dvs [x, y], [fs x, fs y], pf (wex x (wal y (wn (wel y x))))⟩
/-- `ax-pow`, with `$d x y z w`. -/
def axPow : TAssertion L C V := ⟨dvs [x, y, z, w], [fs x, fs y, fs z, fs w],
  pf (wex y (wal z (wi (wal w (wi (wel w z) (wel w x))) (wel z y))))⟩
/-- `ax-pr`, with `$d x z w` and `$d y z w`. -/
def axPr : TAssertion L C V := ⟨dvs [x, z, w] ++ dvs [y, z, w], [fs x, fs y, fs z, fs w],
  pf (wex z (wal w (wi (wo (weq w x) (weq w y)) (wel w z))))⟩
/-- `ax-un`, with `$d w x y z`. -/
def axUn : TAssertion L C V := ⟨dvs [w, x, y, z], [fs x, fs y, fs z, fs w],
  pf (wex y (wal z (wi (wex w (wa (wel z w) (wel w x))) (wel z y))))⟩
/-- `ax-reg`, with `$d x y z`. -/
def axReg : TAssertion L C V := ⟨dvs [x, y, z], [fs x, fs y, fs z],
  pf (wi (wex y (wel y x)) (wex y (wa (wel y x) (wal z (wi (wel z y) (wn (wel z x)))))))⟩
/-- `ax-inf`, with `$d x y z w`. -/
def axInf : TAssertion L C V := ⟨dvs [x, y, z, w], [fs x, fs y, fs z, fs w],
  pf (wex y (wa (wel x y) (wal z (wi (wel z y) (wex w (wa (wel z w) (wel w y)))))))⟩
/-- `ax-ac`, with `$d x y z w v u t`. -/
def axAc : TAssertion L C V := ⟨dvs [x, y, z, w, v, u, t],
  [fs x, fs y, fs z, fs w, fs v, fs u, fs t],
  pf (wex y (wal z (wal w (wi (wa (wel z w) (wel w x))
    (wex v (wal u (wb (wex t (wa (wa (wel u w) (wel w t)) (wa (wel u t) (wel t y))))
      (weq u v))))))))⟩

/-- The axioms of set.mm's ZFC with their labels. -/
def axiomList : List (String × TAssertion L C V) :=
  [("ax-mp", axMp), ("ax-1", ax1), ("ax-2", ax2), ("ax-3", ax3), ("df-bi", dfBi),
    ("df-an", dfAn), ("df-or", dfOr), ("df-ex", dfEx), ("ax-gen", axGen), ("ax-4", ax4),
    ("ax-5", ax5), ("ax-6", ax6), ("ax-7", ax7), ("ax-8", ax8), ("ax-9", ax9), ("ax-10", ax10),
    ("ax-11", ax11), ("ax-12", ax12), ("ax-13", ax13), ("ax-ext", axExt), ("ax-rep", axRep),
    ("ax-sep", axSep), ("ax-nul", axNul), ("ax-pow", axPow), ("ax-pr", axPr), ("ax-un", axUn),
    ("ax-reg", axReg), ("ax-inf", axInf), ("ax-ac", axAc)]

/-- set.mm's ZFC. -/
def ZFC : Set (TAssertion L C V) := {A | ∃ p ∈ axiomList, p.2 = A}

/-- set.mm's ZF: ZFC without the axiom of choice `ax-ac`. -/
def ZF0 : Set (TAssertion L C V) := {A | ∃ p ∈ axiomList, p.1 ≠ "ax-ac" ∧ p.2 = A}

theorem ZF0_subset_ZFC : ZF0 ⊆ ZFC := fun _ ⟨p, hp, _, he⟩ => ⟨p, hp, he⟩

theorem mem_ZFC {A : TAssertion L C V} : A ∈ ZFC ↔ A ∈ axiomList.map Prod.snd := by
  simp [ZFC, eq_comm]

theorem wellFormed_ZFC : ∀ B ∈ ZFC, B.WellFormed grammar := by
  intro B hB
  rw [mem_ZFC] at hB
  have h : ∀ B ∈ axiomList.map Prod.snd, TAssertion.checkWF grammar B = true := by decide
  exact .of_checkWF (h B hB)

theorem wf {A : TAssertion L C V} (h : A ∈ axiomList.map Prod.snd) : A.WellFormed grammar :=
  wellFormed_ZFC A (mem_ZFC.2 h)

/-! ## The axioms hold in the environment model -/

/-- Compute values in the environment model. -/
macro "zf_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [value_wn, value_wi, value_wb, value_wa, value_wo, value_wal, value_wex,
    value_cv, value_wceq, value_wcel, Model.value_var, Valid] $[$loc]?)

section DV

variable {D : Type 1} [Membership D D] {N : Type 1} [DecidableEq N] [Infinite N]
  {A : TAssertion L C V} {ρ : (model D N).Valuation A.ctx}
  (hdv : (model D N).DVHolds ρ A.dv) {a b : V}

include hdv

theorem ne_of_dv (hab : (a, b) ∈ A.dv) (hne : a ≠ b) (ha : grammar.synCtx A.ctx a .setvar)
    (hb : grammar.synCtx A.ctx b .setvar) : (ρ a .setvar ha : N) ≠ ρ b .setvar hb :=
  Kind.fresh_name_name.1 (hdv a b hab hne _ _ ha hb)

theorem notFree_of_dv (hab : (a, b) ∈ A.dv) (hne : a ≠ b) (ha : grammar.synCtx A.ctx a .setvar)
    (hb : grammar.synCtx A.ctx b .wff) :
    NotFree (ρ a .setvar ha : N) (ρ b .wff hb : Term D N Prop).1 :=
  Kind.fresh_name_formula.1 (hdv a b hab hne _ _ ha hb)

end DV

section PredCalc

open PredicateCalculus

variable {D : Type 1} [Membership D D] {N : Type 1} [DecidableEq N] [Infinite N]

theorem sat_axMp : (model D N).Satisfies axMp :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ hess ht => by
    obtain ⟨_, v₁⟩ := (holds_iff ρ _).1 (hess (pf (mv ph)) (by simp [axMp, essentials]))
    obtain ⟨_, v₂⟩ := (holds_iff ρ _).1 (hess (pf (wi (mv ph) (mv ps)))
      (by simp [axMp, essentials]))
    simp only [value_wi, Model.value_var] at v₁ v₂ ⊢
    exact valid_mp v₁ v₂

theorem sat_ax1 : (model D N).Satisfies ax1 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, Model.value_var]; exact valid_ax1 _ _

theorem sat_ax2 : (model D N).Satisfies ax2 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, Model.value_var]; exact valid_ax2 _ _ _

theorem sat_ax3 : (model D N).Satisfies ax3 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wn, Model.value_var]; exact valid_ax3 _ _

theorem sat_dfBi : (model D N).Satisfies dfBi :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht E => by
    zf_simp; simp only [Term.map, Term.map₂]; tauto

theorem sat_dfAn : (model D N).Satisfies dfAn :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht E => by
    zf_simp; simp only [Term.map, Term.map₂]; tauto

theorem sat_dfOr : (model D N).Satisfies dfOr :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht E => by
    zf_simp; simp only [Term.map, Term.map₂]; tauto

theorem sat_dfEx : (model D N).Satisfies dfEx :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wb, value_wex, value_wn, value_wal, Model.value_var]
    exact valid_dfEx _ _

theorem sat_axGen : (model D N).Satisfies axGen :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ hess ht => by
    obtain ⟨_, v₁⟩ := (holds_iff ρ _).1 (hess (pf (mv ph)) (by simp [axGen, essentials]))
    simp only [value_wal, Model.value_var] at v₁ ⊢
    exact valid_gen _ v₁

theorem sat_ax4 : (model D N).Satisfies ax4 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wal, Model.value_var]; exact valid_ax4 _ _ _

theorem sat_ax5 : (model D N).Satisfies ax5 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    simp only [value_wi, value_wal, Model.value_var]
    exact valid_ax5 (notFree_iff.1 (notFree_of_dv hdv (by simp [ax5]) (by decide) _ _))

variable (hext : Extensional D)
include hext

theorem sat_ax6 : (model D N).Satisfies ax6 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wn, value_wal, value_wceq, value_cv, Model.value_var, opEq_cv hext]
    exact valid_ax6 _ _

theorem sat_ax7 : (model D N).Satisfies ax7 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wceq, value_cv, Model.value_var, opEq_cv hext]
    exact valid_ax7 _ _ _

theorem sat_ax8 : (model D N).Satisfies ax8 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wceq, value_wcel, value_cv, Model.value_var, opEq_cv hext,
      opEl_cv hext]
    exact valid_ax8 _ _ _

theorem sat_ax9 : (model D N).Satisfies ax9 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wceq, value_wcel, value_cv, Model.value_var, opEq_cv hext,
      opEl_cv hext]
    exact valid_ax9 _ _ _

omit hext in
theorem sat_ax10 : (model D N).Satisfies ax10 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wn, value_wal, Model.value_var]; exact valid_ax10 _ _

omit hext in
theorem sat_ax11 : (model D N).Satisfies ax11 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wal, Model.value_var]; exact valid_ax11 _ _ _

theorem sat_ax12 : (model D N).Satisfies ax12 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wal, value_wceq, value_cv, Model.value_var, opEq_cv hext]
    exact valid_ax12 _ _ _

theorem sat_ax13 : (model D N).Satisfies ax13 :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    simp only [value_wi, value_wn, value_wal, value_wceq, value_cv, Model.value_var,
      opEq_cv hext]
    exact valid_ax13 _ _ _

end PredCalc

theorem mem_dvs_of_ne {l : List V} {a b : V} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (a, b) ∈ dvs l ∨ (b, a) ∈ dvs l := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [dvs, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact .inl (.inl ⟨b, hb', rfl, rfl⟩)
    · exact .inr (.inl ⟨a, ha', rfl, rfl⟩)
    · exact (ih ha' hb').imp .inr .inr

section ZF

variable {N : Type 1} [DecidableEq N] [Infinite N]

/-- `ZFSet` is extensional. -/
theorem extensional_zfset : Extensional ZFSet.{0} := fun _ _ => ZFSet.ext

theorem ne_of_dvs {A : TAssertion L C V} {ρ : (model ZFSet.{0} N).Valuation A.ctx}
    (hdv : (model ZFSet.{0} N).DVHolds ρ A.dv) {l : List V} (hl : ∀ p ∈ dvs l, p ∈ A.dv)
    {a b : V} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) (hca : grammar.synCtx A.ctx a .setvar)
    (hcb : grammar.synCtx A.ctx b .setvar) : (ρ a .setvar hca : N) ≠ ρ b .setvar hcb := by
  rcases mem_dvs_of_ne ha hb hne with h | h
  · exact ne_of_dv hdv (hl _ h) hne hca hcb
  · exact (ne_of_dv hdv (hl _ h) (Ne.symm hne) hcb hca).symm

/-- Compute values of set-theoretic formulas in `ZFSet`. -/
macro "zfset_simp" : tactic =>
  `(tactic| simp only [value_wn, value_wi, value_wb, value_wa, value_wo, value_wal, value_wex,
    value_cv, value_wceq, value_wcel, Model.value_var, opEq_cv extensional_zfset,
    opEl_cv extensional_zfset])

open ZFSetModel

theorem sat_axExt : (model ZFSet.{0} N).Satisfies axExt :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z] → grammar.synCtx axExt.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl <;> simp [axExt, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv (fun p hp => by simpa [axExt] using hp) ha hb
      hne (c a ha) (c b hb)
    zfset_simp
    exact valid_ext (ne x (by simp) z (by simp) (by decide))
      (ne y (by simp) z (by simp) (by decide))

theorem sat_axRep : (model ZFSet.{0} N).Satisfies axRep :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z, w] → grammar.synCtx axRep.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> simp [axRep, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv (fun p hp => by simpa [axRep] using hp) ha hb
      hne (c a ha) (c b hb)
    zfset_simp
    exact valid_rep (ne x (by simp) y (by simp) (by decide))
      (ne x (by simp) z (by simp) (by decide)) (ne x (by simp) w (by simp) (by decide))
      (ne y (by simp) z (by simp) (by decide)) (ne y (by simp) w (by simp) (by decide))
      (ne z (by simp) w (by simp) (by decide)) _

theorem sat_axSep : (model ZFSet.{0} N).Satisfies axSep :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z] → grammar.synCtx axSep.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl <;> simp [axSep, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv
      (fun p hp => by simp [axSep]; exact .inl hp) ha hb hne (c a ha) (c b hb)
    have hph : grammar.synCtx axSep.ctx ph .wff := ⟨by simp [axSep, ctx], rfl⟩
    have hyph := notFree_of_dv hdv (by simp [axSep, dvs]) (by decide) (c y (by simp)) hph
    zfset_simp
    exact valid_sep (ne x (by simp) y (by simp) (by decide))
      (ne x (by simp) z (by simp) (by decide)) (ne y (by simp) z (by simp) (by decide)) _
      (notFree_iff.1 hyph)

theorem sat_axNul : (model ZFSet.{0} N).Satisfies axNul :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ _ _ ht => by
    zfset_simp
    exact valid_nul _ _

theorem sat_axPow : (model ZFSet.{0} N).Satisfies axPow :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z, w] → grammar.synCtx axPow.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> simp [axPow, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv (fun p hp => by simpa [axPow] using hp) ha hb
      hne (c a ha) (c b hb)
    zfset_simp
    exact valid_pow (ne x (by simp) y (by simp) (by decide))
      (ne x (by simp) z (by simp) (by decide)) (ne x (by simp) w (by simp) (by decide))
      (ne y (by simp) z (by simp) (by decide)) (ne y (by simp) w (by simp) (by decide))
      (ne z (by simp) w (by simp) (by decide))

theorem sat_axPr : (model ZFSet.{0} N).Satisfies axPr :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z, w] → grammar.synCtx axPr.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> simp [axPr, ctx], rfl⟩
    have ne₁ := fun a ha b hb hne => ne_of_dvs (l := [x, z, w]) hdv
      (fun p hp => by simp [axPr]; exact .inl hp) ha hb hne (c a (by simp at ha ⊢; tauto))
      (c b (by simp at hb ⊢; tauto))
    have ne₂ := fun a ha b hb hne => ne_of_dvs (l := [y, z, w]) hdv
      (fun p hp => by simp [axPr]; exact .inr hp) ha hb hne (c a (by simp at ha ⊢; tauto))
      (c b (by simp at hb ⊢; tauto))
    zfset_simp
    exact valid_pr (ne₁ x (by simp) z (by simp) (by decide))
      (ne₁ x (by simp) w (by simp) (by decide)) (ne₂ y (by simp) z (by simp) (by decide))
      (ne₂ y (by simp) w (by simp) (by decide)) (ne₁ z (by simp) w (by simp) (by decide))

theorem sat_axUn : (model ZFSet.{0} N).Satisfies axUn :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [w, x, y, z] → grammar.synCtx axUn.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> simp [axUn, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv (fun p hp => by simpa [axUn] using hp) ha hb
      hne (c a ha) (c b hb)
    zfset_simp
    exact valid_un (ne x (by simp) y (by simp) (by decide))
      (ne x (by simp) z (by simp) (by decide)) (ne x (by simp) w (by simp) (by decide))
      (ne y (by simp) z (by simp) (by decide)) (ne y (by simp) w (by simp) (by decide))
      (ne z (by simp) w (by simp) (by decide))

theorem sat_axReg : (model ZFSet.{0} N).Satisfies axReg :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z] → grammar.synCtx axReg.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl <;> simp [axReg, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv (fun p hp => by simpa [axReg] using hp) ha hb
      hne (c a ha) (c b hb)
    zfset_simp
    exact valid_reg (ne x (by simp) y (by simp) (by decide))
      (ne x (by simp) z (by simp) (by decide)) (ne y (by simp) z (by simp) (by decide))

theorem sat_axInf : (model ZFSet.{0} N).Satisfies axInf :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z, w] → grammar.synCtx axInf.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> simp [axInf, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv (fun p hp => by simpa [axInf] using hp) ha hb
      hne (c a ha) (c b hb)
    zfset_simp
    exact valid_inf (ne x (by simp) y (by simp) (by decide))
      (ne y (by simp) z (by simp) (by decide)) (ne y (by simp) w (by simp) (by decide))
      (ne z (by simp) w (by simp) (by decide))

theorem sat_axAc : (model ZFSet.{0} N).Satisfies axAc :=
  satisfies_of_valid (wf (by simp [axiomList])) rfl fun ρ hdv _ ht => by
    have c : ∀ a, a ∈ [x, y, z, w, v, u, t] → grammar.synCtx axAc.ctx a .setvar := fun a ha =>
      ⟨by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [axAc, ctx], rfl⟩
    have ne := fun a ha b hb hne => ne_of_dvs hdv (fun p hp => by simpa [axAc] using hp) ha hb
      hne (c a ha) (c b hb)
    zfset_simp
    exact valid_ac (ne x (by simp) y (by simp) (by decide))
      (ne x (by simp) z (by simp) (by decide)) (ne x (by simp) w (by simp) (by decide))
      (ne y (by simp) z (by simp) (by decide)) (ne y (by simp) w (by simp) (by decide))
      (ne y (by simp) v (by simp) (by decide)) (ne y (by simp) u (by simp) (by decide))
      (ne y (by simp) t (by simp) (by decide)) (ne z (by simp) w (by simp) (by decide))
      (ne z (by simp) v (by simp) (by decide)) (ne z (by simp) u (by simp) (by decide))
      (ne z (by simp) t (by simp) (by decide)) (ne w (by simp) v (by simp) (by decide))
      (ne w (by simp) u (by simp) (by decide)) (ne w (by simp) t (by simp) (by decide))
      (ne v (by simp) u (by simp) (by decide)) (ne v (by simp) t (by simp) (by decide))
      (ne u (by simp) t (by simp) (by decide))

/-- The environment model over `ZFSet` is a model of set.mm's ZFC. -/
theorem isModel_ZFC : (model ZFSet.{0} N).IsModel ZFC := by
  intro B hB
  rw [mem_ZFC] at hB
  simp only [axiomList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hB
  have e := extensional_zfset
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [sat_axMp, sat_ax1, sat_ax2, sat_ax3, sat_dfBi, sat_dfAn, sat_dfOr, sat_dfEx, sat_axGen,
    sat_ax4, sat_ax5, sat_ax6 e, sat_ax7 e, sat_ax8 e, sat_ax9 e, sat_ax10, sat_ax11, sat_ax12 e,
    sat_ax13 e, sat_axExt, sat_axRep, sat_axSep, sat_axNul, sat_axPow, sat_axPr, sat_axUn,
    sat_axReg, sat_axInf, sat_axAc]

/-- The model over `ZFSet` is not trivial: the constantly false formula is not valid. -/
theorem not_trivialAt : ¬ (model ZFSet.{0} N).TrivialAt (c := .turnstile) (s := .wff) rfl :=
  fun h => h (Term.const False) fun _ => ∅

/-- set.mm's ZFC is consistent: it does not prove `|- ph`. -/
theorem tConsistent_ZFC : TConsistent grammar ZFC .turnstile :=
  Model.tConsistent (M := model ZFSet.{0} (ULift.{1} ℕ)) wellFormed_ZFC isModel_ZFC rfl
    not_trivialAt ph

/-- The string system of set.mm's ZFC is consistent. -/
theorem nonUniversal_ZFC : (system (grammar.axioms ZFC)).NonUniversal :=
  Model.nonUniversal_system (M := model ZFSet.{0} (ULift.{1} ℕ)) unambiguous wellFormed_ZFC
    isModel_ZFC rfl not_trivialAt ph

end ZF

end Silmaril.Logic.Metamath.Peano.ZF
