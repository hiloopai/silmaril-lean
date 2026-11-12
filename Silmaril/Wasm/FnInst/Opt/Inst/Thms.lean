module

public import Silmaril.Wasm.FnInst.Opt.Inst.Defs
import Silmaril.Proofs.Wasm.FnInst.Opt.Inst.Basic

@[expose] public section

/-! # The segment institution: theorems

The results of the segment institution (proofs in `Silmaril.Proofs.Wasm.FnInst.Opt.Inst.Basic`):

* **peephole-rewrite theorem**, institution form: `sat_plug_equiv`, `sat_plug_refine`
  (`(τ, s ≈ s') ⊨ (𝟙, plug τ s ≈ plug τ s')`); per environment `runEq_plug`, `runLe_plug`;
  over partial models `holds_plug_equiv`, `holds_plug_refine`;
* **peephole-rewrite theorem**, module form: `peephole_module` (validity at the minimal hole
  and the least informative model gives the same semantics, at every call depth, for every
  rewrite at typed positions of every well-typed module whose function types extend the
  hole's), with `segEquiv_of_holds_top`;
* distinctions reflect along plugging: `distSome_of_plug`, `distEvery_of_plug`;
* monotonicity in information: `holds_mono` (positive formulas), `holds_distSome_anti`;
  `distSome_iff_not_equiv`, `distSome_of_distEvery`;
* refinement: `holds_refine_of_equiv`, `holds_equiv_iff_refine`;
* out-of-sight functions: `run_restrict`, `Env.restrict_completion`.
-/

namespace Silmaril.Wasm.FnInst.Opt

section

open CategoryTheory

theorem step_restrict {ft : FTypes} (E : Env) {i : Instr} {a : ℕ × ℕ}
    (ha : arity ft i = some a) (st : St) :
    step ft (E.restrict ft.length) i st = step ft E i st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.step_restrict E ha st

theorem run_restrict {ft : FTypes} (E : Env) {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') (st : St) :
    run ft (E.restrict ft.length) c st = run ft E c st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_restrict E hc st

theorem Env.restrict_completion {ft : FTypes} {E M : Env} (hE : E.Completion ft M) :
    (E.restrict ft.length).Completion ft (M.restrict ft.length) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Env.restrict_completion hE

/-- The states reached by a context's `pre` code have the hole's operands on top. -/
theorem pre_height {X Y : HSig} (σ : X ⟶ Y) {E : Env} (hE : E.Typed Y.ft) {st st₁ : St}
    (hst : Y.n ≤ st.stack.length) (h₁ : Out.ok st₁ ∈ run Y.ft E σ.pre st) :
    X.n ≤ st₁.stack.length :=
  Silmaril.Proofs.Wasm.FnInst.Opt.pre_height σ hE hst h₁

theorem run_plugC {X Y : HSig} (σ : X ⟶ Y) (E : Env) (c : Code) (st : St) :
    run Y.ft E (plugC σ c) st =
      Out.bind (Out.bind (run Y.ft E σ.pre st) (run Y.ft E c)) (run Y.ft E σ.post) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_plugC σ E c st

theorem runEq_plug {X Y : HSig} (σ : X ⟶ Y) {E : Env} (hE : E.Typed Y.ft) (s s' : Seg X)
    (h : RunEq X.ft X.n E s.1 s'.1) : RunEq Y.ft Y.n E (plug σ s).1 (plug σ s').1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.runEq_plug σ hE s s' h

theorem runLe_plug {X Y : HSig} (σ : X ⟶ Y) {E : Env} (hE : E.Typed Y.ft) (s s' : Seg X)
    (h : RunLe X.ft X.n E s.1 s'.1) : RunLe Y.ft Y.n E (plug σ s).1 (plug σ s').1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.runLe_plug σ hE s s' h

/-- A completion at `Y` restricts to a completion at `X`, with the same runs of `X`'s code. -/
theorem runEq_of_restrict {X : HSig} {E : Env} (s s' : Seg X)
    (h : RunEq X.ft X.n (E.restrict X.ft.length) s.1 s'.1) : RunEq X.ft X.n E s.1 s'.1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.runEq_of_restrict s s' h

theorem runLe_of_restrict {X : HSig} {E : Env} (s s' : Seg X)
    (h : RunLe X.ft X.n (E.restrict X.ft.length) s.1 s'.1) : RunLe X.ft X.n E s.1 s'.1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.runLe_of_restrict s s' h

theorem Env.completion_of_prefix {ft ft' : FTypes} (hp : ft <+: ft') {E M : Env}
    (hE : E.Completion ft' M) : E.Completion ft M :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Env.completion_of_prefix hp hE

theorem holds_plug_equiv {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds X M (.equiv s s')) : holds Y M (.equiv (plug σ s) (plug σ s')) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_plug_equiv σ h

theorem holds_plug_refine {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds X M (.refine s s')) : holds Y M (.refine (plug σ s) (plug σ s')) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_plug_refine σ h

/-- A difference of plugged code in some completion is a difference of the segments there. -/
theorem distSome_of_plug {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds Y M (.distSome (plug σ s) (plug σ s'))) : holds X M (.distSome s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.distSome_of_plug σ h

theorem distEvery_of_plug {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds Y M (.distEvery (plug σ s) (plug σ s'))) (hX : ∀ E : Env, E.Completion X.ft M →
      E.Completion Y.ft M) : holds X M (.distEvery s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.distEvery_of_plug σ h hX

theorem Model.reduct_val {X Y : HSig} (σ : X ⟶ Y) (M : Model Y) :
    (Model.reduct σ M).1 = M.1.restrict X.ft.length :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Model.reduct_val σ M

/-- Equivalence at the reduct gives equivalence over the model itself. -/
theorem holds_equiv_of_reduct {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : holds X (Model.reduct τ M).1 (.equiv s s')) : holds X M.1 (.equiv s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_equiv_of_reduct τ M h

theorem holds_refine_of_reduct {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : holds X (Model.reduct τ M).1 (.refine s s')) : holds X M.1 (.refine s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_refine_of_reduct τ M h

theorem sat_equiv_iff {Y : HSig} (M : Model Y) (s s' : Seg Y) :
    Sat M (Sen.equiv s s') ↔ holds Y M.1 (.equiv s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.sat_equiv_iff M s s'

/-- **The peephole-rewrite theorem** (institution form): a segment equivalence scoped at a
hole `X` placed in `Y` by `τ` entails the equivalence of the plugged code at `Y`. -/
theorem sat_plug_equiv {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : Sat M (Sen.scoped τ (.equiv s s'))) : Sat M (Sen.equiv (plug τ s) (plug τ s')) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.sat_plug_equiv τ M h

/-- The peephole-rewrite theorem for refinement. -/
theorem sat_plug_refine {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : Sat M (Sen.scoped τ (.refine s s'))) :
    Sat M (⟨Y, 𝟙 Y, .refine (plug τ s) (plug τ s')⟩ : Sen Y) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.sat_plug_refine τ M h

/-- **Monotonicity.** Positive formulas (equivalence, refinement, distinction in every
completion, conjunctions of them) valid with less information stay valid with more. -/
theorem holds_mono {X : HSig} {M M' : Env} (hle : M' ≤ M) :
    ∀ {φ : Form X}, φ.Positive → holds X M φ → holds X M' φ :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_mono hle

/-- Distinction in some completion goes the other way: valid with more information, it stays
valid with less. -/
theorem holds_distSome_anti {X : HSig} {M M' : Env} (hle : M ≤ M') {s s' : Seg X}
    (h : holds X M (.distSome s s')) : holds X M' (.distSome s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_distSome_anti hle h

theorem distSome_iff_not_equiv {X : HSig} {M : Env} {s s' : Seg X} :
    holds X M (.distSome s s') ↔ ¬ holds X M (.equiv s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.distSome_iff_not_equiv

/-- Distinction in every completion implies distinction in some completion, when the model
has a completion at all (a model without completions makes every formula of the `∀` kind
hold vacuously). -/
theorem distSome_of_distEvery {X : HSig} {M : Env} {s s' : Seg X}
    (hc : ∃ E : Env, E.Completion X.ft M) (h : holds X M (.distEvery s s')) :
    holds X M (.distSome s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.distSome_of_distEvery hc h

theorem Env.trapAll_completion (ft : FTypes) : Env.trapAll.Completion ft Env.top :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Env.trapAll_completion ft

theorem holds_refine_of_equiv {X : HSig} {M : Env} {s s' : Seg X}
    (h : holds X M (.equiv s s')) : holds X M (.refine s s') :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_refine_of_equiv h

/-- Equivalence is refinement both ways. -/
theorem holds_equiv_iff_refine {X : HSig} {M : Env} {s s' : Seg X} :
    holds X M (.equiv s s') ↔ holds X M (.refine s s') ∧ holds X M (.refine s' s) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.holds_equiv_iff_refine

/-- A rule valid at its minimal hole, over the least informative model, is valid over every
extension of the hole's function types. -/
theorem segEquiv_of_holds_top {X : HSig} {s s' : Seg X} (h : holds X Env.top (.equiv s s'))
    {ft : FTypes} (hp : X.ft <+: ft) : SegEquiv ft X.n Env.top s.1 s'.1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.segEquiv_of_holds_top h hp

/-- **The peephole-rewrite theorem** (module form): a segment pair equivalent at its minimal
hole `X` over the least informative model can be exchanged at typed positions in any bodies of
any well-typed module whose function types extend `X`'s, and every function of the module
keeps its semantics at every call depth. -/
theorem peephole_module {X : HSig} {s s' : Seg X} (h : holds X Env.top (.equiv s s'))
    {M M' : Mdl} (hp : X.ft <+: M.ft) (hM : M.Typed) {imp : Env} (himp : imp.Typed M.ft)
    (himp' : imp.Total) (hR : Mdl.Rewrites s.1 s'.1 X.n X.m M M') :
    ∀ k, fsem M imp k = fsem M' imp k :=
  Silmaril.Proofs.Wasm.FnInst.Opt.peephole_module h hp hM himp himp' hR

end

end Silmaril.Wasm.FnInst.Opt
