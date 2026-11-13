module

public import Silmaril.Wasm.Component.Reference.Litmus.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.Basic
public import Silmaril.Proofs.Wasm.Component.Reference.Litmus
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Litmus components in the reference machine over `core3 neverFail`

The translations `adderS.toRef`, `recordS.toRef` and `optionS.toRef` are accepted by the
reference validator, and calling their exports after instantiation from the empty store
returns the expected results over the concrete Core 3.0 engine `core3 neverFail`. All runs
are closed computations of the copied validator and executable drivers (`decide +kernel` on
Boolean summaries), turned into behaviours by `exportBehaviours_of_run`.

The hypotheses of `RefToSpecAll` are delimited by two closed computations:

* `refToSpec_needs_inst`: without `Simple.Inst`, the statement is false. `oobS` satisfies every
  other hypothesis, but its module does not instantiate (out-of-bounds data segment), so the
  reference machine over `core3P P` traps during instantiation (a run of the copied driver
  `Machine.run` with a stepper that takes no core step: no core code runs), while
  `exportSpec` is empty;
* `toRef_valid_not_general`: the validity hypothesis cannot be dropped: `badNameS` satisfies
  `Good`, `FloatFree` and `Inst`, and the validator rejects its translation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.Reference.Core3Adder (emb first)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine

/-- The validator accepts. -/
def accepts (c : Core3Component) : Bool :=
  match check? Features.p2 c with
  | .ok _ => true
  | .error _ => false

theorem exists_of_accepts {c : Core3Component} (h : accepts c = true) :
    ∃ ct, check? Features.p2 c = .ok ct := by
  unfold accepts at h
  split at h
  next ct hc => exact ⟨ct, hc⟩
  next => cases h

theorem adderS_valid : ∃ ct, check? Features.p2 adderS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)
theorem recordS_valid : ∃ ct, check? Features.p2 recordS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)
theorem optionS_valid : ∃ ct, check? Features.p2 optionS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

/-- Instantiation, then the call of `name` on `vs`, summarised. -/
def callSummary (c : Core3Component) (name : String) (vs : List Value.Val) :
    Option (Machine.Outcome × Option (Option (List Value.Val))) :=
  (emb.instantiateRun first 400 c [] (initConfig ())).bind fun (r, _, es) =>
    (es.lookup name).bind fun f =>
      (emb.callTop first 400 ⟨0⟩ f vs r.config).map fun r' => (r'.outcome, r'.config.result? ⟨0⟩)

/-- A resolved summary is a returned behaviour. -/
theorem returns_of_summary {c : Core3Component} {name : String} {vs rs : List Value.Val}
    (h : callSummary c name vs = some (.resolved, some (some rs))) :
    Outcome.returns (some rs) ∈ exportBehaviours first.prof (Host.ofEmbedder emb) () c [] name vs := by
  unfold callSummary at h
  obtain ⟨⟨r₁, inst, es⟩, hi, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨f, hf, h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨r, hc, h₃⟩ := Option.map_eq_some_iff.mp h₂
  have hr : r.outcome = .resolved ∧ r.config.result? ⟨0⟩ = some (some rs) := by
    simpa only [Prod.mk.injEq] using h₃
  have ho : callOutcome? ⟨0⟩ r = some (.resolved (some rs)) := by
    simp only [callOutcome?, hr.1, hr.2, Option.map_some]
  exact exportBehaviours_of_run emb first () hi hf hc ho

theorem adder_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () adderS.toRef [] "add"
      [toRefVal (.u32 3), toRefVal (.u32 4)] :=
  returns_of_summary (by decide +kernel)

theorem record_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () recordS.toRef [] "sum"
      [toRefVal (.record [.u32 3, .u32 4])] :=
  returns_of_summary (by decide +kernel)

theorem option_some_ref : Outcome.returns (some [toRefVal (.u32 5)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () optionS.toRef [] "get-or-zero"
      [toRefVal (.variant 1 (some (.u32 5)))] :=
  returns_of_summary (by decide +kernel)

theorem option_none_ref : Outcome.returns (some [toRefVal (.u32 0)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () optionS.toRef [] "get-or-zero"
      [toRefVal (.variant 0 none)] :=
  returns_of_summary (by decide +kernel)

theorem twoS_valid : ∃ ct, check? Features.p2 twoS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

theorem two_add_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () twoS.toRef [] "add"
      [toRefVal (.u32 3), toRefVal (.u32 4)] :=
  returns_of_summary (by decide +kernel)

theorem two_sum_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () twoS.toRef [] "sum"
      [toRefVal (.record [.u32 3, .u32 4])] :=
  returns_of_summary (by decide +kernel)

/-! ## The hypotheses of `RefToSpecAll` -/

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The deterministic profile used by the counterexample. -/
abbrev P0 : Silmaril.Wasm.Numerics.Profile :=
  Silmaril.Wasm.SingleThreaded.profile Silmaril.Wasm.SingleThreaded.neverFail

/-- A stepper of `core3P P` that takes no step (sound for every profile). -/
noncomputable def noExec (P : Silmaril.Wasm.Numerics.Profile) : (core3P P).Exec :=
  ⟨fun _ => none, fun h => by cases h⟩

/-- The embedder of `refHost P` with the stepper `noExec P`. -/
noncomputable def noEmb (P : Silmaril.Wasm.Numerics.Profile) : Embedder (core3P P) Unit :=
  { X := noExec P, hr := fun _ _ => false, host := Canon.HostImpl.none }

theorem ofEmbedder_noEmb (P : Silmaril.Wasm.Numerics.Profile) :
    Host.ofEmbedder (noEmb P) = refHost P :=
  rfl

/-- The instantiation of `c` with no arguments from the empty store traps without an
`internal` fault, within `fuel` internal steps of `noEmb P0`. -/
noncomputable def trapSummary (fuel : Nat) (c : Core3Component) : Bool :=
  match hostStep? (noEmb P0).hr (instantiateTop c []) (initConfig ()) with
  | none => false
  | some (_, m₁) =>
    let r := Machine.run (noEmb P0).hr (noEmb P0).dispatch (noEmb P0).X Oracle.first fuel m₁
    decide (r.outcome = .trap) && !(r.labels.any Label.isInternalTrap)

/-- A trapping summary is a trapping instantiation of the reference machine. -/
theorem traps_of_summary {fuel : Nat} {c : Core3Component} (h : trapSummary fuel c = true) :
    InstResult.traps ∈ instBehaviours (Oracle.first (E := core3P P0)).prof (refHost P0)
      (initConfig ()) c [] := by
  unfold trapSummary at h
  split at h
  next => cases h
  next l m₁ e =>
    have ho : (Machine.run (noEmb P0).hr (noEmb P0).dispatch (noEmb P0).X Oracle.first fuel
        m₁).outcome = .trap ∧ (Machine.run (noEmb P0).hr (noEmb P0).dispatch (noEmb P0).X
          Oracle.first fuel m₁).labels.any Label.isInternalTrap = false := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
        using h
    have hl : l = .host (instantiateTop c []) := hostStep?_run_label e
    have s₁ := hostStep?_sound (Oracle.first (E := core3P P0)).prof (noEmb P0).hr (noEmb P0).dispatch e
    have hs := Machine.run_sound (noEmb P0).hr (noEmb P0).dispatch (noEmb P0).X
      Oracle.first fuel m₁
    have hT : Trapped (Machine.run (noEmb P0).hr (noEmb P0).dispatch (noEmb P0).X
        Oracle.first fuel m₁).config := by
      rcases Machine.run_outcome (noEmb P0).hr (noEmb P0).dispatch (noEmb P0).X Oracle.first
        fuel m₁ with e' | e'
      · exact absurd (e'.symm.trans ho.1) (by decide)
      · exact outcomeOf_trap _ (e' ▸ ho.1)
    refine ⟨_, _, hl ▸ Steps.cons s₁ hs, run_noHost _ _ _ _ _ _, fun msg hm => ?_, hT⟩
    have hany : (Machine.run (noEmb P0).hr (noEmb P0).dispatch (noEmb P0).X Oracle.first fuel
        m₁).labels.any Label.isInternalTrap = true :=
      List.any_eq_true.mpr ⟨_, hm, Label.isInternalTrap_trap_internal msg⟩
    exact absurd (hany.symm.trans ho.2) (by decide)

/-- The validation and instantiation of `oobCore3` against its imports, summarised: it
validates, and instantiation fails. -/
def oobSummary : Bool :=
  match validate? oobCore3 with
  | some mt => (instantiateOnce? (importStore (CExternType.funcs mt.imports)) oobCore3
      ((List.range mt.imports.length).map ExternAddr.func)).isNone
  | none => false

theorem oobSummary_eq : oobSummary = true := by decide +kernel

/-- `oobCore3` has no instance. -/
theorem oob_no_inst : ¬ ∃ I, oobS.mod.IsInst I := by
  rintro ⟨I, ⟨mt, hI⟩, -, -⟩
  obtain ⟨f, hf, -⟩ := hI.instantiated
  have hv : validate? oobCore3 = some mt := hI.valid
  have hn : (instantiateOnce? (importStore (CExternType.funcs mt.imports)) oobCore3
      ((List.range mt.imports.length).map ExternAddr.func)).isNone = true := by
    simpa only [oobSummary, hv] using oobSummary_eq
  have hs : (instantiateOnce? (importStore (CExternType.funcs mt.imports)) oobCore3
      ((List.range mt.imports.length).map ExternAddr.func)).isNone = false := by
    simp only [show oobS.mod.mod = oobCore3 from rfl] at hf
    rw [hf]
    rfl
  exact absurd (hn.symm.trans hs) (by decide)

/-- For well-typed arguments the specification of `oobS` has no outcome. -/
theorem oob_spec_empty (P : Silmaril.Wasm.Numerics.Profile)
    (b : Silmaril.Wasm.Component.Reference.Outcome) :
    b ∉ exportSpec P oobS oobS.exports[0] [] := by
  rintro (⟨r, ⟨I, hI, -⟩, -⟩ | ⟨-, I, hI, -⟩)
  · exact oob_no_inst ⟨I, hI⟩
  · exact oob_no_inst ⟨I, hI⟩

theorem oobS_good : oobS.Good :=
  ⟨by decide, by intro x hx; simp only [oobS, List.mem_singleton] at hx; subst hx; exact ⟨"f", rfl⟩⟩

theorem oobS_floatFree : oobS.FloatFree := by
  intro x hx
  simp only [oobS, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

theorem oobS_valid : ∃ ct, check? Features.p2 oobS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

/-- **Without `Simple.Inst` the reference half is false**: `oobS` meets every other hypothesis,
the reference machine traps when instantiating it, and its specification is empty. -/
theorem refToSpec_needs_inst : ¬ ∀ (P : Silmaril.Wasm.Numerics.Profile) (prof : ProfileKind)
    (c : Simple), c.Good → c.FloatFree → (∃ ct, check? Features.p2 c.toRef = .ok ct) →
    ∀ x ∈ c.exports, ∀ vs, Silmaril.Wasm.Component.ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) ⊆
        exportSpec P c x vs := by
  intro h
  have hb : Silmaril.Wasm.Component.Reference.Outcome.traps ∈ exportBehaviours (Oracle.first (E := core3P P0)).prof (refHost P0) ()
      oobS.toRef [] "f" [] :=
    Or.inr (Or.inl ⟨rfl, traps_of_summary (fuel := 200) (by decide +kernel)⟩)
  exact oob_spec_empty P0 _
    (h P0 _ oobS oobS_good oobS_floatFree oobS_valid _ (List.Mem.head _) [] rfl hb)

theorem badNameS_good : badNameS.Good :=
  ⟨by decide, by intro x hx; simp only [badNameS, List.mem_singleton] at hx; subst hx; exact ⟨"f", rfl⟩⟩

theorem badNameS_floatFree : badNameS.FloatFree := by
  intro x hx
  simp only [badNameS, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

/-- The validator rejects `badNameS.toRef`. -/
theorem badNameS_rejected : ¬ ∃ ct, check? Features.p2 badNameS.toRef = .ok ct := by
  rintro ⟨ct, hct⟩
  have ha : accepts badNameS.toRef = false := by decide +kernel
  simp only [accepts, hct] at ha
  cases ha

/-- **Validity of `toRef` is not general**: `badNameS` meets the fragment conditions and is
rejected by the reference validator. -/
theorem toRef_valid_not_general : ¬ ∀ c : Simple, c.Good → c.FloatFree → c.Inst →
    ∃ ct, check? Features.p2 c.toRef = .ok ct :=
  fun h => badNameS_rejected
    (h badNameS badNameS_good badNameS_floatFree (binMod_inst instSummary_add _))

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
