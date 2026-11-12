module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwdW
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateVar
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateGlobal

/-!
# `local.get`, `global.get`, `local.set`, `global.set` backwards, at any `GoodW` configuration

The per-rule `iff`s of tracks F2–F3 (`State.localGet_iff`, `globalGet_iff`, `localSet_iff`,
`globalSet_iff`) hold at a known left-hand side, given V2's lookups are defined. Here:

* the code is read back from a firing (`firesCfg_list20`, after `WholeDecode.fires_list20`);
* the lookups come from `ResOkL`, part of the invariant `GoodW` of `Task.wholeStepBwdW`
  (`local_of_goodW`, `global_of_goodW`), which replaces the inversion of `$local`/`$global`;
* the typing of the state, value and index the `iff`s ask for comes from the rule's quantifiers,
  moved to every scope (`typedV_of_scope`).

This discharges `Step_read` rules 7 and 8 and `Step` rules 4 and 5 of `BwdRestW` (`bwdRead_localGet`,
`bwdRead_globalGet`, `bwdStep_localSet`, `bwdStep_globalSet`), and `BwdRestW2` lists what is left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk Fires TypedV ValsOnly stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB firesB_iff_of_closed)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Reading a configuration left-hand side back -/

/-- **A firing rule `z; es ~> rh`, inverted**: the code evaluates element by element, and the
state variable is bound to the image of the state. -/
theorem firesCfg_list20 {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp}
    {rh : Exp} {prems : List Prem} {c : Config H} {w : Value}
    (h : HasRuleAt (simEnv20 B) x "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires (simEnv20 B) x k (.tuple [configV hn c, w])) :
    ∃ σ, QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) es (adminsToV c.code) := by
  obtain ⟨σ, hq, he, -⟩ := Sim.State.Fires.rule_eq h hf
  have hl := Sim.RefsGC.lhs_of_concl he
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  refine ⟨σ, hq, ?_, Sim.RefsGC.elems_of_list hL⟩
  exact evalExp_varE_iff.1 hZ

/-- A closed type name, from a rule's scope to every scope binding term variables only. -/
theorem typedV_of_scope {σ : List (IL.Id × Value)} {x : IL.Id} {v : Value}
    (h : HasTyp (simEnv20 B) (VarEnv.empty.bindVals σ) (.varT x []) v) :
    TypedV (simEnv20 B) (.varT x []) v :=
  fun _ hρ => Sim.IntNumeric.hasTyp_varT_nil_congr (Pure.valsOnly_bindVals σ) hρ h

/-- The typing of a quantifier bound to a known value. -/
theorem typedV_quant {σ : List (IL.Id × Value)} {qs : List Param} {x t : IL.Id} {v : Value}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs) (hm : Param.expP x (.varT t []) ∈ qs)
    (hx : (VarEnv.empty.bindVals σ).findVal? x = some v) : TypedV (simEnv20 B) (.varT t []) v := by
  obtain ⟨v', hv', ht⟩ := hq x _ hm
  rw [hx] at hv'
  obtain rfl := Option.some.inj hv'
  exact typedV_of_scope ht

/-! ## The lookups, from `ResOkL` -/

/-- A defined local, from `GoodW` at `local.get x`, `local.set x`. -/
theorem local_of_res {s : Store H} {f : Frame} {x : LocalIdx}
    (h : InstrResOk (⟨s, f⟩ : State H) (.localGet x) ∨ InstrResOk (⟨s, f⟩ : State H) (.localSet x)) :
    ∃ v, f.locals[x.toNat]? = some v := by
  have h' : (f.locals[x.toNat]?).isSome := by
    rcases h with h | h <;> simpa [InstrResOk, State.local?, Frame.local?] using h
  exact Option.isSome_iff_exists.1 h'

/-- A defined global, from `GoodW` at `global.get x`, `global.set x`. -/
theorem global_of_res {s : Store H} {f : Frame} {x : GlobalIdx}
    (h : InstrResOk (⟨s, f⟩ : State H) (.globalGet x) ∨
      InstrResOk (⟨s, f⟩ : State H) (.globalSet x)) :
    ∃ a g, f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := by
  have h' : ((⟨s, f⟩ : State H).global? x).isSome := by
    rcases h with h | h <;> simpa [InstrResOk] using h
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h'
  simp only [State.global?, ModuleInst.globalAddr?, Store.globalInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hg
  obtain ⟨a, ha, hg⟩ := hg
  exact ⟨a, g, ha, hg⟩

/-! ## The four rules -/

/-- The index of a one-instruction left-hand side `OP x`, read back. -/
theorem idx_of_caseE {σ : List (IL.Id × Value)} {op : MixopS} {a : Admin} {X : Value}
    (ha : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.caseE op (.varE "x")) (adminToV a))
    (hX : adminToV a = .case op X) : (VarEnv.empty.bindVals σ).findVal? "x" = some X := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 ha
  have e : u = X := (Value.case.inj (hcu.symm.trans hX)).2
  exact e ▸ evalExp_varE_iff.1 hu

/-- The value of a left-hand side `(val : val <: admininstr)`, read back. -/
theorem val_of_subE {σ : List (IL.Id × Value)} {v : Val}
    (ha : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.subE (.varE "val") (.varT "val" []) (.varT "admininstr" [])) (adminToV v.toAdmin)) :
    (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v) := by
  rw [← Pure.adminToV_toAdmin]
  exact evalExp_varE_iff.1 (evalExp_subE_iff.1 ha)

/-- On `Step_read` and `Step`, a rule fires under the backend reading exactly when it fires. -/
theorem firesB_read20_iff {i : Nat} {v : Value} :
    FiresB (simEnv20 B) "Step_read" i v ↔ Fires (simEnv20 B) "Step_read" i v :=
  firesB_iff_of_closed (closed_step20 B) (by simp)

theorem firesB_step20_iff {i : Nat} {v : Value} :
    FiresB (simEnv20 B) "Step" i v ↔ Fires (simEnv20 B) "Step" i v :=
  firesB_iff_of_closed (closed_step20 B) (by simp)

/-- **`Step_read/local.get` backwards**, at a `GoodW` configuration. -/
theorem bwdRead_localGet {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 7 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes⟩ := firesCfg_list20 (State.hasRuleAt_localGet B) hf
  obtain ⟨a, rfl, ha⟩ := codes20_one hes
  obtain ⟨x, rfl⟩ := head20_localGet (head20_of_caseE ha)
  have hr : InstrResOk (⟨s, f⟩ : State H) (.localGet x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2
  obtain ⟨v, hv⟩ := local_of_res (.inl hr)
  have fx := idx_of_caseE ha rfl
  have hw : Value.list w = .list (adminsToV [v.toAdmin]) :=
    (State.localGet_iff B hn hv (typedV_quant hq (by simp) fz) (typedV_quant hq (by simp) fx)).1
      (firesB_read20_iff.2 hf)
  exact ⟨[v.toAdmin], Value.list.inj hw, .localGet hv⟩

/-- **`Step_read/global.get` backwards**, at a `GoodW` configuration. -/
theorem bwdRead_globalGet {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 8 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes⟩ := firesCfg_list20 (State.hasRuleAt_globalGet B) hf
  obtain ⟨a, rfl, ha⟩ := codes20_one hes
  obtain ⟨x, rfl⟩ := head20_globalGet (head20_of_caseE ha)
  have hr : InstrResOk (⟨s, f⟩ : State H) (.globalGet x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2
  obtain ⟨ad, g, had, hgl⟩ := global_of_res (.inl hr)
  have fx := idx_of_caseE ha rfl
  have hw : Value.list w = .list (adminsToV [g.value.toAdmin]) :=
    (State.globalGet_iff B hn had hgl (typedV_quant hq (by simp) fz)
      (typedV_quant hq (by simp) fx)).1 (firesB_read20_iff.2 hf)
  exact ⟨[g.value.toAdmin], Value.list.inj hw, State.globalGet_step had hgl⟩

/-- **`Step/local.set` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_localSet {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 4 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes⟩ := firesCfg_list20 (State.hasRuleAt_localSet B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨v, rfl⟩ := val20_of_var hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head20_localSet (head20_of_caseE h₂)
  have hr : InstrResOk (⟨s, f⟩ : State H) (.localSet x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.1
  obtain ⟨v', hv'⟩ := local_of_res (.inr hr)
  have hlt : x.toNat < f.locals.length := (List.getElem?_eq_some_iff.1 hv').1
  have fv := val_of_subE h₁
  have fx := idx_of_caseE h₂ rfl
  have hw : w = configV hn ⟨s, f.setLocal x v, []⟩ :=
    (State.localSet_iff B hn hlt (typedV_quant hq (by simp) fz) (typedV_quant hq (by simp) fv)
      (typedV_quant hq (by simp) fx)).1 (firesB_step20_iff.2 hf)
  exact ⟨_, hw, .localSet hlt⟩

/-- **`Step/global.set` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_globalSet {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 5 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes⟩ := firesCfg_list20 (State.hasRuleAt_globalSet B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨v, rfl⟩ := val20_of_var hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head20_globalSet (head20_of_caseE h₂)
  have hr : InstrResOk (⟨s, f⟩ : State H) (.globalSet x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.1
  obtain ⟨ad, g, had, hgl⟩ := global_of_res (.inr hr)
  have fv := val_of_subE h₁
  have fx := idx_of_caseE h₂ rfl
  have hw : w = configV hn ⟨s.setGlobalInst ad { g with value := v }, f, []⟩ :=
    (State.globalSet_iff B hn had hgl (typedV_quant hq (by simp) fz)
      (typedV_quant hq (by simp) fv) (typedV_quant hq (by simp) fx)).1 (firesB_step20_iff.2 hf)
  exact ⟨_, hw, State.globalSet_step P host had hgl⟩

/-! ## What is left -/

/-- **What is left of `BwdRestW`**: the live `Step_read` rules other than `local.get` (7) and
`global.get` (8), and the `Step` rules from `table.set` (6) on. -/
structure BwdRestW2 (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → i ∉ [7, 8] → ∀ (c : Config H) (w : List Value), GoodW c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 6 ≤ i → ∀ (c : Config H) (w : Value), GoodW c →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- `BwdRestW` from what is left. -/
theorem bwdRestW_of_rest2 {P : Profile} {host : HostSemantics H} (R : BwdRestW2 B hn P host) :
    BwdRestW B hn P host where
  read i hd c w hg hc hw hf := by
    by_cases h7 : i = 7
    · subst h7; exact bwdRead_localGet hg hf
    by_cases h8 : i = 8
    · subst h8; exact bwdRead_globalGet hg hf
    exact R.read i hd (by simp [h7, h8]) c w hg hc hw hf
  step i hi c w hg hf := by
    by_cases h4 : i = 4
    · subst h4; exact bwdStep_localSet hg hf
    by_cases h5 : i = 5
    · subst h5; exact bwdStep_globalSet hg hf
    exact R.step i (by omega) c w hg hf

/-- **`Task.wholeStepBwdW` from what is left after this pass** (`BwdRestW2` at the spec's
builtins). -/
theorem wholeStepBwdW_of_rest2
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRestW2 (Sim.Floats.floatIntB (Profile.spec nd r)) hn (Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest fun H hn hinj host nd r => bwdRestW_of_rest2 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole
