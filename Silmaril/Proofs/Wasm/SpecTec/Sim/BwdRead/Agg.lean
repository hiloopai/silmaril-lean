module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Common
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Backward

/-!
# The aggregate null traps, backward

* `aggDecode`: the aggregates track's decoder interface `Aggregates.AggDecode`, proved by tag
  inversion (it was assumed by `Aggregates.bwd_structGetNull`, `bwd_arrayGetNull`,
  `bwd_arrayLenNull`, `Step_read` 70, 77, 80).
* `Step_read` 82 (`array.fill-null`), 93 (`array.init_elem-null`), 98 (`array.init_data-null`):
  premise-free rules; the conclusion is read back by evaluation and the code decoded.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_structGet {a : Admin} (h : Typing.adminHead a = "STRUCT.GET") :
    ∃ sx x i, a = .plain (.structGet sx x i) := by
  revert h
  admin_head_inv

theorem head_arrayGet {a : Admin} (h : Typing.adminHead a = "ARRAY.GET") :
    ∃ sx x, a = .plain (.arrayGet sx x) := by
  revert h
  admin_head_inv

theorem head_arrayLen {a : Admin} (h : Typing.adminHead a = "ARRAY.LEN") :
    a = .plain .arrayLen := by
  revert h
  admin_head_inv

theorem head_arrayFill {a : Admin} (h : Typing.adminHead a = "ARRAY.FILL") :
    ∃ x, a = .plain (.arrayFill x) := by
  revert h
  admin_head_inv

theorem head_arrayInitElem {a : Admin} (h : Typing.adminHead a = "ARRAY.INIT_ELEM") :
    ∃ x y, a = .plain (.arrayInitElem x y) := by
  revert h
  admin_head_inv

theorem head_arrayInitData {a : Admin} (h : Typing.adminHead a = "ARRAY.INIT_DATA") :
    ∃ x y, a = .plain (.arrayInitData x y) := by
  revert h
  admin_head_inv

/-- **The aggregates track's decoders, proved.** -/
theorem aggDecode : Aggregates.AggDecode where
  structGet _ _ h := head_structGet (Typing.adminToV_case h).symm
  arrayGet _ _ h := head_arrayGet (Typing.adminToV_case h).symm
  arrayLen _ _ h := head_arrayLen (Typing.adminToV_case h).symm
  constI32 a w h := (Typing.ctrlDecode_simEnv IntNumeric.intB).constI32 a w h

/-- The image of a non-empty sequence. -/
theorem adminsToV_eq_cons {is : List Admin} {v : Value} {vs : List Value}
    (h : adminsToV is = v :: vs) :
    ∃ a is', is = a :: is' ∧ adminToV a = v ∧ adminsToV is' = vs := by
  match is, h with
  | a :: is', h => exact ⟨a, is', rfl, (List.cons.inj h).1, (List.cons.inj h).2⟩
  | [], h => simp [adminsToV] at h

/-- The image of the empty sequence. -/
theorem adminsToV_eq_nil {is : List Admin} (h : adminsToV is = []) : is = [] := by
  match is, h with
  | [], _ => rfl
  | _ :: _, h => simp [adminsToV] at h

/-- `CONST I32 c`, decoded. -/
theorem decode_constI32 {a : Admin} {w : Value}
    (h : adminToV a = .case "CONST" (.tuple [caseNilV "I32", w])) : ∃ c : BitVec 32, a = constI32 c :=
  (Typing.ctrlDecode_simEnv IntNumeric.intB).constI32 a w h

/-- The image of a five-instruction sequence. -/
theorem adminsToV_eq_quint {is : List Admin} {v₁ v₂ v₃ v₄ v₅ : Value}
    (h : adminsToV is = [v₁, v₂, v₃, v₄, v₅]) :
    ∃ a₁ a₂ a₃ a₄ a₅, is = [a₁, a₂, a₃, a₄, a₅] ∧ adminToV a₁ = v₁ ∧ adminToV a₂ = v₂ ∧
      adminToV a₃ = v₃ ∧ adminToV a₄ = v₄ ∧ adminToV a₅ = v₅ := by
  obtain ⟨a₁, is₁, rfl, h₁, hc₁⟩ := adminsToV_eq_cons h
  obtain ⟨a₂, is₂, rfl, h₂, hc₂⟩ := adminsToV_eq_cons hc₁
  obtain ⟨a₃, a₄, a₅, rfl, h₃, h₄, h₅⟩ := Aggregates.adminsToV_eq_triple hc₂
  exact ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩

/-- The code `REF.NULL_ADDR (CONST I32 i) (CONST I32 j) (CONST I32 n) op`, decoded. -/
theorem decode_null3 {is : List Admin} {I J N : Value} {op : MixopS} {X : Value}
    (h : adminsToV is = [caseNilV "REF.NULL_ADDR", .case "CONST" (.tuple [caseNilV "I32", I]),
      .case "CONST" (.tuple [caseNilV "I32", J]), .case "CONST" (.tuple [caseNilV "I32", N]),
      .case op X]) :
    ∃ i j n a, is = [.ref .null, constI32 i, constI32 j, constI32 n, a] ∧ adminToV a = .case op X := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, his, h₁, h₂, h₃, h₄, h₅⟩ := adminsToV_eq_quint h
  have e₁ : a₁ = .ref .null := (Typing.ctrlDecode_simEnv IntNumeric.intB).refNull a₁ h₁
  obtain ⟨i, e₂⟩ := decode_constI32 h₂
  obtain ⟨j, e₃⟩ := decode_constI32 h₃
  obtain ⟨n, e₄⟩ := decode_constI32 h₄
  exact ⟨i, j, n, a₅, by rw [his, e₁, e₂, e₃, e₄], h₅⟩

/-- The code `REF.NULL_ADDR (CONST I32 i) val (CONST I32 n) op`, decoded. -/
theorem decode_nullFill {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {is : List Admin}
    {I V N : Value} {op : MixopS} {X : Value} (hV : HasTyp (simEnv B) ρ State.valT V)
    (h : adminsToV is = [caseNilV "REF.NULL_ADDR", .case "CONST" (.tuple [caseNilV "I32", I]),
      V, .case "CONST" (.tuple [caseNilV "I32", N]), .case op X]) :
    ∃ (i : BitVec 32) (v : Val) (n : BitVec 32) (a : Admin), is = [.ref .null, constI32 i, v.toAdmin, constI32 n, a] ∧
      adminToV a = .case op X := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, his, h₁, h₂, h₃, h₄, h₅⟩ := adminsToV_eq_quint h
  have e₁ : a₁ = .ref .null := (Typing.ctrlDecode_simEnv IntNumeric.intB).refNull a₁ h₁
  obtain ⟨i, e₂⟩ := decode_constI32 h₂
  obtain ⟨v, e₃⟩ := (Typing.stateDecode_simEnv B).val a₃ ρ hρ (h₃ ▸ hV)
  obtain ⟨n, e₄⟩ := decode_constI32 h₄
  exact ⟨i, v, n, a₅, by rw [his, e₁, e₂, e₃, e₄], h₅⟩

variable (B : Builtins)

/-- **`Backward.read 82`** (`array.fill-null`). -/
theorem bwd_arrayFillNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 82 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (Aggregates.rd B).arrayFillNull hf)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  have hc : ∃ Z I N X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list
      [caseNilV "REF.NULL_ADDR", .case "CONST" (.tuple [caseNilV "I32", I]), V,
        .case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [N])]), .case "ARRAY.FILL" X]]) ∧
      w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨Z, I, N, X, hcfg, hw⟩ := hc
  obtain ⟨i, v, n, a, his, ha⟩ := decode_nullFill (valsOnly_bindVals σ) hV (cfg_inv hcfg).2
  obtain ⟨x, hx⟩ := head_arrayFill (Typing.adminToV_case ha).symm
  have hstep : Step P host ⟨s, f, is⟩ ⟨s, f, [.trap]⟩ := by
    rw [his, hx]
    exact .aggregate .arrayFillNull
  exact ⟨[.trap], trap_out hw, hstep⟩

/-- **`Backward.read 93`** (`array.init_elem-null`). -/
theorem bwd_arrayInitElemNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 93 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (Aggregates.rd B).arrayInitElemNull hf)
  have hc : ∃ Z I J N X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list
      [caseNilV "REF.NULL_ADDR", .case "CONST" (.tuple [caseNilV "I32", I]),
        .case "CONST" (.tuple [caseNilV "I32", J]),
        .case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [N])]),
        .case "ARRAY.INIT_ELEM" X]]) ∧ w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨Z, I, J, N, X, hcfg, hw⟩ := hc
  obtain ⟨i, j, n, a, his, ha⟩ := decode_null3 (cfg_inv hcfg).2
  obtain ⟨x, y, hxy⟩ := head_arrayInitElem (Typing.adminToV_case ha).symm
  have hstep : Step P host ⟨s, f, is⟩ ⟨s, f, [.trap]⟩ := by
    rw [his, hxy]
    exact .aggregate .arrayInitElemNull
  exact ⟨[.trap], trap_out hw, hstep⟩

/-- **`Backward.read 98`** (`array.init_data-null`). -/
theorem bwd_arrayInitDataNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 98 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (Aggregates.rd B).arrayInitDataNull hf)
  have hc : ∃ Z I J N X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list
      [caseNilV "REF.NULL_ADDR", .case "CONST" (.tuple [caseNilV "I32", I]),
        .case "CONST" (.tuple [caseNilV "I32", J]),
        .case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [N])]),
        .case "ARRAY.INIT_DATA" X]]) ∧ w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨Z, I, J, N, X, hcfg, hw⟩ := hc
  obtain ⟨i, j, n, a, his, ha⟩ := decode_null3 (cfg_inv hcfg).2
  obtain ⟨x, y, hxy⟩ := head_arrayInitData (Typing.adminToV_case ha).symm
  have hstep : Step P host ⟨s, f, is⟩ ⟨s, f, [.trap]⟩ := by
    rw [his, hxy]
    exact .aggregate .arrayInitDataNull
  exact ⟨[.trap], trap_out hw, hstep⟩

end Silmaril.Wasm.SpecTec.Sim.BwdRead
