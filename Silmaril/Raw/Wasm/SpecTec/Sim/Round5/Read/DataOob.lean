module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Zero

/-!
# Round 5, pass 2, track read: `array.new_data-oob` (75), `array.init_data-oob2` (100), backward

Both rules carry `Expand($type(z, x), ARRAY mut? zt)` and the bound
`i + n * $zsize(zt)/8 > |$data(z, y).BYTES|` (with `j` for 100). `ReadValidS.seg` resolves the
data segment and gives the type of `x` (validation: an array type with numeric or vector
elements). SpecTec's `Expand` on the type's image ends at Core's expansion
(`R4Fwd.expandInv_builtins`), which fixes `zt` (`R4Fwd.zt_of_expand`); the bound then evaluates
as Core's (`R4Fwd.evalExp_newDataBound`/`evalExp_initDataBound`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open BwdRead (cfg_inv)
open Round4Read (decode_refArray decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_arrayNewData {a : Admin} (h : Typing.adminHead a = "ARRAY.NEW_DATA") :
    ∃ x y, a = .plain (.arrayNewData x y) := by
  revert h
  admin_head_inv

/-- **`Step_read` 75 (`array.new_data-oob`), backward, under `ReadValidS`.** -/
theorem bwdS_arrayNewDataOob : ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 75 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have XI := R4Fwd.expandInv_builtins (prof := P) hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayNewDataOob hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.NEW_DATA" (.tuple [X, Y])]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Aggregates.adminsToV_eq_triple hcode
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₁
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₂
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := head_arrayNewData (Typing.adminToV_case h₃).symm
  have eXY : X = Encode.toValue x ∧ Y = Encode.toValue y := by
    have h₃' : Value.case "ARRAY.NEW_DATA" (.tuple [Encode.toValue x, Encode.toValue y]) = _ := h₃
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₃'
    exact ⟨h₃'.1.symm, h₃'.2.symm⟩
  obtain ⟨rfl, rfl⟩ := eXY
  subst hZ
  obtain ⟨hdat', d, m, zt, hd, hexp, h0⟩ := hv.seg.2.2.1
  obtain ⟨⟨da, di⟩, hdat⟩ := Option.isSome_iff_exists.1 hdat'
  obtain ⟨w', hw', hD⟩ := RefsGC.premW_rule (hp _ List.mem_cons_self)
  have hzt := R4Fwd.zt_of_expand XI hρ hd hexp (evalExp_var fz) (evalExp_var fx) hw' hD
  have hb := R4Fwd.evalExp_newDataBound hρ h0 hdat (evalExp_var fz) (evalExp_var fy)
    (evalExp_var fi) (evalExp_var fn) hzt
  have e := EvalExp.unique (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) hb
  have hlt := of_decide_eq_true (Value.bool.inj e).symm
  exact ⟨[.trap], BwdRead.trap_out hc.2, .aggregate (.arrayNewDataOob hd hexp hdat h0 hlt)⟩

/-- **`Step_read` 100 (`array.init_data-oob2`), backward, under `ReadValidS`.** -/
theorem bwdS_arrayInitDataOob₂ : ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 100 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have XI := R4Fwd.expandInv_builtins (prof := P) hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayInitDataOob2 hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A, .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.INIT_DATA" (.tuple [X, Y])]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitData (Typing.adminToV_case h₅).symm
  have eXY : X = Encode.toValue x ∧ Y = Encode.toValue y := by
    have h₅' : Value.case "ARRAY.INIT_DATA" (.tuple [Encode.toValue x, Encode.toValue y]) = _ := h₅
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₅'
    exact ⟨h₅'.1.symm, h₅'.2.symm⟩
  obtain ⟨rfl, rfl⟩ := eXY
  subst hZ
  obtain ⟨hdat', d, m, zt, hd, hexp, h0⟩ := hv.seg.2.2.2.2.1
  obtain ⟨⟨da, di⟩, hdat⟩ := Option.isSome_iff_exists.1 hdat'
  obtain ⟨w', hw', hD⟩ := RefsGC.premW_rule (hp _ List.mem_cons_self)
  have hzt := R4Fwd.zt_of_expand XI hρ hd hexp (evalExp_var fz) (evalExp_var fx) hw' hD
  have hb := R4Fwd.evalExp_initDataBound hρ h0 hdat (evalExp_var fz) (evalExp_var fy)
    (evalExp_var fj) (evalExp_var fn) hzt
  have e := EvalExp.unique (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) hb
  have hlt := of_decide_eq_true (Value.bool.inj e).symm
  exact ⟨[.trap], BwdRead.trap_out hc.2, .aggregate (.arrayInitDataOob₂ hd hexp hdat h0 hlt)⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Read
