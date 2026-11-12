module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.DataOob

/-!
# Round 5, pass 2, track read: `array.init_data-zero` (101), backward, under `ReadValidS`

The rule carries `otherwise` and `n = 0`. Core's `arrayInitDataZero` needs the array (liveness),
the data segment (`ReadValidS.seg`) and both start indices in bounds. The array index is read
back through `array.init_data-oob1` (99), which shares the rule's quantifiers. The data index
is read back through `array.init_data-oob2` (100), whose quantifiers add `mut?` and `zt`: its body
is built at a fresh assignment from the type `ReadValidS.seg` gives (`body_arrayInitDataOob₂`),
with `Expand` derived without `otherwise` (`Fwd.dderives_expandB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open BwdRead (cfg_inv)
open Round4Read (decode_refArray decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **`array.init_data-oob2` (100) fires on a data range out of bounds**: its body, at the
assignment of Core's instance, with `Expand` read without `otherwise`. -/
theorem body_arrayInitDataOob₂ {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {i j n : BitVec 32} {a da : Nat} {d : DefType} {m : Mutability} {zt : CStorageType}
    {di : DataInst} {els : Prop} (hM : Round4.ModuleBnd f.module) (hd : f.type? x = some d)
    (he : Expand d (.array (.field m zt))) (hdat : s.data? f y = some (da, di))
    (h0 : 0 < storageSize zt) (h : di.bytes.size < j.toNat + n.toNat * storageSize zt / 8)
    (hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn s f)) :
    RuleBody (simEnv (BI P hn host)) (DDerives (simEnv (BI P hn host)) noElse) els [] [] "%~>%"
      Equiv.ExecRead.arrayInitDataOob2Rule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩, .list [.case "TRAP" (.tuple [])]]) := by
  have : Fact (Round4.ModuleBnd f.module) := ⟨hM⟩
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have A := Fwd.aggTypesB_of (Int.typesB (BI P hn host))
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y), ("mut?", mutV m), ("zt", tyV zt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hb := R4Fwd.evalExp_initDataBound (B := BI P hn host) hρ h0 hdat (by eval_tac)
    (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac)
  rw [decide_eq_true h] at hb
  have hbd : Round4.tyBnd zt = true := Fwd.tyBnd_arrayZt' he hd
  refine ⟨rfl, VarEnv.empty, σ, rfl,
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) (QuantsOk.cons rfl (A.mut_ m _ hρ)
      (QuantsOk.cons rfl (A.storagetype _ _ hρ) QuantsOk.nil)))))))),
    by eval_tac, fun pr hpr => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .rulePr (evalArgs_nil _ _) (R4Fwd.evalExp_expandArray hρ hd rfl rfl rfl rfl)
      (Fwd.dderives_expandB (Int.typesB _) noElse (Fwd.tyBnd_type' hd) he)
  · exact .ifPr hb

/-- **`Step_read` 101 (`array.init_data-zero`), backward, under `ReadValidS`.** -/
theorem bwdS_arrayInitDataZero : ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 101 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hct hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayInitDataZero hf)
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
      .case "ARRAY.INIT_DATA" (.tuple [X, Y])]]) ∧ w = .list [] := by
    concl_inv he
  obtain ⟨hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitData (Typing.adminToV_case h₅).symm
  subst hZ
  have h0n : Value.num (.natN n.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (evalExp_var fn) RefsGC.evalExp_num'
  have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using h0n)
  subst hn0
  obtain ⟨ai, ha⟩ := Option.isSome_iff_exists.1 hv.r.live.1
  obtain ⟨hdat', d, m, zt, hd, hexp, h0⟩ := hv.seg.2.2.2.2.1
  obtain ⟨⟨da, di⟩, hdat⟩ := Option.isSome_iff_exists.1 hdat'
  have ho := Round4Read.else_head hp
  have hl := RefsGC.lhs_of_concl he
  have hle₁ : i.toNat ≤ ai.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitDataOob1 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G (valsOnly_bindVals σ) (evalExp_var fz)
        (evalExp_var fa) ha)) (by simpa using hlt))
  have hle₂ : j.toNat ≤ di.bytes.size := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitDataOob2 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩ ?_
    exact body_arrayInitDataOob₂ (j := j) (n := 0) hv.frame hd hexp hdat h0 (by simp; exact hlt)
      (((Typing.typingFacts_simEnv _ hn).config _).1 hct).1
  refine ⟨[], by rw [hw]; rfl, ?_⟩
  exact .aggregate (.arrayInitDataZero ha hdat ⟨hle₁, hle₂⟩)

end Silmaril.Wasm.SpecTec.Sim.Round5.Read
