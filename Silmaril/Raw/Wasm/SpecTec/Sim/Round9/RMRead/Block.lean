module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMRead.FrameAddr

/-!
# Round 9, rm: `block` and `loop` at `configVD` (unrefined)

Round 6's `Bwd.bwd_block` and `bwd_loop` (`Step_read` 0 and 1), re-run at `configVD` at the
concrete primitives. The premise reads `$blocktype_(z, bt)`; the primitive `blocktypeCall` reads
only the frame of `z`, so at a `stateVD` image it is the same as at the `stateV` image
(`blocktypeD_inv`, round 6's `Prims.blocktype_inv` at `stateVD`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD stateVD adminsToVD adminToVD instrsToVD adminsToVD_eq_single
  adminsToVD_append adminsToVD_vals adminsToVD_expression configVD_cfgV)
open RMPure (toV_of_atomD valsD_of adminsToVD_eq_split)

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- **`$blocktype_` at a `stateVD` image reads back to Core's block type.** -/
theorem blocktypeD_inv (s : Store H) (f : Frame) (bt : BlockType) (v₁ v₂ : List Value)
    (h : Applies (simEnv (Prims.builtins P hn host)) "blocktype_"
      [.val (stateVD hn s f), .val (Encode.toValue bt)] (Exn.instrTypeV v₁ v₂)) :
    ∃ t₁ t₂ : List CValType, f.module.blockType? bt = some (t₁, t₂) ∧
      v₁.length = t₁.length ∧ v₂.length = t₂.length := by
  have D := Prims.blocktypeDefs_simEnv (Prims.builtins P hn host)
  cases bt with
  | empty =>
    obtain ⟨rfl, rfl⟩ := Prims.instrTypeV_inj
      (Applies.unique h (Prims.applies_blocktypeResult D _ none))
    exact ⟨[], [], rfl, rfl, rfl⟩
  | value t =>
    obtain ⟨rfl, rfl⟩ := Prims.instrTypeV_inj
      (Applies.unique h (Prims.applies_blocktypeResult D _ (some (Encode.toValue t))))
    exact ⟨_, _, rfl, rfl, rfl⟩
  | typeIdx x =>
    obtain ⟨ps, t, cs, hd, hc⟩ := h
    obtain ⟨ps', t', cs', hd', hn'⟩ := Prims.not_tryClauses_blocktypeIdx D
      (Z := stateVD hn s f) (w := Encode.toValue x) (v := Exn.instrTypeV v₁ v₂)
    obtain ⟨rfl, rfl, rfl⟩ : ps' = ps ∧ t' = t ∧ cs' = cs := by simpa [hd'] using hd
    have hb : Prims.blocktypeCall (stateVD hn s f) (Encode.toValue x) =
        some (Exn.instrTypeV v₁ v₂) := by
      rcases hc with hc | ⟨-, hb⟩
      · exact absurd hc hn'
      · exact (Prims.call_blocktype hn host _ _).symm.trans hb
    have e : Prims.blocktypeCall (stateVD hn s f) (Encode.toValue x) =
        Prims.blocktypeCall (Sim.stateV hn s f) (Encode.toValue x) := rfl
    rw [e, Prims.blocktypeCall_stateV, Option.map_eq_some_iff] at hb
    obtain ⟨⟨t₁, t₂⟩, hbt, he⟩ := hb
    obtain ⟨rfl, rfl⟩ := Prims.instrTypeV_inj he.symm
    exact ⟨t₁, t₂, hbt, List.length_map _, List.length_map _⟩

/-- The premise of `block` and `loop` at a `stateVD` image. -/
theorem blockTypeD_prem {s : Store H} {f : Frame} {ρ : VarEnv} {bt : BlockType}
    (hd : ρ.findDef? "blocktype_" = none) (fz : ρ.findVal? "z" = some (stateVD hn s f))
    (fb : ρ.findVal? "bt" = some (Encode.toValue bt))
    (h : EvalExp (simEnv (Prims.builtins P hn host)) ρ (.cmpE .eqOp .boolT
      (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")])
      (.caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])]), .listE [],
        .caseE "%" (.tupE [.iterE (.varE "t_2")
          (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])]))) (.bool true)) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧
      ρ.findVal? "m" = some (.num (.natN t₁.length)) ∧
      ρ.findVal? "n" = some (.num (.natN t₂.length)) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e : v₁ = v₂ := by simpa [cmpValues] using hc
  obtain ⟨T₁, T₂, fm, fn, rfl⟩ := Bwd.blockTypePat_inv h₂
  obtain ⟨t₁, t₂, hbt, h₁', h₂'⟩ :=
    blocktypeD_inv (P := P) (host := host) s f bt T₁ T₂ (e ▸ Bwd.applies_of_call2 hd fz fb h₁)
  exact ⟨t₁, t₂, hbt, h₁' ▸ fm, h₂' ▸ fn⟩

/-- `BLOCK` or `LOOP` at `adminToVD`. -/
theorem blockLoopD_of {a : Admin} {op : MixopS} {x : Value} (h : adminToVD a = .case op x)
    (hop : op = "BLOCK" ∨ op = "LOOP") :
    ∃ bt body, (a = .plain (.block bt body) ∨ a = .plain (.loop bt body)) ∧
      (op = "BLOCK" → a = .plain (.block bt body)) ∧ (op = "LOOP" → a = .plain (.loop bt body)) ∧
      x = .tuple [Encode.toValue bt, .list (instrsToVD body)] := by
  have hh := Round7.MemSimd.adminToVD_case h
  cases a with
  | plain i =>
    cases i <;> rcases hop with rfl | rfl <;> simp [Typing.adminHead, Typing.instrHead] at hh
    all_goals
      rename_i bt body
      simp only [adminToVD, Round7.MemSimd.instrToVD, Value.case.injEq] at h
      exact ⟨bt, body, by simp, by simp, by simp, h.2.symm⟩
  | ref r =>
    rcases hop with rfl | rfl <;> cases r <;> simp [Typing.adminHead, Typing.refHead] at hh
  | _ => rcases hop with rfl | rfl <;> simp [Typing.adminHead] at hh

/-- The left-hand side `z; val^m (BLOCK|LOOP bt instr*)`, decoded at `configVD`. -/
theorem blockLhsD {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {code : List Admin} {z btv : Value} {is : List Value} {op : MixopS}
    (hop : op = "BLOCK" ∨ op = "LOOP")
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some z)
    (fb : (VarEnv.empty.bindVals σ).findVal? "bt" = some btv)
    (fi : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list is))
    (htv : ∀ ws, (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws) →
      HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws))
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z",
      .catE (valsNPat "val" "val*" "m") (.listE [.caseE op (.tupE [.varE "bt",
        iterPat "instr" "instr*"])])])) (configVD hn ⟨s, f, code⟩)) :
    ∃ vs a bt body ws, code = vals vs ++ [a] ∧ z = stateVD hn s f ∧
      (op = "BLOCK" → a = .plain (.block bt body)) ∧ (op = "LOOP" → a = .plain (.loop bt body)) ∧
      btv = Encode.toValue bt ∧ is = instrsToVD body ∧
      (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws) ∧
      (VarEnv.empty.bindVals σ).findVal? "m" = some (.num (.natN ws.length)) ∧
      adminsToV (vals vs) = ws ∧ ws.length = vs.length := by
  have ei : EvalExp (simEnv B) _ (iterPat "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have hl₀ := Bwd.cfg_inv (Round7.MemSimd.configVD_eq hn ⟨s, f, code⟩ ▸ hl) fz
  obtain ⟨ws, fv, fm, hcode⟩ := Bwd.valsN_cat hl₀.2
    (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) ei)))
  obtain ⟨l₀, a, l₂, rfl, h₀, ha, h₂⟩ := adminsToVD_eq_split (C := [])
    (by rw [Value.list.inj hcode, List.append_nil])
  have hl₂ : l₂ = [] := by
    rw [Round7.MemSimd.adminsToVD_eq_map] at h₂; exact List.map_eq_nil_iff.1 h₂
  subst hl₂
  obtain ⟨vs, rfl, hv, hlen⟩ := valsD_of h₀ (htv ws fv)
  obtain ⟨bt, body, -, hB, hL, hx⟩ := blockLoopD_of ha hop
  have hbv : btv = Encode.toValue bt ∧ is = instrsToVD body := by
    simpa only [Value.tuple.injEq, List.cons.injEq, Value.list.injEq, and_true] using hx
  exact ⟨vs, a, bt, body, ws, by simp, hl₀.1, hB, hL, hbv.1, hbv.2, fv, fm, hv, hlen⟩

theorem bwdRD_block : LeafRD (Prims.builtins P hn host) hn P host 0 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules (Prims.builtins P hn host)).block hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨btv, fb, -⟩ := quant_of (x := "bt") (t := .varT "blocktype" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨vs, a, bt, body, ws, rfl, hz, hB, -, hbt, his, fv, fm, hv, hlen⟩ :=
    blockLhsD (.inl rfl) fz fb fi (Bwd.valsTyped_of hq (.tail _ (.tail _ (.head _)))) hl
  obtain rfl := hB rfl
  obtain ⟨t₁, t₂, hbt', fm₁, fn₂⟩ :=
    blockTypeD_prem rfl (hz ▸ fz) (hbt ▸ fb) (ifPrem (hp _ (.head _)))
  have hm : vs.length = t₁.length := hlen ▸ Bwd.natN_inj (Option.some.inj (fm.symm.trans fm₁))
  have ei : EvalExp (simEnv (Prims.builtins P hn host)) _ (iterPat "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have hw : w = .list [.case "LABEL_%{%}%" (.tuple [.num (.natN t₂.length), .list [],
      .list (ws ++ is)])] :=
    EvalExp.unique hr (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn₂)
      evalExp_listNil (evalExp_cat (evalExp_valsNPat (by decide) fm fv) ei))))
  have hw' : w = .list (adminsToVD [.label t₂.length [] (vals vs ++ expression body)]) := by
    rw [hw, ← hv, his, ← adminsToVD_expression, ← adminsToVD_vals, ← adminsToVD_append]
    rfl
  exact ⟨_, hw', .block hbt' hm⟩

theorem bwdRD_loop : LeafRD (Prims.builtins P hn host) hn P host 1 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules (Prims.builtins P hn host)).loop hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨btv, fb, -⟩ := quant_of (x := "bt") (t := .varT "blocktype" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨vs, a, bt, body, ws, rfl, hz, -, hL, hbt, his, fv, fm, hv, hlen⟩ :=
    blockLhsD (.inr rfl) fz fb fi (Bwd.valsTyped_of hq (.tail _ (.tail _ (.head _)))) hl
  obtain rfl := hL rfl
  obtain ⟨t₁, t₂, hbt', fm₁, fn₂⟩ :=
    blockTypeD_prem rfl (hz ▸ fz) (hbt ▸ fb) (ifPrem (hp _ (.head _)))
  have hm : vs.length = t₁.length := hlen ▸ Bwd.natN_inj (Option.some.inj (fm.symm.trans fm₁))
  have ei : EvalExp (simEnv (Prims.builtins P hn host)) _ (iterPat "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have hw : w = .list [.case "LABEL_%{%}%" (.tuple [.num (.natN t₁.length),
      .list [.case "LOOP" (.tuple [btv, .list is])], .list (ws ++ is)])] :=
    EvalExp.unique hr (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fm₁)
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) ei)))
      (evalExp_cat (evalExp_valsNPat (by decide) fm fv) ei))))
  have hw' : w = .list (adminsToVD [.label t₁.length [.loop bt body]
      (vals vs ++ expression body)]) := by
    rw [hw, ← hv, hbt, his]
    simp only [adminsToVD, Round7.MemSimd.adminToVD, Round7.MemSimd.instrsToVD,
      Round7.MemSimd.instrToVD, adminsToVD_append, adminsToVD_vals, adminsToVD_expression]
  exact ⟨_, hw', .loop hbt' hm⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
