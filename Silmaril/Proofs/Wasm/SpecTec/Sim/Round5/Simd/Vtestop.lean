module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Agree

/-!
# Round 5: `vtestop` (rule 64), backward

`Step_pure/vtestop` rewrites `[v128.const c_1, i?x?.all_true]` to `[i32.const c]` under two `if`
premises: `i* = $lanes_(Jnn X M, c_1)` and `c!%.0 = $prod($inez_($jsizenn(Jnn), i)!%.0*)`. The
second only constrains the first component of `c`; the quantifier `c : num_(I32)` says that `c` is
`%(n)` (`num_i32_inv`, through `iN($sizenn(I32))` and `uN(N)`), so `c` is the image of Core's
`all_true` (`allTrue`, and `EvalExp.unique` for the premise's right-hand side).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.ExecVector (vconstV evalExp_pctFst_iff)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d22)
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type}

/-! ## `num_(I32)` holds only `%(n)` -/

/-- The cases of `uN(N)`: one, `%`, with a natural payload. -/
theorem instCases_d22 : ∃ prems, IntNumeric.instCases Original.d22 0 =
    [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] prems] := ⟨_, rfl⟩

/-- **`uN(N)` holds only `%(n)`.** -/
theorem uN_inv {B : Builtins} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "uN" [.expA e]) v) :
    ∃ n, v = .case "%" (.tuple [.num (.natN n)]) := by
  obtain ⟨ps, qs, htd⟩ := IntNumeric.findTyp_uN (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  cases htd'
  obtain ⟨u, -, rfl⟩ := evalArgs_expA_iff.1 hargs
  have hd := IntNumeric.hasTypInsts_head_inv (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    matchArgs_nil) hi
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
  obtain ⟨prems, hcs⟩ := instCases_d22
  rw [hcs] at hc
  by_cases hop : op = "%"
  · subst hop
    obtain ⟨ht, -⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    obtain ⟨vs, rfl, hvs⟩ := hasTyp_tupT_iff.1 ht
    obtain ⟨x, xs, rfl, hx, hxs⟩ := hasTypTup_cons_iff.1 hvs
    obtain rfl := hasTypTup_nil_iff.1 hxs
    obtain ⟨m, rfl, hm⟩ := hasTyp_numT_iff.1 hx
    cases m <;> simp_all [Num.toTyp, Num.subTyp]
  · exact absurd ((hasTypCase_cons_miss_iff (Ne.symm hop)).1 hc) not_hasTypCase_nil

/-- **`iN(N)` holds only `%(n)`**, through `uN(N)`. -/
theorem iN_inv {B : Builtins} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "iN" [.expA e]) v) :
    ∃ n, v = .case "%" (.tuple [.num (.natN n)]) := by
  obtain ⟨ps, qs, htd⟩ := IntNumeric.findTyp_iN (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  cases htd'
  obtain ⟨u, -, rfl⟩ := evalArgs_expA_iff.1 hargs
  have hd : HasTypDef (simEnv B) (VarEnv.empty.bindVal "N" u)
      (.aliasT (.varT "uN" [.expA (.varE "N")])) v :=
    IntNumeric.hasTypInsts_head_inv (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      matchArgs_nil) hi
  exact uN_inv (hasTypDef_aliasT_iff.1 hd)

/-- **`num_(I32)` holds only `%(n)`**: through `iN($sizenn(I32))` and `uN(N)`. -/
theorem num_i32_inv {B : Builtins} {ρ : VarEnv} {v : Value}
    (h : HasTyp (simEnv B) ρ Vec.i32T v) : ∃ n, v = pctV n := by
  obtain ⟨ps, qs, rest, htd⟩ := IntNumeric.findTyp_num (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  cases htd'
  obtain ⟨u, hu, rfl⟩ := evalArgs_expA_iff.1 hargs
  have hu' : u = IntNumeric.ntV .i32 :=
    EvalExp.unique hu (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩, rfl⟩)
  subst hu'
  have hd := IntNumeric.hasTypInsts_head_inv (matchArgs_cons (IntNumeric.matchArg_InnPat (by simp)
    (IntNumeric.argSubOk_innPat_ntV _)) matchArgs_nil) hi
  obtain ⟨n, hn⟩ := iN_inv (hasTypDef_aliasT_iff.1 hd)
  exact ⟨n, hn⟩

/-! ## Rule 64 -/

/-- A rule with two `if` premises, inverted with its quantifier typing kept. -/
theorem fires_if2Q {env : Env} {x : IL.Id} {i : Nat} {nm : IL.Id} {qs : List Param}
    {e p₁ p₂ : Exp} {v : Value}
    (hr : Equiv.Validation.HasRuleAt env x "%~>%" i (.ruleD nm qs "%~>%" e [.ifPr p₁, .ifPr p₂]))
    (hf : Fires env x i v) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      EvalExp env (VarEnv.empty.bindVals σ) p₁ (.bool true) ∧
      EvalExp env (VarEnv.empty.bindVals σ) p₂ (.bool true) := by
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := Vec.fires_body hr hf
  have h0 : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  subst h0
  exact ⟨σ, hq, he, Vec.inv_if (hp _ List.mem_cons_self),
    Vec.inv_if (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- `vecInstrV?` at `VTESTOP`. -/
theorem vecInstrV?_vtestop {i : Instr} {x : Value}
    (h : Vec.vecInstrV? i = some (.case "VTESTOP" x)) :
    ∃ sh, i = .vecAllTrue sh ∧ x = .tuple [Vec.ishV sh, caseNilV "ALL_TRUE"] := by
  cases i <;> simp [Vec.vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- The `VTESTOP` instruction of rule 64, inverted. -/
theorem inv_vtestopInstr {env : Env} {ρ : VarEnv} {v : Value}
    (h : EvalExp env ρ (.caseE "VTESTOP" (.tupE [.caseE "%X%" (.tupE [.subE (.varE "Jnn")
      (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]), .caseE "ALL_TRUE" (.tupE [])])) v) :
    ∃ jnn Mv, v = .case "VTESTOP" (.tuple [.case "%X%" (.tuple [jnn, Mv]),
      caseNilV "ALL_TRUE"]) ∧ ρ.findVal? "Jnn" = some jnn ∧ ρ.findVal? "M" = some Mv := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨s, a, rfl, hs, ha⟩ := Vec.inv_tup2 hu
  obtain rfl := Vec.inv_nil ha
  obtain ⟨sw, hsw, rfl⟩ := evalExp_caseE_iff.1 hs
  obtain ⟨jnn, Mv, rfl, hj, hM⟩ := Vec.inv_tup2 hsw
  exact ⟨jnn, Mv, rfl, evalExp_varE_iff.1 (evalExp_subE_iff.1 hj), evalExp_varE_iff.1 hM⟩

/-- One round of rule 64's iteration sees the rule's own `Jnn`. -/
theorem findVal?_round {σ : List (IL.Id × Value)} {l : Value} {y : IL.Id} (hy : y ≠ "i") :
    ((VarEnv.empty.bindVals σ).bindVals [("i", l)]).findVal? y =
      (VarEnv.empty.bindVals σ).findVal? y := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, Ne.symm hy]

/-- **`Step_pure/vtestop` (rule 64), backward**, at the concrete builtins. -/
theorem bwd_vtestop {P : Profile} {hn : H → String} {host : HostSemantics H}
    {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" 64 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, hq, he, hp₁, hp₂⟩ := fires_if2Q (Vec.hasVectorRules_simEnv _).vtestop hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := Vec.inst_c1 he
  obtain ⟨jnn, Mv, rfl, fJ, fM⟩ := inv_vtestopInstr hy
  obtain ⟨cv, rfl, fc⟩ := Vec.inv_constI32 hz
  obtain ⟨b, ins, rfl, rfl, hins⟩ := Vec.decode_c1 BwdStep.vecDecode (by simp [Vec.vecTags]) hcode
  obtain ⟨sh, rfl, hx⟩ := vecInstrV?_vtestop hins
  have hx' : Vec.ishV sh = .case "%X%" (.tuple [jnn, Mv]) := by simpa using hx.symm
  obtain ⟨hj, hM⟩ := shapeV_inv (sh := .int sh) hx'
  -- `c : num_(I32)` is `%(n)`.
  obtain ⟨cw, fcw, hcw⟩ := hq "c" Vec.i32T (by simp)
  obtain ⟨n, rfl⟩ := num_i32_inv hcw
  have hcv : cv = pctV n := Option.some.inj (fc.symm.trans fcw)
  subst hcv
  -- `i* : lane_(…)*` is a list, and premise 1 makes it the lanes of `b`.
  obtain ⟨iw, fiw, hiw⟩ := hq "i*" (.iterT (.varT "lane_" [.expA (.callE "lanetype" [.expA
    (.caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []),
      .varE "M"]))])]) .list) (by simp)
  obtain ⟨ls, rfl, -⟩ := hasTyp_iterT_list_iff.1 hiw
  have hsh : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) (.caseE "%X%"
      (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))
      (Vec.shapeV (.int sh)) :=
    by
      rw [show Vec.shapeV (.int sh) = Vec.ishV sh from rfl, hx']
      exact evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fJ)) (evalExp_var fM))
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 hp₁
  have e₁ : v₁ = .list ls :=
    EvalExp.unique h₁ (Equiv.Execution.evalExp_iterPat (by decide) fiw)
  have hargs : EvalArgs (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      [.expA (.caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []),
        .varE "M"])), .expA (.varE "c_1")] [.val (Vec.shapeV (.int sh)), .val (Vec.vecV b)] :=
    Equiv.evalArgs_cons hsh (Equiv.evalArgs_cons (evalExp_var f₁) Equiv.evalArgs_nil)
  have e₂ : v₂ = .list (lanesV (.int sh) b) :=
    Equiv.ExecNumeric.Applies.unique (Vec.inv_call rfl hargs h₂) (applies_lanes P hn host _ b)
  have hls : ls = lanesV (.int sh) b := by
    have : v₁ = v₂ := by simpa [cmpValues] using hcmp
    rw [e₁, e₂] at this
    exact Value.list.inj this
  subst hls
  -- Premise 2: the product of the lane tests is Core's `all_true`.
  obtain ⟨ls', jsz, bs, hl, hjs, hz', hpr⟩ := allTrue P hn host sh b
  have hls' : ls' = lanesV (.int sh) b :=
    Value.list.inj (Equiv.ExecNumeric.Applies.unique hl (applies_lanes P hn host (.int sh) b))
  subst hls'
  have hjs' : Applies (simEnv (BI P hn host)) "jsizenn" [.val jnn] jsz := hj ▸ hjs
  have hround : List.Forall₂ (fun l u => EvalExp (simEnv (BI P hn host))
      ((VarEnv.empty.bindVals σ).bindVals [("i", l)])
      (.projE (.uncaseE (.callE "inez_" [.expA (.callE "jsizenn" [.expA (.varE "Jnn")]),
        .expA (.varE "i")]) "%") 0) u) (lanesV (.int sh) b) (bs.map fun k => .num (.natN k)) :=
    List.forall₂_map_right_iff.2 (hz'.imp fun _ _ hb => Vec.evalExp_inezLane rfl rfl
      ((findVal?_round (by decide)).trans fJ) (by simp [VarEnv.bindVals, VarEnv.findVal?,
        Map.binds, Map.bind]) hjs' hb)
  have eprod : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "prod" [.expA (.iterE (.projE (.uncaseE (.callE "inez_" [.expA (.callE "jsizenn"
        [.expA (.varE "Jnn")]), .expA (.varE "i")]) "%") 0)
        (.mk .list [.mk "i" (.varE "i*")]))]) (.num (.natN (vecAllTrue sh b).toNat)) :=
    Vec.evalExp_call rfl (Equiv.evalArgs_cons (Vec.evalExp_iterList1 fiw hround)
      Equiv.evalArgs_nil) hpr
  obtain ⟨u₁, u₂, g₁, g₂, gcmp⟩ := evalExp_cmpE_iff.1 hp₂
  have eu₁ : u₁ = .num (.natN n) := by
    obtain ⟨rest, hrest⟩ := evalExp_pctFst_iff.1 g₁
    rw [fc] at hrest
    simp only [pctV, Option.some.injEq, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      true_and] at hrest
    exact hrest.1.symm
  have eu₂ : u₂ = .num (.natN (vecAllTrue sh b).toNat) := EvalExp.unique g₂ eprod
  have hn : n = (vecAllTrue sh b).toNat := by
    have : u₁ = u₂ := by simpa [cmpValues] using gcmp
    rw [eu₁, eu₂] at this
    simpa using this
  subst hn
  exact ⟨[constI32 (vecAllTrue sh b)], rfl, .vector (.vecAllTrue sh b)⟩

/-- **`Simd.PureOpenVtestop` at the concrete builtins.** -/
theorem pureOpenVtestop {P : Profile} {hn : H → String} {host : HostSemantics H} :
    PureOpenVtestop hn P host := fun _ _ _ _ _ _ hf => codeEq_of (bwd_vtestop hf)

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
