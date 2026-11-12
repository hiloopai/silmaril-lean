module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.IterN

/-!
# Family X, backward: `try_table` and `throw`

`bwd_read_tryTable` (`Backward.read 22`) and `bwd_step_throw` (`Backward.step 10`). Both rules
count values with `val^m`/`val^n` and match the counts against types (`t_1^m`, `t_2^n`, `t^n`),
so the proofs invert counted iterations (`IterN.lean`). The store helpers are inverted through
`Helpers` (`blocktype_inv`, `tag_inv`, `expand_inv`, uniqueness of `$exninst`, `$tagaddr`,
`$as_deftype`, `$add_exninst`), and the value prefix is read back through `Decoders.vals`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV evalExp_iterPat evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation

section Block

variable {H : Type} {env : Env} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- `vals ++ [i]` read back from `val^m ++ [C e]`. -/
theorem valsNLast_decode {ρ : VarEnv} {m : IL.Id} {op : MixopS} {e : Exp} {code : List Admin}
    (h : EvalExp env ρ (.catE (Equiv.Execution.valsNPat "val" "val*" m) (.listE [.caseE op e]))
      (.list (adminsToV code))) :
    ∃ l₁ a u vs, code = l₁ ++ [a] ∧ adminToV a = .case op u ∧ EvalExp env ρ e u ∧
      ρ.findVal? "val*" = some (.list vs) ∧ ρ.findVal? m = some (.num (.natN vs.length)) ∧
      adminsToV l₁ = vs := by
  obtain ⟨a, b, ha, hb, hab⟩ := evalExp_cat_inv h
  obtain ⟨vs, fv, fm, hvs⟩ := evalExp_valsNPat_inv (by decide) ha
  obtain ⟨x, rfl, hx⟩ := evalExp_list1_inv' hb
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hx
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := adminsToV_eq_append hab
  obtain ⟨a₀, rfl, ha₀⟩ := adminsToV_eq_one h₂
  exact ⟨l₁, a₀, u, vs, rfl, ha₀, hu, fv, fm, by rw [h₁]; exact Value.list.inj hvs⟩

/-- A one-component tuple, inverted. -/
theorem evalExp_tup1_inv {ρ : VarEnv} {e : Exp} {v : Value} (h : EvalExp env ρ (.tupE [e]) v) :
    ∃ u, EvalExp env ρ e u ∧ v = .tuple [u] := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨u, us, hu, hus, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain rfl := evalExps_nil_iff.1 hus
  exact ⟨u, hu, rfl⟩

/-- `%(e)`, inverted. -/
theorem evalExp_pct_inv {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.caseE "%" (.tupE [e])) v) :
    ∃ u, EvalExp env ρ e u ∧ v = .case "%" (.tuple [u]) := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨u, hu, rfl⟩ := evalExp_tup1_inv hw
  exact ⟨u, hu, rfl⟩

/-- `%(t_1^m) ->_[] %(t_2^n)`, inverted. -/
theorem instrType_inv {ρ : VarEnv} {v : Value}
    (h : EvalExp env ρ (.caseE "%->_%%" (.tupE [
      .caseE "%" (.tupE [.iterE (.varE "t_1")
          (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])]),
      .listE [],
      .caseE "%" (.tupE [.iterE (.varE "t_2")
          (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])]))
      v) :
    ∃ v₁ v₂, v = instrTypeV v₁ v₂ ∧ ρ.findVal? "m" = some (.num (.natN v₁.length)) ∧
      ρ.findVal? "n" = some (.num (.natN v₂.length)) := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨a, as₁, ha, has, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨b, bs, hb, hbs, rfl⟩ := evalExps_cons_iff.1 has
  obtain ⟨c, cs, hc, hcs, rfl⟩ := evalExps_cons_iff.1 hbs
  obtain rfl := evalExps_nil_iff.1 hcs
  obtain ⟨ua, hua, rfl⟩ := evalExp_pct_inv ha
  obtain ⟨uc, huc, rfl⟩ := evalExp_pct_inv hc
  obtain ⟨v₁, -, fm, rfl⟩ := evalExp_varN_inv (by decide) hua
  obtain ⟨v₂, -, fn, rfl⟩ := evalExp_varN_inv (by decide) huc
  obtain rfl : b = .list [] := EvalExp.unique hb evalExp_nil
  exact ⟨v₁, v₂, rfl, fm, fn⟩

/-- The premise of `try_table`, inverted: the block type resolves, with the arities `m`, `n`. -/
theorem tryTable_prem_inv (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {bt : BlockType} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fbt : ρ.findVal? "bt" = some (Encode.toValue bt)) (hd : ρ.findDef? "blocktype_" = none)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT
      (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")])
      (.caseE "%->_%%" (.tupE [
        .caseE "%" (.tupE [.iterE (.varE "t_1")
          (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])]),
        .listE [],
        .caseE "%" (.tupE [.iterE (.varE "t_2")
          (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])])))
      (.bool true)) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧
      ρ.findVal? "m" = some (.num (.natN t₁.length)) ∧
      ρ.findVal? "n" = some (.num (.natN t₂.length)) := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have heq : u₁ = u₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  obtain ⟨v₁, v₂, rfl, fm, fn⟩ := instrType_inv hu₂
  have happ : Equiv.ExecNumeric.Applies env "blocktype_"
      [.val (stateV hn s f), .val (Encode.toValue bt)] (instrTypeV v₁ v₂) :=
    heq ▸ (Equiv.ExecNumeric.applies_iff_callDef hd (Equiv.evalArgs_cons (evalExp_var fz)
      (Equiv.evalArgs_cons (evalExp_var fbt) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 hu₁)
  obtain ⟨t₁, t₂, hbt, h₁, h₂⟩ := Hp.blocktype_inv s f bt v₁ v₂ happ
  exact ⟨t₁, t₂, hbt, h₁ ▸ fm, h₂ ▸ fn⟩

/-- A typed `val*` quantifier, at its binding. -/
theorem vals_typed {ρ : VarEnv} {qs : List Param} {vs : List Value} (hq : QuantsOk env ρ qs)
    (hm : Param.expP "val*" valsT ∈ qs) (fv : ρ.findVal? "val*" = some (.list vs)) :
    HasTyp env ρ valsT (.list vs) := by
  obtain ⟨w₀, fv₀, ht⟩ := hq _ _ hm
  rw [fv] at fv₀
  rw [Option.some.inj fv₀]
  exact ht

/-- The right-hand side of `try_table`, evaluated at the decoded configuration. -/
theorem tryTable_rhs {ρ : VarEnv} {k : Nat} {cs : List Catch} {vs : List Val} {body : List Instr}
    {w : Value} (fn : ρ.findVal? "n" = some (.num (.natN k)))
    (hcs : EvalExp env ρ (.iterE (.varE "catch") (.mk .list [.mk "catch" (.varE "catch*")]))
      (.list (cs.map Encode.toValue)))
    (hv : EvalExp env ρ (Equiv.Execution.valsNPat "val" "val*" "m") (.list (adminsToV (vals vs))))
    (hbody : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list (instrsToV body)))
    (hre : EvalExp env ρ (.listE [.caseE "HANDLER_%{%}%" (.tupE [.varE "n",
      .iterE (.varE "catch") (.mk .list [.mk "catch" (.varE "catch*")]),
      .listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [],
        .catE (Equiv.Execution.valsNPat "val" "val*" "m")
          (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))])]])]) w) :
    w = .list (adminsToV [.handler k cs [.label k [] (vals vs ++ expression body)]]) := by
  have hw := EvalExp.unique hre (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) hcs
    (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) evalExp_nil
      (evalExp_cat hv hbody)))))))
  rw [hw, ← adminsToV_expression, ← adminsToV_append]
  rfl

/-- `%(catch*)` inside `TRY_TABLE`, read back. -/
theorem tryCatches_inv {ρ : VarEnv} {cs : List Catch}
    (h : EvalExp env ρ (.caseE "%" (.tupE [.iterE (.varE "catch")
      (.mk .list [.mk "catch" (.varE "catch*")])]))
      (.case "%" (.tuple [.list (cs.map Encode.toValue)]))) :
    EvalExp env ρ (.iterE (.varE "catch") (.mk .list [.mk "catch" (.varE "catch*")]))
      (.list (cs.map Encode.toValue)) := by
  obtain ⟨u', hcs, hu'⟩ := evalExp_pct_inv h
  have hu'' : u' = .list (cs.map Encode.toValue) :=
    (List.cons.inj (Value.tuple.inj (Value.case.inj hu').2)).1.symm
  exact hu'' ▸ hcs

/-- `Step_read/try_table`, backward. -/
theorem bwd_read_tryTable (R : HasReadRules env) (Hp : HelpersInv env hn) (Dc : Decoders env hn) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 22 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := fires_body R.tryTable hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨l₁, a, u, vs, rfl, ha, hu, fv, fm, hl₁⟩ := valsNLast_decode hce
  obtain ⟨bt, cs, body, rfl, rfl⟩ := (adminToV_case ha).2.2.2.2.1 rfl
  obtain ⟨hbt, hcsE, hbody⟩ := evalExp_tup3_inv hu
  obtain ⟨t₁, t₂, hbtt, fm', fn⟩ : ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ _ ∧ _ := by
    cases hp _ (List.mem_singleton_self _) with
    | ifPr h => exact tryTable_prem_inv Hp (evalExp_varE_iff.1 hz) (evalExp_varE_iff.1 hbt) rfl h
  obtain ⟨vs', rfl⟩ := Dc.vals _ ⟨rfl, rfl, rfl⟩ l₁ (hl₁ ▸ vals_typed hq (by simp) fv)
  have hm : (VarEnv.empty.bindVals σ).findVal? "m" = some (.num (.natN vs.length)) := fm
  have hlen : vs'.length = t₁.length := by
    have e : vs.length = t₁.length := by simpa [hm] using fm'
    simpa [← hl₁, adminsToV_vals] using e
  have hv : EvalExp env (VarEnv.empty.bindVals σ) (Equiv.Execution.valsNPat "val" "val*" "m")
      (.list (adminsToV (vals vs'))) := hl₁ ▸ evalExp_valsNPat (by decide) fv fm
  exact ⟨_, tryTable_rhs fn (tryCatches_inv hcsE) hv hbody hre, .tryTable hbtt hlen⟩

/-- A one-argument call, inverted. -/
theorem evalExp_call1_inv {ρ : VarEnv} {g : IL.Id} {e : Exp} {v : Value}
    (hd : ρ.findDef? g = none) (h : EvalExp env ρ (.callE g [.expA e]) v) :
    ∃ u, EvalExp env ρ e u ∧ Equiv.ExecNumeric.Applies env g [.val u] v := by
  obtain ⟨ws, ps, t, cs, hws, -, -⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h)
  obtain ⟨u, ws', hu, hws', rfl⟩ := Equiv.ExecReadControl.evalArgs_expA_cons_iff.1 hws
  obtain rfl : ws' = [] := evalArgs_nil_iff.1 hws'
  exact ⟨u, hu, (Equiv.ExecNumeric.applies_iff_callDef hd hws).2 (evalExp_callE_iff.1 h)⟩

/-- `FUNC %(t^n) -> %([])`, inverted. -/
theorem funcType_inv {ρ : VarEnv} {v : Value}
    (h : EvalExp env ρ (.caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t")
      (.mk (.listN (.varE "n") none) [.mk "t" (.varE "t*")])]), .caseE "%" (.tupE [.listE []])]))
      v) :
    ∃ tvs, v = funcTypeV tvs [] ∧ ρ.findVal? "n" = some (.num (.natN tvs.length)) := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨a, as₁, ha, has, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨b, bs, hb, hbs, rfl⟩ := evalExps_cons_iff.1 has
  obtain rfl := evalExps_nil_iff.1 hbs
  obtain ⟨ua, hua, rfl⟩ := evalExp_pct_inv ha
  obtain ⟨tvs, -, fn, rfl⟩ := evalExp_varN_inv (by decide) hua
  obtain rfl : b = .case "%" (.tuple [.list []]) :=
    EvalExp.unique hb (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons evalExp_nil evalExps_nil,
      rfl⟩))
  exact ⟨tvs, rfl, fn⟩

/-- The arguments of the `Expand` premise of `throw`, inverted. -/
theorem throw_expandArgs_inv (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {x : TagIdx} {wE : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (hd₁ : ρ.findDef? "as_deftype" = none) (hd₂ : ρ.findDef? "tag" = none)
    (he : EvalExp env ρ (.tupE [.callE "as_deftype"
          [.expA (.dotE (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")],
        .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t")
            (.mk (.listN (.varE "n") none) [.mk "t" (.varE "t*")])]),
          .caseE "%" (.tupE [.listE []])])]) wE) :
    ∃ ta ti tvs, s.tag? f x = some (ta, ti) ∧ wE = .tuple [CT.defType ti.type, funcTypeV tvs []] ∧
      ρ.findVal? "n" = some (.num (.natN tvs.length)) := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 he
  obtain ⟨d, ds, hdE, hds, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨ft, fts, hft, hfts, rfl⟩ := evalExps_cons_iff.1 hds
  obtain rfl := evalExps_nil_iff.1 hfts
  obtain ⟨u, hu, happ⟩ := evalExp_call1_inv hd₁ hdE
  obtain ⟨tv, htv, hfield⟩ := evalExp_dotE_iff.1 hu
  have htag : Equiv.ExecNumeric.Applies env "tag"
      [.val (stateV hn s f), .val (Encode.toValue x)] tv :=
    (Equiv.ExecNumeric.applies_iff_callDef hd₂ (Equiv.evalArgs_cons (evalExp_var fz)
      (Equiv.evalArgs_cons (evalExp_var fx) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 htv)
  obtain ⟨ta, ti, htag', rfl⟩ := Hp.tag_inv s f x tv htag
  have hu' : u = CT.defType ti.type := (Option.some.inj hfield).symm
  have hd' : d = CT.defType ti.type :=
    Equiv.ExecNumeric.Applies.unique happ (hu' ▸ Hp.asDeftype ti.type)
  obtain ⟨tvs, rfl, fn⟩ := funcType_inv hft
  exact ⟨ta, ti, tvs, htag', by rw [hd'], fn⟩

/-- The `Expand` premise of `throw`, inverted: the tag exists and its type expands to a function
type with `n` parameters. -/
theorem throw_expand_inv (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {x : TagIdx} {els : Prop} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (hd₁ : ρ.findDef? "as_deftype" = none) (hd₂ : ρ.findDef? "tag" = none)
    (h : PremW env (DDerives env (otherwise env)) els ρ (.rulePr "Expand" [] "%~~%"
      (.tupE [.callE "as_deftype"
          [.expA (.dotE (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")],
        .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t")
            (.mk (.listN (.varE "n") none) [.mk "t" (.varE "t*")])]),
          .caseE "%" (.tupE [.listE []])])]))) :
    ∃ ta ti ts, s.tag? f x = some (ta, ti) ∧ Expand ti.type (.func ts .nil) ∧
      ρ.findVal? "n" = some (.num (.natN ts.length)) := by
  cases h with
  | rulePr hargs he hD =>
      obtain ⟨ta, ti, tvs, htag, rfl, fn⟩ := throw_expandArgs_inv Hp fz fx hd₁ hd₂ he
      have hD' : DDerives env (otherwise env) "Expand" "%~~%" []
          (.tuple [CT.defType ti.type, funcTypeV tvs []]) := evalArgs_nil_iff.1 hargs ▸ hD
      obtain ⟨ts, hex, hlen⟩ := Hp.expand_inv ti.type tvs hD'
      exact ⟨ta, ti, ts, htag, hex, hlen ▸ fn⟩

/-- The address premise of `throw`, inverted: `a` is the next exception address. -/
theorem throw_addr_inv (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (hd : ρ.findDef? "exninst" = none)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.varE "a")
      (.lenE (.callE "exninst" [.expA (.varE "z")]))) (.bool true)) :
    ρ.findVal? "a" = some (.num (.natN s.exns.length)) := by
  obtain ⟨t₁, t₂, ht₁, ht₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have e₁ : t₁ = t₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  have hx : EvalExp env ρ (.callE "exninst" [.expA (.varE "z")]) (.list (s.exns.map exnInstV)) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef hd
      (Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil)).mp (Hp.exninst s f))
  have e₂ : t₂ = .num (.natN s.exns.length) :=
    EvalExp.unique ht₂ (evalExp_lenE_iff.2 ⟨_, hx, by simp⟩)
  rw [← e₂, ← e₁]
  exact evalExp_varE_iff.1 ht₁

/-- The record premise of `throw`, inverted: `exn` is the new exception instance. -/
theorem throw_exn_inv (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {x : TagIdx} {ta : Nat} {vs : List Val} (ht : f.module.tags[x.toNat]? = some ta)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (fv : ρ.findVal? "val*" = some (.list (vs.map valV)))
    (fn : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (hd : ρ.findDef? "tagaddr" = none)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.varE "exn")
      (.strE [.mk "TAG" (.idxE (.callE "tagaddr" [.expA (.varE "z")])
          (.projE (.uncaseE (.varE "x") "%") 0)),
        .mk "FIELDS" (.iterE (.varE "val")
          (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))]))
      (.bool true)) :
    ρ.findVal? "exn" = some (exnInstV ⟨ta, vs⟩) := by
  obtain ⟨t₁, t₂, ht₁, ht₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have e₁ : t₁ = t₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  have e₂ : t₂ = exnInstV ⟨ta, vs⟩ :=
    EvalExp.unique ht₂ (evalExp_strE_iff.2 ⟨_, evalExpFields_two
      (evalExp_tagaddrAt Hp ht fz fx hd) (evalExp_varN (by decide) fv fn), rfl⟩)
  rw [← e₂, ← e₁]
  exact evalExp_varE_iff.1 ht₁

/-- `Step/throw`, backward. -/
theorem bwd_step_throw (R : Equiv.ExecStepRules.HasStepRules env) (Hp : HelpersInv env hn)
    (Dc : Decoders env hn) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step" 10 (.tuple [configV hn c, w]) → BwdP hn P host c w := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := fires_body R.throw hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, hre⟩ := evalExp_concl_inv he
  have fz : _ = some (stateV hn s f) := evalExp_varE_iff.1 hz
  obtain ⟨l₁, a, u, vs, rfl, ha, hu, fv, fn, hl₁⟩ := valsNLast_decode hce
  obtain ⟨x, rfl, rfl⟩ := (adminToV_case ha).2.2.2.1 rfl
  have fx : _ = some (Encode.toValue x) := evalExp_varE_iff.1 hu
  obtain ⟨vs', rfl⟩ := Dc.vals _ ⟨rfl, rfl, rfl⟩ l₁ (hl₁ ▸ vals_typed hq (by simp) fv)
  have hvs : vs = vs'.map valV := by rw [← hl₁, adminsToV_vals]
  subst hvs
  obtain ⟨ta, ti, ts, htag, hex, fn'⟩ :=
    throw_expand_inv Hp fz fx rfl rfl (hp _ (List.mem_cons_self ..))
  have hlen : vs'.length = ts.length := by
    rw [fn] at fn'
    simpa using fn'
  have fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN s.exns.length)) := by
    cases hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
    | ifPr h => exact throw_addr_inv Hp fz rfl h
  have fe : (VarEnv.empty.bindVals σ).findVal? "exn" = some (exnInstV ⟨ta, vs'⟩) := by
    cases hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) with
    | ifPr h => exact throw_exn_inv Hp (tags_of_tag? htag) fz fx fv fn rfl h
  have hadd : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "add_exninst" [.expA (.varE "z"), .expA (.listE [.varE "exn"])])
      (stateV hn (s.addExn ⟨ta, vs'⟩) f) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_list1 (evalExp_var fe))
        Equiv.evalArgs_nil))).mp (Hp.addExn s f ⟨ta, vs'⟩))
  exact ⟨⟨s.addExn ⟨ta, vs'⟩, f, throwing s.exns.length⟩,
    EvalExp.unique hre (evalExp_case (evalExp_tup2 hadd (evalExp_throwExn fa))),
    .throw htag hex hlen⟩

end Block
end Silmaril.Wasm.SpecTec.Sim.Exn
