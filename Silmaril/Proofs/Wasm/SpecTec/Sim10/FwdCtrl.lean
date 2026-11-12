module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdReduce
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureBrSucc
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.ConstBound
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PlainInv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeSubjRed

/-!
# The 1.0 script forward at `br-zero`, `br-succ`, `return-label`, `return-frame`, `trap-vals`

Each of these rules types the code after its redex as `instr*`. At a configuration whose suffix
there is plain instructions (`Plain10`, the reachability invariant of `PlainInv`), it fires:

* `typedV_instr_of_admin10`: an instruction typed as `admininstr` is typed as `instr`. 1.0's
  IL lists `admininstr`'s cases as `instr`'s followed by `CALL_ADDR`, `LABEL_`, `FRAME_` and `TRAP`
  (`findTyp_instrAdmin10`, kernel `rfl`), and no instruction's image has one of those heads;
* `typedV_labelidx10`: every V1 label index is a typed `labelidx` (1.0's `uN(32)`, ported from
  2.0's `hasTyp_uN20`), which `br-succ` needs for the lowered label;
* `fwdAt10_labelBranch` (`br-zero`), `fwdAt10_labelBranchOuter` (`br-succ`),
  `fwdAt10_labelReturn` (`return-label`), `fwdAt10_frameReturn` (`return-frame`),
  `fwdAt10_trapValues` and `fwdAt10_trapTail` (`trap-vals`): each at a plain suffix
  `is.map .source`, at every builtins. They use 2.0's environment-generic conclusion evaluations
  (`Sim20.Pure.eval_brZero`, …), as the backward half does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression lowerLabel)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV iterPat evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly instrsT nT frameT evalExp_case
  evalExp_tup2 evalExp_list1 evalExp_ne_nil evalExp_or typedV_list_iff typedV_list_append)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_nil prems_one eval_brZero eval_brSucc
  eval_returnLabel eval_returnFrame eval_trapVals)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## `instr` inside `admininstr` -/

/-- The name of a variant case. -/
def caseName10 : TypCase → MixopS
  | .mk o _ _ _ => o

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- **1.0's `admininstr` is `instr` followed by four administrative cases.** -/
theorem findTyp_instrAdmin10 : ∃ ci ex, (simEnv10 B).findTyp? "instr" =
      some ([], [.instD [] [] (.variantT ci)]) ∧
    (simEnv10 B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT (ci ++ ex))]) ∧
    ex.map caseName10 = ["CALL_ADDR", "LABEL_%{%}%", "FRAME_%{%}%", "TRAP"] :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- A case of an appended variant is a case of the first part, or named in the second. -/
theorem hasTypCase_append_inv {env : Env} {ρ : VarEnv} {ex : List TypCase} {op : MixopS}
    {w : Value} : ∀ {cs : List TypCase}, HasTypCase env ρ (cs ++ ex) op w →
      HasTypCase env ρ cs op w ∨ op ∈ ex.map caseName10
  | [], h => by
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem h
    exact .inr (List.mem_map.2 ⟨_, hm, rfl⟩)
  | .mk o t qs prems :: cs, h => by
    by_cases ho : o = op
    · exact .inl ((hasTypCase_cons_hit_iffQ ho).2 ((hasTypCase_cons_hit_iffQ ho).1 h))
    · rcases hasTypCase_append_inv ((hasTypCase_cons_miss_iff ho).1 h) with h' | h'
      · exact .inl ((hasTypCase_cons_miss_iff ho).2 h')
      · exact .inr h'

/-- No instruction's image has an administrative head. -/
theorem instrHead10_not_admin (i : V1.Instr) :
    instrHead10 i ∉ ["CALL_ADDR", "LABEL_%{%}%", "FRAME_%{%}%", "TRAP"] := by
  cases i <;> simp [instrHead10]

/-- **An instruction typed as `admininstr` is typed as `instr`.** -/
theorem typedV_instr_of_admin10 {i : V1.Instr} (h : TypedV (simEnv10 B) adminT10 (instrToV i)) :
    TypedV (simEnv10 B) (.varT "instr" []) (instrToV i) := by
  obtain ⟨ci, ex, hi, ha, hex⟩ := findTyp_instrAdmin10 (B := B)
  obtain ⟨u, hu⟩ := instrToV_case10 i
  rw [hu] at h ⊢
  obtain ⟨op, w, he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed ha (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  rcases hasTypCase_append_inv hc with hc' | hm
  · exact fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) hi
      Equiv.evalArgs_nil matchArgs_nil hc'
  · exact absurd (hex ▸ hm) (instrHead10_not_admin i)

/-- **Plain code typed as `admininstr*` is a typed `instr*`.** -/
theorem typedV_instrs_of_admins10 {is : List V1.Instr}
    (h : TypedV (simEnv10 B) adminsT (.list (adminsToV (is.map .source)))) :
    TypedV (simEnv10 B) instrsT (.list (adminsToV (is.map .source))) := by
  rw [adminsToV_map10, List.map_map] at h ⊢
  refine typedV_list_iff.2 fun u hu => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hu
  exact typedV_instr_of_admin10 (typedV_list_iff.1 h _ hu)

/-! ## Label indices -/

/-- `uN(N)` holds every natural below `2 ^ N` in 1.0 (2.0's `hasTyp_uN20`, ported). -/
theorem hasTyp_uN10 {ρ : VarEnv} {e : Exp} {N n : Nat}
    (he : EvalExp (simEnv10 B) ρ e (Equiv.natV N)) (hn : n < 2 ^ N) :
    HasTyp (simEnv10 B) ρ (.varT "uN" [.expA e]) (.case "%" (.tuple [Equiv.natV n])) := by
  obtain ⟨ps, qs, htd⟩ := uNCases10 (B := B)
  have htup : HasTyp (simEnv10 B) (VarEnv.empty.bindVal "N" (Equiv.natV N))
      (.tupT [.mk "i" (.numT .natT)]) (.tuple [Equiv.natV n]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  have hpow : EvalExp (simEnv10 B) ((VarEnv.empty.bindVal "N" (Equiv.natV N)).bindVal "i"
      (Equiv.natV n)) (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N"))
      (Equiv.natV (2 ^ N)) := Equiv.evalExp_twoPow (by simp)
  have hsub : EvalExp (simEnv10 B) ((VarEnv.empty.bindVal "N" (Equiv.natV N)).bindVal "i"
      (Equiv.natV n)) (.binE .subOp (.numT .intT) (.cvtE (.binE .powOp (.numT .natT)
        (.numE (.natN 2)) (.varE "N")) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
      (.num (.intN ((2 ^ N : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  refine hasTyp_varT_case (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (Sim.IntNumeric.hasTypCase_of_findCase rfl htup
      (Sim.IntNumeric.premsOk_if (Sim.IntNumeric.evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (evalExp_var (v := Equiv.natV n) rfl) evalExp_num (by simp [Num.cmp])
  · refine evalExp_cmpNum (evalExp_var (v := Equiv.natV n) rfl) hk ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

/-- **Every V1 label index is a typed `labelidx`.** -/
theorem typedV_labelidx10 (l : LabelIdx) :
    TypedV (simEnv10 B) (.varT "labelidx" []) (idxV l) := by
  have h32 : TypedV (simEnv10 B) (.varT "u32" []) (idxV l) :=
    typedV_aliasG10 findTyp_u32_10 (hasTyp_uN10 evalExp_num l.value.isLt)
  have hidx : TypedV (simEnv10 B) (.varT "idx" []) (idxV l) :=
    typedV_aliasG10 findTyp_idx10 (h32 _ valsOnly_empty)
  exact typedV_aliasG10 findTyp_labelidx10 (hidx _ valsOnly_empty)

/-! ## Reading a typed label or frame body -/

/-- The image of a body `val'* val* M instr*`. -/
theorem adminsToV_body10 (extra vs : List Execution.Runtime.Value) (m : Admin)
    (is : List V1.Instr) :
    adminsToV (values extra ++ values vs ++ [m] ++ is.map .source) =
      adminsToV (values extra) ++ adminsToV (values vs) ++ [adminToV m] ++
        adminsToV (is.map .source) := by
  simp only [adminsToV_map10, List.map_append, List.map_singleton]

/-- The typed pieces of a label body `val'* val* M instr*`. -/
theorem body_typed10 {extra vs : List Execution.Runtime.Value} {m : Admin} {is : List V1.Instr}
    (h : TypedV (simEnv10 B) adminsT
      (.list (adminsToV (values extra ++ values vs ++ [m] ++ is.map .source)))) :
    TypedV (simEnv10 B) valsTy10 (.list (adminsToV (values extra))) ∧
      TypedV (simEnv10 B) valsTy10 (.list (adminsToV (values vs))) ∧
      TypedV (simEnv10 B) instrsT (.list (adminsToV (is.map .source))) := by
  rw [adminsToV_body10] at h
  obtain ⟨h₁₂, hi⟩ := typedV_list_append.1 h
  obtain ⟨h₁₂', -⟩ := typedV_list_append.1 h₁₂
  obtain ⟨h₁, h₂⟩ := typedV_list_append.1 h₁₂'
  rw [adminsToV_values] at h₁ h₂ ⊢
  rw [adminsToV_values]
  exact ⟨typedV_vals_of_admins10 h₁, typedV_vals_of_admins10 h₂, typedV_instrs_of_admins10 hi⟩

/-! ## `br-zero` and `br-succ` -/

/-- **`br-zero` forward**: V1's `labelBranch`, at a plain suffix. -/
theorem fwdAt10_labelBranch (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (extra vs : List Execution.Runtime.Value) (is : List V1.Instr) (hlen : vs.length = n) :
    FwdAt10 B hn ⟨s, f, [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++
      is.map .source)]⟩ ⟨s, f, values vs ++ expression cont⟩ := by
  subst hlen
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨-, hcont, hb⟩ := label_inv10 (typedV_head10 hc)
  obtain ⟨he₁, hv, hi⟩ := body_typed10 hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN (adminsToV (values vs)).length)),
    ("instr'*", .list (instrsToV cont)), ("val'*", .list (adminsToV (values extra))),
    ("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (values vs)).length)) := rfl
  have he := eval_brZero (env := simEnv10 B) fn rfl rfl rfl rfl
  have hlen : (adminsToV (values vs)).length = vs.length := by
    rw [adminsToV_values, List.length_map]
  have hlhs : adminsToV [.label vs.length cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++
      is.map .source)] = [.case "LABEL_%{%}%" (.tuple [.num (.natN (adminsToV (values vs)).length),
        .list (instrsToV cont), .list (adminsToV (values extra) ++ adminsToV (values vs) ++
          [.case "BR" (pctV 0)] ++ adminsToV (is.map .source))])] := by
    rw [hlen, adminsToV_label10, adminsToV_body10]
    rfl
  have hrhs : adminsToV (values vs ++ expression cont) =
      adminsToV (values vs) ++ instrsToV cont := by
    rw [adminsToV_map10, List.map_append, ← adminsToV_map10, ← adminsToV_map10,
      adminsToV_expression]
  rw [hlhs, hrhs]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_brZero B) σ
    (QuantsOk.cons fn (typedV_n10 _ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hcont _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (he₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))))
    he prems_nil)

/-- **`br-succ` forward**: V1's `labelBranchOuter`, at a plain suffix. -/
theorem fwdAt10_labelBranchOuter (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (vs : List Execution.Runtime.Value) (is : List V1.Instr) (l : LabelIdx) (hl : l.toNat ≠ 0) :
    FwdAt10 B hn ⟨s, f, [.label n cont (values vs ++ [.source (.br l)] ++ is.map .source)]⟩
      ⟨s, f, values vs ++ [.source (.br (lowerLabel l))]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨hn', hcont, hb⟩ := label_inv10 (typedV_head10 hc)
  obtain ⟨-, hv, hi⟩ := body_typed10 (extra := []) hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (values vs))), ("l", idxV (lowerLabel l)),
    ("instr*", .list (adminsToV (is.map .source)))]
  have he := eval_brSucc (env := simEnv10 B) (ρ := VarEnv.empty.bindVals σ)
    (k := l.toNat - 1) rfl rfl rfl rfl rfl
  have hk : l.toNat - 1 + 1 = l.toNat := by omega
  rw [hk] at he
  have hlhs : adminsToV [.label n cont (values vs ++ [.source (.br l)] ++ is.map .source)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont),
        .list (adminsToV (values vs) ++ [.case "BR" (pctV l.toNat)] ++
          adminsToV (is.map .source))])] := by
    rw [adminsToV_label10]
    simp only [adminsToV_map10, List.map_append]
    rfl
  have hrhs : adminsToV (values vs ++ [.source (.br (lowerLabel l))]) =
      adminsToV (values vs) ++ [.case "BR" (pctV (l.toNat - 1))] := by
    rw [adminsToV_map10, List.map_append, ← adminsToV_map10]
    rfl
  rw [hlhs, hrhs]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_brSucc B) σ
    (QuantsOk.cons rfl (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hcont _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (typedV_labelidx10 _ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hi _ ⟨rfl, rfl, rfl⟩)
          QuantsOk.nil)))))
    he prems_nil)

/-! ## `return-label` and `return-frame` -/

/-- **`return-label` forward**: V1's `labelReturn`, at a plain suffix. -/
theorem fwdAt10_labelReturn (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (vs : List Execution.Runtime.Value) (is : List V1.Instr) :
    FwdAt10 B hn ⟨s, f, [.label n cont (values vs ++ [.source .return_] ++ is.map .source)]⟩
      ⟨s, f, values vs ++ [.source .return_]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨hn', hcont, hb⟩ := label_inv10 (typedV_head10 hc)
  obtain ⟨-, hv, hi⟩ := body_typed10 (extra := []) hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have he := eval_returnLabel (env := simEnv10 B) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl
  have hlhs : adminsToV [.label n cont (values vs ++ [.source .return_] ++ is.map .source)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont),
        .list (adminsToV (values vs) ++ [caseNilV "RETURN"] ++ adminsToV (is.map .source))])] := by
    rw [adminsToV_label10]
    simp only [adminsToV_map10, List.map_append]
    rfl
  have hrhs : adminsToV (values vs ++ [.source .return_]) =
      adminsToV (values vs) ++ [caseNilV "RETURN"] := by
    rw [adminsToV_map10, List.map_append, ← adminsToV_map10]
    rfl
  rw [hlhs, hrhs]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_returnLabel B) σ
    (QuantsOk.cons rfl (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hcont _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (hi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))
    he prems_nil)

/-- **`return-frame` forward**: V1's `frameReturn`, at a plain suffix. -/
theorem fwdAt10_frameReturn (s : Store H) (f : Frame) (n : Nat) (fr : Frame)
    (extra vs : List Execution.Runtime.Value) (is : List V1.Instr) (hlen : vs.length = n) :
    FwdAt10 B hn ⟨s, f, [.frame n fr (values extra ++ values vs ++ [.source .return_] ++
      is.map .source)]⟩ ⟨s, f, values vs⟩ := by
  subst hlen
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨-, hfr, hb⟩ := frame_inv10 (typedV_head10 hc)
  obtain ⟨he₁, hv, hi⟩ := body_typed10 hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN (adminsToV (values vs)).length)),
    ("f", frameV fr), ("val'*", .list (adminsToV (values extra))),
    ("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (values vs)).length)) := rfl
  have he := eval_returnFrame (env := simEnv10 B) fn rfl rfl rfl rfl
  have hlen : (adminsToV (values vs)).length = vs.length := by
    rw [adminsToV_values, List.length_map]
  have hlhs : adminsToV [.frame vs.length fr (values extra ++ values vs ++ [.source .return_] ++
      is.map .source)] = [.case "FRAME_%{%}%" (.tuple [.num (.natN (adminsToV (values vs)).length),
        frameV fr, .list (adminsToV (values extra) ++ adminsToV (values vs) ++
          [caseNilV "RETURN"] ++ adminsToV (is.map .source))])] := by
    rw [hlen, adminsToV_frame10, adminsToV_body10]
    rfl
  rw [hlhs]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_returnFrame B) σ
    (QuantsOk.cons fn (typedV_n10 _ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hfr _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (he₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))))
    he prems_nil)

/-! ## `trap-vals` -/

/-- `trap-vals` at `val* TRAP instr*` with `val*` or `instr*` non-empty. -/
theorem fwdAt10_trapVals (s : Store H) (f : Frame) (vs : List Execution.Runtime.Value)
    (is : List V1.Instr) (hne : vs ≠ [] ∨ is ≠ []) :
    FwdAt10 B hn ⟨s, f, values vs ++ [.trap] ++ is.map .source⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  have e : values vs ++ [.trap] ++ is.map .source =
      values [] ++ values vs ++ [.trap] ++ is.map .source := rfl
  obtain ⟨-, hv, hi⟩ := body_typed10 (e ▸ hc)
  let σ : List (IL.Id × Value) :=
    [("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (adminsToV (values vs))) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "instr*" =
      some (.list (adminsToV (is.map .source))) := rfl
  have he := eval_trapVals (env := simEnv10 B) fv fi
  have hne' : decide (adminsToV (values vs) ≠ [] ∨ adminsToV (is.map .source) ≠ []) = true := by
    rw [adminsToV_values, adminsToV_map10]
    simpa [List.map_eq_nil_iff] using hne
  have hpr : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterPat "instr" "instr*") (.listE []))) (.bool true) :=
    hne' ▸ evalExp_or (evalExp_ne_nil (evalExp_iterPat (by decide) fv))
      (evalExp_ne_nil (evalExp_iterPat (by decide) fi))
  have hlhs : adminsToV (values vs ++ [.trap] ++ is.map .source) =
      adminsToV (values vs) ++ caseNilV "TRAP" :: adminsToV (is.map .source) := by
    simp only [adminsToV_map10, List.map_append, List.append_assoc, List.singleton_append]
    rfl
  rw [hlhs]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_trapVals B) σ
    (QuantsOk.cons fv (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hi _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil)) he (prems_one (.ifPr hpr)))

/-- **`trap-vals` forward**: V1's `trapValues`, at a plain suffix. -/
theorem fwdAt10_trapValues (s : Store H) (f : Frame) (v : Execution.Runtime.Value)
    (vs : List Execution.Runtime.Value) (is : List V1.Instr) :
    FwdAt10 B hn ⟨s, f, values (v :: vs) ++ [.trap] ++ is.map .source⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10_trapVals s f (v :: vs) is (.inl (List.cons_ne_nil _ _))

/-- **`trap-vals` forward**: V1's `trapTail`, at a plain suffix. -/
theorem fwdAt10_trapTail (s : Store H) (f : Frame) (i : V1.Instr) (is : List V1.Instr) :
    FwdAt10 B hn ⟨s, f, .trap :: (i :: is).map .source⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10_trapVals s f [] (i :: is) (.inr (List.cons_ne_nil _ _))

end Silmaril.Wasm.SpecTec.Sim10.Whole
