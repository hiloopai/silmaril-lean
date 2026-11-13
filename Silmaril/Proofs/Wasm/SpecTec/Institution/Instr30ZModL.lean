module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZMod
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZFreeL

/-!
# Module typing of the wasm-3.0 script, `Module_ok` at any list of memories (scope)

The scope `modσL mts` of `Module_ok` at `memModuleV mts`, for any list `mts` of memory types, and
the parts of the rule that see the memories, evaluated by per-shape lemmas (the lists are
symbolic, so the evaluator's equations cannot be unfolded by `simp`):

* `quantsOk_modL`, `evalExp_modConclL`: the quantifiers are typed and the conclusion evaluates;
* `dprem4_L`: `Mem_ok` over the rows `(MEMORY mt, mt)`, `mt ∈ mts`, when Core validates each;
* `dprem12_L`: `C = C' ⊕ {…, MEMS [] ++ mt*, …}` at `C = {MEMS mt*}`, `C' = {}`;
* `dprem14_L`: `[] = $funcidx_nonfuncs([], MEMORY mt*, [], [], [])`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff applies_iff_callDef)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ctxT_empty evalExp_nil pctNil)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modParams modConcl modPrem4 modPrem12 modPrem14 mtNil
  findDef_closMod tryClausesUndef_closMod fd_fnf)

variable {B : Builtins}

/-! ## The scope -/

/-- **The scope of `Module_ok` at `memModuleV mts`**: as at the empty module, except
`mem* = MEMORY mt*`, `mt* = mts` and `C = {MEMS mts}`. -/
def modσL (mts : List Silmaril.Wasm.MemoryType) : List (IL.Id × Value) :=
  [("type*", .list []), ("import*", .list []), ("tag*", .list []), ("global*", .list []),
   ("mem*", .list (mts.map memV)), ("table*", .list []), ("func*", .list []), ("data*", .list []),
   ("elem*", .list []), ("start?", .opt none), ("export*", .list []),
   ("C", ctxMems (mts.map Encode.toValue)), ("xt_I*", .list []), ("xt_E*", .list []),
   ("dt'*", .list []), ("C'", Round6.RefOkV.ctxEmptyV), ("jt*", .list []), ("gt*", .list []),
   ("mt*", .list (mts.map Encode.toValue)),
   ("tt*", .list []), ("dt*", .list []), ("ok*", .list []), ("rt*", .list []), ("nm*", .list []),
   ("jt_I*", .list []), ("mt_I*", .list []), ("tt_I*", .list []), ("gt_I*", .list []),
   ("dt_I*", .list []), ("x*", .list [])]

/-- The scope, as a variable environment. -/
abbrev ρL (mts : List Silmaril.Wasm.MemoryType) : VarEnv := VarEnv.empty.bindVals (modσL mts)

/-- **`modσL mts` is a well-typed assignment of `Module_ok`'s quantifiers.** -/
theorem quantsOk_modL (mts : List Silmaril.Wasm.MemoryType) :
    QuantsOk (simEnv B) (ρL mts) modParams :=
  have hρ := valsOnly_bind (modσL mts)
  have hl {t : Typ} : HasTyp (simEnv B) (ρL mts) (.iterT t .list) (.list []) :=
    Round5.RefOk.typedV_listNil _ hρ
  have hc : HasTyp (simEnv B) (ρL mts) (.varT "context" []) Round6.RefOkV.ctxEmptyV :=
    ctxT_empty _ hρ
  have hmts : ∀ u ∈ mts.map Encode.toValue, TypedV (simEnv B) (.varT "memtype" []) u := by
    intro u hu
    obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_memtype mt
  have hcm : HasTyp (simEnv B) (ρL mts) (.varT "context" []) (ctxMems (mts.map Encode.toValue)) :=
    ctxT_ctxMems hmts _ hρ
  have hm : HasTyp (simEnv B) (ρL mts) (.iterT (.varT "mem" []) .list) (.list (mts.map memV)) :=
    typedV_list_iff.2 (fun u hu => by
      obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_memV mt) _ hρ
  have hmt : HasTyp (simEnv B) (ρL mts) (.iterT (.varT "memtype" []) .list)
      (.list (mts.map Encode.toValue)) := typedV_list_iff.2 hmts _ hρ
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hm <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl (hasTyp_iterT_opt_iff.2 (.inl rfl)) <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hcm <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hc <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hmt <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl QuantsOk.nil

/-- `x?` iterated over an absent option evaluates to `eps`. -/
theorem evalExp_optStarNone {env : Env} {ρ : VarEnv} {x xs : IL.Id}
    (h : ρ.findVal? xs = some (.opt none)) :
    EvalExp env ρ (.iterE (.varE x) (.mk .opt [.mk x (.varE xs)])) (.opt none) :=
  ⟨10, by simp [evalExp, evalIterE, evalDoms, domSrc, domVar, h, Value.asOpt?, Bind.bind,
    Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩

/-- The module part of the conclusion evaluates to `memModuleV mts`. -/
theorem evalExp_modModuleL (mts : List Silmaril.Wasm.MemoryType) :
    EvalExp (simEnv B) (ρL mts)
      (match modConcl with | .tupE (e :: _) => e | e => e) (memModuleV mts) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_,
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_optStarNone rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) evalExps_nil, rfl⟩)

/-- **The conclusion evaluates to `(memModuleV mts, v)`** when the primitives answer
`$clos_moduletype({MEMS mts}, [] -> [])` with `v`. -/
theorem evalExp_modConclL (mts : List Silmaril.Wasm.MemoryType) {v : Value}
    (hB : B.call "clos_moduletype" [.val (ctxMems (mts.map Encode.toValue)), .val mtNil] = some v) :
    EvalExp (simEnv B) (ρL mts) modConcl (.tuple [memModuleV mts, v]) := by
  obtain ⟨ps, t, hd⟩ := findDef_closMod (B := B)
  have hargs : EvalArgs (simEnv B) (ρL mts)
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))]
      [.val (ctxMems (mts.map Encode.toValue)), .val mtNil] :=
    Equiv.evalArgs_cons (Sim.evalExp_var rfl) (Equiv.evalArgs_cons
      (evalExp_case (evalExp_tup2 (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)))
      Equiv.evalArgs_nil)
  have hcall : CallDef (simEnv B) (ρL mts) "clos_moduletype"
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))] v := by
    refine callDef_iff.2 ⟨_, ps, t, Instr30X.closModClauses, hargs, ?_, .inr ⟨?_, ?_⟩⟩
    · rw [Memory.findDef_bindVals_empty, Option.getD_none]
      exact hd
    · exact tryClausesUndef_closMod _ _
    · rw [Memory.findDef_bindVals_empty, Option.getD_none, simEnv, Env.builtins_withBuiltins]
      exact hB
  exact evalExp_tup2 (evalExp_modModuleL mts) (evalExp_callE_iff.2 hcall)

/-! ## The premises that see the memories -/

/-- The rows of a two-domain iteration over parallel images of one list (copied from
`Sim.Aggregates.iterRows_pair`). -/
theorem iterRows_pair' {α : Type} {x₁ x₂ : IL.Id} {g₁ g₂ : α → Value} (ps : List α) :
    iterRows [(x₁, ps.map g₁), (x₂, ps.map g₂)] none ps.length =
      ps.map fun p => [(x₁, g₁ p), (x₂, g₂ p)] := by
  apply List.ext_getElem
  · simp [iterRows]
  · intro i h₁ h₂
    have hi : i < ps.length := by simpa [iterRows] using h₁
    simp [iterRows, iterRow, hi]

/-- **`Module_ok`'s premise 4, `Mem_ok(C', mem, mt)` over `mem* = MEMORY mt*` and `mt* = mts`**,
holds when Core validates every `mt ∈ mts`. -/
theorem dprem4_L {mts : List Silmaril.Wasm.MemoryType} (hv : ∀ mt ∈ mts, mt.Valid) (O : ElseI)
    (els : Prop) : DPremB (simEnv B) O els (ρL mts) modPrem4 :=
  .iterList (k := mts.length) (.inl rfl)
    (xvs := [("mem", .list (mts.map memV)), ("mt", .list (mts.map Encode.toValue))])
    ⟨5, by simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL,
      Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure]⟩
    (by simp) (dls := [("mem", mts.map memV), ("mt", mts.map Encode.toValue)])
    (by simp [domLists, Value.asList?]) (by simp) (by
      intro r hr
      rw [iterRows_pair'] at hr
      obtain ⟨mt, hmt, rfl⟩ := List.mem_map.1 hr
      exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
        (Sim.evalExp_var rfl)) (dd_memOk O Instr30.ctxT_empty (hv mt hmt)))

/-- One more field, evaluated (as `Round6.TyElim.evalExpFields_cons'`). -/
theorem evalExpFields_cons'' {env : Env} {ρ : VarEnv} {a : AtomS} {e : Exp} {v : Value}
    {fs : List ExpField} {gs : List (AtomS × Value)} (h : EvalExp env ρ e v)
    (hs : EvalExpFields env ρ fs gs) : EvalExpFields env ρ (.mk a e :: fs) ((a, v) :: gs) := by
  obtain ⟨n₁, h₁⟩ := h
  obtain ⟨n₂, h₂⟩ := hs
  obtain ⟨m, hm⟩ : ∃ m, n₂ = m + 1 := by
    cases n₂ with
    | zero => simp [evalExpFields] at h₂
    | succ m => exact ⟨m, rfl⟩
  subst hm
  refine ⟨max n₁ m + 1, ?_⟩
  have e₁ := evalExp_ok_of_le (Nat.le_max_left n₁ m) h₁
  have e₂ := evalExpFields_ok_of_le (m := m + 1) (n := max n₁ m + 1) (by omega) h₂
  simp only [evalExpFields, List.mapM_cons] at e₂ ⊢
  simp [e₁, e₂]

/-- The record premise 12 adds to `C'`, at `memModuleV mts`. -/
theorem evalExp_prem12RecL (mts : List Silmaril.Wasm.MemoryType) :
    EvalExp (simEnv B) (ρL mts) (match modPrem12 with
      | .ifPr (.cmpE _ _ _ (.compE _ e)) => e | _ => .listE []) (ctxMems (mts.map Encode.toValue)) :=
  evalExp_strE_iff.2 ⟨_,
    evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' (evalExp_cat (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)) <|
    evalExpFields_cons'' (evalExp_star (by decide) rfl) <|
    evalExpFields_cons'' (evalExp_cat (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)) <|
    evalExpFields_cons'' (evalExp_cat (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)) <|
    evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' (evalExp_star (by decide) rfl) <|
    evalExpFields_cons'' (evalExp_star (by decide) rfl) <|
    evalExpFields_cons'' evalExp_nil <| evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' (evalExp_optE_none_iff.2 rfl) <| evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' evalExp_nil ⟨1, by simp [evalExpFields]; rfl⟩, rfl⟩

/-- **`Module_ok`'s premise 12, `C = C' ⊕ {…}`, holds at `memModuleV mts`.** -/
theorem dprem12_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem12 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, evalExp_compE_iff.2 ⟨_, _,
    Sim.evalExp_var rfl, evalExp_prem12RecL mts, rfl⟩, Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

/-- **`Module_ok`'s premise 14, `x* = $funcidx_nonfuncs(…)`, holds at `memModuleV mts`.** -/
theorem dprem14_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem14 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_star (by decide) rfl,
    evalExp_callE_iff.2 ((applies_iff_callDef (Memory.findDef_bindVals_empty _ _)
      (Equiv.evalArgs_cons (evalExp_case (evalExp_tupE_iff.2 ⟨_,
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) evalExps_nil, rfl⟩)) Equiv.evalArgs_nil)).1
        ⟨_, _, _, fd_fnf, .inl (tc_funcidxNonfuncsL mts)⟩),
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
