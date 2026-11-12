module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CallIndirect
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowTyping

/-!
# `Step_read/call_indirect-trap` of 1.0, backwards

1.0's `call_indirect-trap` (rule 4 of `Step_read`, `callIndirectTrapRule10`, kernel `rfl`) is
`z; (CONST I32 i) (CALL_INDIRECT x) ~> TRAP -- otherwise`: it fires where `call_indirect-call`
(rule 3) does not fire on the same left-hand side.

Backwards, at a `GoodV1` configuration, table 0 and the type `x` exist (`ResOkL10`), and V1 does
one of four things with the entry at `i`:

* out of bounds, `callIndirectBounds`; a null entry, `callIndirectNull`; a function of another
  type, `callIndirectType` (the function exists by `StoreOk10`). Each traps, as the rule does.
* a function of the named type, `callIndirect`. Then `call_indirect-call` fires forward at
  `CALL_ADDR a` (`body10_callIndirect`), against the `otherwise` premise.

The forward firing needs the quantifiers of rule 3 typed. They are the trap rule's own (`z : state`,
`i : val_(I32)`, `x : idx`), whose typings transfer between term-only scopes
(`hasTyp_varT_nil_congr`, `hasTyp_valI32_congr10`), and `a : addr`, which holds every natural
(`typedV_addr10`). So no typing invariant on the state is needed beyond what the rule itself
quantifies: the trap rule's `z : state` is that invariant.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameTable)
open Silmaril.Wasm.Execution.Runtime (Frame FuncInst TableInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV RuleBody DDerives otherwise otherwiseAt noElse
  ValsOnly evalExp_case evalExp_list1 evalExp_tup2)
open Silmaril.Wasm.SpecTec.Sim20.Whole (constIE iPay)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The rule -/

/-- `Step_read/call_indirect-trap` of 1.0 (transcribed). -/
def callIndirectTrapRule10 : Rule :=
  .ruleD "call_indirect-trap" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "x" (.varT "idx" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "CALL_INDIRECT" (.varE "x")]]),
      .listE [.caseE "TRAP" (.tupE [])]])
    [.elsePr]

variable (B) in
theorem hasRuleAt10_callIndirectTrap :
    HasRuleAt (simEnv10 B) "Step_read" "%~>%" 4 callIndirectTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Typings across scopes -/

/-- `val_(I32)`'s typing is the same in every scope: its argument is closed, and no scope binds a
type with arguments. -/
theorem hasTyp_valI32_congr10 {env : Env} {ρ ρ' : VarEnv} {v : Value}
    (h : HasTyp env ρ valI32T' v) : HasTyp env ρ' valI32T' v := by
  have hl : localTyp? ρ "val_" [.expA (.caseE "I32" (.tupE []))] = none := by
    simp [localTyp?]
  have hl' : localTyp? ρ' "val_" [.expA (.caseE "I32" (.tupE []))] = none := by
    simp [localTyp?]
  obtain ⟨td, ws, htd, hargs, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  have ha : ∀ σ : VarEnv, EvalArgs env σ [.expA (.caseE "I32" (.tupE []))]
      [.val (caseNilV "I32")] := fun _ => evalArgs_cons Sim20.Pure.evalExp_caseNil evalArgs_nil
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.evalArgs_unique hargs (ha ρ)
  exact (hasTyp_varT_global_iff hl').2 ⟨td, _, htd, ha ρ', hi⟩

theorem findTyp_addr10 : (simEnv10 B).findTyp? "addr" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

/-- `addr` holds every natural. -/
theorem typedV_addr10 (k : Nat) : TypedV (simEnv10 B) (.varT "addr" []) (.num (.natN k)) :=
  Sim20.Whole.typedV_aliasG findTyp_addr10 (Sim20.Whole.hasTyp_nat _ _ k)

/-! ## `call_indirect-call`, forward -/

/-- The scope of `call_indirect-call`. -/
abbrev ciScope (zv iv xv : Value) (fa : Execution.Runtime.FuncAddr) : List (IL.Id × Value) :=
  [("z", zv), ("i", iv), ("x", xv), ("a", .num (.natN fa.value))]

/-- **`call_indirect-call` fires forward** where V1 calls through the table: its quantifiers
typed, its two premises evaluated at the 1.0 encoding. -/
theorem body10_callIndirect {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {s : Store H}
    {f : Frame} {x : TypeIdx} {c : BitVec 32} {t : TableInst} {fa : Execution.Runtime.FuncAddr}
    {fn : FuncInst V1.Func H} {ft : V1.FuncType}
    (tz : HasTyp (simEnv10 B) (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV c.toNat)
      (idxV x) fa)) (.varT "state" []) (stateV hn s f))
    (ti : HasTyp (simEnv10 B) (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV c.toNat)
      (idxV x) fa)) valI32T' (pctV c.toNat))
    (tx : HasTyp (simEnv10 B) (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV c.toNat)
      (idxV x) fa)) (.varT "idx" []) (idxV x))
    (ht : frameTable s f = some t) (hft : f.module.types[x.toNat]? = some ft)
    (hent : t.refs[c.toNat]? = some (some fa)) (hfn : s.funcs[fa.value]? = some fn)
    (hty : fn.type = ft) :
    RuleBody (simEnv10 B) D els [] [] "%~>%" callIndirectRule10
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, c⟩, .source (.callIndirect x)]⟩,
        .list [.case "CALL_ADDR" (.num (.natN fa.value))]]) := by
  let σ := ciScope (stateV hn s f) (pctV c.toNat) (idxV x) fa
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have fa' : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN fa.value)) := rfl
  -- The first premise: the table entry at `i` is `?(a)`.
  have hrefs : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.idxE (.dotE (.callE "table"
      [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]) "REFS") iPay)
      (.opt (some (.num (.natN fa.value)))) :=
    evalExp_idxE_iff.2 ⟨_, c.toNat, evalExp_dotE_iff.2 ⟨_, evalExp_table0_10 rfl fz ht, rfl⟩,
      Sim20.Whole.evalExp_iPay fi, by simp [Value.idx?,
        List.getElem?_map, hent]⟩
  have hp₁ : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT (.idxE (.dotE
      (.callE "table" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]) "REFS")
      iPay) (.optE (some (.varE "a")))) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, hrefs, evalExp_optE_some_iff.2 ⟨_, Sim.evalExp_var fa', rfl⟩,
      cmpValues_eq_true_iff.2 rfl⟩
  -- The second premise: the function's type is the named type.
  have hfty : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")
      (funcTypeV ft) := by
    refine evalExp_dotE_iff.2 ⟨funcInstV hn fn, evalExp_idxE_iff.2 ⟨_, fa.value,
      evalExp_funcinst10 rfl fz, Sim.evalExp_var fa', by simp [Value.idx?, List.getElem?_map, hfn]⟩,
      ?_⟩
    subst hty
    cases fn <;> rfl
  have hp₂ : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.callE "type" [.expA (.varE "z"), .expA (.varE "x")])
      (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_type10 rfl fz fx hft, hfty, cmpValues_eq_true_iff.2 rfl⟩
  -- The conclusion.
  have hc : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.tupE [.caseE "%;%" (.tupE [.varE "z",
          .listE [constIE, .caseE "CALL_INDIRECT" (.varE "x")]]),
        .listE [.caseE "CALL_ADDR" (.varE "a")]])
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, c⟩, .source (.callIndirect x)]⟩,
        .list [.case "CALL_ADDR" (.num (.natN fa.value))]]) :=
    evalExp_tup2 (evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
      (evalExp_case (Sim.evalExp_var fx)))))
      (evalExp_list1 (evalExp_case (Sim.evalExp_var fa')))
  refine ⟨rfl, VarEnv.empty, σ, rfl, ?_, hc, ?_⟩
  · exact QuantsOk.cons fz tz (QuantsOk.cons fi ti (QuantsOk.cons fx tx (QuantsOk.cons fa'
      (typedV_addr10 _ _ (Sim.valsOnly_bindVals σ)) QuantsOk.nil)))
  · intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · exact .ifPr hp₁
    · exact .ifPr hp₂

/-! ## The rule backwards -/

/-- **Where the trap rule fires, V1 does not call**: if the table entry names a function of the
named type, `call_indirect-call` fires on the same left-hand side, against `otherwise`. -/
theorem not_call_of_trap10 {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32}
    {t : TableInst} {fa : Execution.Runtime.FuncAddr} {fn : FuncInst V1.Func H} {ft : V1.FuncType}
    {w : List Value} {σ : List (IL.Id × Value)}
    (hq : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ)
      [.expP "z" (.varT "state" []), .expP "i" valI32T', .expP "x" (.varT "idx" [])])
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x))
    (hother : otherwiseAt (simEnv10 B) "Step_read" [] 4
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩, .list w]))
    (ht : frameTable s f = some t) (hft : f.module.types[x.toNat]? = some ft)
    (hent : t.refs[i.toNat]? = some (some fa)) (hfn : s.funcs[fa.value]? = some fn) :
    fn.type ≠ ft := by
  intro hty
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Sim.valsOnly_bindVals σ
  have hρ' : ValsOnly (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV i.toNat) (idxV x)
      fa)) := Sim.valsOnly_bindVals _
  obtain ⟨Z, fZ, tZ⟩ := hq "z" (.varT "state" []) (by simp)
  obtain ⟨I, fI, tI⟩ := hq "i" valI32T' (by simp)
  obtain ⟨X, fX, tX⟩ := hq "x" (.varT "idx" []) (by simp)
  have eZ : Z = stateV hn s f := Option.some.inj (fZ.symm.trans fz)
  have eI : I = pctV i.toNat := Option.some.inj (fI.symm.trans fi)
  have eX : X = idxV x := Option.some.inj (fX.symm.trans fx)
  have body : RuleBody (simEnv10 B) (DDerives (simEnv10 B) noElse)
      (otherwiseAt (simEnv10 B) "Step_read" [] 3
        (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩,
          .list [.case "CALL_ADDR" (.num (.natN fa.value))]]))
      [] [] "%~>%" callIndirectRule10
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩,
        .list [.case "CALL_ADDR" (.num (.natN fa.value))]]) :=
    body10_callIndirect (eZ ▸ Sim.IntNumeric.hasTyp_varT_nil_congr hρ hρ' tZ)
      (eI ▸ hasTyp_valI32_congr10 tI) (eX ▸ Sim.IntNumeric.hasTyp_varT_nil_congr hρ hρ' tX)
      ht hft hent hfn hty
  obtain ⟨ps, tt, rules, hrel, rfl, h3⟩ := hasRuleAt10_callIndirect B
  rw [otherwiseAt] at hother
  exact hother 3 (by decide) [] "%~>%" tt rules callIndirectRule10 hrel h3 _ ⟨_, _, _, rfl, rfl⟩
    body

/-- **`Step_read/call_indirect-trap` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_callIndirectTrap {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10 B) "Step_read" 4 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_callIndirectTrap B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨x, rfl⟩ := head10_callIndirect (head10_of_caseE h₂)
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) :=
    evalExp_varE_iff.1 (idx_of_caseE10 h₂ rfl)
  have hw : w = adminsToV [.trap] :=
    Value.list.inj (EvalExp.unique hrh (evalExp_list1 Sim20.Pure.evalExp_caseNil))
  have hother : otherwiseAt (simEnv10 B) "Step_read" [] 4
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩, .list w]) := by
    cases hp _ (List.mem_singleton_self _) with
    | elsePr h => exact h
  have hres : (frameTable s f).isSome ∧ (f.module.types[x.toNat]?).isSome := hg.1.2.1
  obtain ⟨t, ht⟩ : ∃ t, frameTable s f = some t := Option.isSome_iff_exists.1 hres.1
  obtain ⟨ft, hft⟩ : ∃ ft, f.module.types[x.toNat]? = some ft := Option.isSome_iff_exists.1 hres.2
  refine ⟨[.trap], hw, ?_⟩
  match hent : t.refs[i.toNat]? with
  | none => exact .callIndirectBounds s f x i t ht hent
  | some none => exact .callIndirectNull s f x i t ht hent
  | some (some fa) =>
    have hlt : fa.value < s.funcs.length := by
      obtain ⟨ta, -, hta⟩ := frameTable_some ht
      exact hg.2.1.2 t (List.mem_of_getElem? hta) fa (List.mem_of_getElem? hent)
    have hfn : s.funcs[fa.value]? = some s.funcs[fa.value] := List.getElem?_eq_getElem hlt
    exact .callIndirectType s f x i t fa _ ft ht hft hent hfn
      (not_call_of_trap10 hq fz (evalExp_varE_iff.1 fi) fx hother ht hft hent hfn)

end Silmaril.Wasm.SpecTec.Sim10.Whole
