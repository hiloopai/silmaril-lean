module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CallAddr

/-!
# `Step_read/call_indirect-call` of 1.0, backwards

1.0's `call_indirect-call` (rule 3 of `Step_read`, transcribed as `callIndirectRule10`, kernel
`rfl`) is `z; (CONST I32 i) (CALL_INDIRECT x) ~> (CALL_ADDR a)` under
`$table(z, 0).REFS[i] = ?(a)` and `$type(z, x) = $funcinst(z)[a].TYPE`.

Backwards, at a `GoodV1` configuration: table 0 and the type exist (`ResOkL10`); the first premise
reads the table entry `some a` (`entry_of_eval10`); the function exists because table entries name
functions (`StoreOk10`); and the second premise is V1's `typeMatch`, since `funcTypeV` is injective.
The rule is V1's `Step.callIndirect`.

`call_indirect-trap` (rule 4) is `otherwise`. Discharging it backwards needs the call rule to be
shown *not* to fire, which needs its quantifier `z` typed as a `state`; the obligations of
`BwdRest10h` do not carry the typing of the state, so it is left open.
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
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 idxPayload evalExp_call1 evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Whole (constIE numTypeV_inj)
open Silmaril.Wasm.SpecTec.Sim20.State (sfxPat matchArgs_sfx)
open Silmaril.Wasm.SpecTec.Sim.Bwd (eq_of_cmp)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The rule -/

/-- `Step_read/call_indirect-call` of 1.0 (transcribed). -/
def callIndirectRule10 : Rule :=
  .ruleD "call_indirect-call" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "x" (.varT "idx" []), .expP "a" (.varT "addr" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "CALL_INDIRECT" (.varE "x")]]),
      .listE [.caseE "CALL_ADDR" (.varE "a")]])
    [.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.callE "table" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]) "REFS") Sim20.Whole.iPay)
        (.optE (some (.varE "a")))),
      .ifPr (.cmpE .eqOp .boolT (.callE "type" [.expA (.varE "z"), .expA (.varE "x")])
        (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE"))]

variable (B) in
theorem hasRuleAt10_callIndirect :
    HasRuleAt (simEnv10 B) "Step_read" "%~>%" 3 callIndirectRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem head10_callIndirect {a : Admin} (h : adminHead10 a = "CALL_INDIRECT") :
    ∃ x, a = .source (.callIndirect x) := by
  revert h; admin_head_inv10

/-! ## `$table`, `$type`, and the type test -/

theorem hasClause_table10 : HasClause1 (simEnv10 B) "table" sfxPat
    (.idxE (.dotE (.varE "s") "TABLES") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "TABLES")
      idxPayload)) := ⟨_, _, _, rfl⟩

theorem hasClause_type10 : HasClause1 (simEnv10 B) "type" sfxPat
    (.idxE (.dotE (.dotE (.varE "f") "MODULE") "TYPES") idxPayload) := ⟨_, _, _, rfl⟩

/-- The table of a frame, unfolded. -/
theorem frameTable_some {s : Store H} {f : Frame} {t : TableInst} (h : frameTable s f = some t) :
    ∃ a, f.module.tables[0]? = some a ∧ s.tables[a.value]? = some t := by
  simp only [frameTable, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  exact h

/-- **`$table(z, 0)`** at the 1.0 encoding. -/
theorem evalExp_table0_10 {ρ : VarEnv} {s : Store H} {f : Frame} {t : TableInst}
    (hρ : ρ.findDef? "table" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (ht : frameTable s f = some t) :
    EvalExp (simEnv10 B) ρ (.callE "table" [.expA (.varE "z"),
      .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]) (tableInstV t) := by
  obtain ⟨a, ha, hs⟩ := frameTable_some ht
  exact evalExp_call1 hasClause_table10 hρ
    (evalArgs_cons (evalExp_var fz) (evalArgs_cons evalExp_pct0 evalArgs_nil)) matchArgs_sfx
    (evalExp_idxE_iff.2 ⟨_, a.value, evalExp_dotE_iff.2 ⟨storeV hn s, evalExp_var rfl, rfl⟩,
      evalExp_idxE_iff.2 ⟨_, 0, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
        evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, rfl⟩, rfl⟩,
        evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, hs]⟩)

/-- **`$type(z, x)`** at the 1.0 encoding. -/
theorem evalExp_type10 {ρ : VarEnv} {s : Store H} {f : Frame} {x : TypeIdx} {ft : V1.FuncType}
    (hρ : ρ.findDef? "type" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (idxV x)) (ht : f.module.types[x.toNat]? = some ft) :
    EvalExp (simEnv10 B) ρ (.callE "type" [.expA (.varE "z"), .expA (.varE "x")])
      (funcTypeV ft) :=
  evalExp_call1 hasClause_type10 hρ
    (evalArgs_cons (evalExp_var fz) (evalArgs_cons (evalExp_var fx) evalArgs_nil)) matchArgs_sfx
    (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, rfl⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, List.getElem?_map, ht]⟩)

/-- `funcTypeV` is injective. -/
theorem funcTypeV_inj10 {t t' : V1.FuncType} (h : funcTypeV t = funcTypeV t') : t = t' := by
  have hinj : Function.Injective (List.map valTypeV) :=
    List.map_injective_iff.2 fun _ _ e => numTypeV_inj e
  simp only [funcTypeV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    true_and, and_true] at h
  cases t
  cases t'
  simp only [V1.FuncType.mk.injEq]
  exact ⟨hinj h.1, hinj h.2⟩

/-! ## The premises, read back -/

/-- **The first premise, read back**: the table entry at `i` is `some a`. -/
theorem entry_of_eval10 {ρ : VarEnv} {s : Store H} {f : Frame} {t : TableInst} {c : BitVec 32}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV c.toNat))
    (ht : frameTable s f = some t) (hρ : ρ.findDef? "table" = none)
    (h : EvalExp (simEnv10 B) ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.callE "table"
      [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]) "REFS") Sim20.Whole.iPay)
      (.optE (some (.varE "a")))) (.bool true)) :
    ∃ fa, t.refs[c.toNat]? = some (some fa) ∧ ρ.findVal? "a" = some (.num (.natN fa.value)) := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  obtain ⟨A, hA, rfl⟩ := evalExp_optE_some_iff.1 h₂
  obtain ⟨wl, j, hwl, hj, hidx⟩ := evalExp_idxE_iff.1 h₁
  have ewl : wl = .list (t.refs.map fun r => .opt (r.map fun a => .num (.natN a.value))) :=
    EvalExp.unique hwl (evalExp_dotE_iff.2 ⟨_, evalExp_table0_10 hρ fz ht, rfl⟩)
  have ej : j = c.toNat := Sim.Bwd.natN_inj (EvalExp.unique hj (Sim20.Whole.evalExp_iPay fi))
  have hget : (t.refs.map fun r => Value.opt (r.map fun a => .num (.natN a.value)))[c.toNat]? =
      some (.opt (some A)) := by
    rw [← ej]
    simpa [Value.idx?, ewl] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨r, hr, hrv⟩ := Option.map_eq_some_iff.1 hget
  obtain ⟨fa, rfl, rfl⟩ : ∃ fa, r = some fa ∧ A = .num (.natN fa.value) := by
    cases r with
    | none => simp at hrv
    | some fa => exact ⟨fa, rfl, by simpa using hrv.symm⟩
  exact ⟨fa, hr, evalExp_varE_iff.1 hA⟩

/-- **The second premise, read back**: the function's type is the named type. -/
theorem typeMatch_of_eval10 {ρ : VarEnv} {s : Store H} {f : Frame} {x : TypeIdx}
    {ft : V1.FuncType} {fa : Execution.Runtime.FuncAddr} {fn : FuncInst V1.Func H}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (idxV x))
    (fa' : ρ.findVal? "a" = some (.num (.natN fa.value)))
    (ht : f.module.types[x.toNat]? = some ft) (hfn : s.funcs[fa.value]? = some fn)
    (hρ₁ : ρ.findDef? "type" = none) (hρ₂ : ρ.findDef? "funcinst" = none)
    (h : EvalExp (simEnv10 B) ρ (.cmpE .eqOp .boolT (.callE "type" [.expA (.varE "z"),
      .expA (.varE "x")]) (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE"))
      (.bool true)) : fn.type = ft := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have ev : v = funcTypeV ft := EvalExp.unique h₁ (evalExp_type10 hρ₁ fz fx ht)
  obtain ⟨u, hu, hfld⟩ := evalExp_dotE_iff.1 h₂
  obtain ⟨fi, hfi, rfl⟩ := funcinst_of_eval10 fz fa' hρ₂ hu
  have efi : fi = fn := Option.some.inj (hfi.symm.trans hfn)
  rw [efi] at hfld
  have hty : funcTypeV fn.type = funcTypeV ft := by
    rw [← ev]
    cases fn <;> simpa [funcInstV, Value.field?, FuncInst.type] using hfld
  exact funcTypeV_inj10 hty

/-! ## The rule backwards -/

/-- **`Step_read/call_indirect-call` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_callIndirect {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step_read" 3 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_callIndirect B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨x, rfl⟩ := head10_callIndirect (head10_of_caseE h₂)
  have hres : (frameTable s f).isSome ∧ (f.module.types[x.toNat]?).isSome := hg.1.2.1
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hres.1
  obtain ⟨ft, hft⟩ := Option.isSome_iff_exists.1 hres.2
  obtain ⟨fa, hent, fa'⟩ := entry_of_eval10 fz (evalExp_varE_iff.1 fi) ht rfl
    (Sim20.Pure.ifPrem (hp _ (.head _)))
  have hlt : fa.value < s.funcs.length := by
    obtain ⟨ta, -, hta⟩ := frameTable_some ht
    exact hg.2.1.2 t (List.mem_of_getElem? hta) fa (List.mem_of_getElem? hent)
  have hfn : s.funcs[fa.value]? = some s.funcs[fa.value] := List.getElem?_eq_getElem hlt
  have hty : s.funcs[fa.value].type = ft := typeMatch_of_eval10 fz (idx_of_caseE10 h₂ rfl |>
    evalExp_varE_iff.1) fa' hft hfn rfl rfl (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _))))
  have hw : w = adminsToV [.invoke fa] :=
    Value.list.inj (EvalExp.unique hrh (evalExp_list1 (evalExp_case (evalExp_var fa'))))
  exact ⟨_, hw, .callIndirect s f x i t fa _ ft ht hft hent hfn hty⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
