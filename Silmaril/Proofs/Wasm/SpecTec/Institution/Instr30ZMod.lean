module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZMem
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZFree

/-!
# Module typing of the wasm-3.0 script, the scope of `Module_ok` at one memory
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
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modParams modConcl modPrems modPrem0 modPrem1 modPrem2
  modPrem3 modPrem4 modPrem5 modPrem6 modPrem7 modPrem8 modPrem9 modPrem10 modPrem11 modPrem12
  modPrem13 modPrem14 modPrem15 modPrem16 modPrem17 modPrem18 modPrem19 mtNil dpremB_iterNil
  dd_typesEmpty dd_globalsEmpty findDef_closMod tryClausesUndef_closMod)

variable {B : Builtins}

/-! ## Typing -/

set_option maxRecDepth 100000 in
theorem findTyp_mem : (simEnv B).findTyp? "mem" = some ([], [.instD [] [] (.variantT
    [.mk "MEMORY" (.varT "memtype" []) [] []])]) := rfl

/-- `MEMORY mt` is a `mem`. -/
theorem typedV_memV (mt : Silmaril.Wasm.MemoryType) : TypedV (simEnv B) (.varT "mem" []) (memV mt) :=
  Typing.typedV_closedCase findTyp_mem rfl (typedV_memtype mt _ ⟨rfl, rfl, rfl⟩)

/-- **`{MEMS ms}` is a typed context** when its entries are memory types. -/
theorem ctxT_ctxMems {ms : List Value}
    (hm : ∀ u ∈ ms, TypedV (simEnv B) (.varT "memtype" []) u) : CtxT B (ctxMems ms) :=
  have hn : TypedV (simEnv B) (.iterT (.varT "resulttype" []) .opt) (.opt none) :=
    fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  have h0 {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) := Round5.RefOk.typedV_listNil
  Round5.Pos.typedV_struct Round6.Reading.findTyp_context <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 hm) <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of hn <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_one h0

/-! ## The scope -/

/-- **The scope of `Module_ok` at `memModuleV [mt]`**: as at the empty module, except
`mem* = [MEMORY mt]`, `mt* = [mt]` and `C = {MEMS [mt]}`. -/
def modσ1 (mt : Silmaril.Wasm.MemoryType) : List (IL.Id × Value) :=
  [("type*", .list []), ("import*", .list []), ("tag*", .list []), ("global*", .list []),
   ("mem*", .list [memV mt]), ("table*", .list []), ("func*", .list []), ("data*", .list []),
   ("elem*", .list []), ("start?", .opt none), ("export*", .list []),
   ("C", ctxMems [Encode.toValue mt]), ("xt_I*", .list []), ("xt_E*", .list []), ("dt'*", .list []),
   ("C'", Round6.RefOkV.ctxEmptyV), ("jt*", .list []), ("gt*", .list []),
   ("mt*", .list [Encode.toValue mt]),
   ("tt*", .list []), ("dt*", .list []), ("ok*", .list []), ("rt*", .list []), ("nm*", .list []),
   ("jt_I*", .list []), ("mt_I*", .list []), ("tt_I*", .list []), ("gt_I*", .list []),
   ("dt_I*", .list []), ("x*", .list [])]

/-- The scope, as a variable environment. -/
abbrev ρ1 (mt : Silmaril.Wasm.MemoryType) : VarEnv := VarEnv.empty.bindVals (modσ1 mt)

/-- **`modσ1 mt` is a well-typed assignment of `Module_ok`'s quantifiers.** -/
theorem quantsOk_mod1 (mt : Silmaril.Wasm.MemoryType) : QuantsOk (simEnv B) (ρ1 mt) modParams :=
  have hρ := valsOnly_bind (modσ1 mt)
  have hl {t : Typ} : HasTyp (simEnv B) (ρ1 mt) (.iterT t .list) (.list []) :=
    Round5.RefOk.typedV_listNil _ hρ
  have hc : HasTyp (simEnv B) (ρ1 mt) (.varT "context" []) Round6.RefOkV.ctxEmptyV :=
    ctxT_empty _ hρ
  have hcm : HasTyp (simEnv B) (ρ1 mt) (.varT "context" []) (ctxMems [Encode.toValue mt]) :=
    ctxT_ctxMems (fun u hu => by obtain rfl := List.mem_singleton.1 hu; exact typedV_memtype mt) _ hρ
  have hm : HasTyp (simEnv B) (ρ1 mt) (.iterT (.varT "mem" []) .list) (.list [memV mt]) :=
    typedV_list_iff.2 (fun u hu => by obtain rfl := List.mem_singleton.1 hu; exact typedV_memV mt) _ hρ
  have hmt : HasTyp (simEnv B) (ρ1 mt) (.iterT (.varT "memtype" []) .list)
      (.list [Encode.toValue mt]) :=
    typedV_list_iff.2 (fun u hu => by obtain rfl := List.mem_singleton.1 hu; exact typedV_memtype mt)
      _ hρ
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hm <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl (hasTyp_iterT_opt_iff.2 (.inl rfl)) <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hcm <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hc <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hmt <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl QuantsOk.nil

/-- The module part of the conclusion evaluates to `memModuleV [mt]`. -/
theorem evalExp_modModule1 (mt : Silmaril.Wasm.MemoryType) :
    EvalExp (simEnv B) (ρ1 mt)
      (match modConcl with | .tupE (e :: _) => e | e => e) (memModuleV [mt]) :=
  ⟨20, by
    simp [modConcl, memModuleV, pctNil, evalExp, evalExps, evalIterE, evalDoms, domSrc,
      domVar, VarEnv.findVal?, VarEnv.bindVals, modσ1, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, Value.asOpt?, iterRows, iterRow, Functor.map, Except.map, Bind.bind,
      Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩

/-- The arguments of `$clos_moduletype` in the conclusion evaluate to `({MEMS [mt]}, [] -> [])`. -/
theorem evalArgs_closMod1 (mt : Silmaril.Wasm.MemoryType) :
    EvalArgs (simEnv B) (ρ1 mt)
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))]
      [.val (ctxMems [Encode.toValue mt]), .val mtNil] :=
  ⟨10, by
    simp [mtNil, evalArgs, evalArg, evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar,
      VarEnv.findVal?, VarEnv.bindVals, modσ1, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind,
      Res.ofOption, Pure.pure, Except.pure]⟩

/-- **The conclusion evaluates to `(memModuleV [mt], v)`** when the primitives answer
`$clos_moduletype({MEMS [mt]}, [] -> [])` with `v`. -/
theorem evalExp_modConcl1 (mt : Silmaril.Wasm.MemoryType) {v : Value}
    (hB : B.call "clos_moduletype" [.val (ctxMems [Encode.toValue mt]), .val mtNil] = some v) :
    EvalExp (simEnv B) (ρ1 mt) modConcl (.tuple [memModuleV [mt], v]) := by
  obtain ⟨ps, t, hd⟩ := findDef_closMod (B := B)
  have hcall : CallDef (simEnv B) (ρ1 mt) "clos_moduletype"
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))] v := by
    refine callDef_iff.2 ⟨_, ps, t, Instr30X.closModClauses, evalArgs_closMod1 mt, ?_, .inr ⟨?_, ?_⟩⟩
    · rw [Memory.findDef_bindVals_empty, Option.getD_none]
      exact hd
    · exact tryClausesUndef_closMod _ _
    · rw [Memory.findDef_bindVals_empty, Option.getD_none, simEnv, Env.builtins_withBuiltins]
      exact hB
  exact evalExp_tup2 (evalExp_modModule1 mt) (evalExp_callE_iff.2 hcall)

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
