module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZMod

/-!
# Module typing of the wasm-3.0 script, `Module_ok`'s premises at one memory (A)

The premises that do not mention `mem*`, `mt*` or `C` in a non-trivial way, read in the scope
`modσ1 mt` exactly as `Instr30XModOk` reads them in `modσ` (the proofs are copies with the scope
changed): `Types_ok` and `Globals_ok` by their `empty` rules, and the iterations over empty lists.
Premise 4, `Mem_ok` iterated over `[MEMORY mt]` and `[mt]`, holds by `dd_memOk` when Core
validates `mt` (`dprem4_1`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff applies_iff_callDef)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modPrem0 modPrem1 modPrem2
  modPrem3 modPrem4 modPrem5 modPrem6 modPrem7 modPrem8 modPrem9 modPrem10 modPrem11 modPrem12
  modPrem13 modPrem14 modPrem15 modPrem16 modPrem17 modPrem18 modPrem19 dpremB_iterNil
  dd_typesEmpty dd_globalsEmpty defClauses defSig memTyp_X fd_disj fd_tagsxt fd_globalsxt fd_memsxt
  fd_tablesxt fd_funcsxt fd_fnf)

variable {B : Builtins}

/-- The scope `modσ1` reads list variables as given. -/
theorem evalDoms_mod1 {mt : Silmaril.Wasm.MemoryType} {ds : List Dom} {xvs : List (IL.Id × Value)}
    (h : evalDoms 5 (simEnv B) (ρ1 mt) ds = .ok xvs) : EvalDoms (simEnv B) (ρ1 mt) ds xvs := ⟨5, h⟩

/-- `Module_ok`'s premise 0, `Types_ok`, holds at `memModuleV [mt]`. -/
theorem dprem0_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem0 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [Round6.RefOkV.ctxEmptyV, evalExp, evalExps, evalExpFields, evalIterE, evalDoms, domSrc,
      domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind,
      Res.ofOption, Pure.pure, Except.pure]⟩ (dd_typesEmpty O)

/-- `Module_ok`'s premise 3, `Globals_ok`, holds at `memModuleV [mt]`. -/
theorem dprem3_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem3 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals,
      ρ1, modσ1, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩ (dd_globalsEmpty O)

/-- `Module_ok`'s premise 1, an iteration over empty lists, holds at `memModuleV [mt]`. -/
theorem dprem1_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem1 :=
  dpremB_iterNil (xvs := [("import", .list []), ("xt_I", .list [])]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 2, an iteration over empty lists, holds at `memModuleV [mt]`. -/
theorem dprem2_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem2 :=
  dpremB_iterNil (xvs := [("jt", .list []), ("tag", .list [])]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 5, an iteration over empty lists, holds at `memModuleV [mt]`. -/
theorem dprem5_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem5 :=
  dpremB_iterNil (xvs := [("table", .list []), ("tt", .list [])]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 6, an iteration over empty lists, holds at `memModuleV [mt]`. -/
theorem dprem6_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem6 :=
  dpremB_iterNil (xvs := [("dt", .list []), ("func", .list [])]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 7, an iteration over empty lists, holds at `memModuleV [mt]`. -/
theorem dprem7_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem7 :=
  dpremB_iterNil (xvs := [("data", .list []), ("ok", .list [])]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 8, an iteration over empty lists, holds at `memModuleV [mt]`. -/
theorem dprem8_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem8 :=
  dpremB_iterNil (xvs := [("elem", .list []), ("rt", .list [])]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 10, an iteration over empty lists, holds at `memModuleV [mt]`. -/
theorem dprem10_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem10 :=
  dpremB_iterNil (xvs := [("export", .list []), ("nm", .list []), ("xt_E", .list [])]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 9, `Start_ok` over the absent start function, holds vacuously. -/
theorem dprem9_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem9 :=
  .iterOptNone (xvs := [("start", .opt none)]) (evalDoms_mod1 (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- **`Module_ok`'s premise 4, `Mem_ok(C', mem, mt)` over `mem* = [MEMORY mt]` and `mt* = [mt]`**,
holds when Core validates `mt`. -/
theorem dprem4_1 {mt : Silmaril.Wasm.MemoryType} (hv : mt.Valid) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem4 :=
  .iterList (k := 1) (.inl rfl) (xvs := [("mem", .list [memV mt]), ("mt", .list [Encode.toValue mt])])
    (evalDoms_mod1 (by
      simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1,
        Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
        Except.pure]))
    (by simp []) (dls := [("mem", [memV mt]), ("mt", [Encode.toValue mt])]) rfl
    (by simp) (by
      intro r hr
      simp only [iterRows, iterRow, List.range_one, List.map_cons, List.map_nil, List.mem_singleton]
        at hr
      subst hr
      exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
        (Sim.evalExp_var rfl)) (dd_memOk O Instr30.ctxT_empty hv))

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
