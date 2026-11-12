module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModRule

/-!
# Instruction typing of the wasm-3.0 script, extended: the functions `Module_ok` calls

The clauses of the functions `Module_ok`'s premises call at the empty module, located in
`simEnv B` by a kernel `rfl` against the script's own definitions (`Original.d…`, read through
`defClauses`): `$funcidx_nonfuncs`, `$funcidx_module`, `$free_module`, `$free_list`, `$free_opt`,
`$tagsxt`, `$globalsxt`, `$memsxt`, `$tablesxt`, `$funcsxt` and `$disjoint_`; and that `X`, the
type parameter of `$disjoint_`, is not a global type (`memTyp_X`), so it matches as a pattern
variable.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d384 Original.d311 Original.d310 Original.d75 Original.d74 Original.d161 Original.d162 Original.d163 Original.d164 Original.d165 Original.d13)

variable {B : Builtins}

/-- The clauses of a function definition (or of a one-definition `rec` group). -/
def defClauses : Def → List Clause
  | .decD _ _ _ cs => cs
  | .recD [d] => defClauses d
  | _ => []

/-- The parameters and result type of a function definition. -/
def defSig : Def → List Param × Typ
  | .decD _ ps t _ => (ps, t)
  | .recD [d] => defSig d
  | _ => ([], .boolT)

set_option maxRecDepth 100000 in
/-- `X` is not a global type. -/
theorem memTyp_X : (simEnv B).memTyp "X" = false := rfl

set_option maxRecDepth 100000 in
/-- `$funcidx_nonfuncs`'s clauses. -/
theorem fd_fnf : (simEnv B).findDef? "funcidx_nonfuncs" =
    some ((defSig Original.d384).1, (defSig Original.d384).2, defClauses Original.d384) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$funcidx_module`'s clauses. -/
theorem fd_fm : (simEnv B).findDef? "funcidx_module" =
    some ((defSig Original.d311).1, (defSig Original.d311).2, defClauses Original.d311) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$free_module`'s clauses. -/
theorem fd_fmod : (simEnv B).findDef? "free_module" =
    some ((defSig Original.d310).1, (defSig Original.d310).2, defClauses Original.d310) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$free_list`'s clauses. -/
theorem fd_flist : (simEnv B).findDef? "free_list" =
    some ((defSig Original.d75).1, (defSig Original.d75).2, defClauses Original.d75) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$free_opt`'s clauses. -/
theorem fd_fopt : (simEnv B).findDef? "free_opt" =
    some ((defSig Original.d74).1, (defSig Original.d74).2, defClauses Original.d74) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$tagsxt`'s clauses. -/
theorem fd_tagsxt : (simEnv B).findDef? "tagsxt" =
    some ((defSig Original.d161).1, (defSig Original.d161).2, defClauses Original.d161) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$globalsxt`'s clauses. -/
theorem fd_globalsxt : (simEnv B).findDef? "globalsxt" =
    some ((defSig Original.d162).1, (defSig Original.d162).2, defClauses Original.d162) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$memsxt`'s clauses. -/
theorem fd_memsxt : (simEnv B).findDef? "memsxt" =
    some ((defSig Original.d163).1, (defSig Original.d163).2, defClauses Original.d163) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$tablesxt`'s clauses. -/
theorem fd_tablesxt : (simEnv B).findDef? "tablesxt" =
    some ((defSig Original.d164).1, (defSig Original.d164).2, defClauses Original.d164) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$funcsxt`'s clauses. -/
theorem fd_funcsxt : (simEnv B).findDef? "funcsxt" =
    some ((defSig Original.d165).1, (defSig Original.d165).2, defClauses Original.d165) :=
  rfl

set_option maxRecDepth 100000 in
/-- `$disjoint_`'s clauses. -/
theorem fd_disj : (simEnv B).findDef? "disjoint_" =
    some ((defSig Original.d13).1, (defSig Original.d13).2, defClauses Original.d13) :=
  rfl

end Silmaril.Wasm.SpecTec.Institution.Instr30X
