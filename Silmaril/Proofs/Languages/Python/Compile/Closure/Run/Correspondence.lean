module

public import Silmaril.Languages.Python.Compile.Closure.Run.Defs
public import Silmaril.Languages.Python.Compile.Closure.Link.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.Closure.Run

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure
open Compile.Closure.Run (ArgumentsTranslation Compiled ExecutorEntry NameReadTranslation OperandTranslation
  TableTranslation Translation arguments? executorEntry lowerCode nameRead? operand?)
open Core.Closure (Layout)
open Core.Closure.Executor (NameRead Operand)
open Core.Closure.Dispatch (Definition resolve resolve_iff)

private theorem operand_complete {layout : Layout} {source : Body.Expr layout} {target : Operand layout}
    (translated : OperandTranslation source target) : operand? source = some ⟨target, translated⟩ := by
  induction translated with
  | addInt _ _ first second => simp [operand?, first, second]
  | mulInt _ _ first second => simp [operand?, first, second]
  | _ => rfl

private theorem name_read_complete {layout : Layout} {source : Body.Expr layout} {target : NameRead layout}
    (translated : NameReadTranslation source target) : nameRead? source = some ⟨target, translated⟩ := by
  cases translated <;> rfl

private theorem arguments_complete {layout : Layout} {sources : List (Body.Expr layout)}
    {targets : List (Operand layout)} (translated : ArgumentsTranslation sources targets) :
    arguments? sources = some ⟨targets, translated⟩ := by
  induction translated with
  | nil => rfl
  | cons first _ ih => simp [arguments?, operand_complete first, ih]

theorem lower_complete {layout : Layout} {source : Link.Code layout}
    {target : Core.Closure.Executor.Body layout} (translated : Translation source target) :
    lowerCode source = some ⟨target, translated⟩ := by
  induction translated with
  | ret value =>
    have complete := operand_complete value
    cases value <;> simp [lowerCode, complete]
  | returnClosure => rfl
  | returnClosureCall arguments => simp [lowerCode, arguments_complete arguments]
  | retLocalCall arguments => simp [lowerCode, arguments_complete arguments]
  | retGlobalCall arguments => simp [lowerCode, arguments_complete arguments]


  | assert test _ remaining => simp [lowerCode, operand_complete test, remaining]
  | assertFreeVars read _ remaining => simp [lowerCode, name_read_complete read, remaining]
  | assertCellVars read _ remaining => simp [lowerCode, name_read_complete read, remaining]
  | assertCodeNames read _ remaining => simp [lowerCode, name_read_complete read, remaining]
  | discardCall callee _ remaining => simp [lowerCode, operand_complete callee, remaining]
  | assign value _ remaining =>
    have complete := operand_complete value
    cases value <;> simp [lowerCode, complete, remaining]
  | call callee arguments _ remaining =>
    simp [lowerCode, operand_complete callee, arguments_complete arguments, remaining]
  | closure _ remaining => simp [lowerCode, remaining]

theorem lower_rejected_iff {layout : Layout} (source : Link.Code layout) :
    lowerCode source = none ↔ ¬∃ target, Translation source target := by
  constructor
  · rintro absent ⟨_, translated⟩
    rw [lower_complete translated] at absent
    contradiction
  · intro noTranslation
    cases lowered : lowerCode source with
    | none => rfl
    | some target => exact False.elim (noTranslation ⟨target.val, target.property⟩)

theorem table_entry {blocks : List Link.Block} {entries : List ExecutorEntry}
    (translation : TableTranslation blocks entries) {key : Nat} {block : Link.Block}
    (found : blocks[key]? = some block) :
    ∃ body, Translation block.entry.definition.body body ∧
      entries[key]? = some (executorEntry block body) := by
  induction translation generalizing key with
  | nil => simp at found
  | @cons first body rest targets head tail ih =>
    cases key with
    | zero =>
      have same : first = block := Option.some.inj found
      subst block
      exact ⟨body, head, rfl⟩
    | succ n => exact ih found

theorem resolve_entry {source : Source.Module} (compiled : Compiled source) :
    ∃ target : Core.Closure.Executor.Body compiled.entry.layout,
      Translation (Link.linkBody 1 compiled.sourceBody.moduleTree compiled.sourceBody.code).code target ∧
      resolve compiled.table compiled.entry = .ok
        { parameters := compiled.sourceBody.parameters
          body := target
          freevars := (Link.link compiled.sourceBody).entryFreeVars
          cellvars := (Link.link compiled.sourceBody).entryCellVars
          codeNames := (Link.link compiled.sourceBody).entryCodeNames } := by
  obtain ⟨target, translated, lookup⟩ := table_entry compiled.lowered (key := 0) rfl
  exact ⟨target, translated, resolve_iff.mpr lookup⟩

theorem resolve_reference {source : Source.Module} (compiled : Compiled source)
    {path : Source.BlockPath} {ref : Core.Closure.CodeRef}
    (emitted : (path, ref) ∈ (Link.link compiled.sourceBody).references) :
    ∃ (definition : Definition Link.Code ref.layout) (target : Core.Closure.Executor.Body ref.layout),
      resolve (Link.link compiled.sourceBody).table ref = .ok definition ∧
      Translation definition.body target ∧
      resolve compiled.table ref = .ok
        { parameters := definition.parameters
          body := target
          freevars := definition.freevars
          cellvars := definition.cellvars
          codeNames := definition.codeNames
          varnames := definition.varnames
          variadic := definition.variadic } := by
  obtain ⟨definition, original, resolved⟩ := Link.resolve_reference compiled.sourceBody emitted
  obtain ⟨target, translated, lookup⟩ := table_entry compiled.lowered original
  exact ⟨definition, target, resolved, translated, resolve_iff.mpr lookup⟩

end Silmaril.Proofs.Languages.Python.Compile.Closure.Run
