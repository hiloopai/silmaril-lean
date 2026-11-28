module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.Schema

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip

open Silmaril.Formats
open Arrow.RecursiveSchema.Batch.Rows (Cell Row)
open Parquet Parquet.RecursiveSchema.Tree
open Rows.Projection

private theorem foldlM_agrees {State Item : Type} {first second : State → Item → Option State}
    (step : ∀ state item next, first state item = some next → second state item = some next)
    {items : List Item} {initial result : State} (success : items.foldlM first initial = some result) :
    items.foldlM second initial = some result := by
  induction items generalizing initial with
  | nil => exact success
  | cons item rest ih =>
    cases reached : first initial item with
    | none => simp [List.foldlM_cons, reached, bind, Option.bind] at success
    | some next =>
      simpa [List.foldlM_cons, step _ _ _ reached, bind, Option.bind] using
        ih (by simpa [List.foldlM_cons, reached, bind, Option.bind] using success)

private theorem fields_agree {State : Type} {first second : RecursiveSchema.Repeated.Field → Nat → Cell → State → Option State}
    (step : ∀ field column value state next, first field column value state = some next →
      second field column value state = some next)
    {widths : Array Nat} {shape : List RecursiveSchema.Repeated.Field} {row : Row} {column : Nat} {initial result : State}
    (success : fields first widths shape row column initial = some result) :
    fields second widths shape row column initial = some result := by
  induction shape generalizing row column initial with
  | nil =>
    cases row with
    | nil => exact success
    | cons _ _ => simp [fields] at success
  | cons field tail ih =>
    cases row with
    | nil => simp [fields] at success
    | cons value rest =>
      cases reached : first field column value initial with
      | none => simp [fields, reached, bind, Option.bind] at success
      | some next =>
        simpa [fields, step _ _ _ _ _ reached, bind, Option.bind] using
          ih (by simpa [fields, reached, bind, Option.bind] using success)

private theorem cell_more {State : Type} (push : Push State) (widths : Array Nat) {depth larger : Nat}
    (bound : depth ≤ larger) {levels : Levels} {field : RecursiveSchema.Repeated.Field} {column : Nat} {value : Cell}
    {initial result : State} (success : cell push widths depth levels field column value initial = some result) :
    cell push widths larger levels field column value initial = some result := by
  induction depth generalizing larger levels field column value initial result with
  | zero => simp [cell] at success
  | succ depth ih =>
    cases larger with
    | zero => omega
    | succ larger =>
      have inside := Nat.le_of_succ_le_succ bound
      cases field with
      | leaf plan => simpa only [cell] using success
      | group site children =>
        cases value with
        | none => simpa only [cell] using success
        | some value =>
          cases value <;> simp only [cell] at success ⊢
          any_goals contradiction
          exact fields_agree (fun _ _ _ _ _ read => ih inside read) success
      | list site wrapper element =>
        cases value with
        | none => simpa only [cell] using success
        | some value =>
          cases value <;> simp only [cell] at success ⊢
          any_goals contradiction
          rename_i values
          cases values with
          | nil => exact success
          | cons first tail =>
            let levelsInside : Levels := ⟨levels.definition + site.nullable.toNat + 1,
              levels.repetition, levels.depth + 1⟩
            let later := { levelsInside with repetition := levelsInside.depth }
            change (cell push widths depth levelsInside element column first initial).bind (fun next =>
              tail.foldlM (fun s item => cell push widths depth later element column item s) next) =
              some result at success
            change (cell push widths larger levelsInside element column first initial).bind (fun next =>
              tail.foldlM (fun s item => cell push widths larger later element column item s) next) =
              some result
            cases head : cell push widths depth levelsInside element column first initial with
            | none => simp [head, Option.bind] at success
            | some next =>
              simp only [head, Option.bind] at success
              simpa only [ih inside head, Option.bind] using
                foldlM_agrees (fun _ _ _ read => ih inside read) success

private theorem trace_more {widths : Array Nat} {count depth larger : Nat} (bound : depth ≤ larger)
    {schema : List RecursiveSchema.Repeated.Field} {rows : List Row} {result : Traces}
    (success : trace widths count depth schema rows = some result) :
    trace widths count larger schema rows = some result := by
  unfold trace fold at success ⊢
  cases reached : rows.foldlM (fun columns row => fields (cell emit widths depth {}) widths schema row 0 columns)
      (Array.replicate count []) with
  | none => simp [reached, bind, Option.bind] at success
  | some reversed =>
    have more := foldlM_agrees (fun _ _ _ => fields_agree (fun _ _ _ _ _ read => cell_more emit widths bound read)) reached
    simpa only [more, bind, Option.bind] using
      (by simpa only [reached, bind, Option.bind] using success : pure (reversed.map List.reverse) = some result)

public theorem signed_traces_eq {ll rl : Snapshot.Limits} {ls rs : Snapshot.Checked}
    {left : Compiled ll ls} {right : Compiled rl rs} {lr rr : Rows.Limits} {ordinal : Nat}
    {before : Rows.GroupResult left lr ordinal} {after : Rows.GroupResult right rr ordinal}
    (readL : Rows.readGroupChecked left lr ordinal = .ok before)
    (readR : Rows.readGroupChecked right rr ordinal = .ok after)
    (schema : left.arrow = right.arrow) (observed : before.observation = after.observation) :
    before.inputs.map (·.original.atoms) = after.inputs.map (·.original.atoms) := by
  have sameFields := compiled_fields schema
  have decls : left.declarations = right.declarations := by rw [left.preorder, right.preorder, sameFields]
  have leaves : left.leaves = right.leaves := by rw [left.ordered, right.ordered, decls]
  have widths : Rows.schemaWidths left = Rows.schemaWidths right := by simp [Rows.schemaWidths, decls, leaves]
  have countL : before.inputs.length = left.leaves.size := by
    simpa using congrArg List.length (Rows.GroupResult.order readL)
  have countR : after.inputs.length = right.leaves.size := by
    simpa using congrArg List.length (Rows.GroupResult.order readR)
  have first := trace_more (Nat.le_max_left ll.maxSchemaDepth rl.maxSchemaDepth) (Rows.project_exact before)
  have last := trace_more (Nat.le_max_right ll.maxSchemaDepth rl.maxSchemaDepth) (Rows.project_exact after)
  rw [sameFields, widths, countL, leaves, observed] at first
  rw [countR] at last
  exact List.toArray_inj (Option.some.inj (first.symm.trans last))

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip
