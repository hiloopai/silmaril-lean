module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows

open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct (Plan)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Cell CellFits Row RowFits)

private theorem pairMap_all {α β γ : Type} {f : α → β → Option γ}
    {p : α → Prop} {q : β → Prop} {r : γ → Prop}
    (combine : ∀ {a b c}, f a b = some c → p a → q b → r c)
    {lhs : List α} {rhs : List β} {out : List γ}
    (read : pairMap f lhs rhs = some out)
    (left : ∀ a ∈ lhs, p a) (right : ∀ b ∈ rhs, q b) : ∀ c ∈ out, r c := by
  induction lhs generalizing rhs out with
  | nil => cases rhs <;> simp_all [pairMap, Pure.pure]
  | cons a as ih =>
    cases rhs with
    | nil => simp [pairMap] at read
    | cons b bs =>
      unfold pairMap at read
      split at read
      · rename_i equal
        rw [List.zipWithM_cons_cons] at read
        cases head : f a b with
        | none => simp [head, Bind.bind, Option.bind] at read
        | some c =>
          cases tail : List.zipWithM f as bs with
          | none => simp [head, tail, Bind.bind, Option.bind] at read
          | some cs =>
            simp [head, tail, Bind.bind, Option.bind, Pure.pure] at read
            subst out
            intro cell member
            rcases List.mem_cons.mp member with rfl | member
            · exact combine head (left a (by simp)) (right b (by simp))
            · have rest : pairMap f as bs = some cs := by
                simpa [pairMap, Nat.succ.inj equal] using tail
              exact ih rest (fun item mem => left item (List.mem_cons_of_mem a mem))
                (fun item mem => right item (List.mem_cons_of_mem b mem)) cell member
      · contradiction

private theorem fits_replicate {field : Field} {cells : List Cell} :
    RowFits (List.replicate cells.length field) cells ↔ ∀ c ∈ cells, CellFits field c := by
  induction cells with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil
  | cons first rest ih =>
    rw [List.length_cons, List.replicate_succ]
    constructor
    · intro fit c member
      cases fit with
      | cons head tail =>
        rcases List.mem_cons.mp member with rfl | member
        · exact head
        · exact ih.mp tail c member
    · intro fit
      exact .cons (fit first (by simp)) (ih.mpr (fun c member => fit c (List.mem_cons_of_mem first member)))

private def wrap : List (Option String × Bool) → Field → Field
  | [], field => field
  | (name, nullable) :: rest, field => .node name nullable .list [wrap rest field]

private theorem cell_typed {layers : List (Option String × Bool)} {left right : Field}
    {structName : Option String} {lhs rhs out : Cell}
    (merged : mergeCell layers.length lhs rhs = some out)
    (first : CellFits (wrap layers left) lhs) (other : CellFits (wrap layers right) rhs) :
    CellFits (wrap layers (.node structName false .struct [left, right])) out := by
  induction layers generalizing lhs rhs out with
  | nil =>
    cases Option.some.inj merged
    exact .struct (.cons first (.cons other .nil))
  | cons layer rest ih =>
    rcases layer with ⟨name, nullable⟩
    simp only [wrap] at first other ⊢
    cases first with
    | null =>
      cases other with
      | null =>
        cases Option.some.inj merged
        exact .null
      | list => contradiction
    | list leftFits =>
      cases other with
      | null => contradiction
      | list rightFits =>
        simp only [List.length_cons, mergeCell] at merged
        obtain ⟨cells, pairs, rfl⟩ := Option.map_eq_some_iff.mp merged
        apply CellFits.list
        apply fits_replicate.mpr
        exact pairMap_all (f := mergeCell rest.length)
          (p := CellFits (wrap rest left)) (q := CellFits (wrap rest right))
          (fun read a b => ih read a b) pairs (fits_replicate.mp leftFits) (fits_replicate.mp rightFits)

private theorem row_typed {plan : Plan} {lhs rhs out : Row}
    (merged : mergeRow lhs rhs = some out)
    (first : RowFits (plan.path .left).arrow.fields lhs)
    (other : RowFits (plan.path .right).arrow.fields rhs) :
    RowFits plan.arrow.fields out := by
  change RowFits [_] lhs at first
  change RowFits [_] rhs at other
  cases first with
  | cons leftFit firstTail =>
    cases firstTail
    cases other with
    | cons rightFit otherTail =>
      cases otherTail
      simp only [mergeRow] at merged
      obtain ⟨value, cell, rfl⟩ := Option.map_eq_some_iff.mp merged
      let layers := [(some plan.outer.site.name, plan.outer.site.nullable),
        (some plan.inner.site.name, plan.inner.site.nullable)]
      have fit := cell_typed (layers := layers) (structName := some plan.element.name) cell
        (by exact leftFit) (by exact rightFit)
      exact .cons fit .nil

public theorem mergeRows_typed {plan : Plan} {lhs rhs out : List Row}
    (merged : mergeRows lhs rhs = some out)
    (first : ∀ row ∈ lhs, RowFits (plan.path .left).arrow.fields row)
    (other : ∀ row ∈ rhs, RowFits (plan.path .right).arrow.fields row) :
    ∀ row ∈ out, RowFits plan.arrow.fields row :=
  pairMap_all (f := mergeRow) (fun read a b => row_typed (plan := plan) read a b) merged first other

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows
