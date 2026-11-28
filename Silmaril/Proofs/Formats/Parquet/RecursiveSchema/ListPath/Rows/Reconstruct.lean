module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.Projection

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows

open Silmaril.Formats.Parquet.RecursiveSchema.ListPath
open Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation Row)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error => contradiction
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem assembleRows_count {plan : Plan} {slices : List (List Atom)} {start : Nat} {rows : List Row}
    (accepted : assembleRows plan slices start = .ok rows) :
    rows.length = slices.length := by
  induction slices generalizing start rows with
  | nil => cases Except.ok.inj accepted; rfl
  | cons first rest ih =>
    simp only [assembleRows, List.zipIdx_cons, List.mapM_cons] at accepted
    obtain ⟨_, _, tailAccepted⟩ := bind_ok accepted
    obtain ⟨tail, tailRead, done⟩ := bind_ok tailAccepted
    cases Except.ok.inj done
    simp [ih tailRead]

private theorem assembleRows_exact {plan : Plan} {slices : List (List Atom)} {start : Nat} {rows : List Row}
    (inverse : slices.mapM (fun segment => (assemble plan.shape 0 0 segment).map (· :: [])) = some rows) :
    assembleRows plan slices start = .ok rows := by
  induction slices generalizing start rows with
  | nil => cases Option.some.inj inverse; rfl
  | cons first rest ih =>
    simp only [List.mapM_cons] at inverse
    cases head : assemble plan.shape 0 0 first with
    | none => simp [head, bind, Option.bind] at inverse
    | some value =>
      cases tail : rest.mapM (fun segment => (assemble plan.shape 0 0 segment).map (· :: [])) with
      | none => simp [head, tail, bind, Option.bind] at inverse
      | some remainder =>
        simp [head, tail, bind, Option.bind, pure] at inverse
        subst rows
        have next := ih (start := start + 1) tail
        simp only [assembleRows, List.zipIdx_cons, List.mapM_cons] at next ⊢
        rw [head, next]
        rfl

public theorem reconstruct_wire {limits : Limits} {plan : Plan} {expected : Nat}
    {input : List Atom} {out : Observation}
    (accepted : reconstruct limits plan expected input = .ok out) :
    ObservationWire limits plan input expected out := by
  by_cases overRows : expected > limits.maxRows
  · simp [reconstruct, overRows, bind, Except.bind] at accepted
  by_cases overSlots : input.length > limits.maxSlots
  · simp [reconstruct, overRows, overSlots, bind, Except.bind] at accepted
  by_cases count : (split 0 input).length = expected
  · have admitted : (assembleRows plan (split 0 input) >>= fun rows =>
        if Relation plan input rows then .ok ⟨expected, rows⟩ else throw .traceMismatch) =
          .ok out := by
      simpa [reconstruct, overRows, overSlots, count, bind, Except.bind, pure, Except.pure] using accepted
    obtain ⟨rows, assembled, checked⟩ := bind_ok admitted
    split at checked
    · rename_i relation
      cases Except.ok.inj checked
      exact ⟨Nat.le_of_not_gt overRows, Nat.le_of_not_gt overSlots, relation,
        (assembleRows_count assembled).trans count, rfl,
        (relation_sound relation).1, (relation_sound relation).2⟩
    · contradiction
  · simp [reconstruct, overRows, overSlots, count, bind, Except.bind] at accepted

public theorem reconstruct_of_relation {limits : Limits} {plan : Plan} {input : List Atom} {rows : List Row}
    (original : Relation plan input rows) (budgetRows : rows.length ≤ limits.maxRows)
    (budgetSlots : input.length ≤ limits.maxSlots) :
    reconstruct limits plan rows.length input = .ok ⟨rows.length, rows⟩ := by
  obtain ⟨count, inverse⟩ := relation_segments original
  have exactRows := assembleRows_exact (start := 0) inverse
  simp [reconstruct, Nat.not_lt.mpr budgetRows, Nat.not_lt.mpr budgetSlots,
    count, exactRows, original, bind, Except.bind, pure, Except.pure]

public theorem project_wire {limits : Limits} {plan : Plan} {rows : List Row} {input : List Atom}
    (accepted : project limits plan rows = .ok input) :
    Relation plan input rows ∧ rows.length ≤ limits.maxRows ∧ input.length ≤ limits.maxSlots := by
  by_cases overRows : rows.length > limits.maxRows
  · simp [project, overRows, bind, Except.bind] at accepted
  by_cases overSlots : slotDemand plan rows > limits.maxSlots
  · simp [project, overRows, overSlots, bind, Except.bind] at accepted
  cases projected : Projection.trace plan rows with
  | none => simp [project, overRows, overSlots, projected] at accepted
  | some found =>
    have same : found = input := by simpa [project, overRows, overSlots, projected, pure, Except.pure] using accepted
    subst input
    exact ⟨projected, Nat.le_of_not_gt overRows, relation_demand projected ▸ Nat.le_of_not_gt overSlots⟩

public theorem project_of_relation {limits : Limits} {plan : Plan} {input : List Atom} {rows : List Row}
    (original : Relation plan input rows) (budgetRows : rows.length ≤ limits.maxRows)
    (budgetSlots : input.length ≤ limits.maxSlots) :
    project limits plan rows = .ok input := by
  have bounded : slotDemand plan rows ≤ limits.maxSlots := relation_demand original ▸ budgetSlots
  simp [project, Nat.not_lt.mpr budgetRows, Nat.not_lt.mpr bounded, show Projection.trace plan rows = some input from original,
    pure, Except.pure]

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows
