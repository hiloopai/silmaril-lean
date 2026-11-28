module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats.Parquet.RecursiveSchema.ListPath
open Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk

public theorem step_wire {plan : Plan} {wrappers : List Nat} {ceiling : Nat} {start stop : State}
    {rep defn : Nat} (accepted : step plan wrappers ceiling start rep defn = .ok stop) :
    StepWire plan wrappers ceiling start rep defn stop := by
  by_cases repOver : rep > plan.shape.repetitions
  · simp [step, repOver] at accepted
  by_cases defOver : defn > plan.shape.definitions
  · simp [step, repOver, defOver] at accepted
  by_cases closed : rep > start.live
  · simp [step, repOver, defOver, closed] at accepted
  by_cases short : rep > reached wrappers defn
  · simp [step, repOver, defOver, closed, short] at accepted
  by_cases rowOver : (start.advance rep (reached wrappers defn)).rows > ceiling
  · simp [step, repOver, defOver, closed, short, rowOver] at accepted
  have exact : start.advance rep (reached wrappers defn) = stop := by
    simpa [step, repOver, defOver, closed, short, rowOver] using accepted
  exact ⟨Nat.le_of_not_gt repOver, Nat.le_of_not_gt defOver, Nat.le_of_not_gt closed,
    Nat.le_of_not_gt short, exact.symm, exact ▸ Nat.le_of_not_gt rowOver⟩

public theorem scan_wire {plan : Plan} {wrappers : List Nat} {ceiling : Nat} {start stop : State}
    {levels : List (Nat × Nat)} (accepted : scan plan wrappers ceiling levels start = .ok stop) :
    ScanWire plan wrappers ceiling start levels stop := by
  induction levels generalizing start with
  | nil => cases Except.ok.inj accepted; exact .nil _
  | cons level rest ih =>
    rcases level with ⟨rep, defn⟩
    cases advanced : step plan wrappers ceiling start rep defn with
    | error cause => simp [scan, advanced, Bind.bind, Except.bind] at accepted
    | ok middle =>
      exact .cons (step_wire advanced) (ih (by simpa [scan, advanced, Bind.bind, Except.bind] using accepted))

public theorem scan_counts {plan : Plan} {wrappers : List Nat} {ceiling : Nat} {start stop : State}
    {levels : List (Nat × Nat)} (wire : ScanWire plan wrappers ceiling start levels stop) :
    start.slots + levels.length = stop.slots ∧
    start.rows + levels.countP (fun level => level.1 == 0) = stop.rows := by
  induction wire with
  | nil => simp
  | @cons start middle stop rep defn rest current _ ih =>
    have slots : middle.slots = start.slots + 1 := congrArg State.slots current.after
    have rows : middle.rows = start.rows + (rep == 0).toNat := congrArg State.rows current.after
    simp only [List.length_cons]
    rw [List.countP_cons]
    cases h : (rep == 0) <;> simp [h] at rows ⊢ <;> omega

public theorem atoms_axes {levels : List (Nat × Nat)}
    {aligned : List (Option Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Word)}
    (length : aligned.length = levels.length) :
    (atoms levels aligned).map (fun atom => (atom.repetition, atom.definition)) = levels ∧
    (atoms levels aligned).map Rows.Atom.word = aligned := by
  induction levels generalizing aligned with
  | nil => simp_all [atoms]
  | cons first rest ih =>
    cases aligned with
    | nil => simp at length
    | cons value more =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at length
      obtain ⟨axis, words⟩ := ih length
      rcases first with ⟨rep, defn⟩
      exact ⟨by simpa [atoms] using axis, by simpa [atoms] using words⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
