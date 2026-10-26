module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q13

/-! # Exercise sheet 4, question 14 (Andersen on a loop)

Source: `cam-optcomp-2025-exercise-sheet-4` in `references.bib`, question 14.


Answer. Andersen's method ignores control flow: the pointer statements are
`q = &r`, `p = q`, `p = *p`, `s = q`, `r = &s`, and the least solution is
`pt(q) = {r}`, `pt(s) = {r}`, `pt(r) = {s}`, `pt(p) = {r, s}`
(`andersen_loop`).

Per program point, the relation is the least solution of the forward
inequations of question 13 (`S4Q13.flowStep`) over the loop's flowgraph
(`Node`, `edges`; the test on line 2 and the prints are no-ops). Writing
`(p, q, r, s)` for the targets of the four variables, the relation on entry
to each node is (`perPoint_isLeast`):

| node | entry relation |
|---|---|
| 1 `q = &r` | all empty |
| 2 loop test, 3 `p = q`, 6 `r = &s`, 8 `print 42` | `({r, s}, {r}, {s}, {r})` |
| 4 `p = *p`, 5 `s = q` | `({r}, {r}, {s}, {r})` |
| 4' `print p` | `({s}, {r}, {s}, {r})` |

So inside the `then` branch `p` points to exactly one location at each point,
unlike the flow-insensitive `pt(p) = {r, s}`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q14

open PointsTo

/-- The pointer statements of the program. -/
def program : List (Stmt String) :=
  [.addr "q" "r", .copy "p" "q", .load "p" "p", .copy "s" "q", .addr "r" "s"]

/-- The least solution for `program`. -/
def ptLoop (a : AVal String) : Set (AVal String) :=
  if a = .var "p" then {.var "r", .var "s"}
  else if a = .var "q" then {.var "r"}
  else if a = .var "s" then {.var "r"}
  else if a = .var "r" then {.var "s"}
  else ∅

theorem ptLoop_mem : ptLoop ∈ solutions program := by
  simp [solutions, program, Stmt.Sat, ptLoop]

/-- The overall points-to relation. -/
theorem andersen_loop :
    andersen program (.var "q") = {.var "r"} ∧ andersen program (.var "s") = {.var "r"} ∧
      andersen program (.var "r") = {.var "s"} ∧
      andersen program (.var "p") = {.var "r", .var "s"} := by
  have low : ∀ pt ∈ solutions program,
      AVal.var "r" ∈ pt (.var "q") ∧ AVal.var "r" ∈ pt (.var "s") ∧
        AVal.var "s" ∈ pt (.var "r") ∧ AVal.var "r" ∈ pt (.var "p") ∧
          AVal.var "s" ∈ pt (.var "p") := by
    intro pt hpt
    have q1 : AVal.var "r" ∈ pt (.var "q") := hpt (.addr "q" "r") (by simp [program])
    have c1 : pt (.var "q") ⊆ pt (.var "p") := hpt (.copy "p" "q") (by simp [program])
    have l1 : ∀ z ∈ pt (.var "p"), pt z ⊆ pt (.var "p") := hpt (.load "p" "p") (by simp [program])
    have c2 : pt (.var "q") ⊆ pt (.var "s") := hpt (.copy "s" "q") (by simp [program])
    have a2 : AVal.var "s" ∈ pt (.var "r") := hpt (.addr "r" "s") (by simp [program])
    exact ⟨q1, c2 q1, a2, c1 q1, l1 _ (c1 q1) a2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact andersen_apply_eq _ ptLoop_mem (by simp [ptLoop]) fun pt hpt =>
      Set.singleton_subset_iff.2 (low pt hpt).1
  · exact andersen_apply_eq _ ptLoop_mem (by simp [ptLoop]) fun pt hpt =>
      Set.singleton_subset_iff.2 (low pt hpt).2.1
  · exact andersen_apply_eq _ ptLoop_mem (by simp [ptLoop]) fun pt hpt =>
      Set.singleton_subset_iff.2 (low pt hpt).2.2.1
  · exact andersen_apply_eq _ ptLoop_mem (by simp [ptLoop]) fun pt hpt =>
      Set.insert_subset_iff.2 ⟨(low pt hpt).2.2.2.1, Set.singleton_subset_iff.2 (low pt hpt).2.2.2.2⟩

/-! ## The points-to relation at each program point -/

/-- Nodes of the loop's flowgraph, numbered by source line; `n4'` is
`print p`. -/
inductive Node
  | n1 | n2 | n3 | n4 | n4' | n5 | n6 | n8
  deriving DecidableEq

/-- The pointer statement at each node (`none` for the test and the prints). -/
def stmt : Node → Option (Stmt String)
  | .n1 => some (.addr "q" "r")
  | .n2 => none
  | .n3 => some (.copy "p" "q")
  | .n4 => some (.load "p" "p")
  | .n4' => none
  | .n5 => some (.copy "s" "q")
  | .n6 => some (.addr "r" "s")
  | .n8 => none

/-- The edges of the flowgraph. -/
def edges : List (Node × Node) :=
  [(.n1, .n2), (.n2, .n3), (.n2, .n8), (.n3, .n4), (.n4, .n4'), (.n4', .n6), (.n3, .n5),
    (.n5, .n6), (.n6, .n2)]

/-- Points-to relations. -/
abbrev PT := AVal String → Set (AVal String)

/-- The transfer function of a node (`S4Q13.flowStep`, identity for no-ops). -/
def transfer (pt : PT) : Option (Stmt String) → PT
  | none => pt
  | some s => S4Q13.flowStep pt s

/-- Solutions of the forward inequations: for each edge `m → n`, the relation
on exit from `m` is contained in the relation on entry to `n`. -/
def Sol (X : Node → PT) : Prop := ∀ e ∈ edges, transfer (X e.1) (stmt e.1) ≤ X e.2

/-- The relation with targets `p`, `q`, `r`, `s` for the four variables. -/
def mk (p q r s : Set (AVal String)) : PT := fun a =>
  if a = .var "p" then p else if a = .var "q" then q else if a = .var "r" then r
  else if a = .var "s" then s else ∅

/-- The relation on entry to each node. -/
def expected : Node → PT
  | .n1 => mk ∅ ∅ ∅ ∅
  | .n2 | .n3 | .n6 | .n8 => mk {.var "r", .var "s"} {.var "r"} {.var "s"} {.var "r"}
  | .n4 | .n5 => mk {.var "r"} {.var "r"} {.var "s"} {.var "r"}
  | .n4' => mk {.var "s"} {.var "r"} {.var "s"} {.var "r"}

section mk

variable {p q r s P : Set (AVal String)}

@[simp] theorem mk_p : mk p q r s (.var "p") = p := by simp [mk]
@[simp] theorem mk_q : mk p q r s (.var "q") = q := by simp [mk]
@[simp] theorem mk_r : mk p q r s (.var "r") = r := by simp [mk]
@[simp] theorem mk_s : mk p q r s (.var "s") = s := by simp [mk]

theorem mk_le_iff {Y : PT} :
    mk p q r s ≤ Y ↔
      p ⊆ Y (.var "p") ∧ q ⊆ Y (.var "q") ∧ r ⊆ Y (.var "r") ∧ s ⊆ Y (.var "s") := by
  constructor
  · intro h
    exact ⟨by simpa using h (.var "p"), by simpa using h (.var "q"),
      by simpa using h (.var "r"), by simpa using h (.var "s")⟩
  · rintro ⟨hp, hq, hr, hs⟩ a
    unfold mk
    split_ifs with h1 h2 h3 h4
    · subst h1; exact hp
    · subst h2; exact hq
    · subst h3; exact hr
    · subst h4; exact hs
    · exact Set.empty_subset _

@[simp] theorem update_mk_p : Function.update (mk p q r s) (.var "p") P = mk P q r s := by
  funext a
  by_cases ha : a = .var "p"
  · subst ha; simp
  · rw [Function.update_of_ne ha]; simp [mk, ha]

@[simp] theorem update_mk_s : Function.update (mk p q r s) (.var "s") P = mk p q r P := by
  funext a
  by_cases ha : a = .var "s"
  · subst ha; simp
  · rw [Function.update_of_ne ha]; simp [mk, ha]

@[simp] theorem update_mk_q : Function.update (mk p q r s) (.var "q") P = mk p P r s := by
  funext a
  by_cases ha : a = .var "q"
  · subst ha; simp
  · rw [Function.update_of_ne ha]; simp [mk, ha]

@[simp] theorem update_mk_r : Function.update (mk p q r s) (.var "r") P = mk p q P s := by
  funext a
  by_cases ha : a = .var "r"
  · subst ha; simp
  · rw [Function.update_of_ne ha]; simp [mk, ha]

end mk

/-- An update below `Y` gives the new value and the unchanged ones. -/
theorem update_le {α β : Type*} [DecidableEq α] {pt Y : α → Set β} {x : α} {S : Set β}
    (h : Function.update pt x S ≤ Y) : S ⊆ Y x ∧ ∀ a, a ≠ x → pt a ⊆ Y a :=
  ⟨by simpa using h x, fun a ha => by simpa [Function.update_of_ne ha] using h a⟩

theorem expected_sol : Sol expected := by
  intro e he
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [transfer, stmt, expected, S4Q13.flowStep, mk_le_iff]

/-- The points-to relation at each program point: `expected` is the least
solution of the forward inequations. -/
theorem perPoint_isLeast : IsLeast {X | Sol X} expected := by
  refine ⟨expected_sol, fun X hX => ?_⟩
  have h12 := hX (.n1, .n2) (by simp [edges])
  have h62 := hX (.n6, .n2) (by simp [edges])
  simp only [transfer, stmt, S4Q13.flowStep] at h12 h62
  have e12 := update_le h12
  have e62 := update_le h62
  have e23 : X .n2 ≤ X .n3 := hX (.n2, .n3) (by simp [edges])
  have e28 : X .n2 ≤ X .n8 := hX (.n2, .n8) (by simp [edges])
  have e34 := update_le (pt := X .n3) (x := .var "p") (S := X .n3 (.var "q")) (Y := X .n4)
    (hX (.n3, .n4) (by simp [edges]))
  have e44 := update_le (pt := X .n4) (x := .var "p")
    (S := ⋃ z ∈ X .n4 (.var "p"), X .n4 z) (Y := X .n4') (hX (.n4, .n4') (by simp [edges]))
  have e46 : X .n4' ≤ X .n6 := hX (.n4', .n6) (by simp [edges])
  have e35 := update_le (pt := X .n3) (x := .var "p") (S := X .n3 (.var "q")) (Y := X .n5)
    (hX (.n3, .n5) (by simp [edges]))
  have e56 := update_le (pt := X .n5) (x := .var "s") (S := X .n5 (.var "q")) (Y := X .n6)
    (hX (.n5, .n6) (by simp [edges]))
  have pq : AVal.var "p" ≠ .var "q" := by simp
  have pr : AVal.var "p" ≠ .var "r" := by simp
  have ps : AVal.var "p" ≠ .var "s" := by simp
  have qr : AVal.var "q" ≠ .var "r" := by simp
  have qs : AVal.var "q" ≠ .var "s" := by simp
  have rs : AVal.var "r" ≠ .var "s" := by simp
  -- the first pass round the loop
  have q2 : AVal.var "r" ∈ X .n2 (.var "q") := e12.1 rfl
  have q3 := e23 _ q2
  have p4 : AVal.var "r" ∈ X .n4 (.var "p") := e34.1 q3
  have q4 : AVal.var "r" ∈ X .n4 (.var "q") := e34.2 _ pq.symm q3
  have p5 : AVal.var "r" ∈ X .n5 (.var "p") := e35.1 q3
  have q5 : AVal.var "r" ∈ X .n5 (.var "q") := e35.2 _ pq.symm q3
  have p6 : AVal.var "r" ∈ X .n6 (.var "p") := e56.2 _ ps p5
  have s6 : AVal.var "r" ∈ X .n6 (.var "s") := e56.1 q5
  have q6 : AVal.var "r" ∈ X .n6 (.var "q") := e56.2 _ qs q5
  -- back to the head
  have p2 : AVal.var "r" ∈ X .n2 (.var "p") := e62.2 _ pr p6
  have s2 : AVal.var "r" ∈ X .n2 (.var "s") := e62.2 _ rs.symm s6
  have r2 : AVal.var "s" ∈ X .n2 (.var "r") := e62.1 rfl
  -- the second pass
  have r3 := e23 _ r2
  have s3 := e23 _ s2
  have r4 : AVal.var "s" ∈ X .n4 (.var "r") := e34.2 _ pr.symm r3
  have s4 : AVal.var "r" ∈ X .n4 (.var "s") := e34.2 _ ps.symm s3
  have r5 : AVal.var "s" ∈ X .n5 (.var "r") := e35.2 _ pr.symm r3
  have s5 : AVal.var "r" ∈ X .n5 (.var "s") := e35.2 _ ps.symm s3
  have p4' : AVal.var "s" ∈ X .n4' (.var "p") := e44.1 (Set.mem_biUnion p4 r4)
  have q4' : AVal.var "r" ∈ X .n4' (.var "q") := e44.2 _ pq.symm q4
  have r4' : AVal.var "s" ∈ X .n4' (.var "r") := e44.2 _ pr.symm r4
  have s4' : AVal.var "r" ∈ X .n4' (.var "s") := e44.2 _ ps.symm s4
  have p6' : AVal.var "s" ∈ X .n6 (.var "p") := e46 _ p4'
  have r6 : AVal.var "s" ∈ X .n6 (.var "r") := e56.2 _ rs r5
  have p2' : AVal.var "s" ∈ X .n2 (.var "p") := e62.2 _ pr p6'
  intro n
  cases n <;> simp only [expected, mk_le_iff, Set.empty_subset, Set.insert_subset_iff,
    Set.singleton_subset_iff, and_true, and_assoc]
  · exact ⟨p2, p2', q2, r2, s2⟩
  · exact ⟨e23 _ p2, e23 _ p2', q3, r3, s3⟩
  · exact ⟨p4, q4, r4, s4⟩
  · exact ⟨p4', q4', r4', s4'⟩
  · exact ⟨p5, q5, r5, s5⟩
  · exact ⟨p6, p6', q6, r6, s6⟩
  · exact ⟨e28 _ p2, e28 _ p2', e28 _ q2, e28 _ r2, e28 _ s2⟩

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q14
