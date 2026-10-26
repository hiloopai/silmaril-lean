module

public import Silmaril.Numeric.Ieee754

/-!
# IEEE 754 default exception status

This module models the five status flags and the six non-computational flag
operations required by IEEE 754-2019 §5.7.4. `restoreFlags` replaces only the
selected flags, and both test operations query whether any selected flag is
raised. Explicit flag operations do not signal arithmetic exceptions.

An `Environment` carries the binary rounding direction (§4.3) and sticky status
(§7.1). Binary tininess detection (§7.5) is an implementation choice that must
be consistent across operations; `afterRounding` is this model's default.
Default handling accumulates the flags supplied by a `Result`. Determining
which flags an arithmetic operation raises is a separate obligation: this
module does not classify numerical exceptions or implement alternate handling.
In particular, an exactly tiny result does not raise the underflow flag (§7.5).

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

universe u v w

/-- The five IEEE exception classes (IEEE 754-2019 §7). -/
inductive Exception where
  | invalidOperation
  | divisionByZero
  | overflow
  | underflow
  | inexact
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- A status snapshot or a mask selecting any subset of the five exceptions. -/
structure Flags where
  invalidOperation : Bool := false
  divisionByZero : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  inexact : Bool := false
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace Flags

/-- No selected or raised flags. -/
def empty : Flags := {}

/-- All five selected or raised flags. -/
def all : Flags := ⟨true, true, true, true, true⟩

instance : Inhabited Flags := ⟨empty⟩

/-- Query one flag, without changing the status. -/
def contains (flags : Flags) : Exception → Bool
  | .invalidOperation => flags.invalidOperation
  | .divisionByZero => flags.divisionByZero
  | .overflow => flags.overflow
  | .underflow => flags.underflow
  | .inexact => flags.inexact

instance : Membership Exception Flags := ⟨fun flags e => flags.contains e = true⟩

instance (e : Exception) (flags : Flags) : Decidable (e ∈ flags) :=
  inferInstanceAs (Decidable (flags.contains e = true))

/-- Construct a flag set from its five Boolean membership answers. -/
def ofFunction (f : Exception → Bool) : Flags :=
  ⟨f .invalidOperation, f .divisionByZero, f .overflow, f .underflow, f .inexact⟩

/-- Select exactly one exception. -/
def singleton (e : Exception) : Flags := ofFunction (fun other => other == e)

/-- Accumulate status or combine exception masks. -/
def union (a b : Flags) : Flags := ofFunction (fun e => a.contains e || b.contains e)

/-- Keep only the selected flags. -/
def intersect (a mask : Flags) : Flags := ofFunction (fun e => a.contains e && mask.contains e)

/-- Clear selected flags, leaving all unselected flags untouched. -/
def clear (a mask : Flags) : Flags := ofFunction (fun e => a.contains e && !mask.contains e)

/-- Replace selected flags with their saved values; leave unselected flags untouched. -/
def restore (current saved mask : Flags) : Flags :=
  ofFunction (fun e => if mask.contains e then saved.contains e else current.contains e)

/-- Whether any flag in this set is raised. -/
def any (flags : Flags) : Bool :=
  flags.invalidOperation || flags.divisionByZero || flags.overflow || flags.underflow || flags.inexact

/-- Inclusion of flag sets, used to state sticky accumulation and monotonicity. -/
def Subset (a b : Flags) : Prop := ∀ e : Exception, e ∈ a → e ∈ b

@[simp] theorem contains_ofFunction (f : Exception → Bool) (e : Exception) :
    (ofFunction f).contains e = f e := by cases e <;> rfl

@[ext] theorem ext {a b : Flags} (h : ∀ e, a.contains e = b.contains e) : a = b := by
  cases a
  cases b
  have h₁ := h .invalidOperation
  have h₂ := h .divisionByZero
  have h₃ := h .overflow
  have h₄ := h .underflow
  have h₅ := h .inexact
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  cases h₅
  rfl

@[simp] theorem contains_empty (e : Exception) : empty.contains e = false := by cases e <;> rfl
@[simp] theorem contains_all (e : Exception) : all.contains e = true := by cases e <;> rfl
@[simp] theorem contains_singleton (e other : Exception) : (singleton e).contains other = (other == e) :=
  contains_ofFunction _ _
@[simp] theorem contains_union (a b : Flags) (e : Exception) :
    (a.union b).contains e = (a.contains e || b.contains e) := contains_ofFunction _ _
@[simp] theorem contains_intersect (a mask : Flags) (e : Exception) :
    (a.intersect mask).contains e = (a.contains e && mask.contains e) := contains_ofFunction _ _
@[simp] theorem contains_clear (a mask : Flags) (e : Exception) :
    (a.clear mask).contains e = (a.contains e && !mask.contains e) := contains_ofFunction _ _
@[simp] theorem contains_restore (current saved mask : Flags) (e : Exception) :
    (current.restore saved mask).contains e =
      (if mask.contains e then saved.contains e else current.contains e) := contains_ofFunction _ _

@[simp] theorem mem_singleton (e other : Exception) : other ∈ singleton e ↔ other = e := by
  change (singleton e).contains other = true ↔ other = e
  simp

@[simp] theorem mem_union (a b : Flags) (e : Exception) : e ∈ a.union b ↔ e ∈ a ∨ e ∈ b := by
  change (a.union b).contains e = true ↔ a.contains e = true ∨ b.contains e = true
  simp

@[simp] theorem mem_intersect (a mask : Flags) (e : Exception) :
    e ∈ a.intersect mask ↔ e ∈ a ∧ e ∈ mask := by
  change (a.intersect mask).contains e = true ↔ a.contains e = true ∧ mask.contains e = true
  simp

@[simp] theorem mem_clear (a mask : Flags) (e : Exception) :
    e ∈ a.clear mask ↔ e ∈ a ∧ e ∉ mask := by
  change (a.clear mask).contains e = true ↔ a.contains e = true ∧ ¬mask.contains e = true
  simp

@[simp] theorem mem_restore (current saved mask : Flags) (e : Exception) :
    e ∈ current.restore saved mask ↔
      (e ∈ mask ∧ e ∈ saved) ∨ (e ∉ mask ∧ e ∈ current) := by
  change (current.restore saved mask).contains e = true ↔
    (mask.contains e = true ∧ saved.contains e = true) ∨
      (¬mask.contains e = true ∧ current.contains e = true)
  cases hm : mask.contains e <;> simp [hm]

/-- Boolean flag queries coincide with existential membership. -/
theorem any_eq_true (a : Flags) : a.any = true ↔ ∃ e : Exception, e ∈ a := by
  constructor
  · intro h
    simp only [any, Bool.or_eq_true] at h
    rcases h with ⟨⟨⟨h | h⟩ | h⟩ | h⟩ | h
    · exact ⟨.invalidOperation, h⟩
    · exact ⟨.divisionByZero, h⟩
    · exact ⟨.overflow, h⟩
    · exact ⟨.underflow, h⟩
    · exact ⟨.inexact, h⟩
  · rintro ⟨e, h⟩
    cases e <;> simp_all [any, Membership.mem, contains]

@[simp] theorem union_empty (a : Flags) : a.union empty = a := by ext e; simp
@[simp] theorem empty_union (a : Flags) : empty.union a = a := by ext e; simp
@[simp] theorem union_self (a : Flags) : a.union a = a := by ext e; simp

theorem union_comm (a b : Flags) : a.union b = b.union a := by ext e; simp [Bool.or_comm]
theorem union_assoc (a b c : Flags) : (a.union b).union c = a.union (b.union c) := by
  ext e
  simp [Bool.or_assoc]

@[simp] theorem clear_empty (a : Flags) : a.clear empty = a := by ext e; simp
@[simp] theorem clear_all (a : Flags) : a.clear all = empty := by ext e; simp
@[simp] theorem clear_self (a : Flags) : a.clear a = empty := by ext e; simp

theorem clear_union (a first second : Flags) :
    (a.clear first).clear second = a.clear (first.union second) := by
  ext e
  simp [Bool.and_assoc]

@[simp] theorem restore_empty (a saved : Flags) : a.restore saved empty = a := by ext e; simp
@[simp] theorem restore_all (a saved : Flags) : a.restore saved all = saved := by ext e; simp
@[simp] theorem restore_self (a mask : Flags) : a.restore a mask = a := by ext e; simp

theorem restore_union (a saved first second : Flags) :
    (a.restore saved first).restore saved second = a.restore saved (first.union second) := by
  ext e
  cases hf : first.contains e <;> cases hs : second.contains e <;> simp [hf, hs]

/-- Successive restores under the same mask retain the most recent snapshot. -/
theorem restore_overwrite (a first second mask : Flags) :
    (a.restore first mask).restore second mask = a.restore second mask := by
  ext e
  cases hm : mask.contains e <;> simp [hm]

theorem subset_refl (a : Flags) : a.Subset a := fun _ h => h

theorem subset_trans {a b c : Flags} (hab : a.Subset b) (hbc : b.Subset c) : a.Subset c :=
  fun e h => hbc e (hab e h)

theorem subset_union_left (a b : Flags) : a.Subset (a.union b) :=
  fun e h => (mem_union a b e).mpr (Or.inl h)

theorem subset_union_right (a b : Flags) : b.Subset (a.union b) :=
  fun e h => (mem_union a b e).mpr (Or.inr h)

theorem union_mono {a b c d : Flags} (hab : a.Subset b) (hcd : c.Subset d) :
    (a.union c).Subset (b.union d) := by
  intro e h
  rcases (mem_union a c e).mp h with ha | hc
  · exact (mem_union b d e).mpr (Or.inl (hab e ha))
  · exact (mem_union b d e).mpr (Or.inr (hcd e hc))

theorem clear_subset (a mask : Flags) : (a.clear mask).Subset a :=
  fun e h => ((mem_clear a mask e).mp h).1

/-- Clearing a fixed mask preserves inclusion between incoming status sets. -/
theorem clear_mono {a b : Flags} (h : a.Subset b) (mask : Flags) :
    (a.clear mask).Subset (b.clear mask) := by
  intro e he
  rcases (mem_clear a mask e).mp he with ⟨ha, hm⟩
  exact (mem_clear b mask e).mpr ⟨h e ha, hm⟩

end Flags

/-- Permitted binary tininess detection choices (§7.5), fixed consistently for
all arithmetic in a modeled implementation. This choice does not change values. -/
inductive TininessDetection where
  | beforeRounding
  | afterRounding
  deriving DecidableEq, Repr

/-- Default exception-handling state. No traps or alternate handlers are modeled. -/
structure Environment where
  rounding : RoundingMode := .nearestTiesToEven
  tininess : TininessDetection := .afterRounding
  flags : Flags := Flags.empty
  deriving DecidableEq, Repr

namespace Environment

/-- Startup status for a program that inherits no flags (§7.1). -/
def initial : Environment := {}

instance : Inhabited Environment := ⟨initial⟩

/-- Raise a selected set of flags without signaling an arithmetic exception (§5.7.4). -/
def raiseFlags (env : Environment) (mask : Flags) : Environment :=
  { env with flags := env.flags.union mask }

/-- Clear only the selected flags (§5.7.4). -/
def lowerFlags (env : Environment) (mask : Flags) : Environment :=
  { env with flags := env.flags.clear mask }

/-- Whether any selected flag is currently raised (§5.7.4). -/
def testFlags (env : Environment) (mask : Flags) : Bool := (env.flags.intersect mask).any

/-- Snapshot all flags for subsequent testing or masked restoration (§5.7.4). -/
def saveAllFlags (env : Environment) : Flags := env.flags

/-- Restore the selected flags from a snapshot, preserving the others (§5.7.4). -/
def restoreFlags (env : Environment) (saved mask : Flags) : Environment :=
  { env with flags := env.flags.restore saved mask }

/-- Test whether any selected flag in a saved snapshot is raised (§5.7.4). -/
def testSavedFlags (saved mask : Flags) : Bool := (saved.intersect mask).any

@[simp] theorem mem_raiseFlags (env : Environment) (mask : Flags) (e : Exception) :
    e ∈ (env.raiseFlags mask).flags ↔ e ∈ env.flags ∨ e ∈ mask := Flags.mem_union _ _ _

@[simp] theorem mem_lowerFlags (env : Environment) (mask : Flags) (e : Exception) :
    e ∈ (env.lowerFlags mask).flags ↔ e ∈ env.flags ∧ e ∉ mask := Flags.mem_clear _ _ _

@[simp] theorem mem_restoreFlags (env : Environment) (saved mask : Flags) (e : Exception) :
    e ∈ (env.restoreFlags saved mask).flags ↔
      (e ∈ mask ∧ e ∈ saved) ∨ (e ∉ mask ∧ e ∈ env.flags) := Flags.mem_restore _ _ _ _

@[simp] theorem testFlags_eq_true (env : Environment) (mask : Flags) :
    env.testFlags mask = true ↔ ∃ e : Exception, e ∈ env.flags ∧ e ∈ mask := by
  simp only [testFlags, Flags.any_eq_true, Flags.mem_intersect]

@[simp] theorem testSavedFlags_eq_true (saved mask : Flags) :
    testSavedFlags saved mask = true ↔ ∃ e : Exception, e ∈ saved ∧ e ∈ mask := by
  simp only [testSavedFlags, Flags.any_eq_true, Flags.mem_intersect]

@[simp] theorem testSavedFlags_saveAllFlags (env : Environment) (mask : Flags) :
    testSavedFlags env.saveAllFlags mask = env.testFlags mask := rfl

@[simp] theorem restoreFlags_saveAllFlags (env : Environment) (mask : Flags) :
    env.restoreFlags env.saveAllFlags mask = env := by simp [restoreFlags, saveAllFlags]

/-- Saving then restoring every flag recovers a previous flag state, while
preserving the current rounding and tininess attributes. -/
theorem restoreFlags_all (env : Environment) (saved : Flags) :
    env.restoreFlags saved Flags.all = { env with flags := saved } := by
  simp [restoreFlags]

@[simp] theorem raiseFlags_empty (env : Environment) : env.raiseFlags Flags.empty = env := by
  simp [raiseFlags]

@[simp] theorem lowerFlags_empty (env : Environment) : env.lowerFlags Flags.empty = env := by
  simp [lowerFlags]

theorem raiseFlags_union (env : Environment) (first second : Flags) :
    (env.raiseFlags first).raiseFlags second = env.raiseFlags (first.union second) := by
  simp [raiseFlags, Flags.union_assoc]

theorem lowerFlags_union (env : Environment) (first second : Flags) :
    (env.lowerFlags first).lowerFlags second = env.lowerFlags (first.union second) := by
  simp [lowerFlags, Flags.clear_union]

theorem restoreFlags_union (env : Environment) (saved first second : Flags) :
    (env.restoreFlags saved first).restoreFlags saved second =
      env.restoreFlags saved (first.union second) := by
  simp [restoreFlags, Flags.restore_union]

theorem raiseFlags_sticky (env : Environment) (mask : Flags) :
    env.flags.Subset (env.raiseFlags mask).flags := Flags.subset_union_left _ _

@[simp] theorem raiseFlags_rounding (env : Environment) (mask : Flags) :
    (env.raiseFlags mask).rounding = env.rounding := rfl
@[simp] theorem lowerFlags_rounding (env : Environment) (mask : Flags) :
    (env.lowerFlags mask).rounding = env.rounding := rfl
@[simp] theorem restoreFlags_rounding (env : Environment) (saved mask : Flags) :
    (env.restoreFlags saved mask).rounding = env.rounding := rfl
@[simp] theorem raiseFlags_tininess (env : Environment) (mask : Flags) :
    (env.raiseFlags mask).tininess = env.tininess := rfl
@[simp] theorem lowerFlags_tininess (env : Environment) (mask : Flags) :
    (env.lowerFlags mask).tininess = env.tininess := rfl
@[simp] theorem restoreFlags_tininess (env : Environment) (saved mask : Flags) :
    (env.restoreFlags saved mask).tininess = env.tininess := rfl

end Environment

/-- A returned value and the status flags raised by that operation under default
handling. Arithmetic definitions must separately justify their flag contents;
this container does not classify numerical exceptions. -/
structure Result (α : Type u) where
  value : α
  flags : Flags := Flags.empty
  deriving Repr, DecidableEq

namespace Result

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Return a value without raising any flags. -/
def pure (value : α) : Result α := ⟨value, Flags.empty⟩

/-- Change the returned value without changing the operation's status. -/
def map (f : α → β) (result : Result α) : Result β := ⟨f result.value, result.flags⟩

/-- Sequence operations, retaining the flags raised by either one. -/
def bind (result : Result α) (next : α → Result β) : Result β :=
  let following := next result.value
  ⟨following.value, result.flags.union following.flags⟩

@[simp] theorem pure_bind (value : α) (next : α → Result β) :
    (pure value).bind next = next value := by simp [pure, bind]

@[simp] theorem bind_pure (result : Result α) : result.bind pure = result := by simp [bind, pure]

theorem bind_assoc (result : Result α) (next : α → Result β) (last : β → Result γ) :
    (result.bind next).bind last = result.bind (fun value => (next value).bind last) := by
  simp [bind, Flags.union_assoc]

end Result

namespace Environment

variable {α : Type u} {β : Type v}

/-- Commit a result using default sticky flag accumulation (§7.1), returning the
operation's value unchanged. The operation itself has already selected its value. -/
def commit (env : Environment) (result : Result α) : α × Environment :=
  (result.value, env.raiseFlags result.flags)

@[simp] theorem commit_value (env : Environment) (result : Result α) :
    (env.commit result).1 = result.value := rfl

@[simp] theorem commit_flags (env : Environment) (result : Result α) :
    (env.commit result).2.flags = env.flags.union result.flags := rfl

@[simp] theorem commit_rounding (env : Environment) (result : Result α) :
    (env.commit result).2.rounding = env.rounding := rfl

@[simp] theorem commit_tininess (env : Environment) (result : Result α) :
    (env.commit result).2.tininess = env.tininess := rfl

/-- The outgoing status contains exactly the inherited and newly raised flags. -/
@[simp] theorem mem_commit (env : Environment) (result : Result α) (e : Exception) :
    e ∈ (env.commit result).2.flags ↔ e ∈ env.flags ∨ e ∈ result.flags := Flags.mem_union _ _ _

/-- An operation cannot clear flags that were already raised. -/
theorem commit_sticky (env : Environment) (result : Result α) :
    env.flags.Subset (env.commit result).2.flags := Flags.subset_union_left _ _

/-- Every flag raised by an operation is present after commitment. -/
theorem commit_raises (env : Environment) (result : Result α) :
    result.flags.Subset (env.commit result).2.flags := Flags.subset_union_right _ _

/-- Larger incoming status sets give larger outgoing status sets. -/
theorem commit_mono {left right : Environment} (h : left.flags.Subset right.flags)
    (result : Result α) :
    (left.commit result).2.flags.Subset (right.commit result).2.flags :=
  Flags.union_mono h (Flags.subset_refl _)

@[simp] theorem commit_pure (env : Environment) (value : α) :
    env.commit (Result.pure value) = (value, env) := by simp [commit, Result.pure]

/-- Committing a composed result agrees with committing each operation in order. -/
theorem commit_bind (env : Environment) (result : Result α) (next : α → Result β) :
    env.commit (result.bind next) =
      (env.commit result).2.commit (next (env.commit result).1) := by
  simp [commit, Result.bind, raiseFlags, Flags.union_assoc]

end Environment

end Silmaril.Numeric.Ieee754
