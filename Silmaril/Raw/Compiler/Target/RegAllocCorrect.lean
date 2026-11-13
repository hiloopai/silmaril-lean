module

public import Silmaril.Compiler.Target.RegAlloc.Defs
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
/-! # Local proof obligations for a register-renaming validator

The existing spill simulation relates every defined register and requires a globally
injective allocation. A sharing renamer instead needs a relation indexed by the
registers live at the current point. These lemmas establish the local write and
elided-move obligations without assuming global injectivity.

This is not a validator or a correctness proof for `renumber`. The remaining
obligations are checked live-set transfer across instructions and CFG edges,
parameter/result writes, suspended callers, and a decreasing source measure when
`renameInstr` removes a self-move. The intended final theorem is a strict refinement
of `Lir.sem` from start states of the same function, arguments and memory, with the
identity observation (including returned memory, trapped memory and divergence).
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine

/-- Defined live source registers have their values at their renamed homes; slots
are unchanged. Undefined source registers impose no obligation. -/
structure LiveFrameRel (σ : Nat → Nat) (live : Nat → Prop)
    (fs ft : Lir.Frame Nat) : Prop where
  regs : ∀ r, live r → ∀ x, fs.get r = some x → ft.get (σ r) = some x
  slots : ∀ n x, fs.slots n = some x → ft.slots n = some x

/-- A write may not clobber the home of a different live register. This applies
even when the destination itself is dead after the instruction. -/
def WriteSafe (σ : Nat → Nat) (dest : Nat) (live : Nat → Prop) : Prop :=
  ∀ r, live r → σ r = σ dest → r = dest

/-- Check the interference obligation for one write against a finite live set.
This is only a component of a validator; it does not check a whole program. -/
def checkWrite (σ : Nat → Nat) (dest : Nat) (live : List Nat) : Bool :=
  live.all fun r => σ r != σ dest || r == dest

theorem checkWrite_sound {σ : Nat → Nat} {dest : Nat} {live : List Nat}
    (h : checkWrite σ dest live = true) : WriteSafe σ dest (fun r => r ∈ live) := by
  intro r hr he
  have hc := List.all_eq_true.mp h r hr
  simpa [he] using hc

theorem LiveFrameRel.mono {σ : Nat → Nat} {before after : Nat → Prop}
    {fs ft : Lir.Frame Nat} (h : LiveFrameRel σ before fs ft)
    (sub : ∀ r, after r → before r) : LiveFrameRel σ after fs ft :=
  ⟨fun r hr => h.regs r (sub r hr), h.slots⟩

theorem LiveFrameRel.empty (σ : Nat → Nat) (live : Nat → Prop) :
    LiveFrameRel σ live Lir.Frame.empty Lir.Frame.empty := by
  constructor
  · intro r _ x hx
    cases hx
  · intro n x hx
    cases hx

/-- The backward transfer for a register write removes its destination from the
required old values. Interference is checked against every live value afterwards. -/
theorem LiveFrameRel.set {σ : Nat → Nat} {live : Nat → Prop}
    {fs ft : Lir.Frame Nat} {d : Nat} (x : Lir.Word)
    (h : LiveFrameRel σ (fun r => r ≠ d ∧ live r) fs ft)
    (safe : WriteSafe σ d live) :
    LiveFrameRel σ live (fs.set d x) (ft.set (σ d) x) := by
  constructor
  · intro r hr y hy
    by_cases hd : r = d
    · subst r
      simpa [Lir.Frame.get_set] using hy
    · have ht : σ r ≠ σ d := fun he => hd (safe r hr he)
      simp only [Lir.Frame.get_set, hd, ht, ite_false] at hy ⊢
      exact h.regs r ⟨hd, hr⟩ y hy
  · exact h.slots

/-- Stack slots keep their own namespace under renaming. -/
theorem LiveFrameRel.setSlot {σ : Nat → Nat} {live : Nat → Prop}
    {fs ft : Lir.Frame Nat} (h : LiveFrameRel σ live fs ft) (n : Nat) (x : Lir.Word) :
    LiveFrameRel σ live (fs.setSlot n x) (ft.setSlot n x) := by
  constructor
  · exact h.regs
  · intro m y hy
    by_cases hm : m = n
    · subst m
      simpa using hy
    · simp only [Lir.Frame.slots_setSlot, hm, ite_false] at hy ⊢
      exact h.slots m y hy

/-- A self-move in the renamed program can be elided: its source value is
already in the destination home. This proves only the frame obligation; the
whole-program simulation must also map instruction indices and bound stuttering. -/
theorem LiveFrameRel.elideMove {σ : Nat → Nat} {live : Nat → Prop}
    {fs ft : Lir.Frame Nat} {d s : Nat} {x : Lir.Word}
    (h : LiveFrameRel σ (fun r => r = s ∨ (r ≠ d ∧ live r)) fs ft)
    (same : σ d = σ s) (read : fs.get s = some x) :
    LiveFrameRel σ live (fs.set d x) ft := by
  constructor
  · intro r hr y hy
    by_cases hd : r = d
    · subst r
      have hxy : x = y := by simpa using hy
      subst y
      rw [same]
      exact h.regs s (Or.inl rfl) x read
    · simp only [Lir.Frame.get_set, hd, ite_false] at hy
      exact h.regs r (Or.inr ⟨hd, hr⟩) y hy
  · exact h.slots

/-- Required old register values before one location is written. Slots have no
register kills. -/
def beforeWrite (loc : Lir.Loc Nat) (live : Nat → Prop) : Nat → Prop :=
  match loc with
  | .reg d => fun r => r ≠ d ∧ live r
  | .slot _ => live

/-- Required old register values before a left-to-right list of writes. This
matches `Frame.writeAll`, including repeated locations and argument order. -/
def beforeWrites : List (Lir.Loc Nat) → (Nat → Prop) → Nat → Prop
  | [], live => live
  | l :: ls, live => beforeWrite l (beforeWrites ls live)

/-- Each write is checked against the values needed by the remaining writes.
In particular a later dead parameter must not clobber an earlier live one. -/
def WritesSafe (σ : Nat → Nat) : List (Lir.Loc Nat) → (Nat → Prop) → Prop
  | [], _ => True
  | .reg d :: ls, live => WriteSafe σ d (beforeWrites ls live) ∧ WritesSafe σ ls live
  | .slot _ :: ls, live => WritesSafe σ ls live

theorem LiveFrameRel.write {σ : Nat → Nat} {live : Nat → Prop}
    {fs ft : Lir.Frame Nat} (l : Lir.Loc Nat) (x : Lir.Word)
    (h : LiveFrameRel σ (beforeWrite l live) fs ft)
    (safe : ∀ d, l = .reg d → WriteSafe σ d live) :
    LiveFrameRel σ live (fs.write l x) (ft.write (renameLoc σ l) x) := by
  cases l with
  | reg d => exact h.set x (safe d rfl)
  | slot n => exact h.setSlot n x

/-- Live-frame preservation for parameter binding and returned results, with
the same sequential overwrite semantics as Lir, rather than parallel moves. -/
theorem LiveFrameRel.writeAll {σ : Nat → Nat} {live : Nat → Prop} :
    ∀ {ls : List (Lir.Loc Nat)} {xs : List Lir.Word} {fs fs' ft : Lir.Frame Nat},
      LiveFrameRel σ (beforeWrites ls live) fs ft → WritesSafe σ ls live →
      fs.writeAll ls xs = some fs' →
      ∃ ft', ft.writeAll (ls.map (renameLoc σ)) xs = some ft' ∧ LiveFrameRel σ live fs' ft'
  | [], [], _, _, ft, h, _, he => by
    cases he
    exact ⟨ft, rfl, h⟩
  | [], _ :: _, _, _, _, _, _, he => by cases he
  | _ :: _, [], _, _, _, _, _, he => by cases he
  | l :: ls, x :: xs, fs, fs', ft, h, safe, he => by
    have hs : ∀ d, l = .reg d → WriteSafe σ d (beforeWrites ls live) := by
      intro d hd
      subst l
      exact safe.1
    have ht : WritesSafe σ ls live := by
      cases l <;> simp only [WritesSafe] at safe <;> tauto
    obtain ⟨ft', he', hr⟩ := LiveFrameRel.writeAll (h.write l x hs) ht he
    exact ⟨ft', by simpa only [List.map_cons, Lir.Frame.writeAll] using he', hr⟩

/-! ## Counterexamples to incomplete validator conditions

These invalid candidate renamings are not bugs claimed in `renumber`. A full
checker must reject them. The source executions are defined and the changed
returned values are proved by kernel reduction.
-/

namespace RegAllocValidatorExamples

private def mem : Lir.Memory := .ofList 0 []

-- Only register 0 is live after either instruction. Injectivity restricted to
-- live sets is therefore insufficient: the dead write to 1 clobbers its home.
private def deadWrite : Lir.Func Nat :=
  ⟨[], 0, [⟨[.op (.const 0 7), .op (.const 1 9)], .ret [.reg 0]⟩]⟩

example : (Lir.Prog.runMain ⟨[deadWrite]⟩ 4 0 [] mem).returnedValues? = some [7] := by
  decide

example : (Lir.Prog.runMain ⟨[renameFunc (fun _ => 0) deadWrite]⟩ 4 0 [] mem).returnedValues? =
    some [9] := by
  decide

example : ¬ WriteSafe (fun _ => 0) 1 (fun r => r = 0) := by
  intro h
  have := h 0 rfl rfl
  omega

example : checkWrite (fun _ => 0) 1 [0] = false := by decide

-- Reusing the home for a destination read before it is overwritten is allowed:
-- only the destination is live afterwards, even if its old source had that home.
example : checkWrite (fun _ => 0) 1 [1] = true := by decide

-- A dead parameter is still written by `enter`. Checking only body instructions
-- and live-in values misses the second argument overwriting the first one's home.
private def deadParam : Lir.Func Nat :=
  ⟨[.reg 0, .reg 1], 0, [⟨[], .ret [.reg 0]⟩]⟩

example : (Lir.Prog.runMain ⟨[deadParam]⟩ 2 0 [7, 9] mem).returnedValues? = some [7] := by
  decide

example : (Lir.Prog.runMain ⟨[renameFunc (fun _ => 0) deadParam]⟩ 2 0 [7, 9] mem).returnedValues? =
    some [9] := by
  decide

end RegAllocValidatorExamples

end Silmaril.Compile.Target.RegAlloc
