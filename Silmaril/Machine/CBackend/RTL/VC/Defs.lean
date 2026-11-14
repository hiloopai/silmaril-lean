module

public import Silmaril.Machine.CBackend.RTL.Semantics.Defs
public import Silmaril.Raw.Machine.CBackend.RTL.VC.Wp
/-!
# A cut-point VC generator for RTL, sound for total correctness

The separate RTL stage of the imported program-VC work. The
target is Silmaril's RTL (`Silmaril/Machine/RTL/Semantics.lean`, unchanged): a
control-flow graph over pseudo-registers with Lir's 64-bit operators, where reading an
unwritten register, dividing by zero and similar faults are *stuck*.

A function is annotated Floyd-style: a list of **cut points** (loop heads), each with the
registers that are written there (`defined`), an invariant over their values and the
memory, and a 64-bit measure. `wpN` executes the CFG symbolically from a node until it
reaches a cut point or a `ret`, along every branch of `cond`; reaching a cut point
requires its invariant and, except on the path from the entry, a strictly smaller
(unsigned) measure. `vc` asks this from the entry (under the precondition) and from every
cut point (under its invariant), with the registers outside `defined` unwritten
(`canon`), so a VC never depends on stale registers.

`sound`: if `vc` holds, the function, entered with its parameters written and the
precondition true, **returns** (no stuck state, no trap, no divergence) with values and
memory satisfying the postcondition, in the RTL semantics (`Behaves … (.returned vs m)`).
Calls are not supported (a `call` node makes the VC false).
-/

@[expose] public section
namespace Silmaril.Machine.CBackend.RTL.VC

open Silmaril.Machine.RTL
open Silmaril.Machine.Lir (Word Memory)

/-! ## Frames -/

/-- `g` has every value of `f`. -/
def FLe (f g : Frame Nat) : Prop := ∀ r v, f.get r = some v → g.get r = some v

theorem FLe.refl (f : Frame Nat) : FLe f f := fun _ _ h => h

theorem FLe.set {f g : Frame Nat} (h : FLe f g) (d : Nat) (w : Word) : FLe (f.set d w) (g.set d w) := by
  intro r v hr
  simp only [Frame.get_set] at hr ⊢
  by_cases h' : r = d
  · simp only [h', ite_true] at hr ⊢; exact hr
  · simp only [h', ite_false] at hr ⊢; exact h r v hr

theorem FLe.readAll {f g : Frame Nat} (h : FLe f g) :
    ∀ (rs : List Nat) (vs : List Word), f.readAll rs = some vs → g.readAll rs = some vs := by
  intro rs
  induction rs with
  | nil => intro vs hv; simpa [Frame.readAll] using hv
  | cons r rs ih =>
    intro vs hv
    simp only [Frame.readAll, List.mapM_cons] at hv ⊢
    cases hr : f.get r with
    | none => simp [hr] at hv
    | some x =>
      cases hrs : rs.mapM f.get with
      | none => simp [hr, hrs] at hv
      | some ys =>
        simp only [hr, hrs] at hv
        have := ih ys (by simpa [Frame.readAll] using hrs)
        simp only [Frame.readAll] at this
        simp [h r x hr, this]
        simpa using hv

/-- The values of the registers `ds` (and `0` elsewhere). -/
def valsOn (ds : List Nat) (fr : Frame Nat) : Nat → Word :=
  fun r => if r ∈ ds then (fr.get r).getD 0 else 0

/-- The frame in which exactly the registers `ds` are written, with values `v`. -/
def canon (ds : List Nat) (v : Nat → Word) : Frame Nat :=
  ⟨fun r => if r ∈ ds then some (v r) else none⟩

@[simp] theorem canon_get (ds : List Nat) (v : Nat → Word) (r : Nat) :
    (canon ds v).get r = if r ∈ ds then some (v r) else none := rfl

theorem valsOn_eq {ds : List Nat} {f g : Frame Nat} (hd : ∀ r ∈ ds, (f.get r).isSome) (h : FLe f g) :
    valsOn ds f = valsOn ds g := by
  funext r
  simp only [valsOn]
  split
  · rename_i hr
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hd r hr)
    rw [hx, h r x hx]
  · rfl

theorem canon_le {ds : List Nat} {fr : Frame Nat} (hd : ∀ r ∈ ds, (fr.get r).isSome) :
    FLe (canon ds (valsOn ds fr)) fr := by
  intro r v hr
  simp only [canon_get] at hr
  split at hr
  · rename_i hm
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hd r hm)
    simp only [Option.some.injEq] at hr
    subst hr
    simp [valsOn, hm, hx]
  · simp at hr

/-! ## Annotations and the VC generator -/

/-- A cut point's annotation. -/
structure Cut where
  defined : List Nat
  inv : (Nat → Word) → Memory → Prop
  measure : (Nat → Word) → Memory → Word

/-- A frame and memory satisfy a cut point's annotation. -/
def Cut.holds (c : Cut) (fr : Frame Nat) (m : Memory) : Prop :=
  (∀ r ∈ c.defined, (fr.get r).isSome) ∧ c.inv (valsOn c.defined fr) m

theorem Cut.holds_mono {c : Cut} {f g : Frame Nat} {m : Memory} (h : c.holds f m) (hle : FLe f g) :
    c.holds g m := by
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h.1 r hr)
    simp [hle r x hx]
  · rw [← valsOn_eq h.1 hle]; exact h.2

/-- The measure bound on reaching a cut point: none from the entry. -/
def bound (μ : Option Word) (w : Word) : Prop :=
  match μ with
  | some μ => w < μ
  | none => True

/-- The one-function program of `fn`. -/
def prog (fn : Func Nat) : Prog Nat := ⟨[fn]⟩

section

variable (fn : Func Nat) (cuts : List (Node × Cut)) (post : List Word → Memory → Prop)

/-- Reaching node `n'` with frame `fr'` and memory `m'`: the cut point's annotation and
measure bound, or else the continuation `cont` (the paths onward from `n'`). -/
def nextP (μ : Option Word) (cont : Node → Frame Nat → Memory → Prop) (n' : Node) (fr' : Frame Nat)
    (m' : Memory) : Prop :=
  match cuts.lookup n' with
  | some c => c.holds fr' m' ∧ bound μ (c.measure (valsOn c.defined fr') m')
  | none => cont n' fr' m'

/-- The weakest precondition of one instruction, given what reaching its successors needs. -/
def wpI (next : Node → Frame Nat → Memory → Prop) : Option (Instr Nat) → Frame Nat → Memory → Prop
  | some (.nop n'), fr, m => next n' fr m
  | some (.const d v n'), fr, m => next n' (fr.set d v) m
  | some (.move d s n'), fr, m =>
    match fr.get s with
    | some x => next n' (fr.set d x) m
    | none => False
  | some (.unary op d s n'), fr, m =>
    match fr.get s with
    | some x => next n' (fr.set d (op.eval x)) m
    | none => False
  | some (.binary op d a b n'), fr, m =>
    match fr.get a, fr.get b with
    | some x, some y =>
      match op.eval x y with
      | some z => next n' (fr.set d z) m
      | none => False
    | _, _ => False
  | some (.load w e d b off n'), fr, m =>
    match fr.get b with
    | some addr =>
      match m.load w e (addr.toNat + off) with
      | some z => next n' (fr.set d z) m
      | none => False
    | none => False
  | some (.store w b off s n'), fr, m =>
    match fr.get b, fr.get s with
    | some addr, some x =>
      match m.store w (addr.toNat + off) x with
      | some m' => next n' fr m'
      | none => False
    | _, _ => False
  | some (.cond c n₁ n₂), fr, m =>
    match fr.get c with
    | some x => (x = 0 → next n₂ fr m) ∧ (x ≠ 0 → next n₁ fr m)
    | none => False
  | some (.jump t), fr, m => next t fr m
  | some (.ret rs), fr, m =>
    match fr.readAll rs with
    | some vs => post vs m
    | none => False
  | _, _, _ => False

/-- The weakest precondition of the paths from node `n` to the next cut point or `ret`,
at most `k` instructions long. -/
def wpN (μ : Option Word) : Nat → Node → Frame Nat → Memory → Prop
  | 0, _, _, _ => False
  | k + 1, n, fr, m => wpI post (nextP cuts μ (wpN μ k)) (fn.instr? n) fr m

/-- The VC of an annotated function: from the entry under the precondition, and from
every cut point under its invariant (paths at most `K` instructions long). -/
def vc (pre : List Word → Memory → Prop) (K : Nat) : Prop :=
  (∀ (v : Nat → Word) (m : Memory), pre (fn.params.map v) m →
    wpN fn cuts post none K fn.entry (canon fn.params v) m) ∧
  (∀ nc ∈ cuts, ∀ (v : Nat → Word) (m : Memory), nc.2.inv v m →
    wpN fn cuts post (some (nc.2.measure v m)) K nc.1 (canon nc.2.defined v) m)

/-- What a path from `s` reaches: a return satisfying the postcondition, or a cut point
whose annotation holds, within the measure bound. -/
def Reach (μ : Option Word) (s : State Nat) : Prop :=
  (∃ s' vs m', Steps (prog fn) s s' ∧ step (prog fn) s' = .returned vs m' ∧ post vs m') ∨
  (∃ n' c fr' m', cuts.lookup n' = some c ∧ c.holds fr' m' ∧
    bound μ (c.measure (valsOn c.defined fr') m') ∧ Steps (prog fn) s ⟨⟨0, n'⟩, fr', [], m'⟩)

end

variable {fn : Func Nat} {cuts : List (Node × Cut)} {post : List Word → Memory → Prop}

end Silmaril.Machine.CBackend.RTL.VC
