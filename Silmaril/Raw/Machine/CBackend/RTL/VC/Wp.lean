-- Reproduce with tools/mor/examples/import_rtl_vc.rs; declaration namespace retained.
module

public import Silmaril.Machine.CBackend.RTL.Semantics.Defs
/-!
# A cut-point VC generator for RTL, sound for total correctness

The assembly/IR side of the program-VC demos (research/smt/program-vc/README.md). The
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

namespace ProgramVC.RTL

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

theorem Reach.head {μ : Option Word} {s s' : State Nat} (h : Step (prog fn) s s')
    (hr : Reach fn cuts post μ s') : Reach fn cuts post μ s := by
  rcases hr with ⟨t, vs, m', ht, hf, hp⟩ | ⟨n', c, fr', m', hc, hh, hb, ht⟩
  · exact .inl ⟨t, vs, m', .head h ht, hf, hp⟩
  · exact .inr ⟨n', c, fr', m', hc, hh, hb, .head h ht⟩

theorem fetch_prog (fn : Func Nat) (n : Node) : (prog fn).fetch ⟨0, n⟩ = fn.instr? n := by
  simp [Prog.fetch, Prog.instr?, Prog.func?, prog]

/-- **Paths**: `wpN` from a frame below the actual one reaches a return or a cut point. -/
theorem path (μ : Option Word) : ∀ (k : Nat) (n : Node) (fr : Frame Nat) (m : Memory) (fr' : Frame Nat),
    wpN fn cuts post μ k n fr m → FLe fr fr' → Reach fn cuts post μ ⟨⟨0, n⟩, fr', [], m⟩ := by
  intro k
  induction k with
  | zero => intro n fr m fr' h; exact absurd h id
  | succ k ih =>
    intro n fr m fr' h hle
    -- reaching the next node
    have hnext : ∀ (n₁ : Node) (f₁ : Frame Nat) (m₁ : Memory) (f₁' : Frame Nat),
        nextP cuts μ (wpN fn cuts post μ k) n₁ f₁ m₁ →
        FLe f₁ f₁' → Reach fn cuts post μ ⟨⟨0, n₁⟩, f₁', [], m₁⟩ := by
      intro n₁ f₁ m₁ f₁' h₁ hle₁
      unfold nextP at h₁
      cases hc : cuts.lookup n₁ with
      | none => rw [hc] at h₁; exact ih n₁ f₁ m₁ f₁' h₁ hle₁
      | some c =>
        rw [hc] at h₁
        exact .inr ⟨n₁, c, f₁', m₁, hc, Cut.holds_mono h₁.1 hle₁,
          by rw [← valsOn_eq h₁.1.1 hle₁]; exact h₁.2, .refl⟩
    have hf := fetch_prog fn n
    simp only [wpN] at h
    cases hi : fn.instr? n with
    | none => simp only [hi, wpI] at h
    | some i =>
      rw [hi] at h hf
      simp only [wpI] at h
      cases i with
      | nop n₁ =>
        exact Reach.head (by unfold Step; simp [step, hf, Point.at]) (hnext _ _ _ _ h hle)
      | const d w n₁ =>
        exact Reach.head (by unfold Step; simp [step, hf, Point.at]) (hnext _ _ _ _ h (hle.set d w))
      | move d s n₁ =>
        dsimp only at h
        cases hs : fr.get s with
        | none => simp only [hs] at h
        | some x =>
          simp only [hs] at h
          exact Reach.head (by unfold Step; simp [step, hf, hle s x hs, Point.at])
            (hnext _ _ _ _ h (hle.set d x))
      | unary op d s n₁ =>
        dsimp only at h
        cases hs : fr.get s with
        | none => simp only [hs] at h
        | some x =>
          simp only [hs] at h
          exact Reach.head (by unfold Step; simp [step, hf, hle s x hs, Point.at])
            (hnext _ _ _ _ h (hle.set d _))
      | binary op d a b n₁ =>
        dsimp only at h
        cases ha : fr.get a with
        | none => simp only [ha] at h
        | some x =>
          cases hb : fr.get b with
          | none => simp only [ha, hb] at h
          | some y =>
            simp only [ha, hb] at h
            cases hz : op.eval x y with
            | none => simp only [hz] at h
            | some z =>
              simp only [hz] at h
              exact Reach.head (by unfold Step; simp [step, hf, hle a x ha, hle b y hb, hz, Point.at])
                (hnext _ _ _ _ h (hle.set d z))
      | load w e d b off n₁ =>
        dsimp only at h
        cases hb : fr.get b with
        | none => simp only [hb] at h
        | some addr =>
          simp only [hb] at h
          cases hz : m.load w e (addr.toNat + off) with
          | none => simp only [hz] at h
          | some z =>
            simp only [hz] at h
            exact Reach.head (by unfold Step; simp [step, hf, hle b addr hb, hz, Point.at])
              (hnext _ _ _ _ h (hle.set d z))
      | store w b off s n₁ =>
        dsimp only at h
        cases hb : fr.get b with
        | none => simp only [hb] at h
        | some addr =>
          cases hs : fr.get s with
          | none => simp only [hb, hs] at h
          | some x =>
            simp only [hb, hs] at h
            cases hm : m.store w (addr.toNat + off) x with
            | none => simp only [hm] at h
            | some m₁ =>
              simp only [hm] at h
              exact Reach.head (by unfold Step; simp [step, hf, hle b addr hb, hle s x hs, hm, Point.at])
                (hnext _ _ _ _ h hle)
      | call => exact absurd h id
      | cond c n₁ n₂ =>
        dsimp only at h
        cases hc : fr.get c with
        | none => simp only [hc] at h
        | some x =>
          simp only [hc] at h
          by_cases hx : x = 0
          · exact Reach.head (by unfold Step; simp [step, hf, hle c x hc, hx, Point.at])
              (hnext _ _ _ _ (h.1 hx) hle)
          · exact Reach.head (by unfold Step; simp [step, hf, hle c x hc, Point.at]; exact fun h0 => absurd h0 hx)
              (hnext _ _ _ _ (h.2 hx) hle)
      | jump t =>
        exact Reach.head (by unfold Step; simp [step, hf, Point.at]) (hnext _ _ _ _ h hle)
      | ret rs =>
        dsimp only at h
        cases hr : fr.readAll rs with
        | none => simp only [hr] at h
        | some vs =>
          simp only [hr] at h
          exact .inl ⟨_, vs, m, .refl, by simp [step, hf, hle.readAll rs vs hr], h⟩
      | trap => exact absurd h id

theorem lookup_mem : ∀ {cuts : List (Node × Cut)} {n : Node} {c : Cut},
    cuts.lookup n = some c → (n, c) ∈ cuts
  | [], _, _, h => by simp at h
  | (n', c') :: rest, n, c, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      have : n = n' := by simpa [beq_iff_eq] using he
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem behaves_of_steps {p : Prog Nat} {s s' : State Nat} {vs : List Word} {m : Memory}
    (h : Steps p s s') (hb : Behaves p s' (.returned vs m)) : Behaves p s (.returned vs m) := by
  obtain ⟨t, ht, hf⟩ := hb
  exact ⟨t, h.trans ht, hf⟩

/-- From a cut point whose annotation holds, the function returns into the postcondition. -/
theorem from_cut {pre : List Word → Memory → Prop} {K : Nat} (hvc : vc fn cuts post pre K) :
    ∀ (w : Nat) (n : Node) (c : Cut) (fr : Frame Nat) (m : Memory),
      (c.measure (valsOn c.defined fr) m).toNat = w → cuts.lookup n = some c → c.holds fr m →
      ∃ vs m', Behaves (prog fn) ⟨⟨0, n⟩, fr, [], m⟩ (.returned vs m') ∧ post vs m' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro n c fr m hw hc hh
    have hp := hvc.2 (n, c) (lookup_mem hc) (valsOn c.defined fr) m hh.2
    rcases path _ K n _ m fr hp (canon_le hh.1) with ⟨t, vs, m', ht, hf, hpost⟩ |
        ⟨n', c', fr', m', hc', hh', hb, ht⟩
    · exact ⟨vs, m', ⟨t, ht, hf⟩, hpost⟩
    · simp only [bound] at hb
      have hlt : (c'.measure (valsOn c'.defined fr') m').toNat < w := by
        rw [← hw]; exact (BitVec.lt_def).mp hb
      obtain ⟨vs, m'', hbeh, hpost⟩ := ih _ hlt n' c' fr' m' rfl hc' hh'
      exact ⟨vs, m'', behaves_of_steps ht hbeh, hpost⟩

/-- **Soundness of the RTL VC generator.** If `vc` holds, the function entered at its entry
with every parameter register written and the precondition true of their values returns,
with values and memory satisfying the postcondition. -/
theorem sound {pre : List Word → Memory → Prop} {K : Nat} (hvc : vc fn cuts post pre K)
    (fr : Frame Nat) (m : Memory) (hdef : ∀ r ∈ fn.params, (fr.get r).isSome)
    (hpre : pre (fn.params.map (valsOn fn.params fr)) m) :
    ∃ vs m', Behaves (prog fn) ⟨⟨0, fn.entry⟩, fr, [], m⟩ (.returned vs m') ∧ post vs m' := by
  have hp := hvc.1 (valsOn fn.params fr) m hpre
  rcases path _ K fn.entry _ m fr hp (canon_le hdef) with ⟨t, vs, m', ht, hf, hpost⟩ |
      ⟨n', c', fr', m', hc', hh', _, ht⟩
  · exact ⟨vs, m', ⟨t, ht, hf⟩, hpost⟩
  · obtain ⟨vs, m'', hbeh, hpost⟩ := from_cut hvc _ n' c' fr' m' rfl hc' hh'
    exact ⟨vs, m'', behaves_of_steps ht hbeh, hpost⟩

end ProgramVC.RTL
