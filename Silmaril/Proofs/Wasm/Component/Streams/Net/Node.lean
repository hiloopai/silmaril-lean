module

public import Silmaril.Proofs.Wasm.Component.Streams.Net.Chan
public import Silmaril.Proofs.Wasm.Component.Streams.Spec

/-!
# The node invariant

A node's state is related to its transformer by `NodeInv`: its state is `T` fed with the items it
has read (`got`); every live output has acknowledged, is writing and has queued exactly `T`'s
output so far (`outSoFar`: `T.runP got`, then `T`'s flush once the input has been dropped); a dead
output has acknowledged a prefix of it; an output closed normally has acknowledged all of it, after
the flush. A node that dropped its input before the end did so because `T` was done or every
output was dead; a source has nothing to read.

Each node action preserves the invariant (`inv_onRead`, `inv_readBlk`, `inv_write`,
`inv_waitOut`, `inv_stop`, `inv_dropOut`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Net

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Proofs.Wasm.Component.Streams.Spec

variable {σ : Type}

/-- The input has been dropped (and `T`'s flush queued). -/
def _root_.Silmaril.Wasm.Component.Streams.Net.RV.flushed : RV → Bool
  | .gone _ => true
  | _ => false

/-- `T`'s flush is part of the output: the input was dropped at its end, or when `T` was done (not
when every output was dead, as then nobody reads it). -/
def _root_.Silmaril.Wasm.Component.Streams.Net.NSt.flushedP (T : Tr σ Val Val) (x : NSt σ) : Bool :=
  match x.rd with
  | .gone b => b || T.done x.s
  | _ => false

/-- The output so far of a node. -/
def _root_.Silmaril.Wasm.Component.Streams.Net.NSt.outSoFar (T : Tr σ Val Val) (x : NSt σ) : List Val :=
  (T.feed T.init x.got).2 ++ (if x.flushedP T then T.flush x.s else [])

theorem flushedP_of (T : Tr σ Val Val) (x : NSt σ) (h : x.rd.flushed = false) :
    x.flushedP T = false := by
  unfold NSt.flushedP
  cases hr : x.rd <;> simp_all [RV.flushed]

/-- The invariant of one output, against the output so far `O`. -/
def OInv (O : List Val) (fl : Bool) (o : Out) : Prop :=
  match o.st with
  | .idle q => o.ack ++ q = O
  | .busy xs q => o.ack ++ xs ++ q = O
  | .dead => o.ack <+: O
  | .closed false => o.ack = O ∧ fl = true
  | .closed true => o.ack <+: O

/-- **The node invariant.** -/
structure NodeInv (N : Node) (x : NSt N.σ) : Prop where
  hs : x.s = (N.T.feed N.T.init x.got).1
  len : x.outs.length = N.outs.length
  outs : ∀ o ∈ x.outs, OInv (x.outSoFar N.T) x.rd.flushed o
  stop : x.rd = .gone false → N.T.done x.s = true ∨ (x.outs ≠ [] ∧ ∀ o ∈ x.outs, o.isDead)
  src : N.inp = none → x.rd = .gone true ∧ x.got = []

/-! ## Outputs -/

theorem OInv.push {O ys : List Val} {o : Out} (b : Bool) (h : OInv O false o) :
    OInv (O ++ ys) b (o.push ys) := by
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q =>
    simp only [OInv, Out.push] at h ⊢
    rw [← h, List.append_assoc]
  | busy xs q =>
    simp only [OInv, Out.push] at h ⊢
    rw [← h, List.append_assoc, List.append_assoc, List.append_assoc]
  | dead =>
    simp only [OInv, Out.push] at h ⊢
    exact h.trans (List.prefix_append _ _)
  | closed d =>
    cases d
    · simp [OInv] at h
    · simp only [OInv, Out.push] at h ⊢
      exact h.trans (List.prefix_append _ _)

theorem OInv.onWrite_idle {O : List Val} {fl : Bool} {q a : List Val} (p : Nat)
    (h : OInv O fl ⟨.idle q, a⟩) : OInv O fl (Out.onWrite ⟨.idle q, a⟩ p) := by
  simp only [Out.onWrite]
  split
  · exact h
  · have h' : a ++ q = O := h
    show a <+: O
    rw [← h']
    exact List.prefix_append _ _

theorem OInv.onWrite_busy {O : List Val} {fl : Bool} {xs q a : List Val} (p : Nat)
    (h : OInv O fl ⟨.busy xs q, a⟩) : OInv O fl (Out.onWrite ⟨.busy xs q, a⟩ p) := by
  have h' : a ++ xs ++ q = O := h
  simp only [Out.onWrite]
  split
  · show a ++ xs.take (count p) ++ (xs.drop (count p) ++ q) = O
    rw [← h', List.append_assoc, List.append_assoc, ← List.append_assoc (xs.take _),
      List.take_append_drop]
  · show a ++ xs.take (count p) <+: O
    rw [← h', List.append_assoc]
    exact (List.prefix_append_right_inj a).2 ((List.take_prefix _ _).trans
      (List.prefix_append _ _))

theorem OInv.onWrite {O : List Val} {fl : Bool} {o : Out} (p : Nat) (h : OInv O fl o) :
    OInv O fl (o.onWrite p) := by
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q => exact OInv.onWrite_idle p h
  | busy xs q => exact OInv.onWrite_busy p h
  | dead => exact h
  | closed d => exact h

theorem OInv.afterWrite {O : List Val} {fl : Bool} {q a : List Val} (n r : Nat)
    (h : OInv O fl ⟨.idle q, a⟩) : OInv O fl (Out.afterWrite (q.take n) (q.drop n) a r) := by
  have hb : OInv O fl ⟨.busy (q.take n) (q.drop n), a⟩ := by
    simp only [OInv] at h ⊢
    rw [← h, List.append_assoc, List.take_append_drop]
  unfold Out.afterWrite
  split
  · exact hb
  · exact hb.onWrite r

theorem isDead_push {o : Out} (ys : List Val) (h : o.isDead) : (o.push ys).isDead := by
  obtain ⟨st, a⟩ := o
  rcases h with h | h <;> simp only at h <;> subst h <;> simp [Out.push, Out.isDead]

theorem isDead_onWrite {o : Out} (p : Nat) (h : o.isDead) : (o.onWrite p).isDead := by
  obtain ⟨st, a⟩ := o
  rcases h with h | h <;> simp only at h <;> subst h <;> simp [Out.onWrite, Out.isDead]

/-! ## Node actions -/

theorem outSoFar_onRead (T : Tr σ Val Val) (x : NSt σ) (p : Nat) (ys : List Val)
    (hs : x.s = (T.feed T.init x.got).1) (hfl : x.rd.flushed = false) :
    (x.onRead T p ys).outSoFar T = x.outSoFar T ++ (T.feed x.s ys).2 := by
  have h2 : (x.onRead T p ys).rd.flushed = false := by
    simp only [NSt.onRead]
    split <;> rfl
  simp only [NSt.outSoFar, flushedP_of T _ h2, flushedP_of T _ hfl, Bool.false_eq_true,
    ↓reduceIte, List.append_nil]
  simp only [NSt.onRead, feed_append, hs]

theorem onRead_outs (N : Node) (x : NSt N.σ) (p : Nat) (ys : List Val) (h : NodeInv N x)
    (hfl : x.rd.flushed = false) :
    ∀ o ∈ (x.onRead N.T p ys).outs,
      OInv ((x.onRead N.T p ys).outSoFar N.T) (x.onRead N.T p ys).rd.flushed o := by
  have hfl' : (x.onRead N.T p ys).rd.flushed = false := by
    simp only [NSt.onRead]
    split <;> rfl
  intro o ho
  rw [outSoFar_onRead N.T x p ys h.hs hfl, hfl']
  obtain ⟨o₀, ho₀, rfl⟩ : ∃ o₀ ∈ x.outs, (o₀.push (N.T.feed x.s ys).2) = o := by
    simpa [NSt.onRead] using ho
  have h0 : OInv (x.outSoFar N.T) false o₀ := hfl ▸ h.outs o₀ ho₀
  exact h0.push false

theorem inv_onRead (N : Node) (x : NSt N.σ) (p : Nat) (ys : List Val) (h : NodeInv N x)
    (hrd : x.rd = .idle ∨ x.rd = .busy) : NodeInv N (x.onRead N.T p ys) := by
  have hfl : x.rd.flushed = false := by rcases hrd with h | h <;> rw [h] <;> rfl
  refine ⟨?_, by simp [NSt.onRead, h.len], onRead_outs N x p ys h hfl, fun hg => ?_, fun hi => ?_⟩
  · simp only [NSt.onRead, feed_append, h.hs]
  · simp only [NSt.onRead] at hg
    split at hg <;> cases hg
  · have := (h.src hi).1
    rcases hrd with h' | h' <;> rw [h'] at this <;> cases this

theorem inv_readBlk (N : Node) (x : NSt N.σ) (h : NodeInv N x) (hrd : x.rd = .idle) :
    NodeInv N { x with rd := .busy } := by
  have hfl : x.rd.flushed = false := by rw [hrd]; rfl
  refine ⟨h.hs, h.len, ?_, fun hg => by simp at hg, fun hi => ?_⟩
  · intro o ho
    have := h.outs o ho
    have h1 := flushedP_of N.T x hfl
    have h2 := flushedP_of N.T { x with rd := .busy } rfl
    simp only [NSt.outSoFar, h1, h2, hfl] at this ⊢
    exact this
  · have := (h.src hi).1
    rw [hrd] at this
    cases this

/-- Changing one output. -/
theorem inv_set (N : Node) (x : NSt N.σ) (h : NodeInv N x) (j : Nat) (o o' : Out)
    (ho : x.outs[j]? = some o) (h' : OInv (x.outSoFar N.T) x.rd.flushed o')
    (hd : o.isDead → o'.isDead) : NodeInv N { x with outs := x.outs.set j o' } := by
  refine ⟨h.hs, by simp [h.len], ?_, ?_, h.src⟩
  · intro o₁ ho₁
    rcases List.mem_or_eq_of_mem_set ho₁ with ho₁ | rfl
    · exact h.outs o₁ ho₁
    · exact h'
  · intro hg
    rcases h.stop hg with hT | ⟨hne, hall⟩
    · exact Or.inl hT
    · refine Or.inr ⟨by simpa using hne, fun o₁ ho₁ => ?_⟩
      rcases List.mem_or_eq_of_mem_set ho₁ with ho₁ | rfl
      · exact hall o₁ ho₁
      · exact hd (hall o (List.mem_of_getElem? ho))

theorem inv_write (N : Node) (x : NSt N.σ) (h : NodeInv N x) (j : Nat) (q a : List Val)
    (n r : Nat) (ho : x.outs[j]? = some ⟨.idle q, a⟩) :
    NodeInv N { x with outs := x.outs.set j (Out.afterWrite (q.take n) (q.drop n) a r) } :=
  inv_set N x h j _ _ ho ((h.outs _ (List.mem_of_getElem? ho)).afterWrite n r)
    (fun hd => by rcases hd with hd | hd <;> cases hd)

theorem inv_waitOut (N : Node) (x : NSt N.σ) (h : NodeInv N x) (j : Nat) (o : Out) (p : Nat)
    (ho : x.outs[j]? = some o) : NodeInv N { x with outs := x.outs.set j (o.onWrite p) } :=
  inv_set N x h j _ _ ho ((h.outs _ (List.mem_of_getElem? ho)).onWrite p) (isDead_onWrite p)

theorem inv_dropOut (N : Node) (x : NSt N.σ) (h : NodeInv N x) (j : Nat) (a : List Val)
    (d : Bool) (hrd : ∃ b, x.rd = .gone b)
    (ho : x.outs[j]? = some ⟨.idle [], a⟩ ∧ d = false ∨ x.outs[j]? = some ⟨.dead, a⟩ ∧ d = true) :
    NodeInv N { x with outs := x.outs.set j ⟨.closed d, a⟩ } := by
  have hfl : x.rd.flushed = true := by
    obtain ⟨b, hb⟩ := hrd
    rw [hb]
    rfl
  rcases ho with ⟨ho, rfl⟩ | ⟨ho, rfl⟩
  · refine inv_set N x h j _ _ ho ?_ (fun hd => by rcases hd with hd | hd <;> cases hd)
    have := h.outs _ (List.mem_of_getElem? ho)
    simp only [OInv, List.append_nil] at this ⊢
    exact ⟨this, hfl⟩
  · refine inv_set N x h j _ _ ho ?_ (fun _ => Or.inr rfl)
    have := h.outs _ (List.mem_of_getElem? ho)
    simpa [OInv] using this

theorem stop_flushedP (N : Node) (x : NSt N.σ) (hfl : x.rd.flushed = false) :
    (x.stop N.T).outSoFar N.T =
      x.outSoFar N.T ++ (if decide (x.rd = .ended) || N.T.done x.s then N.T.flush x.s else []) := by
  have hP : (x.stop N.T).flushedP N.T = (decide (x.rd = .ended) || N.T.done x.s) := rfl
  have hP0 := flushedP_of N.T x hfl
  simp only [NSt.outSoFar, hP, hP0, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  rfl

/-- The outputs after the stop: the flush is part of the output, or every output is dead. -/
theorem stop_outs (N : Node) (x : NSt N.σ) (h : NodeInv N x) (hm : x.mayStop N.T)
    (hfl : x.rd.flushed = false) :
    ∀ o ∈ (x.stop N.T).outs, OInv ((x.stop N.T).outSoFar N.T) (x.stop N.T).rd.flushed o := by
  intro o ho
  obtain ⟨o₀, ho₀, rfl⟩ : ∃ o₀ ∈ x.outs, o₀.push (N.T.flush x.s) = o := by
    simpa [NSt.stop] using ho
  have h0 : OInv (x.outSoFar N.T) false o₀ := hfl ▸ h.outs o₀ ho₀
  rw [stop_flushedP N x hfl]
  by_cases hp : (decide (x.rd = .ended) || N.T.done x.s) = true
  · simp only [hp, ↓reduceIte]
    exact h0.push _
  · have hall : o₀.isDead := by
      rcases hm with hm | ⟨-, hT | ⟨-, hall⟩⟩
      · exact absurd (by simp [hm]) hp
      · exact absurd (by simp [hT]) hp
      · exact hall o₀ ho₀
    simp only [hp, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    obtain ⟨st, a⟩ := o₀
    rcases hall with hd | hd <;> simp only at hd <;> subst hd <;> simpa [OInv, Out.push] using h0

/-- A node that stopped without seeing the end did so because `T` was done or every output was
dead. -/
theorem stop_stop (N : Node) (x : NSt N.σ) (hm : x.mayStop N.T)
    (hg : (x.stop N.T).rd = .gone false) :
    N.T.done (x.stop N.T).s = true ∨
      ((x.stop N.T).outs ≠ [] ∧ ∀ o ∈ (x.stop N.T).outs, o.isDead) := by
  have hne : x.rd ≠ .ended := by simpa [NSt.stop] using hg
  rcases hm with hm | ⟨-, hT | ⟨hne', hall⟩⟩
  · exact absurd hm hne
  · exact Or.inl hT
  · refine Or.inr ⟨by simpa [NSt.stop] using hne', fun o ho => ?_⟩
    obtain ⟨o₀, ho₀, rfl⟩ : ∃ o₀ ∈ x.outs, o₀.push (N.T.flush x.s) = o := by
      simpa [NSt.stop] using ho
    exact isDead_push _ (hall o₀ ho₀)

theorem inv_stop (N : Node) (x : NSt N.σ) (h : NodeInv N x) (hm : x.mayStop N.T) :
    NodeInv N (x.stop N.T) := by
  have hrd : x.rd = .idle ∨ x.rd = .ended := by
    rcases hm with hm | ⟨hm, -⟩
    · exact Or.inr hm
    · exact Or.inl hm
  have hfl : x.rd.flushed = false := by rcases hrd with h | h <;> rw [h] <;> rfl
  refine ⟨h.hs, by simp [NSt.stop, h.len], stop_outs N x h hm hfl, stop_stop N x hm, fun hi => ?_⟩
  have := (h.src hi).1
  rcases hrd with h' | h' <;> rw [h'] at this <;> cases this

end Silmaril.Proofs.Wasm.Component.Streams.Net
