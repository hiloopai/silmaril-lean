-- Word-granular memory models from an earlier Silmaril development; namespaces
-- `Silmaril.Memory{,.SC,.TSO}` kept. Re-exported by `Silmaril.X86.MemoryModel.Tso`.
module

public import Silmaril.Raw.X86.MemoryModel.SC
public import Mathlib.Logic.Relation
import Mathlib.Tactic.Convert

/-!
# FIFO store-buffer TSO

Stores enter a per-thread FIFO, loads forward from the newest matching local
entry, and an internal transition flushes only the oldest entry to shared
memory. A fence waits for its own buffer to empty. Observable steps allow
arbitrary finite flushes before and after an instruction. This is the ordinary
load/store/fence fragment of the x86-TSO abstract machine, without locks,
non-temporal accesses, mixed-size accesses, or fairness assumptions.
-/

@[expose] public section

namespace Silmaril.Memory.TSO

universe u

structure State (Tid Addr Val : Type u) where
  memory : Addr → Val
  buffer : Tid → List (Addr × Val)

variable {Tid Addr Val : Type u} [DecidableEq Tid] [DecidableEq Addr]

/-- Buffer lists are oldest first; recursively inspecting the tail makes the
newest matching write take priority. -/
def readBuffer (a : Addr) : List (Addr × Val) → Option Val
  | [] => none
  | (b, v) :: rest => (readBuffer a rest).or (if a = b then some v else none)

@[simp] theorem readBuffer_append (a : Addr) (xs ys : List (Addr × Val)) :
    readBuffer a (xs ++ ys) = (readBuffer a ys).or (readBuffer a xs) := by
  induction xs with
  | nil => simp [readBuffer]
  | cons x xs ih =>
      rcases x with ⟨b, v⟩
      simp only [List.cons_append, readBuffer, ih]
      cases readBuffer a ys <;> cases readBuffer a xs <;> rfl

@[simp] theorem readBuffer_enqueue_same (a : Addr) (v : Val) (xs : List (Addr × Val)) :
    readBuffer a (xs ++ [(a, v)]) = some v := by
  simp [readBuffer]

def embed (h : SC.Heap Addr Val) : State Tid Addr Val := ⟨h, fun _ => []⟩

def enqueue (s : State Tid Addr Val) (t : Tid) (a : Addr) (v : Val) : State Tid Addr Val :=
  { s with buffer := Function.update s.buffer t (s.buffer t ++ [(a, v)]) }

def readValue (s : State Tid Addr Val) (t : Tid) (a : Addr) : Val :=
  (readBuffer a (s.buffer t)).getD (s.memory a)

/-- Store forwarding reads the newest same-address local store even before it
becomes visible in shared memory. -/
@[simp] theorem readValue_enqueue_same (s : State Tid Addr Val) (t : Tid) (a : Addr) (v : Val) :
    readValue (enqueue s t a v) t a = v := by
  simp [readValue, enqueue, readBuffer]

omit [DecidableEq Addr] in
/-- A store buffer does not change the shared heap until propagation. -/
@[simp] theorem enqueue_memory (s : State Tid Addr Val) (t : Tid) (a : Addr) (v : Val) :
    (enqueue s t a v).memory = s.memory := rfl

/-- Only the head (oldest entry) may propagate. -/
inductive Flush : State Tid Addr Val → State Tid Addr Val → Prop
  | head (s : State Tid Addr Val) (t : Tid) (a : Addr) (v : Val) (rest : List (Addr × Val))
      (oldest : s.buffer t = (a, v) :: rest) :
      Flush s ⟨Function.update s.memory a v, Function.update s.buffer t rest⟩

abbrev Flushes := Relation.ReflTransGen (Flush (Tid := Tid) (Addr := Addr) (Val := Val))

/-- Instructions themselves do not silently commit buffered stores. -/
inductive Step : State Tid Addr Val → Event Tid Addr Val → State Tid Addr Val → Prop
  | load (s : State Tid Addr Val) (t : Tid) (a : Addr) : Step s (.load t a (readValue s t a)) s
  | store (s : State Tid Addr Val) (t : Tid) (a : Addr) (v : Val) :
      Step s (.store t a v) (enqueue s t a v)
  | fence (s : State Tid Addr Val) (t : Tid) (empty : s.buffer t = []) : Step s (.fence t) s

/-- An instruction may be surrounded by any finite number of internal flushes. -/
def WeakStep (s : State Tid Addr Val) (e : Event Tid Addr Val) (s' : State Tid Addr Val) : Prop :=
  ∃ before after, Flushes s before ∧ Step before e after ∧ Flushes after s'

theorem Step.weak {s s' : State Tid Addr Val} {e : Event Tid Addr Val} (h : Step s e s') :
    WeakStep s e s' := ⟨s, s', .refl, h, .refl⟩

/-- The atomic fence is enabled exactly when the issuing thread has drained. -/
theorem fence_iff (s s' : State Tid Addr Val) (t : Tid) :
    Step s (.fence t) s' ↔ s.buffer t = [] ∧ s' = s := by
  constructor
  · intro h; cases h with | fence _ h => exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact .fence _ t h

/-- An SC write is implemented by enqueuing and immediately flushing it. -/
theorem flush_enqueued_embed (h : SC.Heap Addr Val) (t : Tid) (a : Addr) (v : Val) :
    Flush (enqueue (embed h) t a v) (embed (Function.update h a v)) := by
  have f := Flush.head (enqueue (embed h) t a v) t a v [] (by simp [enqueue, embed])
  convert f using 1
  simp [enqueue, embed]

/-- SC embeds into TSO with empty buffers at observable boundaries. -/
theorem of_sc_step {h h' : SC.Heap Addr Val} {e : Event Tid Addr Val} (hs : SC.Step h e h') :
    WeakStep (embed h) e (embed h') := by
  cases hs with
  | load t a =>
      apply Step.weak
      simpa [readValue, readBuffer, embed] using Step.load (embed h) t a
  | store t a v =>
      exact ⟨embed h, enqueue (embed h) t a v, .refl, .store _ _ _ _,
        .single (flush_enqueued_embed h t a v)⟩
  | fence t => exact (Step.fence (embed h) t rfl).weak

theorem of_sc_execution {h h' : SC.Heap Addr Val} {es : List (Event Tid Addr Val)}
    (hs : Execution SC.Step h es h') : Execution WeakStep (embed h) es (embed h') :=
  hs.map embed (fun h => of_sc_step h)

theorem of_sc_concurrent {h : SC.Heap Addr Val} {left right : List (Event Tid Addr Val)}
    (hs : Concurrent SC.Step h left right) : Concurrent WeakStep (embed h) left right := by
  rcases hs with ⟨trace, sched, final, exec⟩
  exact ⟨trace, sched, embed final, of_sc_execution exec⟩

namespace Litmus

abbrev S := State Bool Bool Nat

def initial : S := embed SC.Litmus.initial
def afterLeft : S := enqueue initial false false 1
def afterBoth : S := enqueue afterLeft true true 1

/-- The two stores remain buffered while both other-location loads read zero. -/
theorem store_buffering_execution :
    Execution WeakStep initial
      [.store false false 1, .store true true 1, .load false true 0, .load true false 0]
      afterBoth := by
  refine .cons (Step.store _ _ _ _).weak (.cons (Step.store _ _ _ _).weak ?_)
  have l : Step afterBoth (.load false true 0) afterBoth := by
    simpa [afterBoth, afterLeft, initial, enqueue, embed, readValue, readBuffer,
      SC.Litmus.initial, Function.update] using Step.load afterBoth false true
  have r : Step afterBoth (.load true false 0) afterBoth := by
    simpa [afterBoth, afterLeft, initial, enqueue, embed, readValue, readBuffer,
      SC.Litmus.initial, Function.update] using Step.load afterBoth true false
  exact .cons l.weak (.cons r.weak (.nil _))

/-- A checked strict separation: TSO admits the same two thread traces that
SC's store-buffering theorem rules out. -/
theorem store_buffering_allowed : Concurrent WeakStep initial SC.Litmus.sbLeft SC.Litmus.sbRight := by
  refine ⟨_, ?_, afterBoth, store_buffering_execution⟩
  simp [SC.Litmus.sbLeft, SC.Litmus.sbRight, shuffles]

end Litmus
end Silmaril.Memory.TSO
