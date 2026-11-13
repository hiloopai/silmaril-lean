module

public import Silmaril.Net.Channel.Defs

/-!
# Channels: theorems

PROVED (standard axioms):

* `okFrom_mono`: more messages in flight admit more traces; `okFrom_append`: a trace splits at
  any point, the second part seeing the messages sent in the first.
* What the loose channel allows: **`loose_drop`** (loss: removing a receive), **`loose_dup`**
  (duplication: repeating a receive), **`loose_swap`** (reordering adjacent receives), and
  `loose_sends` (any sequence of sends, nothing received).
* What it forbids: **`loose_recv_sent`**: every received message was sent (`received ⊆ sent`),
  whole: there is no event that carries part of a message or two messages.
* **`fifo_loose`**: a reliable FIFO channel is a loose channel.
* **`loose_liftT`**: seen through any partial decoder, a loose channel is loose (layering);
  `liftT_map`: through a decoder inverting the encoder, the encoded trace is the original.
-/

@[expose] public section

namespace Silmaril.Net.Channel

variable {α β : Type}

theorem okFrom_mono {s s' : List α} (hs : ∀ x ∈ s, x ∈ s') (tr : List (Ev α))
    (h : okFrom s tr) : okFrom s' tr := by
  induction tr generalizing s s' with
  | nil => trivial
  | cons e t ih =>
    cases e with
    | send m =>
      exact ih (s := m :: s) (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs x hx)) h
    | recv m => exact ⟨hs m h.1, ih hs h.2⟩

/-- The messages in flight after a trace: those of `seen`, and those sent (most recent first). -/
def seenAfter (seen : List α) : List (Ev α) → List α
  | [] => seen
  | .send m :: t => seenAfter (m :: seen) t
  | .recv _ :: t => seenAfter seen t

theorem okFrom_append (seen : List α) (a b : List (Ev α)) :
    okFrom seen (a ++ b) ↔ okFrom seen a ∧ okFrom (seenAfter seen a) b := by
  induction a generalizing seen with
  | nil => simp [okFrom, seenAfter]
  | cons e t ih =>
    cases e with
    | send m => simpa [okFrom, seenAfter] using ih (m :: seen)
    | recv m => simp only [List.cons_append, okFrom, seenAfter, ih seen, and_assoc]

/-- **Loss**: removing a receive keeps a trace admitted. -/
theorem loose_drop (seen : List α) (a b : List (Ev α)) (m : α)
    (h : okFrom seen (a ++ .recv m :: b)) : okFrom seen (a ++ b) := by
  have hs := (okFrom_append seen a _).mp h
  exact (okFrom_append seen a b).mpr ⟨hs.1, hs.2.2⟩

/-- **Duplication**: repeating a receive keeps a trace admitted. -/
theorem loose_dup (seen : List α) (a b : List (Ev α)) (m : α)
    (h : okFrom seen (a ++ .recv m :: b)) : okFrom seen (a ++ .recv m :: .recv m :: b) := by
  have hs := (okFrom_append seen a _).mp h
  exact (okFrom_append seen a _).mpr ⟨hs.1, hs.2.1, hs.2.1, hs.2.2⟩

/-- **Reordering**: swapping two adjacent receives keeps a trace admitted. -/
theorem loose_swap (seen : List α) (a b : List (Ev α)) (m n : α)
    (h : okFrom seen (a ++ .recv m :: .recv n :: b)) :
    okFrom seen (a ++ .recv n :: .recv m :: b) := by
  have hs := (okFrom_append seen a _).mp h
  exact (okFrom_append seen a _).mpr ⟨hs.1, hs.2.2.1, hs.2.1, hs.2.2.2⟩

/-- Any sequence of sends is admitted (nothing need ever be delivered). -/
theorem loose_sends (seen ms : List α) : okFrom seen (ms.map Ev.send) := by
  induction ms generalizing seen with
  | nil => trivial
  | cons m t ih => exact ih (m :: seen)

theorem okFrom_recv_sent (seen : List α) (tr : List (Ev α)) (h : okFrom seen tr) :
    ∀ m ∈ received tr, m ∈ seen ∨ m ∈ sent tr := by
  induction tr generalizing seen with
  | nil => simp [received]
  | cons e t ih =>
    cases e with
    | send x =>
      intro m hm
      have hr : m ∈ x :: seen ∨ m ∈ sent t := ih (x :: seen) h m hm
      rcases hr with hr | hr
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hr
      · exact Or.inr (List.mem_cons_of_mem _ hr)
    | recv x =>
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl h.1
      · exact ih seen h.2 m hm

/-- **Every received message was sent, whole.** -/
theorem loose_recv_sent {tr : List (Ev α)} (h : Loose tr) : ∀ m ∈ received tr, m ∈ sent tr := by
  intro m hm
  rcases okFrom_recv_sent [] tr h m hm with h' | h'
  · cases h'
  · exact h'

theorem fifoFrom_okFrom (q seen : List α) (hq : ∀ x ∈ q, x ∈ seen) (tr : List (Ev α))
    (h : fifoFrom q tr) : okFrom seen tr := by
  induction tr generalizing q seen with
  | nil => trivial
  | cons e t ih =>
    cases e with
    | send m =>
      refine ih (q ++ [m]) (m :: seen) ?_ h
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_cons_of_mem _ (hq x hx)
      · rw [List.mem_singleton.mp hx]; exact List.mem_cons_self
    | recv m =>
      have hhd : q.head? = some m := h.1
      have hm : m ∈ q := List.mem_of_mem_head? hhd
      refine ⟨hq m hm, ih q.tail seen (fun x hx => hq x (List.mem_of_mem_tail hx)) h.2⟩

/-- **A reliable FIFO channel is a loose channel.** -/
theorem fifo_loose {tr : List (Ev α)} (h : Fifo tr) : Loose tr :=
  fifoFrom_okFrom [] [] (fun _ h => h) tr h

/-- What a decoding layer has in flight, relative to the channel below: every decodable message
in flight below is in flight above, decoded. -/
def LiftInv (dec : β → Option α) (seen : List β) (seen' : List α) : Prop :=
  ∀ b ∈ seen, ∀ a, dec b = some a → a ∈ seen'

theorem liftT_send (dec : β → Option α) (b : β) (t : List (Ev β)) :
    liftT dec (.send b :: t) = ((dec b).map Ev.send).toList ++ liftT dec t := by
  cases h : dec b <;> simp [liftT, Ev.lift, h]

theorem liftT_recv (dec : β → Option α) (b : β) (t : List (Ev β)) :
    liftT dec (.recv b :: t) = ((dec b).map Ev.recv).toList ++ liftT dec t := by
  cases h : dec b <;> simp [liftT, Ev.lift, h]

/-- A send below: the invariant extends, and the decoded send (if any) is admitted above. -/
theorem liftInv_send (dec : β → Option α) {seen : List β} {seen' : List α}
    (hs : LiftInv dec seen seen') (b : β) :
    ∃ seen'', LiftInv dec (b :: seen) seen'' ∧
      ∀ t, okFrom seen'' (liftT dec t) → okFrom seen' (liftT dec (.send b :: t)) := by
  cases hb : dec b with
  | none =>
    refine ⟨seen', ?_, ?_⟩
    · intro x hx a ha
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hb] at ha; cases ha
      · exact hs x hx a ha
    · intro t ht
      rw [liftT_send, hb]
      exact ht
  | some a =>
    refine ⟨a :: seen', ?_, ?_⟩
    · intro x hx a' ha'
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hb] at ha'; cases ha'; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hs x hx a' ha')
    · intro t ht
      rw [liftT_send, hb]
      exact ht

/-- A receive below of a message in flight: the decoded receive (if any) is admitted above. -/
theorem liftInv_recv (dec : β → Option α) {seen : List β} {seen' : List α}
    (hs : LiftInv dec seen seen') {b : β} (hb : b ∈ seen) (t : List (Ev β))
    (ht : okFrom seen' (liftT dec t)) : okFrom seen' (liftT dec (.recv b :: t)) := by
  rw [liftT_recv]
  cases hd : dec b with
  | none => exact ht
  | some a => exact ⟨hs b hb a hd, ht⟩

theorem okFrom_liftT (dec : β → Option α) (seen : List β) (seen' : List α)
    (hs : LiftInv dec seen seen') (tr : List (Ev β))
    (h : okFrom seen tr) : okFrom seen' (liftT dec tr) := by
  induction tr generalizing seen seen' with
  | nil => trivial
  | cons e t ih =>
    cases e with
    | send b =>
      obtain ⟨s'', hinv, hk⟩ := liftInv_send dec hs b
      exact hk t (ih (b :: seen) s'' hinv h)
    | recv b => exact liftInv_recv dec hs h.1 t (ih seen seen' hs h.2)

/-- **Layering**: a layer that decodes the messages of a loose channel, dropping the
undecodable ones, sees a loose channel. -/
theorem loose_liftT (dec : β → Option α) {tr : List (Ev β)} (h : Loose tr) :
    Loose (liftT dec tr) :=
  okFrom_liftT dec [] [] (fun _ h => by cases h) tr h

/-- Through a decoder inverting the encoder, the encoded trace is the original one. -/
theorem liftT_map (enc : α → β) (dec : β → Option α) (h : ∀ a, dec (enc a) = some a)
    (tr : List (Ev α)) : liftT dec (tr.map (Ev.map enc)) = tr := by
  induction tr with
  | nil => rfl
  | cons e t ih =>
    cases e with
    | send a => simp [liftT, Ev.lift, Ev.map, h] at ih ⊢; exact ih
    | recv a => simp [liftT, Ev.lift, Ev.map, h] at ih ⊢; exact ih

end Silmaril.Net.Channel
