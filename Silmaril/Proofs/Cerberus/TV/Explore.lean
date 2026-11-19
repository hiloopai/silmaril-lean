module

public import Silmaril.Cerberus.TV.Explore.Defs

/-! Proofs of `Silmaril.Cerberus.TV.Explore.Thms`: soundness, completeness, termination and
progress of the exhaustive exploration. -/

@[expose] public section

namespace Silmaril.Proofs.Cerberus.TV

open Silmaril.Cerberus
open Silmaril.Cerberus.TV
open Silmaril.Cerberus.Core.Dynamics

/-- One step of `explore` on a nonempty stack. -/
theorem explore_step (file : Program) (labels : Labels) (budget depth : Nat) (s : State)
    (rest : List (Nat × State)) (acc : Leaves) :
    let r := explore file labels (budget + 1) ((depth, s) :: rest) acc
    (∃ o, s.control = .halt o ∧
      r = explore file labels budget rest { acc with ends := (o, s.memory.stdout) :: acc.ends }) ∨
    ((∀ o, s.control ≠ .halt o) ∧ depth = 0 ∧
      r = explore file labels budget rest { acc with limited := true }) ∨
    ((∀ o, s.control ≠ .halt o) ∧ (∃ d, depth = d + 1) ∧ successors file labels s = [] ∧
      r = explore file labels budget rest { acc with stuck := true }) ∨
    ((∀ o, s.control ≠ .halt o) ∧ ∃ d, depth = d + 1 ∧ successors file labels s ≠ [] ∧
      r = explore file labels budget ((successors file labels s).map (fun q => (d, q.2)) ++ rest)
        { acc with steps := acc.steps + 1 }) := by
  intro r
  simp only [r, explore]
  split
  · rename_i o hc
    exact .inl ⟨o, hc, rfl⟩
  · rename_i hlive
    split
    · exact .inr (.inl ⟨hlive, rfl, rfl⟩)
    · rename_i d
      split
      · rename_i hs
        exact .inr (.inr (.inl ⟨hlive, ⟨d, rfl⟩, hs, rfl⟩))
      · rename_i p ps hs
        refine .inr (.inr (.inr ⟨hlive, d, rfl, by simp [hs], ?_⟩))
        rw [hs]

/-- Collected endings only grow. -/
theorem explore_ends_mono (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Leaves) (e : Outcome × String),
      e ∈ acc.ends → e ∈ (explore file labels budget stack acc).ends := by
  intro budget
  induction budget with
  | zero => intro stack acc e h; simp only [explore]; split <;> exact h
  | succ budget ih =>
      intro stack acc e h
      match stack with
      | [] => simpa [explore] using h
      | (depth, s) :: rest =>
          rcases explore_step file labels budget depth s rest acc with
            ⟨o, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ <;> rw [hr]
          · exact ih _ _ e (List.mem_cons_of_mem _ h)
          all_goals exact ih _ _ e h

/-- Once limited, always limited. -/
theorem explore_limited (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Leaves), acc.limited = true →
      (explore file labels budget stack acc).limited = true := by
  intro budget
  induction budget with
  | zero => intro stack acc h; simp only [explore]; split <;> simp [h]
  | succ budget ih =>
      intro stack acc h
      match stack with
      | [] => simpa [explore] using h
      | (depth, s) :: rest =>
          rcases explore_step file labels budget depth s rest acc with
            ⟨o, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ <;> rw [hr]
          · exact ih _ _ h
          · exact ih _ _ rfl
          · exact ih _ _ h
          · exact ih _ _ h

/-- Once stuck, always stuck. -/
theorem explore_stuck (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Leaves), acc.stuck = true →
      (explore file labels budget stack acc).stuck = true := by
  intro budget
  induction budget with
  | zero => intro stack acc h; simp only [explore]; split <;> simp [h]
  | succ budget ih =>
      intro stack acc h
      match stack with
      | [] => simpa [explore] using h
      | (depth, s) :: rest =>
          rcases explore_step file labels budget depth s rest acc with
            ⟨o, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ <;> rw [hr]
          · exact ih _ _ h
          · exact ih _ _ h
          · exact ih _ _ rfl
          · exact ih _ _ h

/-- Every collected ending is reached from the start. -/
theorem explore_sound_aux (file : Program) (labels : Labels) (start : State) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Leaves),
      (∀ p ∈ stack, Spec.Reaches file labels start p.2) →
      (∀ e ∈ acc.ends, ∃ s, Spec.Reaches file labels start s ∧ s.control = .halt e.1 ∧
        s.memory.stdout = e.2) →
      ∀ e ∈ (explore file labels budget stack acc).ends,
        ∃ s, Spec.Reaches file labels start s ∧ s.control = .halt e.1 ∧ s.memory.stdout = e.2 := by
  intro budget
  induction budget with
  | zero => intro stack acc _ hacc e he; simp only [explore] at he; split at he <;> exact hacc e he
  | succ budget ih =>
      intro stack acc hstack hacc e he
      match stack with
      | [] => exact hacc e (by simpa [explore] using he)
      | (depth, s) :: rest =>
          have hs : Spec.Reaches file labels start s := hstack (depth, s) (by simp)
          have hrest : ∀ p ∈ rest, Spec.Reaches file labels start p.2 :=
            fun p hp => hstack p (by simp [hp])
          rcases explore_step file labels budget depth s rest acc with
            ⟨o, hc, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ <;> rw [hr] at he
          · refine ih rest _ hrest ?_ e he
            intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact ⟨s, hs, hc, rfl⟩
            · exact hacc f hf
          · exact ih rest { acc with limited := true } hrest hacc e he
          · exact ih rest { acc with stuck := true } hrest hacc e he
          · refine ih _ { acc with steps := acc.steps + 1 } ?_ hacc e he
            intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · obtain ⟨⟨a, t⟩, hmem, rfl⟩ := List.mem_map.mp hp
              have htr := (successors_correct file labels s a t).mp hmem
              exact Relation.ReflTransGen.tail hs ⟨a, htr⟩
            · exact hrest p hp

/-- A halted state reaches only itself. -/
theorem reaches_halt {file : Program} {labels : Labels} {s t : State} {o : Outcome}
    (hs : s.control = .halt o) (h : Spec.Reaches file labels s t) : t = s := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ _ =>
      obtain ⟨a, hstep⟩ := step
      cases hstep with
      | respond live _ => exact absurd hs (live o)

/-- When the exploration is not limited, every ending reachable from a stack entry is
collected. -/
theorem explore_complete_aux (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Leaves),
      (explore file labels budget stack acc).limited = false →
      ∀ p ∈ stack, ∀ t o, Spec.Reaches file labels p.2 t → t.control = .halt o →
        (o, t.memory.stdout) ∈ (explore file labels budget stack acc).ends := by
  intro budget
  induction budget with
  | zero =>
      intro stack acc hl p hp
      simp only [explore] at hl
      split at hl
      · rename_i hempty
        simp only [List.isEmpty_iff] at hempty
        simp [hempty] at hp
      · simp at hl
  | succ budget ih =>
      intro stack acc hl p hp
      match stack with
      | [] => simp at hp
      | (depth, s) :: rest =>
          rcases explore_step file labels budget depth s rest acc with
            ⟨o, hc, hr⟩ | ⟨_, _, hr⟩ | ⟨hlive, _, hsucc, hr⟩ | ⟨hlive, d, _, _, hr⟩ <;>
            rw [hr] at hl ⊢
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro t o' hreach ht
              have := reaches_halt hc hreach
              subst this
              rw [hc] at ht
              cases ht
              exact explore_ends_mono file labels budget rest _ _ (by simp)
            · exact ih rest _ hl p hp
          · rw [explore_limited file labels budget rest _ rfl] at hl
            cases hl
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro t o hreach ht
              rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨u, ⟨a, hstep⟩, _⟩
              · subst heq
                exact absurd ht (hlive o)
              · have hmem : (a, u) ∈ successors file labels s :=
                  (successors_correct file labels s a u).mpr hstep
                rw [hsucc] at hmem
                cases hmem
            · exact ih rest _ hl p hp
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro t o hreach ht
              rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨u, ⟨a, hstep⟩, hrest⟩
              · subst heq
                exact absurd ht (hlive o)
              · have hmem : (a, u) ∈ successors file labels s :=
                  (successors_correct file labels s a u).mpr hstep
                exact ih _ _ hl (d, u) (List.mem_append_left _
                  (List.mem_map.mpr ⟨(a, u), hmem, rfl⟩)) t o hrest ht
            · exact ih _ _ hl p (List.mem_append_right _ hp)

/-- When the exploration is not limited, no path from a stack entry is longer than the entry's
remaining depth. -/
theorem explore_bounded_aux (P : Closed) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Leaves),
      (explore P.file labels budget stack acc).limited = false →
      ∀ p ∈ stack, ∀ n t, P.Path labels n p.2 t → n ≤ p.1 := by
  intro budget
  induction budget with
  | zero =>
      intro stack acc hl p hp
      simp only [explore] at hl
      split at hl
      · rename_i hempty
        simp only [List.isEmpty_iff] at hempty
        simp [hempty] at hp
      · simp at hl
  | succ budget ih =>
      intro stack acc hl p hp
      match stack with
      | [] => simp at hp
      | (depth, s) :: rest =>
          rcases explore_step P.file labels budget depth s rest acc with
            ⟨o, hc, hr⟩ | ⟨_, _, hr⟩ | ⟨hlive, _, hsucc, hr⟩ | ⟨hlive, d, hd, _, hr⟩ <;>
            rw [hr] at hl
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro n t hpath
              cases hpath with
              | refl => exact Nat.zero_le _
              | step hstep _ =>
                  obtain ⟨a, hstep⟩ := hstep
                  cases hstep with
                  | respond live _ => exact absurd hc (live o)
            · exact ih rest _ hl p hp
          · rw [explore_limited P.file labels budget rest _ rfl] at hl
            cases hl
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro n t hpath
              cases hpath with
              | refl => exact Nat.zero_le _
              | step hstep _ =>
                  rename_i u _
                  obtain ⟨a, hstep⟩ := hstep
                  have hmem : (a, u) ∈ successors P.file labels s :=
                    (successors_correct P.file labels s a u).mpr hstep
                  rw [hsucc] at hmem
                  cases hmem
            · exact ih rest _ hl p hp
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro n t hpath
              cases hpath with
              | refl => exact Nat.zero_le _
              | step hstep hpath' =>
                  rename_i m u
                  obtain ⟨a, hstep⟩ := hstep
                  have hmem : (a, u) ∈ successors P.file labels s :=
                    (successors_correct P.file labels s a u).mpr hstep
                  have := ih _ _ hl (d, u) (List.mem_append_left _
                    (List.mem_map.mpr ⟨(a, u), hmem, rfl⟩)) m t hpath'
                  simp only at this
                  rw [hd]
                  omega
            · exact ih _ _ hl p (List.mem_append_right _ hp)

/-- When the exploration is neither limited nor stuck, every state reachable from a stack entry
that is not halted has a successor. -/
theorem explore_progress_aux (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Leaves),
      (explore file labels budget stack acc).limited = false →
      (explore file labels budget stack acc).stuck = false →
      ∀ p ∈ stack, ∀ t, Spec.Reaches file labels p.2 t → (∀ o, t.control ≠ .halt o) →
        successors file labels t ≠ [] := by
  intro budget
  induction budget with
  | zero =>
      intro stack acc hl _ p hp
      simp only [explore] at hl
      split at hl
      · rename_i hempty
        simp only [List.isEmpty_iff] at hempty
        simp [hempty] at hp
      · simp at hl
  | succ budget ih =>
      intro stack acc hl hst p hp
      match stack with
      | [] => simp at hp
      | (depth, s) :: rest =>
          rcases explore_step file labels budget depth s rest acc with
            ⟨o, hc, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨hlive, d, _, hne, hr⟩ <;>
            rw [hr] at hl hst
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro t hreach ht
              have := reaches_halt hc hreach
              subst this
              exact absurd hc (ht o)
            · exact ih rest _ hl hst p hp
          · rw [explore_limited file labels budget rest _ rfl] at hl
            cases hl
          · rw [explore_stuck file labels budget rest _ rfl] at hst
            cases hst
          · rcases List.mem_cons.mp hp with rfl | hp
            · intro t hreach ht
              rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨u, ⟨a, hstep⟩, hrest⟩
              · subst heq
                exact hne
              · have hmem : (a, u) ∈ successors file labels s :=
                  (successors_correct file labels s a u).mpr hstep
                exact ih _ _ hl hst (d, u) (List.mem_append_left _
                  (List.mem_map.mpr ⟨(a, u), hmem, rfl⟩)) t hrest ht
            · exact ih _ _ hl hst p (List.mem_append_right _ hp)

/-! ## Closed programs -/

theorem Closed.explore_eq (P : Closed) (bounds : Bounds) :
    P.explore bounds = match P.start with
      | .error o => { ends := [(o, "")] }
      | .ok (s0, labels) => TV.explore P.file labels bounds.budget [(bounds.depth, s0)] {} := rfl

theorem Closed.ends_eq (P : Closed) (o : Outcome) (out : String) :
    P.Ends o out = match P.start with
      | .error o' => o = o' ∧ out = ""
      | .ok (s0, labels) =>
          ∃ s, Spec.Reaches P.file labels s0 s ∧ s.control = .halt o ∧ s.memory.stdout = out := rfl

theorem Closed.diverges_eq (P : Closed) :
    P.Diverges = match P.start with
      | .error _ => False
      | .ok (s0, labels) => ∃ f : Nat → State, f 0 = s0 ∧ ∀ n, P.Step labels (f n) (f (n + 1)) :=
  rfl

theorem Closed.stuck_eq (P : Closed) :
    P.Stuck = match P.start with
      | .error _ => False
      | .ok (s0, labels) => ∃ s, Spec.Reaches P.file labels s0 s ∧ (∀ o, s.control ≠ .halt o) ∧
          ∀ t, ¬ P.Step labels s t := rfl

theorem Closed.explore_sound (P : Closed) (bounds : Bounds) (e : Outcome × String)
    (h : e ∈ (P.explore bounds).ends) : P.Ends e.1 e.2 := by
  rw [Closed.explore_eq] at h
  rw [Closed.ends_eq]
  generalize P.start = st at h ⊢
  rcases st with o | ⟨s0, labels⟩
  · simp only [List.mem_singleton] at h
    subst h
    exact ⟨rfl, rfl⟩
  · exact explore_sound_aux P.file labels s0 _ _ _
      (by intro p hp; simp at hp; rw [hp]; exact .refl) (by simp) e h

theorem Closed.explore_complete (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) (o : Outcome) (out : String)
    (h : P.Ends o out) : (o, out) ∈ (P.explore bounds).ends := by
  rw [Closed.explore_eq] at hl ⊢
  rw [Closed.ends_eq] at h
  generalize P.start = st at h hl ⊢
  rcases st with o' | ⟨s0, labels⟩
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · obtain ⟨t, hreach, hc, rfl⟩ := h
    exact explore_complete_aux P.file labels _ _ _ hl (bounds.depth, s0) (by simp) t o hreach hc

theorem Closed.explore_terminates (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) : ¬ P.Diverges := by
  rw [Closed.explore_eq] at hl
  rw [Closed.diverges_eq]
  generalize P.start = st at hl ⊢
  rcases st with o | ⟨s0, labels⟩
  · exact id
  · rintro ⟨f, h0, hf⟩
    have hpath : ∀ n m, P.Path labels n (f m) (f (m + n)) := by
      intro n
      induction n with
      | zero => intro m; exact .refl _
      | succ n ihn =>
          intro m
          have := ihn (m + 1)
          rw [show m + 1 + n = m + (n + 1) by omega] at this
          exact .step (hf m) this
    have h1 := hpath (bounds.depth + 1) 0
    rw [h0, Nat.zero_add] at h1
    have := explore_bounded_aux P labels _ _ _ hl (bounds.depth, s0) (by simp)
      (bounds.depth + 1) (f (bounds.depth + 1)) h1
    simp at this

theorem Closed.explore_noStuck (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) (hs : (P.explore bounds).stuck = false) :
    ¬ P.Stuck := by
  rw [Closed.explore_eq] at hl hs
  rw [Closed.stuck_eq]
  generalize P.start = st at hl hs ⊢
  rcases st with o | ⟨s0, labels⟩
  · exact id
  · rintro ⟨t, hreach, hlive, hnone⟩
    have hne := explore_progress_aux P.file labels _ _ _ hl hs (bounds.depth, s0) (by simp) t
      hreach hlive
    obtain ⟨⟨a, u⟩, hmem⟩ := List.exists_mem_of_ne_nil _ hne
    exact hnone u ⟨a, (successors_correct P.file labels t a u).mp hmem⟩

end Silmaril.Proofs.Cerberus.TV
