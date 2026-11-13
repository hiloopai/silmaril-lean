module

public import Silmaril.Process.Mt.Drf.Defs

/-!
# Proof of the DRF-modulo-primitives bridge

Every run of the store-buffer machine (TSO or XL) from a certified start abstracts, buffered
values installed, to a run of the SC machine with atomic synchronisation. The simulation
invariant is: the certificate's invariant holds of the abstraction, and every buffered cell is
owned by its thread (`BufOwned`). Under it a thread's view agrees with the abstraction on the
cells it may read, a plain write installs exactly what the SC step writes, a synchronising step
(empty buffer) touches no buffered cell, and a flush does not change the abstraction (a flushed
store is the oldest buffered store to its cell).
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Drf

open Silmaril.Process.Mt.Drf

/-! ## Buffers -/

theorem or_none' {α : Type} (x : Option α) : x.or none = x := by cases x <;> rfl

theorem newest_append (b₁ b₂ : List Ent) (a : Nat) :
    newest (b₁ ++ b₂) a = (newest b₂ a).or (newest b₁ a) := by
  induction b₁ with
  | nil => simp [newest]
  | cons e b ih =>
    simp only [List.cons_append, newest, ih]
    cases newest b₂ a <;> cases newest b a <;> rfl

theorem newest_bar (b : List Ent) (a : Nat) : newest (b ++ [.bar]) a = newest b a := by
  rw [newest_append]; rfl

theorem newest_ents_none_or_mem (ws : List (Nat × Nat)) (w : Bool) (a : Nat) :
    newest (ents ws w) a = none ∨ ∃ p ∈ ws, p.1 = a := by
  induction ws with
  | nil => exact Or.inl rfl
  | cons p ws ih =>
    simp only [ents, List.map_cons, newest] at ih ⊢
    rcases ih with h | ⟨q, hq, hqa⟩
    · rw [h]
      by_cases hp : p.1 = a
      · exact Or.inr ⟨p, List.mem_cons_self, hp⟩
      · left; simp [Ent.val, hp]
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqa⟩

theorem newest_ents_isSome (ws : List (Nat × Nat)) (w : Bool) {a : Nat}
    (h : ∃ p ∈ ws, p.1 = a) : (newest (ents ws w) a).isSome := by
  induction ws with
  | nil => obtain ⟨p, hp, _⟩ := h; cases hp
  | cons q ws ih =>
    simp only [ents, List.map_cons, newest] at ih ⊢
    obtain ⟨p, hp, hpa⟩ := h
    rcases List.mem_cons.1 hp with rfl | hp'
    · cases newest (List.map (fun p => Ent.st p.1 p.2 w) ws) a <;> simp [Ent.val, hpa]
    · have := ih ⟨p, hp', hpa⟩
      cases h2 : newest (List.map (fun p => Ent.st p.1 p.2 w) ws) a <;> simp_all

theorem write_apply (m : Mem) (ws : List (Nat × Nat)) (w : Bool) (a : Nat) :
    m.write ws a = (newest (ents ws w) a).getD (m a) := by
  induction ws generalizing m with
  | nil => rfl
  | cons p ws ih =>
    simp only [Mem.write, ih, ents, List.map_cons, newest]
    cases h : newest (List.map (fun p => Ent.st p.1 p.2 w) ws) a with
    | some v => rfl
    | none =>
      by_cases hp : p.1 = a
      · subst hp; simp [Ent.val, Mem.set]
      · simp [Ent.val, Mem.set, hp, Ne.symm hp]

theorem newest_none_of_passes {b v : Nat} {w' : Bool} {pre : List Ent}
    (hp : Ent.passes (.st b v w') pre) : newest pre b = none := by
  induction pre with
  | nil => rfl
  | cons e pre ih =>
    have hp' : Ent.passes (.st b v w') pre := fun e' he' => hp e' (List.mem_cons_of_mem _ he')
    have he := hp e List.mem_cons_self
    simp only [newest, ih hp']
    cases e with
    | bar => exact he.elim
    | st a' v' w'' => simp [Ent.val, he.1]

/-! ## The abstraction -/

theorem upd_same {α : Type} (f : Nat → α) (t : Nat) (x : α) : upd f t x t = x := by
  simp [upd]

theorem upd_ne {α : Type} {f : Nat → α} {t u : Nat} {x : α} (h : u ≠ t) : upd f t x u = f u := by
  simp [upd, h]

theorem bufVal_congr {buf buf' : Nat → List Ent} {a : Nat} {us : List Nat}
    (h : ∀ u, newest (buf u) a = newest (buf' u) a) : bufVal buf a us = bufVal buf' a us := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [bufVal, ih, h u]

theorem bufVal_only {buf : Nat → List Ent} {a t : Nat} {us : List Nat}
    (h : ∀ u, u ≠ t → newest (buf u) a = none) :
    bufVal buf a us = if t ∈ us then newest (buf t) a else none := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [bufVal, ih, List.mem_cons]
    by_cases hu : u = t
    · subst hu
      cases newest (buf u) a <;> by_cases hm : u ∈ us <;> simp [hm]
    · rw [h u hu]
      have : ¬ t = u := fun e => hu e.symm
      simp [this]

theorem bufVal_none {buf : Nat → List Ent} {a : Nat} {us : List Nat}
    (h : ∀ u, newest (buf u) a = none) : bufVal buf a us = none := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [bufVal, ih, h u]

variable {S : Sys} {N : Nat} {R : Cfg S → Own → Prop}

theorem others_none (hc : Cert S N R) {C : BCfg S} {o : Own} (hR : R (C.abs N) o)
    (hb : BufOwned N C o) {t a : Nat} (ho : o t a) : ∀ u, u ≠ t → newest (C.buf u) a = none := by
  intro u hu
  cases hn : newest (C.buf u) a with
  | none => rfl
  | some v => exact (hc.disj _ _ hR u t a hu (hb u a (by simp [hn])).2 ho).elim

theorem unowned_none {C : BCfg S} {o : Own} (hb : BufOwned N C o) {a : Nat}
    (hn : ∀ u, ¬ o u a) : ∀ u, newest (C.buf u) a = none := by
  intro u
  cases h : newest (C.buf u) a with
  | none => rfl
  | some v => exact (hn u (hb u a (by simp [h])).2).elim

theorem abs_owned (hc : Cert S N R) {C : BCfg S} {o : Own} (hR : R (C.abs N) o)
    (hb : BufOwned N C o) {t a : Nat} (ht : t < N) (ho : o t a) :
    (C.abs N).mem a = view C.mem (C.buf t) a := by
  show (bufVal C.buf a (List.range N)).getD (C.mem a) = _
  rw [bufVal_only (others_none hc hR hb ho)]
  simp [List.mem_range, ht, view]

theorem abs_free {C : BCfg S} {a : Nat}
    (hn : ∀ u, newest (C.buf u) a = none) : (C.abs N).mem a = C.mem a := by
  show (bufVal C.buf a (List.range N)).getD (C.mem a) = _
  rw [bufVal_none hn]; rfl

theorem cfg_ext {C C' : Cfg S} (h1 : C.ts = C'.ts) (h2 : ∀ a, C.mem a = C'.mem a) : C = C' := by
  cases C; cases C'
  simp only at h1; subst h1
  have : _ := funext h2
  simp only at this; subst this; rfl

theorem abs_toB (C : Cfg S) : C.toB.abs N = C := by
  refine cfg_ext rfl fun a => ?_
  show (bufVal (fun _ => []) a (List.range N)).getD (C.mem a) = C.mem a
  rw [bufVal_none (fun _ => rfl)]; rfl

theorem abs_drained {C : BCfg S} (hd : C.Drained) : C.abs N = ⟨C.ts, C.mem⟩ := by
  refine cfg_ext rfl fun a => ?_
  show (bufVal C.buf a (List.range N)).getD (C.mem a) = C.mem a
  rw [bufVal_none (fun u => by rw [hd u]; rfl)]; rfl

/-! ## One step -/

/-- **The simulation step.** -/
theorem step (hc : Cert S N R) {M : Model} {C C' : BCfg S} {o : Own} (hR : R (C.abs N) o)
    (hb : BufOwned N C o) (h : BStep M S N C C') :
    ∃ o', R (C'.abs N) o' ∧ BufOwned N C' o' ∧
      (ScStep S N (C.abs N) (C'.abs N) ∨ C'.abs N = C.abs N) := by
  cases h with
  | @plain t rs ws w s' ht hs hr =>
    -- the view agrees with the abstraction on the cells read
    have hreads : (C.abs N).mem.Reads rs := by
      intro p hp
      rcases hc.rd _ _ hR t ht rs ws w s' hs p hp with ho | hn
      · rw [abs_owned hc hR hb ht ho]; exact hr p hp
      · have := unowned_none hb hn
        rw [abs_free this]
        have := hr p hp
        simpa [view, unowned_none hb hn t] using this
    obtain ⟨o', hR', hmono⟩ := hc.plain _ _ hR t ht rs ws w s' hs hreads
    have habs : BCfg.abs N ⟨upd C.ts t s', C.mem, upd C.buf t (C.buf t ++ ents ws w)⟩ =
        ⟨upd C.ts t s', (C.abs N).mem.write ws⟩ := by
      refine cfg_ext rfl fun a => ?_
      show (bufVal (upd C.buf t (C.buf t ++ ents ws w)) a (List.range N)).getD (C.mem a) =
        Mem.write (C.abs N).mem ws a
      rw [write_apply _ ws w]
      rcases newest_ents_none_or_mem ws w a with hn | ⟨p, hp, hpa⟩
      · rw [hn]
        have : ∀ u, newest (upd C.buf t (C.buf t ++ ents ws w) u) a = newest (C.buf u) a := by
          intro u
          by_cases hu : u = t
          · subst hu; simp [upd, newest_append, hn]
          · simp [upd, hu]
        rw [bufVal_congr this]; rfl
      · have ho : o t a := hpa ▸ hc.wr _ _ hR t ht rs ws w s' hs p hp
        have hoth := others_none hc hR hb ho
        obtain ⟨v, hn⟩ := Option.isSome_iff_exists.1 (newest_ents_isSome ws w ⟨p, hp, hpa⟩)
        rw [hn]
        rw [bufVal_only (t := t)]
        · simp [List.mem_range, ht, upd, newest_append, hn]
        · intro u hu; simpa [upd, hu] using hoth u hu
    refine ⟨o', habs ▸ hR', ?_, Or.inl (habs ▸ ScStep.plain ht hs hreads)⟩
    intro u a hs'
    dsimp only at hs'
    by_cases hu : u = t
    · subst hu
      rw [upd_same, newest_append] at hs'
      rcases newest_ents_none_or_mem ws w a with hn | ⟨p, hp, hpa⟩
      · rw [hn] at hs'
        simp only [Option.none_or] at hs'
        exact ⟨ht, hmono _ _ (hb u a hs').2⟩
      · exact ⟨ht, hmono _ _ (hpa ▸ hc.wr _ _ hR u ht rs ws w s' hs p hp)⟩
    · rw [upd_ne hu] at hs'
      exact ⟨(hb u a hs').1, hmono _ _ (hb u a hs').2⟩
  | @sfence t s' ht hs =>
    obtain ⟨o', hR', hmono⟩ := hc.sfence _ _ hR t ht s' hs
    have habs : BCfg.abs N ⟨upd C.ts t s', C.mem, upd C.buf t (C.buf t ++ [.bar])⟩ =
        ⟨upd C.ts t s', (C.abs N).mem⟩ := by
      refine cfg_ext rfl fun a => ?_
      show (bufVal _ a (List.range N)).getD (C.mem a) = (bufVal _ a (List.range N)).getD (C.mem a)
      rw [bufVal_congr (buf' := C.buf)]
      intro u; by_cases hu : u = t
      · subst hu; simp [upd, newest_bar]
      · simp [upd, hu]
    refine ⟨o', habs ▸ hR', ?_, Or.inl (habs ▸ ScStep.sfence ht hs)⟩
    intro u a hs'
    have : (newest (C.buf u) a).isSome := by
      by_cases hu : u = t
      · subst hu; simpa [upd, newest_bar] using hs'
      · simpa [upd, hu] using hs'
    exact ⟨(hb u a this).1, hmono _ _ (hb u a this).2⟩
  | @sync t rs ws ts' ht hs he hr =>
    have hfree : ∀ p ∈ rs ++ ws, ∀ u, newest (C.buf u) p.1 = none := by
      intro p hp u
      by_cases hu : u = t
      · subst hu; rw [he]; rfl
      · cases hn : newest (C.buf u) p.1 with
        | none => rfl
        | some v => exact (hc.syncFp _ _ hR t ht rs ws ts' hs p hp u hu
            (hb u p.1 (by simp [hn])).2).elim
    have hreads : (C.abs N).mem.Reads rs := by
      intro p hp
      rw [abs_free (hfree p (List.mem_append_left _ hp))]
      exact hr p hp
    obtain ⟨o', hR', hmono⟩ := hc.sync _ _ hR t ht rs ws ts' hs hreads
    have habs : BCfg.abs N ⟨ts', C.mem.write ws, C.buf⟩ = ⟨ts', (C.abs N).mem.write ws⟩ := by
      refine cfg_ext rfl fun a => ?_
      show (bufVal C.buf a (List.range N)).getD (C.mem.write ws a) = Mem.write (C.abs N).mem ws a
      rw [write_apply _ ws false, write_apply _ ws false]
      rcases newest_ents_none_or_mem ws false a with hn | ⟨p, hp, hpa⟩
      · rw [hn]; rfl
      · have := hfree p (List.mem_append_right _ hp)
        rw [hpa] at this
        rw [bufVal_none this, abs_free this]
        rfl
    refine ⟨o', habs ▸ hR', ?_, Or.inl (habs ▸ ScStep.sync ht hs hreads)⟩
    intro u a hs'
    have hu : u ≠ t := by rintro rfl; rw [he] at hs'; cases hs'
    exact ⟨(hb u a hs').1, hmono _ _ hu (hb u a hs').2⟩
  | @flush t pre e post hbuf hp hm =>
    cases e with
    | bar =>
      have hn : ∀ u a, newest (upd C.buf t (pre ++ post) u) a = newest (C.buf u) a := by
        intro u a
        by_cases hu : u = t
        · subst hu
          rw [upd_same, hbuf, newest_append, newest_append, newest]
          cases newest post a <;> rfl
        · simp [upd, hu]
      refine ⟨o, ?_, ?_, Or.inr ?_⟩
      · have : BCfg.abs N ⟨C.ts, Ent.apply C.mem .bar, upd C.buf t (pre ++ post)⟩ = C.abs N := by
          refine cfg_ext rfl fun a => ?_
          show (bufVal _ a (List.range N)).getD (C.mem a) = (bufVal _ a (List.range N)).getD _
          rw [bufVal_congr (fun u => hn u a)]
        rw [this]; exact hR
      · intro u a hs'; rw [hn] at hs'; exact hb u a hs'
      · refine cfg_ext rfl fun a => ?_
        show (bufVal _ a (List.range N)).getD (C.mem a) = (bufVal _ a (List.range N)).getD _
        rw [bufVal_congr (fun u => hn u a)]
    | st b v w =>
      have hpre := newest_none_of_passes hp
      have htb : (newest (C.buf t) b).isSome := by
        simp [hbuf, newest_append, newest, Ent.val]
      obtain ⟨htN, hob⟩ := hb t b htb
      have hoth := others_none hc hR hb hob
      -- other cells: unchanged buffers and memory
      have hother : ∀ a, a ≠ b → ∀ u,
          newest (upd C.buf t (pre ++ post) u) a = newest (C.buf u) a := by
        intro a hab u
        by_cases hu : u = t
        · subst hu
          rw [upd_same, hbuf, newest_append, newest_append, newest]
          have : Ent.val (.st b v w) a = none := by simp [Ent.val, Ne.symm hab]
          rw [this]; cases newest post a <;> rfl
        · simp [upd, hu]
      have hsub : ∀ u a, (newest (upd C.buf t (pre ++ post) u) a).isSome →
          (newest (C.buf u) a).isSome := by
        intro u a h
        by_cases hu : u = t
        · subst hu
          rw [upd_same, newest_append] at h
          rw [hbuf, newest_append, newest]
          cases h1 : newest post a <;> cases h2 : newest pre a <;> simp_all
        · simpa [upd, hu] using h
      have habs : BCfg.abs N ⟨C.ts, Ent.apply C.mem (.st b v w), upd C.buf t (pre ++ post)⟩ =
          C.abs N := by
        refine cfg_ext rfl fun a => ?_
        show (bufVal _ a (List.range N)).getD (Mem.set C.mem b v a) =
          (bufVal _ a (List.range N)).getD (C.mem a)
        by_cases hab : a = b
        · subst hab
          rw [bufVal_only (t := t), bufVal_only (t := t) hoth]
          · simp only [List.mem_range, htN, ite_true, upd, hbuf, newest_append, newest, hpre,
              Ent.val]
            cases newest post a <;> simp [Mem.set]
          · intro u hu; simpa [upd, hu] using hoth u hu
        · rw [bufVal_congr (hother a hab)]
          simp [Mem.set, hab]
      refine ⟨o, habs ▸ hR, fun u a h => hb u a (hsub u a h), Or.inr habs⟩

/-! ## Runs -/

theorem reach (hc : Cert S N R) {M : Model} {C C' : BCfg S} (h : BReach M S N C C') :
    ∀ {o : Own}, R (C.abs N) o → BufOwned N C o →
      ScReach S N (C.abs N) (C'.abs N) ∧ ∃ o', R (C'.abs N) o' ∧ BufOwned N C' o' := by
  induction h with
  | refl => intro o hR hb; exact ⟨Star.refl, o, hR, hb⟩
  | step h _ ih =>
    intro o hR hb
    obtain ⟨o', hR', hb', hs⟩ := step hc hR hb h
    obtain ⟨hr, rest⟩ := ih hR' hb'
    refine ⟨?_, rest⟩
    rcases hs with hs | hs
    · exact Star.step hs hr
    · rw [hs] at hr; exact hr

/-- **DRF modulo synchronisation ⇒ SC, under TSO and XL.** -/
theorem drf_reach (hc : Cert S N R) {M : Model} {C0 : Cfg S} {o : Own} (h0 : R C0 o)
    {C : BCfg S} (h : BReach M S N C0.toB C) :
    ScReach S N C0 (C.abs N) ∧ ∃ o', R (C.abs N) o' ∧ BufOwned N C o' := by
  have := reach hc h (o := o) (by rw [abs_toB]; exact h0) (fun t a h => by cases h)
  rwa [abs_toB] at this

theorem tso_le_xl {C C' : BCfg S} (h : BStep .tso S N C C') : BStep .xl S N C C' := by
  cases h with
  | plain ht hs hr => exact .plain ht hs hr
  | sfence ht hs => exact .sfence ht hs
  | sync ht hs he hr => exact .sync ht hs he hr
  | flush hb hp _ => exact .flush hb hp (Or.inl rfl)

theorem tso_reach_xl {C C' : BCfg S} (h : BReach .tso S N C C') : BReach .xl S N C C' := by
  induction h with
  | refl => exact Star.refl
  | step h _ ih => exact Star.step (tso_le_xl h) ih

end Silmaril.Proofs.Process.Mt.Drf
