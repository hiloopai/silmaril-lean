module

public import Silmaril.X86.Concurrency.Cir.Prim.Tasks.Defs

/-!
# Single-writer protocols on the TSO machine

A small thread-modular logic for programs in which **every cell has at most one writer
thread** (the seqlock and the SPSC ring). It works directly on the CIR-native TSO machine
(`Csl.OStep .tso`); no CSL ownership transfer is involved.

* **The world** `W`: for each thread the **log** of the stores it has issued (oldest first)
  and the number of them that have been **flushed**. The machine invariant `SW` says: each
  thread's buffer is the unflushed suffix of its log, every logged store is to a cell the
  thread owns (`Own`), and every owned cell of memory holds the value of the flushed prefix of
  its owner's log (over the start memory). Cells nobody owns keep their start value.
* **Reads** (`RdOk`): a thread reading its own cell sees its whole log (store forwarding), and
  a thread reading another thread's cell sees that thread's flushed prefix (TSO: a thread's
  buffer holds only its own cells).
* **Thread safety** `TSafe Gp t Q` (greatest fixed point, `TF`): the thread's every step is a
  read, or a write-back store to an owned cell, that keeps the protocol invariant `Gp`; its
  states are stable under the other threads' steps and flushes (`Rely`: other logs only grow,
  its own log is unchanged, flush counts only grow).
* **Soundness** (`sw_final`): from a start with empty buffers, if every thread is `TSafe` and
  `Gp` holds and is kept by flushes, then every finished, drained TSO state satisfies each
  thread's postcondition, and every owned cell holds the value of its owner's whole log.

The rules (`tsafe_skip`, `_seq`, `_assign`, `_ite`, `_load`, `_store`, `_loop`, `_chain`) let
the per-thread proofs follow the program text.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Sw

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-! ## Logs -/

/-- The value of the last store to `c` in a log. -/
def lastV : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | e :: l, c => (lastV l c).or (if e.1 = c then some e.2 else none)

/-- The value of cell `c` after the log `l`, over the heap `h`. -/
def cellAfter (h : Heap) (l : List (Nat × Nat)) (c : Nat) : Option Nat := (lastV l c).or (h c)

theorem lastV_append (l₁ l₂ : List (Nat × Nat)) (c : Nat) :
    lastV (l₁ ++ l₂) c = (lastV l₂ c).or (lastV l₁ c) := by
  induction l₁ with
  | nil => simp [lastV]
  | cons e l ih => simp only [List.cons_append, lastV, ih, Option.or_assoc]

theorem lastV_snoc (l : List (Nat × Nat)) (a v c : Nat) :
    lastV (l ++ [(a, v)]) c = if a = c then some v else lastV l c := by
  rw [lastV_append]; by_cases h : a = c <;> simp [lastV, h]

theorem cellAfter_snoc (h : Heap) (l : List (Nat × Nat)) (a v c : Nat) :
    cellAfter h (l ++ [(a, v)]) c = if a = c then some v else cellAfter h l c := by
  simp only [cellAfter, lastV_snoc]; split <;> rfl

theorem lastV_eq_none {l : List (Nat × Nat)} {c : Nat} (h : ∀ e ∈ l, e.1 ≠ c) :
    lastV l c = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [lastV, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), Option.none_or]
    simp [h e List.mem_cons_self]

/-- The buffer entries of a log. -/
def toEnts (l : List (Nat × Nat)) : List Ent := l.map fun e => .st e.1 e.2 false

theorem newest_toEnts (l : List (Nat × Nat)) (c : Nat) : newest (toEnts l) c = lastV l c := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [toEnts, List.map_cons, newest, lastV] at ih ⊢
    rw [ih]; rfl

/-! ## The world and the machine invariant -/

/-- Issued stores and flush counts, per thread. -/
structure W where
  log : Nat → List (Nat × Nat)
  fl : Nat → Nat

/-- Thread `t` issues the store `e`. -/
def W.push (g : W) (t : Nat) (e : Nat × Nat) : W := { g with log := upd g.log t (g.log t ++ [e]) }

/-- Thread `t`'s oldest buffered store is flushed. -/
def W.flush (g : W) (t : Nat) : W := { g with fl := upd g.fl t (g.fl t + 1) }

/-- The start: nothing issued. -/
def W.zero : W := ⟨fun _ => [], fun _ => 0⟩

/-- Flush counts are within the logs. -/
def WF (g : W) : Prop := ∀ u, g.fl u ≤ (g.log u).length

variable (Own : Nat → Nat → Prop) (init : Heap)

/-- **The single-writer machine invariant.** -/
def SW (C : OCfg) (g : W) : Prop :=
  (∀ t, C.buf t = toEnts ((g.log t).drop (g.fl t))) ∧ WF g ∧
  (∀ t, ∀ e ∈ g.log t, Own t e.1) ∧
  (∀ c, (∀ t, ¬ Own t c) → C.mem c = init c) ∧
  (∀ t c, Own t c → C.mem c = cellAfter init ((g.log t).take (g.fl t)) c)

/-- **What a read of `c` by `t` returns**: its own cell through its whole log, another thread's
cell through that thread's flushed prefix, an unowned cell its start value. -/
def RdOk (g : W) (t c v : Nat) : Prop :=
  (Own t c ∧ cellAfter init (g.log t) c = some v) ∨
  (∃ u, u ≠ t ∧ Own u c ∧ cellAfter init ((g.log u).take (g.fl u)) c = some v) ∨
  ((∀ u, ¬ Own u c) ∧ init c = some v)

/-- The labels a thread may take: reads, and write-back stores to owned cells. -/
def Allowed (t : Nat) : Lab → Prop
  | .rd .. => True
  | .wr _ .wb c _ _ => Own t c
  | _ => False

/-- The effect of an allowed label on the world. -/
def Step (g : W) (t : Nat) : Lab → W → Prop
  | .rd _ _ c _ v, g' => RdOk Own init g t c v ∧ g' = g
  | .wr _ _ c _ v, g' => g' = g.push t (c, v)
  | _, _ => False

/-- **The rely of thread `t`**: its log is unchanged, logs only grow, flush counts only grow. -/
def Rely (t : Nat) (g g' : W) : Prop :=
  g'.log t = g.log t ∧ (∀ u, g.log u <+: g'.log u) ∧ (∀ u, g.fl u ≤ g'.fl u) ∧ WF g'

/-- **The safety functional** of thread `t` under the protocol invariant `Gp`. -/
def TF (Gp : W → Prop) (t : Nat) (Q : Regs → W → Prop) (R : Stmt → Regs → W → Prop)
    (s : Stmt) (rs : Regs) (g : W) : Prop :=
  (s = .skip → Q rs g) ∧
  (∀ g', Rely t g g' → Gp g' → R s rs g') ∧
  (∀ s' rs', TStep s rs none s' rs' → R s' rs' g) ∧
  (∀ l s' rs', TStep s rs (some l) s' rs' → Gp g → WF g →
    Allowed Own t l ∧ ∀ g', Step Own init g t l g' → Gp g' ∧ R s' rs' g')

/-- **Thread safety** (greatest fixed point of `TF`). -/
def TSafe (Gp : W → Prop) (t : Nat) (Q : Regs → W → Prop) (s : Stmt) (rs : Regs) (g : W) :
    Prop :=
  ∃ R : Stmt → Regs → W → Prop, R s rs g ∧ ∀ s rs g, R s rs g → TF Own init Gp t Q R s rs g

variable {Own init}

/-! ## The fixed point -/

section Fix

variable {Gp : W → Prop} {t : Nat} {Q : Regs → W → Prop}

theorem TF.mono {R R' : Stmt → Regs → W → Prop} (hR : ∀ s rs g, R s rs g → R' s rs g)
    {s : Stmt} {rs : Regs} {g : W} (h : TF Own init Gp t Q R s rs g) :
    TF Own init Gp t Q R' s rs g :=
  ⟨h.1, fun g' r p => hR _ _ _ (h.2.1 g' r p), fun s' rs' st => hR _ _ _ (h.2.2.1 s' rs' st),
    fun l s' rs' st hg hw => ⟨(h.2.2.2 l s' rs' st hg hw).1,
      fun g' sg => ⟨((h.2.2.2 l s' rs' st hg hw).2 g' sg).1,
        hR _ _ _ ((h.2.2.2 l s' rs' st hg hw).2 g' sg).2⟩⟩⟩

theorem TSafe.unfold {s : Stmt} {rs : Regs} {g : W} (h : TSafe Own init Gp t Q s rs g) :
    TF Own init Gp t Q (TSafe Own init Gp t Q) s rs g := by
  obtain ⟨R, hr, hR⟩ := h
  exact TF.mono (fun s rs g h => ⟨R, h, hR⟩) (hR _ _ _ hr)

/-- Coinduction up to `TSafe`. -/
theorem TSafe.coind (R : Stmt → Regs → W → Prop)
    (hR : ∀ s rs g, R s rs g →
      TF Own init Gp t Q (fun s rs g => R s rs g ∨ TSafe Own init Gp t Q s rs g) s rs g)
    {s : Stmt} {rs : Regs} {g : W} (h : R s rs g) : TSafe Own init Gp t Q s rs g := by
  refine ⟨fun s rs g => R s rs g ∨ TSafe Own init Gp t Q s rs g, Or.inl h, ?_⟩
  rintro s rs g (h | h)
  · exact hR _ _ _ h
  · exact TF.mono (fun _ _ _ h => Or.inr h) h.unfold

theorem TSafe.stable {s : Stmt} {rs : Regs} {g g' : W} (h : TSafe Own init Gp t Q s rs g)
    (r : Rely t g g') (hg : Gp g') : TSafe Own init Gp t Q s rs g' :=
  h.unfold.2.1 g' r hg

theorem TSafe.post {rs : Regs} {g : W} (h : TSafe Own init Gp t Q .skip rs g) : Q rs g :=
  h.unfold.1 rfl

end Fix

/-! ## Rely facts -/

theorem rely_refl {t : Nat} {g : W} (hw : WF g) : Rely t g g :=
  ⟨rfl, fun _ => List.prefix_refl _, fun _ => Nat.le_refl _, hw⟩

theorem rely_trans {t : Nat} {g g' g'' : W} (h₁ : Rely t g g') (h₂ : Rely t g' g'') :
    Rely t g g'' :=
  ⟨h₂.1.trans h₁.1, fun u => (h₁.2.1 u).trans (h₂.2.1 u), fun u => (h₁.2.2.1 u).trans
    (h₂.2.2.1 u), h₂.2.2.2⟩

theorem wf_push {g : W} (hw : WF g) (u : Nat) (e : Nat × Nat) : WF (g.push u e) := by
  intro v
  simp only [W.push, upd]
  split
  · subst v; simp only [List.length_append]; exact Nat.le_succ_of_le (hw _)
  · exact hw v

theorem rely_push {t u : Nat} {g : W} (hw : WF g) (hu : u ≠ t) (e : Nat × Nat) :
    Rely t g (g.push u e) := by
  refine ⟨?_, fun v => ?_, fun v => Nat.le_refl _, wf_push hw u e⟩
  · simp [W.push, upd, Ne.symm hu]
  · simp only [W.push, upd]
    split
    · subst v; exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem wf_flush {g : W} (hw : WF g) {u : Nat} (hu : g.fl u < (g.log u).length) :
    WF (g.flush u) := by
  intro v
  simp only [W.flush, upd]
  split
  · subst v; exact hu
  · exact hw v

theorem rely_flush {t u : Nat} {g : W} (hw : WF g) (hu : g.fl u < (g.log u).length) :
    Rely t g (g.flush u) := by
  refine ⟨rfl, fun _ => List.prefix_refl _, fun v => ?_, wf_flush hw hu⟩
  simp only [W.flush, upd]
  by_cases h : v = u <;> simp [h]

/-! ## Soundness on the TSO machine -/

theorem view_own {mem : Heap} {l : List (Nat × Nat)} {f c : Nat}
    (hm : mem c = cellAfter init (l.take f) c) :
    view mem (toEnts (l.drop f)) c = cellAfter init l c := by
  simp only [view, newest_toEnts, hm, cellAfter]
  conv => rhs; rw [← List.take_append_drop f l]
  rw [lastV_append, Option.or_assoc]

theorem view_other {mem : Heap} {l : List (Nat × Nat)} {c : Nat} (h : ∀ e ∈ l, e.1 ≠ c) :
    view mem (toEnts l) c = mem c := by
  simp [view, newest_toEnts, lastV_eq_none h]

section Sound

variable {Gp : W → Prop} {Q : Nat → Regs → W → Prop}

/-- One TSO step keeps the invariant. -/
theorem sw_step {N : Nat} (hU : ∀ t u c, Own t c → Own u c → t = u)
    (hGf : ∀ g t, Gp g → WF g → g.fl t < (g.log t).length → Gp (g.flush t))
    {C C' : OCfg} (st : OStep .tso N C C') {g : W} (hsw : SW Own init C g) (hG : Gp g)
    (hT : ∀ t < N, TSafe Own init Gp t (Q t) (C.ts t).1 (C.ts t).2 g) :
    ∃ g', SW Own init C' g' ∧ Gp g' ∧
      ∀ t < N, TSafe Own init Gp t (Q t) (C'.ts t).1 (C'.ts t).2 g' := by
  obtain ⟨hbuf, hwf, hown, hfree, hmem⟩ := hsw
  cases st with
  | tau ht hs =>
    rename_i t s' rs'
    refine ⟨g, ⟨hbuf, hwf, hown, hfree, hmem⟩, hG, fun u hu => ?_⟩
    simp only [upd]
    split
    · subst u; exact (hT t ht).unfold.2.2.1 _ _ hs
    · exact hT u hu
  | buffered ht hs hm hd hc hok =>
    rename_i t l s' rs'
    have F := ((hT t ht).unfold.2.2.2 l s' rs' hs hG hwf)
    have others : ∀ g', Gp g' → (∀ u, u ≠ t → Rely u g g') →
        TSafe Own init Gp t (Q t) s' rs' g' →
        ∀ u < N, TSafe Own init Gp u (Q u) ((upd C.ts t (s', rs')) u).1
          ((upd C.ts t (s', rs')) u).2 g' := by
      intro g' hg' hr hs' u hu
      simp only [upd]
      split
      · subst u; exact hs'
      · rename_i hne; exact (hT u hu).stable (hr u hne) hg'
    cases l with
    | rd m fl c sz v =>
      have hv : view C.mem (C.buf t) c = some v := hok (c, v) (by simp [Lab.reads])
      have hrd : RdOk Own init g t c v := by
        by_cases ho : Own t c
        · refine Or.inl ⟨ho, ?_⟩
          rw [← hv, hbuf t, view_own (hmem t c ho)]
        · have hnb : ∀ e ∈ (g.log t).drop (g.fl t), e.1 ≠ c := fun e he hec =>
            ho (hec ▸ hown t e (List.mem_of_mem_drop he))
          rw [hbuf t, view_other hnb] at hv
          by_cases hx : ∃ u, Own u c
          · obtain ⟨u, hu⟩ := hx
            refine Or.inr (Or.inl ⟨u, fun e => ho (e ▸ hu), hu, ?_⟩)
            rw [← hv, hmem u c hu]
          · exact Or.inr (Or.inr ⟨fun u hu => hx ⟨u, hu⟩, by rw [← hv, hfree c
              (fun u hu => hx ⟨u, hu⟩)]⟩)
      obtain ⟨hg', hs'⟩ := F.2 g ⟨hrd, rfl⟩
      refine ⟨g, ⟨fun u => ?_, hwf, hown, hfree, hmem⟩, hg', others g hg'
        (fun _ _ => rely_refl hwf) hs'⟩
      simp only [upd, Lab.ents, List.append_nil]
      split
      · subst u; exact hbuf _
      · exact hbuf u
    | wr m fl c sz v =>
      have hfl : fl = .wb ∧ Own t c := by
        have := F.1; cases fl <;> simp_all [Allowed]
      obtain ⟨rfl, ho⟩ := hfl
      obtain ⟨hg', hs'⟩ := F.2 (g.push t (c, v)) rfl
      refine ⟨g.push t (c, v), ⟨fun u => ?_, wf_push hwf t _, fun u e he => ?_, hfree,
        fun u a hua => ?_⟩, hg', others _ hg' (fun u hu => rely_push hwf (Ne.symm hu) _) hs'⟩
      · simp only [upd, W.push, Lab.ents]
        split
        · subst u
          rw [hbuf, List.drop_append_of_le_length (hwf _)]
          simp [toEnts]
        · exact hbuf u
      · simp only [W.push, upd] at he
        split at he
        · subst u
          rcases List.mem_append.mp he with he | he
          · exact hown _ e he
          · simp only [List.mem_singleton] at he; subst he; exact ho
        · exact hown u e he
      · simp only [W.push, upd]
        split
        · subst u; rw [List.take_append_of_le_length (hwf _)]; exact hmem _ a hua
        · exact hmem u a hua
    | _ => simp [Allowed] at F
  | drained ht hs hm hd he hc hok =>
    rename_i t l s' rs'
    have F := ((hT t ht).unfold.2.2.2 l s' rs' hs hG hwf).1
    cases l <;> simp_all [Allowed, Lab.drains]
  | flush ht hb hp hmod =>
    rename_i t pre e post
    have hpre : pre = [] := by simpa using hmod
    subst hpre
    simp only [List.nil_append] at hb
    rw [hbuf t] at hb
    have hlt : g.fl t < (g.log t).length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hb
      simp [toEnts] at hb
    have hd : (g.log t).drop (g.fl t) = (g.log t)[g.fl t] :: (g.log t).drop (g.fl t + 1) :=
      List.drop_eq_getElem_cons hlt
    rw [hd] at hb
    simp only [toEnts, List.map_cons, List.cons.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hot : Own t (g.log t)[g.fl t].1 := hown t _ (List.getElem_mem _)
    refine ⟨g.flush t, ⟨fun u => ?_, wf_flush hwf hlt, hown, fun c hc => ?_, fun u c hu => ?_⟩,
      hGf g t hG hwf hlt, fun u hu => (hT u hu).stable (rely_flush hwf hlt) (hGf g t hG hwf hlt)⟩
    · simp only [upd, W.flush]
      split
      · subst u; rfl
      · exact hbuf u
    · have hne : c ≠ (g.log t)[g.fl t].1 := fun e => hc t (e ▸ hot)
      simp only [Ent.apply, hne, ite_false]
      exact hfree c hc
    · simp only [Ent.apply, W.flush, upd]
      by_cases hce : c = (g.log t)[g.fl t].1
      · have hut : u = t := hU _ _ _ hu (hce ▸ hot)
        subst hut
        simp only [hce, ite_true]
        rw [List.take_succ_eq_append_getElem hlt, cellAfter_snoc]
        simp
      · simp only [hce, ite_false]
        split
        · subst u
          rw [List.take_succ_eq_append_getElem hlt, cellAfter_snoc]
          simp only [Ne.symm hce, ite_false]
          exact hmem _ c hu
        · exact hmem u c hu

/-- **The invariant along a TSO run.** -/
theorem sw_reach {N : Nat} (hU : ∀ t u c, Own t c → Own u c → t = u)
    (hGf : ∀ g t, Gp g → WF g → g.fl t < (g.log t).length → Gp (g.flush t)) {C0 : Cfg}
    (hG0 : Gp W.zero)
    (hT0 : ∀ t < N, TSafe Own C0.mem Gp t (Q t) (C0.ts t).1 (C0.ts t).2 W.zero)
    {C : OCfg} (hr : OReach .tso N C0.toO C) :
    ∃ g, SW Own C0.mem C g ∧ Gp g ∧
      ∀ t < N, TSafe Own C0.mem Gp t (Q t) (C.ts t).1 (C.ts t).2 g := by
  have h0 : ∃ g, SW Own C0.mem C0.toO g ∧ Gp g ∧
      ∀ t < N, TSafe Own C0.mem Gp t (Q t) (C0.toO.ts t).1 (C0.toO.ts t).2 g :=
    ⟨W.zero, ⟨fun _ => rfl, fun _ => Nat.zero_le _, fun _ _ h => by simp [W.zero] at h,
      fun _ _ => rfl, fun _ _ _ => by simp [W.zero, cellAfter, lastV, Cfg.toO]⟩, hG0, hT0⟩
  clear hT0 hG0
  have key : ∀ A B, OReach .tso N A B → (∃ g, SW Own C0.mem A g ∧ Gp g ∧
      ∀ t < N, TSafe Own C0.mem Gp t (Q t) (A.ts t).1 (A.ts t).2 g) →
      ∃ g, SW Own C0.mem B g ∧ Gp g ∧
      ∀ t < N, TSafe Own C0.mem Gp t (Q t) (B.ts t).1 (B.ts t).2 g := by
    intro A B hr
    induction hr with
    | refl => exact id
    | step st _ ih =>
      intro h
      obtain ⟨g, hsw, hg, hT⟩ := h
      exact ih (sw_step hU hGf st hsw hg hT)
  exact key _ _ hr h0

/-- **Soundness**: at a finished, drained TSO state every postcondition holds, and every owned
cell holds the value of its owner's whole log. -/
theorem sw_final {N : Nat} (hU : ∀ t u c, Own t c → Own u c → t = u)
    (hGf : ∀ g t, Gp g → WF g → g.fl t < (g.log t).length → Gp (g.flush t)) {C0 : Cfg}
    (hG0 : Gp W.zero)
    (hT0 : ∀ t < N, TSafe Own C0.mem Gp t (Q t) (C0.ts t).1 (C0.ts t).2 W.zero)
    {C : OCfg} (hr : OReach .tso N C0.toO C) (hd : C.Drained)
    (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ g, Gp g ∧ (∀ t < N, Q t (C.ts t).2 g) ∧
      (∀ t c, Own t c → C.mem c = cellAfter C0.mem (g.log t) c) ∧
      (∀ t, g.fl t = (g.log t).length) := by
  obtain ⟨g, ⟨hbuf, hwf, _, _, hmem⟩, hg, hT⟩ := sw_reach hU hGf hG0 hT0 hr
  have hfl : ∀ t, (g.log t).length ≤ g.fl t := fun t => by
    have h := hbuf t
    rw [hd t] at h
    have : (g.log t).drop (g.fl t) = [] := by
      have h' := h.symm
      simpa only [toEnts, List.map_eq_nil_iff] using h'
    exact List.drop_eq_nil_iff.mp this
  refine ⟨g, hg, fun t ht => ?_, fun t c hc => ?_, fun t => Nat.le_antisymm (hwf t) (hfl t)⟩
  · have := hT t ht; rw [hfin t ht] at this; exact this.post
  · rw [hmem t c hc, List.take_of_length_le (hfl t)]

end Sound

/-! ## Rules -/

section Rules

variable {Gp : W → Prop} {t : Nat} {Q : Regs → W → Prop}

/-- A stable assertion. -/
def Stab (Gp : W → Prop) (t : Nat) (P : W → Prop) : Prop :=
  ∀ g g', P g → Rely t g g' → Gp g' → P g'

theorem tsafe_skip (hQ : ∀ rs, Stab Gp t (Q rs)) {rs : Regs} {g : W} (h : Q rs g) :
    TSafe Own init Gp t Q .skip rs g := by
  refine TSafe.coind (fun s rs g => s = .skip ∧ Q rs g) ?_ ⟨rfl, h⟩
  rintro s rs g ⟨rfl, hq⟩
  exact ⟨fun _ => hq, fun g' r hg => Or.inl ⟨rfl, hQ rs g g' hq r hg⟩,
    fun _ _ st => (by cases st), fun _ _ _ st => (by cases st)⟩

theorem tsafe_conseq {Q' : Regs → W → Prop} (hQ : ∀ rs g, Q rs g → Q' rs g) {s : Stmt}
    {rs : Regs} {g : W} (h : TSafe Own init Gp t Q s rs g) : TSafe Own init Gp t Q' s rs g := by
  obtain ⟨R, hr, hR⟩ := h
  exact ⟨R, hr, fun s rs g h => let F := hR s rs g h; ⟨fun e => hQ _ _ (F.1 e), F.2⟩⟩

theorem tsafe_seq {s u : Stmt} {rs : Regs} {g : W}
    (h : TSafe Own init Gp t (TSafe Own init Gp t Q u) s rs g) :
    TSafe Own init Gp t Q (.seq s u) rs g := by
  refine TSafe.coind (fun s0 rs g => ∃ s, s0 = .seq s u ∧
    TSafe Own init Gp t (TSafe Own init Gp t Q u) s rs g) ?_ ⟨s, rfl, h⟩
  rintro s0 rs g ⟨s, rfl, hs⟩
  have F := hs.unfold
  refine ⟨fun e => (by cases e), fun g' r hg => Or.inl ⟨s, rfl, hs.stable r hg⟩,
    fun s' rs' st => ?_, fun l s' rs' st hg hw => ?_⟩
  · cases st with
    | seq st => exact Or.inl ⟨_, rfl, F.2.2.1 _ _ st⟩
    | seqSkip => exact Or.inr hs.post
  · cases st with
    | seq st =>
      obtain ⟨ha, hk⟩ := F.2.2.2 l _ _ st hg hw
      exact ⟨ha, fun g' sg => ⟨(hk g' sg).1, Or.inl ⟨_, rfl, (hk g' sg).2⟩⟩⟩

theorem tsafe_assign {d : Reg} {e : Expr} {rs : Regs} {g : W}
    (h : TSafe Own init Gp t Q .skip (rs.set d (e.eval rs)) g) :
    TSafe Own init Gp t Q (.assign d e) rs g := by
  refine TSafe.coind (fun s0 rs g => s0 = .assign d e ∧
    TSafe Own init Gp t Q .skip (rs.set d (e.eval rs)) g) ?_ ⟨rfl, h⟩
  rintro s0 rs g ⟨rfl, hs⟩
  refine ⟨fun e => (by cases e), fun g' r hg => Or.inl ⟨rfl, hs.stable r hg⟩,
    fun s' rs' st => ?_, fun l s' rs' st => (by cases st)⟩
  cases st; exact Or.inr hs

theorem tsafe_ite {c : Expr} {s u : Stmt} {rs : Regs} {g : W}
    (h : TSafe Own init Gp t Q (if truthy (c.eval rs) then s else u) rs g) :
    TSafe Own init Gp t Q (.ite c s u) rs g := by
  refine TSafe.coind (fun s0 rs g => s0 = .ite c s u ∧
    TSafe Own init Gp t Q (if truthy (c.eval rs) then s else u) rs g) ?_ ⟨rfl, h⟩
  rintro s0 rs g ⟨rfl, hs⟩
  refine ⟨fun e => (by cases e), fun g' r hg => Or.inl ⟨rfl, hs.stable r hg⟩,
    fun s' rs' st => ?_, fun l s' rs' st => (by cases st)⟩
  cases st with
  | iteT hc => rw [hc] at hs; exact Or.inr hs
  | iteF hc => rw [hc] at hs; exact Or.inr hs

theorem tsafe_load {d : Reg} {m : Mode} {sz : Nat} {fl : Flav} {a : Expr} {rs : Regs}
    (P : W → Prop) (hP : Stab Gp t P)
    (h : ∀ g v, P g → Gp g → WF g → v < 2 ^ (8 * sz) → RdOk Own init g t (a.eval rs).toNat v →
      TSafe Own init Gp t Q .skip (rs.set d (BitVec.ofNat 64 v)) g)
    {g : W} (hg : P g) : TSafe Own init Gp t Q (.load d m sz fl a) rs g := by
  refine TSafe.coind (fun s0 rs0 g => s0 = .load d m sz fl a ∧ rs0 = rs ∧ P g) ?_ ⟨rfl, rfl, hg⟩
  rintro s0 rs0 g ⟨rfl, rfl, hp⟩
  refine ⟨fun e => (by cases e), fun g' r hg => Or.inl ⟨rfl, rfl, hP g g' hp r hg⟩,
    fun s' rs' st => (by cases st), fun l s' rs' st hG hw => ?_⟩
  cases st with
  | load hv =>
    refine ⟨trivial, fun g' sg => ?_⟩
    obtain ⟨hrd, hgg⟩ := sg
    exact hgg ▸ ⟨hG, Or.inr (h g _ hp hG hw hv hrd)⟩

theorem tsafe_store {m : Mode} {sz : Nat} {a v : Expr} {rs : Regs}
    (P : W → Prop) (hP : Stab Gp t P) (ho : Own t (a.eval rs).toNat)
    (h : ∀ g, P g → Gp g → WF g →
      Gp (g.push t ((a.eval rs).toNat, (v.eval rs).toNat % 2 ^ (8 * sz))) ∧
      TSafe Own init Gp t Q .skip rs
        (g.push t ((a.eval rs).toNat, (v.eval rs).toNat % 2 ^ (8 * sz))))
    {g : W} (hg : P g) : TSafe Own init Gp t Q (.store m sz .wb a v) rs g := by
  refine TSafe.coind (fun s0 rs0 g => s0 = .store m sz .wb a v ∧ rs0 = rs ∧ P g) ?_
    ⟨rfl, rfl, hg⟩
  rintro s0 rs0 g ⟨rfl, rfl, hp⟩
  refine ⟨fun e => (by cases e), fun g' r hg => Or.inl ⟨rfl, rfl, hP g g' hp r hg⟩,
    fun s' rs' st => (by cases st), fun l s' rs' st hG hw => ?_⟩
  cases st with
  | store =>
    refine ⟨ho, fun g' sg => ?_⟩
    simp only [Step] at sg
    subst sg
    exact ⟨(h g hp hG hw).1, Or.inr (h g hp hG hw).2⟩

theorem tsafe_loop {c : Expr} {b : Stmt} (Inv : Regs → W → Prop) (hI : ∀ rs, Stab Gp t (Inv rs))
    (hb : ∀ rs g, Inv rs g → truthy (c.eval rs) = true → TSafe Own init Gp t Inv b rs g)
    (hx : ∀ rs g, Inv rs g → truthy (c.eval rs) = false → TSafe Own init Gp t Q .skip rs g) :
    ∀ n rs g, Inv rs g → TSafe Own init Gp t Q (.loop n c b) rs g := by
  intro n rs g h
  refine TSafe.coind (fun s0 rs g => (∃ n, s0 = .loop n c b ∧ Inv rs g) ∨
    (∃ s n, s0 = .seq s (.loop n c b) ∧ TSafe Own init Gp t Inv s rs g)) ?_ (Or.inl ⟨n, rfl, h⟩)
  rintro s0 rs g (⟨n, rfl, hi⟩ | ⟨s, n, rfl, hs⟩)
  · refine ⟨fun e => (by cases e), fun g' r hg => Or.inl (Or.inl ⟨n, rfl, hI rs g g' hi r hg⟩),
      fun s' rs' st => ?_, fun l s' rs' st => (by cases st)⟩
    cases st with
    | loopT hc => exact Or.inl (Or.inr ⟨_, _, rfl, hb _ _ hi hc⟩)
    | loopF hc => exact Or.inr (hx _ _ hi hc)
  · have F := hs.unfold
    refine ⟨fun e => (by cases e), fun g' r hg => Or.inl (Or.inr ⟨s, n, rfl, hs.stable r hg⟩),
      fun s' rs' st => ?_, fun l s' rs' st hg hw => ?_⟩
    · cases st with
      | seq st => exact Or.inl (Or.inr ⟨_, _, rfl, F.2.2.1 _ _ st⟩)
      | seqSkip => exact Or.inl (Or.inl ⟨n, rfl, hs.post⟩)
    · cases st with
      | seq st =>
        obtain ⟨ha, hk⟩ := F.2.2.2 l _ _ st hg hw
        exact ⟨ha, fun g' sg => ⟨(hk g' sg).1, Or.inl (Or.inr ⟨_, _, rfl, (hk g' sg).2⟩)⟩⟩

/-- **A chain of statements** with an indexed invariant. -/
theorem tsafe_chain (Inv : Nat → Regs → W → Prop) :
    ∀ (l : List Stmt) (j : Nat),
    (∀ i (hi : i < l.length) rs g, Inv (j + i) rs g →
      TSafe Own init Gp t (Inv (j + i + 1)) l[i] rs g) →
    (∀ rs g, Inv (j + l.length) rs g → TSafe Own init Gp t Q .skip rs g) →
    ∀ rs g, Inv j rs g → TSafe Own init Gp t Q (Tv.chain l) rs g
  | [], j, _, hx, rs, g, h => hx rs g (by simpa using h)
  | x :: l, j, hs, hx, rs, g, h => by
    simp only [Tv.chain]
    apply tsafe_seq
    have h0 := hs 0 (by simp) rs g (by simpa using h)
    rw [List.getElem_cons_zero] at h0
    refine tsafe_conseq (Q := Inv (j + 1)) (fun rs g hi => ?_) h0
    refine tsafe_chain Inv l (j + 1) (fun i hi rs g h => ?_) (fun rs g h => hx rs g ?_) rs g hi
    · have := hs (i + 1) (by simp; omega) rs g (by
        rw [← Nat.add_assoc, Nat.add_right_comm]; simpa [Nat.add_assoc, Nat.add_comm 1] using h)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this
    · simpa [Nat.add_assoc, Nat.add_comm 1] using h

end Rules

/-! ## Derived rules -/

section Derived

variable {Gp : W → Prop} {t : Nat} {Q : Regs → W → Prop}

theorem tsafe_skip_of {s : Stmt} {rs : Regs} {g : W} (h : TSafe Own init Gp t Q s rs g) :
    TSafe Own init Gp t (TSafe Own init Gp t Q s) .skip rs g :=
  tsafe_skip (fun _ _ _ h r hg => h.stable r hg) h

theorem tsafe_seq_assign {d : Reg} {e : Expr} {u : Stmt} {rs : Regs} {g : W}
    (h : TSafe Own init Gp t Q u (rs.set d (e.eval rs)) g) :
    TSafe Own init Gp t Q (.seq (.assign d e) u) rs g :=
  tsafe_seq (tsafe_assign (tsafe_skip_of h))

theorem tsafe_seq_load {d : Reg} {m : Mode} {sz : Nat} {fl : Flav} {a : Expr} {u : Stmt}
    {rs : Regs} (P : W → Prop) (hP : Stab Gp t P)
    (h : ∀ g v, P g → Gp g → WF g → v < 2 ^ (8 * sz) → RdOk Own init g t (a.eval rs).toNat v →
      TSafe Own init Gp t Q u (rs.set d (BitVec.ofNat 64 v)) g)
    {g : W} (hg : P g) : TSafe Own init Gp t Q (.seq (.load d m sz fl a) u) rs g :=
  tsafe_seq (tsafe_load P hP (fun g v a b c d e => tsafe_skip_of (h g v a b c d e)) hg)

theorem tsafe_seq_store {m : Mode} {sz : Nat} {a v : Expr} {u : Stmt} {rs : Regs}
    (P : W → Prop) (hP : Stab Gp t P) (ho : Own t (a.eval rs).toNat)
    (h : ∀ g, P g → Gp g → WF g →
      Gp (g.push t ((a.eval rs).toNat, (v.eval rs).toNat % 2 ^ (8 * sz))) ∧
      TSafe Own init Gp t Q u rs (g.push t ((a.eval rs).toNat, (v.eval rs).toNat % 2 ^ (8 * sz))))
    {g : W} (hg : P g) : TSafe Own init Gp t Q (.seq (.store m sz .wb a v) u) rs g :=
  tsafe_seq (tsafe_store P hP ho (fun g a b c => ⟨(h g a b c).1, tsafe_skip_of (h g a b c).2⟩) hg)

theorem tsafe_seq_ite {c : Expr} {s₁ s₂ u : Stmt} {rs : Regs} {g : W}
    (h : TSafe Own init Gp t (TSafe Own init Gp t Q u)
      (if truthy (c.eval rs) then s₁ else s₂) rs g) :
    TSafe Own init Gp t Q (.seq (.ite c s₁ s₂) u) rs g :=
  tsafe_seq (tsafe_ite h)

theorem stab_log (X : List (Nat × Nat)) : Stab Gp t (fun g => g.log t = X) :=
  fun _ _ h r _ => r.1.trans h

theorem stab_and {P P' : W → Prop} (h : Stab Gp t P) (h' : Stab Gp t P') :
    Stab Gp t (fun g => P g ∧ P' g) :=
  fun g g' p r hg => ⟨h g g' p.1 r hg, h' g g' p.2 r hg⟩

theorem stab_const (p : Prop) : Stab Gp t (fun _ => p) := fun _ _ h _ _ => h

/-- A read of an own cell sees the whole own log. -/
theorem rdOk_own (hU : ∀ t u c, Own t c → Own u c → t = u) {g : W} {c v : Nat} (ho : Own t c)
    (h : RdOk Own init g t c v) : cellAfter init (g.log t) c = some v := by
  rcases h with h | ⟨u, hu, hou, _⟩ | ⟨hn, _⟩
  · exact h.2
  · exact absurd (hU _ _ _ hou ho) hu
  · exact absurd ho (hn t)

/-- A read of another thread's cell sees that thread's flushed prefix. -/
theorem rdOk_other (hU : ∀ t u c, Own t c → Own u c → t = u) {g : W} {u c v : Nat}
    (ho : Own u c) (hne : u ≠ t) (h : RdOk Own init g t c v) :
    cellAfter init ((g.log u).take (g.fl u)) c = some v := by
  rcases h with h | ⟨u', _, hou, h⟩ | ⟨hn, _⟩
  · exact absurd (hU _ _ _ ho h.1) hne
  · rw [hU _ _ _ ho hou]; exact h
  · exact absurd ho (hn u)

end Derived

theorem push_log (g : W) (t : Nat) (e : Nat × Nat) : (g.push t e).log t = g.log t ++ [e] := by
  simp [W.push, upd]

theorem push_log_ne (g : W) {t u : Nat} (h : u ≠ t) (e : Nat × Nat) :
    (g.push t e).log u = g.log u := by
  simp [W.push, upd, h]

theorem push_fl (g : W) (t : Nat) (e : Nat × Nat) : (g.push t e).fl = g.fl := rfl

/-! ## Start heaps -/

theorem heapOf_find {l : List (Nat × Nat)} {a : Nat} (h : (a, 0) ∈ l)
    (hu : ∀ p ∈ l, p.1 = a → p.2 = 0) (h0 : Heap) :
    Prim.Clients.heapOf l h0 a = some 0 := by
  simp only [Prim.Clients.heapOf]
  cases hf : l.find? (·.1 == a) with
  | none =>
    have := List.find?_eq_none.mp hf _ h
    simp at this
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpa : p.1 = a := by simpa using List.find?_some hf
    simp [hu p hp hpa]

/-! ## Register arithmetic -/

theorem bv_eq_ofNat {w : Word} {x : Nat} (hx : x < 2 ^ 64) (h : w.toNat = x) :
    w = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem eval_at {rs : Regs} {r : Reg} {x : Nat} (d : Nat) (h : rs r = BitVec.ofNat 64 x)
    (hx : x + d < 2 ^ 64) : ((Prim.at_ r d).eval rs).toNat = x + d := by
  simp only [Prim.at_, Expr.eval, BinOp.eval, h, BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : x < 2 ^ 64 := by omega
  have h2 : d < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt hx]

theorem eval_at' (rs : Regs) (r : Reg) (d : Nat) :
    ((Prim.at_ r d).eval rs).toNat = ((rs r).toNat + d) % 2 ^ 64 := by
  simp only [Prim.at_, Expr.eval, BinOp.eval, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp [Nat.add_mod]

theorem eval_reg_mod {rs : Regs} {r : Reg} {v : Nat} (h : rs r = BitVec.ofNat 64 v)
    (hv : v < 2 ^ 32) : ((Expr.reg r).eval rs).toNat % 2 ^ (8 * 4) = v := by
  simp only [Expr.eval, h, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by simpa using hv)

theorem toNat_mask32 (rs : Regs) (e : Expr) :
    ((TvCfg.mask32 e).eval rs).toNat = (e.eval rs).toNat % 2 ^ 32 := by
  simp only [TvCfg.mask32, Expr.eval, BinOp.eval, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (4294967295 : Nat) % 2 ^ 64 = 2 ^ 32 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem truthy_eq (rs : Regs) (a b : Expr) :
    truthy ((Expr.bin .eq a b).eval rs) = decide (a.eval rs = b.eval rs) := by
  simp only [Expr.eval, BinOp.eval, truthy]
  split <;> simp_all

theorem truthy_notE (rs : Regs) (e : Expr) :
    truthy ((TvCfg.notE e).eval rs) = !(truthy (e.eval rs)) := by
  simp only [TvCfg.notE, truthy_eq]
  simp only [truthy, Expr.eval]
  by_cases h : e.eval rs = BitVec.ofNat 64 0 <;> simp [h]

theorem bv_eq_iff (a b : Word) : a = b ↔ a.toNat = b.toNat := BitVec.toNat_inj.symm

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Sw
