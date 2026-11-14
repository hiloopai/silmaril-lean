module

public import Silmaril.X86.Concurrency.Cir.Pool.Run.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Heap

/-!
# Proofs: concrete pool runs are TSO runs (non-vacuity)

* `blkSucc_sound`: the block step is a `TStep` whose cells are mapped and whose reads agree with
  the view;
* `blkC_sound`: so a block step of a concrete configuration is an `OStep .tso` (`buffered`);
* `runT_reach`, `runAll_reach`: a run of the schedule is a TSO run (the other steps are
  `tsoStepT`, by `Robust.tsoStepT_sound`);
* `memOf_dom`, `mem_dom`: the start configuration's cells as a finite list.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool
open Silmaril.X86.Concurrency.Cir.Pool.Run
open Silmaril.X86.Concurrency.Cir.Robust (CSt memOf tsoStepT rget rlist)
open Silmaril.X86.Concurrency.Cir.Mutex (Iface)

theorem rget_rlist (rs : Regs) : rget (rlist rs) = rs := by
  funext r; cases r <;> rfl

/-- The cells of a block's input list paired with view values. -/
theorem cellVals_map_val : ∀ {cs : List (Nat × Nat)} {f : Nat → Nat} {c : Nat × Nat × Nat},
    c ∈ cellVals cs (cs.map fun d => f d.1) → c.2.2 = f c.1 ∧ ∃ d ∈ cs, d.1 = c.1
  | [], _, _, h => by simp [cellVals] at h
  | d :: cs, f, c, h => by
    simp only [List.map_cons, cellVals, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, d, List.mem_cons_self .., rfl⟩
    · obtain ⟨e, d', hd', e'⟩ := cellVals_map_val h
      exact ⟨e, d', List.mem_cons_of_mem _ hd', e'⟩

/-- **The block step is sound.** -/
theorem blkSucc_sound {fn : List Nat → List Nat} {mem vw : Heap} :
    ∀ {s : Stmt} {rs : Regs} {l : Lab} {s' : Stmt} {rs' : Regs},
      blkSucc fn mem vw s rs = some (l, s', rs') →
      TStep s rs (some l) s' rs' ∧ (∀ a, l.Touches a → (mem a).isSome) ∧ l.okH vw ∧
        l.isMem = true ∧ l.drains = false
  | .local b, rs, l, s', rs', h => by
    simp only [blkSucc] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨hr, hin⟩, hout⟩, hlen⟩, hspec⟩ := hc
      cases h
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · exact TStep.blk (rvs := []) hspec (by simp) (by simp [hr]) hlen
      · intro a ha
        rcases ha with ⟨v, hv⟩ | hw
        · simp only [Lab.reads, List.mem_map] at hv
          obtain ⟨c, hc, e⟩ := hv
          obtain ⟨-, d, hd, ed⟩ := cellVals_map_val (f := fun a => (vw a).getD 0) hc
          have := hin d hd
          simp only [Prod.mk.injEq] at e
          rw [← e.1, ← ed]; exact this.2
        · simp only [Lab.wval] at hw
          obtain ⟨c, hc, ec⟩ := cellLast_some hw
          obtain ⟨d, hd, ed⟩ := cellVals_fst hc
          rw [← ec, ← ed]; exact hout d hd
      · intro p hp
        simp only [Lab.reads, List.mem_map] at hp
        obtain ⟨c, hc, rfl⟩ := hp
        obtain ⟨e, d, hd, ed⟩ := cellVals_map_val (f := fun a => (vw a).getD 0) hc
        have := (hin d hd).1
        simp only
        rw [e, ← ed]
        cases e2 : vw d.1 with
        | none => rw [e2] at this; cases this
        | some w => rfl
    · cases h
  | .seq s t, rs, l, s', rs', h => by
    simp only [blkSucc, Option.map_eq_some_iff] at h
    obtain ⟨⟨l0, s0, r0⟩, h0, e⟩ := h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    obtain ⟨st, a, b, c, d⟩ := blkSucc_sound h0
    exact ⟨TStep.seq st, a, b, c, d⟩
  | .skip, _, _, _, _, h | .assign .., _, _, _, _, h | .load .., _, _, _, _, h
  | .store .., _, _, _, _, h | .rmw .., _, _, _, _, h | .fence _, _, _, _, _, h
  | .futexWait .., _, _, _, _, h | .futexWake .., _, _, _, _, h | .spawn _, _, _, _, _, h
  | .join _, _, _, _, _, h | .ite .., _, _, _, _, h | .loop .., _, _, _, _, h => by
    simp [blkSucc] at h

theorem th_setTh {c : CSt} {t : Nat} (ht : t < c.ts.length) (s : Stmt) (rs : Regs) (u : Nat) :
    (c.setTh t s rs).th u = upd c.th t (s, rs) u := by
  simp only [CSt.th, CSt.setTh, upd, List.getElem?_set]
  by_cases hu : u = t
  · subst hu; simp [ht, rget_rlist]
  · simp [Ne.symm hu, hu]

theorem getD_set {l : List (List Ent)} {t : Nat} (ht : t < l.length) (x : List Ent) (u : Nat) :
    (l.set t x).getD u [] = upd (fun u => l.getD u []) t x u := by
  simp only [upd, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hu : u = t
  · subst hu; simp [ht]
  · simp [Ne.symm hu, hu]

/-- **A block step of a concrete configuration is a TSO step.** -/
theorem blkC_sound {fn : List Nat → List Nat} {N : Nat} {c d : CSt} {t : Nat} (htN : t < N)
    (hb : t < c.buf.length) (hts : t < c.ts.length) (h : blkC fn c t = some d) :
    OStep .tso N c.ocfg d.ocfg := by
  unfold blkC at h
  split at h
  · rename_i l s' rs' e
    cases h
    obtain ⟨st, hc, hok, hm, hd⟩ := blkSucc_sound e
    have := OStep.buffered (M := .tso) (N := N) (C := c.ocfg) htN st hm hd hc hok
    have eq : ({ c.setTh t s' rs' with buf := c.buf.set t (c.bufT t ++ l.ents) } : CSt).ocfg =
        (⟨upd c.ocfg.ts t (s', rs'), c.ocfg.mem,
          upd c.ocfg.buf t (c.ocfg.buf t ++ l.ents)⟩ : OCfg) := by
      simp only [CSt.ocfg]
      congr 1
      · funext u; exact th_setTh hts s' rs' u
      · funext u; exact getD_set hb _ u
    rw [eq]; exact this
  · cases h

/-- **Running one thread follows a TSO run.** -/
theorem runT_reach {fn : List Nat → List Nat} {N t : Nat} :
    ∀ (f : Nat) (c : CSt), OReach .tso N c.ocfg (runT fn N t f c).ocfg
  | 0, _ => .refl
  | f + 1, c => by
    simp only [runT]
    split
    · rename_i hc
      obtain ⟨htN, hb, hts⟩ := hc
      split
      · rename_i d hd
        exact .step (blkC_sound htN hb hts hd) (runT_reach f d)
      · split
        · rename_i d hd
          exact .step (Robust.tsoStepT_sound htN hb (List.mem_of_getElem? hd)) (runT_reach f d)
        · exact .refl
    · exact .refl

theorem runAll_reach {fn : List Nat → List Nat} {N fuel : Nat} :
    ∀ (ts : List Nat) (c : CSt), OReach .tso N c.ocfg (runAll fn N fuel c ts).ocfg
  | [], _ => .refl
  | t :: ts, c => by
    simp only [runAll]
    exact star_trans (runT_reach fuel c) (runAll_reach ts _)
where
  star_trans {a b c : OCfg} (h₁ : OReach .tso N a b) (h₂ : OReach .tso N b c) :
      OReach .tso N a c := by
    induction h₁ with
    | refl => exact h₂
    | step h _ ih => exact .step h (ih h₂)

/-- **A run of a schedule of slices is a TSO run.** -/
theorem runS_reach {fn : List Nat → List Nat} {N : Nat} :
    ∀ (l : List (Nat × Nat)) (c : CSt), OReach .tso N c.ocfg (runS fn N c l).ocfg
  | [], _ => .refl
  | (t, f) :: l, c => by
    simp only [runS]
    exact runAll_reach.star_trans (runT_reach f c) (runS_reach l _)

/-! ## The start configuration's cells -/

theorem memOf_filterMap (H : Heap) : ∀ (D : List Nat) (a : Nat),
    memOf (D.filterMap fun a => (H a).map (a, ·)) a = if a ∈ D then H a else none
  | [], a => by simp [memOf]
  | b :: D, a => by
    have ih := memOf_filterMap H D a
    simp only [List.filterMap_cons, List.mem_cons]
    by_cases hb : a = b
    · subst hb
      cases e : H a with
      | none =>
        simp only [Option.map_none, ih, e]
        split <;> simp
      | some w => simp [memOf]
    · cases e : H b with
      | none => simp only [Option.map_none, ih, hb, false_or]
      | some w =>
        have : (b == a) = false := by simpa using Ne.symm hb
        simp only [Option.map_some, memOf, List.find?_cons, this] at ih ⊢
        simp only [ih, hb, false_or]

theorem memOf_dom {H : Heap} {D : List Nat} (hD : ∀ a, (H a).isSome → a ∈ D) (a : Nat) :
    memOf (D.filterMap fun a => (H a).map (a, ·)) a = H a := by
  rw [memOf_filterMap]
  split
  · rfl
  · rename_i h
    cases e : H a with
    | none => rfl
    | some w => exact absurd (hD a (by simp [e])) h

open Wp in
/-- The cells of the linked pool are in `dom`. -/
theorem link_dom (P : Wp) (M : Iface) (L : Nat) :
    ∀ a, ((P.client.link M L).mem a).isSome → a ∈ dom P M := by
  intro a ha
  have hmem : (P.client.link M L).mem = Heap.union P.mem0 (Heap.union (M.init P.m) Heap.empty) :=
    rfl
  rw [hmem] at ha
  simp only [dom, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap]
  cases e0 : P.mem0 a with
  | none =>
    rw [union_none e0] at ha
    cases e1 : M.init P.m a with
    | none => rw [union_none e1] at ha; simp [Heap.empty] at ha
    | some w =>
      have := M.init_dom P.m a (by simp [e1])
      exact Or.inl (Or.inl ⟨a - P.m, by omega, by omega⟩)
  | some w =>
    simp only [Wp.mem0, union_or] at e0
    cases e1 : P.ctlH 0 0 0 a with
    | some w' =>
      have := ctlH_some (P := P) (k := 0) (d := 0) (e := 0) (a := a) (by rw [e1]; rfl)
      refine Or.inl (Or.inr ?_)
      simp only [Wp.ctl, List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
      rcases this with h | h | h <;> simp [h]
    | none =>
      rw [e1] at e0
      simp only [Option.none_or] at e0
      cases e2 : P.cursH a with
      | some w' =>
        simp only [Wp.cursH] at e2
        split at e2
        · rename_i hh
          obtain ⟨t, ht, et⟩ := List.any_eq_true.mp hh
          refine Or.inl (Or.inr ?_)
          simp only [Wp.ctl, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨t, List.mem_range.mp ht, by simpa using et⟩
        · cases e2
      | none =>
        rw [e2] at e0
        simp only [Option.none_or] at e0
        obtain ⟨j, hj⟩ := jobH_some (P := P) (σ := fun _ => .fresh) (a := a) (by rw [e0]; rfl)
        obtain ⟨hf, hjn⟩ := owner_spec hj
        unfold Wp.fpB at hf
        rw [List.getElem?_eq_getElem hjn] at hf
        exact Or.inr ⟨_, List.getElem_mem hjn, by simpa using hf⟩

theorem start_th (P : Wp) (M : Iface) (L : Nat) (t : Nat) :
    (start P M L).th t = (if t < P.K then P.body (M.lock L) (M.unlock L) t else .skip,
      Regs.zero) := by
  simp only [start, Robust.start, CSt.th, List.map_map, List.getElem?_map]
  by_cases ht : t < P.K
  · simp [ht, rget_rlist]
  · simp [ht]

/-- **The concrete start is the linked pool.** -/
theorem start_cfg (P : Wp) (M : Iface) (L : Nat) : (start P M L).cfg = P.client.link M L := by
  simp only [CSt.cfg]
  congr 1
  · funext t
    rw [start_th]
    rfl
  · funext a
    exact memOf_dom (link_dom P M L) a

theorem start_toO (P : Wp) (M : Iface) (L : Nat) :
    (start P M L).ocfg = (P.client.link M L).toO := by
  rw [← start_cfg, Robust.start_toO]
  simp [start, Robust.start]

/-- A configuration whose Boolean checks pass is drained and finished. -/
theorem final_of_checks {N : Nat} {d : CSt} (h : (d.doneB N && d.drainedB) = true) :
    d.ocfg.Drained ∧ ∀ t < N, (d.ocfg.ts t).1 = .skip := by
  simp only [Bool.and_eq_true, Robust.CSt.doneB, Robust.CSt.drainedB, List.all_eq_true,
    List.mem_range] at h
  refine ⟨fun t => ?_, fun t ht => TvCfg.sbeq_eq (h.1 t ht)⟩
  simp only [CSt.ocfg, List.getD_eq_getElem?_getD]
  cases e : d.buf[t]? with
  | none => rfl
  | some b =>
    have := h.2 b (List.mem_of_getElem? e)
    simpa using this

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
