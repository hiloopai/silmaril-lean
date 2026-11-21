module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Refine

/-!
# Process-level threads: static sync safety

`syncSafe_of_static`: the syntactic conditions `SProg.Static` (literal
addresses in mapped cells, joins of spawnable threads, spawns only by the main thread, never
under a loop, at most once each) imply `SProg.SyncSafe`, so `refines` applies to every such
program without a semantic side proof.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd Star)
open Silmaril.X86.Concurrency.Cir.Proc

/-! ## Cells of local blocks -/

theorem mem_cellVals' : ∀ {cs : List (Nat × Nat)} {vs : List Nat} {c : Nat × Nat × Nat},
    c ∈ cellVals cs vs → (c.1, c.2.1) ∈ cs
  | [], _, _, h => by simp [cellVals] at h
  | _ :: _, [], _, h => by simp [cellVals] at h
  | d :: cs, v :: vs, c, h => by
    simp only [cellVals, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (mem_cellVals' h)

theorem cellLast_mem : ∀ {cs : List (Nat × Nat × Nat)} {a : Nat}, (cellLast cs a).isSome →
    ∃ c ∈ cs, c.1 = a
  | [], _, h => by simp [cellLast] at h
  | c :: cs, a, h => by
    simp only [cellLast, Option.isSome_or] at h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨d, hd, e⟩ := cellLast_mem h; exact ⟨d, List.mem_cons_of_mem _ hd, e⟩
    · split at h
      · rename_i e; exact ⟨c, List.mem_cons_self, e⟩
      · cases h

/-! ## Static properties along thread steps -/

theorem lsf_of_nil : ∀ {s : Stmt}, s.spawns = [] → s.loopSpawnFree = true
  | .seq s t, h | .ite _ s t, h => by
    simp only [Stmt.spawns, List.append_eq_nil_iff] at h
    simp [Stmt.loopSpawnFree, lsf_of_nil h.1, lsf_of_nil h.2]
  | .loop _ _ b, h => by simp only [Stmt.spawns] at h; simp [Stmt.loopSpawnFree, h]
  | .skip, _ | .assign .., _ | .load .., _ | .store .., _ | .rmw .., _ | .fence _, _
  | .futexWait .., _ | .futexWake .., _ | .spawn _, _ | .join _, _ | .local _, _ => rfl

theorem lit_pres {D : List Nat} {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs l s' rs') (hl : s.litIn D = true) : s'.litIn D = true := by
  induction h <;> simp_all [Stmt.litIn]

theorem joins_pres {N : Nat} {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs l s' rs') (hl : s.joinsIn N = true) : s'.joinsIn N = true := by
  induction h <;> simp_all [Stmt.joinsIn]

theorem join_label {N : Nat} {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs l s' rs') (hl : s.joinsIn N = true) {u : Nat} (hu : l = some (.join u)) :
    0 < u ∧ u < N := by
  induction h <;> simp_all [Stmt.joinsIn]

theorem spawn_pres {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs l s' rs') (hl : s.loopSpawnFree = true) :
    s'.loopSpawnFree = true ∧ s'.spawns.Sublist s.spawns ∧
      ∀ u, l = some (.spawn u) → (u :: s'.spawns).Sublist s.spawns := by
  induction h with
  | spawn => exact ⟨rfl, List.nil_sublist _, fun u hu => by cases hu; exact List.Sublist.refl _⟩
  | seq _ ih =>
    simp only [Stmt.loopSpawnFree, Bool.and_eq_true] at hl
    obtain ⟨h1, h2, h3⟩ := ih hl.1
    refine ⟨by simp [Stmt.loopSpawnFree, h1, hl.2], ?_, fun u hu => ?_⟩
    · exact List.Sublist.append h2 (List.Sublist.refl _)
    · exact List.Sublist.append (h3 u hu) (List.Sublist.refl _)
  | seqSkip =>
    simp only [Stmt.loopSpawnFree, Bool.and_eq_true] at hl
    exact ⟨hl.2, by simp [Stmt.spawns], fun u hu => by cases hu⟩
  | iteT =>
    simp only [Stmt.loopSpawnFree, Bool.and_eq_true] at hl
    exact ⟨hl.1, List.sublist_append_left _ _, fun u hu => by cases hu⟩
  | iteF =>
    simp only [Stmt.loopSpawnFree, Bool.and_eq_true] at hl
    exact ⟨hl.2, List.sublist_append_right _ _, fun u hu => by cases hu⟩
  | loopT =>
    simp only [Stmt.loopSpawnFree, List.isEmpty_iff] at hl
    refine ⟨by simp [Stmt.loopSpawnFree, lsf_of_nil hl, hl], by simp [Stmt.spawns, hl],
      fun u hu => by cases hu⟩
  | loopF => exact ⟨rfl, List.nil_sublist _, fun u hu => by cases hu⟩
  | _ => exact ⟨rfl, List.nil_sublist _, fun u hu => by cases hu⟩

theorem load_addr {D : List Nat} {d : Reg} {m : Mode} {sz : Nat} {fl : Flav} {a : Expr}
    {rs : Regs} (h : (Stmt.load d m sz fl a).litIn D = true) : (a.eval rs).toNat ∈ D := by
  cases a <;> simp_all [Stmt.litIn, Expr.eval]

theorem store_addr {D : List Nat} {m : Mode} {sz : Nat} {fl : Flav} {a v : Expr}
    {rs : Regs} (h : (Stmt.store m sz fl a v).litIn D = true) : (a.eval rs).toNat ∈ D := by
  cases a <;> simp_all [Stmt.litIn, Expr.eval]

theorem rmw_addr {D : List Nat} {d : Reg} {m : Mode} {sz : Nat} {op : RmwOp} {a arg : Expr}
    {rs : Regs} (h : (Stmt.rmw d m sz op a arg).litIn D = true) : (a.eval rs).toNat ∈ D := by
  cases a <;> simp_all [Stmt.litIn, Expr.eval]

theorem fwait_addr {D : List Nat} {d : Reg} {a v : Expr}
    {rs : Regs} (h : (Stmt.futexWait d a v).litIn D = true) : (a.eval rs).toNat ∈ D := by
  cases a <;> simp_all [Stmt.litIn, Expr.eval]

theorem touch_lit {D : List Nat} {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt}
    {rs' : Regs} (h : TStep s rs l s' rs') (hl : s.litIn D = true) {lab : Lab}
    (he : l = some lab) {a : Nat} (ht : lab.Touches a) : a ∈ D := by
  induction h with
  | load =>
    cases he
    rcases ht with ⟨v, hv⟩ | hv
    · simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hv
      rw [hv.1]; exact load_addr hl
    · simp [Lab.wval] at hv
  | store =>
    cases he
    rcases ht with ⟨v, hv⟩ | hv
    · simp [Lab.reads] at hv
    · simp only [Lab.wval] at hv
      split at hv
      · rename_i e; rw [← e]; exact store_addr hl
      · cases hv
  | rmw =>
    cases he
    rcases ht with ⟨v, hv⟩ | hv
    · simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hv
      rw [hv.1]; exact rmw_addr hl
    · simp only [Lab.wval] at hv
      split at hv
      · rename_i e; rw [← e]; exact rmw_addr hl
      · cases hv
  | fwait =>
    cases he
    rcases ht with ⟨v, hv⟩ | hv
    · simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hv
      rw [hv.1]; exact fwait_addr hl
    · simp [Lab.wval] at hv
  | blk =>
    cases he
    rename_i b _ _ _ _ _
    simp only [Stmt.litIn, List.all_eq_true, List.contains_iff_mem] at hl
    rcases ht with ⟨v, hv⟩ | hv
    · simp only [Lab.reads, List.mem_map] at hv
      obtain ⟨c, hc, e⟩ := hv
      cases e
      exact hl _ (List.mem_append_left _ (mem_cellVals' hc))
    · simp only [Lab.wval] at hv
      obtain ⟨c, hc, e⟩ := cellLast_mem hv
      subst e
      exact hl _ (List.mem_append_right _ (mem_cellVals' hc))
  | seq _ ih =>
    simp only [Stmt.litIn, Bool.and_eq_true] at hl
    exact ih hl.1 he
  | fwake => cases he; rcases ht with ⟨v, hv⟩ | hv <;> simp [Lab.reads, Lab.wval] at hv
  | fence => cases he; rcases ht with ⟨v, hv⟩ | hv <;> simp [Lab.reads, Lab.wval] at hv
  | spawn => cases he; rcases ht with ⟨v, hv⟩ | hv <;> simp [Lab.reads, Lab.wval] at hv
  | join => cases he; rcases ht with ⟨v, hv⟩ | hv <;> simp [Lab.reads, Lab.wval] at hv
  | _ => cases he

/-! ## The invariant -/

/-- The static invariant of reachable sync configurations. -/
structure SInv (P : SProg) (D : List Nat) (A : SCfg) : Prop where
  dom : ∀ a ∈ D, (A.mem a).isSome
  fresh : ∀ t, A.started t = false → A.ts t = (P.body t, Regs.zero)
  lit : ∀ t, (A.ts t).1.litIn D = true
  joins : ∀ t, (A.ts t).1.joinsIn P.N = true
  child : ∀ t, t ≠ 0 → (A.ts t).1.spawns = []
  mainLoop : (A.ts 0).1.loopSpawnFree = true
  mainNodup : (A.ts 0).1.spawns.Nodup
  mainRange : ∀ u ∈ (A.ts 0).1.spawns, 0 < u ∧ u < P.N ∧ A.started u = false

theorem body_cases (P : SProg) (u : Nat) :
    P.body u = .skip ∨ (P.body u ∈ P.bodies ∧ (u ≠ 0 → P.body u ∈ P.bodies.tail)) := by
  simp only [SProg.body]
  cases hb : P.bodies with
  | nil => simp
  | cons b0 rest =>
    cases u with
    | zero => simp
    | succ u =>
      simp only [List.getD_cons_succ, List.tail_cons, List.mem_cons, ne_eq,
        Nat.add_one_ne_zero, not_false_eq_true, forall_const]
      rw [List.getD_eq_getElem?_getD]
      cases h : rest[u]? with
      | none => simp
      | some s =>
        right
        have : s ∈ rest := List.mem_of_getElem? h
        simp [this]

theorem sInv_init {P : SProg} {D : List Nat} (hs : P.Static D) : SInv P D P.init := by
  have lit : ∀ u, (P.body u).litIn D = true := fun u => by
    rcases body_cases P u with h | ⟨h, -⟩
    · rw [h]; rfl
    · exact hs.lit _ h
  have joins : ∀ u, (P.body u).joinsIn P.N = true := fun u => by
    rcases body_cases P u with h | ⟨h, -⟩
    · rw [h]; rfl
    · exact hs.joins _ h
  refine ⟨hs.dom, fun _ _ => rfl, lit, joins, fun t ht => ?_, hs.mainLoop, hs.mainNodup,
    fun u hu => ?_⟩
  · rcases body_cases P t with h | ⟨-, h⟩
    · show (P.body t).spawns = []
      rw [h]; rfl
    · exact hs.child _ (h ht)
  · obtain ⟨h0, hN⟩ := hs.mainRange u hu
    refine ⟨h0, hN, ?_⟩
    simp only [SProg.init, beq_eq_false_iff_ne, ne_eq]; omega

theorem sInv_step {P : SProg} {D : List Nat} {A A' : SCfg} (I : SInv P D A)
    (h : SStep P.N A A') : SInv P D A' := by
  -- the common part: thread `t` moves from `A.ts t` to `(s', rs')` by a thread step
  have thread : ∀ {t l s' rs'}, A.started t = true → TStep (A.ts t).1 (A.ts t).2 l s' rs' →
      (∀ u, l ≠ some (.spawn u)) →
      SInv P D { A with ts := upd A.ts t (s', rs') } := by
    intro t l s' rs' hst hs hns
    have lsf : (A.ts t).1.loopSpawnFree = true := by
      by_cases e : t = 0
      · subst e; exact I.mainLoop
      · exact lsf_of_nil (I.child t e)
    obtain ⟨l1, l2, -⟩ := spawn_pres hs lsf
    refine ⟨I.dom, fun u hu => ?_, fun u => ?_, fun u => ?_, fun u hu => ?_, ?_, ?_, fun u hu => ?_⟩
    · have : u ≠ t := fun e => by subst e; rw [hst] at hu; cases hu
      simp only [upd_other _ _ this]; exact I.fresh u hu
    · by_cases e : u = t
      · subst e; simp only [upd_same]; exact lit_pres hs (I.lit _)
      · simp only [upd_other _ _ e]; exact I.lit u
    · by_cases e : u = t
      · subst e; simp only [upd_same]; exact joins_pres hs (I.joins _)
      · simp only [upd_other _ _ e]; exact I.joins u
    · by_cases e : u = t
      · subst e; simp only [upd_same]
        exact List.eq_nil_of_sublist_nil (by rw [← I.child _ hu]; exact l2)
      · simp only [upd_other _ _ e]; exact I.child u hu
    · by_cases e : (0 : Nat) = t
      · subst e; simp only [upd_same]; exact l1
      · simp only [upd_other _ _ e]; exact I.mainLoop
    · by_cases e : (0 : Nat) = t
      · subst e; simp only [upd_same]; exact l2.nodup I.mainNodup
      · simp only [upd_other _ _ e]; exact I.mainNodup
    · by_cases e : (0 : Nat) = t
      · subst e; simp only [upd_same] at hu; exact I.mainRange u (l2.subset hu)
      · simp only [upd_other _ _ e] at hu; exact I.mainRange u hu
  cases h with
  | tau _ hst hs => exact thread hst hs (fun _ h => by cases h)
  | lab _ hst hs _ hc _ =>
    have R := thread hst hs (fun u h => by cases h; simp [Lab.isMem] at *)
    refine { R with dom := fun a ha => ?_ }
    simp only [Lab.updH, Option.isSome_or]
    rw [I.dom a ha]; simp
  | join _ hst hs _ _ => exact thread hst hs (fun _ h => by cases h)
  | spawn _ hst hs hu hns =>
    rename_i t u s' rs' _
    have ht0 : t = 0 := by
      by_contra e
      have lsf := lsf_of_nil (I.child t e)
      have := (spawn_pres hs lsf).2.2 u rfl
      rw [I.child t e] at this; cases this
    subst ht0
    obtain ⟨l1, l2, l3⟩ := spawn_pres hs I.mainLoop
    have hsub := l3 u rfl
    have hnd : (u :: s'.spawns).Nodup := hsub.nodup I.mainNodup
    refine ⟨I.dom, fun w hw => ?_, fun w => ?_, fun w => ?_, fun w hw => ?_, ?_, ?_,
      fun w hw => ?_⟩
    · have hwu : w ≠ u := fun e => by subst e; simp [upd] at hw
      have hw' : A.started w = false := by simpa [upd, hwu] using hw
      have : w ≠ 0 := fun e => by subst e; rw [hst] at hw'; cases hw'
      simp only [upd_other _ _ this]; exact I.fresh w hw'
    · by_cases e : w = 0
      · subst e; simp only [upd_same]; exact lit_pres hs (I.lit _)
      · simp only [upd_other _ _ e]; exact I.lit w
    · by_cases e : w = 0
      · subst e; simp only [upd_same]; exact joins_pres hs (I.joins _)
      · simp only [upd_other _ _ e]; exact I.joins w
    · simp only [upd_other _ _ hw]; exact I.child w hw
    · simp only [upd_same]; exact l1
    · simp only [upd_same]; exact (List.nodup_cons.mp hnd).2
    · simp only [upd_same] at hw
      have hwu : w ≠ u := fun e => by subst e; exact (List.nodup_cons.mp hnd).1 hw
      obtain ⟨a1, a2, a3⟩ := I.mainRange w (l2.subset hw)
      exact ⟨a1, a2, by simp [upd, hwu, a3]⟩

/-- **Static sync safety**: the syntactic conditions imply `SyncSafe`. -/
theorem syncSafe_of_static {P : SProg} {D : List Nat} (hs : P.Static D) : P.SyncSafe := by
  have reach : ∀ A, SReach P P.init A → SInv P D A := by
    suffices ∀ A0 A, Star (SStep P.N) A0 A → SInv P D A0 → SInv P D A from
      fun A h => this _ _ h (sInv_init hs)
    intro A0 A h
    induction h with
    | refl => exact id
    | step h1 _ ih => exact fun I => ih (sInv_step I h1)
  intro A hA t _ hst l s' rs' h
  have I := reach A hA
  refine ⟨fun a ha => I.dom a (touch_lit h (I.lit t) rfl ha), fun u hu => ?_,
    fun u hu => join_label h (I.joins t) (congrArg some hu)⟩
  subst hu
  have ht0 : t = 0 := by
    by_contra e
    have := (spawn_pres h (lsf_of_nil (I.child t e))).2.2 u rfl
    rw [I.child t e] at this; cases this
  subst ht0
  exact I.mainRange u ((spawn_pres h I.mainLoop).2.2 u rfl |>.subset List.mem_cons_self)

end Silmaril.Proofs.X86.Concurrency.Cir.Proc
