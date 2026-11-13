module

public import Silmaril.X86.Concurrency.Cir.Prim.Tasks.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms
public import Silmaril.X86.Concurrency.Cir.Csl.Thms

/-!
# The spinlock with its plain-`mov` unlock is a lock on TSO, for every client

`Task.spinMutexTso`, proved with the release rule of `Csl.Rel` (`rel_tso`):

* the lock invariant `spinInvG l R` holds a **ghost token** `spinTk` exactly when the lock word is
  `0` (then it also holds `R`); a non-zero word has neither;
* `spin_lock` (the CIR program, every loop bound) is `SafeR`-safe from nothing and ends owning
  `R` and the token (`spinLock_acquireR`; the same steps as `spinLock_acquire`, with the
  token moving at the successful exchange);
* `spin_unlock`, the plain `mov` of `0`, is a **release** of `R` and the token
  (`spinUnlock_release`): with the token, the invariant cannot be in its `0` state, so in every
  invariant state the store re-establishes the `0` state;
* the critical sections are proofs under the empty invariant, lifted (`safeR_lift`), and keep
  `rdi` (`safeR_keep`);
* at a finished, drained state ghost conservation puts the token back in the invariant, so it
  is in its `0` state: the word is `0` and memory contains a heap satisfying `R`.

`Got` and register lemmas are restated here (their proofs module belongs to another topic).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.TvCfg (setB notE mask32)

/-! ## Heaps -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) : Heap.union h₁ h₂ a = (h₁ a).or (h₂ a) := by
  simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion]; cases h₁ a <;> rfl

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := rfl

theorem union_empty (h : Heap) : Heap.union Heap.empty h = h := by
  funext x; rw [union_apply]; rfl

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext x; rw [union_apply]; cases h x <;> rfl

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.Disjoint h Heap.empty := fun _ => Or.inr rfl

/-! ## Registers kept by a statement -/

theorem setMany_keep {r : Reg} : ∀ {l : List Reg} {vs : List Nat} {rs : Regs}, r ∉ l →
    rs.setMany l vs r = rs r
  | [], _, _, _ => by simp [Regs.setMany]
  | _ :: _, [], _, _ => by simp [Regs.setMany]
  | q :: l, v :: vs, rs, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [Regs.setMany]
    rw [setMany_keep h.2]
    simp [Regs.set, h.1]

/-- A thread step keeps every register its statement does not write. -/
theorem tstep_keep {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (st : TStep s rs l s' rs') {r : Reg} (hr : r ∉ s.writes) : rs' r = rs r ∧ r ∉ s'.writes := by
  induction st with
  | assign | load | rmw | fwait =>
    simp only [Stmt.writes, List.mem_singleton] at hr
    exact ⟨by simp [Regs.set, hr], by simp [Stmt.writes]⟩
  | store | fence | fwake | spawn | join => simp [Stmt.writes]
  | blk => exact ⟨setMany_keep (by simpa [Stmt.writes] using hr), by simp [Stmt.writes]⟩
  | seq _ ih =>
    simp only [Stmt.writes, List.mem_append, not_or] at hr ⊢
    exact ⟨(ih hr.1).1, (ih hr.1).2, hr.2⟩
  | seqSkip =>
    simp only [Stmt.writes, List.mem_append, not_or] at hr; exact ⟨rfl, hr.2⟩
  | iteT | iteF =>
    simp only [Stmt.writes, List.mem_append, not_or] at hr
    first | exact ⟨rfl, hr.1⟩ | exact ⟨rfl, hr.2⟩
  | loopT =>
    refine ⟨rfl, ?_⟩
    simp only [Stmt.writes, List.mem_append, not_or] at hr ⊢; exact ⟨hr, hr⟩
  | loopF => exact ⟨rfl, by simp [Stmt.writes]⟩

/-- **A `SafeR` thread keeps a register its statement does not write.** -/
theorem safeR_keep {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {p : Bool} {s : Stmt}
    {rs : Regs} {h g : Heap} {r : Reg} (hr : r ∉ s.writes) (H : SafeR I Q p s rs h g) :
    SafeR I (fun p rs' h g => Q p rs' h g ∧ rs' r = rs r) p s rs h g := by
  refine safeR_coind (fun p s' rs' h g => r ∉ s'.writes ∧ rs' r = rs r ∧ SafeR I Q p s' rs' h g)
    ?_ ⟨hr, rfl, H⟩
  rintro p s' rs' h g ⟨hw, hv, H⟩
  have F := safeR_unfold H
  refine ⟨fun e => ⟨F.1 e, hv⟩, fun s'' rs'' st => ?_, fun l s'' rs'' st => ?_⟩
  · obtain ⟨k1, k2⟩ := tstep_keep st hw
    exact Or.inl ⟨k2, by rw [k1, hv], F.2.1 _ _ st⟩
  · obtain ⟨k1, k2⟩ := tstep_keep st hw
    exact labOkR_mono (fun _ _ _ x => Or.inl ⟨k2, by rw [k1, hv], x⟩) (F.2.2 l s'' rs'' st)

/-! ## The ghost lock invariant -/


/-- What the thread knows after an exchange. -/
def GotG (R : HProp) (rs : Regs) (h g : Heap) : Prop :=
  (((rs .rax) &&& 0xffffffff#64) = 0 → R h ∧ g = spinTk) ∧
    (((rs .rax) &&& 0xffffffff#64) ≠ 0 → h = Heap.empty ∧ g = Heap.empty)

theorem gotG_of {R : HProp} {old : Nat} (hv : old < 2 ^ (8 * 4)) {rs : Regs} {h g : Heap}
    (h0 : old = 0 → R h ∧ g = spinTk) (h1 : old ≠ 0 → h = Heap.empty ∧ g = Heap.empty) :
    GotG R (rs.set .rax (BitVec.ofNat 64 old)) h g := by
  have hm : (BitVec.ofNat 64 old &&& 0xffffffff#64) = BitVec.ofNat 64 old := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    simp only [BitVec.toNat_ofNat]
    rw [show (4294967295 : Nat) % 2 ^ 64 = 2 ^ 32 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hz : BitVec.ofNat 64 old = 0 ↔ old = 0 := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · rintro rfl; rfl
  refine ⟨fun e => h0 ?_, fun e => h1 ?_⟩
  · simp only [Regs.set, ite_true, hm] at e; exact hz.mp e
  · simp only [Regs.set, ite_true, hm] at e; exact fun h => e (hz.mpr h)

theorem at_rdi {rs : Regs} : ((at_ .rdi 0).eval rs).toNat = (rs .rdi).toNat := by
  simp [at_, Expr.eval, BinOp.eval]

theorem tk_ne : ¬ Heap.Disjoint spinTk spinTk := fun h => by
  rcases h 0 with e | e <;> simp [spinTk, single_apply] at e

/-! ## The two atomic steps of the acquire -/

/-- **The exchange**: the token and `R` move to the thread exactly when the word was `0`. -/
theorem safeR_xchg {l : Nat} {R : HProp} {Q : Bool → Regs → Heap → Heap → Prop} {rs : Regs}
    (hl : (rs .rdi).toNat = l) (hax : rs .rax = 1)
    (hQ : ∀ rs' h' g', rs' .rdi = rs .rdi → rs' .rdx = rs .rdx → GotG R rs' h' g' →
      Q false rs' h' g') :
    SafeR (spinInvG l R) Q false SpinLock.xchg rs Heap.empty Heap.empty := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | rmw hv =>
    rename_i old
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inr rfl, fun hI gI hIi _ _ =>
      ⟨?_, (fun e => by cases e), ?_⟩⟩)⟩
    · intro a ha
      rw [union_empty]
      simp only [Lab.Touches, Lab.reads, Lab.wval, at_rdi, hl, List.mem_singleton,
        Prod.mk.injEq] at ha
      have ha' : a = l := by
        rcases ha with ⟨v, h1, -⟩ | h2
        · exact h1
        · by_contra hne; simp [Ne.symm hne] at h2
      subst ha'
      rcases hIi with ⟨hR, -, hd, rfl, -⟩ | ⟨v, -, rfl, -⟩
      · simp [union_apply, single_apply]
      · simp [single_apply]
    · intro hok
      rw [union_empty] at hok ⊢
      have hrd : hI l = some old := by
        have := hok _ (List.mem_singleton_self _)
        simpa [Lab.reads, at_rdi, hl] using this
      have hnew : RmwOp.result rs 4 old ((Expr.reg .rax).eval rs) .xchg = 1 := by
        simp [RmwOp.result, Expr.eval, hax]
      have hupd : (Lab.rmw .acq ((at_ .rdi 0).eval rs).toNat 4 old
          (RmwOp.result rs 4 old ((Expr.reg .rax).eval rs) .xchg)).updH hI =
          fun x => if x = l then some 1 else hI x := by
        funext x
        simp only [Lab.updH, Lab.wval, at_rdi, hl, hnew]
        by_cases hx : x = l
        · subst hx; simp
        · simp [Ne.symm hx, hx]
      rw [hupd]
      have hQ' := fun h' g' (hg : GotG R (rs.set .rax (BitVec.ofNat 64 old)) h' g') =>
        hQ (rs.set .rax (BitVec.ofNat 64 old)) h' g' rfl rfl hg
      rcases hIi with ⟨hR, hRR, hd, rfl, rfl⟩ | ⟨v, hv0, rfl, rfl⟩
      · -- free: take `R` and the token
        have hold : old = 0 := by
          simp [union_apply, single_apply] at hrd
          omega
        have hRl : hR l = none := by
          rcases hd l with h | h
          · simp [single_apply] at h
          · exact h
        refine ⟨hR, Heap.single l 1, spinTk, Heap.empty, ?_, ?_, disjoint_empty_right _, ?_,
          Or.inr ⟨1, by decide, rfl, rfl⟩,
          hQ' hR spinTk (gotG_of hv (fun _ => ⟨hRR, rfl⟩) (fun h => absurd hold h)), fun e => by
            cases e⟩
        · intro x; by_cases hx : x = l
          · subst hx; exact Or.inl hRl
          · exact Or.inr (by simp [single_apply, hx])
        · funext x
          simp only [union_apply, single_apply]
          by_cases hx : x = l
          · subst hx; simp [hRl]
          · simp only [hx, ite_false]; cases hR x <;> rfl
        · rw [union_empty_right, union_empty]
      · -- taken: nothing changes hands
        have hold : old = v := by simpa [single_apply] using hrd.symm
        refine ⟨Heap.empty, Heap.single l 1, Heap.empty, Heap.empty, disjoint_empty _, ?_,
          disjoint_empty _, rfl, Or.inr ⟨1, by decide, rfl, rfl⟩,
          hQ' Heap.empty Heap.empty (gotG_of hv (fun h => absurd (hold ▸ h) hv0)
            (fun _ => ⟨rfl, rfl⟩)), fun e => by cases e⟩
        funext x; rw [union_empty]; simp only [single_apply]
        by_cases hx : x = l <;> simp [hx]

/-- **A relaxed load of the lock word**: nothing changes hands. -/
theorem safeR_ld {l : Nat} {R : HProp} {Q : Bool → Regs → Heap → Heap → Prop} {rs : Regs}
    (hl : (rs .rdi).toNat = l)
    (hQ : ∀ v, Q false (rs.set .rax (BitVec.ofNat 64 v)) Heap.empty Heap.empty) :
    SafeR (spinInvG l R) Q false SpinLock.ld rs Heap.empty Heap.empty := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | load hv =>
    rename_i v
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl, fun hI gI hIi _ _ =>
      ⟨?_, (fun _ a ha => by cases ha), ?_⟩⟩)⟩
    · intro a ha
      rw [union_empty]
      simp only [Lab.Touches, Lab.reads, Lab.wval, at_rdi, hl, List.mem_singleton,
        Prod.mk.injEq, Option.isSome_none, Bool.false_eq_true, or_false] at ha
      obtain ⟨_, rfl, -⟩ := ha
      rcases hIi with ⟨hR, -, hd, rfl, -⟩ | ⟨v, -, rfl, -⟩
      · simp [union_apply, single_apply]
      · simp [single_apply]
    · intro _
      refine ⟨Heap.empty, hI, Heap.empty, gI, disjoint_empty _, ?_, disjoint_empty _, rfl, hIi,
        hQ v, fun _ a ha => by cases ha⟩
      funext x; rw [union_empty]; simp [Lab.updH, Lab.wval]

/-! ## The acquire -/

theorem body_eq (L : Nat) : SpinLock.cert.body L =
    .seq (.assign .rdx (.lit 1)) (.seq SpinLock.movAX (.seq SpinLock.xchg
      (.seq (.loop L (notE (zTest .rax)) (.seq SpinLock.ld (.seq (.loop L (notE (zTest .rax))
        SpinLock.ld) (.seq SpinLock.movAX SpinLock.xchg)))) .skip))) := rfl

theorem truthy_notE_zTest (rs : Regs) :
    truthy ((notE (zTest .rax)).eval rs) = !decide ((rs .rax &&& 0xffffffff#64) = 0) := by
  simp only [notE, zTest, mask32, Expr.eval, BinOp.eval, truthy, BitVec.and_self]
  split <;> split <;> simp_all

theorem mov_one {rs : Regs} (h : rs .rdx = 1) : (r32 .rdx).eval rs = 1 := by
  simp only [r32, mask32, Expr.eval, BinOp.eval, h]; decide

/-- **Acquire gives `R` and the token** (`SafeR`, every loop bound), keeping `rdi`. -/
theorem spinLock_acquireR (l : Nat) (R : HProp) (L : Nat) (rs : Regs)
    (hl : (rs .rdi).toNat = l) :
    SafeR (spinInvG l R) (fun p rs' h g => p = false ∧ rs' .rdi = rs .rdi ∧ R h ∧ g = spinTk) false
      (SpinLock.cert.body L) rs Heap.empty Heap.empty := by
  let Qf : Bool → Regs → Heap → Heap → Prop :=
    fun p rs' h g => p = false ∧ rs' .rdi = rs .rdi ∧ R h ∧ g = spinTk
  let J : Nat → Bool → Regs → Heap → Heap → Prop := fun _ p rs' h g =>
    p = false ∧ rs' .rdi = rs .rdi ∧ rs' .rdx = 1 ∧ GotG R rs' h g
  let K : Nat → Bool → Regs → Heap → Heap → Prop := fun _ p rs' h g =>
    p = false ∧ rs' .rdi = rs .rdi ∧ rs' .rdx = 1 ∧ h = Heap.empty ∧ g = Heap.empty
  have hswap : ∀ (Q : Bool → Regs → Heap → Heap → Prop) (rs' : Regs), rs' .rdi = rs .rdi →
      rs' .rdx = 1 →
      (∀ rs'' h g, rs'' .rdi = rs .rdi → rs'' .rdx = 1 → GotG R rs'' h g → Q false rs'' h g) →
      SafeR (spinInvG l R) Q false (.seq SpinLock.movAX SpinLock.xchg) rs' Heap.empty
        Heap.empty := by
    intro Q rs' h1 h2 hQ
    apply safeR_seq
    apply safeR_assign
    refine safeR_xchg (by simp [Regs.set, h1, hl])
      (by simp only [Regs.set, ite_true]; exact mov_one h2)
      (fun rs'' h g e1 e2 hg => hQ rs'' h g (by rw [e1]; simpa [Regs.set] using h1)
        (by rw [e2]; simpa [Regs.set] using h2) hg)
  have hretry : ∀ rs' h g, J L false rs' h g → SafeR (spinInvG l R)
      (fun p rs h g => SafeR (spinInvG l R) Qf p .skip rs h g)
      false (.loop L (notE (zTest .rax)) (.seq SpinLock.ld
        (.seq (.loop L (notE (zTest .rax)) SpinLock.ld) (.seq SpinLock.movAX SpinLock.xchg))))
      rs' h g := by
    intro rs' h g hJ
    refine safeR_loop J ?_ ?_ hJ
    · intro k p rs h g ⟨hp, h1, _, hg⟩ hc
      rw [truthy_notE_zTest] at hc
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hc
      exact safeR_skip ⟨hp, h1, (hg.1 hc).1, (hg.1 hc).2⟩
    · intro k p rs h g ⟨hp, h1, h2, hg⟩ hc
      subst hp
      rw [truthy_notE_zTest] at hc
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hc
      obtain ⟨rfl, rfl⟩ := hg.2 hc
      apply safeR_seq
      refine safeR_ld (by rw [h1, hl]) (fun v => ?_)
      apply safeR_seq
      refine safeR_loop K ?_ ?_ (show K L false _ _ _ from ⟨rfl, by simpa [Regs.set] using h1,
        by simpa [Regs.set] using h2, rfl, rfl⟩)
      · intro k' p' rs₂ h₂ g₂ ⟨e0, e1, e2, e3, e4⟩ _
        subst e0 e3 e4
        exact hswap _ rs₂ e1 e2 (fun rs'' h g a b c => ⟨rfl, a, b, c⟩)
      · intro k' p' rs₂ h₂ g₂ ⟨e0, e1, e2, e3, e4⟩ _
        subst e0 e3 e4
        exact safeR_ld (by rw [e1, hl]) (fun v =>
          ⟨rfl, by simpa [Regs.set] using e1, by simpa [Regs.set] using e2, rfl, rfl⟩)
  rw [body_eq]
  apply safeR_seq
  apply safeR_assign
  apply safeR_seq
  apply safeR_assign
  apply safeR_seq
  refine safeR_xchg (by simp [Regs.set, hl])
    (by simp only [Regs.set, ite_true]; exact mov_one (by simp [Regs.set, Expr.eval]))
    (fun rs' h g e1 e2 hg => ?_)
  apply safeR_seq
  exact hretry rs' h g
    ⟨rfl, by rw [e1]; simp [Regs.set], by rw [e2]; simp [Regs.set, Expr.eval], hg⟩

/-! ## The release -/

theorem unlock_eq (L : Nat) : SpinUnlock.cert.body L = .seq SpinUnlock.st .skip := rfl

/-- **`spin_unlock` releases `R` and the token**, by a plain store. -/
theorem spinUnlock_release (l : Nat) (R : HProp) (L : Nat) (rs : Regs) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hR : R h) :
    SafeR (spinInvG l R) (fun _ _ h g => h = Heap.empty ∧ g = Heap.empty) false
      (SpinUnlock.cert.body L) rs h spinTk := by
  rw [unlock_eq]
  apply safeR_seq
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | store =>
    refine ⟨rfl, rfl, Or.inr (Or.inr ⟨.rel, .wb, l, 4, 0, ?_, by decide, Heap.empty, h,
      Heap.empty, spinTk, disjoint_empty _, (union_empty h).symm, disjoint_empty _,
      (union_empty spinTk).symm, safeR_skip ⟨rfl, rfl⟩, ?_⟩)⟩
    · simp [at_rdi, hl, Expr.eval]
    · intro hI gI hIi hd hdg
      rcases hIi with ⟨hR', -, -, -, rfl⟩ | ⟨v, hv0, rfl, rfl⟩
      · exact absurd hdg tk_ne
      · have hl0 : h l = none := by
          rcases hd l with e | e
          · exact e
          · simp [single_apply] at e
        refine ⟨⟨l, 0, false, rfl, by simp [union_apply, single_apply]⟩, Or.inl ⟨h, hR, ?_, ?_,
          union_empty_right spinTk⟩⟩
        · intro x; by_cases hx : x = l
          · subst hx; exact Or.inr hl0
          · exact Or.inl (by simp [single_apply, hx])
        · funext x
          simp only [Ent.apply, union_apply, single_apply]
          by_cases hx : x = l
          · subst hx; simp
          · simp only [hx, ite_false]; cases h x <;> rfl

/-! ## The program -/

theorem regs_rdi (l : Nat) (hl : l < 2 ^ 64) : ((regs [(.rdi, l)]) .rdi).toNat = l := by
  have : l < 18446744073709551616 := hl
  simp [regs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

theorem heapOf_one (l : Nat) (h : Heap) :
    heapOf [(l, 0)] h = Heap.union (Heap.single l 0) h := by
  funext a
  rw [union_apply, single_apply]
  by_cases ha : a = l
  · subst ha; simp [heapOf, List.find?]
  · have : (l == a) = false := by simp [Ne.symm ha]
    simp [heapOf, List.find?, this, ha]

/-- **One thread** of the spinlock client: lock, critical section, unlock. -/
theorem thread_safe {l : Nat} {R : HProp} {L : Nat} {cs : Stmt} (hl : l < 2 ^ 64)
    (hw : .rdi ∉ cs.writes)
    (hcs : ∀ rs h, R h → Safe (fun h => h = Heap.empty) (fun _ h' => R h') cs rs h) :
    SafeR (spinInvG l R) (fun _ _ h g => h = Heap.empty ∧ g = Heap.empty) false
      (Tv.chain [SpinLock.cert.body L, cs, SpinUnlock.cert.body L]) (regs [(.rdi, l)])
      Heap.empty Heap.empty := by
  have hl' := regs_rdi l hl
  simp only [Tv.chain]
  apply safeR_seq
  refine safeR_conseq (fun p rs' h g ⟨hp, e1, hR, hg⟩ => ?_) (spinLock_acquireR l R L _ hl')
  subst hp hg
  apply safeR_seq
  have hc := safeR_keep hw (safeR_lift (I := spinInvG l R) (I0 := fun h => h = Heap.empty)
    (g := spinTk)
    (fun hI gI i => ⟨Heap.empty, hI, disjoint_empty _, (union_empty hI).symm, rfl,
      fun hA' e _ => by rw [e, union_empty]; exact i⟩) (hcs rs' h hR))
  refine safeR_conseq (fun p rs'' h' g' ⟨⟨hp', hR', hg'⟩, e2⟩ => ?_) hc
  subst hp' hg'
  apply safeR_seq
  refine safeR_conseq (fun _ _ _ _ q => safeR_skip q)
    (spinUnlock_release l R L rs'' h' (by rw [e2, e1, hl']) hR')

/-- **`Task.spinMutexTso` holds.** -/
theorem spinMutexTso_holds : Task.spinMutexTso := by
  intro N L l R hR0 cs hl hR0l hRR hw hcs C hr hd hf
  have G : GInvR (spinInvG l R) (fun _ _ _ h g => h = Heap.empty ∧ g = Heap.empty) N
      (lockCfg (SpinLock.cert.body L) (SpinUnlock.cert.body L) N l cs (heapOf [(l, 0)] hR0))
      (fun _ => Heap.empty) (fun _ => Heap.empty) (heapOf [(l, 0)] hR0) spinTk := by
    refine ⟨fun _ _ _ => disjoint_empty _, fun _ => disjoint_empty _, fun _ _ _ => disjoint_empty _,
      fun _ => disjoint_empty _, fun _ _ _ e => (by simp [Heap.empty] at e), fun _ _ e => e, ?_,
      fun t ht => ?_⟩
    · refine Or.inl ⟨hR0, hRR, fun x => ?_, heapOf_one l hR0, rfl⟩
      by_cases hx : x = l
      · subst hx; exact Or.inr hR0l
      · exact Or.inl (by simp [single_apply, hx])
    · simp only [lockCfg, ht, ↓reduceIte]
      exact thread_safe hl (hw t) (fun rs h hR => hcs t rs h hR)
  obtain ⟨hs', gs', hI', gI', ps', q, i, -, l2, -, -, cons⟩ :=
    rel_tso (G0 := spinTk) G (fun c e => Or.inl e) hr hd hf
  have hgI : (gI' 0).isSome := by
    rcases cons 0 (by simp [spinTk, single_apply]) with h | ⟨t, ht, h⟩
    · exact h
    · rw [(q t ht).2] at h; cases h
  rcases i with ⟨hR, hRR', hdisj, rfl, rfl⟩ | ⟨v, -, rfl, rfl⟩
  · refine ⟨l2 l 0 (by simp [union_apply, single_apply]), hR, hRR', fun a v e => l2 a v ?_⟩
    have ha : a ≠ l := fun h => by
      subst h
      rcases hdisj a with e' | e'
      · simp [single_apply] at e'
      · rw [e'] at e; cases e
    rw [union_apply, single_apply]; simpa [ha] using e
  · cases hgI

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks
