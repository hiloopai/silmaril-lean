module

public import Silmaril.X86.Concurrency.Cir.Prim.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Thms

/-!
# The spinlock's acquire in the CSL

`spinLock_acquire`: the CIR program translation-validated from gcc's
`spin_lock` is CSL-safe from an empty heap, with the lock invariant `lockInv l R`, and ends owning
`R`: **acquire gives the invariant's resource**. The proof uses the rules (`safe_seq`,
`safe_loop`, `safe_atomic`) and, for silent `assign` steps, `safe_assign` below, proved from the
definition of `Csl.Safe` (the fixed-point lemmas of the logic are in its proofs module, which this
topic does not import; `labOk_mono`, `safeF_mono`, `safe_post` and `safe_intro` are restated
here).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.TvCfg (setB notE mask32)

/-! ## The fixed point, restated -/

theorem labOk_mono {I : HProp} {K K' : Heap → Prop} (hK : ∀ h, K h → K' h) {l : Lab} {h : Heap}
    (H : LabOk I K l h) : LabOk I K' l h := by
  obtain ⟨hm, hna, hat⟩ := H
  refine ⟨hm, fun hn => ⟨(hna hn).1, fun hok => hK _ ((hna hn).2 hok)⟩, fun hn hI hIi hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hat hn hI hIi hd
  refine ⟨h1, h2, fun hok => ?_⟩
  obtain ⟨h', hI', a, b, c, d, e⟩ := h3 hok
  exact ⟨h', hI', a, b, c, hK _ d, e⟩

theorem safeF_mono {I : HProp} {Q : Regs → HProp} {R R' : Stmt → Regs → Heap → Prop}
    (hR : ∀ s rs h, R s rs h → R' s rs h) {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q R s rs h) : SafeF I Q R' s rs h :=
  ⟨H.1, fun s' rs' hs => hR _ _ _ (H.2.1 s' rs' hs),
    fun l s' rs' hs => labOk_mono (hR _ _) (H.2.2 l s' rs' hs)⟩

theorem safe_post {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Safe I Q s rs h) : SafeF I Q (Safe I Q) s rs h := by
  obtain ⟨R, hR, hpost⟩ := H
  exact safeF_mono (fun s rs h hr => ⟨R, hr, hpost⟩) (hpost _ _ _ hR)

theorem safe_intro {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q (Safe I Q) s rs h) : Safe I Q s rs h := by
  refine ⟨fun s' rs' h' => (s' = s ∧ rs' = rs ∧ h' = h) ∨ Safe I Q s' rs' h',
    Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
  rintro s' rs' h' (⟨rfl, rfl, rfl⟩ | hs)
  · exact safeF_mono (fun _ _ _ x => Or.inr x) H
  · exact safeF_mono (fun _ _ _ x => Or.inr x) (safe_post hs)

/-- **A silent register assignment.** -/
theorem safe_assign {I : HProp} {Q : Regs → HProp} {d : Reg} {e : Expr} {rs : Regs} {h : Heap}
    (hq : Q (rs.set d (e.eval rs)) h) : Safe I Q (.assign d e) rs h := by
  refine safe_intro ⟨(fun e => by cases e), (fun s' rs' hs => ?_), (fun l s' rs' hs => by cases hs)⟩
  cases hs
  exact safe_skip hq

/-! ## Heaps -/

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := rfl

theorem union_empty (h : Heap) : Heap.union Heap.empty h = h := by
  funext x; simp [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, Heap.empty]

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

/-! ## The two atomic steps -/

/-- The address `[rdi]`. -/
theorem at_rdi {rs : Regs} : ((at_ .rdi 0).eval rs).toNat = (rs .rdi).toNat := by
  simp [at_, Expr.eval, BinOp.eval]

/-- What the thread knows after an exchange: it owns `R` exactly when the old value was `0`. -/
def Got (R : HProp) (rs : Regs) (h : Heap) : Prop :=
  (((rs .rax) &&& 0xffffffff#64) = 0 → R h) ∧ (((rs .rax) &&& 0xffffffff#64) ≠ 0 → h = Heap.empty)

theorem got_of {R : HProp} {old : Nat} (hv : old < 2 ^ (8 * 4)) {rs : Regs} {h : Heap}
    (h0 : old = 0 → R h) (h1 : old ≠ 0 → h = Heap.empty) :
    Got R (rs.set .rax (BitVec.ofNat 64 old)) h := by
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

/-- **The exchange**: from an empty heap, with `rax = 1`, `xchg [rdi], eax` re-splits ownership
with the lock invariant; the thread gets `R` exactly when the lock was free. -/
theorem safe_xchg {l : Nat} {R : HProp} {Q : Regs → HProp} {rs : Regs} (hl : (rs .rdi).toNat = l)
    (hax : rs .rax = 1)
    (hQ : ∀ rs' h', rs' .rdi = rs .rdi → rs' .rdx = rs .rdx → Got R rs' h' → Q rs' h') :
    Safe (lockInv l R) Q SpinLock.xchg rs Heap.empty := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | rmw hv =>
    rename_i old
    refine ⟨rfl, rfl, (fun e => by cases e), (fun _ hI hIi _ => ⟨?_, (fun e => by cases e), ?_⟩)⟩
    · intro a ha
      rw [union_empty]
      simp only [Lab.Touches, Lab.reads, Lab.wval, at_rdi, hl, List.mem_singleton,
        Prod.mk.injEq] at ha
      have ha' : a = l := by
        rcases ha with ⟨v, h1, -⟩ | h2
        · exact h1
        · by_contra hne; simp [Ne.symm hne] at h2
      subst ha'
      rcases hIi with ⟨hR, -, hd, rfl⟩ | ⟨v, -, rfl⟩
      · simp [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, single_apply]
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
      have hQ' := fun h' (hg : Got R (rs.set .rax (BitVec.ofNat 64 old)) h') =>
        hQ (rs.set .rax (BitVec.ofNat 64 old)) h' rfl rfl hg
      rcases hIi with ⟨hR, hRR, hd, rfl⟩ | ⟨v, hv0, rfl⟩
      · -- free: take `R`
        have hold : old = 0 := by
          simp [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, single_apply] at hrd
          omega
        have hRl : hR l = none := by
          rcases hd l with h | h
          · simp [single_apply] at h
          · exact h
        refine ⟨hR, Heap.single l 1, ?_, ?_, Or.inr ⟨1, by decide, rfl⟩,
          hQ' hR (got_of hv (fun _ => hRR) (fun h => absurd hold h)), fun _ => ?_⟩
        · intro x; by_cases hx : x = l
          · subst hx; exact Or.inl hRl
          · exact Or.inr (by simp [single_apply, hx])
        · funext x
          simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, single_apply]
          by_cases hx : x = l
          · subst hx; simp [hRl]
          · simp only [hx, ite_false]; cases hR x <;> rfl
        · simp [Heap.empty]
      · -- taken: nothing changes hands
        have hold : old = v := by simpa [single_apply] using hrd.symm
        refine ⟨Heap.empty, Heap.single l 1, disjoint_empty _, ?_, Or.inr ⟨1, by decide, rfl⟩,
          hQ' Heap.empty (got_of hv (fun h => absurd (hold ▸ h) hv0) (fun _ => rfl)), fun _ => ?_⟩
        · funext x; rw [union_empty]; simp only [single_apply]
          by_cases hx : x = l <;> simp [hx]
        · simp [Heap.empty]

/-- **A relaxed load of the lock word** from an empty heap: nothing changes hands. -/
theorem safe_ld {l : Nat} {R : HProp} {Q : Regs → HProp} {rs : Regs} (hl : (rs .rdi).toNat = l)
    (hQ : ∀ v, Q (rs.set .rax (BitVec.ofNat 64 v)) Heap.empty) :
    Safe (lockInv l R) Q SpinLock.ld rs Heap.empty := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | load hv =>
    rename_i v
    refine ⟨rfl, rfl, (fun e => by cases e),
      (fun _ hI hIi _ => ⟨?_, (fun _ a ha => by cases ha), ?_⟩)⟩
    · intro a ha
      rw [union_empty]
      simp only [Lab.Touches, Lab.reads, Lab.wval, at_rdi, hl, List.mem_singleton,
        Prod.mk.injEq, Option.isSome_none, Bool.false_eq_true, or_false] at ha
      obtain ⟨_, rfl, -⟩ := ha
      rcases hIi with ⟨hR, -, hd, rfl⟩ | ⟨v, -, rfl⟩
      · simp [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, single_apply]
      · simp [single_apply]
    · intro _
      refine ⟨Heap.empty, hI, disjoint_empty _, ?_, hIi, hQ v, fun _ a ha => ?_⟩
      · funext x; rw [union_empty]; simp [Lab.updH, Lab.wval]
      · simp [Heap.empty] at ha

/-! ## The acquire -/

/-- The spinlock's program with bound `L`, unfolded. -/
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

/-- **Acquire gives the invariant's resource**: the CIR program of `spin_lock`, started from an
empty heap with `rdi` pointing at the lock word `l`, is CSL-safe under `lockInv l R` for every
loop bound, and ends owning `R`. -/
theorem spinLock_acquire (l : Nat) (R : HProp) (L : Nat) (rs : Regs) (hl : (rs .rdi).toNat = l) :
    Safe (lockInv l R) (fun _ h => R h) (SpinLock.cert.body L) rs Heap.empty := by
  -- the retry loop's invariant, and the spin loop's
  let J : Nat → Regs → Heap → Prop := fun _ rs' h =>
    (rs' .rdi).toNat = l ∧ rs' .rdx = 1 ∧ Got R rs' h
  let K : Nat → Regs → Heap → Prop := fun _ rs' h =>
    (rs' .rdi).toNat = l ∧ rs' .rdx = 1 ∧ h = Heap.empty
  -- `mov eax, edx; xchg [rdi], eax` re-establishes `J`
  have hswap : ∀ (Q : Regs → HProp) (rs' : Regs), (rs' .rdi).toNat = l → rs' .rdx = 1 →
      (∀ rs'' h, (rs'' .rdi).toNat = l → rs'' .rdx = 1 → Got R rs'' h → Q rs'' h) →
      Safe (lockInv l R) Q (.seq SpinLock.movAX SpinLock.xchg) rs' Heap.empty := by
    intro Q rs' h1 h2 hQ
    apply safe_seq
    apply safe_assign
    refine safe_xchg (by simpa [Regs.set] using h1)
      (by simp only [Regs.set, ite_true]; exact mov_one h2)
      (fun rs'' h e1 e2 hg => hQ rs'' h (by rw [e1]; simpa [Regs.set] using h1)
        (by rw [e2]; simpa [Regs.set] using h2) hg)
  -- the retry loop
  have hretry : ∀ rs' h, J L rs' h → Safe (lockInv l R) (fun rs h => Safe (lockInv l R)
      (fun _ h => R h) .skip rs h) (.loop L (notE (zTest .rax)) (.seq SpinLock.ld
        (.seq (.loop L (notE (zTest .rax)) SpinLock.ld) (.seq SpinLock.movAX SpinLock.xchg))))
      rs' h := by
    intro rs' h hJ
    refine safe_loop J ?_ ?_ hJ
    · intro k rs h ⟨_, _, hg⟩ hc
      rw [truthy_notE_zTest] at hc
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hc
      exact safe_skip (hg.1 hc)
    · intro k rs h ⟨h1, h2, hg⟩ hc
      rw [truthy_notE_zTest] at hc
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hc
      have he := hg.2 hc
      subst he
      apply safe_seq
      refine safe_ld h1 (fun v => ?_)
      apply safe_seq
      refine safe_loop K ?_ ?_ (show K L _ _ from ⟨by simpa [Regs.set] using h1,
        by simpa [Regs.set] using h2, rfl⟩)
      · intro k' rs₂ h₂ ⟨e1, e2, e3⟩ _
        subst e3
        exact hswap _ rs₂ e1 e2 (fun rs'' h a b c => ⟨a, b, c⟩)
      · intro k' rs₂ h₂ ⟨e1, e2, e3⟩ _
        subst e3
        exact safe_ld e1 (fun v =>
          ⟨by simpa [Regs.set] using e1, by simpa [Regs.set] using e2, rfl⟩)
  rw [body_eq]
  apply safe_seq
  apply safe_assign
  apply safe_seq
  apply safe_assign
  apply safe_seq
  refine safe_xchg (by simpa [Regs.set] using hl)
    (by simp only [Regs.set, ite_true]; exact mov_one (by simp [Regs.set, Expr.eval]))
    (fun rs' h e1 e2 hg => ?_)
  apply safe_seq
  exact hretry rs' h
    ⟨by rw [e1]; simpa [Regs.set] using hl, by rw [e2]; simp [Regs.set, Expr.eval], hg⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Prim
