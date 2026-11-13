module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Spin
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Defs

/-!
# Proofs: Drepper's futex mutex meets the interface

All on CIR and the CSL. The invariant is `Spin.inv l R = lockInv l (locked l ∗ R)`: the
lock word is `0` and the invariant holds the token and `R`, or the word is not `0`. Drepper's
three states are not visible to the proof: `1` and `2` are both "not `0`".

* `safe_acq`: a locked read-modify-write of the lock word **from an empty heap** that never
  writes `0` (the `cas 0 → 1` and the `xchg 2`) re-splits ownership with the invariant: the
  thread gets the resource exactly when the old value was `0` (`GotV`);
* `safe_wait`: a futex wait on the lock word is an atomic read of an invariant cell, which moves
  no ownership; its result is any value. A wait that blocks for ever has no finished run, so
  partial correctness does not see it;
* `safe_wake`: a futex wake touches no cell;
* `fm_lock`: the CIR program of `fmutex_lock`, for every loop bound, from an empty heap, ends
  owning the resource; the wait loop's invariant is `GotV` with `rdx = 2`;
* `fm_unlock`: the CIR program of `fmutex_unlock` hands the resource and the token back, with
  `safe_xchg0`, then possibly wakes.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Futex
open Silmaril.X86.Concurrency.Cir.Prim (at_ lockInv op32 r32 zTest zCmpI)
open Silmaril.X86.Concurrency.Cir.TvCfg (setB notE mask32)
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (casZ waitStmt wakeStmt)

/-! ## Values of `rax` -/

/-- What the thread knows after a locked access to the lock word: `rax` holds the old value
`old` (32 bits), and it owns `R` exactly when `old = 0`. -/
def GotV (R : HProp) (rs : Regs) (h : Heap) : Prop :=
  ∃ old, old < 2 ^ 32 ∧ rs .rax = BitVec.ofNat 64 old ∧ (old = 0 → R h) ∧ (old ≠ 0 → h = Heap.empty)

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · rintro rfl; rfl

theorem mask_ofNat {a : Nat} (ha : a < 2 ^ 32) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 0xffffffff = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (0xffffffff : Nat) % 2 ^ 64 = 2 ^ 32 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem truthy_casZ0 {rs : Regs} {old : Nat} (ho : old < 2 ^ 32)
    (h : rs .rax = BitVec.ofNat 64 old) :
    truthy ((notE (casZ 0)).eval rs) = decide (old ≠ 0) := by
  have e := ofNat_eq_iff ho (show 0 < 2 ^ 32 by decide)
  simp only [notE, casZ, Expr.eval, BinOp.eval, truthy, h]
  by_cases h0 : old = 0
  · subst h0; decide
  · have : ¬ BitVec.ofNat 64 old = BitVec.ofNat 64 0 := fun x => h0 (e.mp x)
    simp [this, h0]

theorem truthy_zTest {rs : Regs} {old : Nat} (ho : old < 2 ^ 32)
    (h : rs .rax = BitVec.ofNat 64 old) :
    truthy ((zTest .rax).eval rs) = decide (old = 0) := by
  have e := ofNat_eq_iff ho (show 0 < 2 ^ 32 by decide)
  simp only [zTest, mask32, Expr.eval, BinOp.eval, truthy, h, BitVec.and_self]
  rw [mask_ofNat ho]
  by_cases h0 : old = 0
  · subst h0; decide
  · have : ¬ BitVec.ofNat 64 old = 0#64 := fun x => h0 (e.mp x)
    simp [this, h0]

theorem truthy_zCmp2 {rs : Regs} {old : Nat} (ho : old < 2 ^ 32)
    (h : rs .rax = BitVec.ofNat 64 old) :
    truthy ((zCmpI .rax 2).eval rs) = decide (old = 2) := by
  have e := ofNat_eq_iff ho (show 2 < 2 ^ 32 by decide)
  simp only [zCmpI, r32, mask32, Expr.eval, BinOp.eval, truthy, h]
  rw [mask_ofNat ho]
  by_cases h2 : old = 2
  · subst h2; decide
  · have : ¬ BitVec.ofNat 64 old = BitVec.ofNat 64 2 := fun x => h2 (e.mp x)
    simp [this, h2]

theorem truthy_notE' (z : Expr) (rs : Regs) :
    truthy ((notE z).eval rs) = !truthy (z.eval rs) := by
  simp only [notE, Expr.eval, BinOp.eval, truthy]
  by_cases h : z.eval rs = BitVec.ofNat 64 0 <;> simp [h]

/-! ## The atomic steps -/

/-- The lock word is mapped in every heap of the invariant. -/
theorem inv_some {l : Nat} {R : HProp} {hI : Heap} (H : lockInv l R hI) : (hI l).isSome := by
  rcases H with ⟨hR, -, -, rfl⟩ | ⟨v, -, rfl⟩
  · simp [union_apply, single_apply]
  · simp [single_apply]

/-- **A locked access that never writes `0`**, from an empty heap: the thread gets `R` exactly
when the old value was `0`. -/
theorem safe_acq {l : Nat} {R : HProp} {Q : Regs → HProp} {rs : Regs} {md : Mode} {op : RmwOp}
    {arg : Expr} (hl : (rs .rdi).toNat = l)
    (hnz : ∀ old, old < 2 ^ 32 → RmwOp.result rs 4 old (arg.eval rs) op ≠ 0)
    (hQ : ∀ rs' h', (∀ r, r ≠ .rax → rs' r = rs r) → GotV R rs' h' → Q rs' h') :
    Csl.Safe (lockInv l R) Q (.rmw .rax md 4 op (at_ .rdi 0) arg) rs Heap.empty := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | rmw hv =>
    rename_i old
    have hv' : old < 2 ^ 32 := by simpa using hv
    have hn := hnz old hv'
    have hkeep : ∀ r, r ≠ .rax → (rs.set .rax (BitVec.ofNat 64 old)) r = rs r := by
      intro r hr; simp [Regs.set, hr]
    refine ⟨rfl, rfl, (fun e => by cases e), (fun _ hI hIi _ => ⟨?_, (fun e => by cases e), ?_⟩)⟩
    · intro a ha
      rw [union_empty_left]
      simp only [Lab.Touches, Lab.reads, Lab.wval, at_rdi, hl, List.mem_singleton,
        Prod.mk.injEq] at ha
      have ha' : a = l := by
        rcases ha with ⟨v, h1, -⟩ | h2
        · exact h1
        · by_contra hne; simp [Ne.symm hne] at h2
      subst ha'
      exact inv_some hIi
    · intro hok
      rw [union_empty_left] at hok ⊢
      have hrd : hI l = some old := by
        have := hok _ (List.mem_singleton_self _)
        simpa [Lab.reads, at_rdi, hl] using this
      generalize hnew : RmwOp.result rs 4 old (arg.eval rs) op = new at hn
      have hupd : (Lab.rmw md ((at_ .rdi 0).eval rs).toNat 4 old new).updH hI =
          fun x => if x = l then some new else hI x := by
        funext x
        simp only [Lab.updH, Lab.wval, at_rdi, hl]
        by_cases hx : x = l
        · subst hx; simp
        · simp [Ne.symm hx, hx]
      rw [hupd]
      rcases hIi with ⟨hR, hRR, hd, rfl⟩ | ⟨v, hv0, rfl⟩
      · -- free: take `R`
        have hold : old = 0 := by
          simp [union_apply, single_apply] at hrd
          omega
        have hRl : hR l = none := by
          rcases hd l with h | h
          · simp [single_apply] at h
          · exact h
        refine ⟨hR, Heap.single l new, ?_, ?_, Or.inr ⟨new, hn, rfl⟩,
          hQ _ _ hkeep ⟨old, hv', by simp [Regs.set], fun _ => hRR, fun h => absurd hold h⟩,
          fun e => by cases e⟩
        · intro x; by_cases hx : x = l
          · subst hx; exact Or.inl hRl
          · exact Or.inr (by simp [single_apply, hx])
        · funext x
          simp only [union_apply, single_apply]
          by_cases hx : x = l
          · subst hx; simp [hRl]
          · simp only [hx, ite_false]; cases hR x <;> rfl
      · -- taken: nothing changes hands
        have hold : old = v := by simpa [single_apply] using hrd.symm
        refine ⟨Heap.empty, Heap.single l new, disjoint_empty _, ?_, Or.inr ⟨new, hn, rfl⟩,
          hQ _ _ hkeep ⟨old, hv', by simp [Regs.set], fun h => absurd (hold ▸ h) hv0,
            fun _ => rfl⟩, fun e => by cases e⟩
        funext x; rw [union_empty_left]; simp only [single_apply]
        by_cases hx : x = l <;> simp [hx]

/-- **A futex wait on the lock word** from an empty heap: an atomic read of the invariant's cell;
nothing changes hands, and `rax` gets the call's result. -/
theorem safe_wait {l : Nat} {R : HProp} {Q : Regs → HProp} {rs : Regs}
    (hl : (rs .rdi).toNat = l) (hQ : ∀ v, Q (rs.set .rax v) Heap.empty) :
    Csl.Safe (lockInv l R) Q waitStmt rs Heap.empty := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | fwait hv hr =>
    refine ⟨rfl, rfl, (fun e => by cases e),
      (fun _ hI hIi _ => ⟨?_, (fun e => by cases e), ?_⟩)⟩
    · intro a ha
      rw [union_empty_left]
      simp only [Lab.Touches, Lab.reads, Lab.wval, Expr.eval, hl, List.mem_singleton,
        Prod.mk.injEq, Option.isSome_none, Bool.false_eq_true, or_false] at ha
      obtain ⟨_, rfl, -⟩ := ha
      exact inv_some hIi
    · intro _
      refine ⟨Heap.empty, hI, disjoint_empty _, ?_, hIi, hQ _, fun e => by cases e⟩
      funext x; rw [union_empty_left]; simp [Lab.updH, Lab.wval]

/-- **A futex wake** touches no cell. -/
theorem safe_wake {I : HProp} {Q : Regs → HProp} {rs : Regs} {h : Heap} (hQ : Q rs h) :
    Csl.Safe I Q wakeStmt rs h := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | fwake hq =>
    refine ⟨rfl, rfl, (fun e => by cases e), (fun _ hI hIi hd => ⟨?_, (fun e => by cases e), ?_⟩)⟩
    · intro a ha
      simp [Lab.Touches, Lab.reads, Lab.wval] at ha
    · intro _
      refine ⟨h, hI, hd, ?_, hIi, hQ, fun e => by cases e⟩
      funext x; simp [Lab.updH, Lab.wval]

/-! ## Chains -/

theorem safe_chain_cons {I : HProp} {Q : Regs → HProp} {a : Stmt} {l : List Stmt} {rs : Regs}
    {h : Heap} (H : Csl.Safe I (fun rs h => Csl.Safe I Q (Tv.chain l) rs h) a rs h) :
    Csl.Safe I Q (Tv.chain (a :: l)) rs h := safe_seq H

theorem safe_chain_nil {I : HProp} {Q : Regs → HProp} {rs : Regs} {h : Heap} (hq : Q rs h) :
    Csl.Safe I Q (Tv.chain []) rs h := safe_skip hq

/-! ## The lock -/

/-- The slow path with loop bound `L`. -/
def slowL (L : Nat) : Stmt :=
  Tv.chain ([Lock.nr, Lock.op, Lock.val] ++ Lock.body ++
    [.loop L (notE (zTest .rax)) (Tv.chain Lock.body)])

/-- `fmutex_lock`'s program with bound `L`, unfolded. -/
theorem fm_lock_body (L : Nat) : Lock.cert.body L =
    Tv.chain [Lock.zero, Lock.one, Lock.cas, .ite (notE (casZ 0))
      (Tv.chain [.ite (zCmpI .rax 2) (slowL L)
        (Tv.chain [Lock.two, Lock.xchg, .ite (zTest .rax) .skip (slowL L)])]) .skip] := rfl

/-- One round of the wait loop from an empty heap: wait, then exchange in `2`. -/
theorem safe_round {l : Nat} {R : HProp} {Q : Regs → HProp} {rs : Regs}
    (hl : (rs .rdi).toNat = l) (hdx : rs .rdx = 2)
    (hQ : ∀ rs' h', (rs' .rdi).toNat = l → rs' .rdx = 2 → GotV R rs' h' → Q rs' h') :
    Csl.Safe (lockInv l R) Q (Tv.chain Lock.body) rs Heap.empty := by
  simp only [Lock.body]
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons
  refine safe_wait (by simpa [Regs.set] using hl) (fun v => ?_)
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons
  refine safe_acq (by simpa [Regs.set] using hl) (fun old _ => ?_) (fun rs' h' hk hg => ?_)
  · simp [RmwOp.result, Expr.eval, r32, mask32, BinOp.eval, Regs.set, hdx]
  · refine safe_chain_nil (hQ rs' h' ?_ ?_ hg)
    · rw [hk _ (by decide)]; simpa [Regs.set] using hl
    · rw [hk _ (by decide)]; simpa [Regs.set] using hdx

/-- The wait loop. -/
theorem safe_wloop {l : Nat} {R : HProp} {L : Nat} {rs : Regs} {h : Heap}
    (hl : (rs .rdi).toNat = l) (hdx : rs .rdx = 2) (hg : GotV R rs h) :
    Csl.Safe (lockInv l R) (fun rs h => Csl.Safe (lockInv l R) (fun _ h => R h) (Tv.chain []) rs h)
      (.loop L (notE (zTest .rax)) (Tv.chain Lock.body)) rs h := by
  refine safe_loop (fun _ rs h => (rs .rdi).toNat = l ∧ rs .rdx = 2 ∧ GotV R rs h) ?_ ?_
    ⟨hl, hdx, hg⟩
  · intro k rs h ⟨_, _, old, ho, hax, h0, _⟩ hc
    rw [truthy_notE', truthy_zTest ho hax] at hc
    simp only [Bool.not_eq_false', decide_eq_true_eq] at hc
    exact safe_chain_nil (h0 hc)
  · intro k rs h ⟨h1, h2, old, ho, hax, _, h1'⟩ hc
    rw [truthy_notE', truthy_zTest ho hax] at hc
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hc
    rw [h1' hc]
    exact safe_round h1 h2 (fun rs' h' a b c => ⟨a, b, c⟩)

/-- The slow path from an empty heap ends owning `R`. -/
theorem safe_slow {l : Nat} {R : HProp} {L : Nat} {rs : Regs} (hl : (rs .rdi).toNat = l) :
    Csl.Safe (lockInv l R) (fun _ h => R h) (slowL L) rs Heap.empty := by
  simp only [slowL, Lock.body, List.cons_append, List.nil_append]
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  -- one round, as `safe_round` but continuing with the loop
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons
  refine safe_wait (by simpa [Regs.set] using hl) (fun v => ?_)
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons
  refine safe_acq (by simpa [Regs.set] using hl) (fun old _ => ?_) (fun rs' h' hk hg => ?_)
  · simp [RmwOp.result, Expr.eval, r32, mask32, BinOp.eval, Regs.set]
  · apply safe_chain_cons
    refine safe_wloop ?_ ?_ hg
    · rw [hk _ (by decide)]; simpa [Regs.set, Expr.eval] using hl
    · rw [hk _ (by decide)]; simp [Regs.set, Expr.eval]

/-- **Acquire gives the invariant's resource**: the CIR program of `fmutex_lock`, from an empty
heap with `rdi` pointing at the lock word `l`, is CSL-safe under `lockInv l R` for every loop
bound, and ends owning `R`. -/
theorem fm_lock (l : Nat) (R : HProp) (L : Nat) (rs : Regs) (hl : (rs .rdi).toNat = l) :
    Csl.Safe (lockInv l R) (fun _ h => R h) (Lock.cert.body L) rs Heap.empty := by
  rw [fm_lock_body]
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons
  refine safe_acq (by simpa [Regs.set] using hl) (fun old _ => ?_) (fun rs' h' hk hg => ?_)
  · simp [RmwOp.result, Expr.eval, Regs.set, op32, mask32, BinOp.eval]
    first | done | (by_cases h0 : old = 0 <;> simp [h0])
  have hl' : (rs' .rdi).toNat = l := by rw [hk _ (by decide)]; simpa [Regs.set] using hl
  obtain ⟨old, ho, hax, h0, h1⟩ := hg
  apply safe_chain_cons
  apply safe_ite
  · -- the CAS failed: contend
    intro hc
    rw [truthy_casZ0 ho hax] at hc
    simp only [decide_eq_true_eq] at hc
    rw [h1 hc]
    apply safe_chain_cons
    apply safe_ite
    · intro h2
      exact safe_conseq (Q := fun _ h => R h) (fun rs h hq => safe_chain_nil (safe_chain_nil hq))
        (safe_slow (R := R) (L := L) hl')
    · intro _
      apply safe_chain_cons; apply safe_assign
      apply safe_chain_cons
      refine safe_acq (by simpa [Regs.set] using hl') (fun old _ => ?_)
        (fun rs'' h'' hk' hg' => ?_)
      · simp [RmwOp.result, Expr.eval, Regs.set]
      · have hl'' : (rs'' .rdi).toNat = l := by
          rw [hk' _ (by decide)]; simpa [Regs.set] using hl'
        obtain ⟨old', ho', hax', h0', h1'⟩ := hg'
        apply safe_chain_cons
        apply safe_ite
        · intro hz
          rw [truthy_zTest ho' hax'] at hz
          simp only [decide_eq_true_eq] at hz
          exact safe_skip (safe_chain_nil (safe_chain_nil (safe_chain_nil (h0' hz))))
        · intro hz
          rw [truthy_zTest ho' hax'] at hz
          simp only [decide_eq_false_iff_not] at hz
          rw [h1' hz]
          exact safe_conseq (fun rs h hq => safe_chain_nil (safe_chain_nil (safe_chain_nil hq)))
            (safe_slow (R := R) (L := L) hl'')
  · -- the CAS took the lock
    intro hc
    rw [truthy_casZ0 ho hax] at hc
    simp only [decide_eq_false_iff_not, not_not] at hc
    exact safe_skip (safe_chain_nil (h0 hc))

/-! ## The unlock -/

theorem fm_unlock_body (L : Nat) : Unlock.cert.body L =
    Tv.chain [Lock.zero, Unlock.xchg, .ite (zCmpI .rax 2) (Tv.chain Unlock.wake) .skip] := rfl

/-- The wake path, from any heap whose post is `Q`. -/
theorem safe_wakePath {I : HProp} {Q : Regs → HProp} {rs : Regs} {h : Heap}
    (hQ : ∀ rs', Q rs' h) : Csl.Safe I Q (Tv.chain Unlock.wake) rs h := by
  simp only [Unlock.wake]
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons
  exact safe_wake (safe_chain_nil (hQ _))

/-- **Release**: the CIR program of `fmutex_unlock`, from `R ∗ locked l`, is safe under the
invariant and ends with `emp`. -/
theorem fm_unlock {l : Nat} {R : HProp} {L : Nat} {rs : Regs} {h : Heap}
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    Csl.Safe (Spin.inv l R) (fun _ => hemp) (Unlock.cert.body L) rs h := by
  rw [fm_unlock_body]
  apply safe_chain_cons; apply safe_assign
  apply safe_chain_cons
  refine safe_xchg0 (by simpa [Regs.set] using hl) (by simp [Regs.set, zero_eval]) hh
    (fun rs' => ?_)
  apply safe_chain_cons
  apply safe_ite
  · intro _; exact safe_wakePath (fun _ => safe_chain_nil rfl)
  · intro _; exact safe_skip (safe_chain_nil rfl)

/-! ## Static facts -/

theorem fm_lock_spec (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (hl : (rs .rdi).toNat = l) :
    Csl.Safe (Spin.inv l R ∗ J) (fun _ => R ∗ Spin.locked l) (Lock.cert.body L) rs
      Heap.empty :=
  safe_inv_frame (safe_conseq (fun _ _ H => sep_comm H) (fm_lock l (Spin.locked l ∗ R) L rs hl))

theorem fm_unlock_spec (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    Csl.Safe (Spin.inv l R ∗ J) (fun _ => hemp) (Unlock.cert.body L) rs h :=
  safe_inv_frame (fm_unlock hl hh)

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex

namespace Silmaril.X86.Concurrency.Cir.Mutex.Futex

open Silmaril.Proofs.X86.Concurrency.Cir.Mutex

/-- **Drepper's futex mutex as an `Iface`**: `fmutex_lock` and `fmutex_unlock` (exchange
release), with the object, token and invariant. -/
def fmutex : Iface where
  size := 8
  init := Spin.init
  inv := Spin.inv
  locked := Spin.locked
  lockCode := Lock.cert.body
  unlockCode := Unlock.cert.body
  init_dom := spin_init_dom
  init_inv := spin_init_inv
  locked_excl := spin_locked_excl
  lock_spec := fm_lock_spec
  unlock_spec := fm_unlock_spec

end Silmaril.X86.Concurrency.Cir.Mutex.Futex
