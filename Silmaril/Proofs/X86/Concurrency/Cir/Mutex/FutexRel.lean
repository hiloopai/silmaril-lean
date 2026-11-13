module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Rel
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.FutexCsl

/-!
# Proofs: Drepper's original unlock with a plain-`mov` release

`fmutex_unlock_dec` is `rax := fetch_sub(rel)([rdi], 1)`; if the old value was not `1`: the call
registers, `[rdi] := 0` (a plain `mov`), `rdx := 1`, `futex_wake([rdi], rdx)`. In the logic with
release stores, from `R ∗ locked l` under the spin invariant (`Spin.inv`, the invariant of the
`fmutex`):

* the `lock sub` is a draining read-modify-write. The thread holds the token, so the word is not
  `0`. With old value `1` it writes `0` and is itself the release (`R` and the token go back to the
  invariant). With any other old value it writes a non-zero value and moves nothing;
* on that path the `mov` of `0` is a **release** (`st_release`, the same store as the
  `spin_unlock`), and the wake is a draining label touching no cell, which ends the pending window.

So `fmutexDec` (`fmutex_lock`, proved in the base CSL and lifted, with `fmutex_unlock_dec`) is an
`IfaceR`, and `Futex.Task.decUnlock` (restated over `ProvedR`) holds.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Futex
open Silmaril.X86.Concurrency.Cir.Prim (at_ lockInv op32 r32 zTest zCmpI)
open Silmaril.X86.Concurrency.Cir.TvCfg (setB notE mask32)
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (casZ waitStmt wakeStmt subZ subImm)

/-! ## The codes drain first -/

theorem df_fmLock (L : Nat) (rs : Regs) : DF (Lock.cert.body L) rs :=
  df_seq_assign (fun _ => df_seq_assign (fun _ => df_seq_rmw))

theorem df_fmUnlock (L : Nat) (rs : Regs) : DF (Unlock.cert.body L) rs :=
  df_seq_assign (fun _ => df_seq_rmw)

/-! ## Values -/

theorem sub_result {rs : Regs} {old : Nat} (ho : old < 2 ^ 32) :
    RmwOp.result rs 4 old ((Expr.lit 1).eval rs) (.op .sub) = (old + 2 ^ 32 - 1) % 2 ^ 32 := by
  simp only [RmwOp.result, Expr.eval, BinOp.eval, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem truthy_subZ1 {rs : Regs} {old : Nat} (ho : old < 2 ^ 32)
    (h : rs .rax = BitVec.ofNat 64 old) :
    truthy ((notE (subZ .rax 1#32)).eval rs) = decide (old ≠ 1) := by
  rw [truthy_notE']
  simp only [subZ, subImm, mask32, Expr.eval, BinOp.eval, truthy, h]
  by_cases h1 : old = 1
  · subst h1; decide
  · have : ¬ (BitVec.ofNat 64 old - BitVec.ofNat 64 1 &&& BitVec.ofNat 64 4294967295) =
        BitVec.ofNat 64 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      rw [show (4294967295 : Nat) % 2 ^ 64 = 2 ^ 32 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod] at this
      omega
    simp [this, h1]

theorem dec_body (L : Nat) : UnlockDec.cert.body L =
    .seq UnlockDec.dec (.seq (.ite (notE (subZ .rax 1#32)) (Tv.chain UnlockDec.wake) .skip)
      .skip) := rfl

/-! ## The `lock sub` -/

/-- The thread holding the token never sees the unlocked state of the invariant. -/
theorem held_not_unlocked {l : Nat} {R : HProp} {h hT hJ : Heap}
    (hh : (R ∗ Spin.locked l) h) (hTT : (Spin.locked l ∗ R) hT)
    (hd : Heap.Disjoint h (Heap.union (Heap.union (Heap.single l 0) hT) hJ)) : False := by
  obtain ⟨u, ev⟩ := Option.isSome_iff_exists.mp (sepLocked_some (sep_comm hTT))
  have : (Heap.union (Heap.union (Heap.single l 0) hT) hJ (Spin.tok l)).isSome := by
    simp only [union_apply, single_apply, tok_ne l, ↓reduceIte, ev]; rfl
  exact disjoint_some hd (sepLocked_some hh) this

/-- **`lock sub [rdi], 1`** from `R ∗ locked l`: with old value `1` it releases `R` and the token
(writing `0`); otherwise it moves nothing. -/
theorem safeR_dec {l : Nat} {R J : HProp} {Q : Bool → Regs → Heap → Heap → Prop} {rs : Regs}
    {p : Bool} {h : Heap} (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h)
    (hQ : ∀ old, old < 2 ^ 32 →
      (old = 1 → Q false (rs.set .rax (BitVec.ofNat 64 old)) Heap.empty Heap.empty) ∧
      (old ≠ 1 → Q false (rs.set .rax (BitVec.ofNat 64 old)) h Heap.empty)) :
    SafeR (liftI (Spin.inv l R ∗ J)) Q p UnlockDec.dec rs h Heap.empty := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | rmw hv =>
    rename_i old
    have ho : old < 2 ^ 32 := hv
    have ha : ((at_ .rdi 0).eval rs).toNat = l := by rw [at_rdi, hl]
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inr rfl, fun hI gI hIi hd _ =>
      ⟨?_, fun e => (by cases e), ?_⟩⟩)⟩
    · obtain ⟨hInv, hJ, -, rfl, iInv, -⟩ := sep_iff.mp hIi
      intro a ta
      have hal : a = l := by
        simp only [Lab.Touches, Lab.reads, Lab.wval, ha, List.mem_singleton,
          Prod.mk.injEq] at ta
        rcases ta with ⟨v, h1, -⟩ | h2
        · exact h1
        · by_contra hne; simp [Ne.symm hne] at h2
      subst hal
      obtain ⟨u, eu⟩ := Option.isSome_iff_exists.mp (inv_some iInv)
      rw [union_apply, union_apply, eu]
      cases h a <;> rfl
    · intro hok
      obtain ⟨hInv, hJ, dIJ, rfl, iInv, jJ⟩ := sep_iff.mp hIi
      have hrd : (Heap.union h (Heap.union hInv hJ)) l = some old := by
        have := hok _ (List.mem_singleton_self _)
        simpa [Lab.reads, ha] using this
      rcases iInv with ⟨hT, hTT, -, rfl⟩ | ⟨v, hv0, rfl⟩
      · exact absurd hd (fun d => held_not_unlocked hh hTT d)
      · have hJl : hJ l = none := by
          rcases dIJ l with e | e
          · simp [single_apply] at e
          · exact e
        have hhl : h l = none := by
          rcases hd l with e | e
          · exact e
          · simp [union_apply, single_apply] at e
        have dhJ : Heap.Disjoint h hJ := fun x => by
          rcases hd x with e | e
          · exact Or.inl e
          · right; rw [union_apply] at e
            revert e
            cases Heap.single l v x <;> simp
        have hold : old = v := by
          simp [union_apply, hhl, single_apply] at hrd; omega
        subst hold
        have hupd : ∀ (n : Nat), (Lab.rmw .rel ((at_ .rdi 0).eval rs).toNat 4 old n).updH
            (Heap.union h (Heap.union (Heap.single l old) hJ)) =
            Heap.union (Heap.union (Heap.single l n) h) hJ := fun n => by
          funext x
          simp only [Lab.updH, Lab.wval, ha, union_apply, single_apply]
          by_cases hx : x = l
          · subst hx; simp
          · simp only [Ne.symm hx, hx, ite_false, Option.none_or]
        rw [hupd, sub_result ho]
        by_cases h1 : old = 1
        · -- the release
          subst h1
          rw [show (1 + 2 ^ 32 - 1) % 2 ^ 32 = 0 by omega]
          refine ⟨Heap.empty, Heap.union (Heap.union (Heap.single l 0) h) hJ, Heap.empty, gI,
            disjoint_empty _, (union_empty_left _).symm, disjoint_empty _, rfl, ?_,
            (hQ 1 (by omega)).1 rfl, fun e => by cases e⟩
          show (Spin.inv l R ∗ J) _
          exact sep_iff.mpr ⟨Heap.union (Heap.single l 0) h, hJ,
            disjoint_union_left.mpr ⟨disjoint_single_left hJl, dhJ⟩, rfl,
            Or.inl ⟨h, sep_comm hh, disjoint_single_left hhl, rfl⟩, jJ⟩
        · -- nothing changes hands
          have hn : (old + 2 ^ 32 - 1) % 2 ^ 32 ≠ 0 := by omega
          generalize (old + 2 ^ 32 - 1) % 2 ^ 32 = nv at hn ⊢
          refine ⟨h, Heap.union (Heap.single l nv) hJ, Heap.empty, gI,
            ?_, ?_, disjoint_empty _, rfl, ?_, (hQ old ho).2 h1, fun e => by cases e⟩
          · exact disjoint_union_right.mpr ⟨disjoint_symm (disjoint_single_left hhl), dhJ⟩
          · funext x
            simp only [union_apply, single_apply]
            by_cases hx : x = l
            · subst hx; simp [hhl]
            · simp [hx]
          · show (Spin.inv l R ∗ J) _
            exact sep_iff.mpr ⟨Heap.single l nv, hJ,
              disjoint_single_left hJl, rfl, Or.inr ⟨_, hn, rfl⟩, jJ⟩

/-! ## The unlock -/

/-- **A futex wake** touches no cell: a local, draining label (it ends a pending window). -/
theorem safeR_wake {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {p : Bool} {rs : Regs}
    {h g : Heap} (hQ : Q false rs h g) : SafeR I Q p wakeStmt rs h g := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | fwake hq =>
    rename_i q
    refine ⟨rfl, rfl, Or.inl ⟨fun a ta => ?_, fun _ => ?_⟩⟩
    · simp [Lab.Touches, Lab.reads, Lab.wval] at ta
    · have e : (Lab.fwake ((Expr.reg .rdi).eval rs).toNat ((Expr.reg .rdx).eval rs).toNat q).updH
          h = h := by funext x; simp [Lab.updH, Lab.wval]
      simp only [Lab.drains, Bool.not_true, Bool.and_false]
      rw [e]; exact hQ

/-- **Drepper's original unlock is a release**, from `R ∗ locked l`, from either flag. -/
theorem dec_release (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (p : Bool) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    SafeR (liftI (Spin.inv l R ∗ J)) (fun _ _ h g => h = Heap.empty ∧ g = Heap.empty) p
      (UnlockDec.cert.body L) rs h Heap.empty := by
  rw [dec_body]
  apply safeR_seq
  refine safeR_dec hl hh (fun old ho => ⟨fun e1 => ?_, fun e1 => ?_⟩)
  · apply safeR_seq
    apply safeR_ite
    · intro hc
      rw [truthy_subZ1 ho (by simp [Regs.set])] at hc
      simp [e1] at hc
    · intro _; exact safeR_skip (safeR_skip ⟨rfl, rfl⟩)
  · apply safeR_seq
    apply safeR_ite
    · intro _
      simp only [UnlockDec.wake, Tv.chain]
      apply safeR_seq; apply safeR_assign
      apply safeR_seq; apply safeR_assign
      apply safeR_seq; apply safeR_assign
      apply safeR_seq
      refine st_release (by simp [Regs.set, hl]) hh ?_
      apply safeR_seq; apply safeR_assign
      apply safeR_seq
      exact safeR_wake (safeR_skip (safeR_skip ⟨rfl, rfl⟩))
    · intro hc
      rw [truthy_subZ1 ho (by simp [Regs.set])] at hc
      simp [e1] at hc

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex

namespace Silmaril.X86.Concurrency.Cir.Mutex.Futex

open Silmaril.Proofs.X86.Concurrency.Cir.Mutex

/-- **The futex mutex as an `IfaceR`** (exchange unlock). -/
def fmutexR : IfaceR :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceR.ofIface fmutex df_fmLock df_fmUnlock

/-- **Drepper's mutex with the original unlock** (`fetch_sub`, then a plain-`mov` release and a
wake) **is an `IfaceR`.** -/
def fmutexDec : IfaceR where
  size := 8
  init := Spin.init
  inv := Spin.inv
  locked := Spin.locked
  lockCode := Lock.cert.body
  unlockCode := UnlockDec.cert.body
  init_dom := spin_init_dom
  init_inv := spin_init_inv
  locked_excl := spin_locked_excl
  lock_spec := fmutexR.lock_spec
  unlock_spec := dec_release

end Silmaril.X86.Concurrency.Cir.Mutex.Futex

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Futex

theorem initAllR_fmutexDec (ls : List Nat) :
    initAllR fmutexDec ls = ls.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    show Heap.union (Spin.init l) (initAllR fmutexDec ls) = _
    rw [ih]; rfl

/-- **`Futex.Task.decUnlock` holds** (as restated). -/
theorem decUnlock_holds : Futex.Task.decUnlock := by
  intro C goal hC hslot L Cf hr hd hf
  have e : C.startWith (fun a => .seq (.assign .rdi a) (Lock.cert.body L))
      (fun a => .seq (.assign .rdi a) (UnlockDec.cert.body L))
      (C.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty) =
      C.linkR fmutexDec L := by
    rw [Client.linkR, initAllR_fmutexDec]; rfl
  rw [e] at hr
  exact link_any_mutexR hC fmutexDec hslot L hr hd hf

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
