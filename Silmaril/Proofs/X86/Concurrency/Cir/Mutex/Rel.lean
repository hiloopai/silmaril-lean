module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Spin
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms

/-!
# Proofs: the Mutex interface with release stores

* `link_any_mutexR`: a client proved against `IfaceR` gets its goal on TSO with any `IfaceR`
  (`Csl.Rel.rel_tso`).
* `IfaceR.ofIface`: an `Iface` whose lock and unlock drain first is an `IfaceR`
  (`Csl.Rel.safeR_lift`, `Csl.Rel.safeR_flag`); `spinMutexR`, `spinMutexScR`.
* `mov_release`: `spin_unlock` (a plain `mov` of `0`) releases `R ∗ locked l` to the spin
  invariant, by the release rule: with the token, the invariant cannot be unlocked, so in every
  invariant state the store makes it the unlocked state holding `R` and the token.
* `spinMov : IfaceR` and `movUnlock_holds : Task.movUnlock`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex

/-! ## Linking -/

theorem link_any_mutexR {C : Client} {goal : (Nat → Regs) → Heap → Prop} (hC : C.ProvedR goal)
    (M : IfaceR) (hM : M.size ≤ C.slot) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso C.N (C.linkR M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < C.N, (Cf.ts t).1 = .skip) : goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨I, Q, hs, gs, hI, gI, G, hgoal⟩ := hC M hM L
  obtain ⟨hs', gs', hI', gI', ps', q, i, l1, l2, -, -, -⟩ :=
    rel_tso (G0 := Heap.empty) G (fun _ e => by simp [Heap.empty] at e) hr hd hf
  exact hgoal _ _ hs' gs' hI' gI' ps' q i l1 l2

/-! ## `Iface`s whose code drains first -/

/-- The split of a lifted invariant: all of it belongs to the `Iface`. -/
theorem liftI_split {I0 : HProp} :
    ∀ hI gI, liftI I0 hI gI → ∃ hA hB, Heap.Disjoint hA hB ∧ hI = Heap.union hA hB ∧ I0 hA ∧
      ∀ hA', I0 hA' → Heap.Disjoint hA' hB → liftI I0 (Heap.union hA' hB) gI :=
  fun hI _ i => ⟨hI, Heap.empty, disjoint_empty_right _, (union_empty_right hI).symm, i,
    fun hA' i' _ => by show I0 _; rw [union_empty_right]; exact i'⟩

/-- **An `Iface` whose lock and unlock drain first is an `IfaceR`.** -/
def IfaceR.ofIface (M : Iface) (hl : ∀ L rs, DF (M.lockCode L) rs)
    (hu : ∀ L rs, DF (M.unlockCode L) rs) : IfaceR where
  size := M.size
  init := M.init
  inv := M.inv
  locked := M.locked
  lockCode := M.lockCode
  unlockCode := M.unlockCode
  init_dom := M.init_dom
  init_inv := M.init_inv
  locked_excl := M.locked_excl
  lock_spec l R J L rs p hrs :=
    safeR_flag (hl L rs) (safeR_lift (g := Heap.empty) liftI_split (M.lock_spec l R J L rs hrs)) p
  unlock_spec l R J L rs p h hrs hh :=
    safeR_flag (hu L rs) (safeR_conseq (fun _ _ _ _ x => ⟨x.2.1, x.2.2⟩)
      (safeR_lift (g := Heap.empty) liftI_split (M.unlock_spec l R J L rs h hrs hh))) p

theorem df_spinLock (L : Nat) (rs : Regs) : DF (Prim.SpinLock.cert.body L) rs :=
  df_seq_assign (fun _ => df_seq_assign (fun _ => df_seq_rmw))

theorem df_unlock (L : Nat) (rs : Regs) : DF (Spin.unlockCert.body L) rs :=
  df_seq_assign (fun _ => df_seq_rmw)

theorem df_unlockSc (L : Nat) (rs : Regs) : DF (Spin.unlockScCert.body L) rs :=
  df_seq_assign (fun _ => df_seq_rmw)

/-! ## The `mov` release -/

theorem mov_body (L : Nat) : movUnlockCode L = .seq Prim.SpinUnlock.st .skip := rfl

/-- **The release store** `mov dword [rdi], 0` gives `R ∗ locked l` back to the spin invariant
(framed by any `J`), from either pending flag, leaving the flag set. -/
theorem st_release {l : Nat} {R J : HProp} {Q : Bool → Regs → Heap → Heap → Prop} {rs : Regs}
    {p : Bool} {h : Heap} (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h)
    (hQ : Q true rs Heap.empty Heap.empty) :
    SafeR (liftI (Spin.inv l R ∗ J)) Q p Prim.SpinUnlock.st rs h Heap.empty := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | store =>
    refine ⟨rfl, rfl, Or.inr (Or.inr ⟨.rel, .wb, _, 4, _, rfl, by decide, Heap.empty, h,
      Heap.empty, Heap.empty, disjoint_empty _, (union_empty_left h).symm, disjoint_empty _,
      (union_empty_left _).symm, hQ, ?_⟩)⟩
    intro hI gI hIi hd _
    obtain ⟨hInv, hJ, dIJ, rfl, iInv, jJ⟩ := sep_iff.mp hIi
    have ha : ((Prim.at_ .rdi 0).eval rs).toNat = l := by rw [at_rdi, hl]
    have hv : ((Expr.lit 0).eval rs).toNat % 2 ^ (8 * 4) = 0 := by simp [Expr.eval]
    rw [ha, hv]
    have htok := sepLocked_some hh
    rcases iInv with ⟨hT, hTT, -, rfl⟩ | ⟨v, hv0, rfl⟩
    · -- unlocked: impossible, the invariant would hold the token the thread holds
      exfalso
      obtain ⟨u, ev⟩ := Option.isSome_iff_exists.mp (sepLocked_some (sep_comm hTT))
      have : (Heap.union (Heap.union (Heap.single l 0) hT) hJ (Spin.tok l)).isSome := by
        simp only [union_apply, single_apply, tok_ne l, ↓reduceIte, ev]; rfl
      exact disjoint_some hd htok this
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
      refine ⟨⟨l, 0, false, rfl, by simp [union_apply, single_apply, hhl]⟩, ?_⟩
      show (Spin.inv l R ∗ J) _
      refine sep_iff.mpr ⟨Heap.union (Heap.single l 0) h, hJ, ?_, ?_, Or.inl ⟨h, sep_comm hh,
        disjoint_single_left hhl, rfl⟩, jJ⟩
      · exact disjoint_union_left.mpr ⟨disjoint_single_left hJl |> disjoint_symm |>
          disjoint_symm, dhJ⟩
      · funext x
        simp only [Ent.apply, union_apply, single_apply]
        by_cases hx : x = l
        · subst hx; simp
        · simp only [hx, ite_false]

/-- **`spin_unlock` is a release** of `R ∗ locked l` to the spin invariant (framed by any `J`),
from either pending flag. -/
theorem mov_release (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (p : Bool) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    SafeR (liftI (Spin.inv l R ∗ J)) (fun _ _ h g => h = Heap.empty ∧ g = Heap.empty) p
      (movUnlockCode L) rs h Heap.empty := by
  rw [mov_body]
  apply safeR_seq
  exact st_release hl hh (safeR_skip ⟨rfl, rfl⟩)

/-! ## The interfaces -/

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex

namespace Silmaril.X86.Concurrency.Cir.Mutex

open Silmaril.Proofs.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Csl.Rel

/-- **The spin mutex as an `IfaceR`** (exchange unlock). -/
def spinMutexR : IfaceR :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceR.ofIface spinMutex df_spinLock df_unlock

/-- **The spin mutex with `mutex_unlock_sc`, as an `IfaceR`.** -/
def spinMutexScR : IfaceR :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceR.ofIface spinMutexSc df_spinLock df_unlockSc

/-- **The spin lock with the `mov`-release unlock is an `IfaceR`.** -/
def spinMov : IfaceR where
  size := 8
  init := Spin.init
  inv := Spin.inv
  locked := Spin.locked
  lockCode := Prim.SpinLock.cert.body
  unlockCode := movUnlockCode
  init_dom := spin_init_dom
  init_inv := spin_init_inv
  locked_excl := spin_locked_excl
  lock_spec := spinMutexR.lock_spec
  unlock_spec := mov_release

end Silmaril.X86.Concurrency.Cir.Mutex

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex

theorem initAllR_spinMov (ls : List Nat) :
    initAllR spinMov ls = ls.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    show Heap.union (Spin.init l) (initAllR spinMov ls) = _
    rw [ih]; rfl

/-- **`Task.movUnlock` holds.** -/
theorem movUnlock_holds : Task.movUnlock := by
  intro C goal hC hslot L Cf hr hd hf
  have e : C.startWith (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body L))
      (fun a => .seq (.assign .rdi a) (movUnlockCode L))
      (C.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty) = C.linkR spinMov L := by
    rw [Client.linkR, initAllR_spinMov]; rfl
  rw [e] at hr
  exact link_any_mutexR hC spinMov hslot L hr hd hf

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
