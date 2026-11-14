module

public import Silmaril.X86.Concurrency.Cir.Progress.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Progress.Rules

/-!
# Proofs: the spin mutexes and the futex mutex cannot get stuck

All three mutexes access only their lock word `[rdi]`, with 4-byte read-modify-writes, 4-byte
loads and futex calls, and never write `rdi`. `shapeB` checks exactly this shape; `shape_inv`
turns it into `Inv` under `rdi = l` for every width map giving the word at `l` four bytes. The
shape ignores loop bounds (`shapeB_setB`), so one kernel evaluation per program covers every
bound `L`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Progress

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Progress
open Silmaril.X86.Concurrency.Cir.Mutex (Iface spinMutex spinMutexSc)

/-- The two address forms of the mutex code: `[rdi + 0 + 0]` and `[rdi]`. -/
def addrOk (a : Expr) : Bool := a == Prim.at_ .rdi 0 || a == .reg .rdi

theorem addrOk_eval {a : Expr} (h : addrOk a = true) (rs : Regs) :
    (a.eval rs).toNat = (rs .rdi).toNat := by
  simp only [addrOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> simp [Prim.at_, Expr.eval, BinOp.eval]

/-- **The shape of the mutex code**: 4-byte accesses of `[rdi]` (loads, read-modify-writes, futex
calls) and register assignments, never writing `rdi`. -/
def shapeB : Stmt → Bool
  | .skip => true
  | .assign d _ => d != .rdi
  | .load d _ sz _ a => d != .rdi && sz == 4 && addrOk a
  | .rmw d _ sz _ a _ => d != .rdi && sz == 4 && addrOk a
  | .futexWait d a _ => d != .rdi && addrOk a
  | .futexWake _ _ => true
  | .fence _ => true
  | .seq s t => shapeB s && shapeB t
  | .ite _ s t => shapeB s && shapeB t
  | .loop _ _ b => shapeB b
  | _ => false

theorem shapeB_setB (L : Nat) : ∀ s, shapeB (TvCfg.setB L s) = shapeB s
  | .seq s t => by simp [TvCfg.setB, shapeB, shapeB_setB L s, shapeB_setB L t]
  | .ite c s t => by simp [TvCfg.setB, shapeB, shapeB_setB L s, shapeB_setB L t]
  | .loop n c b => by simp [TvCfg.setB, shapeB, shapeB_setB L b]
  | .skip | .assign .. | .load .. | .store .. | .rmw .. | .fence .. | .futexWait ..
  | .futexWake .. | .spawn .. | .join .. | .local .. => rfl

/-- `rdi = l`. -/
def RdiIs (l : Nat) (rs : Regs) : Prop := (rs .rdi).toNat = l

theorem rdiIs_set {l : Nat} {rs : Regs} {d : Reg} (hd : (d != .rdi) = true) (h : RdiIs l rs)
    (v : Word) : RdiIs l (rs.set d v) := by
  have : Silmaril.X86.Reg.rdi ≠ d := fun e => by subst e; simp at hd
  simpa [RdiIs, Regs.set, this] using h

/-- **The shape gives progress** under `rdi = l`, if the word at `l` has four bytes. -/
theorem shape_inv {w : Nat → Option Nat} {l : Nat} (hw : w l = some 4) :
    ∀ s, shapeB s = true → Inv w (RdiIs l) s (RdiIs l)
  | .skip, _ => inv_skip
  | .assign d e, h => inv_assign fun rs hA => rdiIs_set h hA _
  | .load d m sz fl a, h => by
    simp only [shapeB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hd, rfl⟩, ha⟩ := h
    exact inv_load (fun rs hA => ⟨4, by rw [addrOk_eval ha, hA]; exact hw, le_refl _⟩)
      fun rs hA v => rdiIs_set hd hA v
  | .rmw d m sz op a arg, h => by
    simp only [shapeB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hd, rfl⟩, ha⟩ := h
    exact inv_rmw (fun rs hA => by rw [addrOk_eval ha, hA]; exact hw)
      fun rs hA v => rdiIs_set hd hA v
  | .futexWait d a v, h => by
    simp only [shapeB, Bool.and_eq_true] at h
    obtain ⟨hd, ha⟩ := h
    exact inv_fwait (fun rs hA => ⟨4, by rw [addrOk_eval ha, hA]; exact hw, le_refl _⟩)
      fun rs hA x => rdiIs_set hd hA x
  | .futexWake a n, _ => inv_fwake fun _ h => h
  | .fence k, _ => inv_fence fun _ h => h
  | .seq s t, h => by
    simp only [shapeB, Bool.and_eq_true] at h
    exact inv_seq (shape_inv hw s h.1) (shape_inv hw t h.2)
  | .ite c s t, h => by
    simp only [shapeB, Bool.and_eq_true] at h
    exact inv_ite (shape_inv hw s h.1) (shape_inv hw t h.2)
  | .loop n c b, h => inv_loop (shape_inv hw b h)
  | .store .., h | .spawn .., h | .join .., h | .local .., h => by simp [shapeB] at h

/-- The widths of the object at `l`: the lock word has four bytes, the token cell is free. -/
def spinWd (l a : Nat) : Option Nat := if a = l then some 4 else none

theorem spinWd_dom (l a k : Nat) (h : spinWd l a = some k) : l ≤ a ∧ a < l + 8 := by
  simp only [spinWd] at h
  split at h
  · omega
  · cases h

theorem spinInit_fits (l a v : Nat) (h : Mutex.Spin.init l a = some v) : fits (spinWd l) a v := by
  intro k _
  have : v = 0 := by
    simp only [Mutex.Spin.init, Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion,
      Heap.single] at h
    by_cases h1 : a = l
    · simp [h1] at h; exact h.symm
    · by_cases h2 : a = Mutex.Spin.tok l
      · have : Mutex.Spin.tok l ≠ l := by simp [Mutex.Spin.tok]
        simp [h2, this] at h; exact h.symm
      · simp [h1, h2] at h
  subst this
  exact pow_pos' k

theorem agrees_word {w : Nat → Option Nat} {l : Nat} (h : Agrees w (spinWd l) l 8) :
    w l = some 4 := by
  rw [h l (le_refl _) (by omega)]; simp [spinWd]

/-- A mutex of the object whose two programs have the shape. -/
theorem live_of_shape {lk ul : Nat → Stmt} (hl : ∀ L, shapeB (lk L) = true)
    (hu : ∀ L, shapeB (ul L) = true) (l L : Nat) {w : Nat → Option Nat}
    (hag : Agrees w (spinWd l) l 8) :
    Inv w (fun rs => (rs .rdi).toNat = l) (lk L) (fun _ => True) ∧
      Inv w (fun rs => (rs .rdi).toNat = l) (ul L) (fun _ => True) :=
  ⟨inv_conseq (fun _ h => h) (fun _ _ => trivial) (shape_inv (agrees_word hag) _ (hl L)),
    inv_conseq (fun _ h => h) (fun _ _ => trivial) (shape_inv (agrees_word hag) _ (hu L))⟩

theorem spinLock_shape (L : Nat) : shapeB (Prim.SpinLock.cert.body L) = true := by
  rw [TvCfg.GCert.body, shapeB_setB]; decide

theorem spinUnlock_shape (L : Nat) : shapeB (Mutex.Spin.unlockCert.body L) = true := by
  rw [TvCfg.GCert.body, shapeB_setB]; decide

theorem spinUnlockSc_shape (L : Nat) : shapeB (Mutex.Spin.unlockScCert.body L) = true := by
  rw [TvCfg.GCert.body, shapeB_setB]; decide

theorem fLock_shape (L : Nat) : shapeB (Mutex.Futex.Lock.cert.body L) = true := by
  rw [TvCfg.Fx.FCert.body, shapeB_setB]; decide

theorem fUnlock_shape (L : Nat) : shapeB (Mutex.Futex.Unlock.cert.body L) = true := by
  rw [TvCfg.Fx.FCert.body, shapeB_setB]; decide

/-- **The spin mutex cannot get stuck.** -/
def spinLive : MutexLive spinMutex where
  wd := spinWd
  wd_dom := spinWd_dom
  init_fits := spinInit_fits
  lock_inv l L _ hag := (live_of_shape spinLock_shape spinUnlock_shape l L hag).1
  unlock_inv l L _ hag := (live_of_shape spinLock_shape spinUnlock_shape l L hag).2

/-- **The spin mutex with the `seq_cst` unlock cannot get stuck.** -/
def spinScLive : MutexLive spinMutexSc where
  wd := spinWd
  wd_dom := spinWd_dom
  init_fits := spinInit_fits
  lock_inv l L _ hag := (live_of_shape spinLock_shape spinUnlockSc_shape l L hag).1
  unlock_inv l L _ hag := (live_of_shape spinLock_shape spinUnlockSc_shape l L hag).2

/-- **The futex mutex cannot get stuck.** -/
def fmutexLive : MutexLive Mutex.Futex.fmutex where
  wd := spinWd
  wd_dom := spinWd_dom
  init_fits := spinInit_fits
  lock_inv l L _ hag := (live_of_shape fLock_shape fUnlock_shape l L hag).1
  unlock_inv l L _ hag := (live_of_shape fLock_shape fUnlock_shape l L hag).2

end Silmaril.Proofs.X86.Concurrency.Cir.Progress
