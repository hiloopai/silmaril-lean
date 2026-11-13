module

public import Silmaril.Wasm.JcoTool.KFitBuf.Defs
public import Silmaril.Wasm.JcoTool.KLive.Thms

/-!
# `kRechunk n` fits

The step of `kRechunk n` pushes the byte and, when the buffer holds `n` bytes, emits its length
and the buffer and clears it. Every reachable state holds fewer than `n` bytes
(`rechunk_feed_inv`), and the potential `o + 2 · |buf|` (bytes in the output region plus twice
the buffer) grows by at most `2` per byte (`rechunk_step`), so `N ≤ 256` bytes never fill the
`CAP`-byte regions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KFitBuf

open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt kRechunk)
open Silmaril.Wasm.JcoTool.KCore

theorem lit_mod (n : Nat) (hn : n < 256) : n % Silmaril.Wasm.Component.Streams.Kernel.M32 = n :=
  Nat.mod_eq_of_lt (by simp [Silmaril.Wasm.Component.Streams.Kernel.M32]; omega)

/-- The step of `kRechunk n` from a state with fewer than `n` bytes. -/
theorem rechunk_exec (n b : Nat) (s : KSt) (hn : n < 256) (hb : s.buf.length < n) :
    (kRechunk n).step.exec b s =
      if s.buf.length + 1 = n then (⟨s.st, []⟩, (n % 256) :: (s.buf ++ [b % 256]))
      else (⟨s.st, s.buf ++ [b % 256]⟩, []) := by
  by_cases h : s.buf.length + 1 = n
  · simp [kRechunk, KStmt.exec, KExp.eval, h, Silmaril.Wasm.Component.Streams.Kernel.M32]
    omega
  · simp [kRechunk, KStmt.exec, KExp.eval, h, Silmaril.Wasm.Component.Streams.Kernel.M32]
    omega

/-- The step's checks pass when the output region has room for a chunk. -/
theorem rechunk_fitsS (n b o : Nat) (s : KSt) (hn : n < 256) (hb : s.buf.length < n)
    (ho : o + n + 1 ≤ CAP) : fitsS b (kRechunk n).step s o = true := by
  simp [kRechunk, fitsS, KStmt.exec, KExp.eval, lit_mod n hn]
  simp only [CAP] at ho ⊢
  omega

/-- The flush's checks pass. -/
theorem rechunk_flush_fits (n : Nat) (s : KSt) (hb : s.buf.length < 256) :
    fitsS 0 (kRechunk n).flush s 0 = true := by
  simp [kRechunk, fitsS, KStmt.exec, KExp.eval, CAP]; omega

/-- The buffer stays below `n`. -/
theorem rechunk_step_inv (n b : Nat) (s : KSt) (hn : n < 256) (hb : s.buf.length < n) :
    ((kRechunk n).step.exec b s).1.buf.length < n := by
  rw [rechunk_exec n b s hn hb]
  split
  · simp only [List.length_nil]; omega
  · simp only [List.length_append, List.length_singleton]; omega

/-- The potential `o + 2 · |buf|` grows by at most `2` per byte. -/
theorem rechunk_pot (n b : Nat) (s : KSt) (hn : n < 256) (hb : s.buf.length < n) :
    ((kRechunk n).step.exec b s).2.length + 2 * ((kRechunk n).step.exec b s).1.buf.length ≤
      2 * s.buf.length + 2 := by
  rw [rechunk_exec n b s hn hb]
  split
  · simp only [List.length_cons, List.length_append, List.length_nil]; omega
  · simp only [List.length_nil, List.length_append, List.length_singleton]; omega

theorem rechunk_done (n : Nat) (s : KSt) : (kRechunk n).tr.done s = false := rfl

/-- **Every reachable state of `kRechunk n` holds fewer than `n` bytes.** -/
theorem rechunk_feed_inv (n : Nat) (hn : n < 256) :
    ∀ (xs : List Nat) (s : KSt), s.buf.length < n → ((kRechunk n).tr.feed s xs).1.buf.length < n := by
  intro xs
  induction xs with
  | nil => intro s hs; exact hs
  | cons x xs ih =>
    intro s hs
    have e : ((kRechunk n).tr.feed s (x :: xs)).1 =
        ((kRechunk n).tr.feed ((kRechunk n).step.exec x s).1 xs).1 := by
      simp only [Tr.feed, rechunk_done n s, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [e]
    exact ih _ (rechunk_step_inv n x s hn hs)

/-- **The checks pass while `kRechunk n` is fed** up to the potential bound. -/
theorem rechunk_fitsF (n : Nat) (hn : n < 256) :
    ∀ (bs : List Nat) (s : KSt) (o : Nat), s.buf.length < n →
      o + 2 * s.buf.length + 2 * bs.length + n + 3 ≤ CAP → fitsF (kRechunk n) s bs o = true := by
  intro bs
  induction bs with
  | nil => intro _ _ _ _; rfl
  | cons b bs ih =>
    intro s o hs ho
    have hl : (b :: bs).length = bs.length + 1 := rfl
    have hpot := rechunk_pot n b s hn hs
    have hf : fitsS b (kRechunk n).step s o = true := rechunk_fitsS n b o s hn hs (by omega)
    have hr : fitsF (kRechunk n) ((kRechunk n).step.exec b s).1 bs
        (o + ((kRechunk n).step.exec b s).2.length) = true :=
      ih _ _ (rechunk_step_inv n b s hn hs) (by omega)
    simp only [fitsF, rechunk_done n s, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
    exact ⟨hf, hr⟩

/-- **`kRechunk n` fits**, for every read size up to `256`. -/
theorem rechunk_fits (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) {N : Nat} (hN : N ≤ 256) :
    Silmaril.Wasm.JcoTool.KLive.KFits (kRechunk n) N := by
  intro xs bs _ _ hl
  have h0 : (kRechunk n).tr.init.buf.length < n := by simp [KM.tr, kRechunk]; omega
  have hinv := rechunk_feed_inv n (by omega) xs (kRechunk n).tr.init h0
  exact ⟨rechunk_fitsF n (by omega) bs _ 0 hinv (by simp only [CAP]; omega),
    rechunk_flush_fits n _ (by omega)⟩

end Silmaril.Proofs.Wasm.JcoTool.KFitBuf
