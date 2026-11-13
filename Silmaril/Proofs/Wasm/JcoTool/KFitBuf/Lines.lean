module

public import Silmaril.Wasm.JcoTool.KFitBuf.Defs
public import Silmaril.Wasm.JcoTool.KLive.Thms
public import Silmaril.Wasm.Component.Streams.Kernel.Thms

/-!
# `kLines nl` does not fit; `kLinesS nl` has the same runs and is small

* `lines_not_fits`: after `CAP` bytes without a newline the buffer is full (`lines_feed_rep`), and
  the next byte's `push` fails its check: `KFits (kLines nl) N` is false for every `N ≥ 1`.
* `linesS_feed`: feeding the same bytes, the unbuffered kernel has output what the buffered one
  output, followed by its buffer, and its state says whether that buffer is empty; so the runs
  agree (`linesS_run`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KFitBuf

open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt kLines Bytes)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KFitBuf

theorem lines_done (nl : Nat) (s : KSt) : (kLines nl).tr.done s = false := rfl

theorem linesS_done (nl : Nat) (s : KSt) : (kLinesS nl).tr.done s = false := rfl

/-- The step of `kLines nl` on a byte. -/
theorem lines_step (nl b : Nat) (s : KSt) (hnl : nl < 256) (hb : b < 256) :
    (kLines nl).step.exec b s =
      if b = nl then (⟨s.st, []⟩, s.buf ++ [nl]) else (⟨s.st, s.buf ++ [b]⟩, []) := by
  have h1 : nl % 4294967296 = nl := Nat.mod_eq_of_lt (by omega)
  have h2 : nl % 256 = nl := Nat.mod_eq_of_lt hnl
  have h3 : b % 256 = b := Nat.mod_eq_of_lt hb
  by_cases h : b = nl
  · simp [kLines, KStmt.exec, KExp.eval, Silmaril.Wasm.Component.Streams.Kernel.M32, h, h1, h2]
  · simp [kLines, KStmt.exec, KExp.eval, Silmaril.Wasm.Component.Streams.Kernel.M32, h, h1, h3]

/-- The step of `kLinesS nl` on a byte. -/
theorem linesS_step (nl b : Nat) (s : KSt) (hnl : nl < 256) (hb : b < 256) :
    (kLinesS nl).step.exec b s = (⟨if b = nl then 0 else 1, s.buf⟩, [b]) := by
  have h1 : nl % 4294967296 = nl := Nat.mod_eq_of_lt (by omega)
  have h3 : b % 256 = b := Nat.mod_eq_of_lt hb
  by_cases h : b = nl
  · simp [kLinesS, KStmt.exec, KExp.eval, Silmaril.Wasm.Component.Streams.Kernel.M32, h, h1, hnl]
  · simp [kLinesS, KStmt.exec, KExp.eval, Silmaril.Wasm.Component.Streams.Kernel.M32, h, h1, h3]

/-- Bytes without a newline go to the buffer. -/
theorem lines_feed_rep (nl b : Nat) (hnl : nl < 256) (hb : b < 256) (hne : b ≠ nl) :
    ∀ (k : Nat) (s : KSt), ((kLines nl).tr.feed s (List.replicate k b)).1 =
      ⟨s.st, s.buf ++ List.replicate k b⟩ := by
  intro k
  induction k with
  | zero => intro s; simp [Tr.feed]
  | succ k ih =>
    intro s
    have hs : (kLines nl).step.exec b s = (⟨s.st, s.buf ++ [b]⟩, []) := by
      rw [lines_step nl b s hnl hb]; simp [hne]
    have e : ((kLines nl).tr.feed s (List.replicate (k + 1) b)).1 =
        ((kLines nl).tr.feed ((kLines nl).step.exec b s).1 (List.replicate k b)).1 := by
      simp only [List.replicate_succ, Tr.feed, lines_done nl s, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [e, hs, ih]
    simp only [List.append_assoc, List.singleton_append]
    rw [← List.replicate_succ, List.replicate_succ']

/-- **`kLines nl` does not fit**: a line of `CAP` bytes fills its buffer; the next byte traps. -/
theorem lines_not_fits (nl : Nat) (hnl : nl < 256) {N : Nat} (hN : 0 < N) :
    ¬ Silmaril.Wasm.JcoTool.KLive.KFits (kLines nl) N := by
  intro hf
  let b := if nl = 0 then 1 else 0
  have hb : b < 256 := by simp only [b]; split <;> omega
  have hne : b ≠ nl := by simp only [b]; split <;> omega
  have hst := lines_feed_rep nl b hnl hb hne CAP (kLines nl).tr.init
  have hfit := (hf (List.replicate CAP b) [b] (by simp [hb]) (by simp [hb]) (by simp; omega)).1
  rw [hst] at hfit
  have hnl32 : nl % 4294967296 = nl := Nat.mod_eq_of_lt (by omega)
  have hpush : fitsS b (kLines nl).step ⟨(kLines nl).tr.init.st,
      (kLines nl).tr.init.buf ++ List.replicate CAP b⟩ 0 = false := by
    simp [kLines, fitsS, KExp.eval, Silmaril.Wasm.Component.Streams.Kernel.M32, hne, hnl32]
  simp [fitsF, lines_done, hpush] at hfit

/-- One step of each kernel, in the relation of `linesS_feed`. -/
theorem lines_rel_step (nl b : Nat) (hnl : nl < 256) (hb : b < 256) (st : Nat) (buf : List Nat) :
    buf ++ ((kLinesS nl).step.exec b ⟨if buf = [] then 0 else 1, []⟩).2 =
      ((kLines nl).step.exec b ⟨st, buf⟩).2 ++ ((kLines nl).step.exec b ⟨st, buf⟩).1.buf ∧
    ((kLinesS nl).step.exec b ⟨if buf = [] then 0 else 1, []⟩).1 =
      ⟨if ((kLines nl).step.exec b ⟨st, buf⟩).1.buf = [] then 0 else 1, []⟩ ∧
    ((kLines nl).step.exec b ⟨st, buf⟩).1.st = st := by
  rw [lines_step nl b _ hnl hb, linesS_step nl b _ hnl hb]
  by_cases h : b = nl
  · simp [h]
  · simp [h]

theorem feed_cons_lines (nl x : Nat) (xs : List Nat) (s : KSt) :
    (kLines nl).tr.feed s (x :: xs) =
      (((kLines nl).tr.feed ((kLines nl).step.exec x s).1 xs).1,
        ((kLines nl).step.exec x s).2 ++ ((kLines nl).tr.feed ((kLines nl).step.exec x s).1 xs).2) := by
  simp only [Tr.feed, lines_done nl s, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem feed_cons_linesS (nl x : Nat) (xs : List Nat) (s : KSt) :
    (kLinesS nl).tr.feed s (x :: xs) =
      (((kLinesS nl).tr.feed ((kLinesS nl).step.exec x s).1 xs).1,
        ((kLinesS nl).step.exec x s).2 ++ ((kLinesS nl).tr.feed ((kLinesS nl).step.exec x s).1 xs).2) := by
  simp only [Tr.feed, linesS_done nl s, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **The unbuffered kernel has output the buffered one's output, then its buffer.** -/
theorem linesS_feed (nl : Nat) (hnl : nl < 256) :
    ∀ (bs : List Nat), Bytes bs → ∀ (st : Nat) (buf : List Nat),
      buf ++ ((kLinesS nl).tr.feed ⟨if buf = [] then 0 else 1, []⟩ bs).2 =
        ((kLines nl).tr.feed ⟨st, buf⟩ bs).2 ++ ((kLines nl).tr.feed ⟨st, buf⟩ bs).1.buf ∧
      ((kLinesS nl).tr.feed ⟨if buf = [] then 0 else 1, []⟩ bs).1 =
        ⟨if ((kLines nl).tr.feed ⟨st, buf⟩ bs).1.buf = [] then 0 else 1, []⟩ := by
  intro bs
  induction bs with
  | nil => intro _ st buf; exact ⟨by simp [Tr.feed], rfl⟩
  | cons b bs ih =>
    intro hb st buf
    have hb0 : b < 256 := hb b (by simp)
    have hbs : Bytes bs := fun x hx => hb x (by simp [hx])
    obtain ⟨h1, h2, -⟩ := lines_rel_step nl b hnl hb0 st buf
    obtain ⟨i1, i2⟩ := ih hbs ((kLines nl).step.exec b ⟨st, buf⟩).1.st
      ((kLines nl).step.exec b ⟨st, buf⟩).1.buf
    rw [feed_cons_lines, feed_cons_linesS, h2]
    refine ⟨?_, i2⟩
    show buf ++ (_ ++ _) = (_ ++ _) ++ _
    rw [← List.append_assoc, h1, List.append_assoc, i1, List.append_assoc]

theorem linesS_flush (nl f : Nat) (hnl : nl < 256) (b : List Nat) :
    (kLinesS nl).tr.flush ⟨f, b⟩ = if f = 0 then [] else [nl] := by
  have h1 : nl % 4294967296 % 256 = nl := by omega
  by_cases h : f = 0
  · simp [KM.tr, kLinesS, KStmt.exec, KExp.eval, h]
  · simp [KM.tr, kLinesS, KStmt.exec, KExp.eval, Silmaril.Wasm.Component.Streams.Kernel.M32, h, h1]

theorem lines_flush (nl : Nat) (hnl : nl < 256) (s : KSt) :
    (kLines nl).tr.flush s = if s.buf = [] then [] else s.buf ++ [nl] := by
  have h1 : nl % 4294967296 % 256 = nl := by omega
  by_cases h : s.buf = []
  · simp [KM.tr, kLines, KStmt.exec, KExp.eval, h]
  · simp [KM.tr, kLines, KStmt.exec, KExp.eval, Silmaril.Wasm.Component.Streams.Kernel.M32, h, h1]

/-- **The runs agree** on byte streams. -/
theorem linesS_run (nl : Nat) (hnl : nl < 256) (bs : List Nat) (hb : Bytes bs) :
    (kLinesS nl).tr.run bs = (kLines nl).tr.run bs := by
  have hi : (kLinesS nl).tr.init = ⟨if ([] : List Nat) = [] then 0 else 1, []⟩ := by
    simp [KM.tr, kLinesS, Silmaril.Wasm.Component.Streams.Kernel.M32]
  have hl : (kLines nl).tr.init = ⟨0, []⟩ := by simp [KM.tr, kLines, Silmaril.Wasm.Component.Streams.Kernel.M32]
  obtain ⟨h1, h2⟩ := linesS_feed nl hnl bs hb 0 []
  rw [List.nil_append] at h1
  show (kLinesS nl).tr.run bs = (kLines nl).tr.run bs
  unfold Tr.run
  simp only []
  rw [hi, h1, h2, hl, linesS_flush nl _ hnl, lines_flush nl hnl]
  by_cases he : ((kLines nl).tr.feed ⟨0, []⟩ bs).1.buf = []
  · simp [he]
  · simp [he]

end Silmaril.Proofs.Wasm.JcoTool.KFitBuf
