module

public import Silmaril.Wasm.JcoTool.KFit.Defs
public import Silmaril.Wasm.JcoTool.KLive.Thms

/-!
# Small kernels fit, and their networks are live without hypotheses on the kernels

* `small_fits`: a `Small` kernel satisfies `KLive.KFits k N` for every read size `N ≤ 256`.
* `kInc_small`, `kNoDigit_small`, `kTake_small`: the kernels `map (+1)`, `filter (not a digit)` and
  `take n` of the tests are small.
* `kchain_small_exec`, `ktee_small_exec`: every maximal execution of a chain (of any length) or a
  tee of generated modules of small kernels ends with the sinks holding the kernels' composite,
  with no hypothesis left on the kernels.
* `small_notrap`, `small_reads`: the `KRead` pipe model of a small kernel's module never traps and
  reads as its transformer; `kInc_flushNil`, `kNoDigit_flushNil`, `kTake_flushNil`: the three test
  kernels flush nothing when done, so `KRead.core_game` applies to them with no hypothesis on the
  kernel.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KFit

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Kernel (KStmt KM KSt kInc kNoDigit kTake)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KDrop (runs)

theorem exec_len : ∀ (p : KStmt) (b : Nat) (ks : KSt), noBuf p = true →
    (p.exec b ks).2.length ≤ maxEmit p
  | .skip, _, _, _ => by simp [KStmt.exec, maxEmit]
  | .emit _, _, _, _ => by simp [KStmt.exec, maxEmit]
  | .set _, _, _, _ => by simp [KStmt.exec, maxEmit]
  | .clear, _, _, _ => by simp [KStmt.exec, maxEmit]
  | .push _, _, _, h => by simp [noBuf] at h
  | .emitBuf, _, _, h => by simp [noBuf] at h
  | .seq p q, b, ks, h => by
    have hp := exec_len p b ks (by simp [noBuf] at h; exact h.1)
    have hq := exec_len q b (p.exec b ks).1 (by simp [noBuf] at h; exact h.2)
    simp only [KStmt.exec, List.length_append, maxEmit]
    omega
  | .ite c p q, b, ks, h => by
    have hp := exec_len p b ks (by simp [noBuf] at h; exact h.1)
    have hq := exec_len q b ks (by simp [noBuf] at h; exact h.2)
    simp only [KStmt.exec, maxEmit]
    split <;> omega

theorem fitsS_small : ∀ (p : KStmt) (b : Nat) (ks : KSt) (o : Nat), noBuf p = true →
    o + maxEmit p ≤ CAP → fitsS b p ks o = true
  | .skip, _, _, _, _, _ => rfl
  | .set _, _, _, _, _, _ => rfl
  | .clear, _, _, _, _, _ => rfl
  | .emit _, _, _, o, _, h => by simp only [maxEmit] at h; simp [fitsS]; omega
  | .push _, _, _, _, h, _ => by simp [noBuf] at h
  | .emitBuf, _, _, _, h, _ => by simp [noBuf] at h
  | .seq p q, b, ks, o, h, hc => by
    have h₁ : noBuf p = true := by simp [noBuf] at h; exact h.1
    have h₂ : noBuf q = true := by simp [noBuf] at h; exact h.2
    have hl := exec_len p b ks h₁
    simp only [maxEmit] at hc
    simp only [fitsS, Bool.and_eq_true]
    exact ⟨fitsS_small p b ks o h₁ (by omega), fitsS_small q b _ _ h₂ (by omega)⟩
  | .ite c p q, b, ks, o, h, hc => by
    have h₁ : noBuf p = true := by simp [noBuf] at h; exact h.1
    have h₂ : noBuf q = true := by simp [noBuf] at h; exact h.2
    simp only [maxEmit] at hc
    simp only [fitsS]
    split
    · exact fitsS_small p b ks o h₁ (by omega)
    · exact fitsS_small q b ks o h₂ (by omega)

theorem fitsF_small {k : KM} (hk : Small k = true) :
    ∀ (bs : List Nat) (ks : KSt) (o : Nat), o + bs.length ≤ CAP → fitsF k ks bs o = true := by
  have hs : noBuf k.step = true ∧ maxEmit k.step ≤ 1 := by
    simp only [Small, Bool.and_eq_true, decide_eq_true_eq] at hk; exact ⟨hk.1.1.1, hk.1.1.2⟩
  intro bs
  induction bs with
  | nil => intro _ _ _; rfl
  | cons b bs ih =>
    intro ks o ho
    simp only [List.length_cons] at ho
    have hl := exec_len k.step b ks hs.1
    simp only [fitsF]
    split
    · rfl
    · simp only [Bool.and_eq_true]
      exact ⟨fitsS_small _ _ _ _ hs.1 (by omega), ih _ _ (by omega)⟩

/-- **A small kernel fits**, for every read size up to 256. -/
theorem small_fits {k : KM} (hk : Small k = true) {N : Nat} (hN : N ≤ 256) : KFits k N := by
  have hf : noBuf k.flush = true ∧ maxEmit k.flush ≤ 1 := by
    simp only [Small, Bool.and_eq_true, decide_eq_true_eq] at hk; exact ⟨hk.1.2, hk.2⟩
  intro xs bs _ _ hl
  exact ⟨fitsF_small hk bs _ 0 (by simp only [CAP]; omega),
    fitsS_small _ _ _ 0 hf.1 (by simp only [CAP]; omega)⟩

theorem kInc_small : Small kInc = true := rfl

theorem kNoDigit_small : Small kNoDigit = true := rfl

theorem kTake_small (n : Nat) : Small (kTake n) = true := rfl

/-- **Chains of small kernels are live and correct**, with no hypothesis on the kernels. -/
theorem kchain_small_exec {xs : List Val} {ks : List KM} {Nb : Nat → Nat}
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26) (hs : ∀ k ∈ ks, Small k = true)
    {r : Nat → MSys (kchainM xs ks Nb).net} (hr : MExec _ r) :
    ∃ n, ∀ j, n ≤ j → r j = r n ∧ (∃ b, ((r n).ns (snkM xs ks Nb)).rd = .gone b) ∧
      ((r n).ns (snkM xs ks Nb)).got = runs ks xs :=
  kchain_exec_correct hN hws (fun i h => small_fits (hs _ (List.getElem_mem h)) (hN i).2) hr

/-- **Tees of small kernels are live and correct.** -/
theorem ktee_small_exec {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) (s₁ : Small k₁ = true) (s₂ : Small k₂ = true)
    {r : Nat → MSys (ktee xs k₁ k₂ N₁ N₂).net} (hr : MExec _ r) :
    ∃ n, ∀ j, n ≤ j → r j = r n ∧ ((r n).ns (4 : Fin 6)).got = (trV k₁).run xs ∧
      ((r n).ns (5 : Fin 6)).got = (trV k₂).run xs :=
  ktee_exec_correct h₁ h₂ (small_fits s₁ h₁.2) (small_fits s₂ h₂.2) hr

/-! ## The pipe model of `KRead` -/

/-- **A small kernel's module never traps** in the pipe model. -/
theorem small_notrap {k : KM} (hk : Small k = true) {N : Nat} (hN : 0 < N ∧ N ≤ 256) :
    Silmaril.Wasm.JcoTool.KRead.NoTrapAt k N :=
  genD_notrap_fits hN (small_fits hk hN.2)

/-- **A small kernel's module reads as its transformer** in the pipe model. -/
theorem small_reads {k : KM} (hk : Small k = true) {N : Nat} (hN : 0 < N ∧ N ≤ 256)
    (hfl : Silmaril.Wasm.JcoTool.KRead.FlushNil k) :
    (Silmaril.Wasm.JcoTool.KRead.dropObs k N).Reads (trV k) :=
  genD_reads_fits hN (small_fits hk hN.2) hfl

theorem kInc_flushNil : Silmaril.Wasm.JcoTool.KRead.FlushNil kInc := fun _ _ => rfl

theorem kNoDigit_flushNil : Silmaril.Wasm.JcoTool.KRead.FlushNil kNoDigit := fun _ _ => rfl

theorem kTake_flushNil (n : Nat) : Silmaril.Wasm.JcoTool.KRead.FlushNil (kTake n) := fun _ _ => rfl

end Silmaril.Wasm.JcoTool.KFit
