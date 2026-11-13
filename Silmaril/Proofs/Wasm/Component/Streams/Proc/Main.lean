module

public import Silmaril.Proofs.Wasm.Component.Streams.Proc.Inv
public import Silmaril.Wasm.Component.Streams.Spec.Thms

/-!
# The pipeline: main proofs

* `step_inv`, `reach_inv`: every reachable system satisfies the invariant.
* `fin_correct`: when the three components have finished, the consumer holds `T.run F`.
* `prefix_safe`: at every point, what the consumer has received is a prefix of `T.run F`.
* `no_fault`: the transformer never sees its reader gone.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Proc

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Proc
open Silmaril.Proofs.Wasm.Component.Streams.Spec

variable {σ : Type}

/-- **One step of any component preserves the invariant.** -/
theorem step_inv (T : Tr σ Val Val) (N : Nat) (F : List Val) {s s' : Sys σ}
    (hI : Inv T F s) (h : Step T N s s') : Inv T F s' := by
  obtain ⟨A, B, WA, RA, WB, RB, hst, hIA⟩ := hI
  cases h with
  | prod hp =>
    obtain ⟨A', WA', rfl, hI'⟩ := pStep_inv T F _ _ _ A B WA RA WB RB _ _ hIA (hst ▸ hp)
    exact ⟨A', B, WA', RA, WB, RB, rfl, hI'⟩
  | trans ht =>
    obtain ⟨A', B', RA', WB', rfl, hI'⟩ :=
      tStep_inv T N F _ _ _ A B WA RA WB RB _ _ hIA (hst ▸ ht)
    exact ⟨A', B', WA, RA', WB', RB, rfl, hI'⟩
  | cons n _ hc =>
    obtain ⟨B', RB', rfl, hI'⟩ := cStep_inv T F _ _ _ A B WA RA WB RB n _ _ hIA (hst ▸ hc)
    exact ⟨A, B', WA, RA, WB, RB', rfl, hI'⟩

theorem steps_inv (T : Tr σ Val Val) (N : Nat) (F : List Val) {s s' : Sys σ}
    (h : Steps T N s s') (hI : Inv T F s) : Inv T F s' := by
  induction h with
  | refl => exact hI
  | tail _ hs ih => exact step_inv T N F ih hs

/-- **Every reachable system satisfies the invariant.** -/
theorem reach_inv (T : Tr σ Val Val) (N : Nat) (cs : List (List Val)) {s : Sys σ}
    (h : Reach T N cs s) : Inv T cs.flatten s := by
  obtain ⟨st₀, hst, hs⟩ := h
  have h0 : st₀ = toStore {} {} := by
    rw [setup_eq] at hst
    exact (Option.some.inj hst).symm
  exact steps_inv T N _ hs (h0 ▸ inv_init T cs)

/-! ## Correctness at the end -/

/-- What the reader has taken was transferred. -/
theorem RInv.prefix {hr : Nat} {rv : RV} {a : CS} {R : List Val} (h : RInv hr rv a R) :
    R <+: a.c.sent := by
  cases rv with
  | idle => exact h.2.2.2.2 ▸ List.prefix_refl _
  | stopped => exact h.2.2.2.2 ▸ List.prefix_refl _
  | wait =>
    rcases h.2.2 with ⟨_, -, -, hs⟩ | ⟨_, ys, -, -, hs⟩ | ⟨-, -, -, hs⟩
    · exact hs ▸ List.prefix_refl _
    · exact hs ▸ List.prefix_append _ _
    · exact hs ▸ List.prefix_refl _

/-- The items a writer is writing. -/
def wpend : WV → List Val
  | .wait xs => xs
  | _ => []

/-- What was transferred is what the writer knows, followed by part of what it is writing. -/
theorem WInv.sent_le {hw : Nat} {wv : WV} {a : CS} {W : List Val} (h : WInv hw wv a W) :
    a.c.sent <+: W ++ wpend wv := by
  cases wv with
  | idle => exact h.2.2.2.2 ▸ List.prefix_append _ _
  | closed => exact h.2.2.2.2 ▸ List.prefix_append _ _
  | wait xs =>
    rcases h.2.2 with ⟨-, -, hs⟩ | ⟨k, -, -, hs⟩ | ⟨-, -, -, hs⟩
    · exact hs ▸ List.prefix_append _ _
    · rw [hs]
      exact (List.prefix_append_right_inj W).mpr (List.take_prefix k xs)
    · exact hs ▸ List.prefix_append _ _

theorem pdata_le (F : List Val) (p : PPc) (W : List Val) (A : CS) (h : PData F p W A) :
    W ++ wpend (pView p) <+: F := by
  cases p with
  | send cs => exact ⟨cs.flatten, by simpa [wpend, pView, PData] using h⟩
  | wait c cs => exact ⟨cs.flatten, by rw [List.append_assoc]; exact h⟩
  | close => simpa [wpend, pView] using h.1
  | fin => simpa [wpend, pView] using h.1

/-- The transformer's output when it stopped reading is the whole output. -/
theorem stopped_run (T : Tr σ Val Val) (F R : List Val) (hs : Stopped T F R) (hR : R <+: F) :
    T.run R = T.run F := by
  rcases hs with rfl | hd
  · rfl
  · exact run_prefix_done T R F hd hR

/-- The transformer's written and pending outputs are a prefix of `T.run F`. -/
theorem tlink_le (T : Tr σ Val Val) (F : List Val) (t : TPc σ) (R W : List Val)
    (h : TLink T F t R W) (hR : R <+: F) : W ++ wpend (tW t) <+: T.run F := by
  have hP : (T.feed T.init R).2 <+: T.run F := by
    obtain ⟨X, rfl⟩ := hR
    exact (Tr.runP_mono T R X).trans (Tr.runP_le_run T (R ++ X))
  have hS : ∀ ys, Stopped T F R → W ++ ys = T.run R → W ++ ys <+: T.run F := fun ys hs he =>
    he ▸ (stopped_run T F R hs hR) ▸ List.prefix_refl _
  cases t with
  | rd s => simpa [wpend, tW, h.2] using hP
  | wtR s => simpa [wpend, tW, h.2] using hP
  | eoi s => simpa [wpend, tW, h.2.1] using hP
  | wr ys next =>
    rw [tW_wr, show wpend .idle = [] from rfl, List.append_nil]
    cases next with
    | some s => exact (List.prefix_append W ys).trans (h.2 ▸ hP)
    | none => exact (List.prefix_append W ys).trans (hS ys h.2 h.1)
  | wtW ys next =>
    cases next with
    | some s => exact h.2 ▸ hP
    | none => exact hS ys h.2 h.1
  | cl => exact hS [] h.2 (by simpa using h.1)
  | fin => exact hS [] h.2 (by simpa using h.1)
  | fault => exact h.elim

/-- **Safety**: at every point, the consumer's items are a prefix of `T.run F`. -/
theorem prefix_safe (T : Tr σ Val Val) (F : List Val) (s : Sys σ) (hI : Inv T F s) :
    ∀ acc, (s.c = .recv acc ∨ s.c = .wait acc ∨ s.c = .close acc ∨ s.c = .fin acc) →
      acc <+: T.run F := by
  intro acc hc
  obtain ⟨A, B, WA, RA, WB, RB, -, hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have hacc : acc = RB := by
    rcases hc with h | h | h | h <;> (rw [h] at hC; first | exact hC | exact hC.1)
  have hRF : RA <+: F := hRA.prefix.trans (hWA.sent_le.trans (pdata_le F s.p WA A hP))
  rw [hacc]
  exact hRB.prefix.trans (hWB.sent_le.trans (tlink_le T F s.t RA WB hT hRF))

/-- **Correctness at the end**: when all three components have finished, the consumer holds
exactly `T.run F`. -/
theorem fin_correct (T : Tr σ Val Val) (F : List Val) (s : Sys σ) (hI : Inv T F s)
    (hp : s.p = .fin) (ht : s.t = .fin) (acc : List Val) (hc : s.c = .fin acc) :
    acc = T.run F := by
  obtain ⟨A, B, WA, RA, WB, RB, -, hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have hC' : CData (.fin acc) RB B := hc ▸ hC
  have hRB' : RInv 3 .stopped B RB := by simpa [hc, cView] using hRB
  have hWB' : WInv 4 .closed B WB := by simpa [ht, tW] using hWB
  have hT' : TLink T F .fin RA WB := ht ▸ hT
  have hRA' : RInv 1 .stopped A RA := by simpa [ht, tR] using hRA
  have hWA' : WInv 2 .closed A WA := by simpa [hp, pView] using hWA
  have hP' : PData F .fin WA A := hp ▸ hP
  have hRF : RA <+: F := by
    rw [← hRA'.2.2.2.2, hWA'.2.2.2.2]
    exact hP'.1
  rw [hC'.1, ← hRB'.2.2.2.2, hWB'.2.2.2.2, hT'.1]
  exact stopped_run T F RA hT'.2 hRF

/-- The transformer never finds its reader gone. -/
theorem no_fault (T : Tr σ Val Val) (F : List Val) (s : Sys σ) (hI : Inv T F s) :
    s.t ≠ .fault := by
  intro ht
  obtain ⟨A, B, WA, RA, WB, RB, -, -, -, -, -, -, hT, -⟩ := hI
  rw [ht] at hT
  exact hT

end Silmaril.Proofs.Wasm.Component.Streams.Proc
