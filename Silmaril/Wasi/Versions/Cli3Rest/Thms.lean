module

public import Silmaril.Wasi.Versions.Cli3Rest.Defs
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# The last 0.3 `cli` and `clocks` imports: theorems

PROVED (standard axioms):

* **`outImpl_sat`**: for every output function `W` other than the canonical built-ins and the
  terminal and resolution functions, and every environment `E`, the host `outImpl W E` is a
  model of `outTh W E`; `stderrImpl3_sat` is the instance `W = stderrWrite3`.
* **`stderrTh3_examples`**: the theory is not trivial: it accepts a run in which the future
  reports `ok` after the writable end is dropped, and rejects the same `ok` before the drop, a
  terminal answer that contradicts `E`, and a resolution other than `E`'s.
-/

namespace Silmaril.Wasi.Versions.Cli3Rest

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net (gated gated_follows)
open Silmaril.Wasi.Versions.P3 (natV natOf cStreamNew cStreamWrite cStreamDropW cFutureRead)

/-- The output function is none of the other functions the host answers. -/
structure OutFn (W : FnName) : Prop where
  new : W ≠ cStreamNew
  fut : W ≠ cFutureRead
  tin : W ≠ termIn3
  tout : W ≠ termOut3
  terr : W ≠ termErr3
  mres : W ≠ monoRes3
  sres : W ≠ sysRes3

theorem futA_ok (q : OutSt) (fv : Val) :
    (match [fv], futA q fv with
     | [fv], some [_, .variant 0 none] => futDone q fv
     | _, _ => true) = true := by
  unfold futA
  by_cases h : futDone q fv
  · simp [h]
  · simp [h]

theorem termA_ok (b : Bool) (h : Nat) : (optSome (termA b h)).all (· == b) = true := by
  cases b <;> simp [termA, optSome]

/-- **Every answer of the host passes the check.** -/
theorem outImpl_ok {W : FnName} (hW : OutFn W) (E : Term3) (p : List WEv) (f : FnName)
    (a : List Val) :
    outOk E (p.foldl (outNext W) {}) (.imp f a (outImpl W E p f a)) = true := by
  have hs : p.foldl (outNext W) {} = outState W p := rfl
  rw [hs]
  unfold outOk outImpl
  dsimp only
  by_cases h1 : f = cStreamNew
  · simp [h1, cStreamNew, cFutureRead, termIn3, termOut3, termErr3, monoRes3, sysRes3,
      Silmaril.Wasi.Versions.P3.canon]
  by_cases h2 : f = W
  · simp [h2, hW.fut, hW.tin, hW.tout, hW.terr, hW.mres, hW.sres]
  simp only [h1, h2, ↓reduceIte]
  by_cases h3 : f = cStreamWrite
  · simp [h3, cStreamWrite, cFutureRead, termIn3, termOut3, termErr3, monoRes3, sysRes3,
      Silmaril.Wasi.Versions.P3.canon]
  simp only [h3, ↓reduceIte]
  by_cases h4 : f = cStreamDropW
  · simp [h4, cStreamDropW, cFutureRead, termIn3, termOut3, termErr3, monoRes3, sysRes3,
      Silmaril.Wasi.Versions.P3.canon]
  simp only [h4, ↓reduceIte]
  by_cases h5 : f = cFutureRead
  · simp only [h5, ↓reduceIte]
    match a with
    | [fv] => exact futA_ok _ fv
    | [] => rfl
    | _ :: _ :: _ => rfl
  simp only [h5, ↓reduceIte]
  by_cases h6 : f = termIn3
  · simp only [h6, ↓reduceIte]; exact termA_ok _ _
  simp only [h6, ↓reduceIte]
  by_cases h7 : f = termOut3
  · simp only [h7, ↓reduceIte]; exact termA_ok _ _
  simp only [h7, ↓reduceIte]
  by_cases h8 : f = termErr3
  · simp only [h8, ↓reduceIte]; exact termA_ok _ _
  simp only [h8, ↓reduceIte]
  by_cases h9 : f = monoRes3
  · simp [h9, u64Is]
  simp only [h9, ↓reduceIte]
  by_cases h10 : f = sysRes3
  · simp [h10, u64Is]
  simp only [h10, ↓reduceIte]

/-- **The host is a model of the theory.** -/
theorem outImpl_sat {Y : Sig.{0}} {I : Set FnName} {W : FnName} (hW : OutFn W) (E : Term3) :
    (hostSat (outTh W E).Accepts).holds (concrete (Y := Y) (I := I) (outImpl W E)) :=
  concrete_sat _ fun _ ht => gated_follows (outImpl_ok hW E) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

theorem stderr_outFn : OutFn stderrWrite3 := by
  constructor <;> simp [stderrWrite3, cStreamNew, cFutureRead, Silmaril.Wasi.Versions.P3.canon,
    termIn3, termOut3, termErr3, monoRes3, sysRes3]

/-- **The 0.3 stderr host is a model of the 0.3 stderr theory.** -/
theorem stderrImpl3_sat {Y : Sig.{0}} {I : Set FnName} (E : Term3) :
    (hostSat (stderrTh3 E).Accepts).holds (concrete (Y := Y) (I := I) (stderrImpl3 E)) :=
  outImpl_sat stderr_outFn E

/-! ## The theory is not trivial -/

/-- stdout is a terminal, the others are not; resolutions 1 ns and 1000 ns. -/
def envT : Term3 := ⟨false, true, false, 1, 1000⟩

def newE : WEv := .imp cStreamNew [] (some [natV 1, natV 2])
def wvsE : WEv := .imp stderrWrite3 [natV 1] (some [natV 3])
def dropE : WEv := .imp cStreamDropW [natV 2] (some [])
def futOk : WEv := .imp cFutureRead [natV 3] (some [natV 0, .variant 0 none])
def termE (f : FnName) (b : Bool) : WEv :=
  .imp f [] (some [if b then .variant 1 (some (natV 7)) else .variant 0 none])
def resE (f : FnName) (x : Nat) : WEv := .imp f [] (some [.u64 (BitVec.ofNat 64 x)])

/-- **Accepted and rejected runs of `stderrTh3 envT`.** -/
theorem stderrTh3_examples :
    (stderrTh3 envT).Accepts [newE, wvsE, dropE, futOk, termE termOut3 true,
      termE termIn3 false, resE monoRes3 1, resE sysRes3 1000] ∧
    ¬ (stderrTh3 envT).Accepts [newE, wvsE, futOk] ∧
    ¬ (stderrTh3 envT).Accepts [termE termErr3 true] ∧
    ¬ (stderrTh3 envT).Accepts [termE termOut3 false] ∧
    ¬ (stderrTh3 envT).Accepts [resE monoRes3 2] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.Cli3Rest
