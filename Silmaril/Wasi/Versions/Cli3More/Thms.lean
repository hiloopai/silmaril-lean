module

public import Silmaril.Wasi.Versions.Cli3More.Defs
public import Silmaril.Wasi.Versions.FsMore.Thms

@[expose] public section

/-!
# WASI 0.3 environment, exit and clocks: theorems

PROVED (standard axioms):

* **`cli3Impl_sat`**: for every environment `E`, the concrete host `cli3Impl E` is a model of
  `cli3Th E`.
* **`cli3Th_examples`**: the theory is not trivial: it rejects a second `now` below the first,
  a `now` below a `wait-until` bound, an `exit` that returns, a system-clock `instant` with
  `nanoseconds = 10^9`, and arguments other than `E`'s.
-/

namespace Silmaril.Wasi.Versions.Cli3More

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net (gated gated_follows)
open Silmaril.Wasi.Versions.FsMore (charsV strC charsV_strC)

theorem mapM_charsV (l : List (List Char)) : (l.map strC).mapM charsV = some l := by
  induction l with
  | nil => rfl
  | cons s l ih => simp [List.mapM_cons, charsV_strC, ih]

theorem mapM_pairOf (l : List (List Char × List Char)) :
    (l.map fun x => Val.record [strC x.1, strC x.2]).mapM pairOf = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, pairOf, charsV_strC, ih]

theorem optStrOf_optStrV (o : Option (List Char)) : optStrOf (optStrV o) = some o := by
  cases o <;> simp [optStrV, optStrOf, charsV_strC]

theorem le_bmax_left (a b : BitVec 64) : a ≤ bmax a b := by
  unfold bmax; split
  · assumption
  · exact BitVec.le_refl a

theorem le_bmax_right (a b : BitVec 64) : b ≤ bmax a b := by
  unfold bmax; split
  · exact BitVec.le_refl b
  · rename_i h; exact BitVec.le_of_lt (BitVec.not_le.1 h)

/-- **Every answer of the concrete host passes the check.** -/
theorem cli3Impl_ok (E : Env3) (p : List WEv) (f : FnName) (a : List Val) :
    cli3Ok E (p.foldl cli3Next {}) (.imp f a (cli3Impl E p f a)) = true := by
  have hs : p.foldl cli3Next {} = clk3State p := rfl
  rw [hs]
  unfold cli3Ok cli3Impl
  dsimp only
  by_cases h1 : f = getEnv3
  · have hv : (one (some [pairsV E.vars])).bind pairsOf = some E.vars := mapM_pairOf _
    simp only [h1, ↓reduceIte, hv, beq_self_eq_true]
  simp only [h1, ↓reduceIte]
  by_cases h2 : f = getArgs3
  · have hv : (one (some [Val.record (E.args.map strC)])).bind strsOf = some E.args :=
      mapM_charsV _
    simp only [h2, ↓reduceIte, hv, beq_self_eq_true]
  simp only [h2, ↓reduceIte]
  by_cases h3 : f = getCwd3
  · have hv : (one (some [optStrV E.cwd])).bind optStrOf = some E.cwd := optStrOf_optStrV _
    simp only [h3, ↓reduceIte, hv, beq_self_eq_true]
  simp only [h3, ↓reduceIte]
  by_cases h4 : f = exit3 ∨ f = exitCode3
  · simp only [h4, ↓reduceIte, Option.isNone_none]
  simp only [h4, ↓reduceIte]
  by_cases h5 : f = monoNow3
  · simp [h5, le_bmax_left, le_bmax_right]
  simp only [h5, ↓reduceIte]
  by_cases h6 : f = sysNow3
  · simp [h6, instantOk]
  simp only [h6, ↓reduceIte]

/-- **The concrete host is a model of `cli3Th E`.** -/
theorem cli3Impl_sat {Y : Sig.{0}} {I : Set FnName} (E : Env3) :
    (hostSat (cli3Th E).Accepts).holds (concrete (Y := Y) (I := I) (cli3Impl E)) :=
  concrete_sat _ fun _ ht => gated_follows (cli3Impl_ok E) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The theory is not trivial -/

/-- An environment with one argument `a`. -/
def envA : Env3 := ⟨[], [['a']], none⟩

def nowAt (x : Nat) : WEv := .imp monoNow3 [] (some [.u64 (BitVec.ofNat 64 x)])
def untilAt (x : Nat) : WEv := .imp waitUntil3 [.u64 (BitVec.ofNat 64 x)] (some [])
def exitRet : WEv := .imp exit3 [.variant 0 none] (some [])
def sysAt (ns : Nat) : WEv := .imp sysNow3 [] (some [.record [.s64 0, .u32 (BitVec.ofNat 32 ns)]])
def argsAns (l : List (List Char)) : WEv := .imp getArgs3 [] (some [.record (l.map strC)])

/-- **Accepted and rejected runs of `cli3Th envA`.** -/
theorem cli3Th_examples :
    (cli3Th envA).Accepts [nowAt 5, untilAt 9, nowAt 9, argsAns [['a']], sysAt 999999999] ∧
    ¬ (cli3Th envA).Accepts [nowAt 5, nowAt 4] ∧
    ¬ (cli3Th envA).Accepts [nowAt 5, untilAt 9, nowAt 8] ∧
    ¬ (cli3Th envA).Accepts [exitRet] ∧
    ¬ (cli3Th envA).Accepts [sysAt 1000000000] ∧
    ¬ (cli3Th envA).Accepts [argsAns [['b']]] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.Cli3More
