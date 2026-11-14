module

public import Silmaril.Wasi.Versions.HttpOnce.Defs
public import Silmaril.Wasi.Versions.HttpAttr.Thms

@[expose] public section

/-!
# WASI `wasi:http` 0.2 bodies at most once: theorems

PROVED (standard axioms): **`onceImpl_sat`**, the concrete host is a model of `onceTh`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- Every answer of the concrete host passes the check. -/
theorem onceImpl_ok (p : List WEv) (f : FnName) (a : List Val) :
    onceOk (p.foldl onceNext []) (.imp f a (onceImpl p f a)) = true := by
  by_cases ht : f ∈ onceTakes
  · by_cases hq : selfH a ∈ p.foldl onceNext []
    · simp [onceOk, onceImpl, ht, hq, isOkAns, errV]
    · simp [onceOk, onceImpl, ht, hq]
  · simp [onceOk, ht]

/-- **The concrete host is a model of the at-most-once theory.** -/
theorem onceImpl_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat onceTh.Accepts).holds (concrete (Y := Y) (I := I) onceImpl) :=
  concrete_sat _ fun _ ht => gated_follows onceImpl_ok (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

end Silmaril.Wasi.Versions.Net
