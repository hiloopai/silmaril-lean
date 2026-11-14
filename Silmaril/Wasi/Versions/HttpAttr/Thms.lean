module

public import Silmaril.Wasi.Versions.HttpAttr.Defs
public import Silmaril.Wasi.Versions.HttpFields.Thms

@[expose] public section

/-!
# WASI `wasi:http` attributes: theorems

PROVED (standard axioms):

* `attrTh_step`: a step of the theory on a function of the slice is the step of its operation
  (`aOk`, `aNext`), the same in every version.
* **`attrImpl_sat`**: for every slice `N` (in particular `attrFns2`, `attrFns3`), the concrete
  host `attrImpl N` is a model of `attrTh N`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- **A step on a function of the slice** is the step of its operation. -/
theorem attrTh_step (N : AttrFns) {f : FnName} {o : AOp} (h : N.op f = some o) (q : AttrSt)
    (a : List Val) (r : Option (List Val)) :
    (attrTh N).step q (.imp f a r) = if aOk o q a r then some (aNext o q a r) else none := by
  simp [attrTh, gated, aOkE, aNextE, h]

/-- A trap passes every check. -/
theorem aOk_none (o : AOp) (q : AttrSt) (a : List Val) : aOk o q a none = true := by
  unfold aOk; split <;> (try split) <;> simp_all [isOkAns]

/-- A host answer of a getter passes the check. -/
theorem aAns_ok_get (k : Nat) (q : AttrSt) (n : Nat) (a : List Val) :
    aOk (.get k) q a (aAns (.get k) q n a) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    cases hl : lookup h q with
    | none => simp [aOk, aAns, hl]
    | some o' =>
      cases o' with
      | none => simp [aOk, aAns, hl]
      | some m =>
        cases hk : attrOf m k with
        | none => simp [aOk, aAns, hl, hk]
        | some v => simp [aOk, aAns, selfAttrs, selfH, hl, hk]
  all_goals rfl

/-- A host answer of a setter passes the check. -/
theorem aAns_ok_set (k : Nat) (q : AttrSt) (n : Nat) (a : List Val) :
    aOk (.set k) q a (aAns (.set k) q n a) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    cases hl : lookup h q with
    | none => simp [aOk, hl]
    | some o' =>
      cases o' with
      | none => simp [aOk, hl]
      | some m =>
        cases hi : isImm m <;> simp [aOk, aAns, selfAttrs, selfH, hl, hi, isOkAns, okV, errV]
  all_goals rfl

/-- **A host answer passes the check.** -/
theorem aAns_ok (o : AOp) (q : AttrSt) (n : Nat) (a : List Val) : aOk o q a (aAns o q n a) = true := by
  cases o with
  | get k => exact aAns_ok_get k q n a
  | set k => exact aAns_ok_set k q n a
  | ctor ks t => cases t <;> rfl
  | _ => rfl

/-- Every answer of the concrete host passes the check. -/
theorem attrImpl_ok (N : AttrFns) (p : List WEv) (f : FnName) (a : List Val) :
    aOkE N (p.foldl (aNextE N) []) (.imp f a (attrImpl N p f a)) = true := by
  cases hf : N.op f with
  | none => simp [aOkE, hf]
  | some o =>
    simp only [aOkE, attrImpl, hf]
    exact aAns_ok o (attrState N p) p.length a

/-- **The concrete attribute host is a model of the attribute theory.** -/
theorem attrImpl_sat {Y : Sig.{0}} {I : Set FnName} (N : AttrFns) :
    (hostSat (attrTh N).Accepts).holds (concrete (Y := Y) (I := I) (attrImpl N)) :=
  concrete_sat _ fun _ ht => gated_follows (attrImpl_ok N) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

end Silmaril.Wasi.Versions.Net
