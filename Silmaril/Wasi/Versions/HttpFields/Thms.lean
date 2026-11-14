module

public import Silmaril.Wasi.Versions.HttpFields.Defs
public import Silmaril.Wasi.Versions.HttpBody.Thms
public import Silmaril.Wasi.Versions.Net3.Over.Thms

@[expose] public section

/-!
# WASI `wasi:http` headers: theorems

PROVED (standard axioms):

* `fieldsTh_step`: a step of the theory on a function of the slice is the step of its
  operation (`opOk`, `opNext`), the same in every version.
* **`fieldsImpl_sat`**: for every slice `N` (in particular `fieldsFns2`, `fieldsFns3`), the
  concrete host `fieldsImpl N` is a model of `fieldsTh N`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- Values decode back. -/
theorem valsOf_valsV (l : List (List (BitVec 8))) : valsOf (valsV l) = some l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    have ih' : valsOfL (t.map bytesV) = some t := ih
    show valsOfL (bytesV b :: t.map bytesV) = some (b :: t)
    simp [valsOfL, bytesV, ih']

/-- **A step on a function of the slice** is the step of its operation. -/
theorem fieldsTh_step (N : FieldsFns) {f : FnName} {o : FOp} (h : N.op f = some o) (q : FSt)
    (a : List Val) (r : Option (List Val)) :
    (fieldsTh N).step q (.imp f a r) = if opOk o q a r then some (opNext o q a r) else none := by
  simp [fieldsTh, gated, fOk, fNext, h]

/-- The check of a host answer on tracked fields. -/
theorem opCheck_ans (o : FOp) (m : Fields) (h : BitVec 32) (q : FSt) (fresh : BitVec 32)
    (a' : List Val) (hs : selfFields q (.u32 h :: a') = some m) :
    opCheck o m a' (opAns o q fresh (.u32 h :: a')) = true := by
  cases o
  case entries => rcases a' with _ | ⟨nv, a''⟩ <;> simp [opCheck, opAns, hs, fieldsOf_fieldsV]
  case fromList => rcases a' with _ | ⟨nv, a''⟩ <;> simp [opCheck, opAns, fieldsOf]
  all_goals
    rcases a' with _ | ⟨nv, a''⟩
    · simp [opCheck, opAns]
    · cases hn : nameOf nv <;> simp [opCheck, opAns, hn, hs, valsOf_valsV, okV]

/-- **A host answer passes the check.** -/
theorem opAns_ok (o : FOp) (q : FSt) (fresh : BitVec 32) (a : List Val) :
    opOk o q a (opAns o q fresh a) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    cases hl : lookup h q with
    | none => simp [opOk, hl]
    | some o' =>
      cases o' with
      | none => simp [opOk, hl]
      | some m =>
        have hs : selfFields q (.u32 h :: a') = some m := by simp [selfFields, selfH, hl]
        simpa [opOk, hl] using opCheck_ans o m h q fresh a' hs
  all_goals rfl

/-- Every answer of the concrete host passes the check. -/
theorem fieldsImpl_ok (N : FieldsFns) (p : List WEv) (f : FnName) (a : List Val) :
    fOk N (p.foldl (fNext N) []) (.imp f a (fieldsImpl N p f a)) = true := by
  cases hf : N.op f with
  | none => simp [fOk, hf]
  | some o =>
    simp only [fOk, fieldsImpl, hf]
    exact opAns_ok o (fieldsState N p) (BitVec.ofNat 32 p.length) a

/-- **The concrete `fields` host is a model of the `fields` theory.** -/
theorem fieldsImpl_sat {Y : Sig.{0}} {I : Set FnName} (N : FieldsFns) :
    (hostSat (fieldsTh N).Accepts).holds (concrete (Y := Y) (I := I) (fieldsImpl N)) :=
  concrete_sat _ fun _ ht => gated_follows (fieldsImpl_ok N) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

end Silmaril.Wasi.Versions.Net
