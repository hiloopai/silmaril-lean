module

public import Silmaril.Wasi.Versions.HttpHdr.Defs
public import Silmaril.Wasi.Versions.HttpAttr.Thms

@[expose] public section

/-!
# WASI `wasi:http` headers of requests and responses: theorems

PROVED (standard axioms):

* `hdrTh_step`: a step of the theory on a function of the slice is the step of its operation.
* **`hdrImpl_sat`**: for every slice `N` (in particular `hdrFns2`, `hdrFns3`), the concrete
  host `hdrImpl N` is a model of `hdrTh N`: immutable children refuse mutations, invalid names
  and values are refused, and the `fields` answers are those of `fieldsImpl`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- **A step on a function of the slice** is the step of its operation. -/
theorem hdrTh_step (N : HdrFns) {f : FnName} {o : HOp} (h : N.op f = some o) (q : HdrSt)
    (a : List Val) (r : Option (List Val)) :
    (hdrTh N).step q (.imp f a r) = if hOk o q a r then some (hNext o q a r) else none := by
  simp [hdrTh, gated, hOkE, hNextE, h]

/-- `lookup` through a map of the values. -/
theorem lookup_mapSnd {α β : Type} (g : α → β) (h : BitVec 32) (l : List (BitVec 32 × α)) :
    lookup h (l.map fun x => (x.1, g x.2)) = (lookup h l).map g := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    by_cases hx : x.1 = h
    · simp [lookup, hx]
    · simpa [lookup, List.find?_cons, hx] using ih

/-- An error answer passes the `fields` check of a mutation or of `from-list`. -/
theorem opCheck_err {o : FOp} (ho : o.mutates = true ∨ o = .fromList) (m : Fields) (a' : List Val)
    (e : Option Val) : opCheck o m a' (some [errV e]) = true := by
  rcases a' with _ | ⟨nv, a''⟩ <;> cases o <;> first | rfl | simp [FOp.mutates] at ho

/-- Invalid arguments only occur for `set`, `append`, `from-list`. -/
theorem argsOk_false {o : FOp} {a : List Val} (h : argsOk o a = false) :
    o.mutates = true ∨ o = .fromList := by
  by_contra hc
  have hs : o ≠ .set ∧ o ≠ .append ∧ o ≠ .fromList := by cases o <;> simp_all [FOp.mutates]
  have ht : argsOk o a = true := by unfold argsOk; split <;> simp_all
  simp [ht] at h

/-- The `fields` part of the check, on a known handle, for an error answer. -/
theorem rest_err {o : FOp} (ho : o.mutates = true ∨ o = .fromList) (m? : Option Fields)
    (imm : Bool) (a' : List Val) {e : Option Val} (hi : (!(o.mutates && imm) || immOk (some [errV e])) = true) :
    ((!(o.mutates && imm) || immOk (some [errV e])) &&
      match m? with
      | some m => opCheck o m a' (some [errV e])
      | none => true) = true := by
  cases m? with
  | none => simpa using hi
  | some m => simpa [opCheck_err ho m a' e] using hi

/-- The `fields` check after the host's error answer `e`. -/
theorem hOkF_err {o : FOp} (ho : o.mutates = true ∨ o = .fromList) (q : HdrSt) (a : List Val)
    {e : Option Val} (hi : ∀ h a', a = .u32 h :: a' → ∀ m? imm, lookup h q.fs = some (m?, imm) →
      (!(o.mutates && imm) || immOk (some [errV e])) = true) :
    hOkF o q a (some [errV e]) = true := by
  have hk : isOkAns (some [errV e]) = false := rfl
  unfold hOkF
  rw [hk]
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    cases hl : lookup h q.fs with
    | none => simp only [hl, Bool.not_false, Bool.true_or, Bool.and_self]
    | some p =>
      obtain ⟨m?, imm⟩ := p
      simp only [hl, Bool.not_false, Bool.true_or, Bool.true_and]
      exact rest_err ho m? imm a' (hi h a' rfl m? imm hl)
  all_goals rfl

/-- The `fields` check after a forwarded `fieldsImpl` answer, on valid arguments and a handle
that is mutable or not mutated. -/
theorem hOkF_ans (o : FOp) (q : HdrSt) (fresh : BitVec 32) (a : List Val) (hv : argsOk o a = true)
    (hm : (o.mutates && selfImm q a) = false) : hOkF o q a (opAns o q.proj fresh a) = true := by
  unfold hOkF
  rw [hv, Bool.or_true, Bool.true_and]
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    cases hl : lookup h q.fs with
    | none => simp only [hl]
    | some p =>
      obtain ⟨m?, imm⟩ := p
      have hi : (o.mutates && imm) = false := by simpa [selfImm, hl] using hm
      have hs : selfFields q.proj (.u32 h :: a') = m? := by
        simp [selfFields, selfH, HdrSt.proj, lookup_mapSnd Prod.fst, hl]
      have hc : (!(o.mutates && imm)) = true := by simp [hi]
      simp only [hl, hc, Bool.true_or, Bool.true_and]
      cases hp : m? with
      | none => rfl
      | some m => exact opCheck_ans o m h q.proj fresh a' (hs.trans hp)
  all_goals rfl

/-- **A host answer of a `fields` operation passes the check.** -/
theorem hAnsF_ok (o : FOp) (q : HdrSt) (fresh : BitVec 32) (a : List Val) :
    hOkF o q a (hAnsF o q fresh a) = true := by
  unfold hAnsF
  by_cases hi : (o.mutates && selfImm q a) = true
  · simp only [hi, ↓reduceIte]
    have hmu : o.mutates = true := (Bool.and_eq_true _ _ ▸ hi).1
    exact hOkF_err (Or.inl hmu) q a fun _ _ _ _ _ _ => by simp [immOk, errV]
  · simp only [hi, Bool.false_eq_true, ↓reduceIte]
    have hi' : (o.mutates && selfImm q a) = false := by simpa using hi
    by_cases hv : argsOk o a = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact hOkF_ans o q fresh a hv hi'
    · have hv' : argsOk o a = false := by simpa using hv
      simp only [hv', Bool.not_false, ↓reduceIte]
      refine hOkF_err (argsOk_false hv') q a fun h a' ha m? imm hl => ?_
      have : (o.mutates && imm) = false := by simpa [selfImm, ha, hl] using hi'
      simp [this]

/-- **A host answer passes the check.** -/
theorem hAns_ok (o : HOp) (q : HdrSt) (n : Nat) (a : List Val) : hOk o q a (hAns o q n a) = true := by
  cases o with
  | f o => exact hAnsF_ok o q _ a
  | _ => rfl

/-- Every answer of the concrete host passes the check. -/
theorem hdrImpl_ok (N : HdrFns) (p : List WEv) (f : FnName) (a : List Val) :
    hOkE N (p.foldl (hNextE N) {}) (.imp f a (hdrImpl N p f a)) = true := by
  cases hf : N.op f with
  | none => simp [hOkE, hf]
  | some o =>
    simp only [hOkE, hdrImpl, hf]
    exact hAns_ok o (hdrState N p) p.length a

/-- **The concrete headers host is a model of the headers theory.** -/
theorem hdrImpl_sat {Y : Sig.{0}} {I : Set FnName} (N : HdrFns) :
    (hostSat (hdrTh N).Accepts).holds (concrete (Y := Y) (I := I) (hdrImpl N)) :=
  concrete_sat _ fun _ ht => gated_follows (hdrImpl_ok N) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

end Silmaril.Wasi.Versions.Net
