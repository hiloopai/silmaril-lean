module

public import Silmaril.Wasi.Versions.HttpReqBody.Defs
public import Silmaril.Wasi.Versions.Http3.Thms
public import Silmaril.Wasi.Versions.Net3.Over.Thms

@[expose] public section

/-!
# WASI `wasi:http` outgoing request bodies: theorems

PROVED (standard axioms):

* **`req2Impl_sat`**: for every request-body web `Q`, the concrete 0.2 host `req2Impl Q` is a
  model of `req2Th Q`.
* **`req3Impl_sat`**: the concrete 0.3 host `req3Impl Q` is a model of `req3Th Q`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- A `send` answer of an outcome passes the `send` check. -/
theorem sendOk_sendAns (n : Nat) (o : HttpOutcome) : sendOk o (sendAns n o) = true := by
  cases o <;> simp [sendOk, sendAns, okV, errV]

/-- `get` of the concrete 0.2 host passes the check. -/
theorem req2Impl_get (Q : QWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    req2Ok Q (req2State p) (.imp futGet (.u32 h :: a') (req2Impl Q p futGet (.u32 h :: a'))) = true := by
  have hne : ¬(futGet = setAuthority ∨ futGet = setPath ∨ isWriteFn futGet = true ∨
      futGet = outBodyFinish2) := by decide
  have hne' : ¬(futGet = outReqBody2 ∨ futGet = outBodyWrite2 ∨ futGet = httpHandle) := by decide
  cases hl : lookup h (req2State p).futs with
  | none => simp [req2Ok, req2Impl, hne, hne', hl, selfH, gotV]
  | some kb =>
    obtain ⟨k, ob⟩ := kb
    cases hd : (req2State p).done ob <;>
      simp [req2Ok, req2Impl, hne, hne', hl, hd, selfH, outcomeOk_V, okV]

/-- `status` of the concrete 0.2 host passes the check. -/
theorem req2Impl_status (Q : QWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    req2Ok Q (req2State p) (.imp respStatus (.u32 h :: a') (req2Impl Q p respStatus (.u32 h :: a'))) =
      true := by
  have hne : ¬(respStatus = setAuthority ∨ respStatus = setPath ∨ isWriteFn respStatus = true ∨
      respStatus = outBodyFinish2) := by decide
  have hne' : ¬(respStatus = outReqBody2 ∨ respStatus = outBodyWrite2 ∨ respStatus = httpHandle) := by
    decide
  have hg : respStatus ≠ futGet := by decide
  cases hl : lookup h (req2State p).resps with
  | none => simp [req2Ok, hg, hl]
  | some kb =>
    obtain ⟨k, ob⟩ := kb
    cases ob with
    | none => simp [req2Ok, hg, hl]
    | some bs => simpa [req2Ok, req2Impl, hne, hne', hg, hl, selfH] using statusOk_ans (Q.at bs) k

/-- Every answer of the concrete 0.2 host passes the check. -/
theorem req2Impl_ok (Q : QWeb) (p : List WEv) (f : FnName) (a : List Val) :
    req2Ok Q (p.foldl req2Next {}) (.imp f a (req2Impl Q p f a)) = true := by
  have hs : p.foldl req2Next {} = req2State p := rfl
  rw [hs]
  rcases a with _ | ⟨v, a'⟩
  · simp [req2Ok]
  cases v
  case u32 h =>
    by_cases h₁ : f = futGet
    · rw [h₁]; exact req2Impl_get Q p h a'
    by_cases h₂ : f = respStatus
    · rw [h₂]; exact req2Impl_status Q p h a'
    simp [req2Ok, h₁, h₂]
  all_goals simp [req2Ok]

/-- **The concrete 0.2 host with outgoing bodies is a model of `req2Th Q`.** -/
theorem req2Impl_sat {Y : Sig.{0}} {I : Set FnName} (Q : QWeb) :
    (hostSat (req2Th Q).Accepts).holds (concrete (Y := Y) (I := I) (req2Impl Q)) :=
  concrete_sat _ fun _ ht => gated_follows (req2Impl_ok Q) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-- `send` of the concrete 0.3 host passes the check. -/
theorem req3Impl_send (Q : QWeb) (p : List WEv) (r : BitVec 32) (a' : List Val) :
    req3Ok Q (req3State p) (.imp send3 (.u32 r :: a') (req3Impl Q p send3 (.u32 r :: a'))) = true := by
  have hne : send3 ≠ P3.cStreamNew ∧ send3 ≠ P3.cStreamWrite ∧ send3 ≠ P3.cStreamDropW ∧
      send3 ≠ reqNew3 ∧ ¬(send3 = setAuth3 ∨ send3 = setPath3) := by decide
  cases ho : Q ((req3State p).key r).1 ((req3State p).key r).2 (((req3State p).done r).getD []) <;>
    cases hd : (req3State p).done r <;>
    simp_all [req3Ok, req3Impl, sendAns, sendOk, okV, errV]

/-- `get-status-code` of the concrete 0.3 host passes the check. -/
theorem req3Impl_status (Q : QWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    req3Ok Q (req3State p) (.imp getStatus3 (.u32 h :: a') (req3Impl Q p getStatus3 (.u32 h :: a'))) =
      true := by
  have hne : getStatus3 ≠ P3.cStreamNew ∧ getStatus3 ≠ P3.cStreamWrite ∧
      getStatus3 ≠ P3.cStreamDropW ∧ getStatus3 ≠ reqNew3 ∧
      ¬(getStatus3 = setAuth3 ∨ getStatus3 = setPath3) ∧ getStatus3 ≠ send3 := by decide
  cases hl : lookup h (req3State p).resps with
  | none => simp [req3Ok, hne, hl]
  | some kb =>
    obtain ⟨k, ob⟩ := kb
    cases ob with
    | none => simp [req3Ok, hne, hl]
    | some bs => simpa [req3Ok, req3Impl, hne, hl, selfH] using statusOk_ans (Q.at bs) k

/-- Every answer of the concrete 0.3 host passes the check. -/
theorem req3Impl_ok (Q : QWeb) (p : List WEv) (f : FnName) (a : List Val) :
    req3Ok Q (p.foldl req3Next {}) (.imp f a (req3Impl Q p f a)) = true := by
  have hs : p.foldl req3Next {} = req3State p := rfl
  rw [hs]
  rcases a with _ | ⟨v, a'⟩
  · simp [req3Ok]
  cases v
  case u32 h =>
    by_cases h₁ : f = send3
    · rw [h₁]; exact req3Impl_send Q p h a'
    by_cases h₂ : f = getStatus3
    · rw [h₂]; exact req3Impl_status Q p h a'
    simp [req3Ok, h₁, h₂]
  all_goals simp [req3Ok]

/-- **The concrete 0.3 host with outgoing bodies is a model of `req3Th Q`.** -/
theorem req3Impl_sat {Y : Sig.{0}} {I : Set FnName} (Q : QWeb) :
    (hostSat (req3Th Q).Accepts).holds (concrete (Y := Y) (I := I) (req3Impl Q)) :=
  concrete_sat _ fun _ ht => gated_follows (req3Impl_ok Q) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

end Silmaril.Wasi.Versions.Net
