module

public import Silmaril.Wasi.Versions.Http3.Defs
public import Silmaril.Wasi.Versions.NetMore.Thms

@[expose] public section

/-!
# WASI 0.3 outgoing HTTP: theorems

PROVED (standard axioms): `httpImpl3_sat` (the concrete host of `W` is a model of `httpTh3 W`);
`http3_disjoint` and **`no_http3_over_p1`** (relation (d) for 0.3 HTTP: no component importing
preview1 implements `httpTh3` over preview1 for every web and decides a request over some
preview1 model).
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The answer of `send` passes the check. -/
theorem sendOk_ans (n : Nat) (o : HttpOutcome) : sendOk o (sendAns n o) = true := by
  cases o <;> simp [sendOk, sendAns, okV, errV]

/-- The status answer passes the check. -/
theorem statusOk_ans (W : Web) (k : Val × Val) : statusOk W k (statusAns W k) = true := by
  unfold statusOk statusAns
  split <;> simp_all

/-- Every answer of the concrete 0.3 HTTP host passes the check. -/
theorem httpImpl3_ok (W : Web) (p : List WEv) (f : FnName) (a : List Val) :
    http3Ok W (p.foldl http3Next {}) (.imp f a (httpImpl3 W p f a)) = true := by
  have hs : p.foldl http3Next {} = http3State p := rfl
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 r =>
    rw [hs]
    by_cases h₁ : f = send3
    · subst h₁
      simp [http3Ok, httpImpl3, setAuth3, setPath3, send3, sendOk_ans]
    by_cases h₂ : f = getStatus3
    · subst h₂
      cases hl : lookup r (http3State p).resps <;>
        simp [http3Ok, httpImpl3, setAuth3, setPath3, send3, getStatus3, hl, statusOk_ans]
    · simp [http3Ok, h₁, h₂]
  all_goals rfl

/-- **The concrete 0.3 HTTP host of `W` is a model of `httpTh3 W`.** -/
theorem httpImpl3_sat {Y : Sig.{0}} {I : Set FnName} (W : Web) :
    (hostSat (httpTh3 W).Accepts).holds (concrete (Y := Y) (I := I) (httpImpl3 W)) :=
  concrete_sat _ fun _ ht => gated_follows (httpImpl3_ok W) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-- `webUp` and `webDown` admit no common decisive 0.3 answer. -/
theorem http3_disjoint (q : Http3St) (e : WEv) (hd : httpDecisive3 q e)
    (h₁ : http3Ok webUp q e = true) : http3Ok webDown q e = false := by
  obtain ⟨r, a, res, rfl⟩ := hd
  have h₁' : sendOk (.status 200) (some res) = true := by simpa [http3Ok, webUp] using h₁
  simp only [http3Ok, ↓reduceIte, webDown_eq_hand, Option.isNone_some, Bool.false_or]
  unfold sendOk at h₁' ⊢
  split at h₁' <;> simp_all

/-- **0.3 outgoing HTTP is not implementable over preview1.** -/
theorem no_http3_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (ObsOverP1 {} http3Next http3Ok σ ∧ ObsResponsive {} http3Next httpDecisive3 σ) :=
  no_obs_over_p1 webUp webDown http3_disjoint σ

end Silmaril.Wasi.Versions.Net
