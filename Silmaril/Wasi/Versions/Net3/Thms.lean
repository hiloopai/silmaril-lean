module

public import Silmaril.Wasi.Versions.Net3.Defs
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# WASI 0.3 TCP connect: theorems

PROVED (standard axioms):

* `codes2_eq_hand`, `codes3_eq_hand`, `e2to3_eq_hand`, `e3to2_eq_hand`, `ecV3_eq_hand`: the
  code tables, now read from the vendored WIT, equal the hand-written ones; `eWouldBlock_wit`,
  `eNotInProgress_wit`, `eConnRefused_wit`, `eOther3_wit`: the literal case numbers are the WIT
  case numbers of their names.
* `e2to3_names`, `e3to2_names`: the code translations agree with the case names of the vendored
  WIT (`codes2`, `codes3`); a code goes to `other`/`unknown` only when its name has no
  counterpart. `e3to2_ne_wouldBlock`: no 0.3 code becomes `would-block`.
* `tcpImpl3_sat`: the concrete host of `N3` is a model of `tcpTh3 N3`.
* `tcp3_not_both`, **`no_tcp3_over_p1`**: the 0.3 connect, like the 0.2 one, is not implementable
  over preview1 (relation (d)): no component importing preview1 is correct over every preview1
  host model for every network and decides a connect over some preview1 model.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Codes

`codes2`, `codes3`, `e2to3`, `e3to2` and `ecV3` are read from the vendored WIT
(`Silmaril.Wasi.Versions.WitImport.Derived`). The equalities with the hand-written tables are
decided by the kernel on the imported type environments. -/

/-- The WIT-derived 0.2 case list is the hand-written one. -/
theorem codes2_eq_hand : codes2 = codes2H := by decide +kernel
/-- The WIT-derived 0.3 case list is the hand-written one. -/
theorem codes3_eq_hand : codes3 = codes3H := by decide +kernel

/-- The case numbers written as literals are those of the WIT names. -/
theorem eOther3_wit : eOther3 = WitImport.caseIdx codes3 "other" := by decide +kernel
theorem eWouldBlock_wit : eWouldBlock = WitImport.caseIdx codes2 "would-block" := by decide +kernel
theorem eNotInProgress_wit : eNotInProgress = WitImport.caseIdx codes2 "not-in-progress" := by
  decide +kernel
theorem eConnRefused_wit : eConnRefused = WitImport.caseIdx codes2 "connection-refused" := by
  decide +kernel

theorem e2to3_lt_hand : ∀ k, k < 21 → e2to3 k = e2to3H k := by decide +kernel
theorem e3to2_lt_hand : ∀ k, k < 15 → e3to2 k = e3to2H k := by decide +kernel

/-- **The WIT-derived 0.2 → 0.3 translation is the hand-written table**, defaults included. -/
theorem e2to3_eq_hand : e2to3 = e2to3H := by
  funext k
  by_cases hk : k < 21
  · exact e2to3_lt_hand k hk
  · have h1 : WitImport.codes2W[k]? = none := by
      rw [show WitImport.codes2W = codes2H from codes2_eq_hand]
      exact List.getElem?_eq_none (by simp [codes2H]; omega)
    have h2 : e2to3H k = eOther3 := by
      unfold e2to3H
      split <;> omega
    have h3 : WitImport.eOther3W = eOther3 := by decide +kernel
    show WitImport.e2to3W k = e2to3H k
    rw [WitImport.e2to3W, h1, h2, h3]

/-- **The WIT-derived 0.3 → 0.2 translation is the hand-written table**, defaults included. -/
theorem e3to2_eq_hand : e3to2 = e3to2H := by
  funext k
  by_cases hk : k < 15
  · exact e3to2_lt_hand k hk
  · have h1 : WitImport.codes3W[k]? = none := by
      rw [show WitImport.codes3W = codes3H from codes3_eq_hand]
      exact List.getElem?_eq_none (by simp [codes3H]; omega)
    have h2 : e3to2H k = 0 := by
      unfold e3to2H
      split <;> omega
    have h3 : WitImport.caseIdx WitImport.codes2W "unknown" = 0 := by decide +kernel
    show WitImport.e3to2W k = e3to2H k
    rw [WitImport.e3to2W, h1, h2, h3]

/-- The payloads of the 0.3 `error-code` cases: only the last, `other`, has one. -/
theorem payloads3W_eq :
    WitImport.payloads3W = List.replicate 14 none ++ [some (.option (.prim .string))] := by
  decide +kernel

/-- **The WIT-derived 0.3 code value is the hand-written one.** -/
theorem ecV3_eq_hand : ecV3 = ecV3H := by
  funext k
  show WitImport.ecV3W k = ecV3H k
  unfold WitImport.ecV3W
  rw [payloads3W_eq]
  rcases Nat.lt_or_ge k 14 with h | h
  · have hk : k ≠ eOther3 := by simp only [eOther3]; omega
    rw [List.getElem?_append_left (by simpa using h), List.getElem?_replicate]
    simp only [h, ↓reduceIte]
    simp [ecV3H, hk]
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; rfl
    · have hk : k ≠ eOther3 := by simp only [eOther3]; omega
      rw [List.getElem?_eq_none (by simp; omega)]
      simp [ecV3H, hk]

/-- **The 0.2 → 0.3 table follows the names.** -/
theorem e2to3_names : ∀ k < codes2.length, codes3[e2to3 k]? = codes2[k]? ∨
    (e2to3 k = eOther3 ∧ codes2[k]?.all (· ∉ codes3)) := by
  decide +kernel

/-- **The 0.3 → 0.2 table follows the names.** -/
theorem e3to2_names : ∀ k < codes3.length, codes2[e3to2 k]? = codes3[k]? ∨
    (e3to2 k = 0 ∧ codes3[k]?.all (· ∉ codes2)) := by
  decide +kernel

/-- No 0.3 code becomes `would-block`. -/
theorem e3to2_ne_wouldBlock (k : Nat) : e3to2 k ≠ eWouldBlock := by
  rw [e3to2_eq_hand]
  unfold e3to2H
  split <;> decide

/-- `connection-refused` in both directions. -/
theorem e_refused : e2to3 eConnRefused = 9 ∧ e3to2 9 = eConnRefused := by decide +kernel

/-! ## The concrete host -/

/-- The answer of an outcome passes the check. -/
theorem connectOk3_ans (o : Option Nat) : connectOk3 o (outcomeAns3 o) = true := by
  cases o with
  | none => rfl
  | some k =>
    by_cases hk : k = eOther3 <;> simp [connectOk3, outcomeAns3, errV, ecV3_eq_hand, ecV3H, hk]

/-- Every answer of the concrete 0.3 host passes the check. -/
theorem tcpImpl3_ok (N3 : Network) (p : List WEv) (f : FnName) (a : List Val) :
    tcpOk3 N3 (p.foldl (fun _ _ => ()) ()) (.imp f a (tcpImpl3 N3 p f a)) = true := by
  rcases a with _ | ⟨s, _ | ⟨addr, rest⟩⟩
  · rfl
  · rfl
  by_cases hf : f = connect3
  · subst hf
    simp [tcpOk3, tcpImpl3, create3, connect3, connectOk3_ans]
  · simp [tcpOk3, hf]

/-- **The concrete 0.3 TCP host of `N3` is a model of `tcpTh3 N3`.** -/
theorem tcpImpl3_sat {Y : Sig.{0}} {I : Set FnName} (N3 : Network) :
    (hostSat (tcpTh3 N3).Accepts).holds (concrete (Y := Y) (I := I) (tcpImpl3 N3)) :=
  concrete_sat _ fun _ ht => gated_follows (tcpImpl3_ok N3) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## (d) for 0.3 -/

/-- A network refusing every connection with 0.3 `connection-refused`. -/
def net3Down : Network := fun _ => some 9

/-- `netUp` and `net3Down` admit no common decisive answer. -/
theorem tcp3_disjoint (q : Unit) (e : WEv) (hd : tcpDecisive3 q e)
    (h₁ : tcpOk3 netUp q e = true) : tcpOk3 net3Down q e = false := by
  obtain ⟨s, addr, rest, r, rfl⟩ := hd
  have h₁' : connectOk3 none (some r) = true := by simpa [tcpOk3, netUp] using h₁
  have hr : r = [.variant 0 none] := by
    unfold connectOk3 at h₁'
    split at h₁' <;> simp_all
  subst hr
  simp [tcpOk3, net3Down, connectOk3]

/-- **Two networks, one host**, for 0.3. -/
theorem tcp3_not_both {Y : Sig.{0}} {I X : Set FnName} {η : Host Y I}
    {σ : Strategy (nsig I) (nsig X)} (hresp : ∃ p ∈ link η σ, TcpDecides3 (htrace p))
    (hUp : (hostSat (tcpTh3 netUp).Accepts).holds (link η σ)) :
    ¬ (hostSat (tcpTh3 net3Down).Accepts).holds (link η σ) := fun hDown => by
  obtain ⟨p, hp, hd⟩ := hresp
  exact not_decides (ok₁ := tcpOk3 netUp) (ok₂ := tcpOk3 net3Down) tcp3_disjoint (hUp p hp)
    (hDown p hp) hd

/-- **The 0.3 TCP connect is not implementable over preview1.** -/
theorem no_tcp3_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (Tcp3OverP1 σ ∧ Tcp3Responsive σ) := by
  rintro ⟨hσ, Y, η, hη, hresp⟩
  exact tcp3_not_both hresp (hσ netUp Y η hη) (hσ net3Down Y η hη)

end Silmaril.Wasi.Versions.Net
