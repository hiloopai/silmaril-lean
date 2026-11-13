module

public import Silmaril.Wasi.Versions.Tcp3Addr.Defs
public import Silmaril.Wasi.Versions.Udp3Conn.Thms

@[expose] public section

/-!
# WASI 0.3 TCP socket states: theorems

PROVED (standard axioms):

* **`tcpAddrImpl3_sat`**: the host `tcpAddrImpl3` is a model of `tcpAddrTh3`.
* **`tcpAddrTh3_examples`**: the theory is not trivial. Accepted: create an IPv4 socket, read
  its family, bind it to `10.0.0.1:80`, read that address back, listen, read
  `get-is-listening = true`. Rejected: a second successful `bind`; a `bind` to an IPv6
  address from an IPv4 socket; `get-local-address` answered `ok` on an unbound socket; a wrong
  bound address read back; `get-is-listening = true` before `listen`; a wrong family; a
  `connect` answered `ok` on a listening socket; a second successful `listen`.
-/

namespace Silmaril.Wasi.Versions.Tcp3Addr

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.Udp3Conn (isOk okIf okIf_ok famOf)
open Silmaril.Wasi.Versions.Accept3 (tcpBind3 tcpListen3)

/-- The check, on an answer whose arguments do not start with a handle. -/
theorem taOk_other (q : TASt) (f : FnName) (a : List Val) (r : Option (List Val))
    (h : ∀ s rest, a ≠ .u32 s :: rest) : taOk q (.imp f a r) = true := by
  rcases a with _ | ⟨v, rest⟩
  · simp [taOk]
  · cases v
    case u32 s => exact absurd rfl (h s rest)
    all_goals simp [taOk]

/-- The functions `taOk` checks. -/
def Checked (f : FnName) : Prop :=
  f = tcpBind3 ∨ f = tcpListen3 ∨ f = connect3 ∨ f = tcpIsListening3 ∨ f = tcpFamily3 ∨
    f = tcpLocal3

theorem not_checked_create : ¬ Checked create3 := by
  simp [Checked, create3, tcpBind3, tcpListen3, connect3, tcpIsListening3, tcpFamily3, tcpLocal3]

/-- The check accepts every answer of a function it does not check. -/
theorem taOk_quiet (q : TASt) (f : FnName) (a : List Val) (r : Option (List Val))
    (hf : ¬ Checked f) : taOk q (.imp f a r) = true := by
  have h : f ≠ tcpBind3 ∧ f ≠ tcpListen3 ∧ f ≠ connect3 ∧ f ≠ tcpIsListening3 ∧
      f ≠ tcpFamily3 ∧ f ≠ tcpLocal3 := by
    simpa only [Checked, not_or] using hf
  rcases a with _ | ⟨v, rest⟩
  · simp [taOk]
  · cases v
    case u32 s =>
      simp only [taOk]
      cases lookup s q <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
    all_goals simp [taOk]

theorem listeningOk_self (p : TPhase) : listeningOk p (some [.bool (p == .listening)]) = true := by
  simp [listeningOk]

theorem localOk_localAns (t : TSock) : localOk t (localAns t) = true := by
  rcases t with ⟨k, p, a⟩
  cases p <;> cases a <;> simp [localAns, localOk, isOk, errV, okV]

/-- The host's answer on a tracked socket passes the check. -/
theorem taOk_sock (q : TASt) (s : BitVec 32) (t : TSock) (ht : lookup s q = some t)
    (f : FnName) (rest : List Val) :
    taOk q (.imp f (.u32 s :: rest) (sockA t f rest)) = true := by
  simp only [taOk, ht]
  unfold sockA
  by_cases h1 : f = tcpBind3
  · simp only [h1, ↓reduceIte]
    cases rest with
    | nil => rfl
    | cons addr _ => exact okIf_ok _ _
  simp only [h1, ↓reduceIte]
  by_cases h2 : f = tcpListen3
  · simp only [h2, ↓reduceIte]
    cases t.phase.canStart <;> simp [isOk, okV, errV]
  simp only [h2, ↓reduceIte]
  by_cases h3 : f = connect3
  · simp only [h3, ↓reduceIte]; exact okIf_ok _ _
  simp only [h3, ↓reduceIte]
  by_cases h4 : f = tcpIsListening3
  · simp only [h4, ↓reduceIte]; exact listeningOk_self _
  simp only [h4, ↓reduceIte]
  by_cases h5 : f = tcpFamily3
  · simp only [h5, ↓reduceIte]; simp [famOf]
  simp only [h5, ↓reduceIte]
  by_cases h6 : f = tcpLocal3
  · simp only [h6, ↓reduceIte]; exact localOk_localAns t
  simp only [h6, ↓reduceIte]

/-- **Every answer of the host passes the check.** -/
theorem tcpAddrImpl3_ok (p : List WEv) (f : FnName) (a : List Val) :
    taOk (p.foldl taNext []) (.imp f a (tcpAddrImpl3 p f a)) = true := by
  have hs : p.foldl taNext [] = taState p := rfl
  rw [hs]
  by_cases hc : f = create3
  · exact taOk_quiet _ f a _ (hc ▸ not_checked_create)
  by_cases ha : ∃ s rest, a = .u32 s :: rest
  · obtain ⟨s, rest, hsr⟩ := ha
    rw [hsr]
    cases ht : lookup s (taState p) with
    | none => simp [taOk, ht]
    | some t =>
      have hr : tcpAddrImpl3 p f (.u32 s :: rest) = sockA t f rest := by
        simp [tcpAddrImpl3, hc, ht]
      rw [hr]
      exact taOk_sock _ s t ht f rest
  · exact taOk_other _ f a _ fun s rest h => ha ⟨s, rest, h⟩

/-- **The 0.3 TCP socket-state host is a model of the theory.** -/
theorem tcpAddrImpl3_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat tcpAddrTh3.Accepts).holds (concrete (Y := Y) (I := I) tcpAddrImpl3) :=
  concrete_sat _ fun _ ht => gated_follows tcpAddrImpl3_ok (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The theory is not trivial -/

open Silmaril.Wasi.Versions.Udp3Conn (v4 v6)

def okE : Option (List Val) := some [okV none]
def createE : WEv := .imp create3 [.variant 0 none] (some [okV (some (.u32 0))])
def bindE (a : Val) : WEv := .imp tcpBind3 [.u32 0, a] okE
def listenE : WEv := .imp tcpListen3 [.u32 0] (some [okV (some (.u32 1))])
def connectE (a : Val) : WEv := .imp connect3 [.u32 0, a] okE
def localE (a : Val) : WEv := .imp tcpLocal3 [.u32 0] (some [okV (some a)])
def familyE (k : Nat) : WEv := .imp tcpFamily3 [.u32 0] (some [.variant k none])
def listeningE (b : Bool) : WEv := .imp tcpIsListening3 [.u32 0] (some [.bool b])

/-- **Accepted and rejected runs of `tcpAddrTh3`.** -/
theorem tcpAddrTh3_examples :
    tcpAddrTh3.Accepts [createE, familyE 0, listeningE false, bindE (v4 80 10 0 0 1),
      localE (v4 80 10 0 0 1), listenE, listeningE true, localE (v4 80 10 0 0 1)] ∧
    ¬ tcpAddrTh3.Accepts [createE, bindE (v4 80 10 0 0 1), bindE (v4 81 10 0 0 1)] ∧
    ¬ tcpAddrTh3.Accepts [createE, bindE (v6 80)] ∧
    ¬ tcpAddrTh3.Accepts [createE, localE (v4 80 10 0 0 1)] ∧
    ¬ tcpAddrTh3.Accepts [createE, bindE (v4 80 10 0 0 1), localE (v4 80 10 0 0 2)] ∧
    ¬ tcpAddrTh3.Accepts [createE, listeningE true] ∧
    ¬ tcpAddrTh3.Accepts [createE, familyE 1] ∧
    ¬ tcpAddrTh3.Accepts [createE, listenE, connectE (v4 80 10 0 0 1)] ∧
    ¬ tcpAddrTh3.Accepts [createE, listenE, listenE] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.Tcp3Addr
