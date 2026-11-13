module

public import Silmaril.Wasi.Versions.Udp3Conn.Defs
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# WASI 0.3 UDP `connect`/`send`: theorems

PROVED (standard axioms):

* **`udpConnImpl3_sat`**: the host `udpConnImpl3` is a model of `udpConnTh3`.
* **`udpConnTh3_examples`**: the theory is not trivial. Accepted: create an IPv4 socket,
  connect, send without an address and to the connected address, read the remote address,
  disconnect, send to an address. Rejected: a `send` without an address on an unconnected
  socket, a `send` to an address other than the connected one, a `connect` to port `0`, a
  `connect` to `0.0.0.0`, a `connect` to an IPv6 address from an IPv4 socket, a `disconnect`
  of an unconnected socket, a wrong `get-remote-address`, a wrong `get-address-family`, and a
  `get-local-address` of an unbound socket.
-/

namespace Silmaril.Wasi.Versions.Udp3Conn

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net

theorem okIf_ok (c : Bool) (e : Nat) : (!isOk (okIf c e) || c) = true := by
  cases c <;> simp [okIf, isOk, okV, errV]

theorem okAddrIs_self (v : Val) : okAddrIs v (some [okV (some v)]) = true := by
  simp [okAddrIs, okV]

/-- The check, on an answer whose arguments do not start with a handle. -/
theorem ucOk_other (q : UCSt) (f : FnName) (a : List Val) (r : Option (List Val))
    (h : ∀ s rest, a ≠ .u32 s :: rest) : ucOk q (.imp f a r) = true := by
  rcases a with _ | ⟨v, rest⟩
  · simp [ucOk]
  · cases v
    case u32 s => exact absurd rfl (h s rest)
    all_goals simp [ucOk]

/-- The functions `ucOk` checks. -/
def Checked (f : FnName) : Prop :=
  f = udpConnect3 ∨ f = udpDisconnect3 ∨ f = udpSend3 ∨ f = udpRemote3 ∨ f = udpLocal3 ∨
    f = udpReceive3 ∨ f = udpFamily3

/-- The check accepts every answer of a function it does not check. -/
theorem ucOk_quiet (q : UCSt) (f : FnName) (a : List Val) (r : Option (List Val))
    (hf : ¬ Checked f) : ucOk q (.imp f a r) = true := by
  have h : f ≠ udpConnect3 ∧ f ≠ udpDisconnect3 ∧ f ≠ udpSend3 ∧ f ≠ udpRemote3 ∧
      f ≠ udpLocal3 ∧ f ≠ udpReceive3 ∧ f ≠ udpFamily3 := by
    simpa only [Checked, not_or] using hf
  rcases a with _ | ⟨v, rest⟩
  · simp [ucOk]
  · cases v <;> simp [ucOk, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2]

/-- Every answer of the host on a socket passes the check. -/
theorem ucOk_sock (q : UCSt) (f : FnName) (s : BitVec 32) (rest : List Val) :
    ucOk q (.imp f (.u32 s :: rest) (sockA q f s rest)) = true := by
  unfold sockA
  unfold ucOk
  by_cases h1 : f = udpConnect3
  · simp only [h1, ↓reduceIte]
    cases rest with
    | nil => rfl
    | cons addr _ => exact okIf_ok _ _
  simp only [h1, ↓reduceIte]
  by_cases h2 : f = udpDisconnect3
  · simp only [h2, ↓reduceIte]; exact okIf_ok _ _
  simp only [h2, ↓reduceIte]
  by_cases h3 : f = udpSend3
  · simp only [h3, ↓reduceIte]; exact okIf_ok _ _
  simp only [h3, ↓reduceIte]
  by_cases h4 : f = udpRemote3
  · simp only [h4, ↓reduceIte]
    cases connOf q s with
    | none => simp [isOk, errV]
    | some v => exact okAddrIs_self v
  simp only [h4, ↓reduceIte]
  by_cases h5 : f = udpLocal3
  · simp only [h5, ↓reduceIte]
    rcases lookup s q.bound with _ | _ | v
    · simp [isOk, errV]
    · rfl
    · exact okAddrIs_self v
  simp only [h5, ↓reduceIte]
  by_cases h6 : f = udpReceive3
  · simp only [h6, ↓reduceIte]
    cases connOf q s <;> simp [errV]
  simp only [h6, ↓reduceIte]
  by_cases h7 : f = udpFamily3
  · simp only [h7, ↓reduceIte]
    cases lookup s q.fam <;> simp [famOf]
  simp only [h7, ↓reduceIte]

theorem not_checked_create : ¬ Checked udpCreate3 := by
  simp [Checked, udpCreate3, udpConnect3, udpDisconnect3, udpSend3, udpRemote3, udpLocal3,
    udpReceive3, udpFamily3]

theorem not_checked_bind : ¬ Checked udpBind3 := by
  simp [Checked, udpBind3, udpConnect3, udpDisconnect3, udpSend3, udpRemote3, udpLocal3,
    udpReceive3, udpFamily3]

/-- **Every answer of the host passes the check.** -/
theorem udpConnImpl3_ok (p : List WEv) (f : FnName) (a : List Val) :
    ucOk (p.foldl ucNext {}) (.imp f a (udpConnImpl3 p f a)) = true := by
  have hs : p.foldl ucNext {} = ucState p := rfl
  rw [hs]
  by_cases hc : f = udpCreate3
  · exact ucOk_quiet _ f a _ (hc ▸ not_checked_create)
  by_cases hb : f = udpBind3
  · exact ucOk_quiet _ f a _ (hb ▸ not_checked_bind)
  by_cases ha : ∃ s rest, a = .u32 s :: rest
  · obtain ⟨s, rest, hsr⟩ := ha
    have hr : udpConnImpl3 p f (.u32 s :: rest) = sockA (ucState p) f s rest := by
      simp [udpConnImpl3, hc, hb]
    rw [hsr, hr]
    exact ucOk_sock _ f s rest
  · exact ucOk_other _ f a _ fun s rest h => ha ⟨s, rest, h⟩

/-- **The 0.3 UDP connect/send host is a model of the theory.** -/
theorem udpConnImpl3_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat udpConnTh3.Accepts).holds (concrete (Y := Y) (I := I) udpConnImpl3) :=
  concrete_sat _ fun _ ht => gated_follows udpConnImpl3_ok (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The theory is not trivial -/

/-- The IPv4 address `a.b.c.d:port`. -/
def v4 (port a b c d : Nat) : Val :=
  .variant 0 (some (.record [.u16 (BitVec.ofNat 16 port),
    .record [.u8 (BitVec.ofNat 8 a), .u8 (BitVec.ofNat 8 b), .u8 (BitVec.ofNat 8 c),
      .u8 (BitVec.ofNat 8 d)]]))

/-- An IPv6 address `::1` with port `port`. -/
def v6 (port : Nat) : Val :=
  .variant 1 (some (.record [.u16 (BitVec.ofNat 16 port), .u32 0,
    .record [.u16 0, .u16 0, .u16 0, .u16 0, .u16 0, .u16 0, .u16 0, .u16 1], .u32 0]))

def okE : Option (List Val) := some [okV none]
def createE : WEv := .imp udpCreate3 [.variant 0 none] (some [okV (some (.u32 0))])
def connectE (a : Val) : WEv := .imp udpConnect3 [.u32 0, a] okE
def sendE (a : Option Val) : WEv :=
  .imp udpSend3 [.u32 0, .record [], match a with
    | none => .variant 0 none
    | some a => .variant 1 (some a)] okE
def remoteE (a : Val) : WEv := .imp udpRemote3 [.u32 0] (some [okV (some a)])
def localE (a : Val) : WEv := .imp udpLocal3 [.u32 0] (some [okV (some a)])
def familyE (k : Nat) : WEv := .imp udpFamily3 [.u32 0] (some [.variant k none])
def disconnectE : WEv := .imp udpDisconnect3 [.u32 0] okE

/-- **Accepted and rejected runs of `udpConnTh3`.** -/
theorem udpConnTh3_examples :
    udpConnTh3.Accepts [createE, familyE 0, connectE (v4 53 10 0 0 1), sendE none,
      sendE (some (v4 53 10 0 0 1)), remoteE (v4 53 10 0 0 1), disconnectE,
      sendE (some (v4 80 10 0 0 2))] ∧
    ¬ udpConnTh3.Accepts [createE, sendE none] ∧
    ¬ udpConnTh3.Accepts [createE, connectE (v4 53 10 0 0 1), sendE (some (v4 53 10 0 0 2))] ∧
    ¬ udpConnTh3.Accepts [createE, connectE (v4 0 10 0 0 1)] ∧
    ¬ udpConnTh3.Accepts [createE, connectE (v4 53 0 0 0 0)] ∧
    ¬ udpConnTh3.Accepts [createE, connectE (v6 53)] ∧
    ¬ udpConnTh3.Accepts [createE, disconnectE] ∧
    ¬ udpConnTh3.Accepts [createE, connectE (v4 53 10 0 0 1), remoteE (v4 53 10 0 0 2)] ∧
    ¬ udpConnTh3.Accepts [createE, familyE 1] ∧
    ¬ udpConnTh3.Accepts [createE, localE (v4 53 10 0 0 1)] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.Udp3Conn
