module

public import Silmaril.Wasi.Versions.Accept3.Defs
public import Silmaril.Wasi.Versions.SockMore.Thms

@[expose] public section

/-!
# WASI 0.3 listen/accept: theorems

PROVED (standard axioms):

* **`acc3Impl_sat`**: for every peers `P` and connections `C` admitted by them (`ConnOk P C`),
  `acc3Impl C` is a model of `acc3Th P`.
* **`acc3Th_examples`**: a socket read from the listening stream when nobody connects is
  rejected; with every peer connecting the same run is accepted, and the accepted socket's
  remote address is checked against the peers.
-/

namespace Silmaril.Wasi.Versions.Accept3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.P3 (natOf natV copyOf cStreamRead)
open Silmaril.Wasi.Versions.SockMore (Conn ConnOk)

theorem acc3Ok_ne (P : Peers) (q : Acc3St) {f : FnName} (h1 : f ≠ cStreamRead)
    (h2 : f ≠ tcpRemote3) (a : List Val) (r : Option (List Val)) :
    acc3Ok P q (.imp f a r) = true := by
  unfold acc3Ok
  split <;> simp_all

theorem completedOf_1 : completedOf completed1 = some 1 := by decide
theorem completedOf_blocked : completedOf (natV Silmaril.Wasm.Component.Async.blocked) = none := by
  decide

/-- `stream.read` on a stream: the host's answer passes the check. -/
theorem acc3Impl_read_ok {P : Peers} {C : Conn} (hC : ConnOk P C) (p : List WEv) (s : BitVec 32)
    (a : List Val) :
    acc3Ok P (p.foldl acc3Next {}) (.imp cStreamRead (.u32 s :: a)
      (acc3Impl C p cStreamRead (.u32 s :: a))) = true := by
  have hb : cStreamRead ≠ tcpBind3 := by decide
  have hl : cStreamRead ≠ tcpListen3 := by decide
  simp only [acc3Ok, acc3Impl, hb, hl, ↓reduceIte, selfH]
  cases hq : lookup s (p.foldl acc3Next {}).lst with
  | none => rfl
  | some addr =>
    dsimp only
    cases hc : C addr with
    | none => simp [readChk, completedOf_blocked]
    | some r => simp [readChk, completedOf_1, (hC addr r hc).1]

/-- `get-remote-address`: the host's answer passes the check. -/
theorem acc3Impl_remote_ok {P : Peers} {C : Conn} (hC : ConnOk P C) (p : List WEv) (s : BitVec 32)
    (a : List Val) :
    acc3Ok P (p.foldl acc3Next {}) (.imp tcpRemote3 (.u32 s :: a)
      (acc3Impl C p tcpRemote3 (.u32 s :: a))) = true := by
  have hb : tcpRemote3 ≠ tcpBind3 := by decide
  have hl : tcpRemote3 ≠ tcpListen3 := by decide
  have hr : tcpRemote3 ≠ cStreamRead := by decide
  simp only [acc3Ok, acc3Impl, hb, hl, hr, ↓reduceIte, selfH]
  cases hq : lookup s (p.foldl acc3Next {}).acc with
  | none => simp
  | some addr =>
    dsimp only
    cases hc : C addr with
    | none => simp [errAnsN, remoteOk, errV]
    | some r => simpa [remoteOk, okV] using (hC addr r hc).2

/-- Every answer of the host passes the check. -/
theorem acc3Impl_ok {P : Peers} {C : Conn} (hC : ConnOk P C) (p : List WEv) (f : FnName)
    (a : List Val) : acc3Ok P (p.foldl acc3Next {}) (.imp f a (acc3Impl C p f a)) = true := by
  have hs : ∀ g, (∀ s a', acc3Ok P (p.foldl acc3Next {}) (.imp g (.u32 s :: a')
      (acc3Impl C p g (.u32 s :: a'))) = true) →
      acc3Ok P (p.foldl acc3Next {}) (.imp g a (acc3Impl C p g a)) = true := by
    intro g hg
    rcases a with _ | ⟨v, a'⟩
    · rfl
    cases v
    case u32 s => exact hg s a'
    all_goals rfl
  by_cases h1 : f = cStreamRead
  · rw [h1]; exact hs _ (acc3Impl_read_ok hC p)
  by_cases h2 : f = tcpRemote3
  · rw [h2]; exact hs _ (acc3Impl_remote_ok hC p)
  exact acc3Ok_ne P _ h1 h2 a _

/-- **The concrete 0.3 listen/accept host is a model of `acc3Th P`.** -/
theorem acc3Impl_sat {Y : Sig.{0}} {I : Set FnName} {P : Peers} {C : Conn} (hC : ConnOk P C) :
    (hostSat (acc3Th P).Accepts).holds (concrete (Y := Y) (I := I) (acc3Impl C)) :=
  concrete_sat _ fun _ ht => gated_follows (acc3Impl_ok hC) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The theory is not trivial -/

def bindE : WEv := .imp tcpBind3 [.u32 0, .u32 7] (some [okV none])
def listenE : WEv := .imp tcpListen3 [.u32 0] (some [okV (some (.u32 1))])
def readE : WEv := .imp cStreamRead [.u32 1, natV 1] (some [completed1, .record [.u32 2]])
def remoteE : WEv := .imp tcpRemote3 [.u32 2] (some [okV (some (.u32 9))])

/-- Every address has a peer `9`. -/
def peers9 : Peers := ⟨fun _ => true, fun _ r => match r with | .u32 x => x == 9 | _ => false⟩

theorem acc3Th_examples :
    ¬ (acc3Th noPeers).Accepts [bindE, listenE, readE] ∧
    (acc3Th peers9).Accepts [bindE, listenE, readE, remoteE] ∧
    ¬ (acc3Th ⟨fun _ => true, fun _ _ => false⟩).Accepts [bindE, listenE, readE, remoteE] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.Accept3
