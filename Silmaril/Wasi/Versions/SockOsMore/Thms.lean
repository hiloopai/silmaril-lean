module

public import Silmaril.Wasi.Versions.SockOsMore.Defs
public import Silmaril.Wasi.Versions.SockOs.Thms

@[expose] public section

/-!
# The OS image of the pass-2/3 socket theories: theorems

PROVED (standard axioms):

* **`acc3Th_sockOk`**: the 0.3 accept image of every trace `acc3Th P` accepts is admitted by
  the network of the peers `P`.
* **`sendTh_sockOk`**, **`udpConnTh3_sockOk`**: the 0.2 and 0.3 UDP send images of accepted
  traces are admitted (by every network: `send` does not observe it).
-/

namespace Silmaril.Wasi.Versions.SockOsMore

open Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.SockOs
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

/-- The image of a checked 0.3 accept answer is admitted. -/
theorem evAcc3_ok (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : Accept3.Acc3St)
    (e : WEv) (h : Accept3.acc3Ok P q e = true) : SockOk (netOf N₀ U P R) (evAcc3 q e) := by
  have hne : Accept3.tcpRemote3 ≠ Silmaril.Wasi.Versions.P3.cStreamRead := by
    simp [Accept3.tcpRemote3, Silmaril.Wasi.Versions.P3.cStreamRead, Silmaril.Wasi.Versions.P3.canon]
  unfold evAcc3
  split
  · next f c rest a =>
    split
    · next hf =>
      split
      · next loc hl =>
        have ha : P.peer loc a = true := by
          simpa [Accept3.acc3Ok, hf, hne, hl, remoteOk] using h
        exact sockOk_single ha
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- Every send event is admitted. -/
theorem send_ok {N : NetEnv Val} (l : List (SockEv Val)) (h : ∀ e ∈ l, ∃ s d, e = .send s d) :
    SockOk N l := fun e he => by
  obtain ⟨s, d, rfl⟩ := h e he
  trivial

theorem evSend2_send (q : SockMore.SendSt) (e : WEv) :
    ∀ x ∈ evSend2 q e, ∃ s d, x = .send s d := by
  unfold evSend2
  split
  · split
    · intro x hx
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨_, d, rfl⟩
    · simp
  · simp

theorem evSend3_send (q : Udp3Conn.UCSt) (e : WEv) :
    ∀ x ∈ evSend3 q e, ∃ s d, x = .send s d := by
  unfold evSend3
  split
  · split
    · intro x hx
      exact ⟨_, _, List.mem_singleton.1 hx⟩
    · simp
  · simp

/-- **0.3 accept**: the image of an accepted trace is admitted by the peers `P`. -/
theorem acc3Th_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (Accept3.acc3Th P).Accepts t) :
    SockOk (netOf N₀ U P R) (imgRun Accept3.acc3Next evAcc3 {} t) :=
  imgRun_sockOk (evAcc3_ok N₀ U P R) h

/-- **0.2 UDP send**: the image of an accepted trace is admitted. -/
theorem sendTh_sockOk (N : NetEnv Val) {t : List WEv} (h : SockMore.sendTh.Accepts t) :
    SockOk N (imgRun SockMore.sendNext evSend2 [] t) :=
  imgRun_sockOk (fun q e _ => send_ok _ (evSend2_send q e)) h

/-- **0.3 UDP send**: the image of an accepted trace is admitted. -/
theorem udpConnTh3_sockOk (N : NetEnv Val) {t : List WEv} (h : Udp3Conn.udpConnTh3.Accepts t) :
    SockOk N (imgRun Udp3Conn.ucNext evSend3 {} t) :=
  imgRun_sockOk (fun q e _ => send_ok _ (evSend3_send q e)) h

end Silmaril.Wasi.Versions.SockOsMore
