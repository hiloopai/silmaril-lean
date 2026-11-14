module

public import Silmaril.Wasi.Versions.SockOs.Defs
public import Silmaril.Machine.Process.IoSpecNet.Thms
public import Silmaril.Wasi.Versions.Udp.Over.Thms
public import Silmaril.Wasi.Versions.Net3.Over.Thms
public import Silmaril.Wasi.Versions.Net3.Thms
public import Silmaril.Wasi.Versions.P3.Thms

@[expose] public section

/-!
# The OS image of WASI sockets: theorems

PROVED (standard axioms):

* **Theories are observations of the network** (`*_sockOk`): for every trace accepted by a
  socket theory, every socket event of its image is admitted by the network of the environment:
  `tcpTh_sockOk` (0.2 TCP connect, network `N`), `tcpTh3_sockOk` (0.3 TCP connect, `N3`),
  `udpTh_sockOk`, `udpTh3_sockOk` (inbox `U`), `dnsTh_sockOk`, `dnsTh3_sockOk` (resolver `R`),
  `acceptTh_sockOk` (peers `P`). Generic form: `imgRun_sockOk` for gated theories.
* **Hosts**: `tcpImpl3_sockOk`, `udpImpl3_sockOk`, `udpImpl_sockOk`: every run of the concrete
  hosts has an admitted image.
* **Adapters**: `tcp3Over2_sockOk` (the 0.3 connect events of `tcp3Over2` over any host of
  `tcpTh N` are admitted by the translated network `net3of2 N`), `udp3Over2_sockOk`,
  `udp2Over3_sockOk`, `tcp2Over3_sockOk`.
* **The extended image transports the LPS image**: `lpsPart_xRun`, `sockPart_xRun`;
  `lpsPart_xImg2 : lpsPart (xImg2 ch t) = Os.osTrace ch t`, `lpsPart_xImg3 : lpsPart (xImg3 ch
  t) = P3.osTrace3 ch t`, so every statement about the stdout image (`helloRun_os`,
  `hello3Run_os`, `p3OverP2_os`, …) holds of the LPS part of the extended image; `liftA_xImg3`.
  **`xImg3_netOk`**: a 0.3 run accepted by `tcpTh3 N3` and `udpTh3 U` has an extended image
  `NetOk (netOf N3 U P R)` admits, whose LPS part is its stdout image. `xImg2_netOk`: the same
  for 0.2 (`tcpTh N`, `udpTh U`). `hello3_xImg`: for `hello3`, the extended image is the
  embedded `hiOut ch` (no socket event).

Not proved: any refinement of socket events to x86 syscalls (`IoSpecNet.sockArm` is assumed).
-/

namespace Silmaril.Wasi.Versions.SockOs

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

variable {N : NetEnv Val}

/-! ## `SockOk` -/

theorem sockOk_nil : SockOk N [] := fun _ h => absurd h List.not_mem_nil

theorem sockOk_append {l₁ l₂ : List (SockEv Val)} (h₁ : SockOk N l₁) (h₂ : SockOk N l₂) :
    SockOk N (l₁ ++ l₂) := fun e he => (List.mem_append.1 he).elim (h₁ e) (h₂ e)

theorem sockOk_single {e : SockEv Val} (h : e.Admits N) : SockOk N [e] := fun e' he' => by
  rw [List.mem_singleton.1 he']
  exact h

theorem sockOk_map {α : Type} {l : List α} {f : α → SockEv Val} (h : ∀ x ∈ l, (f x).Admits N) :
    SockOk N (l.map f) := fun e he => by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact h x hx

/-! ## Images of runs -/

/-- **An image is admitted when each event's image is**, in the state reached before it. -/
theorem imgRun_sockOk' {S : Type} {next : S → WEv → S} {ev : S → WEv → List (SockEv Val)} :
    ∀ (q : S) (t : List WEv), (∀ u e v, t = u ++ e :: v → SockOk N (ev (u.foldl next q) e)) →
      SockOk N (imgRun next ev q t)
  | _, [], _ => sockOk_nil
  | q, e :: t, h =>
    sockOk_append (h [] e t rfl)
      (imgRun_sockOk' (next q e) t fun u e' v hu => h (e :: u) e' v (by rw [hu]; rfl))

/-- **Gated theories**: an accepted trace has an admitted image when every checked event has. -/
theorem imgRun_sockOk {S : Type} {init : S} {next : S → WEv → S} {ok : S → WEv → Bool}
    {ev : S → WEv → List (SockEv Val)} (hev : ∀ q e, ok q e = true → SockOk N (ev q e))
    {t : List WEv} (h : (gated init next ok).Accepts t) : SockOk N (imgRun next ev init t) :=
  imgRun_sockOk' init t fun u e v hu => hev _ e (gated_ok h u e v hu)

/-! ## Per-event images -/

/-- **An answer with an outcome determines it**: a `finish-connect` answer with an outcome is
not `would-block`, and the network's outcome it passes is that one. -/
theorem outcome2Of_conn {o o' : Option Nat} {r : Option (List Val)} (h : outcome2Of r = some o)
    (hok : isWouldBlock r = true ∨ connectOk o' r = true) : o' = o := by
  unfold outcome2Of at h
  split at h <;> rcases hok with hw | hc <;> cases o' <;> simp_all [isWouldBlock, connectOk]

/-- The image of a checked 0.2 TCP answer is admitted. -/
theorem evTcp2_ok (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : TcpSt) (e : WEv)
    (h : tcpOk N₀ q e = true) : SockOk (netOf N₀ U P R) (evTcp2 q e) := by
  unfold evTcp2
  split
  · next f s rest r =>
    split
    · next hf =>
      split
      · next addr o hl ho =>
        have hok : isWouldBlock r = true ∨ connectOk (N₀ addr) r = true := by
          simpa [tcpOk, hf, hl] using h
        exact sockOk_single (outcome2Of_conn ho hok)
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- **An answer with an outcome determines it** (0.3). -/
theorem outcome3Of_conn {o o' : Option Nat} {r : Option (List Val)} (h : outcome3Of r = some o)
    (hok : (r.isNone || connectOk3 o' r) = true) : o' = o := by
  unfold outcome3Of at h
  split at h <;> cases o' <;> simp_all [connectOk3]

/-- The image of a checked 0.3 TCP answer is admitted. -/
theorem evTcp3_ok (N₃ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : Unit) (e : WEv)
    (h : tcpOk3 N₃ q e = true) : SockOk (netOf N₃ U P R) (evTcp3 q e) := by
  unfold evTcp3
  split
  · next f sv addr rest r =>
    split
    · next hf =>
      split
      · next o ho =>
        have hok : (r.isNone || connectOk3 (N₃ addr) r) = true := by simpa [tcpOk3, hf] using h
        exact sockOk_single (outcome3Of_conn ho hok)
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- The image of a checked 0.2 UDP answer is admitted. -/
theorem evUdp2_ok (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : UdpSt) (e : WEv)
    (h : udpOk U q e = true) : SockOk (netOf N₀ U P R) (evUdp2 q e) := by
  unfold evUdp2
  split
  · split
    · exact sockOk_single trivial
    · exact sockOk_nil
  · next =>
    split
    · next hf =>
      split
      · next addr hl =>
        exact sockOk_map (by simpa [udpOk, hf, hl, recvOk, SockEv.Admits, netOf] using h)
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- The image of a checked 0.3 UDP answer is admitted. -/
theorem evUdp3_ok (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : Udp3St) (e : WEv)
    (h : udpOk3 U q e = true) : SockOk (netOf N₀ U P R) (evUdp3 q e) := by
  unfold evUdp3
  split
  · split
    · exact sockOk_single trivial
    · exact sockOk_nil
  · next =>
    split
    · next hf =>
      split
      · next addr hl =>
        exact sockOk_single (by simpa [udpOk3, hf, hl, recvOk3, SockEv.Admits, netOf] using h)
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- The image of a checked 0.2 name lookup answer is admitted. -/
theorem evDns2_ok (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : DnsSt) (e : WEv)
    (h : dnsOk R q e = true) : SockOk (netOf N₀ U P R) (evDns2 q e) := by
  unfold evDns2
  split
  · next f st rest a =>
    split
    · next hf =>
      split
      · next name hl =>
        have ha : R name a = true := by simpa [dnsOk, hf, hl, nextOk] using h
        exact sockOk_single ha
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- The image of a checked 0.3 name lookup answer is admitted. -/
theorem evDns3_ok (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : Unit) (e : WEv)
    (h : dnsOk3 R q e = true) : SockOk (netOf N₀ U P R) (evDns3 q e) := by
  unfold evDns3
  split
  · next f name rest l =>
    split
    · next hf =>
      have hall : ∀ x ∈ l, R name x = true := by simpa [dnsOk3, hf, listOk] using h
      exact sockOk_map hall
    · exact sockOk_nil
  · exact sockOk_nil

/-- The image of a checked accept answer is admitted. -/
theorem evAcc_ok (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) (q : AccSt) (e : WEv)
    (h : accOk P q e = true) : SockOk (netOf N₀ U P R) (evAcc q e) := by
  have hne : tcpRemote ≠ tcpAccept := by decide
  unfold evAcc
  split
  · next f c rest a =>
    split
    · next hf =>
      split
      · next loc hl =>
        have ha : P.peer loc a = true := by simpa [accOk, hf, hne, hl, remoteOk] using h
        exact sockOk_single ha
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-! ## Theories are observations of the network -/

/-- **0.2 TCP connect**: the image of an accepted trace is admitted by the network `N₀`. -/
theorem tcpTh_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (tcpTh N₀).Accepts t) : SockOk (netOf N₀ U P R) (imgRun tcpNext evTcp2 [] t) :=
  imgRun_sockOk (evTcp2_ok N₀ U P R) h

/-- **0.3 TCP connect**: the image of an accepted trace is admitted by the network `N₃`. -/
theorem tcpTh3_sockOk (N₃ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (tcpTh3 N₃).Accepts t) :
    SockOk (netOf N₃ U P R) (imgRun (fun _ _ => ()) evTcp3 () t) :=
  imgRun_sockOk (evTcp3_ok N₃ U P R) h

/-- **0.2 UDP**: the image of an accepted trace is admitted by the inbox `U`. -/
theorem udpTh_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (udpTh U).Accepts t) : SockOk (netOf N₀ U P R) (imgRun udpNext evUdp2 {} t) :=
  imgRun_sockOk (evUdp2_ok N₀ U P R) h

/-- **0.3 UDP**: the image of an accepted trace is admitted by the inbox `U`. -/
theorem udpTh3_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (udpTh3 U).Accepts t) : SockOk (netOf N₀ U P R) (imgRun udpNext3 evUdp3 [] t) :=
  imgRun_sockOk (evUdp3_ok N₀ U P R) h

/-- **0.2 name lookup**: the image of an accepted trace is admitted by the resolver `R`. -/
theorem dnsTh_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (dnsTh R).Accepts t) : SockOk (netOf N₀ U P R) (imgRun dnsNext evDns2 [] t) :=
  imgRun_sockOk (evDns2_ok N₀ U P R) h

/-- **0.3 name lookup**: the image of an accepted trace is admitted by the resolver `R`. -/
theorem dnsTh3_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (dnsTh3 R).Accepts t) :
    SockOk (netOf N₀ U P R) (imgRun (fun _ _ => ()) evDns3 () t) :=
  imgRun_sockOk (evDns3_ok N₀ U P R) h

/-- **Accept**: the image of an accepted trace is admitted by the peers `P`. -/
theorem acceptTh_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (h : (acceptTh P).Accepts t) : SockOk (netOf N₀ U P R) (imgRun accNext evAcc {} t) :=
  imgRun_sockOk (evAcc_ok N₀ U P R) h

/-! ## Hosts -/

/-- Events other than answers pass every check. -/
theorem other_ok {S : Type} {ok : S → WEv → Bool} (hok : ∀ q f a, ok q (.req f a) = true ∧
    ok q (.call f a) = true ∧ ∀ r, ok q (.ret f a r) = true) (q : S) (e : WEv)
    (he : e.isImp = false) : ok q e = true := by
  cases e with
  | imp f a r => simp [WEv.isImp] at he
  | req f a => exact (hok q f a).1
  | call f a => exact (hok q f a).2.1
  | ret f a r => exact (hok q f a).2.2 r

/-- **Every run of the concrete 0.3 TCP host has an admitted image.** -/
theorem tcpImpl3_sockOk (N₃ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (ht : Follows (tcpImpl3 N₃) t) :
    SockOk (netOf N₃ U P R) (imgRun (fun _ _ => ()) evTcp3 () t) :=
  tcpTh3_sockOk N₃ U P R (gated_follows (tcpImpl3_ok N₃)
    (other_ok fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩) ht)

/-- **Every run of the concrete 0.2 TCP host has an admitted image.** -/
theorem tcpImpl_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver) {t : List WEv}
    (ht : Follows (tcpImpl N₀) t) : SockOk (netOf N₀ U P R) (imgRun tcpNext evTcp2 [] t) :=
  tcpTh_sockOk N₀ U P R (gated_follows (tcpImpl_ok N₀)
    (other_ok fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩) ht)

/-- **Every run of the concrete 0.2 UDP host has an admitted image.** -/
theorem udpImpl_sockOk (N₀ : Network) {U : Inbox} {D : Delivery} (hD : DeliveryOk U D)
    (P : Peers) (R : Resolver) {t : List WEv} (ht : Follows (udpImpl D) t) :
    SockOk (netOf N₀ U P R) (imgRun udpNext evUdp2 {} t) :=
  udpTh_sockOk N₀ U P R (gated_follows (udpImpl_ok hD)
    (other_ok fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩) ht)

/-- **Every run of the concrete 0.3 UDP host has an admitted image.** -/
theorem udpImpl3_sockOk (N₀ : Network) {U : Inbox} {D : Delivery} (hD : DeliveryOk U D)
    (P : Peers) (R : Resolver) {t : List WEv} (ht : Follows (udpImpl3 D) t) :
    SockOk (netOf N₀ U P R) (imgRun udpNext3 evUdp3 [] t) :=
  udpTh3_sockOk N₀ U P R (gated_follows (udpImpl3_ok hD)
    (other_ok fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩) ht)

/-! ## Adapters -/

/-- **TCP 0.3 over 0.2**: over every host of `tcpTh N₀`, the 0.3 connect events of the composite
are admitted by the translated network `net3of2 N₀`. -/
theorem tcp3Over2_sockOk (N₀ : Network) (rounds : Nat) (U : Inbox) (P : Peers) (R : Resolver)
    {Y : Sig.{0}} {η : Host Y tcpImports} (hη : (hostSat (tcpTh N₀).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody (tcp3Over2 rounds) ()),
      SockOk (netOf (net3of2 N₀) U P R) (imgRun (fun _ _ => ()) evTcp3 () (htrace p)) :=
  fun p hp => tcpTh3_sockOk _ U P R (tcp3Over2_model N₀ rounds hη p hp)

/-- **TCP 0.2 over 0.3**: the 0.2 connect events are admitted by `net2of3 N₃`. -/
theorem tcp2Over3_sockOk (N₃ : Network) (U : Inbox) (P : Peers) (R : Resolver)
    {Y : Sig.{0}} {η : Host Y tcp3Fns} (hη : (hostSat (tcpTh3 N₃).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody tcp2Over3 {}),
      SockOk (netOf (net2of3 N₃) U P R) (imgRun tcpNext evTcp2 [] (htrace p)) :=
  fun p hp => tcpTh_sockOk _ U P R (tcp2Over3_model N₃ hη p hp)

/-- **UDP 0.3 over 0.2**: the 0.3 datagrams of the composite are admitted by the inbox. -/
theorem udp3Over2_sockOk (N₀ : Network) (rounds : Nat) (U : Inbox) (P : Peers) (R : Resolver)
    {Y : Sig.{0}} {η : Host Y udpImports} (hη : (hostSat (udpTh U).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody (udp3Over2 rounds) []),
      SockOk (netOf N₀ U P R) (imgRun udpNext3 evUdp3 [] (htrace p)) :=
  fun p hp => udpTh3_sockOk N₀ U P R (udp3Over2_model U rounds hη p hp)

/-- **UDP 0.2 over 0.3**: the 0.2 datagrams of the composite are admitted by the inbox. -/
theorem udp2Over3_sockOk (N₀ : Network) (U : Inbox) (P : Peers) (R : Resolver)
    {Y : Sig.{0}} {η : Host Y udp3Fns} (hη : (hostSat (udpTh3 U).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody udp2Over3 {}),
      SockOk (netOf N₀ U P R) (imgRun udpNext evUdp2 {} (htrace p)) :=
  fun p hp => udpTh_sockOk N₀ U P R (udp2Over3_model U hη p hp)

/-! ## The extended image -/

/-- Socket events have no LPS part. -/
theorem lpsPart_map_sock (l : List (SockEv Val)) : lpsPart (l.map XEvent.sock) = [] := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [lpsPart, XEvent.toLps]

variable {A B : Type} {stepA : A → WEv → A × List Silmaril.Process.LPS.Event}
  {nextB : B → WEv → B} {evB : B → WEv → List (SockEv Val)}

/-- **The LPS part of the extended image is the LPS image.** -/
theorem lpsPart_xRun : ∀ (a : A) (b : B) (t : List WEv),
    lpsPart (xRun stepA nextB evB a b t) = runA stepA a t
  | _, _, [] => rfl
  | a, b, e :: t => by
    simp only [xRun, runA, lpsPart_append, lpsPart_liftT, lpsPart_map_sock, List.append_nil,
      lpsPart_xRun]

/-- **The socket part of the extended image is the socket image.** -/
theorem sockPart_xRun : ∀ (a : A) (b : B) (t : List WEv),
    sockPart (xRun stepA nextB evB a b t) = imgRun nextB evB b t
  | _, _, [] => rfl
  | a, b, e :: t => by
    simp only [xRun, imgRun, sockPart_append, sockPart_liftT, sockPart_map_sock, List.nil_append,
      sockPart_xRun]

/-- The stateless 0.2 stdout image as a run. -/
theorem runA_osEv (ch : Silmaril.Process.LPS.Word) :
    ∀ t, runA (fun (_ : Unit) e => ((), Silmaril.Wasi.Os.osEv ch e)) () t = Silmaril.Wasi.Os.osTrace ch t
  | [] => rfl
  | e :: t => by
    simp only [runA, runA_osEv ch t, Silmaril.Wasi.Os.osTrace, List.flatMap_cons]

/-- The 0.3 stdout image as a run. -/
theorem runA_osStep3 (ch : Silmaril.Process.LPS.Word) :
    ∀ q t, runA (P3.osStep3 ch) q t = P3.osRun3 ch q t
  | _, [] => rfl
  | q, e :: t => by
    simp only [runA, runA_osStep3 ch _ t, P3.osRun3]

/-- **The LPS part of the extended 0.2 image is the stdout image.** -/
theorem lpsPart_xImg2 (ch : Silmaril.Process.LPS.Word) (t : List WEv) :
    lpsPart (xImg2 ch t) = Silmaril.Wasi.Os.osTrace ch t :=
  (lpsPart_xRun _ _ t).trans (runA_osEv ch t)

/-- **The LPS part of the extended 0.3 image is the stdout image.** -/
theorem lpsPart_xImg3 (ch : Silmaril.Process.LPS.Word) (t : List WEv) :
    lpsPart (xImg3 ch t) = P3.osTrace3 ch t :=
  (lpsPart_xRun _ _ t).trans (runA_osStep3 ch _ t)

/-- Every LPS trace predicate transports: `liftA A` of the extended image is `A` of the stdout
image. -/
theorem liftA_xImg3 (ch : Silmaril.Process.LPS.Word) (A : List Silmaril.Process.LPS.Event → Prop)
    (t : List WEv) : liftA A (xImg3 ch t) ↔ A (P3.osTrace3 ch t) := by
  rw [liftA, lpsPart_xImg3]

/-- The 0.2 socket state along a run. -/
theorem foldl_next2 : ∀ (q : Sock2St) (u : List WEv),
    u.foldl next2 q = (u.foldl tcpNext q.1, u.foldl udpNext q.2)
  | _, [] => rfl
  | q, e :: u => foldl_next2 (next2 q e) u

/-- **The extended image of a 0.3 run** accepted by the TCP and UDP theories is admitted by the
network, and its LPS part is the stdout image. -/
theorem xImg3_netOk (ch : Silmaril.Process.LPS.Word) {N₃ : Network} {U : Inbox} (P : Peers)
    (R : Resolver) {t : List WEv} (h₁ : (tcpTh3 N₃).Accepts t) (h₂ : (udpTh3 U).Accepts t) :
    NetOk (netOf N₃ U P R) (xImg3 ch t) ∧ lpsPart (xImg3 ch t) = P3.osTrace3 ch t := by
  refine ⟨fun ev hev => ?_, lpsPart_xImg3 ch t⟩
  have hs : SockOk (netOf N₃ U P R) (imgRun udpNext3 ev3 [] t) :=
    imgRun_sockOk' [] t fun u e v hu => sockOk_append
      (evTcp3_ok N₃ U P R _ e (gated_ok h₁ u e v hu)) (evUdp3_ok N₃ U P R _ e (gated_ok h₂ u e v hu))
  have hev' : ev ∈ imgRun udpNext3 ev3 [] t := by
    rw [xImg3, sockPart_xRun] at hev
    exact hev
  exact hs ev hev'

/-- **The extended image of a 0.2 run** accepted by the TCP and UDP theories is admitted by the
network, and its LPS part is the stdout image. -/
theorem xImg2_netOk (ch : Silmaril.Process.LPS.Word) {N₀ : Network} {U : Inbox} (P : Peers)
    (R : Resolver) {t : List WEv} (h₁ : (tcpTh N₀).Accepts t) (h₂ : (udpTh U).Accepts t) :
    NetOk (netOf N₀ U P R) (xImg2 ch t) ∧ lpsPart (xImg2 ch t) = Silmaril.Wasi.Os.osTrace ch t := by
  refine ⟨fun ev hev => ?_, lpsPart_xImg2 ch t⟩
  have hs : SockOk (netOf N₀ U P R) (imgRun next2 ev2 ([], {}) t) :=
    imgRun_sockOk' _ t fun u e v hu => by
      rw [foldl_next2]
      exact sockOk_append (evTcp2_ok N₀ U P R _ e (gated_ok h₁ u e v hu))
        (evUdp2_ok N₀ U P R _ e (gated_ok h₂ u e v hu))
  have hev' : ev ∈ imgRun next2 ev2 ([], {}) t := by
    rw [xImg2, sockPart_xRun] at hev
    exact hev
  exact hs ev hev'

/-- **`hello3` in the extended vocabulary**: its extended image has the LPS part `hiOut ch` and
no socket event. -/
theorem hello3_xImg (ch : Silmaril.Process.LPS.Word) :
    lpsPart (xImg3 ch (wtrace P3.hello3Run)) = Silmaril.Wasi.Os.hiOut ch ∧
      sockPart (xImg3 ch (wtrace P3.hello3Run)) = [] :=
  ⟨(lpsPart_xImg3 ch _).trans (P3.hello3Run_os ch), by rw [xImg3, sockPart_xRun]; rfl⟩

end Silmaril.Wasi.Versions.SockOs
