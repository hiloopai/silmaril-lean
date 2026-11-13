module

public import Silmaril.Wasi.Versions.NetMore.Defs
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# UDP, name lookup and accept are not implementable over preview1

PROVED (standard axioms), relation (d) for the slices of `Silmaril.Wasi.Versions.NetMore`:

* `gated_not_both`: for any host `η` of any import world and any component `σ`, if `link η σ`
  has a decisive event, it is not a model of two gated theories without a common decisive
  answer. `no_obs_over_p1`: hence no component importing preview1 implements such a family over
  preview1 (`ObsOverP1`) while deciding over some preview1 model (`ObsResponsive`).
* The disjointness of each slice: `udp_disjoint` (every inbox against `udpQuiet`),
  `dns_disjoint`, `dns3_disjoint` (every resolver against `dnsEmpty`), `acc_disjoint` (every set
  of peers against `noPeers`).
* **`no_udp_over_p1`**, **`no_dns_over_p1`**, **`no_dns3_over_p1`**, **`no_accept_over_p1`**.
* Non-vacuity: `dns_decisive_example`, `dns3_decisive_example`, `udp_decisive_example`,
  `accept_decisive_example`: each theory accepts a two- or three-answer trace with a decisive
  event for some environment.

As for TCP connect and HTTP (`no_tcp_over_p1`), these are relative to preview1 host models that
do not depend on the environment (`ObsOverP1` quantifies over all environments for one host).
For **accept** this is the substantive restriction: preview1's `sock_accept` accepts on a
listening socket the host preopened, so a preview1 host wired to the network *can* observe
peers at that one address. What preview1 lacks is `bind` (a guest-chosen local address) and
`listen`; a statement about network-dependent preview1 hosts would need a model of preview1
socket descriptors, which `P1.th` does not have.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Generic -/

/-- **Two environments, one host**, for any gated family. -/
theorem gated_not_both {S : Type} {init : S} {next : S → WEv → S} {ok₁ ok₂ : S → WEv → Bool}
    {D : S → WEv → Prop} (hD : ∀ q e, D q e → ok₁ q e = true → ok₂ q e = false)
    {Y : Sig.{0}} {I X : Set FnName} {η : Host Y I} {σ : Strategy (nsig I) (nsig X)}
    (hresp : ∃ p ∈ link η σ, Decides init next D (htrace p))
    (h₁ : (hostSat (gated init next ok₁).Accepts).holds (link η σ)) :
    ¬ (hostSat (gated init next ok₂).Accepts).holds (link η σ) := fun h₂ => by
  obtain ⟨p, hp, hd⟩ := hresp
  exact not_decides hD (h₁ p hp) (h₂ p hp) hd

/-- **A gated family with two disjoint environments is not implementable over preview1.** -/
theorem no_obs_over_p1 {E S : Type} {init : S} {next : S → WEv → S} {ok : E → S → WEv → Bool}
    {D : S → WEv → Prop} (x₁ x₂ : E) (hD : ∀ q e, D q e → ok x₁ q e = true → ok x₂ q e = false)
    {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (ObsOverP1 init next ok σ ∧ ObsResponsive init next D σ) := by
  rintro ⟨hσ, Y, η, hη, hresp⟩
  exact gated_not_both hD hresp (hσ x₁ Y η hη) (hσ x₂ Y η hη)

/-! ## Disjointness -/

/-- Every inbox and the quiet one admit no common decisive UDP answer. -/
theorem udp_disjoint (U : Inbox) (q : UdpSt) (e : WEv) (hd : udpDecisive q e)
    (_ : udpOk U q e = true) : udpOk udpQuiet q e = false := by
  obtain ⟨i, a, x, l, rfl, hs⟩ := hd
  obtain ⟨addr, hl⟩ := Option.isSome_iff_exists.1 hs
  simp [udpOk, hl, recvOk, udpQuiet]

/-- Every resolver and the empty one admit no common decisive 0.2 answer. -/
theorem dns_disjoint (R : Resolver) (q : DnsSt) (e : WEv) (hd : dnsDecisive q e)
    (_ : dnsOk R q e = true) : dnsOk dnsEmpty q e = false := by
  obtain ⟨st, a, x, rfl, hs⟩ := hd
  obtain ⟨name, hl⟩ := Option.isSome_iff_exists.1 hs
  simp [dnsOk, hl, nextOk, dnsEmpty]

/-- Every resolver and the empty one admit no common decisive 0.3 answer. -/
theorem dns3_disjoint (R : Resolver) (q : Unit) (e : WEv) (hd : dnsDecisive3 q e)
    (_ : dnsOk3 R q e = true) : dnsOk3 dnsEmpty q e = false := by
  obtain ⟨name, a, x, l, rfl⟩ := hd
  simp [dnsOk3, listOk, dnsEmpty]

/-- Every set of peers and the empty one admit no common decisive accept answer. -/
theorem acc_disjoint (P : Peers) (q : AccSt) (e : WEv) (hd : accDecisive q e)
    (_ : accOk P q e = true) : accOk noPeers q e = false := by
  obtain ⟨s, a, v, rfl, hs⟩ := hd
  obtain ⟨addr, hl⟩ := Option.isSome_iff_exists.1 hs
  simp [accOk, hl, acceptOk, noPeers]

/-! ## Not implementable over preview1 -/

/-- **UDP receive is not implementable over preview1.** -/
theorem no_udp_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (ObsOverP1 {} udpNext udpOk σ ∧ ObsResponsive {} udpNext udpDecisive σ) :=
  no_obs_over_p1 (fun _ _ => true) udpQuiet (udp_disjoint _) σ

/-- **0.2 name lookup is not implementable over preview1.** -/
theorem no_dns_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (ObsOverP1 [] dnsNext dnsOk σ ∧ ObsResponsive [] dnsNext dnsDecisive σ) :=
  no_obs_over_p1 (fun _ _ => true) dnsEmpty (dns_disjoint _) σ

/-- **0.3 name lookup is not implementable over preview1.** -/
theorem no_dns3_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (ObsOverP1 () (fun _ _ => ()) dnsOk3 σ ∧
      ObsResponsive () (fun _ _ => ()) dnsDecisive3 σ) :=
  no_obs_over_p1 (fun _ _ => true) dnsEmpty (dns3_disjoint _) σ

/-- **Bind/listen/accept is not implementable over preview1** (for environment-independent
preview1 hosts; see the module docstring). -/
theorem no_accept_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (ObsOverP1 {} accNext accOk σ ∧ ObsResponsive {} accNext accDecisive σ) :=
  no_obs_over_p1 ⟨fun _ => true, fun _ _ => true⟩ noPeers (acc_disjoint _) σ

/-! ## Non-vacuity -/

/-- An address. -/
def addr0 : Val := .variant 0 (some (.record [.u16 80, .record [.u8 10, .u8 0, .u8 0, .u8 1]]))

/-- A name. -/
def name0 : Val := strV "example.org"

/-- A run of the 0.2 name lookup theory with a decisive answer. -/
def dnsRun : List WEv :=
  [.imp resolve2 [.u32 0, name0] (some [.variant 0 (some (.u32 7))]),
   .imp resolveNext [.u32 7] (some [.variant 0 (some (.variant 1 (some addr0)))])]

/-- **The 0.2 name lookup theory admits a decisive run.** -/
theorem dns_decisive_example :
    (dnsTh fun _ _ => true).Accepts dnsRun ∧ Decides [] dnsNext dnsDecisive dnsRun := by
  refine ⟨by unfold Protocol.Accepts; decide,
    [.imp resolve2 [.u32 0, name0] (some [.variant 0 (some (.u32 7))])], _, [], rfl, 7, [], addr0,
    rfl, ?_⟩
  decide

/-- **The 0.3 name lookup theory admits a decisive run.** -/
theorem dns3_decisive_example :
    (dnsTh3 fun _ _ => true).Accepts [.imp resolve3 [name0] (some [.variant 0 (some (.record [addr0]))])] ∧
      Decides () (fun _ _ => ()) dnsDecisive3
        [.imp resolve3 [name0] (some [.variant 0 (some (.record [addr0]))])] :=
  ⟨by unfold Protocol.Accepts; decide, [], _, [], rfl, name0, [], addr0, [], rfl⟩

/-- A datagram from `addr0`. -/
def dgram0 : Val := .record [.record [.u8 1], addr0]

/-- A run of the UDP theory with a decisive answer. -/
def udpRun : List WEv :=
  [.imp udpBind [.u32 3, .u32 0, addr0] (some [.variant 0 none]),
   .imp udpStream [.u32 3, .variant 0 none] (some [.variant 0 (some (.record [.u32 4, .u32 5]))]),
   .imp udpReceive [.u32 4, .u64 1] (some [.variant 0 (some (.record [dgram0]))])]

/-- **The UDP theory admits a decisive run.** -/
theorem udp_decisive_example :
    (udpTh fun _ _ => true).Accepts udpRun ∧ Decides {} udpNext udpDecisive udpRun := by
  refine ⟨by unfold Protocol.Accepts; decide,
    [.imp udpBind [.u32 3, .u32 0, addr0] (some [.variant 0 none]),
     .imp udpStream [.u32 3, .variant 0 none] (some [.variant 0 (some (.record [.u32 4, .u32 5]))])],
    _, [], rfl, 4, [.u64 1], dgram0, [], rfl, ?_⟩
  decide

/-- A run of the accept theory with a decisive answer. -/
def accRun : List WEv :=
  [.imp tcpBind [.u32 3, .u32 0, addr0] (some [.variant 0 none]),
   .imp tcpAccept [.u32 3] (some [.variant 0 (some (.record [.u32 4, .u32 5, .u32 6]))])]

/-- **The accept theory admits a decisive run.** -/
theorem accept_decisive_example :
    (acceptTh ⟨fun _ => true, fun _ _ => true⟩).Accepts accRun ∧ Decides {} accNext accDecisive accRun := by
  refine ⟨by unfold Protocol.Accepts; decide,
    [.imp tcpBind [.u32 3, .u32 0, addr0] (some [.variant 0 none])], _, [], rfl, 3, [], _, rfl, ?_⟩
  decide

end Silmaril.Wasi.Versions.Net
