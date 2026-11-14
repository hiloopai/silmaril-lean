module

public import Silmaril.Net.Tls.Registry.Defs

@[expose] public section

/-!
# How an HTTP request reaches its origin: direct TLS, upgrades and tunnels

This module distinguishes the ways a client can set up the connection that carries an HTTP
request, and what each exposes to the network, under an explicit attacker model:

| Setup | Standards | Status |
| --- | --- | --- |
| `directTls origin alpn` | RFC 9110 §4.2.2, §4.3.3 (`https`); RFC 8446 (TLS 1.3); RFC 7301 (ALPN); historically RFC 2818 | current |
| `cleartext origin` | RFC 9110 §4.2.1, §4.3.2 (`http`); RFC 9112 | current |
| `h2cPriorKnowledge origin` | RFC 9113 §3.3 | current |
| `h2cUpgrade origin` | RFC 7540 §3.2 | removed by RFC 9113 §3.1 |
| `tlsUpgrade origin mode` | RFC 2817 §3 (`Upgrade: TLS/1.0`) | historical, not deployed by browsers |
| `connectTunnel proxy proxyTls inner` | RFC 9110 §9.3.6 (CONNECT), with `inner` end to end | current |

**Model.** `Setup.traces s` lists the possible sequences of `Phase`s on the wire when an
**active network attacker** may drop or rewrite cleartext octets (the Dolev–Yao network of
RFC 3552 §3), but cannot break TLS. Each `request` phase records which TLS peer, if any, protects
the request octets end to end on the hop where they travel. The attacker's power appears in
one place: an *optional* upgrade can be stripped (the attacker removes `Upgrade` or answers
without `101`), so both outcomes are traces.

**Assumption, not theorem.** "Protected by peer `p`" means: TLS with `p`'s authenticated
identity (RFC 9110 §4.3.4 certificate checks; RFC 8446 §4.4.2) provides confidentiality and
integrity. That is the assumption the TLS analyses establish under the computational
assumptions listed in `Silmaril.Net.Tls.CipherSuite.assumptions`. This module proves only
the combinatorial consequences: which setups ever send a request outside TLS with the origin.

**Results** (`Transport.Thms`): `endToEnd_protects` (the structural description is sound for
every setup, tunnels included) and `protects_iff_endToEnd` (and exact without tunnels);
cleartext, `h2c`, and RFC 2817 upgrades that are optional or carried on the real request
expose the request to the network attacker; the `OPTIONS`-first mandatory RFC 2817 upgrade
protects the request but is not an `https` setup; `https_setups_protect`: every setup allowed
for an `https` origin (`Setup.httpsAllowed`: direct TLS, possibly inside CONNECT tunnels)
protects.
-/

namespace Silmaril.Net.Tunnel

open Silmaril.Net.Tls

/-- A host and port, as octets (`authority`, RFC 3986 §3.2). -/
abbrev Authority := List UInt8

/-- How RFC 2817 is used. -/
inductive TlsUpgradeMode where
  /-- RFC 2817 §3.1 "Optional Upgrade": `Upgrade: TLS/1.0` on the real request; "the server
  MAY respond to the clear HTTP operation normally". -/
  | optional
  /-- A client that would refuse a cleartext response but puts the upgrade on the real request.
  RFC 2817 §3.2 forbids this ("If an unsecured response would be unacceptable, a client MUST
  send an OPTIONS request first"); modelled to show why. -/
  | mandatorySameRequest
  /-- RFC 2817 §3.2 "Mandatory Upgrade": `OPTIONS *` with the upgrade first, the real request
  only after the TLS handshake, and no request without `101`. -/
  | mandatoryOptions
  deriving DecidableEq, Repr

/-- A connection setup. -/
inductive Setup where
  | directTls (origin : Authority) (alpn : Option AlpnId)
  | cleartext (origin : Authority)
  | h2cPriorKnowledge (origin : Authority)
  | h2cUpgrade (origin : Authority)
  | tlsUpgrade (origin : Authority) (mode : TlsUpgradeMode)
  /-- CONNECT to `proxy` (over TLS to the proxy if `proxyTls`), then `inner` in the tunnel. -/
  | connectTunnel (proxy : Authority) (proxyTls : Bool) (inner : Setup)
  deriving DecidableEq, Repr

/-- What happens on the wire. `none` as protector means cleartext on the hop. -/
inductive Phase where
  | tlsHandshake (peer : Authority)
  /-- The client's request for the resource. -/
  | request (protectedBy : Option Authority)
  /-- Other HTTP octets: an `OPTIONS *` upgrade probe, a CONNECT request. -/
  | control (protectedBy : Option Authority)
  deriving DecidableEq, Repr

/-- The origin a setup reaches. -/
def Setup.origin : Setup → Authority
  | .directTls o _ | .cleartext o | .h2cPriorKnowledge o | .h2cUpgrade o | .tlsUpgrade o _ => o
  | .connectTunnel _ _ inner => inner.origin

/-- Inside a tunnel to a proxy over TLS, cleartext of the inner setup is still protected on the
network hop, by the proxy's TLS (the proxy reads it). -/
def Phase.underProxy (proxy : Authority) (proxyTls : Bool) : Phase → Phase
  | .request none => .request (if proxyTls then some proxy else none)
  | .control none => .control (if proxyTls then some proxy else none)
  | p => p

/-- The possible traces under an active network attacker. -/
def Setup.traces : Setup → List (List Phase)
  | .directTls o _ => [[.tlsHandshake o, .request (some o)]]
  | .cleartext _ | .h2cPriorKnowledge _ | .h2cUpgrade _ => [[.request none]]
  | .tlsUpgrade o .optional =>
    [[.request none, .tlsHandshake o], [.request none]]
  | .tlsUpgrade o .mandatorySameRequest => [[.request none, .tlsHandshake o], [.request none]]
  | .tlsUpgrade o .mandatoryOptions =>
    [[.control none, .tlsHandshake o, .request (some o)], [.control none]]
  | .connectTunnel p ptls inner =>
    (inner.traces).map fun tr =>
      (if ptls then [Phase.tlsHandshake p] else []) ++
        Phase.control (if ptls then some p else none) :: tr.map (Phase.underProxy p ptls)

/-- Every request in a trace is protected by TLS with `origin`. -/
def protectsTrace (origin : Authority) (tr : List Phase) : Bool :=
  tr.all fun
    | .request q => q == some origin
    | _ => true

/-- Every trace of the setup keeps every request inside TLS with the origin. -/
def Setup.protects (s : Setup) : Bool := s.traces.all (protectsTrace s.origin)

/-- The setups whose requests are always end to end TLS with the origin, described
structurally. -/
def Setup.endToEnd : Setup → Bool
  | .directTls _ _ => true
  | .tlsUpgrade _ .mandatoryOptions => true
  | .connectTunnel _ _ inner => inner.endToEnd
  | _ => false

/-- The setups an `https` origin may be reached with (RFC 9110 §4.3.3: a TLS connection to the
origin, possibly through a CONNECT tunnel, RFC 9110 §9.3.6). -/
def Setup.httpsAllowed : Setup → Bool
  | .directTls _ _ => true
  | .connectTunnel _ _ inner => inner.httpsAllowed
  | _ => false

end Silmaril.Net.Tunnel
