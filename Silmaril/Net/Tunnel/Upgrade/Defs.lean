module

public import Silmaril.Net.Http2.Fields.Defs

@[expose] public section

/-!
# HTTP Upgrade and protocol switching (RFC 9110 §7.8, §15.2.2, §15.5.22; RFC 2817; RFC 9113 §8.6)

`Upgrade` (RFC 9110 §7.8) lets an HTTP/1.1 client ask to switch the connection to another
protocol; a server that agrees answers `101 (Switching Protocols)` and the connection carries
the new protocol "immediately after the 101 response" (§15.2.2). The rules modelled here:

* the request lists protocols in `Upgrade` and names `upgrade` in `Connection` ("the sender
  MUST also send an Upgrade connection option", §7.8);
* "A server MUST NOT switch to a protocol that was not indicated by the client in the
  corresponding request's Upgrade header field" and a 101 response lists the protocol(s)
  switched to, "in layer-ascending order" (§7.8): `validSwitch`;
* `426 (Upgrade Required)` "MUST send an Upgrade header field to indicate the required
  protocol(s)" (§15.5.22): `validUpgradeRequired`;
* "A server MAY ignore a received Upgrade header field" (§7.8): ignoring is always allowed;
* HTTP/2 has no 101 and no `Upgrade` ("HTTP/2 removes support for the 101 (Switching
  Protocols) informational status code", RFC 9113 §8.6; `upgrade` is a connection-specific
  field, §8.2.2): `Silmaril.Net.Http2.validRegular` already rejects it, and
  `Upgrade.Thms.h2_rejects_upgrade` records it.

Upgrade tokens (IANA "HTTP Upgrade Token Registry", RFC 9110 §16.7): `HTTP` (RFC 9110),
`TLS` (RFC 2817), `WebSocket` (RFC 6455, compared case-insensitively), `h2c` (RFC 7540 §3.2,
**removed** by RFC 9113 §3.1: "the "h2c" upgrade token … is not defined"). `UpgradeToken`
records each with its status.

**Historical TLS upgrade (RFC 2817).** RFC 2817 §3 lets a client send `Upgrade: TLS/1.0` with
`Connection: Upgrade` on an `http` connection and start TLS after a `101` (§3.3); a server may
demand it with `426` (§4.2). The optional form (§3.1) puts the upgrade on the real request,
which therefore travels in clear and can be downgraded; the mandatory form (§3.2) sends
`OPTIONS *` first. Neither reaches an `https` origin, which RFC 9110 §4.3.3 defines by a TLS
connection from the start; `Silmaril.Net.Tunnel.Transport` proves what each form exposes. Browsers do not implement RFC 2817; it is modelled because it is the
historical rule that the `TLS` upgrade token denotes.
-/

namespace Silmaril.Net.Tunnel

open Silmaril.Net.Hpack (ascii Entry)

/-- An entry of the HTTP Upgrade Token Registry, with its status. -/
inductive UpgradeToken where
  /-- `HTTP/x.y` (RFC 9110 §7.8). -/
  | http (major minor : Nat)
  /-- `TLS/x.y` (RFC 2817 §3): upgrade an `http` connection to TLS. -/
  | tls (major minor : Nat)
  /-- `websocket` (RFC 6455 §4, §11.2). -/
  | websocket
  /-- `h2c` (RFC 7540 §3.2): removed by RFC 9113 §3.1. -/
  | h2c
  /-- Any other token, by its octets (`protocol-name ["/" protocol-version]`). -/
  | other (name : List UInt8)
  deriving DecidableEq, Repr

/-- Whether a token is defined by a current RFC (`h2c` was withdrawn by RFC 9113). -/
def UpgradeToken.current : UpgradeToken → Bool
  | .h2c => false
  | _ => true

/-- An upgrade request (RFC 9110 §7.8): the protocols offered, in order of preference, and
whether `Connection` names `upgrade`. -/
structure UpgradeRequest where
  offered : List UpgradeToken
  connectionUpgrade : Bool
  deriving DecidableEq, Repr

/-- A request that may be upgraded: a non-empty offer, with the connection option. -/
def UpgradeRequest.valid (r : UpgradeRequest) : Bool := !r.offered.isEmpty && r.connectionUpgrade

/-- The server's answer to an upgrade request. -/
inductive UpgradeAnswer where
  /-- The server ignores `Upgrade` and answers in the current protocol. -/
  | ignore
  /-- `101`, switching to the listed protocols, in layer-ascending order. -/
  | switch (to : List UpgradeToken)
  /-- `426 Upgrade Required`, with the `Upgrade` field it MUST send. -/
  | required (upgrade : List UpgradeToken)
  deriving DecidableEq, Repr

/-- §7.8: switch only to offered protocols, at least one; and only on a valid request. -/
def validSwitch (r : UpgradeRequest) : UpgradeAnswer → Bool
  | .ignore => true
  | .switch to => r.valid && !to.isEmpty && to.all r.offered.contains
  | .required up => !up.isEmpty

/-- §15.5.22: a 426 names the required protocol(s). -/
def validUpgradeRequired : UpgradeAnswer → Bool
  | .required up => !up.isEmpty
  | _ => true

/-- The protocol on the connection after the answer: the last (outermost) switched-to
protocol, or `none` if the connection stays on HTTP/1.1. -/
def afterAnswer : UpgradeAnswer → Option UpgradeToken
  | .switch to => to.getLast?
  | _ => none

/-- An HTTP/2 field section that tries to request an upgrade. -/
def upgradeEntry (v : List UInt8) : Entry := ⟨ascii "upgrade", v⟩

end Silmaril.Net.Tunnel
