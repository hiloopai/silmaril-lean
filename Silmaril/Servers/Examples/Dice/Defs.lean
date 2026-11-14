module

public import Silmaril.Servers.Http.Defs
public import Silmaril.Servers.Hosts.Defs

/-!
# Example: a dice server over a random host

A server with one modeled nondeterministic import, `wasi:random/random` `get-random-u64`
(`Q = Unit`, `R = UInt64`). The same server is a `wasi:http` component in
`tests/servers/policies` (`dice.wat`), run by `wasmtime serve` under host policies; this module
is its specification and its abstract model, not a reading of that binary.

* `/roll`: `200` with the decimal digit of `face 6 x = x % 6 + 1`, for one draw `x`;
* `/pair`: `200` with `a b`, two draws in order;
* any other path-with-query (or none): `404 not found`.

The **buggy** variant (`dice-buggy.wat`) uses `face 7` on `/roll`: it answers `7` exactly when
the host's draw is `6` modulo `7`.

Responses are written with one decimal digit (`digit`), so faces up to `9`.

**Hosts.** The server is a `Machine` on the state of a stateful host `h : Stateful σ Unit
UInt64` (`machine k h`): each draw is a step of the host. Two ways of running it:

* `server k h`: one instance, the host's state carries over between requests;
* `perRequest k h`: a fresh instance per request, the host restarting from `h.init` each time,
  as `wasmtime serve` runs the proxy world (the harness observes this: all `/roll` answers of a
  run are equal; `Thms.perRequest_roll_const` is the model's version).

`openDice k` is the open server: its behaviour (after a successful initialization) under each
host.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Examples.Dice

open Silmaril.Servers Silmaril.Servers.Hosts Silmaril.Servers.Observe
open Silmaril.Net.Http (Request Response)

/-- The face of a draw on a die with `k` faces. -/
def face (k : Nat) (x : UInt64) : Nat := x.toNat % k + 1

/-- One decimal digit (`n ≤ 9`). -/
def digit (n : Nat) : List UInt8 := [(48 + n).toUInt8]

/-- `200` with a face. -/
def rollResp (n : Nat) : Response := Response.simple 200 (digit n)

/-- `200` with two faces, separated by a space. -/
def pairResp (a b : Nat) : Response := Response.simple 200 (digit a ++ [32] ++ digit b)

/-- `404 not found`. -/
def notFound : Response := Response.simple 404 [110, 111, 116, 32, 102, 111, 117, 110, 100]

/-- The path `/roll`. -/
def rollPath : Option (List UInt8) := some [47, 114, 111, 108, 108]

/-- The path `/pair`. -/
def pairPath : Option (List UInt8) := some [47, 112, 97, 105, 114]

/-- A `GET` for a path-with-query. -/
def getReq (p : Option (List UInt8)) : Request := ⟨⟨.get, ⟨none, none, p⟩⟩, [], [], []⟩

/-- **The dice server with `k` faces**, on the state of the host `h`. -/
def machine (k : Nat) {σ : Type} (h : Stateful σ Unit UInt64) : Machine Http.sig σ :=
  fun (q : σ) (r : Request) (s : Response) (q' : σ) =>
    if r.target.pathWithQuery = rollPath then
      s = rollResp (face k (h.step q ()).1) ∧ q' = (h.step q ()).2
    else if r.target.pathWithQuery = pairPath then
      s = pairResp (face k (h.step q ()).1) (face k (h.step (h.step q ()).2 ()).1) ∧
        q' = (h.step (h.step q ()).2 ()).2
    else s = notFound ∧ q' = q

/-- One instance; the host's state carries over. -/
def server (k : Nat) {σ : Type} (h : Stateful σ Unit UInt64) : Model Http.sig :=
  (machine k h).server h.init

/-- A fresh instance per request; the host restarts from its initial state. -/
def perRequest (k : Nat) {σ : Type} (h : Stateful σ Unit UInt64) : Model Http.sig :=
  (Machine.ofRel fun (r : Request) (s : Response) => ∃ q', machine k h h.init r s q').server ()

/-- **The open server**: the behaviour under each host, one instance. -/
def openDice (k : Nat) (σ : Type) : Open (Stateful σ Unit UInt64) Http.sig :=
  fun h => Beh.ofModel (server k h)

/-- **The specification**: `/roll` gives a face in `1..6`, `/pair` two, other paths `404`. -/
def Ok (r : Request) (s : Response) : Prop :=
  (r.target.pathWithQuery = rollPath → ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ s = rollResp n) ∧
  (r.target.pathWithQuery = pairPath →
    ∃ a b, 1 ≤ a ∧ a ≤ 6 ∧ 1 ≤ b ∧ b ≤ 6 ∧ s = pairResp a b) ∧
  (r.target.pathWithQuery ≠ rollPath → r.target.pathWithQuery ≠ pairPath → s = notFound)

/-- The specification as a trace sentence. -/
def spec : Sen Http.sig := Sen.atomic (A := Http.sig) Ok

/-- "Some `/roll` is answered `6`", on observations. -/
def rollsSix : Obs Http.sig → Prop
  | .run t => ∃ i, Event.recv i (getReq rollPath) ∈ t ∧ Event.send i (rollResp 6) ∈ t
  | _ => False

/-- The host that always draws `0` (the harness's `zero` policy), a pure host. -/
def zeroHost : Stateful Unit Unit UInt64 := Pure.toStateful fun _ => 0

/-- The host that always draws `x`. -/
def constHost (x : UInt64) : Stateful Unit Unit UInt64 := Pure.toStateful fun _ => x

end Silmaril.Servers.Examples.Dice
