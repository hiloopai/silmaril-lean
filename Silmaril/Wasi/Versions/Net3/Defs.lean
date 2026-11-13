module

public import Silmaril.Wasi.Versions.Net.Defs
public import Silmaril.Wasi.Versions.WitImport.Derived.Defs

@[expose] public section

/-!
# WASI 0.3 `wasi:sockets` TCP connect as a theory

Checked against `specs/wasi/0.3.2/sockets/types.wit` (interface `types`, resource
`tcp-socket`):

* `create: static func(address-family: ip-address-family) -> result<tcp-socket, error-code>`
  (`create3`, canonical name `[static]tcp-socket.create`);
* `connect: async func(remote-address: ip-socket-address) -> result<_, error-code>`
  (`connect3`, `[method]tcp-socket.connect`), observed **sync-lowered** as in
  `Silmaril.Wasi.Versions.P3`: one call whose answer is the callee's `task.return` value
  (`Silmaril.Wasm.Component.Async.syncRun_result`).

0.3 has no `network` resource, no `start-`/`finish-` split and no `would-block`: the async
`connect` returns the outcome. Its `error-code` is a different `variant` from 0.2's `enum`
(`codes3`, `codes2`; `other(option<string>)` carries a payload). `e2to3` and `e3to2` translate by
name (`e2to3_names`, `e3to2_names` check the tables against the name lists); the codes without a
counterpart go to `other` (0.3) and `unknown` (0.2): 0.2 `unknown`, `concurrency-conflict`,
`not-in-progress`, `would-block`, `new-socket-limit` and the three resolver codes; 0.3
`connection-broken` (EPIPE) and `other`.

## The theory

`tcpTh3 N3`, for a network `N3 : Network` with 0.3 codes, is gated (as `Net.tcpTh`) with a
trivial state: an answer of `connect(s, addr)` is `ok` when `N3 addr = none`, `error(k)` when
`N3 addr = some k`, **or a trap**. The trap is admitted because the theory is a safety theory
like `tcpTh`, where `finish-connect` may answer `would-block` for ever; a trapping `connect`
claims nothing about the network. Errors that are not outcomes of the network (the
`invalid-argument`/`invalid-state` cases of the WIT) are not admitted, as in `tcpTh`.
`net3of2 N` and `net2of3 N3` translate networks between the two code spaces.

`tcpImpl3 N3` answers every `connect` with `N3`'s outcome; `create` answers a fresh handle.

`Silmaril.Process.LPS.Event` has no socket events (`readEv`, `writeEv`, `exitEv` and `killEv`
only), so these hosts have no image in the LPS events themselves. They do have an image in the
extended events of `Silmaril.Machine.Process.IoSpecNet` (the LPS events embedded, plus socket
events `SockEv`): `Silmaril.Wasi.Versions.SockOs` maps a `connect` answered by `tcpTh3 N3`, or by
`tcpImpl3 N3`, to a `connect` socket event (`evTcp3`), and proves every such event admitted by
the network (`tcpTh3_sockOk`, `tcpImpl3_sockOk`; for 0.2, `tcpTh_sockOk`). The refinement of
socket events to x86 syscalls is not proved (`IoSpecNet.sockArm` is assumed).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Names -/

/-- `wasi:sockets/types@0.3.2.[static]tcp-socket.create`. -/
def create3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[static]tcp-socket.create"⟩
/-- `wasi:sockets/types@0.3.2.[method]tcp-socket.connect` (async, observed sync-lowered). -/
def connect3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.connect"⟩

/-- The 0.3 TCP functions of this slice, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `tcp3Fns_eq`. -/
def tcp3Fns : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.sock3T) WitImport.tcp3Keys}

/-- **The imported functions of `tcp3Fns` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem tcp3Fns_eq : tcp3Fns = {create3, connect3} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.sock3T) WitImport.tcp3Keys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.sock3T) WitImport.tcp3Keys).Perm [create3, connect3] by decide +kernel).mem_iff]
  simp

/-! ## Error codes

The code tables are **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport.Derived`):
`codes2`, `codes3`, `e2to3`, `e3to2` and `ecV3` are the WIT-derived definitions. The tables as
first written by hand are kept as the related variants `codes2H`, `codes3H`, `e2to3H`,
`e3to2H`, `ecV3H`; `Silmaril.Wasi.Versions.Net3` proves each equal to its WIT-derived counterpart
(`codes2_eq_hand`, `e2to3_eq_hand`, …), and those equalities are what proofs unfold. -/

/-- The cases of 0.2 `wasi:sockets/network.error-code`, in order, read from
`specs/wasi/0.2.12/sockets/network.wit`. -/
def codes2 : List String := WitImport.codes2W

/-- The cases of 0.3 `wasi:sockets/types.error-code`, in order, read from
`specs/wasi/0.3.2/sockets/types.wit`. -/
def codes3 : List String := WitImport.codes3W

/-- 0.3 `error-code.other` (`eOther3_wit`: the case number of `other` in `codes3`). -/
abbrev eOther3 : Nat := 14

/-- A 0.2 code as a 0.3 code, by name (`other` without a counterpart), from the WIT. -/
def e2to3 : Nat → Nat := WitImport.e2to3W

/-- A 0.3 code as a 0.2 code, by name (`unknown` without a counterpart), from the WIT. -/
def e3to2 : Nat → Nat := WitImport.e3to2W

/-- The value of a 0.3 `error-code` (`other` carries `option::none`), from the WIT payloads. -/
def ecV3 : Nat → Val := WitImport.ecV3W

/-! ### The hand-written tables (related variants) -/

/-- The cases of 0.2 `error-code`, as written by hand. -/
def codes2H : List String :=
  ["unknown", "access-denied", "not-supported", "invalid-argument", "out-of-memory", "timeout",
   "concurrency-conflict", "not-in-progress", "would-block", "invalid-state", "new-socket-limit",
   "address-not-bindable", "address-in-use", "remote-unreachable", "connection-refused",
   "connection-reset", "connection-aborted", "datagram-too-large", "name-unresolvable",
   "temporary-resolver-failure", "permanent-resolver-failure"]

/-- The cases of 0.3 `error-code`, as written by hand. -/
def codes3H : List String :=
  ["access-denied", "not-supported", "invalid-argument", "out-of-memory", "timeout",
   "invalid-state", "address-not-bindable", "address-in-use", "remote-unreachable",
   "connection-refused", "connection-broken", "connection-reset", "connection-aborted",
   "datagram-too-large", "other"]

/-- `e2to3`, as written by hand. -/
def e2to3H : Nat → Nat
  | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 9 => 5 | 11 => 6 | 12 => 7 | 13 => 8
  | 14 => 9 | 15 => 11 | 16 => 12 | 17 => 13
  | _ => eOther3

/-- `e3to2`, as written by hand. -/
def e3to2H : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 9 | 6 => 11 | 7 => 12 | 8 => 13
  | 9 => 14 | 11 => 15 | 12 => 16 | 13 => 17
  | _ => 0

/-- `ecV3`, as written by hand. -/
def ecV3H (k : Nat) : Val :=
  if k = eOther3 then .variant k (some (.variant 0 none)) else .variant k none

/-- A network with 0.3 codes from one with 0.2 codes. -/
def net3of2 (N : Network) : Network := fun a => (N a).map e2to3

/-- A network with 0.2 codes from one with 0.3 codes. -/
def net2of3 (N3 : Network) : Network := fun a => (N3 a).map e3to2

/-! ## The theory -/

/-- An answer of `connect` for the outcome `o` (0.3 codes). -/
def connectOk3 : Option Nat → Option (List Val) → Bool
  | none, some [.variant 0 none] => true
  | some k, some [.variant 1 (some (.variant k' _))] => k' == k
  | _, _ => false

/-- The check of an answer against the network `N3`. -/
def tcpOk3 (N3 : Network) (_ : Unit) (e : WEv) : Bool :=
  match e with
  | .imp f (_ :: addr :: _) r => if f = connect3 then r.isNone || connectOk3 (N3 addr) r else true
  | _ => true

/-- **The 0.3 TCP connect theory** of the network `N3`. -/
def tcpTh3 (N3 : Network) : Protocol Unit WEv := gated () (fun _ _ => ()) (tcpOk3 N3)

/-- A decisive 0.3 event: a `connect` that does not trap. -/
def tcpDecisive3 (_ : Unit) (e : WEv) : Prop :=
  ∃ s addr rest r, e = .imp connect3 (s :: addr :: rest) (some r)

/-- The answers decide a 0.3 connect. -/
def TcpDecides3 (t : List WEv) : Prop := Decides () (fun _ _ => ()) tcpDecisive3 t

/-- The 0.3 answer of an outcome. -/
def outcomeAns3 : Option Nat → Option (List Val)
  | none => some [okV none]
  | some k => some [errV (some (ecV3 k))]

/-- **The concrete 0.3 TCP host of `N3`**: fresh handles; `connect` answers `N3`'s outcome. -/
def tcpImpl3 (N3 : Network) : Impl := fun p f a =>
  if f = create3 then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = connect3 then
    (match a with
     | _ :: addr :: _ => outcomeAns3 (N3 addr)
     | _ => none)
  else none

/-- A component importing preview1 implements the 0.3 TCP theory over preview1. -/
def Tcp3OverP1 {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) : Prop :=
  ∀ (N3 : Network) (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports),
    (hostSat P1.th.Accepts).holds η → (hostSat (tcpTh3 N3).Accepts).holds (link η σ)

/-- The composite decides a 0.3 connect over some preview1 host model. -/
def Tcp3Responsive {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) :
    Prop :=
  ∃ (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports), (hostSat P1.th.Accepts).holds η ∧
    ∃ p ∈ link η σ, TcpDecides3 (htrace p)

end Silmaril.Wasi.Versions.Net
