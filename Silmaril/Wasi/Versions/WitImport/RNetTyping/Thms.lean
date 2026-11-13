module

public import Silmaril.Wasi.Versions.WitImport.RCli2.Thms
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTyping.Thms
public import Silmaril.Wasi.Versions.NetMore.Defs

/-!
# UDP, name lookup and accept against the resolved WIT typing

The `NetMore` theories (`Silmaril.Wasi.Versions.NetMore`: `udpTh`, `dnsTh`, `dnsTh3`, `acceptTh`)
are behavioural and gated, like the TCP theories of `Silmaril.Wasi.Versions.WitImport.NetTyping`.
Against the resolved packages `sock2P`, `sock3P` (`sock2P_strip`, `sock3P_strip`: their tables
are `sock2T`, `sock3T`):

* **Positions** (`netMore_params`): the argument positions the theories read (`self`, then
  `network`, then `local-address` for `start-bind`; `self` for `stream`, `receive`,
  `resolve-next-address`, `accept`, `remote-address`; `network`, then `name` for the 0.2
  `resolve-addresses`; `name` for the 0.3 one) are the imported parameter lists.
* **The gates see every typed success** (`stream_recorded`, `accept_recorded`,
  `resolve2_recorded`, `bind_recorded`): a resolved-typed `ok` answer of `start-bind`,
  `stream`, `accept` (on a bound socket) or of the 0.2 `resolve-addresses` has the shape the
  state update reads, so it is recorded. The theories' patterns miss no WIT-typed success.
* **REFUTED sound direction** (`netMore_not_witR`): on a tied stream, a bound socket, a
  stream of a name, and for the 0.3 lookup, each theory accepts an answer that is not a
  `result` at all, which the resolved (and the unresolved) typing rejects.
* **REFUTED converse; the decisive events are typed** (`netMore_typed_decisive`): for UDP, 0.2
  and 0.3 name lookup and accept, a decisive answer that has the resolved WIT type (with
  resolved-typed arguments) is accepted by the environment that delivers everything and
  rejected by the quiet one. So the WIT typing does not imply the theories, and relation (d)
  (no common decisive answer) is not an artefact of ill-typed answers.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions

theorem sock2P_strip : strip sock2P.1 = sock2T := by decide +kernel
theorem sock3P_strip : strip sock3P.1 = sock3T := by decide +kernel
theorem http2P_strip : strip http2P.1 = http2T := by decide +kernel

/-- The parameter names of `f` in `P`. -/
def paramsOf (P : RPkg) (f : FnName) : Option (List String) :=
  (P.1.lookup f).map fun x => x.2.params.map Prod.fst

/-- **The argument positions read by the theories are the imported parameter lists.** -/
theorem netMore_params :
    paramsOf sock2P Net.udpBind = some ["self", "network", "local-address"] ∧
    paramsOf sock2P Net.tcpBind = some ["self", "network", "local-address"] ∧
    paramsOf sock2P Net.udpStream = some ["self", "remote-address"] ∧
    paramsOf sock2P Net.udpReceive = some ["self", "max-results"] ∧
    paramsOf sock2P Net.resolve2 = some ["network", "name"] ∧
    paramsOf sock2P Net.resolveNext = some ["self"] ∧
    paramsOf sock2P Net.tcpAccept = some ["self"] ∧
    paramsOf sock2P Net.tcpRemote = some ["self"] ∧
    paramsOf sock3P Net.resolve3 = some ["name"] := by
  decide +kernel

/-! ## Typed successes are recorded -/

/-- The result type of `f` in `P`. -/
def resultOf (P : RPkg) (f : FnName) : Option (Binary.IfaceName × Option Binary.Ty) :=
  (P.1.lookup f).map fun x => (x.1, x.2.result)

/-- An `ok` payload of a resolved `result<t, _>`. -/
theorem okPayload {E : TyEnv} {i : Binary.IfaceName} {s : Binary.Sig} {t : Option Binary.Ty}
    {e : Option Binary.Ty} (hs : s.result = some (.result t e)) {p : Option Val}
    (h : resOkR E i s (some [.variant 0 p]) = true) : optOk (tyOkR E 31 i) t p = true := by
  rcases s with ⟨b, ps, r⟩
  simp only at hs
  subst hs
  rw [resOkR_one] at h
  simpa only [fuel, tyOkR_result, resV] using h

theorem own_u32 {E : TyEnv} {n : Nat} {i : Binary.IfaceName} {x : Binary.TyRef} {v : Val}
    (h : tyOkR E (n + 1) i (.own x) v = true) : ∃ k, v = .u32 k := by
  cases v <;> simp_all [tyOkR_own, isU32]

theorem stream_res :
    resultOf sock2P Net.udpStream = some (⟨⟨"wasi", "sockets", some "0.2.12"⟩, "udp"⟩,
    some (.result (some (.tuple [ownT "incoming-datagram-stream", ownT "outgoing-datagram-stream"]))
      (some (refT "error-code")))) := by
  decide +kernel

theorem accept_res :
    resultOf sock2P Net.tcpAccept = some (⟨⟨"wasi", "sockets", some "0.2.12"⟩, "tcp"⟩,
    some (.result (some (.tuple [ownT "tcp-socket", ownT "input-stream", ownT "output-stream"]))
      (some (refT "error-code")))) := by
  decide +kernel

theorem resolve2_res :
    resultOf sock2P Net.resolve2 = some (⟨⟨"wasi", "sockets", some "0.2.12"⟩, "ip-name-lookup"⟩,
      some (.result (some (ownT "resolve-address-stream")) (some (refT "error-code")))) := by
  decide +kernel

theorem bind_res : resultOf sock2P Net.udpBind = some (⟨⟨"wasi", "sockets", some "0.2.12"⟩, "udp"⟩,
      some (.result none (some (refT "error-code")))) ∧
    resultOf sock2P Net.tcpBind = some (⟨⟨"wasi", "sockets", some "0.2.12"⟩, "tcp"⟩,
      some (.result none (some (refT "error-code")))) := by
  decide +kernel

theorem entry_of {P : RPkg} {f : FnName} {i i' : Binary.IfaceName} {s : Binary.Sig}
    {t : Option Binary.Ty} (hr : resultOf P f = some (i', t)) (hl : P.1.lookup f = some (i, s)) :
    i = i' ∧ s.result = t := by
  simp only [resultOf, hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
  exact hr

/-- **A typed `ok` answer of `stream` on a bound socket ties its incoming stream.** -/
theorem stream_recorded (q : Net.UdpSt) (s : BitVec 32) (a : List Val) (addr : Val)
    (p : Option Val) (hb : Net.lookup s q.bound = some addr) {i : Binary.IfaceName}
    {sg : Binary.Sig} (hl : sock2P.1.lookup Net.udpStream = some (i, sg))
    (h : resOkR sock2P.2 i sg (some [.variant 0 p]) = true) :
    ∃ k, (Net.udpNext q (.imp Net.udpStream (.u32 s :: a) (some [.variant 0 p]))).ins =
      (k, addr) :: q.ins := by
  obtain ⟨rfl, hs⟩ := entry_of stream_res hl
  have hp := okPayload hs h
  rcases p with _ | v
  · exact absurd hp Bool.false_ne_true
  cases v <;> try exact absurd hp Bool.false_ne_true
  rename_i vs
  rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩ <;>
    simp only [optOk, tyOkR_tuple, zipOk, Bool.and_false, Bool.false_eq_true, Bool.and_true,
      Bool.and_eq_true] at hp
  obtain ⟨k, rfl⟩ := own_u32 hp.1
  obtain ⟨k', rfl⟩ := own_u32 hp.2
  exact ⟨k, by simp [Net.udpNext, hb]⟩

/-- **A typed `ok` answer of `accept` on a bound socket records the accepted socket.** -/
theorem accept_recorded (q : Net.AccSt) (s : BitVec 32) (a : List Val) (addr : Val)
    (p : Option Val) (hb : Net.lookup s q.bound = some addr) {i : Binary.IfaceName}
    {sg : Binary.Sig} (hl : sock2P.1.lookup Net.tcpAccept = some (i, sg))
    (h : resOkR sock2P.2 i sg (some [.variant 0 p]) = true) :
    ∃ c, (Net.accNext q (.imp Net.tcpAccept (.u32 s :: a) (some [.variant 0 p]))).acc =
      (c, addr) :: q.acc := by
  obtain ⟨rfl, hs⟩ := entry_of accept_res hl
  have hp := okPayload hs h
  rcases p with _ | v
  · exact absurd hp Bool.false_ne_true
  cases v <;> try exact absurd hp Bool.false_ne_true
  rename_i vs
  rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, vs⟩⟩⟩⟩ <;>
    simp only [optOk, tyOkR_tuple, zipOk, Bool.and_false, Bool.false_eq_true, Bool.and_true,
      Bool.and_eq_true] at hp
  obtain ⟨c, rfl⟩ := own_u32 hp.1
  obtain ⟨d, rfl⟩ := own_u32 hp.2.1
  obtain ⟨d', rfl⟩ := own_u32 hp.2.2
  exact ⟨c, by simp [Net.accNext, hb]⟩

/-- **A typed `ok` answer of the 0.2 `resolve-addresses` records the stream's name.** -/
theorem resolve2_recorded (q : Net.DnsSt) (nw name : Val) (a : List Val) (p : Option Val)
    {i : Binary.IfaceName} {sg : Binary.Sig} (hl : sock2P.1.lookup Net.resolve2 = some (i, sg))
    (h : resOkR sock2P.2 i sg (some [.variant 0 p]) = true) :
    ∃ st, Net.dnsNext q (.imp Net.resolve2 (nw :: name :: a) (some [.variant 0 p])) =
      (st, name) :: q := by
  obtain ⟨rfl, hs⟩ := entry_of resolve2_res hl
  have hp := okPayload hs h
  rcases p with _ | v
  · exact absurd hp Bool.false_ne_true
  have hv : tyOkR sock2P.2 31 ⟨⟨"wasi", "sockets", some "0.2.12"⟩, "ip-name-lookup"⟩
      (ownT "resolve-address-stream") v = true := by
    simpa only [optOk] using hp
  obtain ⟨st, rfl⟩ := own_u32 hv
  exact ⟨st, by simp [Net.dnsNext]⟩

/-- **A typed `ok` answer of `start-bind` records the bound socket** (UDP and TCP). -/
theorem bind_recorded (s : BitVec 32) (nw addr : Val) (a : List Val) (p : Option Val)
    {i : Binary.IfaceName} {sg : Binary.Sig} :
    (sock2P.1.lookup Net.udpBind = some (i, sg) →
      resOkR sock2P.2 i sg (some [.variant 0 p]) = true →
      ∀ q : Net.UdpSt, (Net.udpNext q (.imp Net.udpBind (.u32 s :: nw :: addr :: a)
        (some [.variant 0 p]))).bound = (s, addr) :: q.bound) ∧
    (sock2P.1.lookup Net.tcpBind = some (i, sg) →
      resOkR sock2P.2 i sg (some [.variant 0 p]) = true →
      ∀ q : Net.AccSt, (Net.accNext q (.imp Net.tcpBind (.u32 s :: nw :: addr :: a)
        (some [.variant 0 p]))).bound = (s, addr) :: q.bound) := by
  constructor
  all_goals
    intro hl h q
    first
      | obtain ⟨rfl, hs⟩ := entry_of bind_res.1 hl
      | obtain ⟨rfl, hs⟩ := entry_of bind_res.2 hl
    have hp := okPayload hs h
    rcases p with _ | v
    · simp [Net.udpNext, Net.accNext]
    · exact absurd hp Bool.false_ne_true

/-! ## Refutations -/

/-- Some arguments of `f` in `P` have the resolved parameter types. -/
def argsTypedR (P : RPkg) : WEv → Bool
  | .imp f a _ => match P.1.lookup f with
    | some (i, s) => argsOkR P.2 i s a
    | none => false
  | _ => false

/-- An IPv4 socket address `127.0.0.1:80`. -/
def addr4 : Val := .variant 0 (some (.record [.u16 80, .record [.u8 127, .u8 0, .u8 0, .u8 1]]))
/-- The IPv4 address `127.0.0.1`. -/
def ip4 : Val := .variant 0 (some (.record [.u8 127, .u8 0, .u8 0, .u8 1]))
/-- A datagram of one byte from `addr4`. -/
def dgram : Val := .record [.record [.u8 1], addr4]

/-- A UDP state with the stream `0` tied to `addr4`. -/
def udpTied : Net.UdpSt := { ins := [(0, addr4)] }
/-- An accept state with the socket `0` bound to `addr4`. -/
def accBound : Net.AccSt := { bound := [(0, addr4)] }
/-- A name lookup state with the stream `0` of the name `"a"`. -/
def dnsNamed : Net.DnsSt := [(0, strV "a")]

/-- `receive` on the tied stream, answered by nothing. -/
def recvBad : WEv := .imp Net.udpReceive [.u32 0, .u64 1] (some [])
/-- `accept` on the bound socket, answered by nothing. -/
def acceptBad : WEv := .imp Net.tcpAccept [.u32 0] (some [])
/-- `resolve-next-address` on the named stream, answered by nothing. -/
def nextBad : WEv := .imp Net.resolveNext [.u32 0] (some [])

/-- **REFUTED: the theories admit answers that are not WIT-typed**, even where they check. -/
theorem netMore_not_witR :
    (Net.udpOk Net.udpQuiet udpTied recvBad = true ∧ argsTypedR sock2P recvBad = true ∧
      witROk sock2P recvBad = false) ∧
    (Net.accOk Net.noPeers accBound acceptBad = true ∧ argsTypedR sock2P acceptBad = true ∧
      witROk sock2P acceptBad = false) ∧
    (Net.dnsOk Net.dnsEmpty dnsNamed nextBad = true ∧ argsTypedR sock2P nextBad = true ∧
      witROk sock2P nextBad = false) ∧
    (Net.dnsOk3 Net.dnsEmpty () resolveBad = true ∧ argsTypedR sock3P resolveBad = true ∧
      witROk sock3P resolveBad = false) := by
  decide +kernel

/-- `receive` on the tied stream answered with one datagram. -/
def recvOne : WEv := .imp Net.udpReceive [.u32 0, .u64 1] (some [okV (some (.record [dgram]))])
/-- `accept` on the bound socket answered `ok`. -/
def acceptOne : WEv :=
  .imp Net.tcpAccept [.u32 0] (some [okV (some (.record [.u32 1, .u32 2, .u32 3]))])
/-- `resolve-next-address` on the named stream answered `ok(some(127.0.0.1))`. -/
def nextOne : WEv := .imp Net.resolveNext [.u32 0] (some [okV (some (.variant 1 (some ip4)))])
/-- The 0.3 `resolve-addresses("a")` answered `ok([127.0.0.1])`. -/
def resolve3One : WEv := .imp Net.resolve3 [strV "a"] (some [okV (some (.record [ip4]))])

/-- Every datagram arrives everywhere. -/
def udpAll : Net.Inbox := fun _ _ => true
/-- Every name has every address. -/
def dnsAll : Net.Resolver := fun _ _ => true
/-- Every address has every peer. -/
def allPeers : Net.Peers := ⟨fun _ => true, fun _ _ => true⟩

/-- **The decisive events are WIT-typed; REFUTED converse.** Each event has resolved-typed
arguments and answer, is decisive, is accepted by the environment that delivers everything and
rejected by the quiet one. -/
theorem netMore_typed_decisive :
    (argsTypedR sock2P recvOne = true ∧ witROk sock2P recvOne = true ∧
      Net.udpDecisive udpTied recvOne ∧
      Net.udpOk udpAll udpTied recvOne = true ∧ Net.udpOk Net.udpQuiet udpTied recvOne = false) ∧
    (argsTypedR sock2P acceptOne = true ∧ witROk sock2P acceptOne = true ∧
      Net.accDecisive accBound acceptOne ∧
      Net.accOk allPeers accBound acceptOne = true ∧
      Net.accOk Net.noPeers accBound acceptOne = false) ∧
    (argsTypedR sock2P nextOne = true ∧ witROk sock2P nextOne = true ∧
      Net.dnsDecisive dnsNamed nextOne ∧
      Net.dnsOk dnsAll dnsNamed nextOne = true ∧ Net.dnsOk Net.dnsEmpty dnsNamed nextOne = false) ∧
    (argsTypedR sock3P resolve3One = true ∧ witROk sock3P resolve3One = true ∧
      Net.dnsDecisive3 () resolve3One ∧
      Net.dnsOk3 dnsAll () resolve3One = true ∧
      Net.dnsOk3 Net.dnsEmpty () resolve3One = false) := by
  refine ⟨⟨by decide +kernel, by decide +kernel, ⟨0, [.u64 1], dgram, [], rfl, rfl⟩,
      by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, ⟨0, [], _, rfl, rfl⟩, by decide +kernel,
      by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, ⟨0, [], ip4, rfl, rfl⟩, by decide +kernel,
      by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, ⟨strV "a", [], ip4, [], rfl⟩, by decide +kernel,
      by decide +kernel⟩⟩

end Silmaril.Wasi.Versions.WitImport
