module

public import Silmaril.Wasi.Versions.WitImport.RNetTyping.Thms
public import Silmaril.Wasi.Versions.Udp.Defs

/-!
# UDP in 0.2 and 0.3 against the resolved WIT typing

The UDP slices of `Silmaril.Wasi.Versions.Udp` (`udpImports`, `udp3Fns`, `udpTh3`, the hosts
`udpImpl`, `udpImpl3`) against the resolved packages `sock2P`, `sock3P` read from the vendored
WIT. PROVED by kernel evaluation (`decide +kernel`):

* **Names and positions** (`udp_names`, `udp_params`): every function of both slices is in the
  imported table, with the parameter lists the theories and hosts read.
* **One datagram value for both versions** (`dgram_both`): the value `dgram` is a resolved-typed
  0.2 `incoming-datagram` in a `receive` answer and a resolved-typed 0.3
  `tuple<list<u8>, ip-socket-address>` in a `receive` answer.
* **The concrete hosts answer with the resolved types** on sample runs (`udpImpl_witR_ex`,
  `udpImpl3_witR_ex`): `create`, `bind`/`start-bind`, `stream`, and `receive` with a queued
  datagram and with an empty queue (`error(invalid-state)`).
* **0.3 UDP like 0.2** (`udp3_not_witR`, `udp3_typed_decisive`): REFUTED sound direction (the
  theory accepts a `receive` answer that is not a `result`); the decisive event is typed, accepted
  by the inbox that delivers everything and rejected by the quiet one (REFUTED converse).

These are checks on samples, not a typing theorem for every delivery (open).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions

/-- **Every function of the UDP slices is in the imported tables.** -/
theorem udp_names :
    [Net.instanceNetwork, Net.createUdp, Net.udpBind, Net.udpFinishBind, Net.udpStream,
      Net.udpReceive].all (fun f => (sock2P.1.lookup f).isSome) = true ∧
    [Net.udpCreate3, Net.udpBind3, Net.udpReceive3, Net.udpSend3].all
      (fun f => (sock3P.1.lookup f).isSome) = true := by
  decide +kernel

/-- **The argument positions read by the slices are the imported parameter lists.** -/
theorem udp_params :
    paramsOf sock2P Net.createUdp = some ["address-family"] ∧
    paramsOf sock2P Net.udpFinishBind = some ["self"] ∧
    paramsOf sock3P Net.udpCreate3 = some ["address-family"] ∧
    paramsOf sock3P Net.udpBind3 = some ["self", "local-address"] ∧
    paramsOf sock3P Net.udpReceive3 = some ["self"] ∧
    paramsOf sock3P Net.udpSend3 = some ["self", "data", "remote-address"] := by
  decide +kernel

/-- The 0.3 `receive` on socket `0` answered with `dgram`. -/
def recv3One : WEv := .imp Net.udpReceive3 [.u32 0] (some [okV (some dgram)])
/-- The 0.3 `receive` on socket `0` answered by nothing. -/
def recv3Bad : WEv := .imp Net.udpReceive3 [.u32 0] (some [])
/-- A 0.3 UDP state with socket `0` bound to `addr4`. -/
def udp3Bound : Net.Udp3St := [(0, addr4)]

/-- **One datagram value for both versions**: `dgram` is typed in a 0.2 and a 0.3 answer. -/
theorem dgram_both : witROk sock2P recvOne = true ∧ witROk sock3P recv3One = true := by
  decide +kernel

/-- A delivery of `dgram` everywhere. -/
def dgramEverywhere : Net.Delivery := fun _ => [dgram]

/-- A 0.2 run of `udpImpl dgramEverywhere`: create, start-bind, stream, receive. -/
def udp2Run : List WEv :=
  [.imp Net.createUdp [.variant 0 none] (some [okV (some (.u32 0))]),
   .imp Net.udpBind [.u32 0, .u32 1, addr4] (some [okV none]),
   .imp Net.udpStream [.u32 0, .variant 0 none] (some [okV (some (.record [.u32 2, .u32 3]))])]

/-- **The concrete 0.2 host answers with the resolved types** on a sample run. -/
theorem udpImpl_witR_ex :
    witROk sock2P (.imp Net.udpReceive [.u32 2, .u64 1]
      (Net.udpImpl dgramEverywhere udp2Run Net.udpReceive [.u32 2, .u64 1])) = true ∧
    witROk sock2P (.imp Net.udpReceive [.u32 9, .u64 1]
      (Net.udpImpl dgramEverywhere udp2Run Net.udpReceive [.u32 9, .u64 1])) = true ∧
    witROk sock2P (.imp Net.udpStream [.u32 0, .variant 0 none]
      (Net.udpImpl dgramEverywhere [] Net.udpStream [.u32 0, .variant 0 none])) = true ∧
    witROk sock2P (.imp Net.createUdp [.variant 0 none]
      (Net.udpImpl dgramEverywhere [] Net.createUdp [.variant 0 none])) = true := by
  decide +kernel

/-- A 0.3 run of `udpImpl3 dgramEverywhere`: create, bind. -/
def udp3Run : List WEv :=
  [.imp Net.udpCreate3 [.variant 0 none] (some [okV (some (.u32 0))]),
   .imp Net.udpBind3 [.u32 0, addr4] (some [okV none])]

/-- **The concrete 0.3 host answers with the resolved types** on a sample run: a queued
datagram, and `error(invalid-state)` for an unbound socket. -/
theorem udpImpl3_witR_ex :
    witROk sock3P (.imp Net.udpReceive3 [.u32 0]
      (Net.udpImpl3 dgramEverywhere udp3Run Net.udpReceive3 [.u32 0])) = true ∧
    witROk sock3P (.imp Net.udpReceive3 [.u32 7]
      (Net.udpImpl3 dgramEverywhere udp3Run Net.udpReceive3 [.u32 7])) = true ∧
    witROk sock3P (.imp Net.udpBind3 [.u32 0, addr4]
      (Net.udpImpl3 dgramEverywhere [] Net.udpBind3 [.u32 0, addr4])) = true ∧
    witROk sock3P (.imp Net.udpCreate3 [.variant 0 none]
      (Net.udpImpl3 dgramEverywhere [] Net.udpCreate3 [.variant 0 none])) = true := by
  decide +kernel

/-- **REFUTED: the 0.3 UDP theory admits an answer that is not WIT-typed.** -/
theorem udp3_not_witR :
    Net.udpOk3 Net.udpQuiet udp3Bound recv3Bad = true ∧ argsTypedR sock3P recv3Bad = true ∧
      witROk sock3P recv3Bad = false := by
  decide +kernel

/-- **The 0.3 decisive event is WIT-typed; REFUTED converse.** -/
theorem udp3_typed_decisive :
    argsTypedR sock3P recv3One = true ∧ witROk sock3P recv3One = true ∧
      Net.udpDecisive3 udp3Bound recv3One ∧
      Net.udpOk3 udpAll udp3Bound recv3One = true ∧
      Net.udpOk3 Net.udpQuiet udp3Bound recv3One = false :=
  ⟨by decide +kernel, by decide +kernel, ⟨0, [], dgram, rfl, rfl⟩, by decide +kernel,
    by decide +kernel⟩

end Silmaril.Wasi.Versions.WitImport
