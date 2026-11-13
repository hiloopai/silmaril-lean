module

public import Silmaril.Wasi.Versions.Adapter.Defs
public import Silmaril.Wasi.Versions.P2.Host.Defs
public import Silmaril.Wasi.Versions.Net.Defs

@[expose] public section

/-!
# The adapter's 0.2.12 theory against the 0.2.9 theory, and a concrete 0.2 host under it

The preview1 adapter (`Silmaril.Wasi.Versions.Adapter`) assumes the theory `Adapter.p2Th` of its 23
imports, checked against WIT 0.2.12 (the WIT wasmtime `v50.0.1` generates the adapter from).
The WASI 0.2 theory `P2.p2Th r` of `Silmaril.Wasi.Versions.P2` is checked against WIT 0.2.9. The
function names and signatures used are the same in both revisions (they differ in the
`@0.2.x` package versions and in `@since` gates only), so both theories speak about the same
events.

## What the 0.2.9 theory gives the adapter, and what it lacks (`extraTh`)

`P2.p2Th r` implies the adapter's typing of `get-stdin`, `get-stdout`, `get-stderr`,
`[resource-drop]output-stream`, `[resource-drop]descriptor`, monotonic `now` (through `clockTh`)
and `resolution`, `wall-clock.now`/`resolution`, `get-arguments`, `get-environment`, `exit`, of
non-trap answers of `blocking-write-and-flush`, and of `blocking-read(self, len)`. The
remaining sentences of `Adapter.p2Th` are `extraTh`:

* `blocking-write-and-flush` does not trap (the 0.2 theory allows a trap beyond 4096 bytes; the
  adapter writes chunks of at most 4096 bytes, but its theory is stated for every argument);
* `blocking-read` with arguments of another shape answers an error;
* `[resource-drop]input-stream`, `wasi:io/error.[resource-drop]error`: `()` (unconstrained in
  the 0.2 slice);
* `filesystem-error-code`, `wasi:random/random.get-random-bytes` (not in the 0.2 slice);
* `get-directories` returns at most 125 preopens (the room of the adapter's table);
* `open-at`, `get-type`, `read-via-stream`, `write-via-stream`: an error is an `error-code`
  enum case (the 0.2 slice accepts any error payload).

`Silmaril.Wasi.Versions.Adapter.Over.Thms`: `p2Th_of_p2` (`P2.p2Th r ⊗ extraTh ⊨ Adapter.p2Th`).

## A concrete 0.2 host for the adapter (`p2ImplA`)

`P2.p2Impl` traps on the drops of input streams and errors, and does not answer
`filesystem-error-code` or `get-random-bytes` (outside its slice). `p2ImplA` is `p2Impl`
completed on these four functions (drops answer `()`, `filesystem-error-code` answers `none`,
random bytes are zeros). It is a model of the strict 0.2 theory and of `extraTh`, hence of
`Adapter.p2Th` on well-typed calls (`concreteWT`: `Adapter.p2Th` accepts no answer to
`get-random-bytes` with ill-typed arguments, so no host that answers every call is a model of
it), and `link (concreteWT p2ImplA) adapter` is a concrete preview1 host.

## Systems

`p2Sys x` adds the network and web of a system `x : Net.Sys O` to `p2ImplA` (`wasi:sockets`
and `wasi:http` answered by `Net.tcpImpl x.net`, `Net.httpImpl x.web`). The adapter imports no
socket or http function, so the preview1 host `link (concreteWT (p2Sys x)) adapter` is the same
for all systems.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The sentences of `Imp.ok` that the 0.2.9 theory does not give. -/
def Imp.extraOk : Imp → List Val → Option (List Val) → Bool
  | .write, _, r => r.isSome
  | .read, a, r => (match a with | [_, .u64 _] => true | _ => Imp.read.ok a r)
  | .getStdin, _, _ | .getStdout, _, _ | .getStderr, _, _ | .outDrop, _, _ | .fdDrop, _, _
  | .now, _, _ | .monoRes, _, _ | .wallNow, _, _ | .wallRes, _, _ | .getArgs, _, _
  | .getEnv, _, _ | .exit, _, _ => true
  | i, a, r => i.ok a r

/-- The sentences of the adapter's theory that the 0.2.9 theory does not give, on events. -/
def extraOk : WEv → Bool
  | .imp f a r =>
    match Imp.ofName f with
    | some i => i.extraOk a r
    | none => true
  | _ => true

/-- **The adapter's 0.2.12 sentences beyond the 0.2.9 theory.** -/
def extraTh : Protocol Unit WEv := pointwise extraOk

/-- **The concrete 0.2 host for the adapter**: `P2.p2Impl`, completed on the drops of input
streams and errors, `filesystem-error-code` and `get-random-bytes`. -/
def p2ImplA : Impl := fun p f a =>
  if f = inDrop ∨ f = errDrop then some []
  else if f = fsErrCode then some [.variant 0 none]
  else if f = randBytes then
    (match a with
     | [.u64 len] => some [.record (List.replicate len.toNat (.u8 0))]
     | _ => some [.record []])
  else P2.p2Impl p f a

/-- A well-typed call of the adapter's imports: `get-random-bytes` takes one `u64` (the only
import whose typing in `Adapter.p2Th` rejects every answer to an ill-typed call). -/
def wellCalled : WEv → Bool
  | .imp f a _ => if f = randBytes then (match a with | [.u64 _] => true | _ => false) else true
  | _ => true

/-- Following `impl` and answering only well-typed calls is prefix-closed. -/
theorem prefixClosed_followsWT (impl : Impl) :
    PrefixClosed (fun t => Follows impl t ∧ ∀ e ∈ t, wellCalled e = true) :=
  ⟨⟨(prefixClosed_follows impl).1, fun _ h => absurd h List.not_mem_nil⟩,
    fun _ _ hab hb => ⟨(prefixClosed_follows impl).2 hab hb.1, fun e he => hb.2 e (hab.subset he)⟩⟩

/-- **The concrete host of `impl` on well-typed calls**: it answers as `impl`, and only calls
that are well typed (the canonical ABI lifts only well-typed values; an ill-typed call is not
answered). -/
def concreteWT {Y : Silmaril.Games.Sig.{0}} {I : Set FnName} (impl : Impl) : Host Y I :=
  ofPred _ (prefixClosed_followsWT impl)

/-- The interfaces of the network functions. -/
def netIfaces : List String :=
  ["wasi:sockets/instance-network", "wasi:sockets/tcp-create-socket", "wasi:sockets/tcp",
   "wasi:http/outgoing-handler", "wasi:http/types"]

/-- **The 0.2 host of a system**: `p2ImplA`, with `wasi:sockets` answered by the system's
network and `wasi:http` by its web. -/
def p2Sys {O : Type} (x : Net.Sys O) : Impl := fun p f a =>
  if f.iface ∈ netIfaces then
    (if f.iface = "wasi:http/outgoing-handler" ∨ f.iface = "wasi:http/types" then
      Net.httpImpl x.web p f a
    else Net.tcpImpl x.net p f a)
  else p2ImplA p f a

/-- **The preview1 host of a system**: the adapter over the system's 0.2 host. -/
def p1Sys {Y : Silmaril.Games.Sig.{0}} {O : Type} (x : Net.Sys O) : Host Y P1.imports :=
  link (concreteWT (p2Sys x)) adapter

end Silmaril.Wasi.Versions.Adapter
