module

public import Silmaril.Project.WasmP3Rust.Hello.File.Defs
public import Silmaril.Project.WasmP3Rust.Echo.File.Defs
public import Silmaril.Project.WasmP3Rust.Cat.File.Defs
public import Silmaril.Project.WasmP3Rust.CatDebug.File.Defs
public import Silmaril.Project.Shapes.Component.Defs
public import Silmaril.Wasi.Versions.P3.Defs

/-!
# The WASI 0.3 Rust examples: the theorems one wants, as frozen statements

For each example of `examples/wasip3-rust` (`hello`, `echo`, `cat`, and the debug build of
`cat`), the statements that would make it a verified WASI 0.3 program, frozen as `Task`
definitions (open targets; nothing here is assumed). What is proved about the files is in
`Silmaril.Project.WasmP3Rust.<Name>.Thms` and `Silmaril.Project.WasmP3Rust.Thms`.

| statement | shape | status |
|---|---|---|
| `Task.parses b` | the file is a component AST of Silmaril's component grammar | open: the grammar has no `canon` async built-ins (`task.return`, `stream.*`, `waitable-set.*`, `context.*`, …), which every example uses |
| `Task.valid b` | `silmaril.shapes.component.valid` | open (needs `Task.parses`) |
| `Task.hasWorld b W` | `silmaril.shapes.component.has_world`, `W` the `wasi:cli/command@0.3.0` world of `world_names` | open (needs `Task.parses` and the world as a `WorldType`); the import and export *names* are proved (`world_names`) |
| `Task.everyHost b den G` | `silmaril.shapes.component.wasi_every_host` against the loose stdout theory `stdoutTh3` | open (needs a semantics `den` of async components) |
| `helloG`, `catG`, `echoG args` | the functional guarantees | stated here |

**The semantics is a parameter.** `den : Ast → p3World.Model` stands for a denotation of
component ASTs as WASI 0.3 strategies (core Wasm execution plus the canonical ABI, async lifts
and lowers, streams and futures), reading the files' `@0.3.0` interface names as `p3World`'s
`@0.3.2` ones (the `wasi:cli` stdio and run interfaces are the same in both). No such
denotation exists here for these components yet (`Binary.Lower` rejects strings, lists,
streams, futures and async options), so the behavioural statements quantify over it.

**Functional guarantees** are prefix-closed trace predicates (`ofTraces`) on the events of the
world, observed through `stdoutBytes` (the bytes stdout accepted, `osTrace3`) and `stdinBytes`
(the bytes `stream.read` delivered on the readable ends of `stdin.read-via-stream`):

* `helloG`: stdout accepted a prefix of `Hello, WASI 0.3!\n`, all of it once `run` returned `ok`;
* `catG`: stdout accepted a prefix of what stdin delivered, all of it once `run` returned `ok`
  (`cat` copies stdin to stdout **modulo rechunking**: only the byte sequences are compared,
  not the chunks of the reads and writes);
* `echoG args`: as `helloG` with the arguments after the program name joined by spaces.

These are the target behaviours over **every** host of the loose theory: the loose theory lets
a write complete partially (`COMPLETED k`, `k ≤ n`), and the Rust programs use `write_all`, which
retries; `Silmaril.Wasi.Versions.P3.hello3_not_loose_correct` refutes the same guarantee for a
program that does not.

**Refuted.** The old grammar rejects all four files (`Silmaril.Project.WasmP3Rust.TasksP3.Thms`:
`<n>_not_parses`). So `Task.parses`, `valid`, `hasWorld` and every behavioural statement here
are false, for every `den`. `Silmaril.Project.WasmP3Rust.TasksP3.Defs` restates them on
`BinaryP3.parse`, and proves the parse, validity and world statements there.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Project.Shapes.Component (CompValid HasWorld WasiEveryHost)

/-- A list of bytes as an array (no pushes). -/
def arrOf (l : List UInt8) : ByteArray := ⟨⟨l⟩⟩

/-! ## Observations of WASI 0.3 traces -/

/-- The bytes stdout accepted along `t`: the write events of its OS image (`osTrace3`). -/
def stdoutBytes (t : List WEv) : List (BitVec 8) :=
  (osTrace3 0 t).filterMap fun
    | .writeEv _ b => some b
    | _ => none

/-- The readable ends of `stdin.read-via-stream` along `t`, and the bytes `stream.read` delivered
on them (completed reads; a read that blocks and completes in `waitable-set.wait` is not part of
the `p3World` slice's encodings). -/
def stdinScan : List Nat → List WEv → List (BitVec 8)
  | _, [] => []
  | rs, .imp f a r :: t =>
    if f = stdinRead3 then
      match r with
      | some [.record [rv, _]] =>
        match natOf rv with
        | some r' => stdinScan (r' :: rs) t
        | none => stdinScan rs t
      | _ => stdinScan rs t
    else if f = cStreamRead then
      match a, r with
      | [rv, _], some [pv, items] =>
        match natOf rv, natOf pv >>= copyOf with
        | some r', some (some (.completed, k)) =>
          if r' ∈ rs then (bytesOf items).take k ++ stdinScan rs t else stdinScan rs t
        | _, _ => stdinScan rs t
      | _, _ => stdinScan rs t
    else stdinScan rs t
  | rs, _ :: t => stdinScan rs t

/-- The bytes stdin delivered along `t`. -/
def stdinBytes (t : List WEv) : List (BitVec 8) := stdinScan [] t

/-- `run` returned `ok` along `t`. -/
def runOk (t : List WEv) : Bool :=
  t.any fun
    | .ret f _ (some [v]) => decide (f = run3) && resultOk v
    | _ => false

/-- The prefix-closed protocol of a trace predicate: it accepts `t` when every prefix of `t`
satisfies `P`. -/
def ofTraces (P : List WEv → Bool) : Protocol (List WEv) WEv :=
  ⟨[], fun q e => if P (q ++ [e]) then some (q ++ [e]) else none⟩

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List (BitVec 8) := s.toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- Stdout accepted a prefix of `msg`, and all of it once `run` returned `ok`. -/
def printsG (msg : List (BitVec 8)) : Protocol (List WEv) WEv :=
  ofTraces fun t => (stdoutBytes t).isPrefixOf msg && (!runOk t || stdoutBytes t == msg)

/-- **`hello`'s guarantee.** -/
def helloG : Protocol (List WEv) WEv := printsG (utf8 "Hello, WASI 0.3!\n")

/-- **`echo`'s guarantee** when the host's `get-arguments` answers `args`. -/
def echoG (args : List String) : Protocol (List WEv) WEv :=
  printsG (utf8 (" ".intercalate (args.drop 1) ++ "\n"))

/-- **`cat`'s guarantee: stdin is copied to stdout modulo rechunking.** -/
def catG : Protocol (List WEv) WEv :=
  ofTraces fun t =>
    (stdoutBytes t).isPrefixOf (stdinBytes t) && (!runOk t || stdoutBytes t == stdinBytes t)

/-! ## The frozen statements -/

/-- Open: **the file parses** under Silmaril's component grammar. Needs the async `canon`
built-ins (see `tools/wasm-tools/README.md`). -/
def Task.parses (b : List UInt8) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.Binary.parse (arrOf b) = .ok c

/-- Open: **the component is valid** (`silmaril.shapes.component.valid`, index scoping). -/
def Task.valid (b : List UInt8) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.Binary.parse (arrOf b) = .ok c ∧ CompValid c

/-- Open: **the component has the world `W`** (`silmaril.shapes.component.has_world`); for the
examples `W` is `wasi:cli/command@0.3.0` restricted to the interfaces of `world_names`. -/
def Task.hasWorld (b : List UInt8) (W : Silmaril.Wasm.Wit.Project.WorldType) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.Binary.parse (arrOf b) = .ok c ∧ HasWorld c W

/-- Open: **over every host of the loose WASI 0.3 stdout theory, the component meets `G`**
(`silmaril.shapes.component.wasi_every_host`), under the semantics `den`. -/
def Task.everyHost (b : List UInt8) (den : Ast → p3World.Model) {S : Type}
    (G : Protocol S WEv) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.Binary.parse (arrOf b) = .ok c ∧
    WasiEveryHost (den c) stdoutTh3 G

/-- Open: `hello` prints its line over every loose host. -/
def Task.hello_prints (den : Ast → p3World.Model) : Prop :=
  Task.everyHost Hello.File.bytes den helloG

/-- Open: `cat` copies stdin to stdout modulo rechunking over every loose host. -/
def Task.cat_copies (den : Ast → p3World.Model) : Prop :=
  Task.everyHost Cat.File.bytes den catG

/-- Open: the debug build of `cat` copies stdin to stdout modulo rechunking. -/
def Task.catDebug_copies (den : Ast → p3World.Model) : Prop :=
  Task.everyHost CatDebug.File.bytes den catG

/-- Open: **the release and debug builds of `cat` behave the same** under `den`
(`silmaril.shapes.component.digest_behaviour_eq` on the two files). -/
def Task.cat_release_debug (den : Ast → p3World.Model) : Prop :=
  ∃ a b : Ast, Silmaril.Wasm.Component.Binary.parse (arrOf Cat.File.bytes) = .ok a ∧
    Silmaril.Wasm.Component.Binary.parse (arrOf CatDebug.File.bytes) = .ok b ∧ den a = den b

/-- Open: `echo` prints its arguments, in a world `W` with `wasi:cli/environment` whose theory
`T` makes `get-arguments` answer `args` (`p3World` has no environment interface). -/
def Task.echo_prints {S : Type} (W : World) (den : Ast → W.Model) (T : Protocol S WEv)
    (args : List String) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.Binary.parse (arrOf Echo.File.bytes) = .ok c ∧
    WasiEveryHost (den c) T (echoG args)

end Silmaril.Project.WasmP3Rust

end
