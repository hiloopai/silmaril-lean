module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
meta import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.RecordExamples

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Channel.endKind)

public abbrev grow := SingleThreaded.neverFail
public abbrev engine := core3 grow
@[expose] public def resource : RtId := ⟨0⟩
@[expose] public def element : Option (WIT.ClosedType RtId) :=
  some (.record [("word", .prim .u16), ("resource", .own resource)])
@[expose] public def signatureFor (channel : Channel) : Signature := ⟨Bool, (fun isTuple =>
  let owners : WIT.ClosedType RtId := .fixedList (.own resource) 2
  let reader : WIT.ClosedType RtId := .option (match channel with | .stream => .stream element | .future => .future element)
  if isTuple then .tuple [owners, reader] else .record [("owners", owners), ("reader", reader)]), fun _ => .fixed 0⟩
@[expose] public def signature : Signature := signatureFor .stream
private def contractFor (channel : Channel) : Endpoints.Core.Contract (signatureFor channel) :=
  ⟨0, ("host", "accept-node"), (fun tag => if tag == 0 then some false else if tag == 1 then some true else none),
    {}, ⟨0⟩⟩
private def contract : Endpoints.Core.Contract signature := contractFor .stream

private def wordFn (params results : Nat) : V1.FuncType :=
  ⟨List.replicate params (.int .i32), List.replicate results (.int .i32)⟩

private def coreMemory : engine.MemAddr := (0 : Nat)
private def readerMemory : engine.MemAddr := (1 : Nat)

private def imports (channel : Channel) : List (String × V1.FuncType × CanonHost engine) :=
  let signature := signatureFor channel
  let accept := Endpoints.Core.Scheduled.acceptType (contractFor channel)
  let flat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload true)⟩
  let recordFlat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload false)⟩
  let flatIn := wordFn 6 2
  let wideIn : V1.FuncType := ⟨.int .i64 :: .int .i64 :: ABI.flatten .i64 (signature.payload true), flatIn.results⟩
  let asyncOpts : CanonOpts engine := { memory := some coreMemory, async_ := true }
  let (create, dropReader, dropWriter, write, arity) : ResolvedBuiltin engine × ResolvedBuiltin engine ×
      ResolvedBuiltin engine × ResolvedBuiltin engine × Nat := match channel with
    | .stream => (.streamNew element, .streamDropReadable element, .streamDropWritable element,
        .streamWrite element asyncOpts, 3)
    | .future => (.futureNew element, .futureDropReadable element, .futureDropWritable element,
        .futureWrite element asyncOpts, 2)
  [("accept-node", accept, .embedder "accept-node" accept),
    ("give-record", wordFn 2 2, .embedder "give-record" (wordFn 2 2)),
    ("give-payload", wordFn 2 2, .embedder "give-payload" (wordFn 2 2)),
    ("bad-memory", wordFn 2 2, .embedder "bad-memory" (wordFn 2 2)),
    ("bad-realloc", wordFn 2 2, .embedder "bad-realloc" (wordFn 2 2)),
    ("new-own", wordFn 1 1, .builtin (.resourceNew resource .i32) ⟨0⟩),
    ("new-channel", ⟨[], [.int .i64]⟩, .builtin create ⟨0⟩),
    ("rep", wordFn 1 1, .builtin (.resourceRep resource .i32) ⟨0⟩),
    ("close-reader", wordFn 1 0, .builtin dropReader ⟨0⟩),
    ("close-writer", wordFn 1 0, .builtin dropWriter ⟨0⟩),
    ("give-flat", flat, .embedder "give-flat" flat),
    ("wrong-flat-schema", recordFlat, .embedder "wrong-flat-schema" recordFlat),
    ("accept-flat", flatIn, .embedder "accept-flat" flatIn),
    ("wide-flat", wideIn, .embedder "wide-flat" wideIn),
    ("write", wordFn arity 1, .builtin write ⟨0⟩)]

private def readerImports (channel : Channel) : List (String × V1.FuncType × CanonHost engine) :=
  let flat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 ((signatureFor channel).payload true)⟩
  let asyncOpts : CanonOpts engine := { memory := some readerMemory, async_ := true }
  let (read, cancel, close, arity) : ResolvedBuiltin engine × ResolvedBuiltin engine ×
      ResolvedBuiltin engine × Nat := match channel with
    | .stream => (.streamRead element asyncOpts, .streamCancelRead element true, .streamDropReadable element, 3)
    | .future => (.futureRead element asyncOpts, .futureCancelRead element true, .futureDropReadable element, 2)
  [("give-flat", flat, .embedder "give-flat" flat),
    ("read", wordFn arity 1, .builtin read ⟨1⟩),
    ("cancel-read", wordFn 1 1, .builtin cancel ⟨1⟩),
    ("new-set", wordFn 0 1, .builtin .waitableSetNew ⟨1⟩),
    ("join", wordFn 2 0, .builtin .waitableJoin ⟨1⟩),
    ("poll", wordFn 2 1, .builtin (.waitableSetPoll readerMemory) ⟨1⟩),
    ("close-set", wordFn 1 0, .builtin .waitableSetDrop ⟨1⟩),
    ("rep", wordFn 1 1, .builtin (.resourceRep resource .i32) ⟨1⟩),
    ("drop-own", wordFn 1 0, .builtin (.resourceDrop resource) ⟨1⟩),
    ("close-reader", wordFn 1 0, .builtin close ⟨1⟩)]

private def indexOf {kind : IndexKind} (index : Nat) : Idx kind := ⟨Fin.ofNat _ index⟩
private def word (value : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 value)
private def storeWord (ptr value : Nat) : List Instr :=
  [word ptr, word value, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def instantiateWith (initial : Store (CanonHost engine))
    (entries : List (String × V1.FuncType × CanonHost engine))
    (setup : String → List Instr) (locals : List (String × V1.FuncType × List Instr) := []) :
    Option (Store (CanonHost engine) × ModuleInst) := do
  let (store, addrs) := entries.foldl (fun (store, addresses) (_, type, code) =>
    let (next, addr) := SingleThreaded.allocHost store type code
    (next, addresses ++ [ExternAddr.func addr])) (initial, [])
  let names := entries.map (·.1)
  let wrapper := fun index =>
    let params := (entries[index]?.map (·.2.1.params.length)).getD 0
    let instructions := (names[index]?.map setup).getD []
    (⟨indexOf index, [], instructions ++ (List.range params).map (fun param => .localGet (indexOf param)) ++
      [.call (indexOf index)]⟩ : Func)
  let module_ : Module := {
    types := entries.map (·.2.1.toCoreRec) ++ locals.map (·.2.1.toCoreRec)
    imports := names.zipIdx |>.map fun (name, index) => ⟨"host", name, .func (indexOf index)⟩
    memories := [⟨.i32, ⟨1, none⟩⟩]
    funcs := (List.range names.length).map wrapper ++ locals.zipIdx.map (fun ((_, _, body), index) =>
      ⟨indexOf (names.length + index), [], body⟩)
    exports := (names ++ locals.map (·.1)).zipIdx.map fun (name, index) =>
      ⟨name, .func (indexOf (index + names.length))⟩ }
  let (store, inst, none) ← Core3.prepareE? store module_ addrs | none
  return (store, inst)

private def canonicalCallee (channel : Channel) : ComponentCall.Callee (signatureFor channel) :=
  ⟨"accept-canonical", ⟨0⟩, ⟨0⟩, 0, .i32, .utf8, true, true⟩

private def instantiate (channel : Channel := .stream) (canonical : Bool := false) :
    Option (Store (CanonHost engine) × ModuleInst) := do
  let c := canonicalCallee channel
  let entries := imports channel ++ if canonical then [(c.name, c.coreType, c.lowered ⟨0⟩)] else []
  let (store, inst) ← instantiateWith {} entries fun name => match name with
    | "accept-node" => storeWord 32 1 ++ storeWord 36 2 ++ storeWord 40 1 ++ storeWord 44 3
    | "accept-canonical" => storeWord 24 0 ++ storeWord 28 0 ++ storeWord 32 1 ++ storeWord 36 2 ++
        storeWord 40 1 ++ storeWord 44 3
    | "write" => storeWord 64 257 ++ storeWord 68 3
    | _ => []
  guard (inst.mems == [(0 : Nat)])
  return (store, inst)

private def exportAddr (inst : ModuleInst) (name : String) : Option engine.FuncAddr := do
  let (_, .func address) ← (Core3.instExports inst).find? (·.1 == name) | none
  return address

private def session (inst : ModuleInst) (useTuple : Bool) : Session grow signature (Ret engine) := do
  let run (name : String) (args : List Nat) (expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr (args.map i32Flat)) != expected) (.internal s!"unexpected result: {name}")
  let refused := [i32Flat 1, i32Flat 0]
  let success (value : Nat) := [i32Flat 0, i32Flat value]
  let tag := if useTuple then 1 else 0
  let give := if useTuple then "give-payload" else "give-record"
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-channel" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "accept-node" [tag, 32, 0, 0] (success 1)
  run "bad-memory" [1, 0] refused
  run "bad-realloc" [1, 0] refused
  run give [1, 0] (success 0)
  run give [1, 0] refused
  run "rep" [3] [i32Flat 77]
  run "rep" [2] [i32Flat 77]
  run "accept-node" [tag, 0, 0, 0] (success 2)
  run give [1, 0] refused
  run give [2, 16] (success 0)
  run "close-reader" [3] []
  run "close-writer" [4] []
  return .unit

private def ready {sig : Signature} : HostReady (HostState sig) := fun _ _ => false

private def setup (useTuple : Bool) : Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate
  let .ok lower := Binding.giveRecord "give-record" ⟨0⟩ inst 0 .i32 .utf8 | none
  let .ok lowerPayload := Binding.givePayload "give-payload" ⟨0⟩ inst 0 .i32 .utf8 | none
  let badRealloc : Except Issue (Binding signature) :=
    if useTuple then Binding.givePayload "bad-realloc" ⟨0⟩ inst 0 .i32 .utf8 (some 0)
    else Binding.giveRecord "bad-realloc" ⟨0⟩ inst 0 .i32 .utf8 (some 0)
  let .ok badRealloc := badRealloc | none
  let badMemory : RecordDestination := ⟨99, .i32, none, .utf8⟩
  let bindings := [Binding.accept contract inst 0, lower, lowerPayload, badRealloc,
    ⟨"bad-memory", ⟨0⟩, if useTuple then .givePayload badMemory else .giveRecord badMemory⟩]
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩ }],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return (bindings, {
    store := reference, host := {}, conts := [none]
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session inst useTuple)] })

private def run {sig : Signature} (bindings : List (Binding sig)) (config : Machine.Config engine (HostState sig)) :=
  Machine.run ready (specDispatch ready (host bindings)) (core3Exec grow) Machine.Oracle.first 1500 config

private theorem run_sound (bindings : List (Binding signature)) (config : Machine.Config engine (HostState signature)) :
    Machine.Steps .deterministic ready (specDispatch ready (host bindings)) config
      (run bindings config).labels (run bindings config).config :=
  Machine.run_sound ready (specDispatch ready (host bindings)) (core3Exec grow) Machine.Oracle.first 1500 config

private def regression (useTuple : Bool) : Bool :=
  match setup useTuple with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    let spent := if useTuple then Issue.lowerPayload (.claims .unclaimed) else .lowerRecord (.claims .unclaimed)
    let tag := if useTuple then 1 else 0
    let name := if useTuple then "give-payload" else "give-record"
    let accept := fun ticket ptr => Event.entered ticket "accept-node"
      (Endpoints.Core.Scheduled.acceptType contract) [i32Flat tag, i32Flat ptr, i32Flat 0, i32Flat 0]
    let give := fun ticket name handle ptr => Event.entered ticket name (wordFn 2 2) [i32Flat handle, i32Flat ptr]
    result.outcome == .resolved && writer.held.isEmpty && writer.endpoints.isEmpty &&
    writer.accepted.length == 2 &&
    ((writer.accepted.flatMap rootReceipts).map receiptId == [⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩]) &&
    (bytes.extract 0 16).data == #[3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0] &&
    (bytes.extract 16 32).data == #[1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0] &&
    result.config.host.transcript == [accept 0 32, .published 0 1, .returned 0 1,
      give 1 "bad-memory" 1 0, .refused 1 .badLoweringMemory,
      give 2 "bad-realloc" 1 0, .refused 2 .badLoweringRealloc,
      give 3 name 1 0, .returned 3 0,
      give 4 name 1 0, .refused 4 spent,
      accept 5 0, .published 5 2, .returned 5 2,
      give 6 name 1 0, .refused 6 spent,
      give 7 name 2 16, .returned 7 0] &&
    result.config.host.refusals == [spent, spent, .badLoweringRealloc, .badLoweringMemory]

#guard regression false
#guard regression true

private def flatSession (inst : ModuleInst) : Session grow signature (Ret engine) := do
  let run (name : String) (args : List Nat) (expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr (args.map i32Flat)) != expected) (.internal s!"unexpected result: {name}")
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-channel" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "accept-node" [1, 32, 0, 0] ([0, 1].map i32Flat)
  run "wrong-flat-schema" [1] ([1, 0, 0, 0, 0].map i32Flat)
  run "give-flat" [1] ([0, 3, 2, 1, 1].map i32Flat)
  run "give-flat" [1] ([1, 0, 0, 0, 0].map i32Flat)
  run "rep" [3] [i32Flat 77]
  run "rep" [2] [i32Flat 77]
  run "close-reader" [1] []
  run "close-writer" [4] []
  return .unit

private def flatSetup : Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate
  let .ok flat := Binding.giveFlat "give-flat" ⟨0⟩ inst 0 .i32 .utf8 (signature.payload true) | none
  let .ok wrong := Binding.giveFlat "wrong-flat-schema" ⟨0⟩ inst 0 .i32 .utf8 (signature.payload false) | none
  let (_, initial) ← setup true
  let reference := { initial.store with core := store }
  return ([Binding.accept contract inst 0, flat, wrong],
    { initial with store := reference, ctl := [Machine.Activation.ofProg (some ⟨0⟩) (flatSession inst)] })

private def flatRegression : Bool :=
  match flatSetup with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let enter := fun ticket name type args => Event.entered ticket name type (args.map i32Flat)
    let flat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload true)⟩
    let spent := Issue.lowerPayload (.claims .unclaimed)
    result.outcome == .resolved && writer.accepted.length == 1 &&
    writer.held.isEmpty && writer.endpoints.isEmpty &&
    result.config.host.transcript == [enter 0 "accept-node" (Endpoints.Core.Scheduled.acceptType contract) [1, 32, 0, 0],
      .published 0 1, .returned 0 1, enter 1 "wrong-flat-schema" flat [1], .refused 1 .wrongPayloadType,
      enter 2 "give-flat" flat [1], .returnedFlat 2 ([3, 2, 1, 1].map i32Flat),
      enter 3 "give-flat" flat [1], .refused 3 spent]

#guard flatRegression

#guard (flatCompletion 0 [.int .i64, .float .f32] (.error .badSelection)).2 ==
  [i32Flat 1, .int .i64 0, .float .f32 0]

#guard (flatCompletion 0 [.int .i64, .float .f32] (.ok [i32Flat 3, .float .f32 7])).1 ==
  .refused 0 .wrongResultType

private def flatInputSession (inst : ModuleInst) : Session grow signature (Ret engine) := do
  let run (name : String) (args expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr args) != expected) (.internal s!"unexpected result: {name}")
  let refused := [i32Flat 1, i32Flat 0]
  let inputs := [1, 2, 1, 3].map i32Flat
  run "new-own" [i32Flat 77] [i32Flat 1]
  run "new-own" [i32Flat 77] [i32Flat 2]
  run "new-channel" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "wide-flat" (.int .i64 0 :: .int .i64 0 :: inputs) refused
  run "accept-flat" (i32Flat 0 :: i32Flat 1 :: inputs) refused
  run "accept-flat" (i32Flat 0 :: i32Flat 0 :: inputs) [i32Flat 0, i32Flat 1]
  run "give-flat" [i32Flat 1] ([0, 3, 2, 1, 1].map i32Flat)
  run "rep" [i32Flat 3] [i32Flat 77]
  run "rep" [i32Flat 2] [i32Flat 77]
  run "close-reader" [i32Flat 1] []
  run "close-writer" [i32Flat 4] []
  return .unit

private def flatInputSetup (program : ModuleInst → Session grow signature (Ret engine)) :
    Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate
  let .ok input := Binding.acceptFlat ("host", "accept-flat") ⟨0⟩ inst 0 { passing := .flat } true | none
  let .ok wide := Binding.acceptFlat ("host", "wide-flat") ⟨0⟩ inst 0 { address := .i64, passing := .flat } true | none
  let .ok output := Binding.giveFlat "give-flat" ⟨0⟩ inst 0 .i32 .utf8 (signature.payload true) | none
  let (_, initial) ← setup true
  let reference := { initial.store with core := store }
  return ([input, wide, output],
    { initial with store := reference, ctl := [Machine.Activation.ofProg (some ⟨0⟩) (program inst)] })

private def flatInputRegression : Bool :=
  match flatInputSetup flatInputSession with
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let width := Issue.accept (.boundary (.boundary (.addressWidth .i32)))
    let arity := Issue.accept (.boundary (.boundary .badArity))
    let args := [1, 2, 1, 3].map i32Flat
    let input := wordFn 6 2
    let wide : V1.FuncType := ⟨.int .i64 :: .int .i64 :: ABI.flatten .i64 (signature.payload true), input.results⟩
    let output : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload true)⟩
    result.outcome == .resolved && writer.accepted.length == 1 && writer.held.isEmpty &&
    writer.endpoints.isEmpty && result.config.host.refusals == [arity, width] &&
    result.config.host.transcript == [
      .entered 0 "wide-flat" wide (.int .i64 0 :: .int .i64 0 :: args), .refused 0 width,
      .entered 1 "accept-flat" input (i32Flat 0 :: i32Flat 1 :: args), .refused 1 arity,
      .entered 2 "accept-flat" input (i32Flat 0 :: i32Flat 0 :: args), .published 2 1, .returned 2 1,
      .entered 3 "give-flat" output [i32Flat 1], .returnedFlat 3 ([3, 2, 1, 1].map i32Flat)]
  | none => false

#guard flatInputRegression

private def expect {sig : Signature} (inst : ModuleInst) (name : String) (args : List Nat) (expected : List FlatValue) :
    Session grow sig Unit := do
  let some addr := exportAddr inst name | internal s!"missing Core export {name}"
  let result ← callCore addr (args.map i32Flat)
  trapIf (result != expected) (.internal s!"unexpected result: {name} {args} got {repr result}")

private def inlineElement : Channel → Option Stored.TypeOf
  | .future => some (.prim .string)
  | .stream => some (.list (.prim .u8))

private def inlineSignature (channel : Channel) : Signature :=
  let endpoint := match channel with
    | .future => WIT.ValType.future (inlineElement channel)
    | .stream => WIT.ValType.stream (inlineElement channel)
  ⟨Unit, fun _ => .tuple [.prim .u8, endpoint], fun _ => .fixed 0⟩

private def inlineEndpointSession (channel : Channel) (inst : ModuleInst) :
    Session grow (inlineSignature channel) (Ret engine) := do
  let invoke := expect (sig := inlineSignature channel) inst
  invoke "new-channel" [] [.int .i64 (BitVec.ofNat 64 (packEnds 1 2))]
  invoke "accept-flat" [0, 0, 37, 1] ([0, 1].map i32Flat)
  invoke "give-flat" [1] ([0, 37, 1].map i32Flat)
  invoke "accept-flat" [0, 0, 37, 1] ([0, 2].map i32Flat)
  invoke "give-payload" [2, 16] ([0, 0].map i32Flat)
  invoke "close-reader" [1] []
  return .unit

private def inlineEndpointSetup (channel : Channel) :
    Option (List (Binding (inlineSignature channel)) × Machine.Config engine (HostState (inlineSignature channel))) := do
  let elem := inlineElement channel
  let (create, closeReader) : ResolvedBuiltin engine × ResolvedBuiltin engine :=
    match channel with
    | .future => (.futureNew elem, .futureDropReadable elem)
    | .stream => (.streamNew elem, .streamDropReadable elem)
  let entries := [("new-channel", ⟨[], [.int .i64]⟩, .builtin create ⟨0⟩),
    ("accept-flat", wordFn 4 2, .embedder "accept-flat" (wordFn 4 2)),
    ("give-flat", wordFn 1 3, .embedder "give-flat" (wordFn 1 3)),
    ("give-payload", wordFn 2 2, .embedder "give-payload" (wordFn 2 2)),
    ("close-reader", wordFn 1 0, .builtin closeReader ⟨0⟩)]
  let (store, inst) ← instantiateWith {} entries (fun _ => [])
  let sig := inlineSignature channel
  let .ok input := Binding.acceptFlat (sig := sig) ("host", "accept-flat") ⟨0⟩ inst 0 { passing := .flat } () | none
  let .ok flat := Binding.giveFlat (sig := sig) "give-flat" ⟨0⟩ inst 0 .i32 .utf8 (sig.payload ()) | none
  let .ok memory := Binding.givePayload (sig := sig) "give-payload" ⟨0⟩ inst 0 .i32 .utf8 | none
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return ([input, flat, memory], {
    store := reference, host := {}, conts := [none]
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (inlineEndpointSession channel inst)] })

private def inlineEndpointRegression (channel : Channel) : Bool :=
  match inlineEndpointSetup channel with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let state := result.config.host
    result.outcome == .resolved && state.refusals.isEmpty && state.publications == [(0, 1), (2, 2)] &&
    state.writer.held.isEmpty && state.writer.endpoints.isEmpty &&
    (result.config.store.core.mems[0]?.map fun mem => (mem.bytes.extract 16 24).data) ==
      some #[37, 0, 0, 0, 1, 0, 0, 0] &&
    (result.config.store.insts[0]?.map fun inst => [inst.handles.get? 1, inst.handles.get? 2]) ==
      some [none, some (.waitable (.end_ ⟨1⟩))]

#guard inlineEndpointRegression .future
#guard inlineEndpointRegression .stream

@[expose] public def reallocSignature : Signature :=
  ⟨Unit, fun _ => .tuple [.own resource, .list (.record [("code", .prim .u32)]), .prim .u32], fun _ => .fixed 0⟩

private def reallocContract : Endpoints.Core.Contract reallocSignature :=
  ⟨0, ("host", "accept-node"), fun tag => if tag == 0 then some () else none, {}, ⟨0⟩⟩

private def reallocBody (invalid : Bool) (flatResults : Nat := 5) : List Instr :=
  [word 1, .memoryGrow ⟨0⟩, .drop, word 208, .localGet ⟨2⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
    word 212, .localGet ⟨3⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
    word 1, .call ⟨2⟩] ++ List.replicate flatResults .drop ++ [word (if invalid then 65537 else 65536)]

private def reallocSession (inst : ModuleInst) (flat : Bool) : Session grow reallocSignature (Ret engine) := do
  let call (name : String) (args expected : List Nat) := do
    let some address := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore address (args.map i32Flat)) != expected.map i32Flat)
      (.internal s!"unexpected result: {name}")
  call "new-own" [77] [1]
  call "accept-node" [0, 32, 0, 0] [0, 1]
  if flat then call "give-flat" [1] [0, 1, 65536, 1, 91]
  else call "give-payload" [1, 0] [0, 0]
  call "rep" [1] [77]
  return .unit

private def reallocInput : List Instr :=
  storeWord 32 1 ++ storeWord 36 64 ++ storeWord 40 1 ++ storeWord 44 91 ++ storeWord 64 77

private def reallocModule (invalid : Bool)
    (extraImports : List (String × V1.FuncType × CanonHost engine) := [])
    (extraLocals : List (String × V1.FuncType × List Instr) := []) :
    Option (List (Binding reallocSignature) × Store (CanonHost engine) × ModuleInst) := do
  let input := Endpoints.Core.Scheduled.acceptType reallocContract
  let entries := [
    ("accept-node", input, CanonHost.embedder "accept-node" input),
    ("give-payload", wordFn 2 2, .embedder "give-payload" (wordFn 2 2)),
    ("give-flat", wordFn 1 5, .embedder "give-flat" (wordFn 1 5)),
    ("new-own", wordFn 1 1, .builtin (.resourceNew resource .i32) ⟨0⟩),
    ("rep", wordFn 1 1, .builtin (.resourceRep resource .i32) ⟨0⟩)] ++ extraImports
  let (store, inst) ← instantiateWith {} entries (fun name =>
    if name == "accept-node" then reallocInput else [])
    ([("realloc", wordFn 4 1, reallocBody invalid)] ++ extraLocals)
  let reallocIndex := some (entries.length * 2)
  let .ok memory := Binding.givePayload "give-payload" ⟨0⟩ inst 0 .i32 .utf8 reallocIndex | none
  let .ok flatBinding := Binding.giveFlat (sig := reallocSignature) "give-flat" ⟨0⟩ inst 0 .i32 .utf8
    (reallocSignature.payload ()) reallocIndex | none
  return ([Binding.accept reallocContract inst 0, memory, flatBinding], store, inst)

private def reallocSetup (flat invalid : Bool) :
    Option (List (Binding reallocSignature) × Machine.Config engine (HostState reallocSignature)) := do
  let (bindings, store, inst) ← reallocModule invalid
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩ }],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return (bindings, {
    store := reference, host := {}, conts := [none],
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (reallocSession inst flat)] })

private def expectWords (expected : List Nat) : List Instr :=
  expected.reverse.flatMap fun value => [word value, .intRelOp .i32 .eq, .if_ .empty [] [.unreachable]]

private def liftedReallocBody (flat : Bool) : List Instr :=
  [word 77, .call ⟨3⟩] ++ expectWords [1] ++ reallocInput ++
  [word 0, word 32, word 0, word 0, .call ⟨0⟩] ++ expectWords [0, 1] ++
  (if flat then [word 1, .call ⟨2⟩] ++ expectWords [0, 1, 65536, 1, 91]
    else [word 1, word 0, .call ⟨1⟩] ++ expectWords [0, 0]) ++
  [word 1, .call ⟨4⟩] ++ expectWords [77] ++ storeWord 216 91 ++
  [.call ⟨5⟩] ++ expectWords [0] ++ [word 91, .call ⟨6⟩]

private def liftedReallocSetup (flat invalid : Bool) :
    Option (List (Binding reallocSignature) × Machine.Config engine (HostState reallocSignature)) := do
  let opts : CanonOpts engine := { async_ := true }
  let result : Option (WIT.ClosedType RtId) := some (.prim .u32)
  let (bindings, core, inst) ← reallocModule invalid
    [("yield", wordFn 0 1, .builtin .threadYield ⟨0⟩),
     ("task-return", wordFn 1 0, .builtin (.taskReturn result opts) ⟨0⟩)]
    [("run", wordFn 0 0, liftedReallocBody flat)]
  let address ← exportAddr inst "run"
  let store : CStore engine := { CStore.empty with
    core, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩ }],
    funcs := [.lifted address ⟨[], result, true⟩ opts ⟨0⟩] }
  return (bindings, { store, host := {} })

private def runLiftedRealloc (bindings : List (Binding reallocSignature))
    (start : Machine.Config engine (HostState reallocSignature)) :=
  Machine.runTopCall ready (specDispatch ready (host bindings)) (core3Exec grow)
    Machine.Oracle.first 1500 ⟨0⟩ ⟨0⟩ [] start

theorem lifted_realloc_replay_sound (bindings : List (Binding reallocSignature))
    (start : Machine.Config engine (HostState reallocSignature)) {replay}
    (ran : runLiftedRealloc bindings start = some replay) :
    ∃ tail, replay.labels = .host (.invoke ⟨0⟩ ⟨0⟩ []) :: tail ∧
      Machine.Steps .deterministic ready (specDispatch ready (host bindings)) start
        replay.labels replay.config ∧ (⟨0⟩, ⟨0⟩, []) ∈ replay.config.pending :=
  Machine.runTopCall_sound ready (specDispatch ready (host bindings)) (core3Exec grow) Machine.Oracle.first ran

private def liftedReallocParked (flat : Bool) : Bool := Id.run do
  let some (bindings, start) := liftedReallocSetup flat false | return false
  let some (_, invoked) := Machine.hostStep? ready (.invoke ⟨0⟩ ⟨0⟩ []) start | return false
  let paused := run bindings invoked
  let state := paused.config
  let returned := if flat then .returnedFlat 1 ([1, 65536, 1, 91].map i32Flat) else Event.returned 1 0
  return paused.outcome == .running && state.hostReady && state.conts.any Option.isSome &&
    (state.cancel? ⟨0⟩).isSome && (state.result? ⟨0⟩).isNone &&
    state.host.publications == [(0, 1)] && state.host.transcript.contains returned

private def liftedReallocRegression (flat invalid : Bool) : Bool := Id.run do
  let some (bindings, start) := liftedReallocSetup flat invalid | return false
  let some replay := runLiftedRealloc bindings start | return false
  let final := replay.config
  let bytes := (final.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
  let ticked := replay.labels.any (· matches .host .tick)
  let returned := if flat then .returnedFlat 1 ([1, 65536, 1, 91].map i32Flat) else Event.returned 1 0
  let returnRecorded := final.host.transcript.contains returned
  let outcome := if invalid then
      replay.outcome == .trap && replay.labels.any (· matches .trap .unalignedPointer) &&
        (final.result? ⟨0⟩).isNone && !ticked && !returnRecorded
    else replay.outcome == .resolved && final.result? ⟨0⟩ == some (some [.int .u32 91]) &&
      ticked && returnRecorded
  return outcome && final.host.publications == [(0, 1)] && final.host.refusals == [.wrongContext] &&
    final.host.writer.held.isEmpty &&
    ((final.store.inst? ⟨0⟩).bind (·.handles.get? 1)) == some (.resource ⟨1⟩) &&
    bytes.size == 131072 && (bytes.extract 208 216).data == #[4, 0, 0, 0, 4, 0, 0, 0] &&
    (bytes.extract 216 220).data == (if invalid then #[0, 0, 0, 0] else #[91, 0, 0, 0]) &&
    (bytes.extract 65536 65540).data == (if invalid then #[0, 0, 0, 0] else #[77, 0, 0, 0])

#guard liftedReallocParked false
#guard liftedReallocParked true
#guard liftedReallocRegression false false
#guard liftedReallocRegression true false
#guard liftedReallocRegression false true
#guard liftedReallocRegression true true

private def reallocRegression (flat invalid : Bool) : Bool :=
  match reallocSetup flat invalid with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let state := result.config.host
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    let completion := if invalid then [] else if flat then [.returnedFlat 1 ([1, 65536, 1, 91].map i32Flat)]
      else [.returned 1 0]
    let outer := if flat then Event.entered 1 "give-flat" (wordFn 1 5) [i32Flat 1]
      else .entered 1 "give-payload" (wordFn 2 2) ([1, 0].map i32Flat)
    let journal := [Event.entered 0 "accept-node" (Endpoints.Core.Scheduled.acceptType reallocContract)
        ([0, 32, 0, 0].map i32Flat), .published 0 1, .returned 0 1, outer,
      .entered 2 "give-flat" (wordFn 1 5) [i32Flat 1], .refused 2 .wrongContext] ++ completion
    let descriptor := if flat then #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else
      if invalid then #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else #[1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]
    result.outcome == (if invalid then .trap else .resolved) &&
    result.labels.any (· matches .trap .unalignedPointer) == invalid &&
    state.transcript == journal && state.writer.held.isEmpty &&
    ((result.config.store.inst? ⟨0⟩).bind (·.handles.get? 1)) == some (.resource ⟨1⟩) &&
    bytes.size == 131072 && (bytes.extract 208 216).data == #[4, 0, 0, 0, 4, 0, 0, 0] &&
    (bytes.extract 0 12).data == descriptor && (bytes.extract 65536 65540).data ==
      (if invalid then #[0, 0, 0, 0] else #[77, 0, 0, 0]) &&
    (bytes.extract 12 16).data == (if flat || invalid then #[0, 0, 0, 0] else #[91, 0, 0, 0])

#guard reallocRegression false false
#guard reallocRegression true false
#guard reallocRegression false true
#guard reallocRegression true true

@[expose] public def scalarListSignature : Signature :=
  ⟨Unit, fun _ => .list (.prim .u32), fun _ => .fixed 0⟩

private def localListSignature (nested : Bool) : Signature :=
  ⟨Unit, fun _ => if nested then .list (.tuple [.prim .u8, .record [("code", .prim .u32)]])
    else scalarListSignature.payload (), fun _ => .fixed 0⟩

private def localListContract (nested : Bool) : Endpoints.Core.Contract (localListSignature nested) :=
  ⟨0, ("host", "accept-node"), fun tag => if tag == 0 then some () else none, {}, ⟨0⟩⟩

private def localListSession (inst : ModuleInst) (flat nested : Bool) : Session grow (localListSignature nested) (Ret engine) := do
  let call (name : String) (args expected : List Nat) := do
    let some address := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore address (args.map i32Flat)) != expected.map i32Flat)
      (.internal s!"unexpected result: {name}")
  call "accept-node" [0, 32, 0, 0] [0, 1]
  if flat then call "give-flat" [1] [0, 65536, 3]
  else call "give-payload" [1, 0] [0, 0]
  return .unit

private def localListSetup (flat invalid nested : Bool) :
    Option (List (Binding (localListSignature nested)) × Machine.Config engine (HostState (localListSignature nested))) := do
  let input := Endpoints.Core.Scheduled.acceptType (localListContract nested)
  let entries := [
    ("accept-node", input, CanonHost.embedder "accept-node" input),
    ("give-payload", wordFn 2 2, .embedder "give-payload" (wordFn 2 2)),
    ("give-flat", wordFn 1 3, .embedder "give-flat" (wordFn 1 3))]
  let (store, inst) ← instantiateWith {} entries (fun name =>
    if name != "accept-node" then [] else storeWord 32 64 ++ storeWord 36 3 ++
      if nested then storeWord 64 65317 ++ storeWord 68 256 ++ storeWord 72 5 ++
        storeWord 76 512 ++ storeWord 80 17 ++ storeWord 84 1024
      else storeWord 64 37 ++ storeWord 68 256 ++ storeWord 72 5) [("realloc", wordFn 4 1, reallocBody invalid 3)]
  let reallocIndex := some (entries.length * 2)
  let .ok memory := Binding.givePayload "give-payload" ⟨0⟩ inst 0 .i32 .utf8 reallocIndex | none
  let .ok flatBinding := Binding.giveFlat (sig := localListSignature nested) "give-flat" ⟨0⟩ inst 0 .i32 .utf8
    ((localListSignature nested).payload ()) reallocIndex | none
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}], tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return ([Binding.accept (localListContract nested) inst 0, memory, flatBinding], {
    store := reference, host := {}, conts := [none],
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (localListSession inst flat nested)] })

private def localListRegression (flat invalid : Bool) (nested : Bool := false) : Bool :=
  match localListSetup flat invalid nested with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    let completion := if invalid then [] else if flat then [.returnedFlat 1 ([65536, 3].map i32Flat)] else [.returned 1 0]
    let outer := if flat then Event.entered 1 "give-flat" (wordFn 1 3) [i32Flat 1]
      else .entered 1 "give-payload" (wordFn 2 2) ([1, 0].map i32Flat)
    let journal := [Event.entered 0 "accept-node" (Endpoints.Core.Scheduled.acceptType (localListContract nested))
        ([0, 32, 0, 0].map i32Flat), .published 0 1, .returned 0 1, outer,
      .entered 2 "give-flat" (wordFn 1 3) [i32Flat 1], .refused 2 .wrongContext] ++ completion
    let extent := if nested then 24 else 12
    let cells := if invalid then Array.replicate extent 0
      else if nested then #[37, 0, 0, 0, 0, 1, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 17, 0, 0, 0, 0, 4, 0, 0]
      else #[37, 0, 0, 0, 0, 1, 0, 0, 5, 0, 0, 0]
    result.outcome == (if invalid then .trap else .resolved) &&
    result.labels.any (· matches .trap .unalignedPointer) == invalid &&
    result.config.host.transcript == journal &&
    bytes.size == 131072 && (bytes.extract 208 216).data == #[4, 0, 0, 0, UInt8.ofNat extent, 0, 0, 0] &&
    (bytes.extract 0 8).data == (if flat || invalid then #[0, 0, 0, 0, 0, 0, 0, 0] else #[0, 0, 1, 0, 3, 0, 0, 0]) &&
    (bytes.extract 65536 (65536 + extent)).data == cells

#guard localListRegression false false
#guard localListRegression true false
#guard localListRegression false true
#guard localListRegression true true
#guard localListRegression false false true
#guard localListRegression true false true
private def bindingTrapArgs : List Nat := [0, 0, 1, 0, 0, 0]

private def bindingTrapSession (inst : ModuleInst) : Session grow signature (Ret engine) := do
  expect inst "new-own" [77] [i32Flat 1]
  expect inst "accept-flat" bindingTrapArgs []
  return .unit

private def bindingTrapRegression (issue : Issue) : Bool := Id.run do
  let some (binding :: _, config) := flatInputSetup bindingTrapSession | return false
  let bindings := match issue with
    | .unlinkedImport => []
    | .wrongType => [{ binding with action := .giveOwner resource }]
    | .ambiguousBinding => [binding, binding]
    | _ => []
  let result := run bindings config
  let traps := result.labels.filterMap fun | .trap reason => some reason | _ => none
  let reached := result.config
  return result.outcome == .trap && traps == [.hostTrap "invalid mixed acceptor import binding"] &&
    reached.host.writer.accepted.isEmpty && reached.host.writer.held.isEmpty &&
    reached.host.publications.isEmpty && reached.host.refusals == [issue] &&
    reached.host.transcript == [.entered 0 "accept-flat" (wordFn 6 2) (bindingTrapArgs.map i32Flat),
      .bindingTrap 0 issue] &&
    (reached.store.insts[0]?.bind fun inst => inst.handles.get? 1) == some (.resource ⟨0⟩)

#guard bindingTrapRegression .unlinkedImport
#guard bindingTrapRegression .wrongType
#guard bindingTrapRegression .ambiguousBinding

private def channelArgs (channel : Channel) (slot address : Nat) : List Nat :=
  match channel with | .stream => [slot, address, 1] | .future => [slot, address]

private def copyResult (channel : Channel) (result : CopyResult) (count : Nat) : Nat :=
  match channel with | .stream => packStreamCopyResult result count | .future => futureCopyPayload result

private def flatChannelWriter (channel : Channel) (inst : ModuleInst) (canonical : Bool) :
    Session grow (signatureFor channel) (Ret engine) := do
  let run := expect (sig := signatureFor channel) inst
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-channel" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  if canonical then
    run "accept-canonical" [24, 112] [i32Flat AsyncLowerResult.returned.pack]
    let result ← readMem { inst := ⟨0⟩, opts := { memory := some coreMemory } } 112 8
    trapIf (result.data != #[0, 0, 0, 0, 1, 0, 0, 0]) (.internal "unexpected canonical accept result")
  else run "accept-flat" [0, 0, 1, 2, 1, 3] ([0, 1].map i32Flat)
  run "new-own" [97] [i32Flat 3]
  block (some ⟨1⟩)
  run "write" (channelArgs channel 4 64) [i32Flat (copyResult channel .completed 1)]
  resumeThread ⟨1⟩
  run "close-writer" [4] []
  resumeThread ⟨1⟩
  return .unit

private def flatChannelReader (channel : Channel) (inst : ModuleInst) (stale : Bool) :
    Session grow (signatureFor channel) (Ret engine) := do
  let run := expect (sig := signatureFor channel) inst
  let complete := copyResult channel .completed 1
  let args := channelArgs channel 3 80
  let cx : LiftLowerContext engine := { inst := ⟨1⟩, opts := { memory := some readerMemory } }
  run "give-flat" [1] ([0, 1, 2, 1, 3].map i32Flat)
  run "new-set" [] [i32Flat 4]
  run "join" [3, 4] []
  run "read" args [i32Flat blocked]
  run "poll" [4, 96] [i32Flat EventCode.none.toNat]
  run "cancel-read" [3] [i32Flat (copyResult channel .cancelled 0)]
  trapIf ((← readMem cx 80 8).data != #[0, 0, 0, 0, 0, 0, 0, 0]) (.internal "cancel wrote memory")
  run "read" args [i32Flat blocked]
  block (some ⟨0⟩)
  run "poll" [4, 96] [i32Flat (channel.endKind .read).eventCode.toNat]
  trapIf ((← readMem cx 96 8).data != (u32Bytes 3).data ++ (u32Bytes complete).data)
    (.internal "unexpected endpoint readiness record")
  run "rep" [5] [i32Flat 97]
  run "rep" [1] [i32Flat 77]
  run "rep" [2] [i32Flat 77]
  run "drop-own" [5] []
  run "drop-own" [1] []
  run "drop-own" [2] []
  block none
  if channel == .stream then run "read" args [i32Flat (copyResult channel .dropped 0)]
  run "join" [3, 0] []
  run "close-reader" [3] []
  run "close-set" [4] []
  if stale then run "read" args []
  return .unit

private def flatChannelSetup (channel : Channel) (stale canonical : Bool) :
    Option (List (Binding (signatureFor channel)) × Machine.Config engine (HostState (signatureFor channel))) := do
  let signature := signatureFor channel
  let (store, writer) ← instantiate channel canonical
  let (store, reader) ← instantiateWith store (readerImports channel) (fun _ => [])
  guard (reader.mems == [(1 : Nat)])
  let .ok input := Binding.acceptFlat ("host", "accept-flat") ⟨0⟩ writer 0 { passing := .flat } true | none
  let .ok output := Binding.giveFlat "give-flat" ⟨1⟩ reader 0 .i32 .utf8 (signature.payload true) | none
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}, {}], resourceTypes := [{ impl := some ⟨0⟩ }],
    funcs := if canonical then [.host (canonicalCallee channel).funcType ⟨0⟩] else [],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ },
      { ft := ⟨[], none, false⟩, opts := {}, inst := ⟨1⟩, caller := ⟨1⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }, { status := .blocked, task := ⟨1⟩ }] }
  let config : Machine.Config engine (HostState signature) := {
    store := reference
    host := {}
    conts := [none, some (Machine.Activation.ofProg (some ⟨1⟩) (flatChannelReader channel reader stale))],
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (flatChannelWriter channel writer canonical)] }
  return ([input, output], config)

private def flatChannelRegression (channel : Channel) (stale : Bool) (canonical : Bool := false) : Bool :=
  match flatChannelSetup channel stale canonical with
  | some (bindings, config) =>
    let implementation := if canonical then ComponentCall.hostWithComponent bindings [canonicalCallee channel]
      else host bindings
    let result := Machine.run ready (specDispatch ready implementation) (core3Exec grow) Machine.Oracle.first 5000 config
    let writer := result.config.host.writer
    let traps := result.labels.filterMap fun | .trap reason => some reason | _ => none
    result.outcome == (if stale then .trap else .resolved) &&
    traps == (if stale then [.unknownHandle 3] else []) &&
    writer.accepted.length == 1 && writer.held.isEmpty && writer.endpoints.isEmpty &&
    result.config.host.refusals.isEmpty && result.config.host.publications == [(0, 1)] &&
    (result.config.store.core.mems[1]?.map fun mem => (mem.bytes.extract 80 88).data) ==
      some #[1, 1, 0, 0, 5, 0, 0, 0] &&
    result.config.store.insts.map (fun inst => [1, 2, 3, 4, 5].map inst.handles.get?) ==
      [[none, none, none, none, none], [none, none, none, none, none]]
  | none => false

#guard flatChannelRegression .stream false
#guard flatChannelRegression .stream true
#guard flatChannelRegression .future false
#guard flatChannelRegression .future true
#guard flatChannelRegression .stream false true
#guard flatChannelRegression .stream true true
#guard flatChannelRegression .future false true
#guard flatChannelRegression .future true true

private def flatBindingIssue {sig : Signature} (result : Except Issue (Binding sig)) : Option Issue :=
  match result with
  | .ok _ => none
  | .error issue => some issue

private def inactiveBorrow : Signature :=
  ⟨Unit, fun _ => .list (.option (.borrow resource)), fun _ => .fixed 0⟩

#guard flatBindingIssue (Binding.acceptFlat (sig := inactiveBorrow) ("host", "bad") ⟨0⟩ {} 0
  { passing := .flat } ()) ==
  some (.accept (.claims (.lift (.schema .storedBorrow))))

private def endpointBorrow : Signature :=
  ⟨Unit, fun _ => .future (some (.list (.option (.borrow resource)))), fun _ => .fixed 0⟩

#guard flatBindingIssue (Binding.giveFlat (sig := endpointBorrow) "bad" ⟨0⟩ {} 0 .i32 .utf8
  (endpointBorrow.payload ())) == some (.lowerPayload (.preflight (.schema .storedBorrow)))

#guard flatBindingIssue (Binding.acceptFlat (sig := signature) ("host", "bad") ⟨0⟩ {} 0
  { passing := .flat, asynchronous := true } true) == some (.accept (.boundary (.boundary .asyncCall)))

#guard flatBindingIssue (Binding.acceptFlat (sig := signature) ("host", "bad") ⟨0⟩ {} 0 {} true) ==
  some .wrongPassingMode

#guard Endpoints.Core.checkChildren signature true (2 ^ 32 - 2) 0 0 == .ok ()
#guard Endpoints.Core.checkChildren signature true (2 ^ 32 - 1) 0 0 == .error .exhaustedHandles

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.RecordExamples
