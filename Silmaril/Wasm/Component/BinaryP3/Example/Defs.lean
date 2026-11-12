module

public import Silmaril.Wasm.Component.BinaryP3.Check.Defs
public meta import Silmaril.Wasm.Component.BinaryP3.Check.Defs

/-!
# Async built-ins: byte-level tests

`allWasmTools` is the canonical-function section that `wasm-tools 1.262.0` (`parse`, then
`dump`) writes for one `(core func (canon …))` of every built-in it supports, copied byte by
byte from its `dump` output (the source `.wat` is
`tests/wasm-p3-binary/all-builtins.wat`); `specOnly` adds the remaining built-ins,
assembled by hand from `Binary.md` at `d095e2f` (`wasm-tools` writes the same bytes for the
first four, see `tests/wasm-p3-binary/more-builtins.wat`; for the shared-everything
`thread.spawn-ref`, `thread.spawn-indirect` and `thread.available-parallelism` it writes no
`sh?` byte, an older encoding, which this parser rejects). The checks are executed by
`#guard`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3.Example

open Silmaril.Wasm.Component.Binary (CanonOpt ValType PrimValType CoreValType)

/-- A component with one canonical-function section holding `n` entries `body`. -/
def withCanons (n : UInt8) (body : List UInt8) : ByteArray :=
  ⟨(Binary.preambleBytes ++ [0x08, (body.length + 1).toUInt8, n] ++ body).toArray⟩

/-- The section bytes of `wasm-tools dump` (one line per built-in). -/
def allWasmToolsBody : List UInt8 := [
  0x24,
  0x25,
  0x09, 0x00, 0x79, 0x01, 0x03, 0x00,
  0x09, 0x01, 0x00, 0x00,
  0x05,
  0x0a, 0x7f, 0x00,
  0x0b, 0x7f, 0x00,
  0x06, 0x00,
  0x06, 0x01,
  0x0d,
  0x0e, 0x00,
  0x0f, 0x00, 0x01, 0x03, 0x00,
  0x0f, 0x00, 0x02, 0x06, 0x03, 0x00,
  0x10, 0x00, 0x01, 0x03, 0x00,
  0x11, 0x00, 0x00,
  0x12, 0x00, 0x01,
  0x13, 0x00,
  0x14, 0x00,
  0x15, 0x01,
  0x16, 0x01, 0x01, 0x03, 0x00,
  0x17, 0x01, 0x01, 0x03, 0x00,
  0x18, 0x01, 0x00,
  0x19, 0x01, 0x01,
  0x1a, 0x01,
  0x1b, 0x01,
  0x1c, 0x01, 0x03, 0x00,
  0x1d, 0x02, 0x03, 0x00, 0x04, 0x00,
  0x1e,
  0x1f,
  0x20, 0x00, 0x00,
  0x21, 0x00, 0x00,
  0x22,
  0x23,
  0x0c, 0x00,
  0x26,
  0x27, 0x00, 0x00,
  0x29, 0x00,
  0x28,
  0x2a, 0x00,
  0x2b, 0x00]

def allWasmTools : ByteArray := withCanons 40 allWasmToolsBody

/-- What `wasm-tools dump` prints for the same entries. -/
def allWasmToolsAst : List Canon := [
  .backpressureInc, .backpressureDec,
  .taskReturn (some (.prim .u32)) [.memory 0], .taskReturn none [],
  .taskCancel, .contextGet .i32 0, .contextSet .i32 0,
  .subtaskCancel false, .subtaskCancel true, .subtaskDrop,
  .streamNew 0, .streamRead 0 [.memory 0], .streamRead 0 [.async, .memory 0],
  .streamWrite 0 [.memory 0], .streamCancelRead 0 false, .streamCancelWrite 0 true,
  .streamDropReadable 0, .streamDropWritable 0,
  .futureNew 1, .futureRead 1 [.memory 0], .futureWrite 1 [.memory 0],
  .futureCancelRead 1 false, .futureCancelWrite 1 true,
  .futureDropReadable 1, .futureDropWritable 1,
  .errorContextNew [.memory 0], .errorContextDebugMessage [.memory 0, .realloc 0],
  .errorContextDrop,
  .waitableSetNew, .waitableSetWait 0, .waitableSetPoll 0, .waitableSetDrop, .waitableJoin,
  .threadYield, .threadIndex, .threadNewIndirect 0 0, .threadSuspend, .threadResumeLater,
  .threadSuspendThenResume, .threadYieldThenResume]

#guard (parse allWasmTools).toOption.map Ast.canons == some allWasmToolsAst
#guard (encode (.mk [.canons allWasmToolsAst])).map (·.data) == some allWasmTools.data
-- The old parser stops at the first async built-in (`0x24`).
#guard (Binary.parse allWasmTools).toOption.isNone

/-- The other built-ins, from `Binary.md` at `d095e2f`. -/
def specOnlyBody : List UInt8 := [
  0x2c, 0x00,
  0x2d, 0x00,
  0x2e, 0x05,
  0x2f, 0x86, 0x01,
  0x40, 0x01, 0x07,
  0x41, 0x00, 0x07, 0x08,
  0x42, 0x01]

def specOnlyAst : List Canon := [
  .threadSuspendThenPromote, .threadYieldThenPromote, .streamForward 5, .futureForward 134,
  .threadSpawnRef true 7, .threadSpawnIndirect false 7 8, .threadAvailableParallelism true]

#guard (parse (withCanons 7 specOnlyBody)).toOption.map Ast.canons == some specOnlyAst
#guard (encode (.mk [.canons specOnlyAst])).map (·.data) == some (withCanons 7 specOnlyBody).data

/-- Every constructor once, through the encoder and back. -/
def everyCanon : List Canon := [
  .lift 3 [.utf16, .memory 0, .realloc 1, .postReturn 2] 4, .lower 5 [.async, .callback 9],
  .resourceNew 1, .resourceDrop 2, .resourceRep 3] ++ allWasmToolsAst ++ specOnlyAst ++ [
  .taskReturn (some (.idx 300)) [.utf8, .latin1utf16], .contextGet .i64 1, .contextSet .i32 1,
  .streamForward 0, .futureForward 0]

#guard ((encode (.mk [.canons everyCanon])).bind fun b => (parse b).toOption).map Ast.canons ==
  some everyCanon

/-! Rejections: an unassigned tag, a missing `0x00`, a bad `async?`, a bad `sh?`. -/

#guard (parse (withCanons 1 [0x07])).toOption.isNone
#guard (parse (withCanons 1 [0x29, 0x01])).toOption.isNone
#guard (parse (withCanons 1 [0x06, 0x02])).toOption.isNone
#guard (parse (withCanons 1 [0x42, 0x02])).toOption.isNone
#guard (parse (withCanons 1 [0x20, 0x01, 0x00])).toOption.isNone
-- `wasm-tools` 1.262.0's `thread.available_parallelism` and `thread.spawn-ref 0` (no `sh?`).
#guard (parse (withCanons 1 [0x42])).toOption.isNone
#guard (parse (withCanons 1 [0x40, 0x00])).toOption.isNone

/-! The report of `component-check` on the `wasm-tools` section. -/

#guard ((Check.report allWasmTools).take 8).eraseIdx 1 ==
  ["parse ok", "v0-agrees n/a", "reencode same", "core-modules 0 decoded 0",
   "outer-alias-sorts ok", "attributes ok", "canons 40"]
#guard ((Check.report allWasmTools)[1]!).startsWith "v0 err"

end Silmaril.Wasm.Component.BinaryP3.Example
