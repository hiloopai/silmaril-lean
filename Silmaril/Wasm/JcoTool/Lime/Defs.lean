module

public import Silmaril.Wasm.JcoTool.Tool.Defs
public import Silmaril.Wasm.LimeCompile.Direct.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# `wasm-jco new --lime`: Lime-preserving components

Lime1 is silmaril's Wasm 1.0-based feature set (`docs/projects/wasm-components.md`, Lime against 3.0). With
`--lime`, `wasm-jco` first runs the input module through the direct 3.0 → Lime compiler
(`Silmaril.Wasm.LimeCompile.Direct.compile`, proved correct: `compile_correct`, export-equivalent
for valid modules) and re-encodes the result with silmaril's verified encoder, then builds the
component (thin wrapper or `--adaptor`) from those bytes, and finally checks that **every**
core module of the output (the input, the adaptor `adaptorLime`, the `shim` and `fixup`
helpers) decodes and compiles to Lime1 (`isLime`). A module outside Lime1 is rejected with a
message.

Theorems: `Silmaril.Wasm.JcoTool.Lime.Thms` (`newLime_correct`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Lime

open Silmaril.Wasm.Wit.Binary (World)

/-- The bytes decode to a module the Lime compiler accepts. -/
def isLime (b : ByteArray) : Bool :=
  match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
  | some m => (Silmaril.Wasm.LimeCompile.Direct.compile m).isSome
  | none => false

/-- The input module through the Lime compiler, re-encoded. -/
def toLime (core : ByteArray) : Except String ByteArray :=
  match Silmaril.Wasm.Perf.CoreDecode.decodeF core with
  | none => .error "the core module is outside silmaril's decoder"
  | some m => match Silmaril.Wasm.LimeCompile.Direct.compile m with
    | none => .error "the core module is outside Lime1 (the 3.0 → Lime compiler rejects it)"
    | some l => (fun bs => ⟨bs.toArray⟩) <$> Silmaril.Wasm.Binaryen.Exe.encodeModule? l.toCore

/-- The thin wrapper, or adaptor mode with the allocator `alloc`. -/
def build (core : ByteArray) (w : World) : Option String → Except String Tool.Out
  | some alloc => Tool.newAdaptor core w alloc
  | none => Tool.newWith core w

/-- **`wasm-jco new --lime`** (thin wrapper, or adaptor mode with `alloc`). -/
def newLime (core : ByteArray) (w : World) (adaptor : Option String) : Except String Tool.Out := do
  let core' ← toLime core
  let o ← build core' w adaptor
  New.require (o.cores.all isLime)
    s!"output core modules outside Lime1 (0 = the input): {(o.cores.zipIdx.filter (!isLime ·.1)).map (·.2)}"
  pure { o with summary := "lime: every core module of the output is in Lime1" :: o.summary }

end Silmaril.Wasm.JcoTool.Lime
