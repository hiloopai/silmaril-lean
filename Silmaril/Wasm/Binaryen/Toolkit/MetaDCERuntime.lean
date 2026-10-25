module

public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCEGraph
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binaryen.Pass.RUME

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.MetaDCE

/-- A lowering-preserving structured lift; no optimizer is run here. -/
def tree (m : Module) : BModule :=
  ⟨m, m.funcs.map (Declaration.Func.mapBody liftInstrs)⟩

def project (names : List String) (m : Module) : Module :=
  {m with exports := m.exports.filter fun e => names.contains e.name}

/-- First semantic subset: closed numeric-signature function modules, with
arbitrary base-profile code (including direct calls, loops and traps). -/
def supported (m : Module) : Bool :=
  m.imports.isEmpty && m.tags.isEmpty && m.globals.isEmpty && m.memories.isEmpty &&
    m.tables.isEmpty && m.data.isEmpty && m.elems.isEmpty && m.start.isNone &&
    (tree m).inProfileBase && numSigs (tree m)

/-- Total pass-facing view with identity fallback outside the supported family.
The command-line tool retains explicit rejection of unsupported modules. -/
def optimize (names : List String) (m : Module) : Module :=
  if supported m then
    match Validation.validate? (project names m) with
    | some _ => (rume (tree (project names m))).lower
    | none => m
  else m

def checkBindings (graph : Graph) (source : Module) : Except String Unit := do
  for n in graph do
    if let some name := n.exportName then
      unless source.exports.any (fun e => e.name == name) do
        throw s!"metadce: graph export {name} does not exist in the module"

structure Artifact where
  graph : Graph
  live : List String
  source : Module
  projected : Module
  result : Module
  bytes : ByteArray

/-- External roots select exports; the existing real Wasm reachability then
removes unreachable function bodies and renumbers direct calls. Graph imports
reject: no external back-edge is silently omitted from this closed subset. -/
def eliminateBytes (graphText : String) (input : ByteArray) : Except String Artifact := do
  let graph ← parseGraph graphText
  let live ← match solve graph with
    | some live => pure live
    | none => throw "metadce: graph closure check failed"
  let source ← (Binary.Core.Decode.decodeModule input).mapError ("metadce: " ++ ·)
  match Validation.validate? source with
  | none => throw "metadce: source validation failed"
  | some _ => pure ()
  unless supported source do
    throw "metadce: unsupported module; expected a closed numeric-signature function-only base-profile module"
  checkBindings graph source
  let projected := project (selected graph live) source
  match Validation.validate? projected with
  | none => throw "metadce: projected module validation failed"
  | some _ => pure ()
  let result := (rume (tree projected)).lower
  match Validation.validate? result with
  | none => throw "metadce: output validation failed"
  | some _ => pure ()
  let encoded ← Exe.encodeModule? result
  pure ⟨graph, live, source, projected, result, ⟨encoded.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit.MetaDCE
