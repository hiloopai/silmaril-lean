module

public import Silmaril.Wasm.JcoTool.WorldMerge.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Perf.CoreDecode.Defs

/-!
# The `cm32p2` naming scheme

wit-component reads the core imports and exports of a module under two naming schemes: the
legacy one (`$root`, `[export]ns:pkg/i@1.2.3`, `[resource-drop]r`, `ns:pkg/i@1.2.3#f`,
`cabi_post_f`, `cabi_realloc`, `memory`, …), which `wasm-jco` reads, and the *standard* one of
the component model's `cm32p2` ABI (`validation.rs`, `Standard`, wasm-tools 1.262.0):

| standard | legacy |
|---|---|
| import module `cm32p2`, name `f` | `$root`, `f` (`r_drop`: `[resource-drop]r`) |
| import module `cm32p2|I`, name `f` | `I'`, `f` (`r_drop`: `[resource-drop]r`) |
| import module `cm32p2|_ex_I`, names `r_drop`, `r_new`, `r_rep` | `[export]I'`, `[resource-drop]r`, … |
| export `cm32p2||f`, `cm32p2||f_post` | `f`, `cabi_post_f` |
| export `cm32p2|I|f`, `cm32p2|I|f_post`, `cm32p2|I|r_dtor` | `I'#f`, `cabi_post_I'#f`, `I'#[dtor]r` |
| export `cm32p2_memory`, `cm32p2_realloc`, `cm32p2_initialize` | `memory`, `cabi_realloc`, `_initialize` |

where `I` is an interface's *canonical* id (the version cut to its semver-compatible part:
`@1`, `@0.2`, `@0.0.3`) or a plain world-item name, and `I'` the id the world gives it.

`normalize` renames a module that uses the standard scheme to the legacy one, from its own
worlds (the `component-type` sections), with silmaril's verified decoder and encoder, the custom
sections appended again unchanged. Only names change: the module's code, types and index spaces
are those of the input, so the component embeds a module with the same behaviour under the
names wit-component would have read. Modules without a `cm32p2` name are returned unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Cm32

open Silmaril.Wasm.Wit.Binary

/-- The semver-compatible part of a version, as `canonicalized_id_of` writes it. -/
def canonVer (v : String) : String :=
  match WorldMerge.parseVer v with
  | some ⟨maj, mi, pa, pre⟩ =>
    if pre ≠ "" then v
    else if maj ≠ 0 then s!"{maj}"
    else if mi ≠ 0 then s!"0.{mi}"
    else s!"0.0.{pa}"
  | none => v

/-- An interface's canonical id. -/
def canonId (i : IfaceName) : String :=
  s!"{i.pkg.ns}:{i.pkg.name}/{i.name}" ++ (i.pkg.version.map (fun v => "@" ++ canonVer v)).getD ""

/-- The canonical ids of the worlds' interfaces, with the ids the worlds give them. -/
def idMap (wfs : List WorldFull) : List (String × String) :=
  wfs.flatMap fun wf => (wf.imports ++ wf.exports).filterMap fun
    | .iface (.inl i) _ => some (canonId i, i.id)
    | _ => none

def mapIface (m : List (String × String)) (s : String) : String := (m.lookup s).getD s

/-- `x_suf` as `x`. -/
def stripSuffix? (suf s : String) : Option String :=
  if s.endsWith suf && s.length > suf.length then some (s.take (s.length - suf.length)).toString
  else none

/-- A name of a function an imported item provides, or of its resources' drops. -/
def importName (n : String) : String :=
  if n.startsWith "[" then n
  else match stripSuffix? "_drop" n with
    | some r => "[resource-drop]" ++ r
    | none => n

/-- A resource intrinsic of an exported interface. -/
def exIntrinsic (n : String) : String :=
  match stripSuffix? "_drop" n, stripSuffix? "_new" n, stripSuffix? "_rep" n with
  | some r, _, _ => "[resource-drop]" ++ r
  | _, some r, _ => "[resource-new]" ++ r
  | _, _, some r => "[resource-rep]" ++ r
  | _, _, _ => n

/-- A core import `(module, name)`, renamed to the legacy scheme. -/
def renameImport (m : List (String × String)) (mod name : String) : String × String :=
  if mod == "cm32p2" then ("$root", importName name)
  else match (mod.dropPrefix? "cm32p2|").map (·.toString) with
    | some rest => match (rest.dropPrefix? "_ex_").map (·.toString) with
      | some k => ("[export]" ++ mapIface m k, exIntrinsic name)
      | none => (mapIface m rest, importName name)
    | none => (mod, name)

/-- A core export, renamed to the legacy scheme. -/
def renameExport (m : List (String × String)) (n : String) : String :=
  if n == "cm32p2_memory" then "memory"
  else if n == "cm32p2_realloc" then "cabi_realloc"
  else if n == "cm32p2_initialize" then "_initialize"
  else match (n.dropPrefix? "cm32p2|").map (·.toString) with
    | some rest => match rest.splitOn "|" with
      | [i, f] =>
        let pre := if i == "" then "" else mapIface m i ++ "#"
        match stripSuffix? "_post" f, stripSuffix? "_dtor" f with
        | some g, _ => "cabi_post_" ++ pre ++ g
        | _, some r => if i == "" then n else pre ++ "[dtor]" ++ r
        | _, _ => pre ++ f
      | _ => n
    | none => n

/-- Whether a module uses the standard scheme. -/
def usesCm32 (m : Silmaril.Wasm.Module) : Bool :=
  m.imports.any (fun i => i.moduleName.startsWith "cm32p2") ||
  m.exports.any (fun e => e.name.startsWith "cm32p2")

/-- **A module in the standard naming scheme, renamed to the legacy one** (unchanged when it
has no `cm32p2` name). Decoded with `Perf.CoreDecode.decodeModule`, equal to silmaril's
`Decode.decodeModule` (`CoreDecode.decodeModule_eq`). -/
def normalize (b : ByteArray) : Except String ByteArray := do
  let m ← match Silmaril.Wasm.Perf.CoreDecode.decodeModule b with
    | .ok m => pure m
    | .error _ => return b
  if !usesCm32 m then return b
  let wfs ← WorldMerge.sectionWorlds b
  let ids := idMap wfs
  let m' : Silmaril.Wasm.Module :=
    { m with imports := m.imports.map (fun i =>
                let (mn, n) := renameImport ids i.moduleName i.name
                { i with moduleName := mn, name := n }),
             exports := m.exports.map fun e => { e with name := renameExport ids e.name } }
  let bs ← match Silmaril.Wasm.Binaryen.Exe.encodeModule? m' with
    | .ok bs => pure (⟨bs.toArray⟩ : ByteArray)
    | .error e => throw s!"cm32p2 names: the renamed module does not encode: {e}"
  let cs ← customSections b
  cs.foldlM (fun acc (n, d) => match customSection n d with
    | some s => pure (acc ++ s)
    | none => throw "cm32p2 names: a custom section is too large") bs

/-- An import `(module, name)` the module has twice. The Component Model forbids duplicate import
names in a component's core modules; wit-component rewrites the module to import each once
(renumbering its functions), which `wasm-jco` does not do: such modules are refused. -/
def dupImportOf (m : Silmaril.Wasm.Module) : Option (String × String) :=
  let ns := m.imports.map fun i => (i.moduleName, i.name)
  (ns.zipIdx.find? fun (n, k) => (ns.take k).contains n).map (·.1)

/-- **The module `wasm-jco new` componentizes**: refused when it imports a name twice, renamed
from the `cm32p2` scheme when it uses it (`normalize`), else unchanged; decoded once. -/
def prepare (b : ByteArray) : Except String ByteArray :=
  match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
  | none => pure b
  | some m =>
    match dupImportOf m with
    | some (mn, n) => throw s!"the module imports {mn} {n} twice (wit-component deduplicates such imports by rewriting the module; not supported)"
    | none => if usesCm32 m then normalize b else pure b

end Silmaril.Wasm.JcoTool.Cm32
