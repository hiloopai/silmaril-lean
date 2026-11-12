module

public import Silmaril.Wasm.Wit.Binary.Custom.Defs
public import Silmaril.Wasm.Component.Wat.Defs
public import Silmaril.Wasm.Wit.Project.Defs
public import Silmaril.Wasm.Wit.Binary.Print.Defs

/-!
# The core of the `wasm-wit` tool

Pure functions behind the subcommands of `wasm-wit` (`tools/wasm-wit`); the
executable only reads files, calls these and writes the results.

| subcommand | function | built on |
|---|---|---|
| `print`   | `printWat`   | `Component.Binary.parse`, `Wat.print` |
| `parse`   | `parseWat`   | `Wat.read`, `Component.Binary.encode` |
| `decode`  | `decode`     | `Wit.Binary.decodePackage`, `decodeEnv` |
| `encode`  | `reencode`   | `decode`, then `Wit.Binary.encodePackage` |
| `check`   | `check`      | `decode`, `Package.Valid`, `NamesUnique`, `reencode` |
| `project` | `projectBytes`, `projectWat` | `Wit.Project.project` |
| `wit`     | `witText`    | `decodePackage`, `Wit.Binary.printPackage` (unverified) |

`print`/`parse` are the component WAT printer and reader (the counterparts of
`wasm-tools print`/`wasm-tools parse`); `encode` re-encodes the WIT package a
binary holds (wit-component's `encode` on the decoded package and the
interfaces the binary shows); `check` decides the hypotheses of the round-trip
theorems of `Silmaril.Wasm.Wit.Binary` on the decoded package and compares the
re-encoded bytes with the input. The theorems are in
`Silmaril.Wasm.Wit.Tool.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Tool

open Silmaril.Wasm.Component
open Silmaril.Wasm.Wit.Binary (Package Env decodePackage decodeEnv encodePackage)

/-! ## Decidability of the hypotheses of the round-trip theorems -/

section Decide
open Silmaril.Wasm.Wit.Binary

instance (i : IfaceName) : Decidable i.Valid := by
  unfold IfaceName.Valid; infer_instance

instance (f : Func) : Decidable f.Valid := by
  unfold Func.Valid; split <;> infer_instance

instance (b : Interface) : Decidable b.Valid := by
  unfold Interface.Valid; infer_instance

instance (it : WorldItem) : Decidable it.Valid := by
  unfold WorldItem.Valid; split <;> infer_instance

instance (w : World) : Decidable w.Valid := by
  unfold World.Valid; infer_instance

instance (p : Package) (deps : Env) : Decidable (p.Valid deps) := by
  unfold Package.Valid; infer_instance

instance (k : TyDefKind) : Decidable k.LabelsUnique := by
  unfold TyDefKind.LabelsUnique; split <;> infer_instance

instance (b : Interface) : Decidable b.NamesUnique := by
  unfold Interface.NamesUnique; infer_instance

instance (w : World) : Decidable w.NamesUnique := by
  unfold World.NamesUnique
  refine @instDecidableAnd _ _ _ (@instDecidableAnd _ _ _ (@instDecidableAnd _ _ _ ?_))
  refine @List.decidableBAll _ _ (fun it => ?_) _
  split <;> infer_instance

instance (p : Package) : Decidable p.NamesUnique := by
  unfold Package.NamesUnique; infer_instance

end Decide

/-! ## Component WAT -/

/-- `wasm-wit print`: component bytes to component WAT. -/
def printWat (b : ByteArray) : Except String String :=
  match Binary.parse b with
  | .ok c => .ok (Wat.print c)
  | .error _ => .error "malformed component"

/-- `wasm-wit parse`: component WAT to component bytes. -/
def parseWat (t : String) : Except String ByteArray :=
  match Wat.read t with
  | none => .error "not component WAT this reader accepts"
  | some c => match Binary.encode c with
    | some b => .ok b
    | none => .error "a number or size exceeds 2^32"

/-! ## WIT packages -/

/-- A decoded WIT binary: the package and the interfaces the binary shows. -/
structure Decoded where
  pkg : Package
  env : Env

/-- `wasm-wit decode`: the WIT package of a binary. -/
def decode (b : ByteArray) : Except String Decoded := do
  let p ← decodePackage b
  let env ← decodeEnv b
  pure ⟨p, env⟩

/-- `wasm-wit encode`: the bytes wit-component writes for the decoded package. -/
def reencode (b : ByteArray) : Except String ByteArray := do
  let d ← decode b
  encodePackage d.env d.pkg

/-- `wasm-wit wit`: the WIT text of the main package of a binary
(`Binary.printPackage`, unverified, compared with `wasm-tools component wit`). -/
def witText (b : ByteArray) : Except String String := do
  let p ← decodePackage b
  pure (Binary.printPackage p)

/-- The result of `wasm-wit check` on a WIT binary. -/
structure Report where
  /-- The decoded package. -/
  decoded : Decoded
  /-- `Package.Valid` holds for the package in the environment the binary shows. -/
  valid : Bool
  /-- `Package.NamesUnique` holds. -/
  unique : Bool
  /-- The package is in wit-component's function order (`p.canon = p`). -/
  canonical : Bool
  /-- The re-encoded bytes, if the encoder succeeds. -/
  reencoded : Option ByteArray
  /-- The re-encoded bytes are the input. -/
  fixpoint : Bool

/-- `wasm-wit check`: decode, decide the hypotheses of the round-trip theorems,
re-encode and compare. -/
def check (b : ByteArray) : Except String Report := do
  let d ← decode b
  let r := encodePackage d.env d.pkg
  let r? := match r with | .ok b' => some b' | .error _ => none
  pure { decoded := d
         valid := decide (d.pkg.Valid d.env)
         unique := decide d.pkg.NamesUnique
         canonical := decide (d.pkg.canon = d.pkg)
         reencoded := r?
         fixpoint := r? == some b }

/-- All checks passed: the bytes are the encoding of a valid package with
distinct names, in wit-component's order, in the environment they show. -/
def Report.ok (r : Report) : Bool := r.valid && r.unique && r.canonical && r.fixpoint

/-! ## Projection -/

/-- `wasm-wit project` on bytes: the world (component type) of a component. -/
def projectBytes (b : ByteArray) : Except String Project.WorldType :=
  match Binary.parse b with
  | .ok c => match Project.project c with
    | some w => .ok w
    | none => .error "the component is outside the domain of the projection"
  | .error _ => .error "malformed component"

/-- `wasm-wit project` on component WAT. -/
def projectWat (t : String) : Except String Project.WorldType :=
  match Wat.read t with
  | some c => match Project.project c with
    | some w => .ok w
    | none => .error "the component is outside the domain of the projection"
  | none => .error "not component WAT this reader accepts"

/-- A world as a component holding its component type, for printing. -/
def worldAst (w : Project.WorldType) : Binary.Ast := .mk [.types [.component w]]

end Silmaril.Wasm.Wit.Tool
