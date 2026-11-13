module

public import Silmaril.Wasm.Wit.Binary.Encode.Defs
public import Silmaril.Wasm.Wit.Binary.Decode.Defs

/-!
# The normal form of the binary encoding, and validity

What the item sections of a WIT binary keep of a package is its *normal
form* (`Package.normalize`):

* functions of an interface are reordered resource by resource
  (`sortFuncs`, wit-component's order);
* docs and stability are dropped (they are kept by the `package-docs` custom
  section, `Silmaril.Wasm.Wit.Binary.Docs`), as are the docs of record fields,
  variant cases, enum cases and flags;
* world references to interfaces keep only the interface name.

Comments other than doc comments, the order of `use` statements and other
surface syntax are already gone in the resolved model.

`Package.Valid` collects the conditions under which names survive the
encoding: interface, world and package names parse back from
`ns:pkg/name@version`, function names demangle back, inline interface names
are plain.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

def Labeled.strip {α : Type} (l : Labeled α) : Labeled α := { l with docs := none }

def TyDefKind.strip : TyDefKind → TyDefKind
  | .record fs => .record (fs.map Labeled.strip)
  | .variant cs => .variant (cs.map Labeled.strip)
  | .enum cs => .enum (cs.map Labeled.strip)
  | .flags fs => .flags (fs.map Labeled.strip)
  | k => k

def TypeDef.strip (td : TypeDef) : TypeDef := { name := td.name, kind := td.kind.strip }

def Func.strip (f : Func) : Func := { f with docs := none, stability := .unknown }

/-- The normal form of an interface body. -/
def Interface.normalize (b : Interface) : Interface :=
  { types := b.types.map TypeDef.strip, funcs := (sortFuncs b.types b.funcs).map Func.strip }

def WorldItem.normalize : WorldItem → WorldItem
  | .ifaceRef i _ _ => .ifaceRef i
  | .ifaceInline n b => .ifaceInline n b.normalize
  | .func f => .func f.strip
  | .type t => .type t.strip

def World.normalize (w : World) : World :=
  { imports := w.imports.map WorldItem.normalize, exports := w.exports.map WorldItem.normalize }

/-- The normal form of a package: what its item sections encode. -/
def Package.normalize (p : Package) : Package :=
  { name := p.name,
    interfaces := p.interfaces.map fun (n, b) => (n, b.normalize)
    worlds := p.worlds.map fun (n, w) => (n, w.normalize) }

/-! ## Validity of names -/

/-- Names of interface `i` parse back. -/
def IfaceName.Valid (i : IfaceName) : Prop :=
  ':' ∉ i.pkg.ns.toList ∧ '/' ∉ i.pkg.name.toList ∧ '@' ∉ i.name.toList

/-- A function name demangles back. -/
def Func.Valid (f : Func) : Prop :=
  match f.kind with
  | .freestanding => f.async = false → f.name.toList.head? ≠ some '['
  | .method r | .static r => '.' ∉ r.toList
  | .constructor r => f.name = r ∧ f.async = false

def Interface.Valid (b : Interface) : Prop := ∀ f ∈ b.funcs, f.Valid

def WorldItem.Valid : WorldItem → Prop
  | .ifaceRef i _ _ => i.Valid
  | .ifaceInline n b => ':' ∉ n.toList ∧ b.Valid
  | .func f => f.Valid
  | .type _ => True

def World.Valid (w : World) : Prop :=
  (∀ it ∈ w.imports, it.Valid) ∧ (∀ it ∈ w.exports, it.Valid)

/-- Validity of a package and of the environment it is encoded in. -/
def Package.Valid (p : Package) (deps : Env) : Prop :=
  (p.interfaces ≠ [] ∨ p.worlds ≠ []) ∧
  (∀ nb ∈ p.interfaces, (p.name.iface nb.1).Valid) ∧
  (∀ nw ∈ p.worlds, (p.name.iface nw.1).Valid) ∧
  (∀ ib ∈ p.env deps, ib.1.Valid ∧ ib.2.Valid) ∧
  (∀ nw ∈ p.worlds, nw.2.Valid)

end Silmaril.Wasm.Wit.Binary
