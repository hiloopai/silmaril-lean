module

public import Silmaril.Wasi.Versions.WitImport.KSplit.Defs

@[expose] public section

/-!
# WIT documents and binary packages without doc comments

`Document.erase` sets every `docs` field of a parsed WIT document to `{}` (fields, cases,
labels, resource functions, type definitions, functions, interfaces, world externs, worlds,
packages); `Binary.Package.erase` and `Binary.Env.erase` set every `docs` field of an
elaborated package to `none`. Nothing else changes.

`Silmaril.Wasi.Versions.WitImport.KErase.Thms` proves that the importer commutes with them
(`Elab.elaborate` on the erased universe is the erased elaboration) and that the signature
tables, drops and resolved packages do not read doc comments, so a file whose erased parse is
the parse of its text without doc comments gives the same tables.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Wit

/-! ## WIT syntax -/

def Field.erase (f : Field) : Field := { f with docs := {} }
def Case.erase (c : Case) : Case := { c with docs := {} }
def Label.erase (l : Label) : Label := { l with docs := {} }
def ResourceFunc.erase (rf : ResourceFunc) : ResourceFunc := { rf with docs := {} }

def TypeDefKind.erase : TypeDefKind → TypeDefKind
  | .alias t => .alias t
  | .record fs => .record (fs.map Field.erase)
  | .variant cs => .variant (cs.map Case.erase)
  | .enum ls => .enum (ls.map Label.erase)
  | .flags ls => .flags (ls.map Label.erase)
  | .resource fns => .resource (fns.map ResourceFunc.erase)

def TypeDef.erase (d : TypeDef) : TypeDef := { d with kind := d.kind.erase, docs := {} }
def FuncDef.erase (f : FuncDef) : FuncDef := { f with docs := {} }

def IfaceItem.erase : IfaceItem → IfaceItem
  | .type d => .type d.erase
  | .use u => .use u
  | .func f => .func f.erase

def Interface.erase (I : Interface) : Interface :=
  { I with items := I.items.map IfaceItem.erase, docs := {} }

def Extern.erase : Extern → Extern
  | .func n f => .func n f
  | .iface n items => .iface n (items.map IfaceItem.erase)
  | .path p => .path p

def WorldExtern.erase (e : WorldExtern) : WorldExtern := { e with ext := e.ext.erase, docs := {} }

def WorldItem.erase : WorldItem → WorldItem
  | .import e => .import e.erase
  | .export e => .export e.erase
  | .use u => .use u
  | .type d => .type d.erase
  | .include i => .include i

def World.erase (W : World) : World := { W with items := W.items.map WorldItem.erase, docs := {} }

def PackageItem.erase : PackageItem → PackageItem
  | .iface I => .iface I.erase
  | .world W => .world W.erase
  | .use u => .use u

def Package.erase (P : Package) : Package :=
  { P with items := P.items.map PackageItem.erase, docs := {} }

def Document.erase (d : Document) : Document :=
  { main := d.main.erase, nested := d.nested.map Package.erase }

def Universe.erase (U : Universe) : Universe := U.map Package.erase

def ScopeItem.erase : ScopeItem → ScopeItem
  | .type d => .type d.erase
  | .use u => .use u

def Src.erase : Src → Src
  | .type d => .type d.erase
  | .use p n => .use p n

/-! ## Binary packages -/

namespace Binary

def Labeled.erase {α : Type} (l : Labeled α) : Labeled α := { l with docs := none }

def TyDefKind.erase : TyDefKind → TyDefKind
  | .record fs => .record (fs.map Labeled.erase)
  | .variant cs => .variant (cs.map Labeled.erase)
  | .enum cs => .enum (cs.map Labeled.erase)
  | .flags fs => .flags (fs.map Labeled.erase)
  | k => k

def TypeDef.erase (d : TypeDef) : TypeDef := { d with kind := d.kind.erase, docs := none }
def Func.erase (f : Func) : Func := { f with docs := none }

def Interface.erase (b : Interface) : Interface :=
  { b with types := b.types.map TypeDef.erase, funcs := b.funcs.map Func.erase, docs := none }

def WorldItem.erase : WorldItem → WorldItem
  | .ifaceRef i _ s => .ifaceRef i none s
  | .ifaceInline n b => .ifaceInline n b.erase
  | .func f => .func f.erase
  | .type t => .type t.erase

def World.erase (w : World) : World :=
  { w with imports := w.imports.map WorldItem.erase, exports := w.exports.map WorldItem.erase,
           docs := none }

def Env.erase (env : Env) : Env := env.map fun x => (x.1, x.2.erase)

def Package.erase (p : Package) : Package :=
  { p with docs := none, interfaces := p.interfaces.map (fun x => (x.1, x.2.erase)),
           worlds := p.worlds.map fun x => (x.1, x.2.erase) }

end Binary

end Silmaril.Wasm.Wit
