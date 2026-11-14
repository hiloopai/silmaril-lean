module

public import Silmaril.Machine.Link.Defs

/-! # ABI-tagged static linking

Every export (defined global) and import (undefined global) of every object
carries an ABI/convention tag, and link-time ABI compatibility is an explicit,
checked condition in front of the imported linker:

* `Interface Tag`: the tags of one object's exports and imports. `checkAbi`
  requires it to annotate exactly that object's defined and undefined global
  names, once each;
* `Policy Tag`: `compatible importTag exportTag`, a list of declared `Thunk`s
  (an import with tag `ti` may bind an export with tag `te` only if
  `compatible ti te` or a thunk `⟨name, ti, te⟩` is declared) and the tags of
  absolute (`externals`) symbols;
* `linkAbi = guard (checkAbi … && externalsTag …) *> link …`: cross-ABI links
  without a declared thunk, and absolute symbols without a tag in
  `policy.externals`, are rejected before any layout or relocation work.

`Tag` is a parameter so an ABI-as-institution development can instantiate it with its
own signatures (and `compatible` with the existence of a morphism). `Conv` is a
small default instance whose `sysv64` is the default tag. A declared thunk is
only a link-time permission here; the adapter code and its contract obligations
belong to the TU-contract layer (DESIGN.md WP-L4).
-/

@[expose] public section

namespace Silmaril.Machine.Link.Abi

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link

/-- A small default convention vocabulary. -/
inductive Conv where
  /-- System V AMD64 psABI (`Silmaril.Machine.SystemV.Abi`). -/
  | sysv64
  /-- Microsoft x64. -/
  | ms64
  /-- A data object: no calling convention, only an address. -/
  | data
  /-- A named private convention, e.g. an inferred `.isra`/`.constprop` one. -/
  | custom (name : String)
  deriving DecidableEq, Repr

instance : Inhabited Conv := ⟨.sysv64⟩

/-- One object's ABI interface: a tag for each export and each import. -/
structure Interface (Tag : Type) where
  exports : List (NameBytes × Tag) := []
  imports : List (NameBytes × Tag) := []
  deriving Repr

/-- A declared adapter: import `name` with `importTag` may bind an export with
`exportTag`. -/
structure Thunk (Tag : Type) where
  name : NameBytes
  importTag : Tag
  exportTag : Tag
  deriving DecidableEq, Repr

structure Policy (Tag : Type) where
  compatible : Tag → Tag → Bool
  thunks : List (Thunk Tag) := []
  /-- Tags of absolute symbols supplied to `link` (e.g. linker-defined). -/
  externals : List (NameBytes × Tag) := []

variable {Tag : Type} [DecidableEq Tag]

/-- Only identical tags are compatible; no thunks, no externals. -/
def Policy.exact : Policy Tag := { compatible := fun a b => decide (a = b) }

/-- Global names defined in the object (`STB_GLOBAL`, section index ≠ 0), as in
`Silmaril.Formats.ELF.Link.globalDefinitions`. -/
def definedGlobals (object : ObjectFile) : List NameBytes :=
  (object.symbols.filter fun symbol =>
    symbol.binding == 1 && symbol.raw.sectionIndex != 0).map ObjectSymbol.name

/-- Named global references the object leaves undefined. -/
def undefinedGlobals (object : ObjectFile) : List NameBytes :=
  (object.symbols.filter fun symbol =>
    symbol.binding == 1 && symbol.raw.sectionIndex == 0 && symbol.name != []).map
    ObjectSymbol.name

/-- `entries` tags exactly `names`, each once. -/
def tags (names : List NameBytes) (entries : List (NameBytes × Tag)) : Bool :=
  names.all (fun name => entries.any (·.1 == name)) &&
    entries.all (fun entry => names.contains entry.1) &&
    decide (entries.map Prod.fst).Nodup

def Interface.annotates (iface : Interface Tag) (object : ObjectFile) : Bool :=
  tags (definedGlobals object) iface.exports && tags (undefinedGlobals object) iface.imports

def Policy.accepts (policy : Policy Tag) (name : NameBytes) (importTag exportTag : Tag) :
    Bool :=
  policy.compatible importTag exportTag ||
    policy.thunks.contains ⟨name, importTag, exportTag⟩

/-- Every tag a reference to `name` could bind to: exports of any object and
absolute symbols. -/
def candidates (policy : Policy Tag) (ifaces : List (Interface Tag)) (name : NameBytes) :
    List Tag :=
  ifaces.flatMap (fun iface => (iface.exports.filter (·.1 == name)).map Prod.snd) ++
    (policy.externals.filter (·.1 == name)).map Prod.snd

def importOk (policy : Policy Tag) (ifaces : List (Interface Tag)) (name : NameBytes)
    (importTag : Tag) : Bool :=
  (candidates policy ifaces name).all (policy.accepts name importTag)

/-- The link-time ABI check: complete annotation and compatible bindings. -/
def checkAbi (policy : Policy Tag) (objects : List ObjectFile) (ifaces : List (Interface Tag)) :
    Bool :=
  ifaces.length == objects.length &&
    (objects.zip ifaces).all (fun pair => pair.2.annotates pair.1) &&
    ifaces.all (fun iface => iface.imports.all fun entry => importOk policy ifaces entry.1 entry.2)

/-- Every absolute symbol supplied to `link` has a tag in `policy.externals`.
Without this an import could bind an untagged absolute symbol unchecked. -/
def externalsTag (policy : Policy Tag) (absolute : AbsoluteSymbols) : Bool :=
  absolute.all fun entry => policy.externals.any (·.1 == entry.1)

/-- The imported linker behind the ABI check (and the absolute-symbol tag
check). -/
def linkAbi (accepts : Header → Bool) (relocate : Relocator) (policy : Policy Tag)
    (objects : List ObjectFile) (ifaces : List (Interface Tag)) (layout : Layout)
    (absolute : AbsoluteSymbols := []) : Option (List LinkedSection) := do
  guard (checkAbi policy objects ifaces && externalsTag policy absolute)
  link accepts relocate objects layout absolute

/-- Semantic reading of `checkAbi`: every undefined global of object `i` has an
import tag `ti`, and for every object `j` defining that name (and every
absolute symbol of that name) the export tag `te` is accepted for `ti`. -/
def AbiSound (policy : Policy Tag) (objects : List ObjectFile) (ifaces : List (Interface Tag)) :
    Prop :=
  ∀ (i : Nat) (object : ObjectFile) (iface : Interface Tag), objects[i]? = some object → ifaces[i]? = some iface →
    ∀ name ∈ undefinedGlobals object, ∃ importTag, (name, importTag) ∈ iface.imports ∧
      (∀ (j : Nat) (object' : ObjectFile) (iface' : Interface Tag), objects[j]? = some object' → ifaces[j]? = some iface' →
        name ∈ definedGlobals object' → ∃ exportTag, (name, exportTag) ∈ iface'.exports ∧
          policy.accepts name importTag exportTag = true) ∧
      (∀ exportTag, (name, exportTag) ∈ policy.externals →
        policy.accepts name importTag exportTag = true)

end Silmaril.Machine.Link.Abi
