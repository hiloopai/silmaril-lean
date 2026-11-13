module

public import Silmaril.Wasm.Wit.Binary.Normal.Defs

/-!
# The `package-docs` custom section

wit-parser keeps docs and stability (`@since`, `@unstable`, `@deprecated`) of
a package in a custom section named `package-docs` (wit-parser `0.263.0`,
`src/metadata.rs`): a version byte `0x01` followed by the compact JSON
(serde_json) of `PackageMetadata`. This module writes that JSON exactly
(`Package.docsJson`, `docsSection`) and reads it back into a package
(`injectDocs`).

The JSON is a fragment: strings and objects only, written without spaces,
escaped as serde_json does (`\"`, `\\`, `\b`, `\f`, `\n`, `\r`, `\t`, other
control characters as `\u00xx`, everything else verbatim). The reader
(`JVal.parse`) accepts this fragment (with any `\uXXXX` escape below
`0x10000`). Absent fields and empty maps are omitted, as serde does with its
`skip_serializing_if`; maps are in item order. The section bytes are decoded
with `String.fromUTF8Lossy` (wit-parser rejects invalid UTF-8; the encoder
never writes it).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

/-! ## A JSON fragment -/

/-- JSON strings and objects. -/
inductive JVal where
  | str (s : String)
  | obj (fs : List (String × JVal))
  deriving Repr, Inhabited

/-- A lowercase hexadecimal digit. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- serde_json's escape of one character. -/
def escChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c = '\n' then ['\\', 'n']
  else if c = '\r' then ['\\', 'r']
  else if c = '\t' then ['\\', 't']
  else if c = '\x08' then ['\\', 'b']
  else if c = '\x0c' then ['\\', 'f']
  else if c.toNat < 0x20 then ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

def quoteChars (s : List Char) : List Char := '"' :: (s.flatMap escChar ++ ['"'])

mutual
def JVal.print : JVal → List Char
  | .str s => quoteChars s.toList
  | .obj fs => '{' :: (JVal.printMembers fs ++ ['}'])

/-- Members separated by commas. -/
def JVal.printMembers : List (String × JVal) → List Char
  | [] => []
  | (k, v) :: rest => quoteChars k.toList ++ ':' :: (v.print ++ JVal.printRest rest)

/-- The members after the first, each after a comma. -/
def JVal.printRest : List (String × JVal) → List Char
  | [] => []
  | (k, v) :: rest => ',' :: (quoteChars k.toList ++ ':' :: (v.print ++ JVal.printRest rest))
end

/-- The value of a hexadecimal digit. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- The character of a two-character escape `\e`. -/
def unesc (e : Char) : Option Char :=
  if e = '"' then some '"' else if e = '\\' then some '\\' else if e = '/' then some '/'
  else if e = 'n' then some '\n' else if e = 'r' then some '\r' else if e = 't' then some '\t'
  else if e = 'b' then some '\x08' else if e = 'f' then some '\x0c' else none

/-- The body of a string after its opening quote: its characters and the
input after the closing quote. -/
def unquote : List Char → Option (List Char × List Char)
  | [] => none
  | c :: r =>
    if c = '"' then some ([], r)
    else if c = '\\' then
      match r with
      | [] => none
      | e :: r1 =>
        if e = 'u' then
          match r1 with
          | a :: b :: c1 :: d :: r2 => do
            let n := ((← hexVal a) * 16 + (← hexVal b)) * 256 + (← hexVal c1) * 16 + (← hexVal d)
            let (s, r3) ← unquote r2
            pure (Char.ofNat n :: s, r3)
          | _ => none
        else do
          let x ← unesc e
          let (s, r2) ← unquote r1
          pure (x :: s, r2)
    else do
      let (s, r1) ← unquote r
      pure (c :: s, r1)

mutual
/-- A value, with `fuel` bounding the nesting. -/
def JVal.parseAux : Nat → List Char → Option (JVal × List Char)
  | 0, _ => none
  | _ + 1, '"' :: r => (unquote r).map fun (s, r) => (.str (String.ofList s), r)
  | _ + 1, '{' :: '}' :: r => some (.obj [], r)
  | n + 1, '{' :: r => (JVal.parseMembers n r).map fun (fs, r) => (.obj fs, r)
  | _ + 1, _ => none

/-- Members `"k":v` separated by commas, then `}`. -/
def JVal.parseMembers : Nat → List Char → Option (List (String × JVal) × List Char)
  | 0, _ => none
  | n + 1, '"' :: r => do
    let (k, r) ← unquote r
    let r ← match r with | ':' :: r => some r | _ => none
    let (v, r) ← JVal.parseAux n r
    match r with
    | '}' :: r => pure ([(String.ofList k, v)], r)
    | ',' :: r => do
      let (fs, r) ← JVal.parseMembers n r
      pure ((String.ofList k, v) :: fs, r)
    | _ => none
  | _ + 1, _ => none
end

/-- Parse a whole JSON text of the fragment. -/
def JVal.parse (cs : List Char) : Option JVal :=
  match JVal.parseAux (cs.length + 1) cs with
  | some (v, []) => some v
  | _ => none

def JVal.get (k : String) : JVal → Option JVal
  | .obj fs => (fs.find? (·.1 = k)).map (·.2)
  | .str _ => none

def JVal.getStr (k : String) (v : JVal) : Option String :=
  match v.get k with
  | some (.str s) => some s
  | _ => none

/-! ## Metadata as JSON -/

/-- `key: value` if present. -/
def jopt (k : String) : Option JVal → List (String × JVal)
  | some v => [(k, v)]
  | none => []

/-- A map, omitted when empty. -/
def jmap (k : String) : List (String × JVal) → List (String × JVal)
  | [] => []
  | fs => [(k, .obj fs)]

/-- A non-empty object, or nothing. -/
def jobj : List (String × JVal) → Option JVal
  | [] => none
  | fs => some (.obj fs)

def jstr (s : Option String) : Option JVal := s.map .str

def Stability.json : Stability → Option JVal
  | .unknown => none
  | .stable v d => some (.obj [("stable", .obj ([("since", .str v)] ++ jopt "deprecated" (jstr d)))])
  | .unstable f d => some (.obj [("unstable", .obj ([("feature", .str f)] ++ jopt "deprecated" (jstr d)))])

def Stability.ofJson (v : Option JVal) : Stability :=
  match v with
  | some j => match j.get "stable", j.get "unstable" with
    | some s, _ => match s.getStr "since" with
      | some since => .stable since (s.getStr "deprecated")
      | none => .unknown
    | none, some u => match u.getStr "feature" with
      | some f => .unstable f (u.getStr "deprecated")
      | none => .unknown
    | none, none => .unknown
  | none => .unknown

/-- `{docs?, stability?}`, the common head of every metadata object. -/
def headJson (docs : Option String) (st : Stability) : List (String × JVal) :=
  jopt "docs" (jstr docs) ++ jopt "stability" st.json

def labelDocs {α : Type} (ls : List (Labeled α)) : List (String × JVal) :=
  ls.filterMap fun l => l.docs.map fun d => (l.name, .str d)

def TyDefKind.items : TyDefKind → List (String × JVal)
  | .record fs => labelDocs fs
  | .variant cs => labelDocs cs
  | .enum cs => labelDocs cs
  | .flags fs => labelDocs fs
  | _ => []

/-- `TypeMetadata`. -/
def TypeDef.meta (td : TypeDef) : Option JVal :=
  jobj (headJson td.docs td.stability ++ jmap "items" td.kind.items)

/-- `FunctionMetadata::DocsAndStability`. -/
def Func.meta (f : Func) : Option JVal := jobj (headJson f.docs f.stability)

/-- The entries `name: meta` whose metadata is not empty. -/
def metaMap {α : Type} (name : α → String) (m : α → Option JVal) (xs : List α) : List (String × JVal) :=
  xs.filterMap fun x => (m x).map (name x, ·)

/-- `InterfaceMetadata`. -/
def Interface.meta (b : Interface) : Option JVal :=
  jobj (headJson b.docs b.stability ++ jmap "funcs" (metaMap Func.mangled Func.meta b.funcs) ++
    jmap "types" (metaMap TypeDef.name TypeDef.meta b.types))

def inlineMeta : WorldItem → Option (String × JVal)
  | .ifaceInline n b => b.meta.map (n, ·)
  | _ => none

def typeMeta : WorldItem → Option (String × JVal)
  | .type td => td.meta.map (td.name, ·)
  | _ => none

def funcMeta : WorldItem → Option (String × JVal)
  | .func f => f.meta.map (f.mangled, ·)
  | _ => none

def refStability : WorldItem → Option (String × JVal)
  | .ifaceRef i _ st => st.json.map (i.id, ·)
  | _ => none

def refDocs : WorldItem → Option (String × JVal)
  | .ifaceRef i d _ => d.map fun d => (i.id, .str d)
  | _ => none

/-- `WorldMetadata` (format version 1). -/
def World.meta (w : World) : Option JVal :=
  jobj (headJson w.docs w.stability ++
    jmap "interfaces" (w.imports.filterMap inlineMeta) ++
    jmap "types" (w.imports.filterMap typeMeta) ++
    jmap "funcs" (w.imports.filterMap funcMeta) ++
    jmap "interface_exports" (w.exports.filterMap inlineMeta) ++
    jmap "func_exports" (w.exports.filterMap funcMeta) ++
    jmap "interface_import_stability" (w.imports.filterMap refStability) ++
    jmap "interface_export_stability" (w.exports.filterMap refStability) ++
    jmap "interface_import_docs" (w.imports.filterMap refDocs) ++
    jmap "interface_export_docs" (w.exports.filterMap refDocs))

/-- `PackageMetadata`. -/
def Package.docsJson (p : Package) : JVal :=
  .obj (jopt "docs" (jstr p.docs) ++
    jmap "worlds" (metaMap Prod.fst (fun nw => nw.2.meta) p.worlds) ++
    jmap "interfaces" (metaMap Prod.fst (fun nb => nb.2.meta) p.interfaces))

/-- The contents of the `package-docs` custom section. -/
def docsSection (p : Package) : ByteArray :=
  ⟨#[0x01]⟩ ++ (String.ofList p.docsJson.print).toUTF8

/-! ## Injecting metadata -/

def getObj (k : String) (v : Option JVal) : Option JVal := v.bind (·.get k)

def getStr? (k : String) (v : Option JVal) : Option String := v.bind (·.getStr k)

def Labeled.inject {α : Type} (items : Option JVal) (l : Labeled α) : Labeled α :=
  { l with docs := getStr? l.name items }

def TyDefKind.inject (items : Option JVal) : TyDefKind → TyDefKind
  | .record fs => .record (fs.map (Labeled.inject items))
  | .variant cs => .variant (cs.map (Labeled.inject items))
  | .enum cs => .enum (cs.map (Labeled.inject items))
  | .flags fs => .flags (fs.map (Labeled.inject items))
  | k => k

def TypeDef.inject (m : Option JVal) (td : TypeDef) : TypeDef :=
  let mt := getObj td.name m
  { td with docs := getStr? "docs" mt, stability := Stability.ofJson (getObj "stability" mt),
            kind := td.kind.inject (getObj "items" mt) }

def Func.inject (m : Option JVal) (f : Func) : Func :=
  let mf := getObj f.mangled m
  { f with docs := getStr? "docs" mf, stability := Stability.ofJson (getObj "stability" mf) }

def Interface.inject (m : Option JVal) (b : Interface) : Interface :=
  { b with docs := getStr? "docs" m, stability := Stability.ofJson (getObj "stability" m),
           types := b.types.map (TypeDef.inject (getObj "types" m)),
           funcs := b.funcs.map (Func.inject (getObj "funcs" m)) }

def WorldItem.inject (m : Option JVal) (imp : Bool) : WorldItem → WorldItem
  | .ifaceRef i _ _ =>
    let (st, ds) := if imp then ("interface_import_stability", "interface_import_docs")
      else ("interface_export_stability", "interface_export_docs")
    .ifaceRef i (getStr? i.id (getObj ds m)) (Stability.ofJson (getObj i.id (getObj st m)))
  | .ifaceInline n b =>
    .ifaceInline n (b.inject (getObj n (getObj (if imp then "interfaces" else "interface_exports") m)))
  | .func f => .func (f.inject (getObj (if imp then "funcs" else "func_exports") m))
  | .type td => .type (td.inject (getObj "types" m))

def World.inject (m : Option JVal) (w : World) : World :=
  { imports := w.imports.map (WorldItem.inject m true),
    exports := w.exports.map (WorldItem.inject m false),
    docs := getStr? "docs" m, stability := Stability.ofJson (getObj "stability" m) }

/-- Put the metadata `m` (a `PackageMetadata` object) into a package. -/
def Package.inject (m : JVal) (p : Package) : Package :=
  { p with docs := m.getStr "docs",
           interfaces := p.interfaces.map fun (n, b) => (n, b.inject (getObj n (m.get "interfaces")))
           worlds := p.worlds.map fun (n, w) => (n, w.inject (getObj n (m.get "worlds"))) }

/-- Read the `package-docs` section contents (version `0` or `1`). -/
def readDocsSection (data : ByteArray) : Option JVal :=
  match data.data.toList with
  | v :: rest => if v = 0 ∨ v = 1 then JVal.parse (String.fromUTF8Lossy ⟨rest.toArray⟩).toList else none
  | [] => none

end Silmaril.Wasm.Wit.Binary

namespace Silmaril.Wasm.Wit.Binary

/-! ## The normal form with docs -/

/-- An interface with its functions in wit-component's order, docs kept. -/
def Interface.canon (b : Interface) : Interface := { b with funcs := sortFuncs b.types b.funcs }

def WorldItem.canon : WorldItem → WorldItem
  | .ifaceInline n b => .ifaceInline n b.canon
  | it => it

def World.canon (w : World) : World :=
  { w with imports := w.imports.map WorldItem.canon, exports := w.exports.map WorldItem.canon }

/-- The normal form of a package with its docs: what `decodePackage` gives
back. -/
def Package.canon (p : Package) : Package :=
  { p with interfaces := p.interfaces.map fun (n, b) => (n, b.canon),
           worlds := p.worlds.map fun (n, w) => (n, w.canon) }

/-- Labels of a record, variant, enum or flags type are distinct. -/
def TyDefKind.LabelsUnique : TyDefKind → Prop
  | .record fs => (fs.map (·.name)).Nodup
  | .variant cs => (cs.map (·.name)).Nodup
  | .enum cs => (cs.map (·.name)).Nodup
  | .flags fs => (fs.map (·.name)).Nodup
  | _ => True

/-- The names the metadata is keyed by are distinct within an interface. -/
def Interface.NamesUnique (b : Interface) : Prop :=
  (b.types.map (·.name)).Nodup ∧ (b.funcs.map Func.mangled).Nodup ∧ ∀ td ∈ b.types, td.kind.LabelsUnique

/-- The keys of one direction (imports or exports) of a world are distinct. -/
def WorldItem.key : WorldItem → String
  | .ifaceRef i _ _ => i.id
  | .ifaceInline n _ => n
  | .func f => f.mangled
  | .type t => t.name

def WorldItem.isType : WorldItem → Bool
  | .type _ => true
  | _ => false

def World.NamesUnique (w : World) : Prop :=
  (w.imports.map WorldItem.key).Nodup ∧ (w.exports.map WorldItem.key).Nodup ∧
  (∀ it ∈ w.exports, it.isType = false) ∧
  (∀ it ∈ w.imports ++ w.exports, match it with
    | .ifaceInline _ b => b.NamesUnique
    | .type td => td.kind.LabelsUnique
    | _ => True)

/-- The names the metadata is keyed by are distinct. -/
def Package.NamesUnique (p : Package) : Prop :=
  (p.interfaces.map (·.1)).Nodup ∧ (p.worlds.map (·.1)).Nodup ∧
  (∀ nb ∈ p.interfaces, nb.2.NamesUnique) ∧ (∀ nw ∈ p.worlds, nw.2.NamesUnique)

end Silmaril.Wasm.Wit.Binary
