module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# wasmparser's type-size budget on component binaries, in linear time

wasmparser 1.262.0 keeps, for every component-level type it validates, a `TypeInfo`: a size and
a nesting depth (`crates/wasmparser/src/validator/types.rs`). A type with no members has size 1
and depth 1 (`TypeInfo::new`); an aggregate starts there and `combine`s each member
(`TypeInfo::combine`: depth the maximum of its own and the member's plus one, refused above
`MAX_WASM_COMPONENT_TYPE_DEPTH = 100` with "type nesting is too deep"; size the sum, refused
from `MAX_WASM_TYPE_SIZE = 1000000` on with "effective type size exceeds the limit of
1000000"; `combine_type_sizes` in `validator.rs`). The members (`validator/component.rs`):

* records, tuples, variants (the cases with a payload), `list`, fixed-length lists, `option`,
  `result` (`ok`, then `err`), `future`/`stream` (their payload), `map` (key, then value);
  primitives, `flags`, `enum`, `own`, `borrow`, resources have no members, and a type index
  has the size of the type it names;
* function types: the parameters, then the result;
* instance types: their exports; component types: their imports and exports
  (`validate_extern`); a top-level component likewise (`ComponentState::type_info`).

Because each type's information is computed once, from those of the types it names, the
computation is linear in the size of the binary, however large the expanded types are. The
specification side is wasm-jco's flattening and the copied validator, which expand types and
do not terminate in practice on `wit-deep-record.wit` (`16^8` leaves); this check runs first
and refuses those binaries as wasmparser does.

`problem b` reports the first refusal in a component binary with wasmparser's text and the
offset of the top-level item (a type definition, import, export or alias) being validated,
which is how wasmparser reports errors inside a type: `effective type size exceeds the limit
of 1000000 (at offset 0x27)`. Offsets of items after the first one in a section are computed
from the minimal LEB128 encoding of the items before it (`Binary.Encode`), exact for
binaries written by `wasm-encoder`.

It is an under-approximation, used only to refuse: what it does not follow counts as size 1
(core module types, `instance` sections, instances and functions it cannot resolve, values
bound by `eq`), and the outer-alias charge (`outer_alias_type_size`) is not kept; nested
`component` sections are checked with the offset of their section. Theorems:
`Silmaril.Wasm.Tools.Component.Budget.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Budget

open Silmaril.Wasm.Component.Binary (ValType DefValType DefType InstanceDecl ComponentDecl
  ExternDesc TypeBound ValueBound Alias AliasTarget ItemSort Import Export FuncType)

/-! ## Type information -/

/-- wasmparser's `MAX_WASM_TYPE_SIZE`. -/
def maxSize : Nat := 1000000

/-- wasmparser's `MAX_WASM_COMPONENT_TYPE_DEPTH`. -/
def maxDepth : Nat := 100

/-- `TypeInfo`: size and nesting depth. -/
structure TI where
  size : Nat
  depth : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `TypeInfo::new()`. -/
def TI.new : TI := ⟨1, 1⟩

def sizeMsg : String := s!"effective type size exceeds the limit of {maxSize}"
def depthMsg : String := "type nesting is too deep"

/-- **`TypeInfo::combine`**: add a member's information to an aggregate's. -/
def combine (a o : TI) : Except String TI :=
  let d := max a.depth (o.depth + 1)
  if maxDepth < d then throw depthMsg
  else if a.size + o.size < maxSize then pure ⟨a.size + o.size, d⟩
  else throw sizeMsg

/-- `TypeInfo::new()` combined with each member in order. -/
def combineAll (os : List TI) : Except String TI := os.foldlM combine TI.new

/-! ## Index spaces -/

/-- A type: its information and, for an instance type, the information of its exports. -/
structure TEnt where
  info : TI
  exps : List (String × TI) := []
  deriving Inhabited

/-- The state of one scope (a component, or a component or instance type declaration). -/
structure Sc where
  types : Array TEnt := #[]
  insts : Array (List (String × TI) × TI) := #[]
  funcs : Array TI := #[]
  /-- The scope's own information: its imports and exports combined. -/
  acc : TI := TI.new
  /-- Its exports in order (an instance type's export map). -/
  exps : List (String × TI) := []
  deriving Inhabited

def Sc.ty (sc : Sc) (i : Nat) : TEnt := sc.types[i]?.getD ⟨TI.new, []⟩

def Sc.tyInfo (sc : Sc) (i : Nat) : TI := (sc.ty i).info

def Sc.valInfo (sc : Sc) : ValType → TI
  | .prim _ => TI.new
  | .idx i => sc.tyInfo i

def Sc.optInfo (sc : Sc) : Option ValType → List TI
  | none => []
  | some t => [sc.valInfo t]

/-- The information of an imported or exported entity (`ComponentEntityType::info`). -/
def Sc.entInfo (sc : Sc) : ExternDesc → TI
  | .coreModule _ => TI.new
  | .func i => sc.tyInfo i
  | .value (.type t) => sc.valInfo t
  | .value (.eq _) => TI.new
  | .type (.eq i) => sc.tyInfo i
  | .type .subResource => TI.new
  | .component i => sc.tyInfo i
  | .instance i => sc.tyInfo i

/-- The index an imported or exported entity adds. -/
def Sc.register (sc : Sc) (info : TI) : ExternDesc → Sc
  | .type (.eq i) => { sc with types := sc.types.push (sc.ty i) }
  | .type .subResource => { sc with types := sc.types.push ⟨TI.new, []⟩ }
  | .instance i => { sc with insts := sc.insts.push ((sc.ty i).exps, info) }
  | .func _ => { sc with funcs := sc.funcs.push info }
  | _ => sc

/-- An import or export: combined into the scope, its index added. -/
def Sc.extern (sc : Sc) (name : String) (d : ExternDesc) (export_ : Bool) : Except String Sc := do
  let i := sc.entInfo d
  let acc ← combine sc.acc i
  let sc := { sc with acc, exps := if export_ then sc.exps ++ [(name, i)] else sc.exps }
  pure (sc.register i d)

/-- An alias: the type, instance or function it names (`outer` counts from the scope). -/
def aliasStep (outer : List Sc) (sc : Sc) (a : Alias) : Sc :=
  match a.sort, a.target with
  | .type, .outer ct idx =>
    let e := if ct = 0 then sc.ty idx else ((outer[ct - 1]?).map (·.ty idx)).getD ⟨TI.new, []⟩
    { sc with types := sc.types.push e }
  | .type, .export inst n =>
    let i := ((sc.insts[inst]?).bind fun p => p.1.lookup n).getD TI.new
    { sc with types := sc.types.push ⟨i, []⟩ }
  | .instance, .export inst n =>
    let i := ((sc.insts[inst]?).bind fun p => p.1.lookup n).getD TI.new
    { sc with insts := sc.insts.push ([], i) }
  | .func, .export inst n =>
    let i := ((sc.insts[inst]?).bind fun p => p.1.lookup n).getD TI.new
    { sc with funcs := sc.funcs.push i }
  | _, _ => sc

/-- The members of a value type definition. -/
def Sc.members (sc : Sc) : DefValType → List TI
  | .prim _ | .flags _ | .enum _ | .own _ | .borrow _ => []
  | .record fs => fs.map fun f => sc.valInfo f.2
  | .variant cs => cs.flatMap fun c => sc.optInfo c.2
  | .list t | .option t | .fixedList t _ => [sc.valInfo t]
  | .tuple ts => ts.map sc.valInfo
  | .result ok err => sc.optInfo ok ++ sc.optInfo err
  | .stream t | .future t => sc.optInfo t
  | .map k v => [sc.valInfo k, sc.valInfo v]

/-- The members of a function type: its parameters, then its result. -/
def Sc.funcMembers (sc : Sc) (f : FuncType) : List TI :=
  f.params.map (fun p => sc.valInfo p.2) ++ sc.optInfo f.result

/-! ## Declarations -/

mutual
/-- The information of a type definition in scope `sc` (enclosing scopes `outer`). -/
def defType (outer : List Sc) (sc : Sc) : DefType → Except String TEnt
  | .val d => do pure ⟨← combineAll (sc.members d), []⟩
  | .func f => do pure ⟨← combineAll (sc.funcMembers f), []⟩
  | .resource _ _ => pure ⟨TI.new, []⟩
  | .component ds => do
    let s ← compDecls (sc :: outer) {} ds
    pure ⟨s.acc, []⟩
  | .instance ds => do
    let s ← instDecls (sc :: outer) {} ds
    pure ⟨s.acc, s.exps⟩

/-- One instance-type declaration. -/
def instDecl (outer : List Sc) (sc : Sc) : InstanceDecl → Except String Sc
  | .coreType _ => pure sc
  | .type t => do
    let e ← defType outer sc t
    pure { sc with types := sc.types.push e }
  | .alias a => pure (aliasStep outer sc a)
  | .export n d => sc.extern n.name d true

/-- Instance-type declarations in order. -/
def instDecls (outer : List Sc) (sc : Sc) : List InstanceDecl → Except String Sc
  | [] => pure sc
  | d :: ds => do instDecls outer (← instDecl outer sc d) ds

/-- Component-type declarations in order. -/
def compDecls (outer : List Sc) (sc : Sc) : List ComponentDecl → Except String Sc
  | [] => pure sc
  | .import n d :: ds => do compDecls outer (← sc.extern n.name d false) ds
  | .inst d :: ds => do compDecls outer (← instDecl outer sc d) ds
end

/-! ## Components -/

open Silmaril.Wasm.Component.BinaryP3 (Section Ast Canon)

/-- An unsigned LEB128 number at `i`: its value and its length. -/
def leb (b : ByteArray) (i : Nat) : Nat × Nat :=
  go i 0 0 6
where
  go (j shift acc : Nat) : Nat → Nat × Nat
    | 0 => (acc, j - i)
    | k + 1 =>
      let x := (b[j]?.getD 0).toNat
      let acc := acc + (x % 128) * 2 ^ shift
      if x < 128 then (acc, j + 1 - i) else go (j + 1) (shift + 7) acc k

/-- The start of the first item of every section of a component (after its count, for the
sections that are vectors), in order. -/
def itemStarts (b : ByteArray) : List Nat :=
  go 8 (b.size + 1)
where
  go (pos : Nat) : Nat → List Nat
    | 0 => []
    | k + 1 =>
      if pos < b.size then
        let (size, n) := leb b (pos + 1)
        let c := pos + 1 + n
        let (_, m) := leb b c
        (c + m) :: go (c + size) k
      else []

/-- `0x…` in lowercase hexadecimal, as Rust's `{:#x}`. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The offsets of items encoded by `enc`, the first at `start`. -/
def offsets {α : Type} (enc : α → Option (List UInt8)) (start : Nat) : List α → List Nat
  | [] => []
  | x :: xs => start :: offsets enc (start + ((enc x).map List.length).getD 0) xs

/-- Run `f` on the items with their offsets; an error carries the item's offset. -/
def itemsAt {α : Type} (enc : α → Option (List UInt8)) (start : Nat) (sc : Sc) (xs : List α)
    (f : Sc → α → Except String Sc) : Except String Sc :=
  (xs.zip (offsets enc start xs)).foldlM (init := sc) fun sc (x, o) =>
    match f sc x with
    | .ok s => .ok s
    | .error e => .error s!"{e} (at offset {hex o})"

/-- A top-level export (`sortidx`, with an optional ascribed type). -/
def exportStep (sc : Sc) (e : Export) : Except String Sc :=
  match e.desc with
  | some d => sc.extern e.name.name d true
  | none =>
    match e.item.sort with
    | .type => do
      let i := sc.tyInfo e.item.idx
      let acc ← combine sc.acc i
      pure { sc with acc, exps := sc.exps ++ [(e.name.name, i)],
                     types := sc.types.push (sc.ty e.item.idx) }
    | .instance => do
      let p := (sc.insts[e.item.idx]?).getD ([], TI.new)
      let acc ← combine sc.acc p.2
      pure { sc with acc, exps := sc.exps ++ [(e.name.name, p.2)], insts := sc.insts.push p }
    | .func => do
      let i := (sc.funcs[e.item.idx]?).getD TI.new
      let acc ← combine sc.acc i
      pure { sc with acc, exps := sc.exps ++ [(e.name.name, i)], funcs := sc.funcs.push i }
    | _ => do
      let acc ← combine sc.acc TI.new
      pure { sc with acc }

/-- A top-level type definition. -/
def typeStep (outer : List Sc) (sc : Sc) (t : DefType) : Except String Sc := do
  let e ← defType outer sc t
  pure { sc with types := sc.types.push e }

/-- A top-level import. -/
def importStep (sc : Sc) (i : Import) : Except String Sc := sc.extern i.name.name i.desc false

/-- The functions a `canon` section adds (`lift` gives a component function of its type). -/
def canonStep (sc : Sc) : Canon → Sc
  | .lift _ _ t => { sc with funcs := sc.funcs.push (sc.tyInfo t) }
  | _ => sc

/-- The budget check of a component's sections; `starts` are their first items' offsets
(only for the top level: nested components use the offset of their section). -/
def sections (outer : List Sc) (sc : Sc) : List Section → List Nat → Nat → Except String Sc
  | [], _, _ => pure sc
  | s :: ss, starts, dflt => do
    let o := starts.headD dflt
    let sc ← match s with
      | .types xs => itemsAt Silmaril.Wasm.Component.Binary.Encode.defType o sc xs (typeStep outer)
      | .imports xs => itemsAt Silmaril.Wasm.Component.Binary.Encode.import_ o sc xs importStep
      | .exports xs => itemsAt Silmaril.Wasm.Component.Binary.Encode.export_ o sc xs exportStep
      | .aliases xs => pure (xs.foldl (aliasStep outer) sc)
      | .instances xs => pure (xs.foldl (fun sc _ => { sc with insts := sc.insts.push ([], TI.new) }) sc)
      | .canons xs => pure (xs.foldl canonStep sc)
      | .component (.mk css) => do
        let _ ← sectionsNested (sc :: outer) {} css o
        pure sc
      | _ => pure sc
    sections outer sc ss starts.tail dflt
where
  /-- Sections of a nested component (no item offsets). -/
  sectionsNested (outer : List Sc) (sc : Sc) : List Section → Nat → Except String Sc
    | [], _ => pure sc
    | s :: ss, o => do
      let at_ (r : Except String Sc) : Except String Sc :=
        match r with
        | .ok s => .ok s
        | .error e => .error s!"{e} (at offset {hex o})"
      let sc ← match s with
        | .types xs => at_ (xs.foldlM (typeStep outer) sc)
        | .imports xs => at_ (xs.foldlM importStep sc)
        | .exports xs => at_ (xs.foldlM exportStep sc)
        | .aliases xs => pure (xs.foldl (aliasStep outer) sc)
        | .canons xs => pure (xs.foldl canonStep sc)
        | _ => pure sc
      sectionsNested outer sc ss o

/-- **The budget problem of a component binary**: wasmparser's message and offset for the
first type, import or export that exceeds the size or depth limit; `none` when there is none or
when the binary does not parse. -/
def problem (b : ByteArray) : Option String :=
  match Silmaril.Wasm.Component.Codec.decodeLax b with
  | .error _ => none
  | .ok (.mk ss) =>
    match sections [] {} ss (itemStarts b) 0 with
    | .ok _ => none
    | .error e => some e

/-- The budget problem of the `component-type` custom sections of a core module: the
section's name and the problem of its payload. -/
def coreProblem (sections : List (String × ByteArray)) : Option (String × String) :=
  sections.findSome? fun (n, pl) =>
    if n.startsWith "component-type" then (problem pl).map (n, ·) else none

end Silmaril.Wasm.Tools.Component.Budget
