module

public import Silmaril.Wasm.Wit.Binary.Model.Defs

/-!
# WIT packages as type-only components: the decoder

`decodeItems` reads the item sections of a type-only component back into a
package (without docs and stability, which live in the `package-docs` custom
section). It interprets the declarations of each component and instance type
in order, keeping for every type index what it denotes (`Slot`):

* an anonymous definition denotes a WIT type (`Slot.ty`), or a record,
  variant, enum or flags definition awaiting its name (`Slot.def`);
* an export (in a world, an import) of a type names it (`Slot.named`), and a
  definition is *claimed* by the export naming it (`Slot.used`);
* an alias of a type exported by an imported interface instance denotes that
  interface's type.

Function names are demangled (`demangle`), import and export names of
interfaces are parsed (`parseIfaceName`). The decoder accepts the shapes
wit-component writes; it is not wit-parser's decoder (which validates the
component first and accepts more).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary

/-! ## Names -/

/-- `l` without the prefix `p`. -/
def dropPrefix? : List Char → List Char → Option (List Char)
  | [], l => some l
  | _ :: _, [] => none
  | a :: p, b :: l => if a = b then dropPrefix? p l else none

/-- Split at the first `c`. -/
def splitAt? (c : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | a :: l => if a = c then some ([], l) else (splitAt? c l).map fun (x, y) => (a :: x, y)

/-- Parse `ns:pkg/name@version`. -/
def parseIfaceName (cs : List Char) : Option IfaceName := do
  let (ns, r) ← splitAt? ':' cs
  let (pkg, r) ← splitAt? '/' r
  match splitAt? '@' r with
  | some (n, v) => pure ⟨⟨String.ofList ns, String.ofList pkg, some (String.ofList v)⟩, String.ofList n⟩
  | none => pure ⟨⟨String.ofList ns, String.ofList pkg, none⟩, String.ofList r⟩

/-- The kind, base name and asyncness of a function name. -/
def demangleChars (cs : List Char) : Option (FuncKind × List Char × Bool) :=
  match dropPrefix? pConstructor cs with
  | some r => some (.constructor (String.ofList r), r, false)
  | none =>
  let res (k : String → FuncKind) (a : Bool) (r : List Char) :=
    (splitAt? '.' r).map fun (x, y) => (k (String.ofList x), y, a)
  match dropPrefix? pMethod cs with
  | some r => res .method false r
  | none => match dropPrefix? pStatic cs with
  | some r => res .static false r
  | none => match dropPrefix? pAsyncMethod cs with
  | some r => res .method true r
  | none => match dropPrefix? pAsyncStatic cs with
  | some r => res .static true r
  | none => match dropPrefix? pAsync cs with
  | some r => some (.freestanding, r, true)
  | none => if cs.head? = some '[' then none else some (.freestanding, cs, false)

/-! ## Slots -/

/-- What a type index denotes. -/
inductive Slot where
  | ty (t : Ty)
  | def (k : TyDefKind)
  | named (r : TyRef)
  | func (s : Sig)
  | inst (b : Interface)
  | used
  deriving Repr, Inhabited

abbrev DecM := Except String

def slotAt (slots : List Slot) (k : Nat) : DecM Slot :=
  match slots[k]? with
  | some s => pure s
  | none => throw s!"type index {k} out of bounds"

def decRef (slots : List Slot) (k : Nat) : DecM TyRef := do
  match ← slotAt slots k with
  | .named r => pure r
  | _ => throw s!"type {k} is not a named type"

def decValType (slots : List Slot) : Silmaril.Wasm.Component.Binary.ValType → DecM Ty
  | .prim p => pure (.prim p)
  | .idx k => do
    match ← slotAt slots k with
    | .ty t => pure t
    | .named r => pure (.ref r)
    | _ => throw s!"type {k} is not a value type"

def decOpt (slots : List Slot) : Option Silmaril.Wasm.Component.Binary.ValType → DecM (Option Ty)
  | none => pure none
  | some v => some <$> decValType slots v

def decValTypes (slots : List Slot) : List Silmaril.Wasm.Component.Binary.ValType → DecM (List Ty)
  | [] => pure []
  | v :: vs => do
    let a ← decValType slots v
    let b ← decValTypes slots vs
    pure (a :: b)

def decFields (slots : List Slot) : List (String × Silmaril.Wasm.Component.Binary.ValType) → DecM (List (Labeled Ty))
  | [] => pure []
  | (n, v) :: fs => do
    let a ← decValType slots v
    let b ← decFields slots fs
    pure ({ name := n, ty := a } :: b)

def decCases (slots : List Slot) : List (String × Option Silmaril.Wasm.Component.Binary.ValType) → DecM (List (Labeled (Option Ty)))
  | [] => pure []
  | (n, v) :: cs => do
    let a ← decOpt slots v
    let b ← decCases slots cs
    pure ({ name := n, ty := a } :: b)

def decParams (slots : List Slot) : List (String × Silmaril.Wasm.Component.Binary.ValType) → DecM (List (String × Ty))
  | [] => pure []
  | (n, v) :: ps => do
    let a ← decValType slots v
    let b ← decParams slots ps
    pure ((n, a) :: b)

def label (n : String) : Labeled Unit := { name := n, ty := () }

/-- The slot of a type definition. -/
def decDefVal (slots : List Slot) : DefValType → DecM Slot
  | .prim p => pure (.ty (.prim p))
  | .record fs => (.def ∘ .record) <$> decFields slots fs
  | .variant cs => (.def ∘ .variant) <$> decCases slots cs
  | .enum ls => pure (.def (.enum (ls.map label)))
  | .flags ls => pure (.def (.flags (ls.map label)))
  | .list v => (.ty ∘ .list) <$> decValType slots v
  | .fixedList v n => (.ty ∘ (.fixedList · n)) <$> decValType slots v
  | .map k v => do
    let a ← decValType slots k
    let b ← decValType slots v
    pure (.ty (.map a b))
  | .option v => (.ty ∘ .option) <$> decValType slots v
  | .result o e => do
    let a ← decOpt slots o
    let b ← decOpt slots e
    pure (.ty (.result a b))
  | .tuple vs => (.ty ∘ .tuple) <$> decValTypes slots vs
  | .own k => (.ty ∘ .own) <$> decRef slots k
  | .borrow k => (.ty ∘ .borrow) <$> decRef slots k
  | .future o => (.ty ∘ .future) <$> decOpt slots o
  | .stream o => (.ty ∘ .stream) <$> decOpt slots o

def decFuncType (slots : List Slot) (f : Silmaril.Wasm.Component.Binary.FuncType) : DecM Sig := do
  let ps ← decParams slots f.params
  let r ← decOpt slots f.result
  pure ⟨f.async, ps, r⟩

/-- The kind of the type named by an export of index `k`, and the slots with
`k` claimed. -/
def claim (slots : List Slot) (k : Nat) : DecM (TyDefKind × List Slot) := do
  match ← slotAt slots k with
  | .def kind => pure (kind, slots.set k .used)
  | .ty t => pure (.type t, slots.set k .used)
  | .named r => pure (.type (.ref r), slots)
  | _ => throw s!"type {k} cannot be named"

/-- A function from its export name and type. -/
def demangle (n : String) (s : Sig) : DecM Func :=
  match demangleChars n.toList with
  | some (k, base, a) =>
    if a = s.async then pure { name := String.ofList base, kind := k, async := a, params := s.params, result := s.result }
    else throw s!"function `{n}`: name and type disagree on async"
  | none => throw s!"malformed function name `{n}`"

/-! ## Instance types -/

/-- Decoder state of an instance type. -/
structure DSt where
  slots : List Slot := []
  types : List TypeDef := []
  funcs : List Func := []
  deriving Inhabited

/-- One declaration of an instance type; `outer` are the slots of the
enclosing component type. -/
def instStep (outer : List Slot) (s : DSt) : InstanceDecl → DecM DSt
  | .type (.val d) => do
    let sl ← decDefVal s.slots d
    pure { s with slots := s.slots ++ [sl] }
  | .type (.func ft) => do
    let sig ← decFuncType s.slots ft
    pure { s with slots := s.slots ++ [.func sig] }
  | .alias ⟨.type, .outer 1 j⟩ => do
    match outer[j]? with
    | some (.named r) => pure { s with slots := s.slots ++ [.named r] }
    | _ => throw s!"outer type {j} is not a named type"
  | .export ⟨n, .plain0⟩ (.type .subResource) =>
    pure { s with slots := s.slots ++ [.named ⟨.local, n⟩],
                  types := s.types ++ [{ name := n, kind := .resource }] }
  | .export ⟨n, .plain0⟩ (.type (.eq k)) => do
    let (kind, sl) ← claim s.slots k
    pure { s with slots := sl ++ [.named ⟨.local, n⟩], types := s.types ++ [{ name := n, kind := kind }] }
  | .export ⟨n, .plain0⟩ (.func k) => do
    match ← slotAt s.slots k with
    | .func sig => do
      let f ← demangle n sig
      pure { s with funcs := s.funcs ++ [f] }
    | _ => throw s!"function `{n}`: type {k} is not a function type"
  | _ => throw "unexpected declaration in an instance type"

def instSteps (outer : List Slot) : DSt → List InstanceDecl → DecM DSt
  | s, [] => pure s
  | s, d :: ds => do
    let s ← instStep outer s d
    instSteps outer s ds

/-- An instance type as an interface body. -/
def decInstance (outer : List Slot) (ds : List InstanceDecl) : DecM Interface := do
  let s ← instSteps outer {} ds
  pure { types := s.types, funcs := s.funcs }

/-! ## Component types (worlds and interface wrappers) -/

/-- An import or export of a component type, before it becomes a world item:
interfaces keep their bodies. -/
inductive DItem where
  | iface (key : IfaceName ⊕ String) (body : Interface)
  | func (f : Func)
  | type (t : TypeDef)
  deriving Repr

instance : Inhabited DItem := ⟨.func default⟩

/-- Decoder state of a component type. -/
structure CSt where
  slots : List Slot := []
  insts : List (Option IfaceName) := []
  imports : List DItem := []
  exports : List DItem := []
  deriving Inhabited

/-- An interface import/export name: an interface id or a plain name. -/
def nameKey (n : String) : DecM (IfaceName ⊕ String) :=
  if ':' ∈ n.toList then
    match parseIfaceName n.toList with
    | some i => pure (.inl i)
    | none => throw s!"malformed interface name `{n}`"
  else pure (.inr n)

def instanceItem (s : CSt) (n : String) (k : Nat) : DecM (DItem × CSt) := do
  match ← slotAt s.slots k with
  | .inst b => do
    let key ← nameKey n
    pure (.iface key b, { s with insts := s.insts ++ [key.getLeft?] })
  | _ => throw s!"`{n}`: type {k} is not an instance type"

def funcItem (s : CSt) (n : String) (k : Nat) : DecM DItem := do
  match ← slotAt s.slots k with
  | .func sig => .func <$> demangle n sig
  | _ => throw s!"function `{n}`: type {k} is not a function type"

/-- One declaration of a component type. -/
def compStep (s : CSt) : ComponentDecl → DecM CSt
  | .inst (.type (.instance ds)) => do
    let b ← decInstance s.slots ds
    pure { s with slots := s.slots ++ [.inst b] }
  | .inst (.type (.val d)) => do
    let sl ← decDefVal s.slots d
    pure { s with slots := s.slots ++ [sl] }
  | .inst (.type (.func ft)) => do
    let sig ← decFuncType s.slots ft
    pure { s with slots := s.slots ++ [.func sig] }
  | .inst (.alias ⟨.type, .export i n⟩) => do
    match s.insts[i]? with
    | some (some j) => pure { s with slots := s.slots ++ [.named ⟨.iface j, n⟩] }
    | _ => throw s!"instance {i} is not a named interface"
  | .import ⟨n, .plain0⟩ (.instance k) => do
    let (it, s) ← instanceItem s n k
    pure { s with imports := s.imports ++ [it] }
  | .inst (.export ⟨n, .plain0⟩ (.instance k)) => do
    let (it, s) ← instanceItem s n k
    pure { s with exports := s.exports ++ [it] }
  | .import ⟨n, .plain0⟩ (.func k) => do
    let it ← funcItem s n k
    pure { s with imports := s.imports ++ [it] }
  | .inst (.export ⟨n, .plain0⟩ (.func k)) => do
    let it ← funcItem s n k
    pure { s with exports := s.exports ++ [it] }
  | .import ⟨n, .plain0⟩ (.type .subResource) =>
    pure { s with slots := s.slots ++ [.named ⟨.local, n⟩],
                  imports := s.imports ++ [.type { name := n, kind := .resource }] }
  | .import ⟨n, .plain0⟩ (.type (.eq k)) => do
    let (kind, sl) ← claim s.slots k
    pure { s with slots := sl ++ [.named ⟨.local, n⟩],
                  imports := s.imports ++ [.type { name := n, kind := kind }] }
  | _ => throw "unexpected declaration in a component type"

def compSteps : CSt → List ComponentDecl → DecM CSt
  | s, [] => pure s
  | s, d :: ds => do
    let s ← compStep s d
    compSteps s ds

def DItem.toWorldItem : DItem → WorldItem
  | .iface (.inl i) _ => .ifaceRef i
  | .iface (.inr n) b => .ifaceInline n b
  | .func f => .func f
  | .type t => .type t

/-- A world's component type. -/
def decWorld (ds : List ComponentDecl) : DecM World := do
  let s ← compSteps {} ds
  pure { imports := s.imports.map DItem.toWorldItem, exports := s.exports.map DItem.toWorldItem }

/-! ## Packages -/

/-- A decoded top-level item: an interface or a world, with its package. -/
inductive Top where
  | iface (pkg : PackageName) (name : String) (body : Interface)
  | world (pkg : PackageName) (name : String) (w : World)
  deriving Repr, Inhabited

def Top.pkg : Top → PackageName
  | .iface p _ _ | .world p _ _ => p

/-- One exported component type `name`: a world wrapper or an interface's
component type. -/
def decTop (name : String) : List ComponentDecl → DecM Top
  | [.inst (.type (.component wds)), .inst (.export ⟨m, .plain0⟩ (.component 0))] => do
    let some i := parseIfaceName m.toList | throw s!"malformed world name `{m}`"
    if i.name ≠ name then throw s!"world `{name}` exported as `{m}`"
    let w ← decWorld wds
    pure (.world i.pkg name w)
  | ds => do
    let s ← compSteps {} ds
    match s.exports with
    | [.iface (.inl i) b] =>
      if i.name ≠ name then throw s!"interface `{name}` exported as `{i.id}`"
      pure (.iface i.pkg name b)
    | _ => throw s!"`{name}` is neither an interface nor a world"

/-- The item sections, the `k`-th item exported with type index `2 k`. -/
def decTops (k : Nat) : List Section → DecM (List Top)
  | [] => pure []
  | .types [.component ds] :: .exports [⟨⟨n, .plain0⟩, ⟨.type, j⟩, none⟩] :: rest => do
    if j ≠ 2 * k then throw s!"item `{n}` exports type {j}, expected {2 * k}"
    let t ← decTop n ds
    let ts ← decTops (k + 1) rest
    pure (t :: ts)
  | _ => throw "unexpected section"

def Top.iface? : Top → Option (String × Interface)
  | .iface _ n b => some (n, b)
  | .world .. => none

def Top.world? : Top → Option (String × World)
  | .world _ n w => some (n, w)
  | .iface .. => none

/-- Assemble a package; all items must agree on the package. -/
def assemble : List Top → DecM Package
  | [] => throw "no exported component type found"
  | t :: ts =>
    if ts.any (·.pkg ≠ t.pkg) then throw "item defined with mismatched package name"
    else pure { name := t.pkg, interfaces := (t :: ts).filterMap Top.iface?,
                worlds := (t :: ts).filterMap Top.world? }

/-- Decode the item sections of a WIT package. -/
def decodeItems (ss : List Section) : DecM Package := do
  assemble (← decTops 0 ss)

end Silmaril.Wasm.Wit.Binary
