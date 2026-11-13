module

public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# Strict parsing of component binaries: core modules, outer alias sorts, attributes

`BinaryP3.parse` follows the grammar of `Binary.md` at component-model `d095e2f`. Three rules
are not part of that grammar, but `wasm-tools` (1.262.0, the pin of
`tests/wasm-p3-binary`) and the component-model tests treat a binary that breaks them as
malformed:

* **core modules**: the bytes of a `core:module` section are a Core WebAssembly module
  (`Binary.md` keeps them opaque; here: silmaril's core decoder `decode?` accepts them);
* **outer alias sorts**: an `outer` alias is of a core module, a core type, a type or a
  component (`(if s in outeraliassort)` in `Binary.md`, which does not define the set; this is
  the set `wasm-tools` enforces);
* **attribute uniqueness**: the attributes of an `externname` (`implements`, `versionSuffix`,
  `externalId`) are of pairwise different kinds (a validation rule in `Binary.md`).

`parseStrict b` is `parse b` followed by these checks, everywhere in the component (nested
components, component and instance types included). The checks are stated as a decidable
predicate `StrictOk c` over three lists collected from `c` (`modules`, `aliases`, `names`), so
what is checked is visible in the definition. Laws in `Silmaril.Wasm.Component.BinaryP3.Strict.Thms`.

`Silmaril.Wasm.Component.BinaryP3.Check.strict` (the `tools/component-check` report) computes the
same three verdicts with `partial` functions; this module is the total version.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Wasm.Component.Binary (ItemSort CoreSort ExternName NameForm Attribute DefType
  InstanceDecl ComponentDecl AliasTarget Alias InstanceExpr)
open Silmaril.Parse.ByteParse (Error)

/-! ## The three rules -/

/-- `outeraliassort`: core modules, core types, types and components. -/
def outerSortOk : ItemSort → Bool
  | .core .module | .core .type | .type | .component => true
  | _ => false

/-- An alias is not an `outer` alias of another sort. -/
def aliasOk (a : Alias) : Bool :=
  match a.target with
  | .outer .. => outerSortOk a.sort
  | _ => true

/-- The kind of an attribute. -/
def attrKind : Attribute → Nat
  | .implements _ => 0 | .versionSuffix _ => 1 | .externalId _ => 2

/-- The attributes of a name are of pairwise different kinds. -/
def nameOk (n : ExternName) : Bool :=
  match n.form with
  | .attrs as => (as.map attrKind).Nodup
  | _ => true

/-- The bytes of a core module section are a core module (silmaril's decoder). -/
def moduleOk (m : ByteArray) : Bool := (Silmaril.Wasm.Binary.Core.decode? m).isSome

/-! ## What the rules apply to -/

/-- Aliases and names of a type definition. -/
structure Items where
  aliases : List Alias := []
  names : List ExternName := []

/-- Concatenation of collected items. -/
def Items.app (a b : Items) : Items := ⟨a.aliases ++ b.aliases, a.names ++ b.names⟩

mutual
/-- The aliases and names of a type definition (component and instance types). -/
def defTypeItems : DefType → Items
  | .component ds => componentDeclsItems ds
  | .instance ds => instanceDeclsItems ds
  | _ => {}

/-- The aliases and names of instance declarations. -/
def instanceDeclsItems : List InstanceDecl → Items
  | [] => {}
  | d :: ds => (instanceDeclItems d).app (instanceDeclsItems ds)

/-- The aliases and names of an instance declaration. -/
def instanceDeclItems : InstanceDecl → Items
  | .type t => defTypeItems t
  | .alias a => ⟨[a], []⟩
  | .export n _ => ⟨[], [n]⟩
  | .coreType _ => {}

/-- The aliases and names of component declarations. -/
def componentDeclsItems : List ComponentDecl → Items
  | [] => {}
  | d :: ds => (componentDeclItems d).app (componentDeclsItems ds)

/-- The aliases and names of a component declaration. -/
def componentDeclItems : ComponentDecl → Items
  | .import n _ => ⟨[], [n]⟩
  | .inst d => instanceDeclItems d
end

/-- The aliases and names of a list of type definitions. -/
def defTypesItems : List DefType → Items
  | [] => {}
  | t :: ts => (defTypeItems t).app (defTypesItems ts)

/-- The names of an instance expression (inline exports). -/
def instanceExprNames : InstanceExpr → List ExternName
  | .exports es => es.map (·.1)
  | _ => []

/-- What the rules apply to in a component: core modules, aliases, names. -/
structure Collected where
  modules : List ByteArray := []
  aliases : List Alias := []
  names : List ExternName := []

/-- Concatenation. -/
def Collected.app (a b : Collected) : Collected :=
  ⟨a.modules ++ b.modules, a.aliases ++ b.aliases, a.names ++ b.names⟩

/-- Items as collected. -/
def Items.toCollected (i : Items) : Collected := ⟨[], i.aliases, i.names⟩

mutual
/-- The core modules, aliases and names of a section (nested components included). -/
def Section.collect : Section → Collected
  | .coreModule b => ⟨[b], [], []⟩
  | .component c => c.collect
  | .aliases xs => ⟨[], xs, []⟩
  | .types xs => (defTypesItems xs).toCollected
  | .imports xs => ⟨[], [], xs.map (·.name)⟩
  | .exports xs => ⟨[], [], xs.map (·.name)⟩
  | .instances xs => ⟨[], [], xs.flatMap instanceExprNames⟩
  | _ => {}

/-- The core modules, aliases and names of sections. -/
def Section.collectList : List Section → Collected
  | [] => {}
  | s :: ss => s.collect.app (Section.collectList ss)

/-- The core modules, aliases and names of a component. -/
def Ast.collect : Ast → Collected
  | .mk ss => Section.collectList ss
end

/-- **The three rules hold in `c`**: every core module decodes, every alias is not an `outer`
alias of another sort, every name has attributes of different kinds. -/
def StrictOk (c : Ast) : Prop :=
  c.collect.modules.all moduleOk = true ∧ c.collect.aliases.all aliasOk = true ∧
    c.collect.names.all nameOk = true

instance (c : Ast) : Decidable (StrictOk c) := by unfold StrictOk; infer_instance

/-- The checks, as a boolean. -/
def strictOk (c : Ast) : Bool := decide (StrictOk c)

/-- The error of a component that breaks one of the rules (at the end of the input). -/
def strictError (b : ByteArray) : Error := ⟨b.size, .other "strict: core module, outer alias sort or attribute check failed"⟩

/-- **Strict parsing**: `parse`, then the three rules. -/
def parseStrict (b : ByteArray) : Except Error Ast :=
  match parse b with
  | .ok c => if strictOk c then .ok c else .error (strictError b)
  | .error e => .error e

end Silmaril.Wasm.Component.BinaryP3

end
