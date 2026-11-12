module

public import Silmaril.Wasm.Wac.Elab.Defs

/-!
# WAC: alias expansion in item kinds

wac compares value types after resolving aliases (`Types::resolve_value_type`, called by
`SubtypeChecker::value_type`, wac `5a7480c`): `type x = u32` makes `x` and `u32` the
same type. In an item kind, an alias is a type export `(x, .type (.value t))` whose
definiens `t` is not the self-reference `ref x` (a record, variant, enum or flags type
`x` exports `.type (.value (ref x))`), and a use of it is the local reference
`ref ⟨.local, x⟩` (or `own`/`borrow` of it, for an alias of a resource).

* `aliases es`: the alias table of a list of items (an instance's exports; a
  component's imports, where a world's types live);
* `Ty.substA Γ t`: replace every local reference to an alias of `Γ` by its definiens,
  one level; `normTable Γ` iterates this on the table itself (`Γ.length` times), so
  that for acyclic aliases every definiens is alias-free (`Normal`);
* `Kind.expand`: expand the aliases of every instance and component, each with its own
  table (a local reference means the enclosing instance or component);
* `PkgEnv.expand` and **`elabDocA env d := elabDoc env.expand d`**: elaboration against
  a registry whose aliases are expanded. The document's own declarations are expanded
  as they are elaborated (`Silmaril.Wasm.Wac.WitDecl`), so every comparison of the
  elaborator (`sub`) is a comparison up to aliases.

`Silmaril.Wasm.Wac.Alias.Thms`: on a normal table an alias and its definiens expand to the
same type (`substA_alias`) and expansion is idempotent (`substA_idem`); expansion keeps
kinds WIT-shaped (`expand_wit`), so `elabDocA` inherits `elabDoc_iff` and
`elabDoc_typed`.

**Restriction.** Aliases are local to an instance or component. A reference to a type of
another interface (`ref ⟨.iface I, t⟩`, a used type) is not expanded even when `t` is
an alias in `I`; the WAC side keeps it the same way.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

namespace Alias

/-- An alias table: local names and their definientia. -/
abbrev Table := List (String × Silmaril.Wasm.Wit.Binary.Ty)

/-- The aliases among named items. -/
def aliases (es : Externs) : Table :=
  es.filterMap fun p => match p.2 with
    | .type (.value t) => if t = .ref ⟨.local, p.1⟩ then none else some (p.1, t)
    | _ => none

/-- The resource an alias of a resource stands for. -/
def resOf (Γ : Table) (x : String) : TyRef :=
  match Γ.lookup x with
  | some (.ref r) | some (.own r) => r
  | _ => ⟨.local, x⟩

mutual
/-- Replace the local references to aliases by their definientia (one level). -/
def substA (Γ : Table) : Silmaril.Wasm.Wit.Binary.Ty → Silmaril.Wasm.Wit.Binary.Ty
  | .prim p => .prim p
  | .ref ⟨.local, x⟩ => (Γ.lookup x).getD (.ref ⟨.local, x⟩)
  | .ref r => .ref r
  | .list t => .list (substA Γ t)
  | .fixedList t n => .fixedList (substA Γ t) n
  | .map k v => .map (substA Γ k) (substA Γ v)
  | .option t => .option (substA Γ t)
  | .result a b => .result (substAOpt Γ a) (substAOpt Γ b)
  | .tuple ts => .tuple (substAs Γ ts)
  | .own ⟨.local, x⟩ => .own (resOf Γ x)
  | .own r => .own r
  | .borrow ⟨.local, x⟩ => .borrow (resOf Γ x)
  | .borrow r => .borrow r
  | .future t => .future (substAOpt Γ t)
  | .stream t => .stream (substAOpt Γ t)
def substAOpt (Γ : Table) : Option Silmaril.Wasm.Wit.Binary.Ty → Option Silmaril.Wasm.Wit.Binary.Ty
  | none => none
  | some t => some (substA Γ t)
def substAs (Γ : Table) : List Silmaril.Wasm.Wit.Binary.Ty → List Silmaril.Wasm.Wit.Binary.Ty
  | [] => []
  | t :: ts => substA Γ t :: substAs Γ ts
end

/-- A function type with its aliases expanded. -/
def substSig (Γ : Table) (s : Sig) : Sig :=
  ⟨s.async, s.params.map fun p => (p.1, substA Γ p.2), s.result.map (substA Γ)⟩

/-- Expand the definientia of a table within the table, `n` times. -/
def normTableN : Nat → Table → Table
  | 0, Γ => Γ
  | n + 1, Γ => normTableN n (Γ.map fun p => (p.1, substA Γ p.2))

/-- The table with its definientia expanded (alias-free when the aliases are acyclic). -/
def normTable (Γ : Table) : Table := normTableN Γ.length Γ

/-- Every definiens is alias-free: expanding it changes nothing. -/
def Normal (Γ : Table) : Prop := ∀ p ∈ Γ, substA Γ p.2 = p.2

mutual
/-- Expand the aliases of a kind; `Γ` is the table of the enclosing instance or
component (used by its functions, values and type definitions). -/
def expandIn (Γ : Table) : Kind → Kind
  | .func s => .func (substSig Γ s)
  | .value t => .value (substA Γ t)
  | .resource r => .resource r
  | .type k => .type (expandIn Γ k)
  | .inst id es => .inst id (expandEx (normTable (aliases es)) es)
  | .comp id is es => .comp id (expandEx (normTable (aliases is)) is) (expandEx (normTable (aliases is)) es)
/-- Expand the aliases of named items. -/
def expandEx (Γ : Table) : Externs → Externs
  | [] => []
  | (n, k) :: rest => (n, expandIn Γ k) :: expandEx Γ rest
end

end Alias

/-- A kind with the aliases of its instances and components expanded. -/
def Kind.expand (k : Kind) : Kind := Alias.expandIn [] k

/-- A package with its aliases expanded. -/
def PkgType.expand (p : PkgType) : PkgType :=
  { imports := Alias.expandEx [] p.imports, exports := Alias.expandEx [] p.exports,
    defs := Alias.expandEx [] p.defs }

/-- A registry with its aliases expanded. -/
def PkgEnv.expand (env : PkgEnv) : PkgEnv := env.map fun p => (p.1, p.2.expand)

/-- **Elaboration up to aliases**: against the registry with its aliases expanded. -/
def elabDocA (env : PkgEnv) (d : Syntax.Document) : Except ElabError CGraph := elabDoc env.expand d

end Silmaril.Wasm.Wac
