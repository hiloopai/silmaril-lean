module

public import Silmaril.Wasm.Component.Wat.Defs

/-!
# WAC: the composition profile of component WAT

The intermediate representation of a WAC composition is component WAT restricted to
the *composition profile*: the sections that `wac compose` / `wac encode` emit for a
composition (wac `crates/wac-graph/src/encoding.rs` at the pinned revision of
`docs/projects/wasm-components.md`):

* `types`: the types of imports (any type definition);
* `imports`: imports of any sort (instances, functions, types, components);
* `component`: an embedded package definition (opaque: any component);
* `instances`: only `(instance (instantiate c (with "name" (sort i))*))` with
  pairwise distinct argument names (fully explicit, named arguments; no inline
  export bundles);
* `aliases`: only instance-export aliases `(alias export i "name" (sort))` (WAC
  accesses `a.b`, `a["b"]`); no core or outer aliases at the top level;
* `exports`: exports of any sort;
* custom sections (`producers`, names).

Core modules, core instances, core types, `canon`, `start` and values are outside
the profile. A WAC `targets` clause has no WAT spelling: it is kept beside the WAT
(`Composition.targets`), as a WIT world name.

`isProfile` is the decidable predicate, `Profile` its `Prop`; `readProfile` reads
WAT and keeps only profile components. The round trip on the profile is in
`Silmaril.Wasm.Wac.Profile.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component

/-- An instantiation in the profile: `instantiate` with pairwise distinct argument names. -/
def instOk : InstanceExpr → Bool
  | .instantiate _ args => decide (args.map Prod.fst).Nodup
  | .exports _ => false

/-- An alias in the profile: an export of a component instance. -/
def aliasOk (a : Alias) : Bool :=
  match a.target with
  | .export _ _ => true
  | _ => false

/-- A section in the profile. -/
def secOk : Section → Bool
  | .custom _ _ => true
  | .types _ => true
  | .imports _ => true
  | .component _ => true
  | .instances xs => xs.all instOk
  | .aliases xs => xs.all aliasOk
  | .exports _ => true
  | _ => false

/-- **The composition profile** (decidable). -/
def isProfile (c : Ast) : Bool := c.sections.all secOk

/-- The composition profile. -/
def Profile (c : Ast) : Prop := isProfile c = true

instance (c : Ast) : Decidable (Profile c) := inferInstanceAs (Decidable (_ = true))

/-- Read component WAT in the composition profile. -/
def readProfile (s : String) : Option Ast :=
  (Wat.read s).bind fun c => if isProfile c then some c else none

/-- A composition: its component WAT (in the profile) and its optional target world
(`targets ns:pkg/world`, a WIT world name; checked against the WIT projection). -/
structure Composition where
  /-- The composed component. -/
  comp : Ast
  /-- The world named by `targets`, if any. -/
  targets : Option String := none

end Silmaril.Wasm.Wac
