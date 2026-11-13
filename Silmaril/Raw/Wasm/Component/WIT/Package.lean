module

public import Silmaril.Wasm.Component.Reference.WIT.Package.Defs

public import Silmaril.Raw.Wasm.Component.WIT

/-!
# WIT packages, interfaces and worlds

WIT source-level declarations as Lean data, following the pinned component-model design
`WIT.md` (revision `a25fc0b`): §Package Names, §WIT Interfaces, §WIT Worlds (including
§Union of Worlds with `include`), §WIT Packages and `use` (including §Top-level `use`),
§WIT Functions, §WIT Types, §WIT Identifiers, §Lexical structure (§Keywords, §Feature Gates),
§Item: `world` / `include` / `interface` / `use` / type items / `resource`, §Types, §Handles and
§Name resolution. Label spelling and name uniqueness follow `Explainer.md` §Import and Export
Definitions (the `label`, `words` and `interfacename` productions) and §Name Uniqueness.

Contents:
* identifiers: the kebab-case `label` and `words` productions as decidable predicates
  (`IsLabel`, `IsWords`) over a structural fragment split, the WIT keyword list, and the
  strong-uniqueness canonical keys (`NameKey`);
* package names with 🪺 nested namespaces/packages and SemVer 2.0 versions, use paths,
  feature gates (`@since`, `@unstable`, `@deprecated`) as data, type definitions (alias, record,
  variant, enum, flags, resource with constructor/methods/static functions), interface items
  (`use`, types, functions, with the `async` marker of `FuncType.async_`), worlds (imports and
  exports of interfaces, functions, inline interfaces and 🏷️ `name: path` imports, `use`, types,
  `include … with`), top-level `use`, and packages;
* resolution (`resolveName`, `resolveType`, `closeType`, `Interface.closedFunctions`) of source
  names to nominal `TypeId`s / `ResourceId`s and to canonical-ABI-ready `ClosedType ResourceId`,
  with a `ResolveError` on unknown names, non-resources in handles, and cycles;
* a well-formedness predicate `Package.WellFormed`, decidable, with an executable diagnostic
  list `Package.errors` and `Package.errors_eq_nil_iff`.

Resource identity is the defining `(owner, name)` pair: a resource reached through `use`
chains resolves to the interface that defines it. This is the per-definition identity of the
WIT resolver; the per-import duplication that happens when a world imports the same interface
under two plain names (`WIT.md` §Package Format) belongs to the world-to-component-type
translation, which is not modelled here.

Not modelled or not claimed: no parser (the renderer is `WIT/Render.lean`); resource
getters/setters 📡, `@external-id` 🏷️, and nested `package … { }` blocks are omitted; include
expansion (union, interface de-duplication, `with` renaming) and implicit transitive imports of
`use`d interfaces (§Transitive imports and worlds) are not computed, so world name uniqueness
ignores included items (include *cycles* are rejected); the gate *compatibility* rules (§Rules for feature gate usage: an item
referring to or contained in a gated item must be compatibly gated) are not checked; versions
in qualified paths must match a dependency's version exactly (no semver-compatible matching);
dependencies in the environment are not themselves checked. The resolution fuel is a size bound
which suffices for acyclic packages; this sufficiency, and agreement with `wit-parser`, are not
proved. Where `WIT.md` is silent, we follow the stricter binary rules: names are strongly unique
(`Explainer.md` §Name Uniqueness, stronger than WIT's case-insensitive uniqueness, so e.g.
`[method]r.r` is rejected), tuples are nonempty, and `borrow` may not occur in function results
or `future`/`stream` payloads (`Binary.md` type rules), and `stream<char>` is rejected
(`Binary.md` §Type Definitions, a temporary TODO there). Gate rules follow wit-parser 0.259
rather than the text of `WIT.md` (see `Gate.Valid`): `@unstable` is allowed in an unversioned
package, `@since` requires a package version no older than it, and `@deprecated` requires
`@since` or `@unstable`. Handle names follow `type` aliases to resources, as in wit-parser
(`WIT.md` §Handles only mentions resource items).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v w

/-! ## Identifiers -/

/-! ## Versions and package names -/

/-! ## Feature gates -/

/-! ## Declarations -/

/-! ## Desugared names -/

/-! ## Resolution -/

section Bind

variable {Ref : Type u} {Res : Type v} {Ref' Res' : Type w} {m : Type w → Type w} [Monad m]
  (onRef : Ref → m (ValType Ref' Res')) (onOwn onBorrow : Res → m (ValType Ref' Res'))

end Bind

section Checks

variable {Ref : Type u} {Res : Type v}

end Checks

/-! ## Well-formedness -/

theorem Package.errors_eq_nil_iff (env : Env) (p : Package) :
    p.errors env = [] ↔ p.WellFormed env := by
  rw [Package.wellFormed_iff]
  simp only [Package.errors, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    List.filterMap_eq_nil_iff, Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not,
    Bool.not_eq_true, and_assoc]

end Silmaril.Wasm.Component.WIT
