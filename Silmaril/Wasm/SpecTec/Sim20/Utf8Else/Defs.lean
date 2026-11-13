module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.Thms

/-!
# Reading `otherwise` back across the 2.0 `$utf8` erratum (definitions)

An earlier step  moved every positive derivation of `simEnv20T B` to `utf8Env20T B`
(`Utf8Mono.dderivesB_ext`) and every step under `ElseMono`: the `otherwise` premises of
`simEnv20T B` must hold in `utf8Env20T B`. An `otherwise` premise is negative, so it moves only if
every earlier rule that fires in `utf8Env20T B` also fires in `simEnv20T B`. This topic proves the
converse monotonicity that this needs, on syntax that never calls `$utf8`, and uses it on the
`otherwise` rules of the 2.0 script.

The converse is generic in a pair `EnvExt e₁ e₂ x₀` (`Utf8Mono.EnvExt`): `e₂` answers at least what
`e₁` answers, and they differ only at the definition `x₀`.

* `GoodEv x₀`, `GoodEvs x₀ l`: no event of `l` refers to the definition `x₀`. Relation, type and
  grammar references are unrestricted.
* `DefsOk x₀ ρ`: no definition variable of `ρ` names `x₀`. `ArgOk x₀ w`: a definition argument
  is not `x₀`.
* **`Clean e₁ x₀`**: no clause of a definition of `e₁` other than `x₀`, and no rule of a relation of
  `e₁`, refers to `x₀`. For the 2.0 script and `$utf8` it is one kernel check
  (`Utf8Else.clean20T`): among all items of `fixedT20`, only `$utf8` itself, the type `name` and
  the grammar `Bname` refer to `$utf8`.
* `utf8Users20`: those three items.
* `badU20`: the twelve types of `fixedT20` whose unfolding reaches `name`, computed by a
  reference closure over the script's type table and checked by the kernel
  (`Utf8Else.typsOffB_badU20`): `name`, `export`, `import`, `exportinst`, `module`,
  `moduleinst`, `funcinst`, `frame`, `store`, `state`, `admininstr` and `config`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evClause evRule evRefs items)

/-- An event that does not refer to the definition `x₀`. -/
def GoodEv (x₀ : String) : Ev → Prop
  | .ref 1 x => x ≠ x₀
  | _ => True

/-- No event of `l` refers to the definition `x₀`. -/
def GoodEvs (x₀ : String) (l : List Ev) : Prop := ∀ e ∈ l, GoodEv x₀ e

/-- No definition variable of `ρ` names `x₀`. -/
def DefsOk (x₀ : String) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.defs, p.2 ≠ x₀

/-- A definition argument that is not `x₀`. -/
def ArgOk (x₀ : String) : ArgV → Prop
  | .defName y => y ≠ x₀
  | _ => True

/-- **`e₁` never refers to `x₀`** outside `x₀`'s own clauses: in no clause of another definition
and in no rule of a relation. -/
structure Clean (e₁ : Env) (x₀ : String) : Prop where
  defs : ∀ x d, x ≠ x₀ → e₁.findDef? x = some d → ∀ c ∈ d.2.2, GoodEvs x₀ (evClause c)
  rels : ∀ x d, e₁.findRel? x = some d → ∀ r ∈ d.2.2.2, GoodEvs x₀ (evRule r)

/-- The items of `s` that refer to the definition `x`, as a check: every other item is free of
it. -/
def refFreeB (x : String) (allowed : List (Nat × String)) (s : Script) : Bool :=
  (items s).all fun it => allowed.contains (it.1, it.2.1) || !(evRefs it.2.2).contains (1, x)

/-- The items of the 2.0 script allowed to refer to `$utf8`. -/
def utf8Users20 : List (Nat × String) := [(1, "utf8"), (2, "name"), (3, "Bname")]

/-- The types of the 2.0 script whose unfolding reaches `name`. -/
def badU20 : List String :=
  ["name", "export", "import", "exportinst", "module", "moduleinst", "funcinst", "frame", "store",
    "state", "admininstr", "config"]

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
