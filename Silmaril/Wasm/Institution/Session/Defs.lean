module

public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.Binaryen.Contracts
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

/-!
# Wasm session logics

The observational semantics (`Silmaril.Wasm.Institution.Generic`) behind silmaril's module-level
notions `ExportRefines R P host` and `ExportEquiv R P host` (`Silmaril.Wasm.Binaryen.Equiv`).

* **Interfaces** are sets of export names `X : Set String`, with inclusions as morphisms.
* A **semantic object** of `X` (`Obj H X`) is an *instantiable* predicate on environments
  (store, import list) and, for each environment and each *script over `X`* (a list of export
  invocations whose names lie in `X`), a set of observations (lists of behaviours). This is
  exactly the data `ExportRefines` inspects: `Instantiate` and `moduleObs`. The reduct along
  `X ⊆ Y` hides the exports outside `X` by only running scripts over `X`.
* A Core module denotes `den P host X m` (its instantiability and `moduleObs`); a Binaryen IR
  module denotes the denotation of its lowering, as in silmaril (`entryPoints`, `BModule.obs`).
* **Operators** are the closures `close R` of a semantic object under a behaviour relation `R`
  lifted to sessions (`SessionRel R`), which keep instantiability.
* **Refinement** `Refines R a b` is `ExportRefines`' two clauses at the level of semantic objects,
  observed through scripts over `X`; `Equiv R a b` is `Refines R a b ∧ Refines Rᵒᵖ b a`, the shape
  of `ExportEquiv`.

Validity of the concrete sentence `m ⊑ m'` at the full interface `Set.univ` is exactly
`ExportRefines R P host m m'` (`Silmaril.Wasm.Institution.Session.valid_coreRef_iff`, in `Thms`).
-/

namespace Silmaril.Wasm.Institution.Session

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-- Behaviour relations (contracts on single behaviours: `Eq`, `TrapsUB`, ...). -/
abbrev BRel : Type := Behaviour Val → Behaviour Val → Prop

/-- Interfaces: sets of export names, with inclusions (`Set String` as a preorder category). -/
abbrev Iface : Type := Set String

/-- Scripts over an interface: export invocations naming only exports in the interface. -/
def Script (X : Iface) : Type := {sc : List Call // ∀ c ∈ sc, c.1 ∈ X}

/-- A script over `X` is a script over any `Y ⊇ X`. -/
def Script.widen {X Y : Iface} (h : X ≤ Y) (sc : Script X) : Script Y :=
  ⟨sc.1, fun c hc => h (sc.2 c hc)⟩

/-- Every script is a script over the full interface. -/
def Script.univ (sc : List Call) : Script Set.univ := ⟨sc, fun _ _ => trivial⟩

variable (H : Type)

/-- A semantic object of interface `X`: instantiability and session observations per
environment, for scripts over `X`. -/
structure Obj (X : Iface) where
  /-- The module can be instantiated from store `s` with imports `xas`. -/
  inst : Store H → List ExternAddr → Prop
  /-- Observations of the instantiation run followed by the session `script`. -/
  obs : Store H → List ExternAddr → Script X → Set (List (Behaviour Val))

variable {H}

/-- Hiding: observe only through scripts over the smaller interface. -/
def Obj.restrict {X Y : Iface} (f : X ⟶ Y) (a : Obj H Y) : Obj H X :=
  ⟨a.inst, fun s xas sc => a.obs s xas (sc.widen f.le)⟩

/-- The closure of a semantic object under a behaviour relation lifted to sessions: every
session `SessionRel R`-related to an observation becomes an observation. -/
def close (R : BRel) {X : Iface} (a : Obj H X) : Obj H X :=
  ⟨a.inst, fun s xas sc => {bs | ∃ bs' ∈ a.obs s xas sc, SessionRel R bs bs'}⟩

/-- **Refinement of semantic objects** under `R`: the clauses of `ExportRefines`. -/
def Refines (R : BRel) {X : Iface} (a b : Obj H X) : Prop :=
  (∀ (s : Store H) xas, StoreOk s → b.inst s xas → a.inst s xas) ∧
  ∀ (s : Store H) xas (sc : Script X), StoreOk s →
    ∀ bs ∈ a.obs s xas sc, ∃ bs' ∈ b.obs s xas sc, SessionRel R bs bs'

/-- **Equivalence of semantic objects** under `R`: the shape of `ExportEquiv`. -/
def Equiv (R : BRel) {X : Iface} (a b : Obj H X) : Prop :=
  Refines R a b ∧ Refines (fun x y => R y x) b a

variable (P : Profile) (host : HostSemantics H)

/-- The denotation of a Core module at interface `X`. -/
def den (X : Iface) (m : Module) : Obj H X :=
  ⟨fun s xas => ∃ c, Instantiate P host s m xas c, fun s xas sc => moduleObs P host s xas m sc.1⟩

/-- The session semantics over programs `Prog` with denotation `d` and refinement `Le`. -/
def mk (Prog : Type) (d : ∀ X : Iface, Prog → Obj H X)
    (Le : ∀ X : Iface, Obj H X → Obj H X → Prop) : ObsSemantics Iface where
  Sem := Obj H
  restrict := Obj.restrict
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl
  Prog := Prog
  den := d
  Op := BRel
  op _ R a := close R a
  Le := Le

/-- Core modules, refinement under `R`: the logic of `ExportRefines R`. -/
abbrev coreRef (R : BRel) : ObsSemantics Iface := mk Module (den P host) (fun _ => Refines R)

/-- Binaryen IR modules (meaning their lowering), refinement under `R`. -/
abbrev birRef (R : BRel) : ObsSemantics Iface :=
  mk BModule (fun X m => den P host X m.lower) (fun _ => Refines R)

/-- Core modules, equivalence under `R`: the logic of `ExportEquiv R`. -/
abbrev coreEquiv (R : BRel) : ObsSemantics Iface := mk Module (den P host) (fun _ => Equiv R)

/-- Binaryen IR modules, equivalence under `R`. -/
abbrev birEquiv (R : BRel) : ObsSemantics Iface :=
  mk BModule (fun X m => den P host X m.lower) (fun _ => Equiv R)

end Silmaril.Wasm.Institution.Session
