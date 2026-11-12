module

public import Silmaril.Logic.Institution.Borrowing
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
# The standard trace-institution format for programs over import/export interfaces

This is the common format of the specification logics of `Silmaril.Wasm.Spec`: a way to read any
*logic of trace properties* together with any *trace semantics of programs* as an institution
(`Silmaril.Logic.Institution.Inst`, a functor `Sign ⥤ Room`).

## Interfaces and events

* `Iface Ty`: a **typed import/export interface**, two lists of function types (`Ty` is a
  parameter: scalar Wasm function types `Silmaril.Wasm.Game.FnType` for core modules; component
  function types later). Imports and exports are named by their index.
* `Iface.Hom Z X` (the morphisms of the category `Iface Ty`): `Z` is a sub-interface of `X` up to
  renaming, i.e. injective, type-preserving maps of the exports and of the imports of `Z` into
  those of `X`.
* `Event A R X`: the observable events of a program with interface `X`, in the shape of the
  moves of `Silmaril.Games` (`Move E F = Ev E ⊕ Ev F`): `inl` events happen at the imports,
  `inr` events at the exports, and each is a call (`ask`, carrying an argument payload `A`) or a
  return (`ans`, carrying a result payload `R`). For scalar Core Wasm `A = List Val` and
  `R = Behaviour Val`; richer value types (records, lists, streams) only change `A` and `R`.
  `Event.call`, `Event.ret`, `Event.icall`, `Event.iret` name the four kinds.
* A trace is a list of events; programs denote *good* trace sets (`Good`: nonempty and prefix
  closed), the safety reading of a game strategy.

## Observation along an interface morphism

`back f : List (Event A R X) → Option (List (Event A R Z))` reads an `X`-trace through
`f : Z ⟶ X`: export events outside the image of `f` make the trace unobservable (`none`: the
environment observing through `Z` never calls those exports), import events outside the image are
erased (calls `Z` does not name are not observed), and the remaining events are renamed back.
`reduct f T` is the image of a trace set. Strict functoriality (`reduct_comp`, `reduct_id`) and
`Good.reduct` are in `Silmaril.Wasm.Spec.Format.Thms`.

## Logics, semantics and the institution

* `Logic Ty A R`: formulas `Fm X` at each interface and a satisfaction relation `Sat T φ`
  between trace sets and formulas. Trace-set satisfaction (rather than per-trace) covers
  branching logics (CTL over the play tree) and fairness (TLA) as well as linear ones.
* `Semantics Ty A R`: programs `Prog X` at each interface and their good trace sets `traces p`.
* `inst L S : Inst.{0, 0, 0, 0, 0}`, the **institution of `L`-specifications of
  `S`-programs**:
  - signatures: interfaces `X`;
  - sentences at `X`: `Sen L X`, an observation scope `obs : scope ⟶ X` and a formula at the
    scope (the scope is part of the sentence because properties are not invariant under adding
    exports: a new export lets the environment drive the program into new states);
  - models at `X`: `Model S X`, a program `prog` at some interface `iface` observed through
    `obs : X ⟶ iface` (so every model is the semantics of an actual program, observed through
    a sub-interface); model morphisms are equalities;
  - satisfaction: `M ⊨ (τ, φ)` iff `φ` holds of the program's traces observed through
    `τ ≫ M.obs`;
  - sentence translation composes scopes, model reduct composes observations.

  The satisfaction condition (`sat_map_iff`) is associativity of composition in `Iface Ty`.
* `LogicMap L L'`: formulas of `L` as formulas of `L'`, satisfaction preserved on good trace
  sets. It yields a model-expansive comorphism `LogicMap.coHom S : inst L S → inst L' S`, so
  entailment is borrowed. `Logic.sum` joins two logics; its injections are logic maps and it has
  copairing (`LogicMap.copair`).
* `SemMap S S'`: programs of `S` as programs of `S'` with the same traces. It yields a comorphism
  `SemMap.coHom L : inst L S' → inst L S` (sentences unchanged, models translated).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec

open CategoryTheory Silmaril.Logic.Institution

/-! ## Interfaces -/

/-- A typed import/export interface: the function types of the imports and of the exports. -/
structure Iface (Ty : Type) where
  /-- The types of the imported functions, by index. -/
  imports : List Ty
  /-- The types of the exported functions, by index. -/
  exports : List Ty

namespace Iface

variable {Ty : Type}

/-- Import names of an interface. -/
abbrev Imp (X : Iface Ty) : Type := Fin X.imports.length

/-- Export names of an interface. -/
abbrev Exp (X : Iface Ty) : Type := Fin X.exports.length

/-- An interface morphism `Z ⟶ X`: `Z` is a sub-interface of `X` up to renaming (injective,
type-preserving maps of exports and imports). -/
@[ext] structure Hom (Z X : Iface Ty) where
  /-- Where each export of `Z` sits in `X`. -/
  exp : Z.Exp → X.Exp
  exp_inj : Function.Injective exp
  exp_ty : ∀ j, X.exports.get (exp j) = Z.exports.get j
  /-- Where each import of `Z` sits in `X`. -/
  imp : Z.Imp → X.Imp
  imp_inj : Function.Injective imp
  imp_ty : ∀ i, X.imports.get (imp i) = Z.imports.get i

/-- Interfaces and sub-interface renamings form a category. -/
instance category : Category.{0} (Iface Ty) where
  Hom := Hom
  id _ := ⟨id, Function.injective_id, fun _ => rfl, id, Function.injective_id, fun _ => rfl⟩
  comp f g := ⟨g.exp ∘ f.exp, g.exp_inj.comp f.exp_inj, fun j => (g.exp_ty _).trans (f.exp_ty j),
    g.imp ∘ f.imp, g.imp_inj.comp f.imp_inj, fun i => (g.imp_ty _).trans (f.imp_ty i)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_exp (X : Iface Ty) : (𝟙 X : Hom X X).exp = id := rfl
@[simp] theorem id_imp (X : Iface Ty) : (𝟙 X : Hom X X).imp = id := rfl
@[simp] theorem comp_exp {X Y Z : Iface Ty} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : Hom X Z).exp = g.exp ∘ f.exp := rfl
@[simp] theorem comp_imp {X Y Z : Iface Ty} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : Hom X Z).imp = g.imp ∘ f.imp := rfl

end Iface

/-! ## Events and traces -/

/-- An event at one side of an interface with `n` functions: a call of function `i` with
argument payload `a`, or its return with result payload `r`. -/
inductive SideEv (A R : Type) (n : ℕ) : Type where
  /-- Function `i` is called with `a`. -/
  | ask (i : Fin n) (a : A)
  /-- Function `i` returns `r`. -/
  | ans (i : Fin n) (r : R)

/-- The observable events of a program with interface `X`: import events (`inl`) and export
events (`inr`), as the moves of `Silmaril.Games`. -/
abbrev Event {Ty : Type} (A R : Type) (X : Iface Ty) : Type :=
  SideEv A R X.imports.length ⊕ SideEv A R X.exports.length

namespace Event

variable {Ty A R : Type} {X : Iface Ty}

/-- The environment calls export `j` with `a`. -/
abbrev call (j : X.Exp) (a : A) : Event A R X := .inr (.ask j a)
/-- Export `j` returns `r` to the environment. -/
abbrev ret (j : X.Exp) (r : R) : Event A R X := .inr (.ans j r)
/-- The program calls import `i` with `a`. -/
abbrev icall (i : X.Imp) (a : A) : Event A R X := .inl (.ask i a)
/-- Import `i` returns `r` to the program. -/
abbrev iret (i : X.Imp) (r : R) : Event A R X := .inl (.ans i r)

end Event

/-- The export events of a trace. -/
def exportEvents {Ty A R : Type} {X : Iface Ty} (t : List (Event A R X)) :
    List (SideEv A R X.exports.length) :=
  t.filterMap Sum.getRight?

/-- The import events of a trace. -/
def importEvents {Ty A R : Type} {X : Iface Ty} (t : List (Event A R X)) :
    List (SideEv A R X.imports.length) :=
  t.filterMap Sum.getLeft?

/-- A set of traces is good when it contains the empty trace and is closed under prefixes. -/
structure Good {α : Type} (T : Set (List α)) : Prop where
  nil_mem : [] ∈ T
  of_prefix : ∀ {s t : List α}, t ∈ T → s <+: t → s ∈ T

/-! ## Observation along interface morphisms -/

/-- The preimage of `j` under a map of finite types, if any. -/
def preimage? {n m : ℕ} (f : Fin n → Fin m) (j : Fin m) : Option (Fin n) :=
  (List.finRange n).find? fun i => decide (f i = j)

/-- Read a side event through an injective renaming: `none` when outside the image. -/
def SideEv.back {A R : Type} {n m : ℕ} (f : Fin n → Fin m) : SideEv A R m → Option (SideEv A R n)
  | .ask j a => (preimage? f j).map fun i => .ask i a
  | .ans j r => (preimage? f j).map fun i => .ans i r

variable {Ty A R : Type}

/-- Read an `X`-trace through `f : Z ⟶ X`: `none` if it calls an export outside the image of
`f`; otherwise its events renamed back, import events outside the image being erased. -/
def back {Z X : Iface Ty} (f : Z ⟶ X) : List (Event A R X) → Option (List (Event A R Z))
  | [] => some []
  | .inl e :: t =>
    match e.back f.imp with
    | some e' => (back f t).map (.inl e' :: ·)
    | none => back f t
  | .inr e :: t =>
    match e.back f.exp with
    | some e' => (back f t).map (.inr e' :: ·)
    | none => none

/-- The traces of `T` observed through `f`. -/
def reduct {Z X : Iface Ty} (f : Z ⟶ X) (T : Set (List (Event A R X))) :
    Set (List (Event A R Z)) :=
  {t | ∃ u ∈ T, back f u = some t}

/-! ## Logics and semantics -/

/-- A logic of trace properties: formulas at each interface and satisfaction by trace sets. -/
structure Logic (Ty A R : Type) where
  /-- Formulas at an interface. -/
  Fm : Iface Ty → Type
  /-- Satisfaction of a formula by a set of traces. -/
  Sat : ∀ {X : Iface Ty}, Set (List (Event A R X)) → Fm X → Prop

/-- A trace semantics of programs: programs at each interface and their good trace sets. -/
structure Semantics (Ty A R : Type) where
  /-- Programs with interface `X`. -/
  Prog : Iface Ty → Type
  /-- The observable traces of a program. -/
  traces : ∀ {X : Iface Ty}, Prog X → Set (List (Event A R X))
  /-- Trace sets are good. -/
  good : ∀ {X : Iface Ty} (p : Prog X), Good (traces p)

/-! ## The institution -/

/-- A sentence at `X`: a formula at an observation scope sitting in `X`. -/
structure Sen (L : Logic Ty A R) (X : Iface Ty) where
  /-- The interface through which the formula observes. -/
  scope : Iface Ty
  /-- How the scope sits in `X`. -/
  obs : scope ⟶ X
  /-- The formula, at the scope. -/
  φ : L.Fm scope

/-- The sentence `φ` observed through all of `X`. -/
def Sen.atTop {L : Logic Ty A R} {X : Iface Ty} (φ : L.Fm X) : Sen L X := ⟨X, 𝟙 X, φ⟩

/-- Sentence translation along an interface morphism: compose the scope. -/
def Sen.map {L : Logic Ty A R} {X X' : Iface Ty} (f : X ⟶ X') (s : Sen L X) : Sen L X' :=
  ⟨s.scope, s.obs ≫ f, s.φ⟩

/-- A model at `X`: a program at some interface, observed through `X`. -/
structure Model (S : Semantics Ty A R) (X : Iface Ty) where
  /-- The program's interface. -/
  iface : Iface Ty
  /-- How `X` sits in the program's interface. -/
  obs : X ⟶ iface
  /-- The program. -/
  prog : S.Prog iface

/-- A program as a model at its own interface. -/
def Model.ofProg {S : Semantics Ty A R} {X : Iface Ty} (p : S.Prog X) : Model S X := ⟨X, 𝟙 X, p⟩

/-- The traces of a model, at its signature. -/
def Model.traces {S : Semantics Ty A R} {X : Iface Ty} (M : Model S X) :
    Set (List (Event A R X)) :=
  reduct M.obs (S.traces M.prog)

/-- The discrete category of models. -/
instance Model.category (S : Semantics Ty A R) (X : Iface Ty) : Category.{0} (Model S X) where
  Hom M M' := PLift (M = M')
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- The model reduct along an interface morphism: compose the observation. -/
def Model.reduct (S : Semantics Ty A R) {X X' : Iface Ty} (f : X ⟶ X') : Model S X' ⥤ Model S X where
  obj M := ⟨M.iface, f ≫ M.obs, M.prog⟩
  map h := ⟨congrArg (fun M : Model S X' => (⟨M.iface, f ≫ M.obs, M.prog⟩ : Model S X)) h.down⟩

/-- **Satisfaction**: the formula holds of the program's traces observed through the scope. -/
def Sat (L : Logic Ty A R) (S : Semantics Ty A R) {X : Iface Ty} (M : Model S X) (s : Sen L X) :
    Prop :=
  L.Sat (reduct (s.obs ≫ M.obs) (S.traces M.prog)) s.φ

/-- **The satisfaction condition** (associativity of composition of interface morphisms). -/
theorem sat_map_iff (L : Logic Ty A R) (S : Semantics Ty A R) {X X' : Iface Ty} (f : X ⟶ X')
    (M : Model S X') (s : Sen L X) :
    Sat L S M (s.map f) ↔ Sat L S ((Model.reduct S f).obj M) s := by
  unfold Sat Sen.map Model.reduct
  rw [Category.assoc]

/-- The room of an interface. -/
def room (L : Logic Ty A R) (S : Semantics Ty A R) (X : Iface Ty) : Room.{0, 0, 0} :=
  ⟨Sen L X, Cat.of (Model S X), Sat L S⟩

/-- The corridor of an interface morphism. -/
def corridor (L : Logic Ty A R) (S : Semantics Ty A R) {X X' : Iface Ty} (f : X ⟶ X') :
    room L S X ⟶ room L S X' :=
  ⟨Sen.map f, Model.reduct S f, fun M s => sat_map_iff L S f M s⟩

/-- **The institution of `L`-specifications of `S`-programs**, as a functor into rooms. -/
def institution (L : Logic Ty A R) (S : Semantics Ty A R) : Iface Ty ⥤ Room.{0, 0, 0} where
  obj := room L S
  map := corridor L S
  map_id X := Room.hom_ext (funext fun s => by cases s; rfl)
    (Functor.ext (fun M => by cases M; rfl) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (funext fun s => by cases s; rfl)
    (Functor.ext (fun M => by cases M; rfl) (fun _ _ _ => rfl))

/-- The institution of `L`-specifications of `S`-programs, bundled. -/
def inst (L : Logic Ty A R) (S : Semantics Ty A R) : Inst.{0, 0, 0, 0, 0} :=
  ⟨Iface Ty, institution L S⟩

/-- A program satisfies a formula at its own interface. -/
def Models (L : Logic Ty A R) (S : Semantics Ty A R) {X : Iface Ty} (p : S.Prog X) (φ : L.Fm X) :
    Prop :=
  Sat L S (Model.ofProg p) (Sen.atTop φ)

/-! ## Logic maps: comorphisms over a fixed semantics -/

/-- A map of logics: formulas of `L` as formulas of `L'` with the same meaning on good trace
sets. -/
structure LogicMap (L L' : Logic Ty A R) where
  /-- The formula translation. -/
  fm : ∀ {X : Iface Ty}, L.Fm X → L'.Fm X
  /-- Satisfaction is preserved and reflected on good trace sets. -/
  sat_fm : ∀ {X : Iface Ty} (T : Set (List (Event A R X))), Good T → ∀ φ : L.Fm X,
    L'.Sat T (fm φ) ↔ L.Sat T φ

/-- The identity logic map. -/
def LogicMap.id (L : Logic Ty A R) : LogicMap L L := ⟨fun φ => φ, fun _ _ _ => Iff.rfl⟩

/-- Composition of logic maps. -/
def LogicMap.comp {L L' L'' : Logic Ty A R} (f : LogicMap L L') (g : LogicMap L' L'') :
    LogicMap L L'' :=
  ⟨fun φ => g.fm (f.fm φ), fun T hT φ => (g.sat_fm T hT _).trans (f.sat_fm T hT φ)⟩

/-- The sum of two logics: formulas of either, each with its own satisfaction. -/
def Logic.sum (L₁ L₂ : Logic Ty A R) : Logic Ty A R where
  Fm X := L₁.Fm X ⊕ L₂.Fm X
  Sat T
    | .inl φ => L₁.Sat T φ
    | .inr ψ => L₂.Sat T ψ

/-- The left injection into a sum of logics. -/
def LogicMap.inl (L₁ L₂ : Logic Ty A R) : LogicMap L₁ (L₁.sum L₂) :=
  ⟨fun φ => .inl φ, fun _ _ _ => Iff.rfl⟩

/-- The right injection into a sum of logics. -/
def LogicMap.inr (L₁ L₂ : Logic Ty A R) : LogicMap L₂ (L₁.sum L₂) :=
  ⟨fun φ => .inr φ, fun _ _ _ => Iff.rfl⟩

/-- Copairing: two logic maps into `L` give a logic map from the sum. -/
def LogicMap.copair {L₁ L₂ L : Logic Ty A R} (f : LogicMap L₁ L) (g : LogicMap L₂ L) :
    LogicMap (L₁.sum L₂) L where
  fm
    | .inl φ => f.fm φ
    | .inr ψ => g.fm ψ
  sat_fm T hT
    | .inl φ => f.sat_fm T hT φ
    | .inr ψ => g.sat_fm T hT ψ

/-- Sentence translation along a logic map. -/
def LogicMap.sen {L L' : Logic Ty A R} (f : LogicMap L L') {X : Iface Ty} (s : Sen L X) :
    Sen L' X :=
  ⟨s.scope, s.obs, f.fm s.φ⟩

/-! ## Semantics maps -/

/-- A map of semantics: programs of `S` as programs of `S'` with the same traces. -/
structure SemMap (S S' : Semantics Ty A R) where
  /-- The program translation. -/
  prog : ∀ {X : Iface Ty}, S.Prog X → S'.Prog X
  /-- Traces are preserved. -/
  traces_prog : ∀ {X : Iface Ty} (p : S.Prog X), S'.traces (prog p) = S.traces p

/-- Model translation along a semantics map. -/
def SemMap.model {S S' : Semantics Ty A R} (m : SemMap S S') {X : Iface Ty} (M : Model S X) :
    Model S' X :=
  ⟨M.iface, M.obs, m.prog M.prog⟩

end Silmaril.Wasm.Spec
