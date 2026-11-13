module

public import Silmaril.Wasm.Unified.Inst.Defs
public import Silmaril.Wasm.Institution.Components.Defs

/-!
# Components over unified core modules

The component institutions of `Silmaril.Wasm.Institution.Components` are parametric in a core
semantics `C : CoreSem M`. This module instantiates them with the unified core institution
(`Silmaril.Wasm.Unified`): core modules carry code over the opcodes of a feature signature, and a
unified model gives every such module its meaning.

* `UMod S`: a core module over the opcodes of `S`: core import and export interfaces and, for
  every export index `j`, its code `code j : S.Code`. `UMod.map σ` renames the opcodes along a
  signature morphism and keeps the interfaces (definitionally).
* `Abi In B`: a flat calling convention for a unified model with inputs `In` and observations
  `B`: how a core payload becomes an input (`arg`), and how an observation becomes an answer
  (`ret b = some r`: the call answers `r`, a payload or a trap `none`; `ret b = none`: no
  answer, e.g. divergence). `Model.abi A M` is the model with payload inputs and answer
  observations (`PModel S`); it has the same opcode algebra, so it commutes with reducts.
* `coreSem M : CoreSem (UMod S)`, for `M : PModel S`: the core strategy of a module answers a
  call of export `j` with payload `p` by any observation of `M` on `(code j, p)`. It is a
  reduction semantics with one configuration and no internal steps or imports
  (`coreRed`); core modules of the unified institution are closed (their host is part of the
  model, as in `Silmaril.Wasm.Unified.Core30.model30`).
* `pullC C σ`: the core semantics of `S`-modules through renaming into `S'`-modules.
* `mapComp σ`: rename the opcodes of every core module of a component (nested ones included).
* `CProg S`: core modules and components; `den M x` is the strategy over `sigU` (`modU` for a
  module, `Comp.denU` for a component) and `obs M (x, j, p)` the answers to a first call of
  export `j` with payload `p`: for a module, read off the core strategy at its export
  interface; for a component, the two-move plays of its strategy.
* `uModuleSem M`, `uCompSem M`, `uLinkedSem M`, `uProgramSem M`: the component logics of
  `Silmaril.Wasm.Institution.Components` at `coreSem M`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Wasm.Component Silmaril.Wasm.Unified
open Silmaril.Games (Strategy)

/-- A core module over the opcodes of `S`: core interfaces and the code of each export. -/
structure UMod (S : FSig) where
  /-- The core functions it imports. -/
  imports : CoreIface
  /-- The core functions it exports. -/
  exports : CoreIface
  /-- The code of export `j`. -/
  code : Nat → S.Code

instance (S : FSig) : CoreModule (UMod S) := ⟨UMod.imports, UMod.exports⟩

/-- Rename the opcodes of a module along a signature morphism. -/
def UMod.map {S S' : FSig} (σ : S ⟶ S') (m : UMod S) : UMod S' :=
  ⟨m.imports, m.exports, fun j => UInstr.mapCode σ.f (m.code j)⟩

/-- The module with one export (no imports) running `c`. -/
def UMod.single {S : FSig} (c : S.Code) : UMod S := ⟨[], [("main", ⟨[], []⟩)], fun _ => c⟩

/-- A flat calling convention for a unified model with inputs `In` and observations `B`. -/
structure Abi (In B : Type) where
  /-- The input of a payload (`none`: the payload is rejected and the call has no answer). -/
  arg : Payload → Option In
  /-- The answer of an observation: `some r` answers `r` (a payload, or a trap `none`);
  `none` gives no answer (divergence). -/
  ret : B → Option (Option Payload)

/-- Models with payload inputs and answer observations: the models the component layer runs. -/
abbrev PModel (S : FSig) : Type 1 := Model Payload (Option Payload) S

/-- A model seen through a flat calling convention. -/
def _root_.Silmaril.Wasm.Unified.Model.abi {In B : Type} {S : FSig} (A : Abi In B)
    (M : Model In B S) : PModel S :=
  ⟨M.alg, M.ok, fun d p => {r | ∃ i, A.arg p = some i ∧ ∃ b ∈ M.run d i, A.ret b = some r}⟩

variable {S S' S'' : FSig}

/-- The core reduction semantics of a module in the model `M`: one configuration, no steps, no
calls; the answer to `(j, p)` is any observation of `M` on `(code j, p)`. -/
def coreRed (M : PModel S) (m : UMod S) :
    Silmaril.Games.Reduction (CoreIface.sig (CoreModule.imports m))
      (CoreIface.sig (CoreModule.exports m)) where
  Conf _ := Unit
  start _ := ()
  step _ _ := False
  call _ _ _ := False
  done {q} _ r := r ∈ M.obs (m.code q.1.val, q.2)

/-- **The core semantics of a unified model.** -/
def coreSem (M : PModel S) : CoreSem (UMod S) := ⟨fun m => Strategy.ofReduction (coreRed M m)⟩

/-- The core semantics of `S`-modules through renaming into `S'`-modules. -/
def pullC (C : CoreSem (UMod S')) (σ : S ⟶ S') : CoreSem (UMod S) :=
  ⟨fun m => C.sem (m.map σ)⟩

mutual
/-- Rename the opcodes of every core module of a component. -/
def mapComp (σ : S ⟶ S') : Comp (UMod S) → Comp (UMod S')
  | .mk I ns xs => .mk I (mapNodes σ ns) xs

/-- `mapComp` on a list of nodes. -/
def mapNodes (σ : S ⟶ S') : List (Node (UMod S)) → List (Node (UMod S'))
  | [] => []
  | n :: ns => mapNode σ n :: mapNodes σ ns

/-- `mapComp` on a node. -/
def mapNode (σ : S ⟶ S') : Node (UMod S) → Node (UMod S')
  | .core m args => .core (m.map σ) args
  | .inst c args => .inst (mapComp σ c) args
end

/-- Programs of the component layer: core modules and components. -/
inductive CProg (S : FSig) where
  /-- A core module. -/
  | core (m : UMod S)
  /-- A component. -/
  | comp (c : Comp (UMod S))

/-- Rename the opcodes of a program. -/
def CProg.map (σ : S ⟶ S') : CProg S → CProg S'
  | .core m => .core (m.map σ)
  | .comp c => .comp (mapComp σ c)

/-- The strategy of a program over `sigU`, in the model `M`. -/
def den (M : PModel S) : CProg S → Strategy sigU sigU
  | .core m => Silmaril.Wasm.Institution.Components.modU (coreSem M) m
  | .comp c => c.denU (coreSem M)

/-- The answers to a first call of export `j` with payload `p`. A module is read at its
export interface (core level); a component through its strategy over `sigU`. -/
def obs (M : PModel S) : CProg S × Nat × Payload → Set (Option Payload)
  | (.core m, j, p) => {r | ∃ h : j < (CoreModule.exports m).length,
      [.inr (.ask (⟨j, h⟩, p)), .inr (.ans (⟨j, h⟩, p) r)] ∈ (coreSem M).sem m}
  | (.comp c, j, p) => {r | [.inr (.ask (j, p)), .inr (.ans (j, p) r)] ∈ c.denU (coreSem M)}

/-! ## The component logics at a unified model -/

/-- The core-module logic at the model `M`. -/
abbrev uModuleSem (M : PModel S) := Silmaril.Wasm.Institution.Components.moduleSem (coreSem M)

/-- The nested-component logic at the model `M`. -/
abbrev uCompSem (M : PModel S) := Silmaril.Wasm.Institution.Components.compSem (coreSem M)

/-- The flat-component logic at the model `M`. -/
abbrev uLinkedSem (M : PModel S) := Silmaril.Wasm.Institution.Components.linkedSem (coreSem M)

/-- The program logic at the model `M`. -/
abbrev uProgramSem (M : PModel S) := Silmaril.Wasm.Institution.Components.programSem (coreSem M)

end Silmaril.Wasm.Unified.Component
