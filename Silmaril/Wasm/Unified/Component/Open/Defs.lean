module

public import Silmaril.Wasm.Unified.Component.Inst.Defs

/-!
# Core modules with imports: open unified models

The unified models of `Silmaril.Wasm.Unified.Component.Core` are **closed**: an observation is an
answer, so `coreSem M` never calls an import of a module (a host is part of the model, as in
`model30`). This module adds **open** models, whose observations are interaction programs over
the imports of the module, and their component semantics.

* `OModel S := Model Payload (Prog sigU (Option Payload)) S`: an open model of `S`. Its
  observations of a call `(code, p)` are programs that may call import `i` with a payload
  (`Prog.call (i, a) k`) and continue with the answer, and finally answer (`Prog.pure r`).
  Opcode algebra, validation and reducts are those of every unified model, so open models are
  interpretations of the same signatures.
* `coreRedO M m`: the reduction semantics of the module `m`: from the start configuration it
  chooses an observation of `M` on the code of the called export and runs it; a call of an
  import `i` below the length of the module's import interface is a call of the strategy
  (`sigN` index `i`), a call beyond it traps (the continuation receives `none`).
  `coreSemO M : CoreSem (UMod S)`.
* `denC C`, `obsC C`: strategies and first-call answers of programs at any core semantics `C`
  (`den M` and `obs M` are `denC (coreSem M)` and `obsC (coreSem M)`); `denO M`, `obsO M` at
  `coreSemO M`.
* `CSatO`: satisfaction of the `cinst` sentences (`CSen`) in an open model, the same clauses as
  `CSat`; `cinstO` (`Silmaril.Wasm.Unified.Component.Open.Thms`) is the institution.
* `Model.toOpen M`: a closed model as an open one (every answer `r` becomes `Prog.pure r`).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Wasm.Atlas Silmaril.Wasm.Resource Silmaril.Wasm.Component Silmaril.Wasm.Unified
open Silmaril.Games (Strategy Prog Reduction)

/-- Open models: observations are programs over the imports. -/
abbrev OModel (S : FSig) : Type 1 := Model Payload (Prog sigU (Option Payload)) S

/-- A closed model as an open one. -/
def _root_.Silmaril.Wasm.Unified.Model.toOpen {S : FSig} (M : PModel S) : OModel S :=
  ⟨M.alg, M.ok, fun d p => Prog.pure '' M.run d p⟩

/-- Configurations of a run of an open module. -/
inductive OConf where
  /-- Before choosing an observation. -/
  | start
  /-- Running a program. -/
  | run (P : Prog sigU (Option Payload))

variable {S : FSig}

/-- Internal steps: choose an observation of the export's code; trap at an import beyond `n`. -/
def stepO (M : OModel S) (m : UMod S) (n : Nat) (q : Nat × Payload) : OConf → OConf → Prop
  | .start, .run P => P ∈ M.obs (m.code q.1, q.2)
  | .run (.call (i, _) k), .run P => n ≤ i ∧ P = k none
  | _, _ => False

/-- Calls: the program calls import `i < n`. -/
def callO (n : Nat) (c : OConf) (i : Fin n) (a : Payload) (k : Option Payload → OConf) : Prop :=
  ∃ k', c = .run (.call (i.val, a) k') ∧ k = fun r => .run (k' r)

/-- **The reduction semantics of a module in an open model.** -/
def coreRedO (M : OModel S) (m : UMod S) :
    Reduction (CoreIface.sig (CoreModule.imports m)) (CoreIface.sig (CoreModule.exports m)) where
  Conf _ := OConf
  start _ := .start
  step {q} c c' := stepO M m (CoreModule.imports m).length (q.1.val, q.2) c c'
  call c i k := callO (CoreModule.imports m).length c i.1 i.2 k
  done c r := c = .run (.pure r)

/-- **The core semantics of an open model.** -/
def coreSemO (M : OModel S) : CoreSem (UMod S) := ⟨fun m => Strategy.ofReduction (coreRedO M m)⟩

/-- The strategy of a program at a core semantics. -/
def denC (C : CoreSem (UMod S)) : CProg S → Strategy sigU sigU
  | .core m => Silmaril.Wasm.Institution.Components.modU C m
  | .comp c => c.denU C

/-- The answers to a first call at a core semantics. -/
def obsC (C : CoreSem (UMod S)) : CProg S × Nat × Payload → Set (Option Payload)
  | (.core m, j, p) => {r | ∃ h : j < (CoreModule.exports m).length,
      [.inr (.ask (⟨j, h⟩, p)), .inr (.ans (⟨j, h⟩, p) r)] ∈ C.sem m}
  | (.comp c, j, p) => {r | [.inr (.ask (j, p)), .inr (.ans (j, p) r)] ∈ c.denU C}

/-- The strategy of a program in an open model. -/
abbrev denO (M : OModel S) : CProg S → Strategy sigU sigU := denC (coreSemO M)

/-- The answers to a first call in an open model. -/
abbrev obsO (M : OModel S) : CProg S × Nat × Payload → Set (Option Payload) := obsC (coreSemO M)

/-- **Satisfaction** of the component sentences in an open model. -/
def CSatO {T : CSig} (M : OModel T.1) : CSen T → Prop
  | .beh φ => φ.Sat fun x => obsO M (x.1.1, x.2)
  | .res x d _ r => ∀ s ∈ denO M x.1, (handleProto Flat r).Accepts (s.map (resEv d))
  | .and φ ψ => CSatO M φ ∧ CSatO M ψ

end Silmaril.Wasm.Unified.Component
