module

public import Silmaril.Wasm.Logic.Strategy.Defs
public import Silmaril.Games.LTS.Defs

/-!
# Open Wasm modules: specifications and game semantics

An **open module** `M : OMod H` is a set of Wasm function instances placed at
store addresses. Its imports are **host-function stubs** in the store
(`FuncCode.host h`, silmaril-lean's form for functions whose code is not Wasm);
`bind h` is the address of the function the import `h` stands for in the
environment. A call of a stub is not executed: it is a question to the
environment.

* `specHost bind Γi`: the host relation of the **most general environment**
  meeting the import context `Γi`: a stub `h` called in a store and with
  arguments satisfying the precondition of `Γi (bind h)` may return any store and
  result satisfying its postcondition, or diverge; a call violating the
  precondition has no outcome (it is stuck, which the every-run logic rules out).
* `ModuleSat P M bind Γi Γe`: the specifications of `Γe` are about functions of
  `M` (their preconditions require `M`'s code in the store) and hold, in the
  every-run logic `Silmaril.Wasm.Logic.Hoare`, under `specHost bind Γi`. Proofs use
  the ordinary rules; an import call is discharged with the stub rule
  `Open.FSpecAt.stub` and `Hoare.Safe.call`.
* `modRed P M bind : Silmaril.Games.Reduction (WCall H) (WCall H)`: the reduction
  semantics of `M` with external calls. An Opponent question `(a, s, args)` starts
  `$invoke s a args`; internal steps are silmaril-lean's host-free Core steps; at a
  host-call redex (silmaril-lean's `SingleThreaded.decompose?`) of stub `h` the
  module asks the question `(bind h, s, args)` and resumes with the answer
  `(s', r)` in place of the call; a run that ends in values, an exception or a
  trap answers with the store and that `Result`. The module answers only questions
  about its own functions in stores that hold its code (`OMod.Accepts`).
* `modStrat P M bind`: its strategy (`Silmaril.Games.Strategy.ofReduction`).

The theorems (`Silmaril.Wasm.Logic.Open.Thms`) say that `ModuleSat` implies that
`modStrat` refines the assume/guarantee strategy `agStrat (ctxSpec Γi) (ctxSpec Γe)`,
so that linked modules meet composed specifications.

## The model and its limits

* The store is shared and passed with every question and answer (as in
  silmaril-lean's host interface); an environment may return any store its
  specification allows.
* Only stub calls are imports. A call to an address of the store that holds Wasm
  code outside `M` is executed internally, as in the closed-world semantics.
* Imports do not call back into the module during a call (silmaril-lean's host
  calls are atomic); re-entrancy, at the level of the game, happens only between
  calls.
* Linking resolves a stub `h` of one module to the address `bind h` of another
  module's export; it is not silmaril-lean's instantiation, where an imported
  function's address is the exporter's own. Relating the two is pending.
* Strategies observe finite plays: this is partial correctness.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Open

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec)
open Silmaril.Wasm.Logic.Strategy (WCall resultOutcome)

variable {H : Type}

/-- **The most general environment meeting an import context**, as a host
relation: a stub `h` stands for the function at `bind h`. -/
def specHost (bind : H → Nat) (Γi : Ctx H) : HostSemantics H := fun h s args o =>
  ∃ S, Γi (bind h) = some S ∧ S.pre s args ∧
    match o with
    | .returned s' r => S.post s args s' (resultOutcome r)
    | .diverged => True

/-- An open module: the Wasm function instances it places at store addresses. -/
structure OMod (H : Type) where
  /-- The function instance at each address of the module. -/
  funcs : Nat → Option (FuncInst H)

/-- The store holds the module's code. -/
def OMod.Has (M : OMod H) (s : Store H) : Prop :=
  ∀ a fi, M.funcs a = some fi → s.funcs[a]? = some fi

/-- The module answers a question: it asks for one of its functions, in a store
holding its code. -/
def OMod.Accepts (M : OMod H) (q : Nat × Store H × List Val) : Prop :=
  (M.funcs q.1).isSome ∧ M.Has q.2.1

/-- **An open module meets its export specifications under its import
specifications.** -/
def ModuleSat (P : Profile) (M : OMod H) (bind : H → Nat) (Γi Γe : Ctx H) : Prop :=
  (∀ a S, Γe a = some S → (M.funcs a).isSome ∧ ∀ s args, S.pre s args → M.Has s) ∧
    Hoare.Ctx.Valid P (specHost bind Γi) Γe

/-- The relation with no host outcome: host calls do not step internally. -/
def noHost : HostSemantics H := fun _ _ _ _ => False

/-- **The reduction semantics of an open module** with external calls. -/
def modRed (P : Profile) (M : OMod H) (bind : H → Nat) : Reduction (WCall H) (WCall H) where
  Conf _ := Config H
  start q := invoke q.2.1 q.1 q.2.2
  step {q} c c' := M.Accepts q ∧ Silmaril.Games.Step P noHost c c'
  call {q} c m k := M.Accepts q ∧ ∃ E a h args, decompose? c.store c.code = some (E, a, h, args) ∧
    m = (bind h, c.store, args) ∧ k = fun ans => ⟨ans.1, c.frame, E.fill ans.2.toAdmin⟩
  done {q} c r := M.Accepts q ∧ c.store = r.1 ∧ c.code = r.2.toAdmin

/-- **The strategy of an open module.** -/
def modStrat (P : Profile) (M : OMod H) (bind : H → Nat) : Strategy (WCall H) (WCall H) :=
  Strategy.ofReduction (modRed P M bind)

/-- The specification of an import stub at address `a` with host code `h`, for an
import specification `S`: `S`, provided the stub is in the store and the
arguments have the stub's arity. -/
def stubSpec (a : Nat) (h : H) (S : FSpec H) : FSpec H where
  pre s args := (∃ (fi : FuncInst H) (ps rs : Ty (.list .val)), s.funcs[a]? = some fi ∧
    fi.code = .host h ∧ Expand fi.type (.func ps rs) ∧ args.length = ps.length) ∧ S.pre s args
  post := S.post

end Silmaril.Wasm.Logic.Open
