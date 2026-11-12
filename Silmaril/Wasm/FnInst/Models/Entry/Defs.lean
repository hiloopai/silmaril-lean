module

public import Silmaril.Wasm.FnInst.Models.Base.Defs
public import Silmaril.Wasm.Institution.Entry.Defs

/-!
# Closed modules as entry points of the existing module-level logics

The link from the function-level models to the single-invocation logics of
`Silmaril.Wasm.Institution.Entry` (`Equiv.ModuleEquiv E R`, the entry logics `entryEquiv E R`).

* `Closed L`: a module context with partial bodies (functions without a body are imports);
* `entryPoints S obs`: the invocation boundary of closed modules: invoking function `a` with
  arguments `vs` can show any behaviour that `obs` reads off the behaviour of `a` in *some*
  solution of the body equations (imports behave arbitrarily). `obs` fixes the observation
  (for a stateful semantics: the initial state and how outcomes become `Behaviour`s);
* `Closed.replace T B b`: the module of context `T` with bodies `B` and `b` at the focus.

`Thms` proves that a function-level equation satisfied by the partial-body model of `B` gives
module equivalence of the two replacements, and validity of the equation between them in the
entry logic.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

open Silmaril.Wasm

variable {L : FnSyntax}

/-- A closed module: a context and partial bodies (no body: an import). -/
structure Closed (L : FnSyntax) where
  /-- The context. -/
  ctx : Ctx L
  /-- The bodies. -/
  bodies : PBodies ctx

/-- The invocation boundary of closed modules, observed through `obs`. -/
def entryPoints (S : FnSem L) {V : Type} (obs : S.Den → List V → Set (Behaviour V)) :
    Equiv.EntryPoints (Closed L) ℕ V where
  Ok _ _ _ := True
  beh m a vs := {β | ∃ env ∈ Sol S m.bodies ∅, ∃ h : a < m.ctx.n, β ∈ obs (env ⟨a, h⟩) vs}

/-- The module with bodies `B` and the candidate `b` at the focus. -/
def Closed.replace (T : Sig L) (B : PBodies T.toCtx) (b : L.Body T.n) : Closed L :=
  ⟨T.toCtx, Function.update B T.focus (some b)⟩

end Silmaril.Wasm.FnInst.Models
