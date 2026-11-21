module

public import Silmaril.Semantics.Operational.Policy.Defs

/-! # Behavioural refinement with undefined behaviour

Fix what the client can observe, not the type of a program's entry. An arrow
relates entries (e.g. a block layout and a flat address space). It reads back
*every* target behaviour and rules out target UB whenever the source is safe.
See `docs/projects/memory-refinement.md` for the two different memory axes.
-/

@[expose] public section

namespace Silmaril.Semantics.MemoryRefinement

universe u v w

structure Model (Obs : Type v) where
  Entry : Type u
  may : Entry → Obs → Prop
  ub : Entry → Prop

variable {Obs : Type v} {View : Type w}

/-- Demonic safety and partial correctness. Liveness is not implicit in `may`. -/
def Model.wp (model : Model Obs) (post : Obs → Prop) (entry : model.Entry) : Prop :=
  ¬ model.ub entry ∧ ∀ out, model.may entry out → post out

/-- For this fragment an unimplemented or failed evaluation relinquishes the guarantee. -/
def ofEval {Entry : Type u} (eval : Entry → Option Obs) : Model Obs :=
  ⟨Entry, fun entry out => eval entry = some out, fun entry => eval entry = none⟩

/-- Read observations through a public view; do not hide UB. -/
def Model.map (model : Model Obs) (view : Obs → View) : Model View :=
  ⟨model.Entry, fun entry seen => ∃ out, model.may entry out ∧ view out = seen, model.ub⟩

/-- The existing operational policy, observed at an initial state. Traps remain observations. -/
def ofOperational {State : Type u} (sem : Operational.WithUB State Obs) :
    Model (Operational.Outcome Obs) := ⟨State, sem.toOpSem.May, sem.UBReachable⟩

def SoundAt (source target : Model Obs) (left : source.Entry) (right : target.Entry) : Prop :=
  ¬ source.ub left → ¬ target.ub right ∧ ∀ out, target.may right out → source.may left out

@[ext] structure Hom (source target : Model Obs) where
  rel : source.Entry → target.Entry → Prop
  sound : ∀ {left right}, rel left right → SoundAt source target left right

namespace Hom

variable {first middle last : Model Obs}

def id (model : Model Obs) : Hom model model :=
  ⟨Eq, fun | rfl, safe => ⟨safe, fun _ allowed => allowed⟩⟩

def comp (one : Hom first middle) (two : Hom middle last) : Hom first last :=
  ⟨Operational.RelComp one.rel two.rel, fun ⟨_, left, right⟩ safe =>
    let mid := one.sound left safe
    let endpt := two.sound right mid.1
    ⟨endpt.1, fun out allowed => mid.2 out (endpt.2 out allowed)⟩⟩

end Hom
end Silmaril.Semantics.MemoryRefinement
