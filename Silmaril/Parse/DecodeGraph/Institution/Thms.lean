module

public import Silmaril.Parse.DecodeGraph.Institution.Defs

public section

namespace Silmaril.Parse.DecodeGraph.Institution

variable {Context Buffer Source Middle Target : Type*}

@[simp] theorem translate_id : translate (Context := Context) (Buffer := Buffer) (id : Source → Source) = id := rfl

theorem translate_comp (first : Source → Middle) (second : Middle → Target) :
    translate (Context := Context) (Buffer := Buffer) (second ∘ first) = translate second ∘ translate first := rfl

@[simp] theorem reduct_id (model : Graph Context Buffer Source) : reduct id model = model := rfl

theorem reduct_comp (first : Source → Middle) (second : Middle → Target) (model : Graph Context Buffer Target) :
    reduct (second ∘ first) model = reduct first (reduct second model) := rfl

/-- The institution satisfaction condition for positive exact-success atoms. -/
theorem satisfaction (f : Source → Target) (model : Graph Context Buffer Target) (atom : Atom Context Buffer Source) :
    Satisfies model (translate f atom) ↔ Satisfies (reduct f model) atom := Iff.rfl

/-- A successful target instruction with two distinct preimages gives two
successful reduct outcomes at the same query and span. -/
theorem reduct_not_deterministic_of_collision {f : Source → Target} {model : Graph Context Buffer Target}
    {input : Input Context Buffer} {left right : Source} {endPos : Nat}
    (different : left ≠ right) (collision : f left = f right) (success : (input, (f left, endPos)) ∈ model) :
    ¬ Deterministic (reduct f model) :=
  fun unique => different (congrArg Prod.fst (unique
    (show (input, (left, endPos)) ∈ reduct f model from success)
    (show (input, (right, endPos)) ∈ reduct f model from
      (show (input, (f right, endPos)) ∈ model from collision ▸ success))))

end Silmaril.Parse.DecodeGraph.Institution
