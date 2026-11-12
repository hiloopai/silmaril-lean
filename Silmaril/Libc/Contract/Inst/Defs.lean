module

public import Silmaril.Libc.Contract.Spec.Thms
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The library-contract institution, and clients that see only the contract

**The institution** (`inst : Sig A ⥤ Room`, in the sense of `Silmaril.Logic.Institution`):

| institution | here |
|---|---|
| signatures | `Sig A`: a set of exported functions and an invariant interface (ghost state) |
| signature morphisms | `Sig.Hom`: inclusion of functions, surjective projection of ghost states |
| sentences | `Contract S` |
| sentence translation | `Contract.map σ` |
| models | `Model S`: implementations as state machines (abstract machines; ELF code through a loading model) |
| model reduct | `Model.reduct σ`: forget functions |
| satisfaction | `Sat M C`: the contract holds relative to some hidden invariant |

The satisfaction condition is `Thms.sat_map_iff` (`Spec`), so `inst` is a functor into rooms and
`classic` the institution in Goguen–Burstall's direct form. The models of a signature form the
discrete category (implementations are compared through their contracts, not by simulations).

**The dual view: clients.** A client of the signature `S` is a program that calls the library only
through the functions of `S` (`Prog S α`: return a value, or call `f` and continue with its
result). It is **verified against the contract** when its weakest precondition (`Prog.WP C Q`)
holds at every allowed initial abstract state: every call it makes is a valid use, and whatever
the contract allows each call to return, the final value and abstract state satisfy `Q`. Its
**runs** against a model (`Prog.Run M p s o`) end in `done a t` or `ub` (a call crashed).

`Thms.client_correct`: a client verified against `(S, C)` runs correctly **on every model** that
satisfies `C`, from every valid start state: no crash, and the result satisfies `Q` for some
abstract state the final implementation state represents. The model's invariant never appears;
so swapping implementations is free (`Thms.client_swap`), and a client of a smaller signature
runs on every model of a bigger one through the reduct (`Thms.client_reduct`).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open CategoryTheory Silmaril.Logic.Institution

variable {A : Api}

/-! ## The institution -/

/-- The room of a signature: its contracts, its models (discrete), satisfaction. -/
def room (S : Sig A) : Room.{0, 1, 1} :=
  ⟨Contract S, Cat.of (Discrete (Model S)), fun M C => Sat (Discrete.as M) C⟩

/-- The corridor of a signature morphism: sentence translation, model reduct, the satisfaction
condition. -/
def corridor {S T : Sig A} (σ : S ⟶ T) : room S ⟶ room T :=
  ⟨Contract.map σ, Discrete.functor fun (M : Model T) => Discrete.mk (M.reduct σ),
    fun M C => sat_map_iff σ (Discrete.as M) C⟩

/-- **The library-contract institution**, as a functor into rooms. -/
def inst : Sig A ⥤ Room.{0, 1, 1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext fun C => Contract.map_id C)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))
  map_comp σ τ := Room.hom_ext (funext fun C => (Contract.map_comp σ τ C).symm)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))

/-- **The institution in the direct form** (sentence functor, model functor, satisfaction, the
satisfaction condition). -/
def classic : ClassicInstitution.{1, 0, 0, 1, 1} (Sig A) := ClassicInstitution.ofRoomFunctor inst

/-! ## Clients -/

/-- **A client of the signature `S`**: return a value, or call a function of `S` and continue
with its result. -/
inductive Prog (S : Sig A) (α : Type) : Type where
  | ret (a : α)
  | call (f : A.Fn) (hf : f ∈ S.F) (x : A.Arg f) (k : A.Ret f → Prog S α)

/-- The outcome of a client run: a crash, or a value and the final implementation state. -/
inductive Outcome (St α : Type) : Type where
  | ub
  | done (a : α) (s : St)

namespace Prog

variable {S T : Sig A} {α : Type}

/-- **The weakest precondition** of a client against a contract, for the postcondition `Q` on the
result and the final abstract state. -/
def WP (C : Contract S) (Q : α → S.G → Prop) : Prog S α → S.G → Prop
  | .ret a, g => Q a g
  | .call f hf x k, g => C.pre f hf g x ∧ ∀ r g', C.post f hf g x r g' → WP C Q (k r) g'

/-- **The client is verified against `(S, C)`** for `Q`: its weakest precondition holds at every
allowed initial abstract state. -/
def Verified (C : Contract S) (Q : α → S.G → Prop) (p : Prog S α) : Prop :=
  ∀ g, C.init g → WP C Q p g

/-- **The runs of a client** against a model. -/
inductive Run (M : Model S) : Prog S α → M.St → Outcome M.St α → Prop
  | ret (a : α) (s : M.St) : Run M (.ret a) s (.done a s)
  | ub {f : A.Fn} {hf : f ∈ S.F} {x : A.Arg f} {k : A.Ret f → Prog S α} {s : M.St} :
      M.step f hf s x none → Run M (.call f hf x k) s .ub
  | call {f : A.Fn} {hf : f ∈ S.F} {x : A.Arg f} {k : A.Ret f → Prog S α} {s t : M.St}
      {r : A.Ret f} {o : Outcome M.St α} :
      M.step f hf s x (some (t, r)) → Run M (k r) t o → Run M (.call f hf x k) s o

/-- A client of `S`, as a client of the bigger signature `T`. -/
def map (σ : Sig.Hom S T) : Prog S α → Prog T α
  | .ret a => .ret a
  | .call f hf x k => .call f (σ.le hf) x fun r => map σ (k r)

end Prog

end Silmaril.Libc.Contracts
