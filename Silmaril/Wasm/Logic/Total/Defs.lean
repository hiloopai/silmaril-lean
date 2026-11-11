module

public import Silmaril.Wasm.Logic.Hoare.Defs

/-!
# Total correctness for the every-run logic: definitions

The inductive total-correctness predicate `Hoare.TSafe`/`Hoare.TWP`
(`Silmaril.Wasm.Logic.Hoare.Defs`: every run terminates, at an exit satisfying the
postcondition) gets the structure of the partial logic:

* `seqPostT`, `labelPostT`, `framePostT`, `bodyPostT`: how an outcome is seen
  from outside a sequence, a label, a function frame and a function body, with
  the continuation (falling through, a branch to the label, a tail call) required
  to be **totally** correct;
* `TFSpecAt P host a S`: a **total** function specification: from any store and
  arguments satisfying the precondition, in any calling frame, below any caller
  stack and through any `CALL_REF` form, every run of the call terminates with
  the call postcondition; `TCtx.Valid` for a specification context;
* `FSpec.below S μ n`: the specification `S` restricted to calls whose measure
  `μ s args` is below `n`, for the **total recursion rule** (a natural-number
  measure on the arguments of the functions of a context);
* `TCtxSat P host Γi Γe μ`: the **total module rule**, guarded validity of
  exports `Γe` relative to imports `Γi` by induction on the measure `μ`;
* `loopPostT`: the postcondition of a loop body for the **loop rule with a
  variant**.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type}

/-- The postcondition of `c₁` in `c₁ ++ c₂` for total correctness: on falling
through, `c₂` must be totally correct. -/
def seqPostT (P : Profile) (host : HostSemantics H) (c₂ : List Admin) (Q : Post H) : Post H :=
  fun s f o =>
    match o with
    | .normal vs => TSafe P host Q ⟨s, f, vals vs ++ c₂⟩
    | o => Q s f o

/-- The postcondition of the body of `LABEL_n{cont}` on the values `us`, for total
correctness: a branch to the label continues, totally correctly, with `cont`. -/
def labelPostT (P : Profile) (host : HostSemantics H) (n : Nat) (cont : List Instr)
    (us : List Val) (Q : Post H) : Post H := fun s f o =>
  match o with
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧
      TSafe P host Q ⟨s, f, vals us ++ vals vs₂ ++ expression cont⟩
  | o => labelPostK P host n cont us Q 0 s f o

/-- The postcondition of the body of a function frame `FRAME_n{F}` called from
frame `f` on the values `vs₀`, for total correctness: a tail call continues,
totally correctly, with the call it makes. -/
def framePostT (P : Profile) (host : HostSemantics H) (n : Nat) (f : Frame) (vs₀ : List Val)
    (Q : Post H) : Post H := fun s F o =>
  match o with
  | .tail vs a c => ∃ (vs₁ args : List Val) (fn : FuncInst H) (ps rs : Ty (.list .val)),
      vs = vs₁ ++ args ∧ s.funcs[a]? = some fn ∧ Expand fn.type (.func ps rs) ∧
      args.length = ps.length ∧
      TSafe P host Q ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c.retToCallIn F.module]⟩
  | o => framePostK P host n f vs₀ Q 0 s F o

/-- The postcondition of a function body for total correctness. -/
def bodyPostT (P : Profile) (host : HostSemantics H) (n : Nat) (f : Frame) (vs₀ : List Val)
    (Q : Post H) : Post H :=
  labelPostT P host n [] [] (framePostT P host n f vs₀ Q)

/-- **A total function specification** at address `a`. -/
def TFSpecAt (P : Profile) (host : HostSemantics H) (a : Nat) (S : FSpec H) : Prop :=
  ∀ s args, S.pre s args → ∀ (f : Frame) (vs₀ : List Val) (c : Admin), c.IsCallRef →
    TSafe P host (callPost f vs₀ (S.post s args)) ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c]⟩

/-- Every specification of the context is totally correct. -/
def TCtx.Valid (P : Profile) (host : HostSemantics H) (Γ : Ctx H) : Prop :=
  ∀ a S, Γ a = some S → TFSpecAt P host a S

/-- The specification restricted to calls whose measure is below `n`. -/
def FSpec.below (S : FSpec H) (μ : Store H → List Val → Nat) (n : Nat) : FSpec H where
  pre s args := S.pre s args ∧ μ s args < n
  post := S.post

/-- Every specification of the context, restricted to calls whose measure (for
that function) is below `n`, is totally correct. -/
def TCtx.ValidBelow (P : Profile) (host : HostSemantics H) (Γ : Ctx H)
    (μ : Nat → Store H → List Val → Nat) (n : Nat) : Prop :=
  ∀ a S, Γ a = some S → TFSpecAt P host a (S.below (μ a) n)

/-- **Guarded total validity of `Γe` relative to `Γi`** with the measure `μ`
(the total module rule): with valid imports, if the exports hold for calls of
measure below `n`, they hold for calls of measure below `n + 1`. -/
def TCtxSat (P : Profile) (host : HostSemantics H) (Γi Γe : Ctx H)
    (μ : Nat → Store H → List Val → Nat) : Prop :=
  ∀ n, TCtx.Valid P host Γi → TCtx.ValidBelow P host Γe μ n → TCtx.ValidBelow P host Γe μ (n + 1)

/-- What a loop body may end with, for total correctness with the variant `V`: a
branch back to the loop must re-establish the invariant with a smaller variant
than `v` (the variant on entry); everything else leaves the loop. -/
def loopPostT (n : Nat) (us : List Val) (Inv : Store H → Frame → List Val → Prop)
    (V : Store H → Frame → List Val → Nat) (v : Nat) (Q : Post H) : Post H := fun s f o =>
  match o with
  | .normal vs => Q s f (.normal (us ++ vs))
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧ Inv s f vs₂ ∧ V s f vs₂ < v
  | .br (l + 1) vs => Q s f (.br l (us ++ vs))
  | .ret vs => Q s f (.ret (us ++ vs))
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail (us ++ vs) a c)

end Silmaril.Wasm.Logic.Hoare
