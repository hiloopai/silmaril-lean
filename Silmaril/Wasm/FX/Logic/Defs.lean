module

public import Silmaril.Wasm.Models.FXV.Defs
public import Silmaril.Wasm.Logic.Core.Defs

/-!
# A handler-aware weakest-precondition calculus for WasmFX: definitions

`WP P host fx s K f code Q` says: from Core store `s`, continuation store `K` and frame `f`,
the FX code `code` **can run** under `StepFX'` (`Silmaril.Wasm.Models.FXV`: CoreFX with
continuation references as values) to a final form whose outcome satisfies `Q`. It is the
existential calculus of `Silmaril.Wasm.Logic.Core` (one run; every profile, every host relation)
carried over to WasmFX, with the outcomes extended by **effects**:

* `normal vs`, `br l vs`, `ret vs`, `trap`, `throw a`: as in `Silmaril.Wasm.Logic.Core.Outcome`,
  with FX values (`FVal`: Core values and continuation references) on the stack;
* `susp E vs x`: the code performs the effect `suspend x` with payload `vs` in the evaluation
  context `E` (`E.plug (vs; suspend x)`), not yet handled;
* `swtch E vs k ct x`: the code performs `switch ct x` to the continuation `k`, payload `vs`, in
  the evaluation context `E`, not yet handled.

Postconditions see the Core store, the continuation store, the frame and the outcome
(`PostFX`). The combinators say how an outcome is seen from outside an evaluation context:

* `seqPost us rest Q`: from inside `us; · ; rest` (values below, code after). Falling through
  continues with `rest`; an effect extends its context by `seq us · rest`;
* `labelPost n k Q`: from inside `label_n{k}`; a branch to the label continues with `k`, an
  effect extends its context by the label;
* `framePost n f Q`: from inside a function frame, returning to the frame `f`; an effect
  extends its context by the frame (an effect can leave a function: the context captured by
  `suspend` includes the frames between the handler and the `suspend`);
* **`handlerPost hs Q`**: from inside the handler frame `handler hs` that `resume` installs.
  This is the **handler rule**. A `suspend x` whose tag is caught by a clause `(on x l)` becomes
  a branch to `l` carrying the payload and the new continuation (slot `K.length`, the captured
  context `E`), exactly the `suspend` step; a `switch` caught by `(on x switch)` continues with
  the target continuation under the same handler; an effect may also be forwarded outward
  (its context then includes the handler, whose clauses the enclosing handler's rule checks
  through `CtxV.Handles`). Values, branches, returns, traps and exceptions pass through.

`corePost K Q` reads a Core postcondition (`Silmaril.Wasm.Logic.Core.Post`) as an FX one, so the
Core calculus and its tactics run on Core code inside FX code.

`OutcomeFX.ofResult r` is the outcome of a Wasm result (values, a thrown exception, a trap),
used by the adequacy theorem (`WP.behaviour`): a proved `WP` gives a behaviour of
`behavioursFX'`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

/-! ## Outcomes -/

/-- How control leaves a piece of FX code. -/
inductive OutcomeFX where
  /-- Fell through with the values `vs`. -/
  | normal (vs : List FVal)
  /-- About to branch to the enclosing label `l` with the values `vs`. -/
  | br (l : Nat) (vs : List FVal)
  /-- About to return with the values `vs`. -/
  | ret (vs : List FVal)
  /-- Trapped. -/
  | trap
  /-- Throwing the exception at address `a`. -/
  | throw (a : Nat)
  /-- Performing `suspend x` with payload `vs` in the (unhandled) context `E`. -/
  | susp (E : CtxV) (vs : List FVal) (x : TagIdx)
  /-- Performing `switch ct x` to the continuation `k` with payload `vs` in the context `E`. -/
  | swtch (E : CtxV) (vs : List FVal) (k : Nat) (ct : TypeIdx) (x : TagIdx)

/-- The code `c` is a final form of outcome `o`. -/
def OutcomeFX.Ends : OutcomeFX → List AdminFX → Prop
  | .normal vs, c => c = fvals vs
  | .br l vs, c => ∃ (x : LabelIdx) (rest : List AdminFX), x.toNat = l ∧
      c = fvals vs ++ .core (.plain (.br x)) :: rest
  | .ret vs, c => ∃ rest : List AdminFX, c = fvals vs ++ .core (.plain .return_) :: rest
  | .trap, c => c = [.core .trap]
  | .throw a, c => c = cthrowing a
  | .susp E vs x, c => c = E.plug (fvals vs ++ [.fx (.suspend x)])
  | .swtch E vs k ct x, c => c = E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)])

/-- The outcome of a Wasm result. -/
def OutcomeFX.ofResult : Result → OutcomeFX
  | .values vs => .normal (liftV vs)
  | .throw a => .throw a
  | .trap => .trap

/-- The continuation store. -/
abbrev Conts := List (Option ContFX)

/-- Postconditions see the Core store, the continuation store, the frame and the outcome. -/
abbrev PostFX (H : Type) := Store H → Conts → Frame → OutcomeFX → Prop

variable {H : Type}

/-- The continuation `cont.new` makes from the function at address `a` (instance `fi`). -/
def newCont (a : Nat) (fi : FuncInst H) : ContFX :=
  ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩

/-- The continuation `cont.bind` makes from `C` by binding the values `vs`. -/
def bindCont (C : ContFX) (vs : List FVal) : ContFX := ⟨fun c => C.plug (fvals vs ++ c)⟩

/-! ## The weakest precondition -/

/-- **The weakest precondition for WasmFX.** From `s`, `K` and `f`, `code` can run under
`StepFX'` to a final form whose outcome satisfies `Q`. -/
def WP (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (s : Store H) (K : Conts)
    (f : Frame) (code : List AdminFX) (Q : PostFX H) : Prop :=
  ∃ (s' : Store H) (K' : Conts) (f' : Frame) (c' : List AdminFX) (o : OutcomeFX),
    StepsFX' P host fx ⟨s, K, f, code⟩ ⟨s', K', f', c'⟩ ∧ o.Ends c' ∧ Q s' K' f' o

/-! ## Outcomes seen from outside an evaluation context -/

/-- The postcondition of `c` in `us; c; rest`: falling through continues with `rest` on the
values; branches and returns carry `us` below; traps and exceptions discard everything; an
effect's context grows by `seq us · rest`. -/
def seqPost (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (us : List FVal)
    (rest : List AdminFX) (Q : PostFX H) : PostFX H := fun s K f o =>
  match o with
  | .normal vs => WP P host fx s K f (fvals (us ++ vs) ++ rest) Q
  | .br l vs => Q s K f (.br l (us ++ vs))
  | .ret vs => Q s K f (.ret (us ++ vs))
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x => Q s K f (.susp (.seq us E rest) vs x)
  | .swtch E vs k ct x => Q s K f (.swtch (.seq us E rest) vs k ct x)

/-- What the code inside `label_n{k}` may end with, seen from outside the label. -/
def labelPost (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (n : Nat)
    (k : List InstrFX) (Q : PostFX H) : PostFX H := fun s K f o =>
  match o with
  | .normal vs => Q s K f (.normal vs)
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧
      WP P host fx s K f (fvals vs₂ ++ k.map InstrFX.toAdmin) Q
  | .br (l + 1) vs => Q s K f (.br l vs)
  | .ret vs => Q s K f (.ret vs)
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x => Q s K f (.susp (.label n k E) vs x)
  | .swtch E vs j ct x => Q s K f (.swtch (.label n k E) vs j ct x)

/-- What the body of a function frame `frame_n{F}` may end with, seen from the caller's frame
`f`: `n` results, falling through or returned; traps and exceptions pass; an effect's context
grows by the frame (with the callee's frame `F` at the effect). -/
def framePost (n : Nat) (f : Frame) (Q : PostFX H) : PostFX H := fun s K F o =>
  match o with
  | .normal vs => vs.length = n ∧ Q s K f (.normal vs)
  | .br _ _ => False
  | .ret vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧ Q s K f (.normal vs₂)
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x => Q s K f (.susp (.frame n F E) vs x)
  | .swtch E vs k ct x => Q s K f (.swtch (.frame n F E) vs k ct x)

/-- **The handler rule's postcondition.** What the code under `handler hs` may end with, seen
from outside the handler: a `suspend x` caught by `(on x l)` branches to `l` with the payload
and the new continuation; a `switch` caught by `(on x switch)` runs the target continuation
under the same handler; either effect may be forwarded outward; everything else passes. -/
def handlerPost (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (hs : List HClause) (Q : PostFX H) : PostFX H := fun s K f o =>
  match o with
  | .normal vs => Q s K f (.normal vs)
  | .br l vs => Q s K f (.br l vs)
  | .ret vs => Q s K f (.ret vs)
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x =>
      (∃ (ta : Nat) (ti : TagInst) (l : LabelIdx), s.tag? (E.frameAt f) x = some (ta, ti) ∧
        ¬ E.Handles ta ∧ hs.find? (fun c => c.tag == ta) = some (.onLabel ta l) ∧
        Q s (K ++ [some ⟨E.plug⟩]) f (.br l.toNat (vs ++ [.cont K.length]))) ∨
      Q s K f (.susp (.handler hs E) vs x)
  | .swtch E vs k ct x =>
      (∃ (C : ContFX) (ta : Nat) (ti : TagInst), K[k]? = some (some C) ∧
        s.tag? (E.frameAt f) x = some (ta, ti) ∧ ¬ E.Handles ta ∧
        hs.find? (fun c => c.tag == ta) = some (.onSwitch ta) ∧
        WP P host fx s (K.set k none ++ [some ⟨E.plug⟩]) f
          [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))] Q) ∨
      Q s K f (.swtch (.handler hs E) vs k ct x)

/-- A Core postcondition read as an FX one, with the continuation store `K` (Core steps do not
change it). Core tail calls have no FX counterpart in this calculus. -/
def corePost (K : Conts) (Q : PostFX H) : Silmaril.Wasm.Logic.Core.Post H := fun s f o =>
  match o with
  | .normal vs => Q s K f (.normal (liftV vs))
  | .br l vs => Q s K f (.br l (liftV vs))
  | .ret vs => Q s K f (.ret (liftV vs))
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .tail _ _ _ => False

end Silmaril.Wasm.FX.Logic
