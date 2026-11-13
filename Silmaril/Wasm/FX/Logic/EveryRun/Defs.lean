module

public import Silmaril.Wasm.FX.Logic.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

/-!
# An every-run program logic for WasmFX: definitions

`Silmaril.Wasm.Logic.Hoare` is an every-run, step-indexed program logic for Core 3.0. This module
ports it to WasmFX: `StepFX'` (`Silmaril.Wasm.Models.FXV`, CoreFX with continuation references as
values), without host calls (`noHost`), for every profile and every FX function table.

**Stopped code.** `Stops s f o c` says that the code `c` has stopped with the outcome `o`
(`Silmaril.Wasm.FX.Logic.OutcomeFX`): values, a branch or `return` with the values below it, an
exact `trap` or thrown exception, or an **unhandled effect**: `suspend x` (or `switch ct x`)
in an evaluation context `E` that has no handler for the tag `x` resolves to (`Unhandled`).

**Safety.** `Safe P fx Q n c`: for `n` steps, every reachable configuration that has stopped
satisfies `Q`, for **every** outcome it stops with. Unlike Core's `Hoare.Safe` it does not ask
for progress: `StepFX'` gets stuck where the reference semantics does too (a `suspend` may take
any suffix of the values in front of it as payload, `Silmaril.Wasm.Models.FXAsyncSus`, and the
shorter payloads are stuck at the handler's label), and a stuck run has no behaviour. So `Safe`
is partial correctness for behaviours: every result of a run satisfies `Q`
(`Silmaril.Wasm.FX.Logic.EveryRun.Thms`). A stopped code can have several outcomes (a `suspend`
under the values `V` stops with every split of `V`), and `Safe` asks for all of them.

`HWP` (every index) is the every-run weakest precondition, partial correctness. `TSafe` is the
inductive version and `TWP` the **total-correctness** weakest precondition: every run also
terminates (no infinite `StepFX'` trace).

**Outcomes seen from outside.** The postconditions of the context rules take a predicate `J`
on the code a context continues with (`Safe P fx Q k` for the step-indexed rules, `TSafe P fx Q`
for the total ones):

* `seqPost J c₂ Q`: from `c₁` in `c₁ ++ c₂`; falling through continues with `c₂`;
* `labelPost J n k us Q`: from inside `label_n{k}` with the values `us` below it; a branch to
  the label continues with `k` for **every** split of the values whose top part has the
  label's arity (none if too few);
* `framePost n f us Q`: from inside a function frame, returning to the frame `f`;
* **`handlerPost J hs us Q`**: from inside `handler hs`, the handler rule. A `suspend x` caught by
  the first clause for `x`, `(on x l)`, becomes a branch to `l` with the payload and the new
  continuation (slot `K.length`, holding the captured context); a `switch` caught by
  `(on x switch)` continues with the target continuation under the same handler; an effect that
  `hs` does not handle stops outside the handler.

Effect outcomes carry an evaluation context, and contexts that plug alike are different terms.
`Inv Q` says that `Q` does not tell such contexts apart; the context rules ask it of the
outer postcondition (`Inv` holds of every postcondition built here, `Thms`).

A Silmaril addition, built on
`Silmaril.Wasm.Logic.Hoare` (design) and `Silmaril.Wasm.FX.Logic` (outcomes).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Stopped code -/

/-- No handler frame of `E` has a clause for the tag that `x` resolves to at the hole. -/
def Unhandled (s : Store H) (f : Frame) (E : CtxV) (x : TagIdx) : Prop :=
  ∀ ta ti, s.tag? (E.frameAt f) x = some (ta, ti) → ¬ E.Handles ta

/-- `suspend x` with the payload `vs`. -/
def suspCode (vs : List FVal) (x : TagIdx) : List AdminFX := fvals vs ++ [.fx (.suspend x)]

/-- `switch ct x` to the continuation `k` with the payload `vs`. -/
def switchCode (vs : List FVal) (k : Nat) (ct : TypeIdx) (x : TagIdx) : List AdminFX :=
  fvals vs ++ [.contRef k, .fx (.switch ct x)]

/-- **The code `c` has stopped with outcome `o`**, at store `s` and frame `f`. -/
def Stops (s : Store H) (f : Frame) : OutcomeFX → List AdminFX → Prop
  | .normal vs, c => c = fvals vs
  | .br l vs, c => ∃ (x : LabelIdx) (rest : List AdminFX), x.toNat = l ∧
      c = fvals vs ++ .core (.plain (.br x)) :: rest
  | .ret vs, c => ∃ rest : List AdminFX, c = fvals vs ++ .core (.plain .return_) :: rest
  | .trap, c => c = [.core .trap]
  | .throw a, c => c = cthrowing a
  | .susp E vs x, c => c = E.plug (suspCode vs x) ∧ Unhandled s f E x
  | .swtch E vs k ct x, c => c = E.plug (switchCode vs k ct x) ∧ Unhandled s f E x

/-! ## Safety and the weakest preconditions -/

/-- **Step-indexed every-run safety** (without progress): for `n` steps, every reachable
stopped configuration satisfies `Q`, for every outcome it stops with. -/
def Safe (P : Profile) (fx : H → Option FuncFX) (Q : PostFX H) : Nat → ConfigFX H → Prop
  | 0, _ => True
  | n + 1, c => (∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o) ∧
      ∀ c', StepFX' P noHost fx c c' → Safe P fx Q n c'

/-- **The every-run weakest precondition** (partial correctness). -/
def HWP (P : Profile) (fx : H → Option FuncFX) (s : Store H) (K : Conts) (f : Frame)
    (code : List AdminFX) (Q : PostFX H) : Prop :=
  ∀ n, Safe P fx Q n ⟨s, K, f, code⟩

/-- **Total every-run safety**: the inductive version; every run also terminates. -/
inductive TSafe (P : Profile) (fx : H → Option FuncFX) (Q : PostFX H) : ConfigFX H → Prop where
  | intro {c : ConfigFX H}
      (hq : ∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o)
      (hs : ∀ c', StepFX' P noHost fx c c' → TSafe P fx Q c') : TSafe P fx Q c

/-- **The total-correctness weakest precondition.** -/
def TWP (P : Profile) (fx : H → Option FuncFX) (s : Store H) (K : Conts) (f : Frame)
    (code : List AdminFX) (Q : PostFX H) : Prop :=
  TSafe P fx Q ⟨s, K, f, code⟩

/-! ## Postconditions that do not tell plug-equal contexts apart -/

/-- `Q` sees an effect's context only through what it plugs to. -/
def Inv (Q : PostFX H) : Prop :=
  (∀ s K f (E E' : CtxV) vs x, E.plug (suspCode vs x) = E'.plug (suspCode vs x) →
      Q s K f (.susp E vs x) → Q s K f (.susp E' vs x)) ∧
  (∀ s K f (E E' : CtxV) vs k ct x, E.plug (switchCode vs k ct x) = E'.plug (switchCode vs k ct x) →
      Q s K f (.swtch E vs k ct x) → Q s K f (.swtch E' vs k ct x))

/-! ## Outcomes seen from outside a context -/

/-- The postcondition of `c₁` in `c₁ ++ c₂`. -/
def seqPost (J : Store H → Conts → Frame → List AdminFX → Prop) (c₂ : List AdminFX)
    (Q : PostFX H) : PostFX H := fun s K f o =>
  match o with
  | .normal vs => J s K f (fvals vs ++ c₂)
  | .br l vs => Q s K f (.br l vs)
  | .ret vs => Q s K f (.ret vs)
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x => Q s K f (.susp (.seq [] E c₂) vs x)
  | .swtch E vs k ct x => Q s K f (.swtch (.seq [] E c₂) vs k ct x)

/-- What the body of `label_n{k}`, sitting on the values `us`, may stop with, seen from outside
the label. -/
def labelPost (J : Store H → Conts → Frame → List AdminFX → Prop) (n : Nat) (k : List InstrFX)
    (us : List FVal) (Q : PostFX H) : PostFX H := fun s K f o =>
  match o with
  | .normal vs => Q s K f (.normal (us ++ vs))
  | .br 0 vs => ∀ vs₁ vs₂, vs = vs₁ ++ vs₂ → vs₂.length = n →
      J s K f (fvals (us ++ vs₂) ++ k.map InstrFX.toAdmin)
  | .br (l + 1) vs => Q s K f (.br l (us ++ vs))
  | .ret vs => Q s K f (.ret (us ++ vs))
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x => Q s K f (.susp (.seq us (.label n k E) []) vs x)
  | .swtch E vs j ct x => Q s K f (.swtch (.seq us (.label n k E) []) vs j ct x)

/-- What the body of `frame_n{F}`, sitting on the values `us`, may stop with, seen from the
caller's frame `f`. A branch out of a frame is stuck. -/
def framePost (n : Nat) (f : Frame) (us : List FVal) (Q : PostFX H) : PostFX H := fun s K F o =>
  match o with
  | .normal vs => vs.length = n → Q s K f (.normal (us ++ vs))
  | .br _ _ => True
  | .ret vs => ∀ vs₁ vs₂, vs = vs₁ ++ vs₂ → vs₂.length = n → Q s K f (.normal (us ++ vs₂))
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x => Q s K f (.susp (.seq us (.frame n F E) []) vs x)
  | .swtch E vs k ct x => Q s K f (.swtch (.seq us (.frame n F E) []) vs k ct x)

/-- **The handler rule's postcondition**: what the code under `handler hs`, sitting on the values
`us`, may stop with, seen from outside the handler. -/
def handlerPost (J : Store H → Conts → Frame → List AdminFX → Prop) (hs : List HClause)
    (us : List FVal) (Q : PostFX H) : PostFX H := fun s K f o =>
  match o with
  | .normal vs => Q s K f (.normal (us ++ vs))
  | .br l vs => Q s K f (.br l (us ++ vs))
  | .ret vs => Q s K f (.ret (us ++ vs))
  | .trap => Q s K f .trap
  | .throw a => Q s K f (.throw a)
  | .susp E vs x =>
      (∀ ta ti (l : LabelIdx), s.tag? (E.frameAt f) x = some (ta, ti) → ¬ E.Handles ta →
        hs.find? (fun c => c.tag == ta) = some (.onLabel ta l) →
        Q s (K ++ [some ⟨E.plug⟩]) f (.br l.toNat (us ++ vs ++ [.cont K.length]))) ∧
      (Unhandled s f (.handler hs E) x → Q s K f (.susp (.seq us (.handler hs E) []) vs x))
  | .swtch E vs k ct x =>
      (∀ (C : ContFX) ta ti, K[k]? = some (some C) → s.tag? (E.frameAt f) x = some (ta, ti) →
        ¬ E.Handles ta → hs.find? (fun c => c.tag == ta) = some (.onSwitch ta) →
        J s (K.set k none ++ [some ⟨E.plug⟩]) f
          (fvals us ++ [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))])) ∧
      (Unhandled s f (.handler hs E) x →
        Q s K f (.swtch (.seq us (.handler hs E) []) vs k ct x))

/-- The continuation predicate of the step-indexed rules: safe for `k` steps. -/
def safeJ (P : Profile) (fx : H → Option FuncFX) (Q : PostFX H) (k : Nat) :
    Store H → Conts → Frame → List AdminFX → Prop :=
  fun s K f c => Safe P fx Q k ⟨s, K, f, c⟩

/-- The continuation predicate of the total rules. -/
def totJ (P : Profile) (fx : H → Option FuncFX) (Q : PostFX H) :
    Store H → Conts → Frame → List AdminFX → Prop :=
  fun s K f c => TSafe P fx Q ⟨s, K, f, c⟩

end Silmaril.Wasm.FX.Logic.EveryRun
