module

public import Silmaril.Wasm.FX.Logic.EveryRun.Defs

/-!
# Function specifications for WasmFX functions: definitions

The module rules of the every-run Core logic (`Silmaril.Wasm.Logic.Hoare`: `FSpec`, `FSpecAt`,
`Ctx`, `CtxSat`) for FX functions under `StepFX'` without host calls
(`Silmaril.Wasm.FX.Logic.EveryRun`).

* `FSpec H`: a precondition on the Core store, the continuation store and the (Core) arguments
  (FX functions take Core values: `StepFX'.invoke`), and a postcondition on those and the final
  stores and outcome.
* `callPost f vs₀ R`: the outcome of a call seen by the caller in frame `f` with the values
  `vs₀` below the arguments: it falls through with the results on top of `vs₀`, traps, throws,
  or performs an unhandled effect (`suspend` / `switch`) whose context the caller sees as is;
  a branch or `return` never leaves a call.
* `InvO R`: `R` does not tell plug-equal effect contexts apart (`Inv`, without the frame).
* **`FSpecAt P fx n a S`**: the specification holds for `n` steps at address `a`: from every
  pre-state, in every calling frame, below every caller stack and through every `CALL_REF` form,
  the call is `Safe` for `n` steps with the call postcondition. `FSpecT` is the total version
  (`TSafe`).
* `bodyPost`: the postcondition a function body must satisfy inside its label and frame.
* `Ctx`, `Ctx.ValidAt`, `Ctx.Valid`, **`CtxSat Γi Γe`** (guarded validity: if all of `Γi` and
  `Γe` hold for `n` steps, `Γe` holds for `n + 1`), as in `Silmaril.Wasm.Logic.Hoare`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Module

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Safe TSafe Inv safeJ totJ)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **A function specification** for an FX function. -/
structure FSpec (H : Type) where
  /-- The precondition: Core store, continuation store, arguments. -/
  pre : Store H → Conts → List Val → Prop
  /-- The postcondition: the pre-state and arguments, the final stores and the outcome. -/
  post : Store H → Conts → List Val → Store H → Conts → OutcomeFX → Prop

/-- The outcome of a call seen by the caller in frame `f`, with `vs₀` below the arguments. -/
def callPost (f : Frame) (vs₀ : List FVal) (R : Store H → Conts → OutcomeFX → Prop) :
    PostFX H := fun s K f' o => f' = f ∧
  match o with
  | .normal vs => ∃ res, vs = vs₀ ++ res ∧ R s K (.normal res)
  | .br _ _ => False
  | .ret _ => False
  | .trap => R s K .trap
  | .throw a => R s K (.throw a)
  | .susp E vs x => R s K (.susp E vs x)
  | .swtch E vs k ct x => R s K (.swtch E vs k ct x)

/-- `R` does not tell plug-equal effect contexts apart. -/
def InvO (R : Store H → Conts → OutcomeFX → Prop) : Prop :=
  Inv (fun s K (_ : Frame) o => R s K o)

/-- The code of a call through `CALL_REF` form `c` of the function at address `a`. -/
def callCode (vs₀ : List FVal) (args : List Val) (a : Nat) (c : Admin) : List AdminFX :=
  fvals (vs₀ ++ liftV args ++ [.val (.ref (.func a))]) ++ [.core c]

/-- **A function specification holds for `n` steps** at address `a`. -/
def FSpecAt (P : Profile) (fx : H → Option FuncFX) (n : Nat) (a : Nat) (S : FSpec H) : Prop :=
  ∀ s K args, S.pre s K args → ∀ (f : Frame) (vs₀ : List FVal) (c : Admin), c.IsCallRef →
    Safe P fx (callPost f vs₀ (S.post s K args)) n ⟨s, K, f, callCode vs₀ args a c⟩

/-- **A function specification with total correctness** at address `a`. -/
def FSpecT (P : Profile) (fx : H → Option FuncFX) (a : Nat) (S : FSpec H) : Prop :=
  ∀ s K args, S.pre s K args → ∀ (f : Frame) (vs₀ : List FVal) (c : Admin), c.IsCallRef →
    TSafe P fx (callPost f vs₀ (S.post s K args)) ⟨s, K, f, callCode vs₀ args a c⟩

/-- The postcondition of a function body with `N` results inside its label and frame, for `n`
steps after the label. -/
def bodyPost (P : Profile) (fx : H → Option FuncFX) (N : Nat) (f : Frame) (vs₀ : List FVal)
    (Q : PostFX H) (n : Nat) : PostFX H :=
  EveryRun.labelPost (safeJ P fx (EveryRun.framePost N f vs₀ Q) n) N [] []
      (EveryRun.framePost N f vs₀ Q)

/-- The postcondition of a function body, total correctness. -/
def bodyPostT (P : Profile) (fx : H → Option FuncFX) (N : Nat) (f : Frame) (vs₀ : List FVal)
    (Q : PostFX H) : PostFX H :=
  EveryRun.labelPost (totJ P fx (EveryRun.framePost N f vs₀ Q)) N [] []
    (EveryRun.framePost N f vs₀ Q)

/-- A **specification context**: specifications for some function addresses. -/
abbrev Ctx (H : Type) := Nat → Option (FSpec H)

/-- Every specification of the context holds for `n` steps. -/
def Ctx.ValidAt (P : Profile) (fx : H → Option FuncFX) (n : Nat) (Γ : Ctx H) : Prop :=
  ∀ a S, Γ a = some S → FSpecAt P fx n a S

/-- Every specification of the context holds. -/
def Ctx.Valid (P : Profile) (fx : H → Option FuncFX) (Γ : Ctx H) : Prop :=
  ∀ n, Ctx.ValidAt P fx n Γ

/-- Every specification of `Γ` is in `Γ'`. -/
def Ctx.Le (Γ Γ' : Ctx H) : Prop := ∀ a S, Γ a = some S → Γ' a = some S

/-- Two contexts side by side (the first wins where both specify). -/
def Ctx.union (Γ Γ' : Ctx H) : Ctx H := fun a => (Γ a).orElse fun _ => Γ' a

/-- **Guarded validity of `Γe` relative to `Γi`.** -/
def CtxSat (P : Profile) (fx : H → Option FuncFX) (Γi Γe : Ctx H) : Prop :=
  ∀ n, Ctx.ValidAt P fx n Γi → Ctx.ValidAt P fx n Γe → Ctx.ValidAt P fx (n + 1) Γe

end Silmaril.Wasm.FX.Logic.Module
