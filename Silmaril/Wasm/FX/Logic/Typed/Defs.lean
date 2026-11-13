module

public import Silmaril.Wasm.FX.Logic.EveryRun.Defs
public import Silmaril.Wasm.Models.FXResumeT.Defs

/-!
# The every-run WasmFX logic for typed `resume` (`StepFXR`): definitions

`StepFXR` (`Silmaril.Wasm.Models.FXResumeT`) is `StepFX'` with `cont.bind` and `resume` typed: they
take exactly as many values as the continuation type says (`BindArity`, `ResumeArity`). This
module defines the every-run predicates of `Silmaril.Wasm.FX.Logic.EveryRun` over `StepFXR`, without
host calls, with the same stopped outcomes (`Stops`, which reads only the code):

* `SafeR P fx Q n c` (step-indexed, partial correctness) and `HWPR`;
* `TSafeR P fx Q c` (inductive, total correctness) and `TWPR`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Typed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXResumeT (StepFXR)
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Stops)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Step-indexed every-run safety under typed `resume`.** -/
def SafeR (P : Profile) (fx : H → Option FuncFX) (Q : PostFX H) : Nat → ConfigFX H → Prop
  | 0, _ => True
  | n + 1, c => (∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o) ∧
      ∀ c', StepFXR P noHost fx c c' → SafeR P fx Q n c'

/-- The every-run weakest precondition under typed `resume` (partial correctness). -/
def HWPR (P : Profile) (fx : H → Option FuncFX) (s : Store H) (K : Conts) (f : Frame)
    (code : List AdminFX) (Q : PostFX H) : Prop :=
  ∀ n, SafeR P fx Q n ⟨s, K, f, code⟩

/-- **Total every-run safety under typed `resume`.** -/
inductive TSafeR (P : Profile) (fx : H → Option FuncFX) (Q : PostFX H) : ConfigFX H → Prop where
  | intro {c : ConfigFX H}
      (hq : ∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o)
      (hs : ∀ c', StepFXR P noHost fx c c' → TSafeR P fx Q c') : TSafeR P fx Q c

/-- The total-correctness weakest precondition under typed `resume`. -/
def TWPR (P : Profile) (fx : H → Option FuncFX) (s : Store H) (K : Conts) (f : Frame)
    (code : List AdminFX) (Q : PostFX H) : Prop :=
  TSafeR P fx Q ⟨s, K, f, code⟩

end Silmaril.Wasm.FX.Logic.Typed
