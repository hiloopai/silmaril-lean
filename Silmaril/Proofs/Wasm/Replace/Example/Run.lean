module

public import Silmaril.Wasm.Replace.Example.Defs
public import Silmaril.Proofs.Wasm.Replace.Example.Inversion

/-!
# The forced run of an idle function

Invoking `idleFn ls` on a value stack `vs` runs in three steps to `vs` and the store it started
from (`steps_idle`), every run out of the invocation is a prefix of that one (`reach_idle`), so
every run to a result ends there (`steps_result_idle`) and none diverges (`not_diverges_idle`).
Hence two addresses both holding idle functions satisfy `CallSim` (`callSim_idle`).
-/

@[expose] public section

namespace Silmaril.Wasm.Replace.Example

open Silmaril (InfiniteTrace)
open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1 (ValType)

variable {H : Type}

/-- The activation frame of an idle function. -/
def idleFrame (md : ModuleInst) (ls : List Silmaril.Wasm.V1.ValType) : Frame := ⟨ls.map Value.zero, md⟩

/-- The configuration after the invocation step: a frame around an empty label. -/
def entered (s : Store H) (md : ModuleInst) (ls : List Silmaril.Wasm.V1.ValType) (vs : List Value) : Config H :=
  ⟨s, ⟨[], {}⟩, values vs ++ [.frame 0 (idleFrame md ls) [.label 0 [] []]]⟩

/-- The configuration after the label exits: a frame around the empty body. -/
def exited (s : Store H) (md : ModuleInst) (ls : List Silmaril.Wasm.V1.ValType) (vs : List Value) : Config H :=
  ⟨s, ⟨[], {}⟩, values vs ++ [.frame 0 (idleFrame md ls) []]⟩

/-- The final configuration: the value stack, unchanged. -/
def returned (s : Store H) (vs : List Value) : Config H := ⟨s, ⟨[], {}⟩, values vs⟩

section

variable {host : HostSemantics H} {s : Store H} {a : FuncAddr} {md : ModuleInst}
  {ls : List Silmaril.Wasm.V1.ValType} {vs : List Value}

/-- The invocation step. -/
theorem step_entered (found : s.funcs[a.value]? = some (.wasm unitType md (idleFn ls))) :
    Step host (invoke s a vs) (entered s md ls vs) := by
  have h := (Step.invokeWasm (host := host) s ⟨[], {}⟩ a unitType md (idleFn ls) [] found rfl
    (by decide)).context vs []
  simpa [invoke, entered, idleFrame, idleFn, unitType, expression, values] using h

/-- The label step. -/
theorem step_exited : Step host (entered s md ls vs) (exited s md ls vs) := by
  have h := ((Step.pure (host := host) s (idleFrame md ls) (PureStep.labelDone 0 [] [])).frame 0
    ⟨[], {}⟩).context vs []
  simpa [entered, exited, values] using h

/-- The frame step. -/
theorem step_returned : Step host (exited s md ls vs) (returned s vs) := by
  have h := (Step.pure (host := host) s ⟨[], {}⟩
    (PureStep.frameDone 0 (idleFrame md ls) [] rfl)).context vs []
  simpa [exited, returned, values] using h

/-- **The run of an idle function** returns the value stack it was invoked on. -/
theorem steps_idle (found : s.funcs[a.value]? = some (.wasm unitType md (idleFn ls))) :
    Steps host (invoke s a vs) (returned s vs) :=
  (step_entered found).steps.trans (step_exited.steps.trans step_returned.steps)

/-- **Every run out of the invocation** is a prefix of `steps_idle`. -/
theorem reach_idle (found : s.funcs[a.value]? = some (.wasm unitType md (idleFn ls)))
    {d : Config H} (h : Steps host (invoke s a vs) d) :
    d = invoke s a vs ∨ d = entered s md ls vs ∨ d = exited s md ls vs ∨ d = returned s vs := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hstep ih =>
    rcases ih with rfl | rfl | rfl | rfl
    · exact .inr (.inl (step_invoke_inv found hstep))
    · exact .inr (.inr (.inl (step_frame_label_inv hstep)))
    · exact .inr (.inr (.inr (step_frame_nil_inv hstep)))
    · exact absurd hstep not_step_values

/-- `values` is injective: `asValue?` decodes it. -/
theorem values_injective : Function.Injective (values : List Value → List Admin) := by
  intro ws vs h
  have h' : (values ws).map asValue? = (values vs).map asValue? := by rw [h]
  have hid : asValue? ∘ value = some := funext asValue?_value
  have hs : ws.map some = vs.map some := by simpa [values, hid] using h'
  exact List.map_injective_iff.mpr (Option.some_injective _) hs

/-- Rigid code after a value stack is not a result. -/
theorem values_append_ne_result {X : List Admin} (hrig : Rigid s X) (r : Result) :
    values vs ++ X ≠ result r := by
  simpa [plug_seq, plug_hole] using hrig.plug_ne_result (.seq vs .hole []) r

/-- The first three configurations of the run are not results. -/
theorem code_ne_result (found : s.funcs[a.value]? = some (.wasm unitType md (idleFn ls)))
    (r : Result) :
    (invoke s a vs).code ≠ result r ∧ (entered s md ls vs).code ≠ result r ∧
      (exited s md ls vs).code ≠ result r := by
  have hsat : Saturated s a [] := ⟨_, found, rfl⟩
  exact ⟨values_append_ne_result (X := [.invoke a]) (Rigid.invoke hsat) r,
    values_append_ne_result (Rigid.frame (s := s) _ _ _) r,
    values_append_ne_result (Rigid.frame (s := s) _ _ _) r⟩

/-- **Every run to a result** out of the invocation ends where `steps_idle` does. -/
theorem steps_result_idle (found : s.funcs[a.value]? = some (.wasm unitType md (idleFn ls)))
    {s₂ : Store H} {f : Frame} {r : Result} (h : Steps host (invoke s a vs) ⟨s₂, f, result r⟩) :
    s₂ = s ∧ r = .values vs := by
  obtain ⟨h₀, h₁, h₂⟩ := code_ne_result (vs := vs) found r
  rcases reach_idle found h with he | he | he | he
  · exact absurd (congrArg Config.code he).symm h₀
  · exact absurd (congrArg Config.code he).symm h₁
  · exact absurd (congrArg Config.code he).symm h₂
  · have hcode : result r = result (.values vs) := congrArg Config.code he
    have hr : r = .values vs := by
      cases r with
      | values ws => exact congrArg Result.values (values_injective hcode)
      | trap => exact absurd hcode.symm (by simp [result, values])
    exact ⟨congrArg Config.store he, hr⟩

/-- **The invocation does not diverge**: its run stops after three steps. -/
theorem not_diverges_idle (found : s.funcs[a.value]? = some (.wasm unitType md (idleFn ls))) :
    ¬ Diverges host (invoke s a vs) := by
  intro hdv
  obtain ⟨c₁, h₁, hd₁⟩ := hdv.unfold
  obtain ⟨c₂, h₂, hd₂⟩ := hd₁.unfold
  obtain ⟨c₃, h₃, hd₃⟩ := hd₂.unfold
  obtain ⟨c₄, h₄, -⟩ := hd₃.unfold
  have e₁ : c₁ = entered s md ls vs := step_invoke_inv found h₁
  have e₂ : c₂ = exited s md ls vs := step_frame_label_inv (e₁ ▸ h₂)
  have e₃ : c₃ = returned s vs := step_frame_nil_inv (e₂ ▸ h₃)
  exact not_step_values (e₃ ▸ h₄)

/-- **`CallSim` for idle functions.** If `a` holds an idle function before and after the
replacement, the replacement is invisible at `a`: both runs return the value stack and keep the
store. -/
theorem callSim_idle {ls ls' : List Silmaril.Wasm.V1.ValType} {md' : ModuleInst} {b : FuncAddr}
    (found : s.funcs[a.value]? = some (.wasm unitType md (idleFn ls)))
    (found' : (s.replaceFunc a b).funcs[a.value]? = some (.wasm unitType md' (idleFn ls'))) :
    CallSim host a b s := by
  refine ⟨fun vs s₂ r h => ?_, fun vs s₂' r h => ?_, fun vs => ?_⟩
  · obtain ⟨rfl, rfl⟩ := steps_result_idle found h
    exact steps_idle found'
  · obtain ⟨rfl, rfl⟩ := steps_result_idle found' h
    exact ⟨s, rfl, steps_idle found⟩
  · exact iff_of_false (not_diverges_idle found) (not_diverges_idle found')

end

end Silmaril.Wasm.Replace.Example
