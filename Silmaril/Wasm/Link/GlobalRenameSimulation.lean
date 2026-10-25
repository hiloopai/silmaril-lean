module

public import Silmaril.Wasm.Link.GlobalRenameLeaf
public import Silmaril.Wasm.Link.SimulationDefs

/-! # Core executions under global-address renaming

Global renaming leaves instructions and runtime values unchanged. It changes
module global-address tables, including those in nested administrative frames.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.GlobalRenameSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open GlobalPermutation

variable {H : Type} {P : Profile}

mutual
def admin (p : Nat ≃ Nat) : Admin → Admin
  | .label n cont body => .label n cont (admins p body)
  | .handler n catches body => .handler n catches (admins p body)
  | .frame n f body => .frame n (frame p f) (admins p body)
  | .plain i => .plain i
  | .ref r => .ref r
  | .callRefType d => .callRefType d
  | .returnCallRefType d => .returnCallRefType d
  | .trap => .trap

def admins (p : Nat ≃ Nat) : List Admin → List Admin
  | [] => []
  | a :: rest => admin p a :: admins p rest
end

@[simp] theorem admin_value (p : Nat ≃ Nat) (v : Val) :
    admin p v.toAdmin = v.toAdmin := by
  cases v with
  | num n => cases n with | mk t b => cases t <;> rfl
  | vec b => rfl
  | ref r => rfl

@[simp] theorem admins_append (p : Nat ≃ Nat) (xs ys : List Admin) :
    admins p (xs ++ ys) = admins p xs ++ admins p ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, admins, ih]

@[simp] theorem admins_vals (p : Nat ≃ Nat) (vs : List Val) :
    admins p (vals vs) = vals vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons, admins, admin_value]
    exact congrArg (List.cons v.toAdmin) ih

@[simp] theorem admins_expression (p : Nat ≃ Nat) (code : List Instr) :
    admins p (expression code) = expression code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    simp only [expression, List.map_cons, admins, admin]
    exact congrArg (List.cons (.plain i)) ih

@[simp] theorem admins_refs (p : Nat ≃ Nat) (refs : List Ref) :
    admins p (refs.map Admin.ref) = refs.map Admin.ref := by
  induction refs with
  | nil => rfl
  | cons r refs ih =>
    simp only [List.map_cons, admins, admin]
    exact congrArg (List.cons (.ref r)) ih

@[simp] theorem admins_length (p : Nat ≃ Nat) (code : List Admin) :
    (admins p code).length = code.length := by
  induction code with
  | nil => rfl
  | cons i code ih => simp only [admins, List.length_cons, ih]

def config (p : Nat ≃ Nat) (targetStore : Store H) (source : Config H) : Config H :=
  ⟨targetStore, frame p source.frame, admins p source.code⟩

theorem parametric {p : Nat ≃ Nat} {code out : List Admin}
    (step : ParametricStep code out) : ParametricStep (admins p code) (admins p out) := by
  have original := step
  cases step <;> simpa only [admins, admin, admin_value, constI32] using original

theorem numeric {p : Nat ≃ Nat} {code out : List Admin}
    (step : NumericStep P code out) : NumericStep P (admins p code) (admins p out) := by
  have original := step
  cases step <;> simpa only [admins, admin, admin_value, constI32] using original

theorem vector {p : Nat ≃ Nat} {code out : List Admin}
    (step : VectorStep P code out) : VectorStep P (admins p code) (admins p out) := by
  have original := step
  cases step <;> simpa only [admins, admin, admin_value, constI32] using original

theorem variable_code {p : Nat ≃ Nat} {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : VariableStep ⟨s,f,code⟩ ⟨s',f',out⟩) :
    admins p code = code ∧ admins p out = out := by
  cases step <;> simp only [admins, admin, admin_value, and_self]

theorem reference_code {p : Nat ≃ Nat} {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : RefStep ⟨s,f,code⟩ ⟨s',f',out⟩) :
    admins p code = code ∧ admins p out = out := by
  cases step <;> simp only [admins, admin, admin_value, constI32, and_self]

theorem aggregate_code {p : Nat ≃ Nat} {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : AggregateStep ⟨s,f,code⟩ ⟨s',f',out⟩) :
    admins p code = code ∧ admins p out = out := by
  cases step <;> simp only [admins_append, admins_vals, admins_refs, admins, admin, admin_value, constI32, and_self]

theorem table_code {p : Nat ≃ Nat} {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : TableStep P ⟨s,f,code⟩ ⟨s',f',out⟩) :
    admins p code = code ∧ admins p out = out := by
  cases step <;> simp only [admins, admin, admin_value, constI32, and_self]

theorem memory_code {p : Nat ≃ Nat} {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : MemoryStep P ⟨s,f,code⟩ ⟨s',f',out⟩) :
    admins p code = code ∧ admins p out = out := by
  cases step <;> simp only [admins, admin, admin_value, constI32, load8u, store8, and_self]

theorem admins_ne_nil {p : Nat ≃ Nat} {code : List Admin} (nonempty : code ≠ []) :
    admins p code ≠ [] := by
  intro empty
  have := congrArg List.length empty
  rw [admins_length, List.length_nil, List.length_eq_zero_iff] at this
  exact nonempty this

theorem call_ref_fixed {p : Nat ≃ Nat} {a : Admin} (call : a.IsCallRef) : admin p a = a := by
  cases a <;> first | rfl | cases call

theorem return_call_ref_fixed {p : Nat ≃ Nat} {a : Admin}
    (call : a.IsReturnCallRef) : admin p a = a := by
  cases a <;> first | rfl | cases call

theorem ret_to_call_in_fixed (p : Nat ≃ Nat) (m : ModuleInst) {a : Admin}
    (call : a.IsReturnCallRef) :
    admin p (a.retToCallIn m) = a.retToCallIn (moduleView p m) := by
  cases a with
  | plain i =>
    cases i <;> try rfl
    simp only [Admin.retToCallIn, moduleView]
    split <;> rfl
  | returnCallRefType d => rfl
  | _ => cases call

/-- Renaming global addresses commutes with each actual host-free reduction.
No configuration typing or assumed execution correspondence is needed. -/
theorem step {source sourceFinal : Config H} (sourceStep : Step P Simulation.noHost source sourceFinal) :
    ∀ {p : Nat ≃ Nat} {targetStore : Store H}, Renamed p source.store targetStore →
      ∃ targetFinalStore, Step P Simulation.noHost (config p targetStore source)
        (config p targetFinalStore sourceFinal) ∧ Renamed p sourceFinal.store targetFinalStore := by
  induction sourceStep
  all_goals intro p targetStore stores
  case parametric h => exact ⟨targetStore, .parametric (parametric h), stores⟩
  case numeric h => exact ⟨targetStore, .numeric (numeric h), stores⟩
  case vector h => exact ⟨targetStore, .vector (vector h), stores⟩
  case «variable» c c' h =>
    obtain ⟨s,f,code⟩ := c
    obtain ⟨s',f',out⟩ := c'
    obtain ⟨target', reduced, renamed⟩ := variable_step stores h
    have fixed := variable_code (p := p) h
    exact ⟨target', by simpa only [config, fixed.1, fixed.2] using Step.variable reduced, renamed⟩
  case reference c c' h =>
    obtain ⟨s,f,code⟩ := c
    obtain ⟨s',f',out⟩ := c'
    have original := h
    have fixed := reference_code (p := p) h
    cases h
    all_goals
      have reduced := reference_step stores original
      exact ⟨targetStore, by simpa only [config, fixed.1, fixed.2] using Step.reference reduced, stores⟩
  case aggregate c c' h =>
    obtain ⟨s,f,code⟩ := c
    obtain ⟨s',f',out⟩ := c'
    obtain ⟨target', reduced, renamed⟩ := aggregate_step stores h
    have fixed := aggregate_code (p := p) h
    exact ⟨target', by simpa only [config, fixed.1, fixed.2] using Step.aggregate reduced, renamed⟩
  case table c c' h =>
    obtain ⟨s,f,code⟩ := c
    obtain ⟨s',f',out⟩ := c'
    obtain ⟨target', reduced, renamed⟩ := table_step stores h
    have fixed := table_code (p := p) h
    exact ⟨target', by simpa only [config, fixed.1, fixed.2] using Step.table reduced, renamed⟩
  case memory c c' h =>
    obtain ⟨s,f,code⟩ := c
    obtain ⟨s',f',out⟩ := c'
    obtain ⟨target', reduced, renamed⟩ := memory_step stores h
    have fixed := memory_code (p := p) h
    exact ⟨target', by simpa only [config, fixed.1, fixed.2] using Step.memory reduced, renamed⟩
  case ctxtInstrs _ nonempty ih =>
    obtain ⟨target', reduced, renamed⟩ := ih stores
    refine ⟨target', ?_, renamed⟩
    simpa only [config, admins_append, admins_vals] using Step.ctxtInstrs reduced
      (nonempty.imp_right admins_ne_nil)
  case ctxtLabel _ ih =>
    obtain ⟨target', reduced, renamed⟩ := ih stores
    exact ⟨target', by simpa only [config, admins, admin] using Step.ctxtLabel reduced, renamed⟩
  case ctxtHandler _ ih =>
    obtain ⟨target', reduced, renamed⟩ := ih stores
    exact ⟨target', by simpa only [config, admins, admin] using Step.ctxtHandler reduced, renamed⟩
  case ctxtFrame _ ih =>
    obtain ⟨target', reduced, renamed⟩ := ih stores
    exact ⟨target', by simpa only [config, admins, admin] using Step.ctxtFrame reduced, renamed⟩
  case callRefHost _ _ _ _ _ impossible => exact False.elim impossible
  case callRefHostDiv _ _ _ _ _ impossible => exact False.elim impossible
  all_goals
    simp only [config, admins_append, admins_vals, admins_expression, admins, admin, admin_value, constI32]
  case block hbt hm => exact ⟨targetStore, .block hbt hm, stores⟩
  case loop hbt hm => exact ⟨targetStore, .loop hbt hm, stores⟩
  case ifTrue hc => exact ⟨targetStore, .ifTrue hc, stores⟩
  case ifFalse => exact ⟨targetStore, .ifFalse, stores⟩
  case labelVals => exact ⟨targetStore, .labelVals, stores⟩
  case brLabelZero hl hn => exact ⟨targetStore, .brLabelZero hl hn, stores⟩
  case brLabelSucc hl => exact ⟨targetStore, .brLabelSucc hl, stores⟩
  case brHandler => exact ⟨targetStore, .brHandler, stores⟩
  case brIfTrue hc => exact ⟨targetStore, .brIfTrue hc, stores⟩
  case brIfFalse => exact ⟨targetStore, .brIfFalse, stores⟩
  case brTableLt hi => exact ⟨targetStore, .brTableLt hi, stores⟩
  case brTableGe hi => exact ⟨targetStore, .brTableGe hi, stores⟩
  case brOnNullNull => exact ⟨targetStore, .brOnNullNull, stores⟩
  case brOnNullAddr hv => exact ⟨targetStore, .brOnNullAddr hv, stores⟩
  case brOnNonNullNull => exact ⟨targetStore, .brOnNonNullNull, stores⟩
  case brOnNonNullAddr hv => exact ⟨targetStore, .brOnNonNullAddr hv, stores⟩
  case brOnCastSucceed h => exact ⟨targetStore, .brOnCastSucceed (stores.refOk h), stores⟩
  case brOnCastFail h => exact ⟨targetStore, .brOnCastFail (fun hh => h (stores.symm.refOk hh)), stores⟩
  case brOnCastFailSucceed h => exact ⟨targetStore, .brOnCastFailSucceed (stores.refOk h), stores⟩
  case brOnCastFailFail h => exact ⟨targetStore, .brOnCastFailFail (fun hh => h (stores.symm.refOk hh)), stores⟩
  case call s f x a fi hx hf =>
    refine ⟨targetStore, ?_, stores⟩
    simpa only [function] using
      (Step.call (P := P) (host := Simulation.noHost) (s := targetStore) (f := frame p f)
        (fi := function p fi) hx (stores.function_lookup hf))
  case callRefNull s f c hc =>
    refine ⟨targetStore, ?_, stores⟩
    simpa only [call_ref_fixed hc] using
      (Step.callRefNull (P := P) (host := Simulation.noHost) (s := targetStore) (f := frame p f) hc)
  case callRefFunc s f c vs a fi ps rs fn hc hf he hn hcode =>
    refine ⟨targetStore, ?_, stores⟩
    simpa only [frame, function, hcode, Frame.forCall, moduleView, call_ref_fixed hc] using
      (Step.callRefFunc (P := P) (host := Simulation.noHost) (s := targetStore) (f := frame p f)
        (fi := function p fi) hc (stores.function_lookup hf) he hn hcode)
  case returnCall s f x a fi hx hf =>
    refine ⟨targetStore, ?_, stores⟩
    simpa only [function] using
      (Step.returnCall (P := P) (host := Simulation.noHost) (s := targetStore) (f := frame p f)
        (fi := function p fi) hx (stores.function_lookup hf))
  case returnCallRefLabel hc =>
    exact ⟨targetStore, by simpa only [return_call_ref_fixed hc] using Step.returnCallRefLabel hc, stores⟩
  case returnCallRefHandler hc =>
    exact ⟨targetStore, by simpa only [return_call_ref_fixed hc] using Step.returnCallRefHandler hc, stores⟩
  case returnCallRefFrameNull hc =>
    exact ⟨targetStore, by simpa only [return_call_ref_fixed hc] using Step.returnCallRefFrameNull hc, stores⟩
  case returnCallRefFrameAddr hc hf he hn =>
    exact ⟨targetStore, by simpa only [return_call_ref_fixed hc, ret_to_call_in_fixed p _ hc, frame] using
      Step.returnCallRefFrameAddr hc (stores.function_lookup hf) he hn, stores⟩
  case callIndirect => exact ⟨targetStore, .callIndirect, stores⟩
  case returnCallIndirect => exact ⟨targetStore, .returnCallIndirect, stores⟩
  case frameVals hn => exact ⟨targetStore, .frameVals hn, stores⟩
  case returnFrame hn => exact ⟨targetStore, .returnFrame hn, stores⟩
  case returnLabel => exact ⟨targetStore, .returnLabel, stores⟩
  case returnHandler => exact ⟨targetStore, .returnHandler, stores⟩
  case throw s f x vs ta ti ts ht he hn =>
    have exns : s.exns = targetStore.exns := stores.exns
    refine ⟨_, ?_, stores.addExn _⟩
    simpa only [throwing, exns] using Step.throw
      (P := P) (host := Simulation.noHost) (s := targetStore) (f := frame p f)
      (by simpa only [Store.tag?, frame, moduleView, ← stores.tags] using ht) he hn
  case throwRefNull => exact ⟨targetStore, .throwRefNull, stores⟩
  case throwRefInstrs hne => exact ⟨targetStore, .throwRefInstrs (hne.imp_right admins_ne_nil), stores⟩
  case throwRefLabel => exact ⟨targetStore, .throwRefLabel, stores⟩
  case throwRefFrame => exact ⟨targetStore, .throwRefFrame, stores⟩
  case throwRefHandlerEmpty => exact ⟨targetStore, .throwRefHandlerEmpty, stores⟩
  case throwRefHandlerCatch he ht =>
    exact ⟨targetStore, .throwRefHandlerCatch (stores.exns ▸ he) ht, stores⟩
  case throwRefHandlerCatchRef he ht =>
    exact ⟨targetStore, .throwRefHandlerCatchRef (stores.exns ▸ he) ht, stores⟩
  case throwRefHandlerCatchAll => exact ⟨targetStore, .throwRefHandlerCatchAll, stores⟩
  case throwRefHandlerCatchAllRef => exact ⟨targetStore, .throwRefHandlerCatchAllRef, stores⟩
  case throwRefHandlerNext h =>
    exact ⟨targetStore, .throwRefHandlerNext (by simpa only [CatchMatches, frame, moduleView, ← stores.exns] using h), stores⟩
  case tryTable hbt hm => exact ⟨targetStore, .tryTable hbt hm, stores⟩
  case handlerVals => exact ⟨targetStore, .handlerVals, stores⟩
  case trapInstrs hne => exact ⟨targetStore, .trapInstrs (hne.imp_right admins_ne_nil), stores⟩
  case trapLabel => exact ⟨targetStore, .trapLabel, stores⟩
  case trapHandler => exact ⟨targetStore, .trapHandler, stores⟩
  case trapFrame => exact ⟨targetStore, .trapFrame, stores⟩

/-- Complete host-free executions commute with global-address renaming. -/
theorem steps {source sourceFinal : Config H}
    (sourceRun : Steps P Simulation.noHost source sourceFinal) :
    ∀ {p : Nat ≃ Nat} {targetStore : Store H}, Renamed p source.store targetStore →
      ∃ targetFinalStore, Steps P Simulation.noHost (config p targetStore source)
        (config p targetFinalStore sourceFinal) ∧ Renamed p sourceFinal.store targetFinalStore := by
  induction sourceRun with
  | refl => intro p targetStore stores; exact ⟨targetStore, .refl, stores⟩
  | tail previous next ih =>
    intro p targetStore stores
    obtain ⟨targetMid, run, renamed⟩ := ih stores
    obtain ⟨targetFinal, reduced, renamedFinal⟩ := step next renamed
    exact ⟨targetFinal, run.tail reduced, renamedFinal⟩

/-- Invocation uses closed function tags, which are unaffected by the global
permutation; its caller has empty module tables. -/
theorem config_invoke {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) (address : Nat) (args : List Val) :
    config p target (invoke source address args) = invoke target address args := by
  simp only [invoke, config, admins_append, admins_vals, admins, admin,
    stores.function_tag_lookup address, frame, moduleView, List.map_nil]

/-- A complete source invocation gives a complete renamed invocation, without
an assumed target run or any typing premise. -/
theorem invoke_steps {p : Nat ≃ Nat} {source target : Store H}
    {address : Nat} {args : List Val} {sourceFinal : Config H}
    (stores : Renamed p source target)
    (run : Steps P Simulation.noHost (invoke source address args) sourceFinal) :
    ∃ targetFinalStore, Steps P Simulation.noHost (invoke target address args)
      (config p targetFinalStore sourceFinal) ∧ Renamed p sourceFinal.store targetFinalStore := by
  obtain ⟨targetFinal, targetRun, renamed⟩ := steps run stores
  exact ⟨targetFinal, config_invoke stores address args ▸ targetRun, renamed⟩

/-- The global renaming preserves every terminal result exactly. -/
theorem admins_result (p : Nat ≃ Nat) (result : Result) :
    admins p result.toAdmin = result.toAdmin := by
  cases result with
  | values vs => exact admins_vals p vs
  | throw address => rfl
  | trap => rfl

/-- A terminal source observation constructs the same renamed observation. -/
theorem invoke_result {p : Nat ≃ Nat} {source target : Store H}
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (stores : Renamed p source target)
    (run : Steps P Simulation.noHost (invoke source address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinalStore, Steps P Simulation.noHost (invoke target address args)
      (config p targetFinalStore sourceFinal) ∧ Renamed p sourceFinal.store targetFinalStore ∧
      (config p targetFinalStore sourceFinal).code = result.toAdmin := by
  obtain ⟨targetFinal, targetRun, renamed⟩ := invoke_steps stores run
  exact ⟨targetFinal, targetRun, renamed, by simp only [config, returned, admins_result]⟩

end Silmaril.Wasm.Link.GC.GlobalRenameSimulation
