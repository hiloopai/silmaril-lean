module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Step

/-!
# A V1 step keeps any property of all module instances

The 1.0 form of `Sim20.Utf8Strip.modsQ_step`. V1 reduction never makes a module instance: the
store's function instances are never replaced (only globals and memories are written), and an
invocation copies the callee's module into the new frame. So **`modsQ10_step`**: on a store
without host functions, a step keeps `ModsQ10 Q` (every module instance of the configuration,
in the store, the frame and every frame of the code, has `Q`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression result setGlobal setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst)

variable {H : Type} {Q : ModuleInst → Prop}

mutual
/-- Every frame inside `a` has a module with `Q`. -/
def AdminMods10 (Q : ModuleInst → Prop) : Admin → Prop
  | .label _ _ body => AdminsMods10 Q body
  | .frame _ f body => Q f.module ∧ AdminsMods10 Q body
  | _ => True

/-- `AdminMods10` on a sequence. -/
def AdminsMods10 (Q : ModuleInst → Prop) : List Admin → Prop
  | [] => True
  | a :: l => AdminMods10 Q a ∧ AdminsMods10 Q l
end

/-- The module of a defined function instance has `Q`. -/
def FuncMod10 (Q : ModuleInst → Prop) (fi : FuncInst V1.Func H) : Prop :=
  ∀ t m fn, fi = .wasm t m fn → Q m

/-- **Every module instance of `c` has `Q`.** -/
structure ModsQ10 (Q : ModuleInst → Prop) (c : Config H) : Prop where
  funcs : ∀ fi ∈ c.store.funcs, FuncMod10 Q fi
  frame : Q c.frame.module
  code : AdminsMods10 Q c.code

@[simp] theorem adminMods10_source (i : V1.Instr) : AdminMods10 Q (.source i) := trivial
@[simp] theorem adminMods10_trap : AdminMods10 Q .trap := trivial
@[simp] theorem adminMods10_invoke (a : Execution.Runtime.FuncAddr) :
    AdminMods10 Q (.invoke a) := trivial
@[simp] theorem adminMods10_label (n : Nat) (cont : V1.Expr) (body : List Admin) :
    AdminMods10 Q (.label n cont body) ↔ AdminsMods10 Q body := Iff.rfl
@[simp] theorem adminMods10_frame (n : Nat) (f : Frame) (body : List Admin) :
    AdminMods10 Q (.frame n f body) ↔ Q f.module ∧ AdminsMods10 Q body := Iff.rfl
@[simp] theorem adminsMods10_nil : AdminsMods10 Q [] := trivial
@[simp] theorem adminsMods10_cons (a : Admin) (l : List Admin) :
    AdminsMods10 Q (a :: l) ↔ AdminMods10 Q a ∧ AdminsMods10 Q l := Iff.rfl

@[simp] theorem adminsMods10_append (l₁ l₂ : List Admin) :
    AdminsMods10 Q (l₁ ++ l₂) ↔ AdminsMods10 Q l₁ ∧ AdminsMods10 Q l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, and_assoc]

@[simp] theorem adminMods10_value (v : Execution.Runtime.Value) : AdminMods10 Q (value v) := by
  unfold value
  split <;> trivial

@[simp] theorem adminsMods10_values (vs : List Execution.Runtime.Value) :
    AdminsMods10 Q (values vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨adminMods10_value v, ih⟩

@[simp] theorem adminsMods10_expression (is : List V1.Instr) :
    AdminsMods10 Q (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih => exact ⟨trivial, ih⟩

@[simp] theorem adminsMods10_result (r : Execution.Runtime.Result) :
    AdminsMods10 Q (result r) := by
  cases r <;> simp [result]

/-- **A pure step keeps the modules of the code.** -/
theorem pureStep_mods10 {is is' : List Admin} (h : PureStep is is') (hq : AdminsMods10 Q is) :
    AdminsMods10 Q is' := by
  cases h <;> simp_all

/-- **A V1 step keeps `ModsQ10 Q`** on a store without host functions. -/
theorem modsQ10_step {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hs : Whole.NoHost10 c.store) (hq : ModsQ10 Q c) : ModsQ10 Q c' := by
  induction h with
  | pure s f h => exact ⟨hq.funcs, hq.frame, pureStep_mods10 h hq.code⟩
  | @context _ _ _ _ before _ _ vs tail ih =>
    have hc : AdminsMods10 Q before ∧ AdminsMods10 Q tail := by
      simpa only [adminsMods10_append, adminsMods10_values, true_and] using hq.code
    have h' := ih hs ⟨hq.funcs, hq.frame, hc.1⟩
    exact ⟨h'.funcs, h'.frame, by simpa only [adminsMods10_append, adminsMods10_values,
      true_and] using ⟨h'.code, hc.2⟩⟩
  | @label _ _ _ _ before _ _ n cont ih =>
    have hc : AdminsMods10 Q before := by simpa using hq.code
    have h' := ih hs ⟨hq.funcs, hq.frame, hc⟩
    exact ⟨h'.funcs, h'.frame, by simpa using h'.code⟩
  | @frame _ _ inner _ before _ _ n outer ih =>
    have hc : Q inner.module ∧ AdminsMods10 Q before := by simpa using hq.code
    have h' := ih hs ⟨hq.funcs, hc.1, hc.2⟩
    exact ⟨h'.funcs, hq.frame, by simpa using ⟨h'.frame, h'.code⟩⟩
  | invokeWasm s f a ft m fn args hf _ _ =>
    have hm : Q m := hq.funcs _ (List.mem_of_getElem? hf) ft m fn rfl
    exact ⟨hq.funcs, hq.frame, by simpa using hm⟩
  | invokeHost s s' f a ft fn args r hf => exact absurd hf (hs a.value ft fn)
  | invokeHostDiverges s f a ft fn args hf => exact absurd hf (hs a.value ft fn)
  | _ => exact ⟨hq.funcs, hq.frame, by simp⟩

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
