module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Swap10Enc

/-!
# Removing export lists commutes with V1 `Step` on host-free stores

The 1.0 analogue of `Sim20.Utf8Strip.step_strip20`. V1 never reads an export list during
reduction: every rule reads a module through its other five fields, and an invocation copies
the callee's module into the new frame. So

* `expAdmin10` fixes source instructions, invocations and `trap`, so `expAdmins10` fixes
  values and plain code and distributes over `++`;
* `pureStep_exp10`: a `PureStep` of `is` gives one of `expAdmins10 F is`;
* **`step_exp10`**: on a store without host functions (`Whole.NoHost10`), a step `c → c'`
  gives the step `expConfig10 F c → expConfig10 F c'`. Host calls are excluded because the host
  relation sees the store, export lists included.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression result frameMemory frameTable setGlobal setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst ExportInst)

variable {H : Type} {F : ModuleInst → List ExportInst}

@[simp] theorem expAdmin10_source (i : V1.Instr) : expAdmin10 F (.source i) = .source i := rfl
@[simp] theorem expAdmin10_trap : expAdmin10 F .trap = .trap := rfl
@[simp] theorem expAdmin10_invoke (a : Execution.Runtime.FuncAddr) :
    expAdmin10 F (.invoke a) = .invoke a := rfl
@[simp] theorem expAdmin10_label (n : Nat) (cont : V1.Expr) (body : List Admin) :
    expAdmin10 F (.label n cont body) = .label n cont (expAdmins10 F body) := rfl
@[simp] theorem expAdmin10_frame (n : Nat) (f : Frame) (body : List Admin) :
    expAdmin10 F (.frame n f body) = .frame n (expFrame10 F f) (expAdmins10 F body) := rfl

@[simp] theorem expAdmins10_nil : expAdmins10 F [] = [] := rfl
@[simp] theorem expAdmins10_cons (a : Admin) (l : List Admin) :
    expAdmins10 F (a :: l) = expAdmin10 F a :: expAdmins10 F l := rfl

theorem expAdmins10_eq_map : ∀ l : List Admin, expAdmins10 F l = l.map (expAdmin10 F)
  | [] => rfl
  | a :: l => by simp [expAdmins10_eq_map l]

@[simp] theorem expAdmins10_append (l₁ l₂ : List Admin) :
    expAdmins10 F (l₁ ++ l₂) = expAdmins10 F l₁ ++ expAdmins10 F l₂ := by
  simp [expAdmins10_eq_map]

@[simp] theorem expAdmins10_eq_nil {l : List Admin} : expAdmins10 F l = [] ↔ l = [] := by
  simp [expAdmins10_eq_map]

@[simp] theorem expAdmin10_value (v : Execution.Runtime.Value) :
    expAdmin10 F (value v) = value v := by
  unfold value
  split <;> rfl

@[simp] theorem expAdmins10_values (vs : List Execution.Runtime.Value) :
    expAdmins10 F (values vs) = values vs := by
  simp [expAdmins10_eq_map, values]

@[simp] theorem expAdmins10_sources (is : List V1.Instr) :
    expAdmins10 F (is.map .source) = is.map .source := by
  simp [expAdmins10_eq_map]

@[simp] theorem expAdmins10_expression (is : List V1.Instr) :
    expAdmins10 F (expression is) = expression is := by
  simp [expAdmins10_eq_map, expression]

@[simp] theorem expAdmins10_result (r : Execution.Runtime.Result) :
    expAdmins10 F (result r) = result r := by
  cases r <;> simp [result]

theorem funcs_stripStore10 (s : Store H) (i : Nat) :
    (expStore10 F s).funcs[i]? = (s.funcs[i]?).map (expFI10 F) := by
  simp [expStore10]

@[simp] theorem expStore10_globals (s : Store H) : (expStore10 F s).globals = s.globals := rfl
@[simp] theorem expStore10_memories (s : Store H) :
    (expStore10 F s).memories = s.memories := rfl
@[simp] theorem expStore10_tables (s : Store H) : (expStore10 F s).tables = s.tables := rfl
@[simp] theorem expFrame10_locals (f : Frame) : (expFrame10 F f).locals = f.locals := rfl
@[simp] theorem expFrame10_globals (f : Frame) :
    (expFrame10 F f).module.globals = f.module.globals := rfl
@[simp] theorem expFrame10_funcs (f : Frame) :
    (expFrame10 F f).module.funcs = f.module.funcs := rfl
@[simp] theorem expFrame10_types (f : Frame) :
    (expFrame10 F f).module.types = f.module.types := rfl

theorem expFI10_type (fi : FuncInst V1.Func H) : (expFI10 F fi).type = fi.type := by
  cases fi <;> rfl

theorem frameMemory_exp10 (s : Store H) (f : Frame) :
    frameMemory (expStore10 F s) (expFrame10 F f) = frameMemory s f := rfl

theorem frameTable_exp10 (s : Store H) (f : Frame) :
    frameTable (expStore10 F s) (expFrame10 F f) = frameTable s f := rfl

theorem expStore10_setGlobal (s : Store H) (a : Execution.Runtime.GlobalAddr)
    (g : Execution.Runtime.GlobalInst) :
    expStore10 F (setGlobal s a g) = setGlobal (expStore10 F s) a g := rfl

theorem expStore10_setMemory (s : Store H) (a : Execution.Runtime.MemAddr)
    (m : Execution.Runtime.MemInst) :
    expStore10 F (setMemory s a m) = setMemory (expStore10 F s) a m := rfl

theorem expFrame10_setLocal (f : Frame) (i : Nat) (v : Execution.Runtime.Value) :
    expFrame10 F { f with locals := f.locals.set i v } =
      { expFrame10 F f with locals := f.locals.set i v } := rfl

/-- **A pure step commutes with stripping.** -/
theorem pureStep_exp10 {is is' : List Admin} (h : PureStep is is') :
    PureStep (expAdmins10 F is) (expAdmins10 F is') := by
  cases h <;> simp only [expAdmins10_cons, expAdmins10_nil, expAdmins10_append,
    expAdmins10_values, expAdmins10_expression, expAdmin10_value, expAdmin10_source,
    expAdmin10_trap, expAdmin10_label, expAdmin10_frame] <;>
    (constructor! <;> assumption)

/-- Unfold `expConfig10` on a literal configuration and apply a state rule at the re-encoded
store and frame. -/
local macro "stripStep " t:term : tactic =>
  `(tactic| (simp only [expConfig10, expAdmins10_cons, expAdmins10_nil,
      expAdmin10_source, expAdmin10_value, expAdmin10_trap, expAdmin10_invoke,
      expAdmins10_append, expAdmins10_values, expStore10_setGlobal,
      expStore10_setMemory, expFrame10_setLocal]) <;> exact $t)

/-- **Forward stripping for V1**: on a store without host functions, a step `c → c'` gives the
step `expConfig10 F c → expConfig10 F c'`. -/
theorem step_exp10 {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hs : Whole.NoHost10 c.store) : Step host (expConfig10 F c) (expConfig10 F c') := by
  induction h with
  | pure s f h => exact .pure _ _ (pureStep_exp10 h)
  | context _ vs tail ih =>
    simpa only [expConfig10, expAdmins10_append, expAdmins10_values] using
      Step.context (ih hs) vs (expAdmins10 F tail)
  | label _ n cont ih =>
    simpa only [expConfig10, expAdmins10_cons, expAdmins10_nil, expAdmin10_label] using
      Step.label (ih hs) n cont
  | frame _ n outer ih =>
    simpa only [expConfig10, expAdmins10_cons, expAdmins10_nil, expAdmin10_frame] using
      Step.frame (ih hs) n (expFrame10 F outer)
  | localGet s f i v hv => stripStep Step.localGet _ _ i v hv
  | localSet s f i v old hv => stripStep Step.localSet _ _ i v old hv
  | globalGet s f i a g hi hg => stripStep Step.globalGet _ _ i a g hi hg
  | globalSet s f i a g v hi hg hm => stripStep Step.globalSet _ _ i a g v hi hg hm
  | call s f i a hf => stripStep Step.call _ _ i a hf
  | callIndirect s f i c t a fn ft ht hy he hf hm =>
    stripStep Step.callIndirect _ _ i c t a (expFI10 F fn) ft ht hy he
      (by rw [funcs_stripStore10, hf]; rfl) (by rw [expFI10_type]; exact hm)
  | callIndirectBounds s f i c t ht ho => stripStep Step.callIndirectBounds _ _ i c t ht ho
  | callIndirectNull s f i c t ht hn => stripStep Step.callIndirectNull _ _ i c t ht hn
  | callIndirectType s f i c t a fn ft ht hy he hf hm =>
    stripStep Step.callIndirectType _ _ i c t a (expFI10 F fn) ft ht hy he
      (by rw [funcs_stripStore10, hf]; rfl) (by rw [expFI10_type]; exact hm)
  | invokeWasm s f a ft m fn args hf har hres =>
    simp only [expConfig10, expAdmins10_append, expAdmins10_values, expAdmins10_cons,
      expAdmins10_nil, expAdmin10_invoke, expAdmin10_frame, expAdmin10_label,
      expAdmins10_expression]
    exact Step.invokeWasm _ _ a ft (expModule10 F m) fn args
      (by rw [funcs_stripStore10, hf]; rfl) har hres
  | invokeHost s s' f a ft fn args r hf => exact absurd hf (hs a.value ft fn)
  | invokeHostDiverges s f a ft fn args hf => exact absurd hf (hs a.value ft fn)
  | intLoad s f t p arg c a m v hm hl => stripStep Step.intLoad _ _ t p arg c a m v hm hl
  | intLoadTrap s f t p arg c a m hm hl => stripStep Step.intLoadTrap _ _ t p arg c a m hm hl
  | floatLoad s f t arg c a m v hm hl => stripStep Step.floatLoad _ _ t arg c a m v hm hl
  | floatLoadTrap s f t arg c a m hm hl => stripStep Step.floatLoadTrap _ _ t arg c a m hm hl
  | intStore s f t p arg c x a m b hm hw => stripStep Step.intStore _ _ t p arg c x a m b hm hw
  | intStoreTrap s f t p arg c x a m hm hw => stripStep Step.intStoreTrap _ _ t p arg c x a m hm hw
  | floatStore s f t arg c x a m b hm hw => stripStep Step.floatStore _ _ t arg c x a m b hm hw
  | floatStoreTrap s f t arg c x a m hm hw =>
    stripStep Step.floatStoreTrap _ _ t arg c x a m hm hw
  | memorySize s f a m hm => stripStep Step.memorySize _ _ a m hm
  | memoryGrow s f a m c r b hm hg => stripStep Step.memoryGrow _ _ a m c r b hm hg

end Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10
