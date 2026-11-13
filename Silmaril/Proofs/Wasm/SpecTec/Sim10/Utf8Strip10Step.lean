module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.Defs

/-!
# Removing export lists commutes with V1 `Step` on host-free stores

The 1.0 analogue of `Sim20.Utf8Strip.step_strip20`. V1 never reads an export list during
reduction: every rule reads a module through its other five fields, and an invocation copies
the callee's module into the new frame. So

* `stripAdmin10` fixes source instructions, invocations and `trap`, so `stripAdmins10` fixes
  values and plain code and distributes over `++`;
* `pureStep_strip10`: a `PureStep` of `is` gives one of `stripAdmins10 is`;
* **`step_strip10`**: on a store without host functions (`Whole.NoHost10`), a step `c → c'`
  gives the step `stripConfig10 c → stripConfig10 c'`. Host calls are excluded because the host
  relation sees the store, export lists included.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression result frameMemory frameTable setGlobal setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst)

variable {H : Type}

@[simp] theorem stripAdmin10_source (i : V1.Instr) : stripAdmin10 (.source i) = .source i := rfl
@[simp] theorem stripAdmin10_trap : stripAdmin10 .trap = .trap := rfl
@[simp] theorem stripAdmin10_invoke (a : Execution.Runtime.FuncAddr) :
    stripAdmin10 (.invoke a) = .invoke a := rfl
@[simp] theorem stripAdmin10_label (n : Nat) (cont : V1.Expr) (body : List Admin) :
    stripAdmin10 (.label n cont body) = .label n cont (stripAdmins10 body) := rfl
@[simp] theorem stripAdmin10_frame (n : Nat) (f : Frame) (body : List Admin) :
    stripAdmin10 (.frame n f body) = .frame n (stripFrame10 f) (stripAdmins10 body) := rfl

@[simp] theorem stripAdmins10_nil : stripAdmins10 [] = [] := rfl
@[simp] theorem stripAdmins10_cons (a : Admin) (l : List Admin) :
    stripAdmins10 (a :: l) = stripAdmin10 a :: stripAdmins10 l := rfl

theorem stripAdmins10_eq_map : ∀ l : List Admin, stripAdmins10 l = l.map stripAdmin10
  | [] => rfl
  | a :: l => by simp [stripAdmins10_eq_map l]

@[simp] theorem stripAdmins10_append (l₁ l₂ : List Admin) :
    stripAdmins10 (l₁ ++ l₂) = stripAdmins10 l₁ ++ stripAdmins10 l₂ := by
  simp [stripAdmins10_eq_map]

@[simp] theorem stripAdmins10_eq_nil {l : List Admin} : stripAdmins10 l = [] ↔ l = [] := by
  simp [stripAdmins10_eq_map]

@[simp] theorem stripAdmin10_value (v : Execution.Runtime.Value) :
    stripAdmin10 (value v) = value v := by
  unfold value
  split <;> rfl

@[simp] theorem stripAdmins10_values (vs : List Execution.Runtime.Value) :
    stripAdmins10 (values vs) = values vs := by
  simp [stripAdmins10_eq_map, values]

@[simp] theorem stripAdmins10_sources (is : List V1.Instr) :
    stripAdmins10 (is.map .source) = is.map .source := by
  simp [stripAdmins10_eq_map]

@[simp] theorem stripAdmins10_expression (is : List V1.Instr) :
    stripAdmins10 (expression is) = expression is := by
  simp [stripAdmins10_eq_map, expression]

@[simp] theorem stripAdmins10_result (r : Execution.Runtime.Result) :
    stripAdmins10 (result r) = result r := by
  cases r <;> simp [result]

theorem funcs_stripStore10 (s : Store H) (i : Nat) :
    (stripStore10 s).funcs[i]? = (s.funcs[i]?).map stripFI10 := by
  simp [stripStore10]

@[simp] theorem stripStore10_globals (s : Store H) : (stripStore10 s).globals = s.globals := rfl
@[simp] theorem stripStore10_memories (s : Store H) :
    (stripStore10 s).memories = s.memories := rfl
@[simp] theorem stripStore10_tables (s : Store H) : (stripStore10 s).tables = s.tables := rfl
@[simp] theorem stripFrame10_locals (f : Frame) : (stripFrame10 f).locals = f.locals := rfl
@[simp] theorem stripFrame10_globals (f : Frame) :
    (stripFrame10 f).module.globals = f.module.globals := rfl
@[simp] theorem stripFrame10_funcs (f : Frame) :
    (stripFrame10 f).module.funcs = f.module.funcs := rfl
@[simp] theorem stripFrame10_types (f : Frame) :
    (stripFrame10 f).module.types = f.module.types := rfl

theorem stripFI10_type (fi : FuncInst V1.Func H) : (stripFI10 fi).type = fi.type := by
  cases fi <;> rfl

theorem frameMemory_strip10 (s : Store H) (f : Frame) :
    frameMemory (stripStore10 s) (stripFrame10 f) = frameMemory s f := rfl

theorem frameTable_strip10 (s : Store H) (f : Frame) :
    frameTable (stripStore10 s) (stripFrame10 f) = frameTable s f := rfl

theorem stripStore10_setGlobal (s : Store H) (a : Execution.Runtime.GlobalAddr)
    (g : Execution.Runtime.GlobalInst) :
    stripStore10 (setGlobal s a g) = setGlobal (stripStore10 s) a g := rfl

theorem stripStore10_setMemory (s : Store H) (a : Execution.Runtime.MemAddr)
    (m : Execution.Runtime.MemInst) :
    stripStore10 (setMemory s a m) = setMemory (stripStore10 s) a m := rfl

theorem stripFrame10_setLocal (f : Frame) (i : Nat) (v : Execution.Runtime.Value) :
    stripFrame10 { f with locals := f.locals.set i v } =
      { stripFrame10 f with locals := f.locals.set i v } := rfl

/-- **A pure step commutes with stripping.** -/
theorem pureStep_strip10 {is is' : List Admin} (h : PureStep is is') :
    PureStep (stripAdmins10 is) (stripAdmins10 is') := by
  cases h <;> simp only [stripAdmins10_cons, stripAdmins10_nil, stripAdmins10_append,
    stripAdmins10_values, stripAdmins10_expression, stripAdmin10_value, stripAdmin10_source,
    stripAdmin10_trap, stripAdmin10_label, stripAdmin10_frame] <;>
    (constructor! <;> assumption)

/-- Unfold `stripConfig10` on a literal configuration and apply a state rule at the stripped
store and frame. -/
local macro "stripStep " t:term : tactic =>
  `(tactic| (simp only [stripConfig10, stripAdmins10_cons, stripAdmins10_nil,
      stripAdmin10_source, stripAdmin10_value, stripAdmin10_trap, stripAdmin10_invoke,
      stripAdmins10_append, stripAdmins10_values, stripStore10_setGlobal,
      stripStore10_setMemory, stripFrame10_setLocal]) <;> exact $t)

/-- **Forward stripping for V1**: on a store without host functions, a step `c → c'` gives the
step `stripConfig10 c → stripConfig10 c'`. -/
theorem step_strip10 {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hs : Whole.NoHost10 c.store) : Step host (stripConfig10 c) (stripConfig10 c') := by
  induction h with
  | pure s f h => exact .pure _ _ (pureStep_strip10 h)
  | context _ vs tail ih =>
    simpa only [stripConfig10, stripAdmins10_append, stripAdmins10_values] using
      Step.context (ih hs) vs (stripAdmins10 tail)
  | label _ n cont ih =>
    simpa only [stripConfig10, stripAdmins10_cons, stripAdmins10_nil, stripAdmin10_label] using
      Step.label (ih hs) n cont
  | frame _ n outer ih =>
    simpa only [stripConfig10, stripAdmins10_cons, stripAdmins10_nil, stripAdmin10_frame] using
      Step.frame (ih hs) n (stripFrame10 outer)
  | localGet s f i v hv => stripStep Step.localGet _ _ i v hv
  | localSet s f i v old hv => stripStep Step.localSet _ _ i v old hv
  | globalGet s f i a g hi hg => stripStep Step.globalGet _ _ i a g hi hg
  | globalSet s f i a g v hi hg hm => stripStep Step.globalSet _ _ i a g v hi hg hm
  | call s f i a hf => stripStep Step.call _ _ i a hf
  | callIndirect s f i c t a fn ft ht hy he hf hm =>
    stripStep Step.callIndirect _ _ i c t a (stripFI10 fn) ft ht hy he
      (by rw [funcs_stripStore10, hf]; rfl) (by rw [stripFI10_type]; exact hm)
  | callIndirectBounds s f i c t ht ho => stripStep Step.callIndirectBounds _ _ i c t ht ho
  | callIndirectNull s f i c t ht hn => stripStep Step.callIndirectNull _ _ i c t ht hn
  | callIndirectType s f i c t a fn ft ht hy he hf hm =>
    stripStep Step.callIndirectType _ _ i c t a (stripFI10 fn) ft ht hy he
      (by rw [funcs_stripStore10, hf]; rfl) (by rw [stripFI10_type]; exact hm)
  | invokeWasm s f a ft m fn args hf har hres =>
    simp only [stripConfig10, stripAdmins10_append, stripAdmins10_values, stripAdmins10_cons,
      stripAdmins10_nil, stripAdmin10_invoke, stripAdmin10_frame, stripAdmin10_label,
      stripAdmins10_expression]
    exact Step.invokeWasm _ _ a ft (stripModule10 m) fn args
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

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
