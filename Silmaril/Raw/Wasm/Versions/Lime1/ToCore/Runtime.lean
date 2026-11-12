module

public import Silmaril.Raw.Wasm.Versions.Foundations.ListExt
public import Silmaril.Raw.Wasm.Versions.Lime1.Execution
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Validation
public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-! # Lime1 runtime objects as Core 3.0 runtime objects

Real, total maps from the shared V1/Lime1 runtime (`Execution.Runtime`) to the
Core runtime (`Execution.Core`):

* values: `Value.toCore v = .num ⟨v.type, v.bits⟩`, so a Lime1 value instruction
  `.source (.intConst t b)` maps to the Core value instruction
  `.plain (.intConst t b)` by the instruction map (`value_toCore`, by cases);
* instances: function types become `V1.FuncType.toDefType`, tables become
  `funcref`/`i32` tables whose minimum is the current size, memories are `i32`
  memories, globals keep their value and mutability;
* code: `.invoke a` becomes `REF.FUNC_ADDR a` followed by `CALL_REF` annotated
  with the callee's defined type (read from the store, which never changes
  function types), exactly the spec's `$invoke`/`Step_read/call` result.

**Simulation relation.** Core configurations reached from Lime1 images differ in
two inessential ways: Core instantiation allocates (then drops) data and element
segments, which Lime1 never has, and Core `call_indirect` produces a `CALL_REF`
annotated with a type *index* where Lime1's `.invoke` gives a defined type.
`Config.norm` erases segments and resolves `CALL_REF` index annotations against
the enclosing frame's module; `Sim a c := c.norm = a.toCore`.
-/

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Validation (DefType Ty)

namespace ToCore

abbrev CVal := Silmaril.Wasm.Execution.Core.Val
abbrev CAdmin := Silmaril.Wasm.Execution.Core.Admin
abbrev CModuleInst := Silmaril.Wasm.Execution.Core.ModuleInst
abbrev CFrame := Silmaril.Wasm.Execution.Core.Frame
abbrev CStore (H : Type) := Silmaril.Wasm.Execution.Core.Store H
abbrev CConfig (H : Type) := Silmaril.Wasm.Execution.Core.Config H
abbrev CResult := Silmaril.Wasm.Execution.Core.Result
abbrev CHostOutcome (H : Type) := Silmaril.Wasm.Execution.Core.HostOutcome H
abbrev CHostSemantics (H : Type) := Silmaril.Wasm.Execution.Core.HostSemantics H

end ToCore

open ToCore

def _root_.Silmaril.Wasm.Execution.Runtime.Value.toCore (v : Value) : CVal := .num ⟨v.type, v.bits⟩

def _root_.Silmaril.Wasm.Execution.Runtime.ExternVal.toCore : ExternVal → Silmaril.Wasm.Execution.Core.ExternAddr
  | .func a => .func a.value
  | .table a => .table a.value
  | .memory a => .mem a.value
  | .global a => .global a.value

def _root_.Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore (m : ModuleInst) : CModuleInst where
  types := m.types.map V1.FuncType.toDefType
  funcs := m.funcs.map Addr.value
  tables := m.tables.map Addr.value
  mems := m.memories.map Addr.value
  globals := m.globals.map Addr.value
  exports := m.exports.map fun e => ⟨e.name, e.value.toCore⟩

def _root_.Silmaril.Wasm.Execution.Runtime.Frame.toCore (f : Frame) : CFrame := ⟨f.locals.map (some ∘ Value.toCore), f.module.toCore⟩

variable {H : Type}

def _root_.Silmaril.Wasm.Execution.Runtime.FuncInst.toCore : FuncInst Func H → Silmaril.Wasm.Execution.Core.FuncInst H
  | .wasm t m c => ⟨t.toDefType, m.toCore, .wasm c.toCore⟩
  | .host t h => ⟨t.toDefType, {}, .host h⟩

def _root_.Silmaril.Wasm.Execution.Runtime.TableInst.toCore (t : TableInst) : Silmaril.Wasm.Execution.Core.TableInst :=
  ⟨⟨.i32, ⟨Fin.ofNat _ t.refs.length, t.max.map (Fin.ofNat _)⟩, Silmaril.Wasm.Validation.Ty.funcref⟩,
    t.refs.map fun | none => .null | some a => .func a.value⟩

def _root_.Silmaril.Wasm.Execution.Runtime.MemInst.toCore (m : MemInst) : Silmaril.Wasm.Execution.Core.MemInst :=
  ⟨⟨.i32, ⟨Fin.ofNat _ (m.data.size / Silmaril.Wasm.Execution.Memory.pageSize), m.max.map (Fin.ofNat _)⟩⟩, m.data⟩

def _root_.Silmaril.Wasm.Execution.Runtime.GlobalInst.toCore (g : GlobalInst) : Silmaril.Wasm.Execution.Core.GlobalInst :=
  ⟨⟨g.mutability, .num g.value.type⟩, g.value.toCore⟩

def _root_.Silmaril.Wasm.Execution.Runtime.Store.toCore (s : Store H) : CStore H where
  funcs := s.funcs.map FuncInst.toCore
  tables := s.tables.map TableInst.toCore
  mems := s.memories.map MemInst.toCore
  globals := s.globals.map GlobalInst.toCore

/-- The defined type of the function at address `a` (default if absent). -/
def _root_.Silmaril.Wasm.Execution.Runtime.Store.funcDefType (s : Store H) (a : FuncAddr) : DefType :=
  ((s.funcs[a.value]?).map fun fi => fi.type.toDefType).getD default

mutual
def Silmaril.Wasm.Execution.Core.Admin.toCore (s : Store H) : Silmaril.Wasm.Execution.Core.Admin → List CAdmin
  | .source i => [.plain i.toCore]
  | .invoke a => [.ref (.func a.value), .callRefType (s.funcDefType a)]
  | .label n cont body => [.label n (cont.map Instr.toCore) (Silmaril.Wasm.Execution.Core.Admin.listToCore s body)]
  | .frame n f body => [.frame n f.toCore (Silmaril.Wasm.Execution.Core.Admin.listToCore s body)]
  | .trap => [.trap]

def Silmaril.Wasm.Execution.Core.Admin.listToCore (s : Store H) : List Silmaril.Wasm.Execution.Core.Admin → List CAdmin
  | [] => []
  | a :: as => Silmaril.Wasm.Execution.Core.Admin.toCore s a ++ Silmaril.Wasm.Execution.Core.Admin.listToCore s as
end

def _root_.Silmaril.Wasm.Execution.Runtime.Config.toCore (c : Config H) : CConfig H :=
  ⟨c.store.toCore, c.frame.toCore, Silmaril.Wasm.Execution.Core.Admin.listToCore c.store c.code⟩

def _root_.Silmaril.Wasm.Execution.Runtime.Result.toCore : Result → CResult
  | .values vs => .values (vs.map Value.toCore)
  | .trap => .trap

/-! ## Normalisation and the simulation relation -/

namespace ToCore

open Silmaril.Wasm.Execution.Core

def ModuleInst.erase (m : CModuleInst) : CModuleInst := { m with datas := [], elems := [] }

def Frame.erase (f : CFrame) : CFrame := { f with module := ModuleInst.erase f.module }

/-- A global's declared type is replaced by the type of its current numeric value:
Lime1 globals carry no declared type separate from their value, and a Lime1
`global.set` (unlike Core's, which keeps the declared type) retypes the global
with the stored value. -/
def GlobalInst.erase (g : Silmaril.Wasm.Execution.Core.GlobalInst) :
    Silmaril.Wasm.Execution.Core.GlobalInst :=
  match g.value with
  | .num v => { g with type := ⟨g.type.mutability, .num v.type⟩ }
  | _ => g

def Store.erase (s : CStore H) : CStore H :=
  { s with datas := [], elems := [],
           funcs := s.funcs.map fun fi => { fi with module := ModuleInst.erase fi.module },
           globals := s.globals.map GlobalInst.erase }

mutual
/-- Resolve `CALL_REF x` annotations against module `m`; erase segment addresses. -/
def Silmaril.Wasm.Execution.Core.Admin.norm (m : CModuleInst) : CAdmin → CAdmin
  | .plain (.callRef x) => .callRefType ((m.types[x.toNat]?).getD default)
  | .plain (.returnCallRef x) => .returnCallRefType ((m.types[x.toNat]?).getD default)
  | .label n cont body => .label n cont (Silmaril.Wasm.Execution.Core.Admin.normList m body)
  | .handler n cs body => .handler n cs (Silmaril.Wasm.Execution.Core.Admin.normList m body)
  | .frame n f body => .frame n (Frame.erase f) (Silmaril.Wasm.Execution.Core.Admin.normList f.module body)
  | a => a

def Silmaril.Wasm.Execution.Core.Admin.normList (m : CModuleInst) : List CAdmin → List CAdmin
  | [] => []
  | a :: as => Silmaril.Wasm.Execution.Core.Admin.norm m a :: Silmaril.Wasm.Execution.Core.Admin.normList m as
end

def Config.norm (c : CConfig H) : CConfig H :=
  ⟨Store.erase c.store, Frame.erase c.frame, Silmaril.Wasm.Execution.Core.Admin.normList c.frame.module c.code⟩

/-- Module-instance similarity: the Core instance additionally records (dropped)
data and element segment addresses, which Lime1 never has. (Graft from design A.) -/
def ModuleInstSim (mL : Silmaril.Wasm.Execution.Runtime.ModuleInst) (mC : CModuleInst) : Prop :=
  ModuleInst.erase mC = mL.toCore

end ToCore

/-! ## Well-formedness of Lime1 configurations

Lime1's `call` does not look up its callee in the store (a dangling address gives
a stuck `.invoke`), whereas Core's `call` does; memory growth compares against a
maximum that Core stores in `Fin (2^64)`; and the Core `memory.fill`/`memory.copy`
iterations use wrapping 32-bit addresses. The simulation is therefore stated for
configurations whose function addresses are allocated and whose memories fit the
32-bit address space. -/

/-- Function addresses of a module instance are allocated. -/
def ModWF (s : Store H) (m : Silmaril.Wasm.Execution.Runtime.ModuleInst) : Prop :=
  ∀ a ∈ m.funcs, a.value < s.funcs.length

mutual
/-- Invoked addresses are allocated; frames have well-formed modules. -/
def Silmaril.Wasm.Execution.Core.Admin.WF (s : Store H) : Silmaril.Wasm.Execution.Core.Admin → Prop
  | .source _ => True
  | .invoke a => a.value < s.funcs.length
  | .label _ _ body => Silmaril.Wasm.Execution.Core.Admin.listWF s body
  | .frame _ f body => ModWF s f.module ∧ Silmaril.Wasm.Execution.Core.Admin.listWF s body
  | .trap => True

def Silmaril.Wasm.Execution.Core.Admin.listWF (s : Store H) : List Silmaril.Wasm.Execution.Core.Admin → Prop
  | [] => True
  | a :: as => Silmaril.Wasm.Execution.Core.Admin.WF s a ∧ Silmaril.Wasm.Execution.Core.Admin.listWF s as
end

/-- Store well-formedness: module instances of Wasm functions are well formed, and
memories fit the 32-bit address space with a maximum representable in Core limits. -/
def StoreWF (s : Store H) : Prop :=
  (∀ (i : Nat) (t : V1.FuncType) (m : Silmaril.Wasm.Execution.Runtime.ModuleInst) (c : Func),
    s.funcs[i]? = some (FuncInst.wasm t m c) → ModWF s m) ∧
  (∀ (i : Nat) (mi : MemInst), s.memories[i]? = some mi →
    mi.data.size ≤ 2 ^ 32 ∧ ∀ j, mi.max = some j → j < 2 ^ 64)

/-- Configuration well-formedness. -/
def ConfigWF (a : Config H) : Prop :=
  StoreWF a.store ∧ ModWF a.store a.frame.module ∧ Silmaril.Wasm.Execution.Core.Admin.listWF a.store a.code

/-- Store extension as far as functions are concerned: allocated functions stay
allocated with the same type. -/
def StoreExt (s s' : Store H) : Prop := ListExt FuncInst.type s.funcs s'.funcs

/-- Host calls preserve store well-formedness and extend the store. The shared
`Silmaril.Wasm.Execution.Host.Preserves` with Lime1's invariants. -/
def HostPreserves (src : HostSemantics H) : Prop :=
  Silmaril.Wasm.Execution.Host.Preserves StoreWF (fun s s' => StoreWF s' ∧ StoreExt s s') src

/-- The simulation relation between Lime1 and Core configurations: the normalised
Core configuration is the image of a well-formed Lime1 configuration. -/
def Sim (a : Config H) (c : CConfig H) : Prop := ToCore.Config.norm c = a.toCore ∧ ConfigWF a

/-- Host outcomes correspond. The shared `Silmaril.Wasm.Execution.Host.Outcome.Sim`,
for the store relation "the erased Core store is the image of the Lime1 store"
and the result translation `Result.toCore`. -/
def HostOutcomeSim : HostOutcome Func H → CHostOutcome H → Prop :=
  Silmaril.Wasm.Execution.Host.Outcome.Sim (fun s sC => ToCore.Store.erase sC = s.toCore)
    Silmaril.Wasm.Execution.Runtime.Result.toCore

/-- Host compatibility: every Lime1 host behaviour is matched by the Core host on
a related store. The shared `Silmaril.Wasm.Execution.Host.Compatible`. -/
def HostCompatible (src : HostSemantics H) (tgt : CHostSemantics H) : Prop :=
  Silmaril.Wasm.Execution.Host.Compatible StoreWF (fun s s' => StoreWF s' ∧ StoreExt s s')
    (fun s sC => ToCore.Store.erase sC = s.toCore) Value.toCore HostOutcomeSim src tgt

/-! ## Commuting lemmas (the `simp` battery for the simulation proofs) -/

@[simp] theorem value_toCore (s : Store H) (v : Value) :
    Silmaril.Wasm.Execution.Core.Admin.toCore s (value v) = [(Value.toCore v).toAdmin] := by
  rcases v with ⟨⟨_ | _⟩, _⟩ <;> rfl

@[simp] theorem listToCore_nil (s : Store H) : Silmaril.Wasm.Execution.Core.Admin.listToCore s [] = [] := by
  simp [Silmaril.Wasm.Execution.Core.Admin.listToCore]

@[simp] theorem listToCore_cons (s : Store H) (a : Silmaril.Wasm.Execution.Core.Admin) (as : List Silmaril.Wasm.Execution.Core.Admin) :
    Silmaril.Wasm.Execution.Core.Admin.listToCore s (a :: as) = Silmaril.Wasm.Execution.Core.Admin.toCore s a ++ Silmaril.Wasm.Execution.Core.Admin.listToCore s as := by
  simp [Silmaril.Wasm.Execution.Core.Admin.listToCore]

theorem listToCore_append (s : Store H) (xs ys : List Silmaril.Wasm.Execution.Core.Admin) :
    Silmaril.Wasm.Execution.Core.Admin.listToCore s (xs ++ ys) = Silmaril.Wasm.Execution.Core.Admin.listToCore s xs ++ Silmaril.Wasm.Execution.Core.Admin.listToCore s ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

@[simp] theorem values_toCore (s : Store H) (vs : List Value) :
    Silmaril.Wasm.Execution.Core.Admin.listToCore s (values vs) = Silmaril.Wasm.Execution.Core.vals (vs.map Value.toCore) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [values, List.map_cons, listToCore_cons, value_toCore] at ih ⊢
    rw [ih]; rfl

@[simp] theorem source_toCore (s : Store H) (i : Instr) :
    Silmaril.Wasm.Execution.Core.Admin.toCore s (.source i) = [.plain i.toCore] := by simp [Silmaril.Wasm.Execution.Core.Admin.toCore]

@[simp] theorem invoke_toCore (s : Store H) (a : FuncAddr) :
    Silmaril.Wasm.Execution.Core.Admin.toCore s (.invoke a) = [.ref (.func a.value), .callRefType (s.funcDefType a)] := by
  simp [Silmaril.Wasm.Execution.Core.Admin.toCore]

@[simp] theorem label_toCore (s : Store H) (n : Nat) (cont : Expr) (body : List Silmaril.Wasm.Execution.Core.Admin) :
    Silmaril.Wasm.Execution.Core.Admin.toCore s (.label n cont body) =
      [.label n (cont.map Instr.toCore) (Silmaril.Wasm.Execution.Core.Admin.listToCore s body)] := by simp [Silmaril.Wasm.Execution.Core.Admin.toCore]

@[simp] theorem frame_toCore (s : Store H) (n : Nat) (f : Frame) (body : List Silmaril.Wasm.Execution.Core.Admin) :
    Silmaril.Wasm.Execution.Core.Admin.toCore s (.frame n f body) = [.frame n f.toCore (Silmaril.Wasm.Execution.Core.Admin.listToCore s body)] := by
  simp [Silmaril.Wasm.Execution.Core.Admin.toCore]

@[simp] theorem trap_toCore (s : Store H) : Silmaril.Wasm.Execution.Core.Admin.toCore s .trap = [.trap] := by
  simp [Silmaril.Wasm.Execution.Core.Admin.toCore]

@[simp] theorem expression_toCore (s : Store H) (es : Expr) :
    Silmaril.Wasm.Execution.Core.Admin.listToCore s (expression es) =
      Silmaril.Wasm.Execution.Core.expression (es.map Instr.toCore) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [expression, List.map_cons, listToCore_cons, source_toCore] at ih ⊢
    rw [ih]; rfl

theorem toCore_ne_nil (s : Store H) (a : Silmaril.Wasm.Execution.Core.Admin) : Silmaril.Wasm.Execution.Core.Admin.toCore s a ≠ [] := by
  cases a <;> simp

theorem Instr.toCore_ne_callRef (i : Instr) (x : TypeIdx) : i.toCore ≠ .callRef x := by
  cases i <;> simp [Instr.toCore]

theorem Instr.toCore_ne_returnCallRef (i : Instr) (x : TypeIdx) : i.toCore ≠ .returnCallRef x := by
  cases i <;> simp [Instr.toCore]

/-! ## Normalisation lemmas -/

namespace ToCore

open Silmaril.Wasm.Execution.Core

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.normList_nil (m : CModuleInst) : Silmaril.Wasm.Execution.Core.Admin.normList m [] = [] := by
  simp [Silmaril.Wasm.Execution.Core.Admin.normList]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.normList_cons (m : CModuleInst) (a : CAdmin) (as : List CAdmin) :
    Silmaril.Wasm.Execution.Core.Admin.normList m (a :: as) = Silmaril.Wasm.Execution.Core.Admin.norm m a :: Silmaril.Wasm.Execution.Core.Admin.normList m as := by
  simp [Silmaril.Wasm.Execution.Core.Admin.normList]

theorem Silmaril.Wasm.Execution.Core.Admin.normList_eq_map (m : CModuleInst) (l : List CAdmin) :
    Silmaril.Wasm.Execution.Core.Admin.normList m l = l.map (Silmaril.Wasm.Execution.Core.Admin.norm m) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem Silmaril.Wasm.Execution.Core.Admin.norm_plain (m : CModuleInst) (i : Silmaril.Wasm.Instr)
    (h₁ : ∀ x, i ≠ .callRef x) (h₂ : ∀ x, i ≠ .returnCallRef x) :
    Silmaril.Wasm.Execution.Core.Admin.norm m (.plain i) = .plain i := by
  cases i <;> simp_all [Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_ref (m : CModuleInst) (r : Ref) : Silmaril.Wasm.Execution.Core.Admin.norm m (.ref r) = .ref r := by
  simp [Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_trap (m : CModuleInst) : Silmaril.Wasm.Execution.Core.Admin.norm m .trap = .trap := by
  simp [Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_callRefType (m : CModuleInst) (d : DefType) :
    Silmaril.Wasm.Execution.Core.Admin.norm m (.callRefType d) = .callRefType d := by simp [Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_returnCallRefType (m : CModuleInst) (d : DefType) :
    Silmaril.Wasm.Execution.Core.Admin.norm m (.returnCallRefType d) = .returnCallRefType d := by simp [Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_label (m : CModuleInst) (n : Nat) (k : List Silmaril.Wasm.Instr)
    (b : List CAdmin) : Silmaril.Wasm.Execution.Core.Admin.norm m (.label n k b) = .label n k (b.map (Silmaril.Wasm.Execution.Core.Admin.norm m)) := by
  simp [Silmaril.Wasm.Execution.Core.Admin.norm, Silmaril.Wasm.Execution.Core.Admin.normList_eq_map]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_handler (m : CModuleInst) (n : Nat) (cs : List Catch)
    (b : List CAdmin) : Silmaril.Wasm.Execution.Core.Admin.norm m (.handler n cs b) = .handler n cs (b.map (Silmaril.Wasm.Execution.Core.Admin.norm m)) := by
  simp [Silmaril.Wasm.Execution.Core.Admin.norm, Silmaril.Wasm.Execution.Core.Admin.normList_eq_map]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_frame (m : CModuleInst) (n : Nat) (f : CFrame) (b : List CAdmin) :
    Silmaril.Wasm.Execution.Core.Admin.norm m (.frame n f b) = .frame n (Frame.erase f) (b.map (Silmaril.Wasm.Execution.Core.Admin.norm f.module)) := by
  simp [Silmaril.Wasm.Execution.Core.Admin.norm, Silmaril.Wasm.Execution.Core.Admin.normList_eq_map]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_callRef (m : CModuleInst) (x : TypeIdx) :
    Silmaril.Wasm.Execution.Core.Admin.norm m (.plain (.callRef x)) = .callRefType ((m.types[x.toNat]?).getD default) := by
  simp [Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_returnCallRef (m : CModuleInst) (x : TypeIdx) :
    Silmaril.Wasm.Execution.Core.Admin.norm m (.plain (.returnCallRef x)) =
      .returnCallRefType ((m.types[x.toNat]?).getD default) := by
  simp [Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_toCore_plain (m : CModuleInst) (i : Instr) :
    Silmaril.Wasm.Execution.Core.Admin.norm m (.plain i.toCore) = .plain i.toCore :=
  Silmaril.Wasm.Execution.Core.Admin.norm_plain m _ (Instr.toCore_ne_callRef i) (Instr.toCore_ne_returnCallRef i)

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.norm_val (m : CModuleInst) (v : Val) : Silmaril.Wasm.Execution.Core.Admin.norm m v.toAdmin = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Silmaril.Wasm.Execution.Core.Admin.norm]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.map_norm_vals (m : CModuleInst) (vs : List Val) :
    (vals vs).map (Silmaril.Wasm.Execution.Core.Admin.norm m) = vals vs := by
  simp [vals]

@[simp] theorem Silmaril.Wasm.Execution.Core.Admin.map_norm_expression (m : CModuleInst) (es : Expr) :
    (Silmaril.Wasm.Execution.Core.expression (es.map Silmaril.Wasm.Lime1.Instr.toCore)).map
      (Silmaril.Wasm.Execution.Core.Admin.norm m) =
      Silmaril.Wasm.Execution.Core.expression (es.map Silmaril.Wasm.Lime1.Instr.toCore) := by
  simp [Silmaril.Wasm.Execution.Core.expression]

/-- Elements that normalisation does not produce from anything else. -/
def Rigid : CAdmin → Prop
  | .plain i => (∀ x, i ≠ .callRef x) ∧ (∀ x, i ≠ .returnCallRef x)
  | .ref _ => True
  | .trap => True
  | _ => False

theorem Rigid.norm {m : CModuleInst} {y : CAdmin} (hy : Rigid y) : Silmaril.Wasm.Execution.Core.Admin.norm m y = y := by
  cases y with
  | plain i => exact Silmaril.Wasm.Execution.Core.Admin.norm_plain m _ hy.1 hy.2
  | ref => simp
  | trap => simp
  | _ => simp [Rigid] at hy

theorem Rigid.eq_of_norm {m : CModuleInst} {x y : CAdmin} (hy : Rigid y)
    (h : Silmaril.Wasm.Execution.Core.Admin.norm m x = y) : x = y := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; simp at h; subst h; simp [Rigid] at hy
    by_cases h₂ : ∃ z, i = .returnCallRef z
    · obtain ⟨z, rfl⟩ := h₂; simp at h; subst h; simp [Rigid] at hy
    push Not at h₁ h₂
    rwa [Silmaril.Wasm.Execution.Core.Admin.norm_plain m i h₁ h₂] at h
  | label => simp at h; subst h; simp [Rigid] at hy
  | frame => simp at h; subst h; simp [Rigid] at hy
  | handler => simp at h; subst h; simp [Rigid] at hy
  | callRefType => simp at h; subst h; simp [Rigid] at hy
  | returnCallRefType => simp at h; subst h; simp [Rigid] at hy
  | ref => simpa using h
  | trap => simpa using h

theorem Rigid.val (v : Val) : Rigid v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Rigid]

theorem Rigid.toCore (i : Instr) : Rigid (.plain i.toCore) :=
  ⟨Instr.toCore_ne_callRef i, Instr.toCore_ne_returnCallRef i⟩

theorem map_norm_eq_of_rigid {m : CModuleInst} {l L : List CAdmin} (hL : ∀ y ∈ L, Rigid y)
    (h : l.map (Silmaril.Wasm.Execution.Core.Admin.norm m) = L) : l = L := by
  induction L generalizing l with
  | nil => simpa using h
  | cons y L ih =>
    rcases l with _ | ⟨x, l⟩
    · simp at h
    · simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hL
      rw [(hL.1).eq_of_norm h.1, ih hL.2 h.2]

theorem map_norm_vals {m : CModuleInst} {l : List CAdmin} {vs : List Val}
    (h : l.map (Silmaril.Wasm.Execution.Core.Admin.norm m) = vals vs) : l = vals vs :=
  map_norm_eq_of_rigid (by simp only [vals, List.mem_map]; rintro _ ⟨v, _, rfl⟩; exact Rigid.val v) h

theorem norm_eq_label {m : CModuleInst} {x : CAdmin} {n : Nat} {k : List Silmaril.Wasm.Instr}
    {b : List CAdmin} (h : Silmaril.Wasm.Execution.Core.Admin.norm m x = .label n k b) :
    ∃ b', x = .label n k b' ∧ b'.map (Silmaril.Wasm.Execution.Core.Admin.norm m) = b := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; simp at h
    by_cases h₂ : ∃ z, i = .returnCallRef z
    · obtain ⟨z, rfl⟩ := h₂; simp at h
    push Not at h₁ h₂
    rw [Silmaril.Wasm.Execution.Core.Admin.norm_plain m i h₁ h₂] at h; cases h
  | label n' k' b' => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨b', rfl, rfl⟩
  | _ => simp at h

theorem norm_eq_frame {m : CModuleInst} {x : CAdmin} {n : Nat} {f : CFrame} {b : List CAdmin}
    (h : Silmaril.Wasm.Execution.Core.Admin.norm m x = .frame n f b) :
    ∃ f' b', x = .frame n f' b' ∧ Frame.erase f' = f ∧ b'.map (Silmaril.Wasm.Execution.Core.Admin.norm f'.module) = b := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; simp at h
    by_cases h₂ : ∃ z, i = .returnCallRef z
    · obtain ⟨z, rfl⟩ := h₂; simp at h
    push Not at h₁ h₂
    rw [Silmaril.Wasm.Execution.Core.Admin.norm_plain m i h₁ h₂] at h; cases h
  | frame n' f' b' => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨f', b', rfl, rfl, rfl⟩
  | _ => simp at h

theorem norm_eq_callRefType {m : CModuleInst} {x : CAdmin} {d : DefType}
    (h : Silmaril.Wasm.Execution.Core.Admin.norm m x = .callRefType d) :
    x = .callRefType d ∨ ∃ y, x = .plain (.callRef y) ∧ (m.types[y.toNat]?).getD default = d := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; simp at h; exact .inr ⟨z, rfl, h⟩
    by_cases h₂ : ∃ z, i = .returnCallRef z
    · obtain ⟨z, rfl⟩ := h₂; simp at h
    push Not at h₁ h₂
    rw [Silmaril.Wasm.Execution.Core.Admin.norm_plain m i h₁ h₂] at h; cases h
  | callRefType d' => simp at h; exact .inl (by rw [h])
  | _ => simp at h

mutual
/-- Normalisation only reads the enclosing module's types. -/
theorem Silmaril.Wasm.Execution.Core.Admin.norm_congr {m m' : CModuleInst} (h : m.types = m'.types) :
    (x : CAdmin) → Silmaril.Wasm.Execution.Core.Admin.norm m x = Silmaril.Wasm.Execution.Core.Admin.norm m' x
  | .plain i => by
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; simp [h]
    by_cases h₂ : ∃ z, i = .returnCallRef z
    · obtain ⟨z, rfl⟩ := h₂; simp [h]
    push Not at h₁ h₂
    rw [Silmaril.Wasm.Execution.Core.Admin.norm_plain m i h₁ h₂, Silmaril.Wasm.Execution.Core.Admin.norm_plain m' i h₁ h₂]
  | .label n k b => by simp only [Silmaril.Wasm.Execution.Core.Admin.norm_label]; rw [Silmaril.Wasm.Execution.Core.Admin.map_norm_congr h b]
  | .handler n cs b => by simp only [Silmaril.Wasm.Execution.Core.Admin.norm_handler]; rw [Silmaril.Wasm.Execution.Core.Admin.map_norm_congr h b]
  | .frame n f b => by simp
  | .ref r => by simp
  | .callRefType d => by simp
  | .returnCallRefType d => by simp
  | .trap => by simp

theorem Silmaril.Wasm.Execution.Core.Admin.map_norm_congr {m m' : CModuleInst} (h : m.types = m'.types) :
    (l : List CAdmin) → l.map (Silmaril.Wasm.Execution.Core.Admin.norm m) = l.map (Silmaril.Wasm.Execution.Core.Admin.norm m')
  | [] => rfl
  | x :: l => by simp only [List.map_cons]; rw [Silmaril.Wasm.Execution.Core.Admin.norm_congr h x, Silmaril.Wasm.Execution.Core.Admin.map_norm_congr h l]
end

theorem ModuleInst.erase_toCore (m : Silmaril.Wasm.Execution.Runtime.ModuleInst) :
    ModuleInst.erase m.toCore = m.toCore := rfl

theorem Frame.erase_toCore (f : Silmaril.Wasm.Execution.Runtime.Frame) :
    Frame.erase f.toCore = f.toCore := rfl

theorem Store.erase_toCore (s : Store H) : Store.erase s.toCore = s.toCore := by
  simp only [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toCore, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

theorem Config.norm_eq_toCore_iff {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {a : Config H} :
    Config.norm ⟨cs, cf, cl⟩ = a.toCore ↔
      Store.erase cs = a.store.toCore ∧ Frame.erase cf = a.frame.toCore ∧
        cl.map (Silmaril.Wasm.Execution.Core.Admin.norm cf.module) = Silmaril.Wasm.Execution.Core.Admin.listToCore a.store a.code := by
  simp [Config.norm, Silmaril.Wasm.Execution.Runtime.Config.toCore, Silmaril.Wasm.Execution.Core.Admin.normList_eq_map]

end ToCore

open ToCore in
mutual
theorem map_norm_toCore (m : CModuleInst) (s : Store H) :
    (a : Silmaril.Wasm.Execution.Core.Admin) → (Silmaril.Wasm.Execution.Core.Admin.toCore s a).map (ToCore.Admin.norm m) = Silmaril.Wasm.Execution.Core.Admin.toCore s a
  | .source i => by simp
  | .invoke a => by simp
  | .label n cont body => by simp [map_norm_listToCore m s body]
  | .frame n f body => by
    simp only [frame_toCore, List.map_cons, List.map_nil, ToCore.Admin.norm_frame]
    rw [map_norm_listToCore _ s body, ToCore.Frame.erase_toCore]
  | .trap => by simp

theorem map_norm_listToCore (m : CModuleInst) (s : Store H) :
    (l : List Silmaril.Wasm.Execution.Core.Admin) → (Silmaril.Wasm.Execution.Core.Admin.listToCore s l).map (ToCore.Admin.norm m) = Silmaril.Wasm.Execution.Core.Admin.listToCore s l
  | [] => by simp
  | a :: as => by
    simp only [listToCore_cons, List.map_append]
    rw [map_norm_toCore m s a, map_norm_listToCore m s as]
end

/-- Lime1 images are normal. -/
theorem Sim.refl_toCore (a : Config H) (hwf : ConfigWF a) : Sim a a.toCore := by
  refine ⟨?_, hwf⟩
  simp only [ToCore.Config.norm, Silmaril.Wasm.Execution.Runtime.Config.toCore,
    ToCore.Store.erase_toCore, ToCore.Frame.erase_toCore, ToCore.Admin.normList_eq_map,
    map_norm_listToCore]

end Silmaril.Wasm.Lime1.Execution
