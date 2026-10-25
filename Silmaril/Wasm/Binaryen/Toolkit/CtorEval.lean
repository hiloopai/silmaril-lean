module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalRuntime
public import Silmaril.Wasm.Binaryen.GrowWrapperPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

open Execution.Core Execution.Core.Sim Numerics Validation

set_option maxHeartbeats 2000000

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Successful recognition retains every source field. -/
theorem recognize?_sound {m : Module} {p : Params} (h : recognize? m = some p) :
    m = mod p.type p.initial p.value false := by
  unfold recognize? at h
  split at h
  · split at h
    · rename_i hm
      obtain ⟨rfl, rfl⟩ := hm
      cases h
      rfl
    · cases h
  · split at h
    · rename_i hm
      obtain ⟨rfl, rfl⟩ := hm
      cases h
      rfl
    · cases h
  · cases h

theorem recognize?_complete (t : IntType) (i v : BitVec t.width) :
    recognize? (mod t i v false) = some ⟨t, i, v⟩ := by
  cases t <;> with_unfolding_all rfl

def dt (t : IntType) (getter : Bool) : DefType :=
  (allocTypes (types t))[if getter then 1 else 0]!

@[simp] theorem type_get_ctor (t : IntType) :
    (allocTypes (types t))[0]? = some (dt t false) := by cases t <;> rfl

@[simp] theorem type_get_getter (t : IntType) :
    (allocTypes (types t))[1]? = some (dt t true) := by cases t <;> rfl

def moduleInst (s : Store H) (t : IntType) : ModuleInst :=
  { types := allocTypes (types t), globals := [s.globals.length + 1],
    funcs := [s.funcs.length, s.funcs.length + 1],
    exports := [⟨"get", .func (s.funcs.length + 1)⟩,
      ⟨"state", .global (s.globals.length + 1)⟩] }

/-- Keep the inaccessible provisional initializer slot explicit: Core's
initializer evaluation allocates it before final module-global allocation. -/
def store (s : Store H) (t : IntType) (scratch current value : BitVec t.width) : Store H :=
  { s with
    globals := s.globals ++ [⟨⟨.var, .num (.int t)⟩, .num ⟨.int t, scratch⟩⟩,
      ⟨⟨.var, .num (.int t)⟩, .num ⟨.int t, current⟩⟩],
    funcs := s.funcs ++ [⟨dt t false, moduleInst s t, .wasm (ctor t value)⟩,
      ⟨dt t true, moduleInst s t, .wasm getter⟩] }

def initial (s : Store H) (t : IntType) (i v : BitVec t.width) (evaluated : Bool) : Config H :=
  let x := if evaluated then v else i
  ⟨store s t x x v, {module := moduleInst s t}, if evaluated then [] else [.plain (.call ⟨0⟩)]⟩

def moduleType (t : IntType) : CModuleType :=
  ⟨[], [.func (dt t true), .global ⟨.var, .num (.int t)⟩]⟩

theorem validate_eq (t : IntType) (i v : BitVec t.width) (evaluated : Bool) :
    validate? (mod t i v evaluated) = some (moduleType t) := by
  cases t <;> cases evaluated <;> with_unfolding_all rfl

theorem module_ok (t : IntType) (i v : BitVec t.width) (evaluated : Bool) :
    ModuleOk (mod t i v evaluated) (moduleType t) := validate?_sound (validate_eq t i v evaluated)

theorem instantiate_eq (s : Store H) (t : IntType) (i v : BitVec t.width) (evaluated : Bool) :
    instantiate? evalConst? s (mod t i v evaluated) [] = some (initial s t i v evaluated) := by
  cases t <;> cases evaluated <;>
    simp [instantiate?, mod, initial, store, moduleInst, evalGlobals?, evalConst?, constExpr?,
      constInstr?, evalExprs?, evalExprss?, allocModule?, allocGlobal, allocMany,
      allocFunc, allocExport?, ExternAddr.globals, ExternAddr.funcs, ExternAddr.tags,
      ExternAddr.mems, ExternAddr.tables, ModuleInst.initial, Idx.toNat,
      ctor, getter, exports, expression, List.range_succ, List.append_assoc] <;>
      with_unfolding_all rfl

theorem instantiate (s : Store H) (t : IntType) (i v : BitVec t.width) (evaluated : Bool) :
    Instantiate P host s (mod t i v evaluated) [] (initial s t i v evaluated) :=
  (instantiate?_iff ⟨_, [], module_ok t i v evaluated, .nil⟩).mp (instantiate_eq s t i v evaluated)

theorem instantiate_inv {s : Store H} {t : IntType} {i v : BitVec t.width} {evaluated : Bool}
    {imports : List ExternAddr} {c : Config H}
    (hi : Instantiate P host s (mod t i v evaluated) imports c) :
    imports = [] ∧ c = initial s t i v evaluated := by
  obtain ⟨xtE, xtI, hm, hxa⟩ := hi.valid
  have ht := congrArg CModuleType.imports (hm.unique (module_ok t i v evaluated))
  change xtI = [] at ht
  subst xtI
  have hx : imports = [] := by cases hxa; rfl
  subst imports
  exact ⟨rfl, Option.some.inj ((instantiate?_evalConst_complete hi).symm.trans
    (instantiate_eq s t i v evaluated))⟩

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
