module

public import Silmaril.Wasm.Binaryen.GrowOOMLiteralRuntime
public import Silmaril.Wasm.Binaryen.GrowWrapperPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOMLiteral

open Execution.Core Execution.Core.Sim Numerics Validation
open Silmaril.Wasm.SingleThreaded.Det

set_option maxHeartbeats 2000000

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Both address-width output modules validate, including the inserted guard. -/
theorem validate_eq (a : AddrType) (n : BitVec a.intType.width) :
    validate? (mod a n) = some (GrowWrapper.moduleType a) := by
  cases a <;> with_unfolding_all rfl

theorem module_ok (a : AddrType) (n : BitVec a.intType.width) : ModuleOk (mod a n) (GrowWrapper.moduleType a) :=
  validate?_sound (validate_eq a n)

def store (s : Store H) (a : AddrType) (n : BitVec a.intType.width) : Store H :=
  { s with
    mems := s.mems ++ [MemoryGrowFailure.emptyMemory a]
    funcs := s.funcs ++ [⟨GrowWrapper.dt a, GrowWrapper.moduleInst s a, .wasm (func a n)⟩] }

def initial (s : Store H) (a : AddrType) (n : BitVec a.intType.width) : Config H :=
  ⟨store s a n, {module := GrowWrapper.moduleInst s a}, []⟩

theorem instantiate_eq (s : Store H) (a : AddrType) (n : BitVec a.intType.width) :
    instantiate? evalConst? s (mod a n) [] = some (initial s a n) := by
  cases a <;> with_unfolding_all rfl

/-- No totality assumption: the guarded module really instantiates in the same
ambient store, with the same empty import interface. -/
theorem instantiate (s : Store H) (a : AddrType) (n : BitVec a.intType.width) :
    Instantiate P host s (mod a n) [] (initial s a n) :=
  (instantiate?_iff ⟨_, [], module_ok a n, .nil⟩).mp (instantiate_eq s a n)

theorem instantiate_inv {s : Store H} {a : AddrType} {n : BitVec a.intType.width}
    {imports : List ExternAddr} {c : Config H}
    (hi : Instantiate P host s (mod a n) imports c) :
    imports = [] ∧ c = initial s a n := by
  obtain ⟨xtE, xtI, hm, hxa⟩ := hi.valid
  have ht := congrArg CModuleType.imports (hm.unique (module_ok a n))
  change xtI = [] at ht
  subst xtI
  have hx : imports = [] := by cases hxa; rfl
  subst imports
  exact ⟨rfl, Option.some.inj ((instantiate?_evalConst_complete hi).symm.trans
    (instantiate_eq s a n))⟩

theorem func_lookup (s : Store H) (a : AddrType) (n : BitVec a.intType.width) :
    (store s a n).funcs[s.funcs.length]? =
      some ⟨GrowWrapper.dt a, GrowWrapper.moduleInst s a, .wasm (func a n)⟩ := by
  simp [store]

end Silmaril.Wasm.Binaryen.GrowOOMLiteral
