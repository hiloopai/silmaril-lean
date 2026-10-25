module

public import Silmaril.Wasm.Binaryen.MemoryGrowFailure
public import Silmaril.Wasm.Binaryen.GrowWrapperRuntime
public import Silmaril.Wasm.Binaryen.PassAPI.Modes
public import Silmaril.Wasm.Binaryen.LoopCex
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
public import Silmaril.Wasm.Validation.Check.Validate

/-! # Closed exported growth wrappers

A bounded whole-module client of the feasible refinement policy. The source
exports a no-argument growth wrapper and its memory; the target selects growth
failure for an arbitrary literal delta. No start function or imports are used.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowWrapper

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure

variable {H : Type} {P : Profile} {host : HostSemantics H}

def dt (a : AddrType) : DefType := (allocTypes [recType a]).head!

def moduleInst (s : Store H) (a : AddrType) : ModuleInst :=
  { types := allocTypes [recType a], mems := [s.mems.length], funcs := [s.funcs.length],
    exports := [⟨"grow", .func s.funcs.length⟩, ⟨"memory", .mem s.mems.length⟩] }

def store (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) : Store H :=
  { s with
    mems := s.mems ++ [emptyMemory a]
    funcs := s.funcs ++ [⟨dt a, moduleInst s a, .wasm (func a n failure)⟩] }

def initial (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) : Config H := ⟨store s a n failure, {module := moduleInst s a}, []⟩

theorem instantiate_eq (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) :
    instantiate? evalConst? s (mod a n failure) [] = some (initial s a n failure) := by
  cases a <;> cases failure <;> with_unfolding_all rfl

theorem valid (a : AddrType) (n : BitVec a.intType.width) (failure : Bool) :
    (validate? (mod a n failure)).isSome = true := by
  cases a <;> cases failure <;> with_unfolding_all rfl

theorem expand_dt (a : AddrType) :
    (dt a).expand? = some (.func .nil (.cons (.num (.int a.intType)) .nil)) := by
  cases a <;> rfl

theorem expand_dt_inv {a : AddrType} {ps rs : Ty (.list .val)}
    (he : Expand (dt a) (.func ps rs)) :
    ps = .nil ∧ rs = .cons (.num (.int a.intType)) .nil := by
  have h := (expand_dt a).symm.trans (Expand.iff.mp he)
  simpa only [Option.some.injEq, Ty.func.injEq] using h.symm

theorem func_lookup (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) :
    (store s a n failure).funcs[s.funcs.length]? =
      some ⟨dt a, moduleInst s a, .wasm (func a n failure)⟩ := by
  simp [store]

theorem invokeOk_iff (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) (vs : List Val) :
    InvokeOk (store s a n failure) s.funcs.length vs ↔ vs = [] := by
  constructor
  · rintro ⟨fi, ps, rs, hf, he, hv⟩
    rw [func_lookup] at hf
    cases hf
    obtain ⟨rfl, _⟩ := expand_dt_inv (a := a) he
    change List.Forall₂ _ vs [] at hv
    cases hv
    rfl
  · rintro rfl
    exact ⟨_, .nil, _, func_lookup s a n failure, Expand.iff.mpr (expand_dt a), .nil⟩


def moduleType (a : AddrType) : CModuleType :=
  ⟨[], [.func (dt a), .mem (emptyMemory a).type]⟩

theorem validate_eq (a : AddrType) (n : BitVec a.intType.width) (failure : Bool) :
    validate? (mod a n failure) = some (moduleType a) := by
  cases a <;> cases failure <;> with_unfolding_all rfl

theorem module_ok (a : AddrType) (n : BitVec a.intType.width) (failure : Bool) :
    ModuleOk (mod a n failure) (moduleType a) := validate?_sound (validate_eq a n failure)

/-- Allocation succeeds in every initial store and is independent of host and
numerical choices: this module has no imports or initializers. -/
theorem instantiate (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) :
    Instantiate P host s (mod a n failure) [] (initial s a n failure) :=
  (instantiate?_iff ⟨_, [], module_ok a n failure, .nil⟩).mp (instantiate_eq s a n failure)

/-- Every relational instantiation has exactly the computed allocation shape. -/
theorem instantiate_inv {s : Store H} {a : AddrType} {n : BitVec a.intType.width}
    {failure : Bool} {imports : List ExternAddr} {c : Config H}
    (hi : Instantiate P host s (mod a n failure) imports c) :
    imports = [] ∧ c = initial s a n failure := by
  obtain ⟨xtE, xtI, hm, hxa⟩ := hi.valid
  have ht := congrArg CModuleType.imports (hm.unique (module_ok a n failure))
  change xtI = [] at ht
  subst xtI
  have hx : imports = [] := by cases hxa; rfl
  subst imports
  exact ⟨rfl, Option.some.inj ((instantiate?_evalConst_complete hi).symm.trans
    (instantiate_eq s a n failure))⟩

theorem exportFunc_iff (s : Store H) (a : AddrType) (x : String) (addr : Nat) :
    exportFunc? (moduleInst s a) x = some addr ↔ x = "grow" ∧ addr = s.funcs.length := by
  by_cases hx : x = "grow"
  · subst x
    simp [exportFunc?, moduleInst, eq_comm]
  · by_cases hm : x = "memory"
    · subst x
      simp [exportFunc?, moduleInst]
    · simp [exportFunc?, moduleInst, List.find?, Ne.symm hx, hx, show ("memory" == x) = false from beq_eq_false_iff_ne.mpr (Ne.symm hm)]

end Silmaril.Wasm.Binaryen.GrowWrapper
