module

public import Silmaril.Wasm.Binaryen.GrowZeroSuccessRuntime
public import Silmaril.Wasm.Binaryen.GrowOOMMode
public import Silmaril.Wasm.Binaryen.GrowWrapperPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowZeroSuccess

open Execution.Core Execution.Core.Sim Numerics Validation
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Successful recognition identifies the complete source module. -/
theorem recognize?_sound {m : Module} {a : AddrType} (h : recognize? m = some a) :
    m = GrowOOM.mod a := by
  unfold recognize? at h
  split at h
  · split at h
    · rename_i accepted
      obtain ⟨metadata, body⟩ := accepted
      obtain ⟨rfl, hm, rfl⟩ := metadata
      have hb := Exe.instrsEqb_sound body
      cases h
      cases hm
      cases hb
      rfl
    · cases h
  · cases h

theorem recognize?_complete (a : AddrType) :
    recognize? (GrowOOM.mod a) = some a := by
  cases a <;> with_unfolding_all rfl

theorem optimize_of_rejected {m : BModule} (h : recognize? m.lower = none) :
    optimize m = m := by simp [optimize, h]

@[simp] theorem optimize_guarded_wrapper (a : AddrType) :
    optimize (BModule.lift (GrowOOM.mod a)) = BModule.lift (mod a) := by
  rw [optimize, lower_lift, recognize?_complete]

/-- Both address-width output modules validate, retaining the same empty memory. -/
theorem validate_eq (a : AddrType) :
    validate? (mod a) = some (GrowWrapper.moduleType a) := by
  cases a <;> with_unfolding_all rfl

theorem module_ok (a : AddrType) : ModuleOk (mod a) (GrowWrapper.moduleType a) :=
  validate?_sound (validate_eq a)

def store (s : Store H) (a : AddrType) : Store H :=
  { s with
    mems := s.mems ++ [MemoryGrowFailure.emptyMemory a]
    funcs := s.funcs ++ [⟨GrowWrapper.dt a, GrowWrapper.moduleInst s a, .wasm (func a)⟩] }

def initial (s : Store H) (a : AddrType) : Config H :=
  ⟨store s a, {module := GrowWrapper.moduleInst s a}, []⟩

theorem instantiate_eq (s : Store H) (a : AddrType) :
    instantiate? evalConst? s (mod a) [] = some (initial s a) := by
  cases a <;> with_unfolding_all rfl

/-- No totality assumption: the constant-return module really instantiates in the same
ambient store, with the same empty import interface. -/
theorem instantiate (s : Store H) (a : AddrType) :
    Instantiate P host s (mod a) [] (initial s a) :=
  (instantiate?_iff ⟨_, [], module_ok a, .nil⟩).mp (instantiate_eq s a)

theorem instantiate_inv {s : Store H} {a : AddrType}
    {imports : List ExternAddr} {c : Config H}
    (hi : Instantiate P host s (mod a) imports c) :
    imports = [] ∧ c = initial s a := by
  obtain ⟨xtE, xtI, hm, hxa⟩ := hi.valid
  have ht := congrArg CModuleType.imports (hm.unique (module_ok a))
  change xtI = [] at ht
  subst xtI
  have hx : imports = [] := by cases hxa; rfl
  subst imports
  exact ⟨rfl, Option.some.inj ((instantiate?_evalConst_complete hi).symm.trans
    (instantiate_eq s a))⟩

theorem func_lookup (s : Store H) (a : AddrType) :
    (store s a).funcs[s.funcs.length]? =
      some ⟨GrowWrapper.dt a, GrowWrapper.moduleInst s a, .wasm (func a)⟩ := by
  simp [store]

theorem invokeOk_iff (s : Store H) (a : AddrType) (vs : List Val) :
    InvokeOk (store s a) s.funcs.length vs ↔ vs = [] := by
  constructor
  · rintro ⟨fi, ps, rs, hf, he, hv⟩
    rw [func_lookup] at hf
    cases hf
    obtain ⟨rfl, _⟩ := GrowWrapper.expand_dt_inv (a := a) he
    change List.Forall₂ _ vs [] at hv
    cases hv
    rfl
  · rintro rfl
    exact ⟨_, .nil, _, func_lookup s a, Expand.iff.mpr (GrowWrapper.expand_dt a), .nil⟩

theorem invoke_first (s : Store H) (a : AddrType) :
    Step P closedHost (invoke (store s a) s.funcs.length [])
      ⟨store s a, {}, [.frame 1 {module := GrowWrapper.moduleInst s a}
        [.label 1 [] (expression (func a).body)]]⟩ := by
  have h := Step.callRefFunc (P := P) (host := closedHost)
    (s := store s a) (f := {}) (c := .callRefType (GrowWrapper.dt a)) (vs := [])
    trivial (func_lookup s a) (Expand.iff.mpr (GrowWrapper.expand_dt a)) rfl rfl
  simpa [invoke, func_lookup, Frame.forCall, func, vals, Ty.length] using h

end Silmaril.Wasm.Binaryen.GrowZeroSuccess
