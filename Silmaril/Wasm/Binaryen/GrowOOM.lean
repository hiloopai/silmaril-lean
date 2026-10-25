module

public import Silmaril.Wasm.Binaryen.GrowOOMRuntime
public import Silmaril.Wasm.Binaryen.GrowWrapperPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOM

open Execution.Core Execution.Core.Sim Numerics Validation
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The source recognizer identifies the entire retained module. -/
theorem recognize?_sound {m : Module} {a : AddrType} (h : recognize? m = some a) :
    m = GrowWrapper.mod a 0 false := by
  unfold recognize? at h
  cases hr : GrowWrapper.recognize? m with
  | none => simp [hr] at h
  | some p =>
    simp only [hr, bind, Option.bind] at h
    split at h
    · rename_i hz
      cases Option.some.inj h
      simpa only [hz] using GrowWrapper.recognize?_sound hr
    · cases h

theorem recognize?_complete (a : AddrType) :
    recognize? (GrowWrapper.mod a 0 false) = some a := by
  simp [recognize?, GrowWrapper.recognize?_complete]

theorem optimize_of_rejected {m : BModule} (h : recognize? m.lower = none) :
    optimize m = m := by simp [optimize, h]

@[simp] theorem optimize_zero_wrapper (a : AddrType) :
    optimize (BModule.lift (GrowWrapper.mod a 0 false)) = BModule.lift (mod a) := by
  rw [optimize, lower_lift, recognize?_complete]

/-- Both address-width output modules validate, including the inserted guard. -/
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

/-- No totality assumption: the guarded module really instantiates in the same
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

end Silmaril.Wasm.Binaryen.GrowOOM
