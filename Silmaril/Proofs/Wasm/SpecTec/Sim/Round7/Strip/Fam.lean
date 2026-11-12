module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Basic

/-!
# Round 7: the per-family reduction relations do not read exports

Every reduction family that `Step` delegates to (`ParametricStep`, `NumericStep`, `VectorStep`,
`VariableStep`, `TableStep`, `MemoryStep`, `RefStep`, `AggregateStep`) works on code without
labels, handlers or frames (`*_atomic`), never changes the store's function instances or the
frame's module, and never reads `ModuleInst.exports` or a function instance's module. So it
commutes with replacing the function instances by others of the same types and the frame's
exports by anything (`*_setEx`), and it is a simulation of `ExRel` (`exRel_fam`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The configuration `c` with the function instances `F` and the frame's exports `E`. -/
def setEx (F : List (FuncInst H)) (E : List ExportInst) (c : Config H) : Config H :=
  ⟨{ c.store with funcs := F }, { c.frame with module := { c.frame.module with exports := E } },
    c.code⟩

/-! ## References only read the types of function instances -/

theorem types_of_stripFI {F G : List (FuncInst H)} (h : F.map stripFI = G.map stripFI) (a : Nat) :
    (F[a]?).map FuncInst.type = (G[a]?).map FuncInst.type := by
  have h' := congrArg (fun l => (l[a]?).map FuncInst.type) h
  simpa [stripFI, Option.map_map, Function.comp_def] using h'

theorem refOk_withFuncs {s : Store H} {F : List (FuncInst H)}
    (hF : F.map stripFI = s.funcs.map stripFI) {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    RefOk { s with funcs := F } r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h =>
      rename_i a fi
      have ht := types_of_stripFI hF a
      rw [h] at ht
      obtain ⟨fi', hfi', hty⟩ := Option.map_eq_some_iff.mp ht
      exact hty ▸ .func hfi'
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_withFuncs_iff {s : Store H} {F : List (FuncInst H)}
    (hF : F.map stripFI = s.funcs.map stripFI) {r : Ref} {rt : CRefType} :
    RefOk { s with funcs := F } r rt ↔ RefOk s r rt :=
  ⟨fun h => refOk_withFuncs (s := { s with funcs := F }) hF.symm h, refOk_withFuncs hF⟩

/-! ## The families commute with `setEx` -/

theorem variableStep_setEx {c c' : Config H} (h : VariableStep c c') (F : List (FuncInst H))
    (E : List ExportInst) : VariableStep (setEx F E c) (setEx F E c') := by
  cases h <;> simp only [setEx] <;> constructor! <;> assumption

theorem tableStep_setEx {P : Profile} {c c' : Config H} (h : TableStep P c c')
    (F : List (FuncInst H)) (E : List ExportInst) : TableStep P (setEx F E c) (setEx F E c') := by
  cases h <;> simp only [setEx] <;> constructor! <;> assumption

theorem memoryStep_setEx {P : Profile} {c c' : Config H} (h : MemoryStep P c c')
    (F : List (FuncInst H)) (E : List ExportInst) :
    MemoryStep P (setEx F E c) (setEx F E c') := by
  cases h <;> simp only [setEx] <;> constructor! <;> assumption

theorem aggregateStep_setEx {c c' : Config H} (h : AggregateStep c c') (F : List (FuncInst H))
    (E : List ExportInst) : AggregateStep (setEx F E c) (setEx F E c') := by
  cases h <;> simp only [setEx] <;>
    first
      | (constructor! <;> assumption)
      | (apply AggregateStep.arrayCopyOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitElemOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitDataOob₂ <;> assumption)

theorem refStep_setEx {c c' : Config H} (h : RefStep c c') (F : List (FuncInst H))
    (hF : F.map stripFI = c.store.funcs.map stripFI) (E : List ExportInst) :
    RefStep (setEx F E c) (setEx F E c') := by
  cases h <;> simp only [setEx] at hF ⊢ <;> constructor! <;>
    first
      | assumption
      | exact (refOk_withFuncs_iff hF).mpr ‹_›
      | exact fun h' => ‹¬ _› ((refOk_withFuncs_iff hF).mp h')

/-! ## The families keep the function instances and the frame's module -/

theorem variableStep_funcs {c c' : Config H} (h : VariableStep c c') :
    c'.store.funcs = c.store.funcs ∧ c'.frame.module = c.frame.module := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem tableStep_funcs {P : Profile} {c c' : Config H} (h : TableStep P c c') :
    c'.store.funcs = c.store.funcs ∧ c'.frame.module = c.frame.module := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem memoryStep_funcs {P : Profile} {c c' : Config H} (h : MemoryStep P c c') :
    c'.store.funcs = c.store.funcs ∧ c'.frame.module = c.frame.module := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem aggregateStep_funcs {c c' : Config H} (h : AggregateStep c c') :
    c'.store.funcs = c.store.funcs ∧ c'.frame.module = c.frame.module := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem refStep_funcs {c c' : Config H} (h : RefStep c c') :
    c'.store.funcs = c.store.funcs ∧ c'.frame.module = c.frame.module := by
  cases h <;> exact ⟨rfl, rfl⟩

/-! ## The families work on code without labels, handlers or frames -/

theorem forall_mem_vals_atomic (vs : List Val) : ∀ a ∈ vals vs, Atomic a := allAtomic_vals vs

theorem atomic_plain (i : Instr) : Atomic (.plain i) := True.intro
theorem atomic_ref (r : Ref) : Atomic (.ref r) := True.intro
theorem atomic_trap : Atomic .trap := True.intro
theorem atomic_constI32 (c : BitVec 32) : Atomic (constI32 c) := atomic_toAdmin _
theorem atomic_callRefType (d : DefType) : Atomic (.callRefType d) := True.intro
theorem atomic_returnCallRefType (d : DefType) : Atomic (.returnCallRefType d) := True.intro

attribute [local simp] atomic_toAdmin forall_mem_vals_atomic atomic_plain atomic_ref atomic_trap atomic_constI32
  atomic_callRefType atomic_returnCallRefType

theorem parametricStep_atomic {is is' : List Admin} (h : ParametricStep is is') : AllAtomic is := by
  cases h <;> simp [AllAtomic, or_imp, forall_and]

theorem numericStep_atomic {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    AllAtomic is := by
  cases h <;> simp [AllAtomic, or_imp, forall_and]

theorem vectorStep_atomic {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    AllAtomic is := by
  cases h <;> simp [AllAtomic, or_imp, forall_and]

theorem variableStep_atomic {c c' : Config H} (h : VariableStep c c') : AllAtomic c.code := by
  cases h <;> simp [AllAtomic, or_imp, forall_and]

theorem tableStep_atomic {P : Profile} {c c' : Config H} (h : TableStep P c c') :
    AllAtomic c.code := by
  cases h <;> simp [AllAtomic, or_imp, forall_and]

theorem memoryStep_atomic {P : Profile} {c c' : Config H} (h : MemoryStep P c c') :
    AllAtomic c.code := by
  cases h <;> simp [AllAtomic, or_imp, forall_and]

theorem aggregateStep_atomic {c c' : Config H} (h : AggregateStep c c') : AllAtomic c.code := by
  cases h <;> simp [AllAtomic, or_imp, forall_and] <;> exact forall_mem_vals_atomic _

theorem refStep_atomic {c c' : Config H} (h : RefStep c c') : AllAtomic c.code := by
  cases h <;> simp [AllAtomic, or_imp, forall_and]

/-! ## The families are simulations of `ExRel` -/

/-- A configuration related to `c`, whose code is atomic, is `c` with other function instances
and frame exports. -/
theorem exRel_setEx {c d : Config H} (hat : AllAtomic c.code) (hd : ExRel c d) :
    ∃ F E, F.map stripFI = c.store.funcs.map stripFI ∧ d = setEx F E c := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨F, E, js, rfl, hF, hjs⟩ := exRel_nf hd
  exact ⟨F, E, hF, by rw [stripAdmins_eq_atomic hat hjs]; rfl⟩

theorem exRel_setEx_of {c : Config H} {F : List (FuncInst H)} (E : List ExportInst)
    (hF : F.map stripFI = c.store.funcs.map stripFI) : ExRel c (setEx F E c) :=
  exRel_mk (stripStore_withFuncs c.store hF).symm (stripFrame_withEx c.frame E).symm rfl

/-- **A family step is a simulation of `ExRel`**, from the three facts above. -/
theorem exRel_fam {R : Config H → Config H → Prop} {c c' d : Config H} (hat : AllAtomic c.code)
    (htr : ∀ F E, F.map stripFI = c.store.funcs.map stripFI → R (setEx F E c) (setEx F E c'))
    (hfun : c'.store.funcs = c.store.funcs) (hd : ExRel c d) :
    ∃ d', R d d' ∧ ExRel c' d' := by
  obtain ⟨F, E, hF, rfl⟩ := exRel_setEx hat hd
  exact ⟨setEx F E c', htr F E hF, exRel_setEx_of E (hfun ▸ hF)⟩

end Silmaril.Wasm.SpecTec.Sim.Round7
