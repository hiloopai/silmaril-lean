module

public import Silmaril.Wasm.Component.Engine.Core3K.Defs
public import Silmaril.Wasm.Execution.MemRep.Inst.Thms

/-! Proofs for `Silmaril.Wasm.Component.Engine.Core3K.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Core3K

open Silmaril.Wasm Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Engine.Core3
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

variable {H R : Type} [MemRep R]

theorem externTypeE?_toBytes (s : Store H R) (xa : ExternAddr) :
    externTypeE? s.toBytes xa = externTypeE? s xa := by
  unfold externTypeE?
  rw [externAddrType?_toBytes]

theorem prepareE?_toBytes [LawfulMemRep R] (s : Store H R) (m : Module) (xas : List ExternAddr) :
    prepareE? s.toBytes m xas = (prepareE? s m xas).map fun r => (r.1.toBytes, r.2) := by
  unfold prepareE?
  rcases validate? m with _ | mt
  · rfl
  · dsimp only
    rw [externAddrsOk?_toBytes]
    split_ifs
    · rw [← instantiateOnce?_toBytes]
      rcases instantiateOnce? s m xas with _ | ⟨s', f', _ | x⟩
      · rfl
      · rfl
      · dsimp only [Option.map_some]
        rcases f'.module.funcs[x.toNat]? with _ | a <;> rfl
    · rfl

theorem statusE_toBytes [LawfulMemRep R] (o : GrowOracle) (s : Store H R) (t : Thread) :
    statusE o s.toBytes t = statusE o s t := by
  unfold statusE
  rw [Exec.statusC_toBytes]

theorem internalC_some_toBytes [LawfulMemRep R] (o : GrowOracle) {s s' : Store H R}
    {t t' : Thread} (h : internalC (Exec.stepI o) (s, t) = some (s', t')) :
    internalC (Exec.stepI o) (s.toBytes, t) = some (s'.toBytes, t') := by
  rw [← Exec.internalC_toBytes, h]
  rfl

theorem internalC_lift_toBytes [LawfulMemRep R] (o : GrowOracle) {s : Store H R} {t : Thread}
    {c' : Store H × Thread} (h : internalC (Exec.stepI o) (s.toBytes, t) = some c') :
    ∃ s' t', internalC (Exec.stepI o) (s, t) = some (s', t') ∧ c' = (s'.toBytes, t') := by
  rw [← Exec.internalC_toBytes] at h
  obtain ⟨⟨s', t'⟩, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨s', t', h1, rfl⟩

end Silmaril.Proofs.Wasm.Component.Core3K
