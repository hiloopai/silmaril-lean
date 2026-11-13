module

public import Silmaril.Wasm.Models.V10.Defs
public import Silmaril.Wasm.V1.Validation.Examples

/-!
# A valid 1.0 module that is not a valid 2.0 module

`definedGlobalOffset`: one memory, one defined immutable `i32` global and one data segment whose
offset reads that global. Wasm 1.0 checks segment offsets in the full module context, so it is
valid (`definedGlobalOffset_valid`); Wasm 2.0 checks them in `C'`, whose globals are the
imported ones only (`wasm-2.0/6-typing:703`), so its 2.0 image is invalid
(`definedGlobalOffset_toV2_invalid`). The 1.0 analogue of silmaril's Lime1 counterexample
`Lime1.Validation.definedGlobalOffsetModule`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10

open Silmaril.Wasm Silmaril.Wasm.V1 Silmaril.Wasm.V1.Validation

/-- The data segment: memory 0, offset `global.get 0`. -/
def definedGlobalOffsetData : Silmaril.Wasm.V1.Data :=
  ⟨⟨⟨0, Nat.two_pow_pos 32⟩⟩, [.globalGet ⟨⟨0, Nat.two_pow_pos 32⟩⟩], ByteArray.empty⟩

/-- **The module.** -/
def definedGlobalOffset : Silmaril.Wasm.V1.Module where
  memories := [⟨⟨⟨0, Nat.two_pow_pos 32⟩, none⟩⟩]
  globals := [⟨⟨.const, .i32⟩, [.intConst .i32 8]⟩]
  data := [definedGlobalOffsetData]

theorem definedGlobalOffset_memories :
    ∀ mt ∈ definedGlobalOffset.memories, MemoryTypeValid mt := by
  intro mt hmt
  have e : mt = ⟨⟨⟨0, Nat.two_pow_pos 32⟩, none⟩⟩ := List.mem_singleton.mp hmt
  rw [e]
  exact ⟨Nat.zero_le _, by simp⟩

theorem definedGlobalOffset_globals :
    ∀ g ∈ definedGlobalOffset.globals, GlobalValid (initializerContext definedGlobalOffset) g := by
  intro g hg
  have e : g = ⟨⟨.const, .i32⟩, [.intConst .i32 8]⟩ := List.mem_singleton.mp hg
  rw [e]
  refine ⟨.cons (.intConst .i32 8) (.nil _), fun i hi => ?_⟩
  have ei : i = .intConst .i32 8 := List.mem_singleton.mp hi
  rw [ei]
  exact .intConst _ _

theorem definedGlobalOffset_data :
    ∀ d ∈ definedGlobalOffset.data, DataValid (moduleContext definedGlobalOffset) d := by
  intro d hd
  have e : d = definedGlobalOffsetData := List.mem_singleton.mp hd
  rw [e]
  refine ⟨⟨_, rfl⟩, ⟨.cons (.globalGet _ rfl) (.nil _), fun i hi => ?_⟩⟩
  have ei : i = .globalGet ⟨⟨0, Nat.two_pow_pos 32⟩⟩ := List.mem_singleton.mp hi
  rw [ei]
  exact .globalGet _ rfl

theorem definedGlobalOffset_valid : ModuleValid definedGlobalOffset where
  types := by simp [definedGlobalOffset]
  imports := by simp [definedGlobalOffset]
  functions := by simp [definedGlobalOffset]
  tables := by simp [definedGlobalOffset]
  memories := definedGlobalOffset_memories
  globals := definedGlobalOffset_globals
  elements := by simp [definedGlobalOffset]
  data := definedGlobalOffset_data
  start := by simp [StartValid, definedGlobalOffset]
  exports := by simp [definedGlobalOffset]
  uniqueExports := by simp [definedGlobalOffset]
  singleTable := by simp [moduleContext, definedGlobalOffset]
  singleMemory := by simp [moduleContext, definedGlobalOffset]

theorem definedGlobalOffset_toV2_invalid :
    ¬ Silmaril.Wasm.V2.Validation.ModuleValid definedGlobalOffset.toV2 := by
  rintro ⟨ixt, xt, hok⟩
  obtain ⟨-, himports, -, -, -, -, hdatas, -, -, -, -, -, -, rfl⟩ := hok
  have hixt : ixt = [] := by
    have hlen := himports.length_eq
    simp only [Silmaril.Wasm.V1.Module.toV2, Silmaril.Wasm.Lime1.Module.toV2,
      Silmaril.Wasm.V1.Module.toLime, definedGlobalOffset, List.map_nil,
      List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  subst hixt
  have hmem : Silmaril.Wasm.Lime1.Data.toV2 (Silmaril.Wasm.V1.Data.toLime definedGlobalOffsetData) ∈
      definedGlobalOffset.toV2.data := by
    simp [Silmaril.Wasm.V1.Module.toV2, Silmaril.Wasm.Lime1.Module.toV2,
      Silmaril.Wasm.V1.Module.toLime, definedGlobalOffset]
  cases hdatas _ hmem with
  | active hx hmem hoff =>
    refine Silmaril.Wasm.V2.Validation.InstrsOk.singleton_elim hoff.typed (fun it' hit' => ?_)
    obtain ⟨gt, hgt, -⟩ := Silmaril.Wasm.V2.Validation.InstrOk.globalGet_inv hit'
    simp [Silmaril.Wasm.V2.ExternType.globals] at hgt

/-- A 1.0 module whose only type has two results (1.0 has no multi-value). -/
def twoResults : Silmaril.Wasm.V1.Module where
  types := [⟨[], [.i32, .i64]⟩]

theorem twoResults_invalid : ¬ ModuleValid twoResults :=
  Silmaril.Wasm.V1.Validation.Examples.two_results_invalid

/-- Its 2.0 image is valid: 2.0 has multi-value. -/
theorem twoResults_toV2_valid : Silmaril.Wasm.V2.Validation.ModuleValid twoResults.toV2 := by
  refine ⟨[], [], .mk (ft' := [Silmaril.Wasm.Lime1.FuncType.toV2 ⟨[], [.i32, .i64]⟩]) (ft := [])
    (gt := []) (tt := []) (mt := []) (rt := []) (.cons ⟨rfl, trivial⟩ .nil) .nil .nil .nil .nil .nil
    ?_ .nil ?_ .nil ?_ ?_ rfl rfl⟩
  · intro d hd
    simp [Silmaril.Wasm.V1.Module.toV2, Silmaril.Wasm.Lime1.Module.toV2,
      Silmaril.Wasm.V1.Module.toLime, twoResults] at hd
  · intro x hx
    simp [Silmaril.Wasm.V1.Module.toV2, Silmaril.Wasm.Lime1.Module.toV2,
      Silmaril.Wasm.V1.Module.toLime, twoResults] at hx
  · simp [Silmaril.Wasm.V2.ExternType.mems]
  · simp [Silmaril.Wasm.V1.Module.toV2, Silmaril.Wasm.Lime1.Module.toV2,
      Silmaril.Wasm.V1.Module.toLime, twoResults]

end Silmaril.Proofs.Wasm.Models.V10
