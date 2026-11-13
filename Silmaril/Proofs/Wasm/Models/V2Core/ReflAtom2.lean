module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflAtom

/-!
# Reflecting Core typings of 2.0 variable, table, memory, reference and branch instructions

The instructions whose rules read the context. Each lookup in the Core image context is the image
of a 2.0 lookup (`Rel.*_get`); Core subtyping between two image reference types is equality
(`toC_sub_toC`), which is what 2.0's `table.copy`, `table.init` and `call_indirect` ask for.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC)
open Silmaril.Wasm.Validation (TypeCtx TyOk)

/-- Invert a Core typing of a non-control instruction. -/
local macro "kinv " h:ident : tactic =>
  `(tactic| (cases $h:ident <;> rename_i $h:ident <;> cases $h:ident))

variable {C : VCtx} {D : KCtx} {it : Silmaril.Wasm.Validation.InstrType}

/-! ## Helpers -/

@[simp] theorem er_refToC (Δ : TypeCtx) (r : Silmaril.Wasm.V2.RefType) :
    er Δ (.refv r.toC) = .val (.ref r) := by
  cases r <;> rfl

theorem refToC_inj {r r' : Silmaril.Wasm.V2.RefType} (h : r.toC = r'.toC) : r = r' := by
  cases r <;> cases r' <;> first | rfl | cases h

/-- Core subtyping between image reference types is equality. -/
theorem refToC_sub (hR : Rel C D) {r r' : Silmaril.Wasm.V2.RefType}
    (h : Silmaril.Wasm.Validation.Sub D.toTypeCtx r.toC r'.toC) : r = r' := by
  have e := toC_sub_toC hR.typesOk hR.recs (t := .ref r) (u := .ref r') (.refv h)
  exact Silmaril.Wasm.V2.ValType.ref.inj e

/-- Memory `0` of an image context. -/
theorem mem0 (hR : Rel C D) {a : Silmaril.Wasm.AddrType} {l : Silmaril.Wasm.Limits}
    (h : D.mems[0]? = some ⟨a, l⟩) : ∃ mt, C.mems[0]? = some mt ∧ a = .i32 := by
  obtain ⟨mt, hmt, e⟩ := hR.mems_get h
  exact ⟨mt, hmt, (congrArg Silmaril.Wasm.MemoryType.address e).symm⟩

/-- A table of an image context. -/
theorem table_get (hR : Rel C D) {x : Nat} {a : Silmaril.Wasm.AddrType} {l : Silmaril.Wasm.Limits}
    {rt : Silmaril.Wasm.Validation.CRefType} (h : D.tables[x]? = some ⟨a, l, rt⟩) :
    ∃ tt, C.tables[x]? = some tt ∧ a = .i32 ∧ rt = tt.element.toC := by
  obtain ⟨tt, htt, e⟩ := hR.tables_get h
  exact ⟨tt, htt, (congrArg Silmaril.Wasm.Validation.CTableType.address e).symm,
    (congrArg Silmaril.Wasm.Validation.CTableType.element e).symm⟩

/-- Core's alignment premise contains 2.0's. -/
theorem memArg_of {arg : Silmaril.Wasm.V2.MemArg} {a : Silmaril.Wasm.AddrType} {N : Nat}
    (h : Silmaril.Wasm.Validation.MemArgOk arg.toCore a N) :
    Silmaril.Wasm.V2.Validation.MemArgOk arg N := h.1

/-! ## Variables -/

theorem r_localGet (hR : Rel C D) {x} (h : KOk D (.localGet x) it) :
    VSeq C [.localGet x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i t ht
  obtain ⟨t', ht', rfl⟩ := hR.locals_get ht
  simp only [erT, ers, List.map_cons, List.map_nil, er_toC]
  exact vone (.localGet ht')

theorem r_localSet (hR : Rel C D) {x} (h : KOk D (.localSet x) it) :
    VSeq C [.localSet x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i i t ht
  obtain ⟨t', ht', rfl⟩ := hR.locals_get ht
  simp only [erT, ers, List.map_cons, List.map_nil, er_toC]
  exact vone (.localSet ht')

theorem r_localTee (hR : Rel C D) {x} (h : KOk D (.localTee x) it) :
    VSeq C [.localTee x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i i t ht
  obtain ⟨t', ht', rfl⟩ := hR.locals_get ht
  simp only [erT, ers, List.map_cons, List.map_nil, er_toC]
  exact vone (.localTee ht')

theorem r_globalGet (hR : Rel C D) {x} (h : KOk D (.globalGet x) it) :
    VSeq C [.globalGet x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i m t ht
  obtain ⟨gt, hgt, e⟩ := hR.globals_get ht
  obtain rfl : t = gt.value.toC := (congrArg Silmaril.Wasm.Validation.CGlobalType.type e).symm
  simp only [erT, ers, List.map_cons, List.map_nil, er_toC]
  exact vone (.globalGet hgt)

theorem r_globalSet (hR : Rel C D) {x} (h : KOk D (.globalSet x) it) :
    VSeq C [.globalSet x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i t ht
  obtain ⟨gt, hgt, e⟩ := hR.globals_get ht
  obtain rfl : t = gt.value.toC := (congrArg Silmaril.Wasm.Validation.CGlobalType.type e).symm
  have hm : gt.mutability = .var := congrArg Silmaril.Wasm.Validation.CGlobalType.mutability e
  simp only [erT, ers, List.map_cons, List.map_nil, er_toC]
  exact vone (.globalSet hgt hm)

/-! ## Tables -/

theorem r_tableGet (hR : Rel C D) {x} (h : KOk D (.tableGet x) it) :
    VSeq C [.tableGet x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a l rt ht
  obtain ⟨tt, htt, rfl, rfl⟩ := table_get hR ht
  simp only [erT, ers, List.map_cons, List.map_nil, er_refToC]
  exact vone (.tableGet htt)

theorem r_tableSet (hR : Rel C D) {x} (h : KOk D (.tableSet x) it) :
    VSeq C [.tableSet x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a l rt ht
  obtain ⟨tt, htt, rfl, rfl⟩ := table_get hR ht
  simp only [erT, ers, List.map_cons, List.map_nil, er_refToC]
  exact vone (.tableSet htt)

theorem r_tableSize (hR : Rel C D) {x} (h : KOk D (.tableSize x) it) :
    VSeq C [.tableSize x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a l rt ht
  obtain ⟨tt, htt, rfl, rfl⟩ := table_get hR ht
  exact vone (.tableSize htt)

theorem r_tableGrow (hR : Rel C D) {x} (h : KOk D (.tableGrow x) it) :
    VSeq C [.tableGrow x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a l rt ht
  obtain ⟨tt, htt, rfl, rfl⟩ := table_get hR ht
  simp only [erT, ers, List.map_cons, List.map_nil, er_refToC]
  exact vone (.tableGrow htt)

theorem r_tableFill (hR : Rel C D) {x} (h : KOk D (.tableFill x) it) :
    VSeq C [.tableFill x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a l rt ht
  obtain ⟨tt, htt, rfl, rfl⟩ := table_get hR ht
  simp only [erT, ers, List.map_cons, List.map_nil, er_refToC]
  exact vone (.tableFill htt)

theorem r_tableCopy (hR : Rel C D) {x y} (h : KOk D (.tableCopy x y) it) :
    VSeq C [.tableCopy x y] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a₁ a₂ l₁ l₂ rt₁ rt₂ hs h₁ h₂
  obtain ⟨tt₁, htt₁, rfl, rfl⟩ := table_get hR h₁
  obtain ⟨tt₂, htt₂, rfl, rfl⟩ := table_get hR h₂
  exact vone (.tableCopy htt₁ htt₂ (refToC_sub hR hs).symm)

theorem r_tableInit (hR : Rel C D) {x y} (h : KOk D (.tableInit x y) it) :
    VSeq C [.tableInit x y] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a l rt₁ rt₂ hs ht he
  obtain ⟨tt, htt, rfl, rfl⟩ := table_get hR ht
  obtain ⟨rt, hrt, rfl⟩ := hR.elems_get he
  exact vone (.tableInit htt hrt (refToC_sub hR hs).symm)

theorem r_elemDrop (hR : Rel C D) {x} (h : KOk D (.elemDrop x) it) :
    VSeq C [.elemDrop x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i rt he
  obtain ⟨rt', hrt, -⟩ := hR.elems_get he
  exact vone (.elemDrop hrt)

/-! ## Memory -/

theorem r_memorySize (hR : Rel C D) (h : KOk D (.memorySize ⟨0⟩) it) :
    VSeq C [.memorySize] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.memorySize hmt)

theorem r_memoryGrow (hR : Rel C D) (h : KOk D (.memoryGrow ⟨0⟩) it) :
    VSeq C [.memoryGrow] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.memoryGrow hmt)

theorem r_memoryFill (hR : Rel C D) (h : KOk D (.memoryFill ⟨0⟩) it) :
    VSeq C [.memoryFill] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.memoryFill hmt)

theorem r_memoryCopy (hR : Rel C D) (h : KOk D (.memoryCopy ⟨0⟩ ⟨0⟩) it) :
    VSeq C [.memoryCopy] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a₁ a₂ l₁ l₂ h₁ h₂
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR h₁
  obtain ⟨-, -, rfl⟩ := mem0 hR h₂
  exact vone (.memoryCopy hmt)

theorem r_memoryInit (hR : Rel C D) {x} (h : KOk D (.memoryInit ⟨0⟩ x) it) :
    VSeq C [.memoryInit x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i a l hm hd
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR hm
  exact vone (.memoryInit hmt (hR.datas_get hd))

theorem r_dataDrop (hR : Rel C D) {x} (h : KOk D (.dataDrop x) it) :
    VSeq C [.dataDrop x] (erT D.toTypeCtx it) := by
  kinv h
  exact vone (.dataDrop (hR.datas_get ‹_›))

theorem r_intLoad (hR : Rel C D) {t p} {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.intLoad t p ⟨0⟩ arg.toCore) it) :
    VSeq C [.intLoad t p arg] (erT D.toTypeCtx it) := by
  kinv h
  · obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
    exact vone (.intLoadVal hmt (memArg_of ‹_›))
  · obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
    exact vone (.intLoadPack hmt ‹_› (memArg_of ‹_›))

theorem r_floatLoad (hR : Rel C D) {t} {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.floatLoad t ⟨0⟩ arg.toCore) it) :
    VSeq C [.floatLoad t arg] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.floatLoadVal hmt (memArg_of ‹_›))

theorem r_intStore (hR : Rel C D) {t p} {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.intStore t p ⟨0⟩ arg.toCore) it) :
    VSeq C [.intStore t p arg] (erT D.toTypeCtx it) := by
  kinv h
  · obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
    exact vone (.intStoreVal hmt (memArg_of ‹_›))
  · obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
    exact vone (.intStorePack hmt ‹_› (memArg_of ‹_›))

theorem r_floatStore (hR : Rel C D) {t} {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.floatStore t ⟨0⟩ arg.toCore) it) :
    VSeq C [.floatStore t arg] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.floatStoreVal hmt (memArg_of ‹_›))

/-- The packed-load alignment bound of 2.0 is the Core bound for a 64-bit access. -/
theorem pack_of {arg : Silmaril.Wasm.V2.MemArg} {M N : Nat} (h : M / 8 * N = 8)
    (ha : Silmaril.Wasm.V2.Validation.MemArgOk arg 64) :
    Silmaril.Wasm.V2.Validation.MemArgOkPack arg M N := by
  unfold Silmaril.Wasm.V2.Validation.MemArgOkPack
  rw [h]
  simpa [Silmaril.Wasm.V2.Validation.MemArgOk] using ha

/-- The 2.0 vector-load rule for each load shape. -/
theorem vload_of {op : Option Silmaril.Wasm.V2.VecLoadOp} {arg : Silmaril.Wasm.V2.MemArg}
    {mt : Silmaril.Wasm.V2.MemoryType} (hmt : C.mems[0]? = some mt)
    (ha : Silmaril.Wasm.V2.Validation.MemArgOk arg
      (Silmaril.Wasm.V2.VecLoadOp.toCoreOpt op).accessWidth) :
    Silmaril.Wasm.V2.Validation.InstrOk C (.vecLoad op arg) ⟨[.val .i32], [.val .v128]⟩ := by
  match op with
  | none => exact .vloadVal hmt ha
  | some (.shape8x8 _) => exact .vloadPack hmt rfl (pack_of (by decide) ha)
  | some (.shape16x4 _) => exact .vloadPack hmt rfl (pack_of (by decide) ha)
  | some (.shape32x2 _) => exact .vloadPack hmt rfl (pack_of (by decide) ha)
  | some (.splat _) => exact .vloadSplat hmt ha
  | some .zero32 => exact .vloadZero hmt rfl ha
  | some .zero64 => exact .vloadZero hmt rfl ha

theorem r_vecLoad (hR : Rel C D) {op} {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.vecLoad (Silmaril.Wasm.V2.VecLoadOp.toCoreOpt op) ⟨0⟩ arg.toCore) it) :
    VSeq C [.vecLoad op arg] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (vload_of hmt (memArg_of ‹_›))

theorem r_vecLoadLane (hR : Rel C D) {sz i} {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.vecLoadLane sz ⟨0⟩ arg.toCore i) it) :
    VSeq C [.vecLoadLane sz arg i] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.vloadLane hmt (memArg_of ‹_›) ‹_›)

theorem r_vecStore (hR : Rel C D) {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.vecStore ⟨0⟩ arg.toCore) it) :
    VSeq C [.vecStore arg] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.vstore hmt (memArg_of ‹_›))

theorem r_vecStoreLane (hR : Rel C D) {sz i} {arg : Silmaril.Wasm.V2.MemArg}
    (h : KOk D (.vecStoreLane sz ⟨0⟩ arg.toCore i) it) :
    VSeq C [.vecStoreLane sz arg i] (erT D.toTypeCtx it) := by
  kinv h
  obtain ⟨mt, hmt, rfl⟩ := mem0 hR ‹_›
  exact vone (.vstoreLane hmt (memArg_of ‹_›) ‹_›)

/-! ## References -/

theorem r_refNull {rt : Silmaril.Wasm.V2.RefType} (h : KOk D (.refNull rt.toCoreHeap) it) :
    VSeq C [.refNull rt] (erT D.toTypeCtx it) := by
  kinv h
  cases rt <;> exact vone .refNull

theorem r_refFunc (hR : Rel C D) {x} (h : KOk D (.refFunc x) it) :
    VSeq C [.refFunc x] (erT D.toTypeCtx it) := by
  kinv h
  rename_i d hd hr
  obtain ⟨ft, hft, rfl⟩ := hR.funcs_get hd
  simp only [erT, ers, List.map_cons, List.map_nil, Silmaril.Wasm.Validation.Ty.refT, er_defHeap]
  exact vone (.refFunc hft (hR.refs_mem hr))

theorem r_refIsNull (h : KOk D .refIsNull it) : VSeq C [.refIsNull] (erT D.toTypeCtx it) := by
  kinv h
  rename_i ht _
  show VSeq C _ ⟨[er _ (.refv (.ref true ht))], [.val .i32]⟩
  rw [er_refv]
  cases erHeap D.toTypeCtx ht with
  | some r => exact vone (.refIsNull (rt := r))
  | none =>
    exact .sub (vone (.refIsNull (rt := .funcref)))
      ⟨.cons (.bot _) .nil, Silmaril.Wasm.V2.Validation.CResultType.sub_refl _⟩

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
