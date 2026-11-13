module

public import Silmaril.Proofs.Wasm.Logic.HoareExamples.Loop

/-!
# Example: a GC linked list

`listProg_hwp`: for a struct type `x` with two value fields (`{t₀, t₁}`, e.g.
`{i32, ref null x}`), every run of `listProg` builds the list `2 → 1 → null` on the
GC heap (two `struct.new`, the first node kept in local `0`) and reads `1`
through the first node (`struct.get x 1`, then `struct.get x 0`). The heap
addresses are the store's: the two nodes are allocated at `s.structs.length` and
`s.structs.length + 1`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.HoareExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem newFields_val {fs : Ty (.list .field)} {ft₀ ft₁ : CFieldType} {t₀ t₁ : Ty .val}
    (hfs : fs.toList = [ft₀, ft₁]) (h₀ : fieldStorage ft₀ = .val t₀)
    (h₁ : fieldStorage ft₁ = .val t₁) (v₀ v₁ : Val) :
    newFields fs [v₀, v₁] = [.val v₀, .val v₁] := by
  simp [newFields, hfs, h₀, h₁, packField]

theorem packable_val {fs : Ty (.list .field)} {ft₀ ft₁ : CFieldType} {t₀ t₁ : Ty .val}
    (hfs : fs.toList = [ft₀, ft₁]) (h₀ : fieldStorage ft₀ = .val t₀)
    (h₁ : fieldStorage ft₁ = .val t₁) (v₀ v₁ : Val) :
    ∀ p ∈ fs.toList.zip [v₀, v₁], packable (fieldStorage p.1) p.2 := by
  simp [hfs, h₀, h₁, packable]

/-- The heap after the first allocation. -/
def heap₁ (s : Store H) (d : DefType) : Store H :=
  s.addStruct ⟨d, [.val (.i32 1), .val (.ref .null)]⟩

/-- The heap after the second allocation. -/
def heap₂ (s : Store H) (d : DefType) : Store H :=
  (heap₁ s d).addStruct ⟨d, [.val (.i32 2), .val (.ref (.struct s.structs.length))]⟩

theorem heap₂_first (s : Store H) (d : DefType) :
    (heap₂ s d).structs[s.structs.length]? = some ⟨d, [.val (.i32 1), .val (.ref .null)]⟩ := by
  simp [heap₂, heap₁, Store.addStruct]

theorem heap₂_second (s : Store H) (d : DefType) :
    (heap₂ s d).structs[(heap₁ s d).structs.length]? =
      some ⟨d, [.val (.i32 2), .val (.ref (.struct s.structs.length))]⟩ := by
  simp [heap₂, Store.addStruct]

/-- The reads at the end: the second field of the second node, then the first
field of the first node. -/
theorem list_reads {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
    {ft₀ ft₁ : CFieldType} {t₀ t₁ : Ty .val} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hfs : fs.toList = [ft₀, ft₁]) (h₀ : fieldStorage ft₀ = .val t₀)
    (h₁ : fieldStorage ft₁ = .val t₁) :
    HWP P host (heap₂ s d) f (vals ([] ++ [.ref (.struct (heap₁ s d).structs.length)]) ++
      .plain (.structGet none x i1) :: [.plain (.structGet none x i0)])
      (fun _ _ o => o = .normal [.i32 1]) := by
  have hlast : HWP P host (heap₂ s d) f (vals ([] ++ [Val.i32 1]) ++ [])
      (fun _ _ o => o = .normal [.i32 1]) := by
    simpa using HWP.of_vals (P := P) (host := host) (s := heap₂ s d) (f := f) (vs := [Val.i32 1])
      (Q := fun _ _ o => o = .normal [.i32 1]) rfl
  have hget₀ : HWP P host (heap₂ s d) f (vals ([] ++ [.ref (.struct s.structs.length)]) ++
      .plain (.structGet none x i0) :: []) (fun _ _ o => o = .normal [.i32 1]) :=
    HWP.structGet (ft := ft₀) (heap₂_first s d) rfl hd he (by simp [hfs, i0, Idx.toNat])
      (by simp [h₀, unpackable]) hlast
  exact HWP.structGet (ft := ft₁) (heap₂_second s d) rfl hd he (by simp [hfs, i1, Idx.toNat])
    (by simp [h₁, unpackable]) hget₀

/-- **The linked list.** -/
theorem listProg_hwp {s : Store H} {f : Frame} {ht : HeapType} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {ft₀ ft₁ : CFieldType} {t₀ t₁ : Ty .val}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hfs : fs.toList = [ft₀, ft₁])
    (h₀ : fieldStorage ft₀ = .val t₀) (h₁ : fieldStorage ft₁ = .val t₁)
    (hloc : x0.toNat < f.locals.length) :
    HWP P host s f (expression (listProg ht x)) (fun _ _ o => o = .normal [.i32 1]) := by
  have hn : ([Val.i32 2, .ref (.struct s.structs.length)]).length = fs.length := by
    simp [Ty.length, hfs]
  have hn' : ([Val.i32 1, .ref .null]).length = fs.length := by simp [Ty.length, hfs]
  let f₁ := f.setLocal x0 (.ref (.struct s.structs.length))
  have hd₁ : f₁.type? x = some d := hd
  have hloc₁ : f₁.local? x0 = some (some (.ref (.struct s.structs.length))) := by
    simp [f₁, Frame.setLocal, Frame.local?, hloc]
  have hnew₂ : HWP P host (heap₁ s d) f₁ (vals ([] ++ [Val.i32 2, .ref (.struct s.structs.length)]) ++
      .plain (.structNew x) :: [.plain (.structGet none x i1), .plain (.structGet none x i0)])
      (fun _ _ o => o = .normal [.i32 1]) :=
    HWP.structNew hd₁ he hn (packable_val hfs h₀ h₁ _ _)
      (by rw [newFields_val hfs h₀ h₁]; exact list_reads hd₁ he hfs h₀ h₁)
  have hget : HWP P host (heap₁ s d) f₁ (vals [Val.i32 2] ++ .plain (.localGet x0) ::
      [.plain (.structNew x), .plain (.structGet none x i1), .plain (.structGet none x i0)]) _ :=
    HWP.localGet hloc₁ hnew₂
  have hset : HWP P host (heap₁ s d) f (vals ([] ++ [.ref (.struct s.structs.length)]) ++
      .plain (.localSet x0) :: [.plain (.intConst .i32 2), .plain (.localGet x0),
        .plain (.structNew x), .plain (.structGet none x i1), .plain (.structGet none x i0)]) _ :=
    HWP.localSet hloc hget
  have hnew₁ : HWP P host s f (vals ([] ++ [Val.i32 1, .ref .null]) ++ .plain (.structNew x) ::
      [.plain (.localSet x0), .plain (.intConst .i32 2), .plain (.localGet x0),
        .plain (.structNew x), .plain (.structGet none x i1), .plain (.structGet none x i0)]) _ :=
    HWP.structNew hd he hn' (packable_val hfs h₀ h₁ _ _)
      (by rw [newFields_val hfs h₀ h₁]; exact hset)
  exact HWP.refNull (us := [.i32 1]) hnew₁

end Silmaril.Wasm.Logic.HoareExamples
