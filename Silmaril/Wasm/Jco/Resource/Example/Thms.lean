module

public import Silmaril.Wasm.Jco.Resource.Example.Defs
public import Silmaril.Wasm.Jco.Resource.Merge.Thms

/-!
# A litmus world with a resource: the hypotheses hold

For the litmus instance `exRInst` and world `exMdR` (`own` parameters, `borrow` parameters and an
`own` result), every hypothesis of `wrapR_correct` and `merged_sim` holds from the empty canonical
table: `Meta.Conforms`, `AllocTotal`, `MergeOk`, the table invariant and room. So the theorems
apply unconditionally to this world (`exR_wrapR`, `exR_merged`, `exR_merged_eq`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res.Example

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Component (Flat ValTy Val)
open Silmaril.Wasm.Component.Runtime (Table)

theorem exR_conforms : exMdR.erase.Conforms exRInst where
  alloc xs := by
    intro m r m' h
    have h' : Out.ok r m' = rAllocOut xs m := h
    unfold rAllocOut at h'
    split at h'
    · exact ⟨_, (Out.ok.inj h').1⟩
    · cases h'
  outPtr s hs hm := by
    have hf : ∀ s ∈ exMdR.erase.world, inMem s.result = false := by decide
    rw [hf s hs] at hm
    cases hm

theorem exR_allocTotal : exMdR.AllocTotal exRInst := fun _ _ => ⟨_, rfl⟩

/-- Every resource type of a type list is below `2^32`. -/
def smallRts (ts : List RTy) : Bool :=
  ts.all fun
    | .own r | .borrow r => decide (r < 2 ^ 32)
    | .base _ => true

theorem rts_of_small {ts : List RTy} (h : smallRts ts = true) {t : RTy} (ht : t ∈ ts) {r : RtId}
    (hr : t = .own r ∨ t = .borrow r) : r < 2 ^ 32 := by
  have ht' := List.all_eq_true.1 h t ht
  rcases hr with rfl | rfl <;> simpa using ht'

theorem exR_mergeOk : exMdR.MergeOk where
  alloc := by decide
  names := by decide
  rts s hs t ht r hr := by
    have hsmall : ∀ s ∈ exMdR.world, smallRts (s.result.toList ++ s.params) = true := by decide
    exact rts_of_small (hsmall s hs) ht hr

theorem empty_inv : refTab.Inv (Silmaril.Wasm.Component.Runtime.Table.empty : Silmaril.Wasm.Component.Runtime.Table HEntry) :=
  ⟨Silmaril.Wasm.Resource.freeOK_empty, by
    show (#[none] : Array (Option HEntry)).size ≤ Silmaril.Wasm.Component.Runtime.Table.maxLength + 1; simp⟩

theorem exR_room (name : String) : exMdR.Room refTab Silmaril.Wasm.Component.Runtime.Table.empty name := by
  intro s hs c hc
  have hle : ∀ s ∈ exMdR.world, ownCount s.params + ownRes s.result ≤ 1 := by decide
  have hc' : c = 2 ^ 28 - 1 := by
    have h1 : refTab.cap Silmaril.Wasm.Component.Runtime.Table.empty = some (2 ^ 28 - 1) := rfl
    rw [h1] at hc
    exact (Option.some.inj hc).symm
  have := hle s (List.mem_of_find?_eq_some hs)
  omega

/-- `wrapR_correct` for the litmus world, from the empty canonical table. -/
theorem exR_wrapR (name : String) (vs : List RVal) :
    Sim ((wrapR exMdR).callExport exRInst refTab name vs) (exMdR.spec exRInst name vs)
      Silmaril.Wasm.Component.Runtime.Table.empty fun a b t' => a = b ∧ refTab.Same Silmaril.Wasm.Component.Runtime.Table.empty t' :=
  wrapR_correct_ref exRInst exMdR exR_conforms name vs empty_inv (exR_room name)

/-- `merged_eq_specHost` for the litmus world. -/
theorem exR_merged_eq (H : HTab) (name : String) (vs : List RVal) :
    exMdR.hostView ((merged exMdR).callExport (link exRInst (mgr H))) name vs =
      specHost H exRInst exMdR name vs :=
  merged_eq_specHost exRInst H exMdR exR_conforms exR_allocTotal exR_mergeOk name vs

/-- `merged_sim` for the litmus world, from the empty canonical table. -/
theorem exR_merged (name : String) (vs : List RVal) :
    Sim (canonHost refTab exRInst exMdR name vs)
      (exMdR.hostView ((merged exMdR).callExport (link exRInst (mgr refTab))) name vs)
      Silmaril.Wasm.Component.Runtime.Table.empty fun a b t' => a = b ∧ refTab.Same Silmaril.Wasm.Component.Runtime.Table.empty t' :=
  merged_sim exRInst refTab refTab_lawful exMdR exR_conforms exR_allocTotal exR_mergeOk name vs
    empty_inv (exR_room name)

end Silmaril.Wasm.Jco.Res.Example
