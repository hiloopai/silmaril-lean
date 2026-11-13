module

public import Silmaril.Wasm.Logic.Iris.Heap.Defs

/-!
# The Wasm 3.0 ghost heap: reading, updating and allocating cells

* `interp_lookup`/`interp_lookup_cells`: a points-to reads the store;
* `interp_change`: the general update of the state interpretation along a change
  of store and frame, updating the owned cells `ps` to `ps'` and allocating the
  fresh cells `qs`; every instruction rule of `Silmaril.Wasm.Logic.Iris.Rules.Thms`
  uses it.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open _root_.Iris _root_.Iris.BI _root_.Iris.Std

variable {H : Type} {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-! ## Updating a ghost heap at a list of locations -/

/-- Insert the cells `ps`, left to right. -/
def updMap (σ : HeapF ICell) : List (ILoc × ICell) → HeapF ICell
  | [] => σ
  | p :: ps => updMap (insert σ p.1 p.2) ps

theorem lookup_cons_eq (l : ILoc) (c : ICell) (ps : List (ILoc × ICell)) :
    ((l, c) :: ps).lookup l = some c := by
  simp [List.lookup]

theorem lookup_cons_ne {l k : ILoc} (c : ICell) (ps : List (ILoc × ICell)) (h : l ≠ k) :
    ((k, c) :: ps).lookup l = ps.lookup l := by
  have hb : (l == k) = false := beq_eq_false_iff_ne.mpr h
  simp [List.lookup, hb]

theorem lookup_eq_none {l : ILoc} : ∀ {ps : List (ILoc × ICell)}, l ∉ ps.map Prod.fst →
    ps.lookup l = none
  | [], _ => rfl
  | (k, c) :: ps, h => by
    have hk : l ≠ k := fun he => h (by simp [he])
    have hr : l ∉ ps.map Prod.fst := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [lookup_cons_ne c ps hk, lookup_eq_none hr]

theorem get?_updMap : ∀ {σ : HeapF ICell} {ps : List (ILoc × ICell)},
    (ps.map Prod.fst).Nodup → ∀ l, get? (updMap σ ps) l = (ps.lookup l).or (get? σ l)
  | _, [], _, _ => rfl
  | σ, (k, c) :: ps, hnd, l => by
    have hk : k ∉ ps.map Prod.fst := (List.nodup_cons.mp hnd).1
    have ih : get? (updMap (insert σ k c) ps) l = (ps.lookup l).or (get? (insert σ k c) l) :=
      get?_updMap (List.nodup_cons.mp hnd).2 l
    show get? (updMap (insert σ k c) ps) l = _
    rw [ih]
    by_cases h : l = k
    · subst h
      rw [lookup_eq_none hk, lookup_cons_eq, get?_insert_eq rfl]
      rfl
    · rw [lookup_cons_ne c ps h, get?_insert_ne (Ne.symm h)]

theorem lookup_mem {l : ILoc} {c : ICell} : ∀ {ps : List (ILoc × ICell)}, ps.lookup l = some c →
    (l, c) ∈ ps
  | [], h => by cases h
  | (k, d) :: ps, h => by
    by_cases hk : l = k
    · subst hk
      rw [lookup_cons_eq] at h
      cases h
      exact List.mem_cons_self ..
    · rw [lookup_cons_ne d ps hk] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_isSome {l : ILoc} : ∀ {ps : List (ILoc × ICell)}, l ∈ ps.map Prod.fst →
    ∃ c, ps.lookup l = some c
  | [], h => by cases h
  | (k, d) :: ps, h => by
    by_cases hk : l = k
    · subst hk
      exact ⟨d, lookup_cons_eq ..⟩
    · have h' : l ∈ ps.map Prod.fst := by simpa [hk] using h
      obtain ⟨c, hc⟩ := lookup_isSome h'
      exact ⟨c, by rw [lookup_cons_ne d ps hk, hc]⟩

/-- Where a ghost heap updated with `ps'` and then `qs` comes from. -/
theorem get?_updMap₂_cases {m : HeapF ICell} {ps' qs : List (ILoc × ICell)}
    (hnd : (ps'.map Prod.fst ++ qs.map Prod.fst).Nodup) {l : ILoc} {c : ICell}
    (hl : get? (updMap (updMap m ps') qs) l = some c) :
    (l, c) ∈ ps' ++ qs ∨ (l ∉ ps'.map Prod.fst ∧ get? m l = some c) := by
  have hnd₁ : (ps'.map Prod.fst).Nodup := (List.nodup_append.mp hnd).1
  have hnd₂ : (qs.map Prod.fst).Nodup := (List.nodup_append.mp hnd).2.1
  have hl' : (qs.lookup l).or ((ps'.lookup l).or (get? m l)) = some c := by
    rw [← get?_updMap hnd₁, ← get?_updMap hnd₂]; exact hl
  rcases hq : qs.lookup l with _ | c'
  · rcases hp : ps'.lookup l with _ | c''
    · have hm : get? m l = some c := by simpa [hq, hp] using hl'
      refine .inr ⟨fun hmem => ?_, hm⟩
      obtain ⟨d, hd⟩ := lookup_isSome hmem
      rw [hp] at hd
      cases hd
    · have hc : c'' = c := by simpa [hq, hp] using hl'
      exact .inl (List.mem_append_left _ (hc ▸ lookup_mem hp))
  · have hc : c' = c := by simpa [hq] using hl'
    exact .inl (List.mem_append_right _ (hc ▸ lookup_mem hq))

/-! ## Points-to assertions read the store -/

theorem genHeap_update_cells : ∀ {σ : HeapF ICell} {ps ps' : List (ILoc × ICell)},
    ps.map Prod.fst = ps'.map Prod.fst →
    genHeapInterp (GF := GF) σ ∗ ownCells ps ==∗ genHeapInterp (updMap σ ps') ∗ ownCells ps'
  | σ, [], [], _ => by
    simp only [ownCells, updMap]
    iintro ⟨H, -⟩
    imodintro
    iframe H
  | _, [], _ :: _, h => by cases h
  | _, _ :: _, [], h => by cases h
  | σ, (l, c) :: ps, (l', c') :: ps', h => by
    have hl : l = l' := (List.cons.inj h).1
    have hs : ps.map Prod.fst = ps'.map Prod.fst := (List.cons.inj h).2
    subst hl
    simp only [ownCells, updMap]
    iintro ⟨H, Hl, Hs⟩
    imod genHeap_update (v₂ := c') $$ [$H $Hl] with ⟨H, Hl⟩
    imod genHeap_update_cells (σ := insert σ l c') hs $$ [$H $Hs] with ⟨H, Hs⟩
    imodintro
    iframe

theorem genHeap_alloc_cells : ∀ {σ : HeapF ICell} {qs : List (ILoc × ICell)},
    (qs.map Prod.fst).Nodup → (∀ q ∈ qs, get? σ q.1 = none) →
    genHeapInterp (GF := GF) σ ==∗ genHeapInterp (updMap σ qs) ∗ ownCells qs
  | σ, [], _, _ => by
    simp only [ownCells, updMap]
    iintro H
    imodintro
    iframe H
  | σ, (l, c) :: qs, hnd, hf => by
    have hl : get? σ l = none := hf (l, c) (List.mem_cons_self ..)
    have hk : l ∉ qs.map Prod.fst := (List.nodup_cons.mp hnd).1
    have hf' : ∀ q ∈ qs, get? (insert σ l c) q.1 = none := fun q hq => by
      have hne : l ≠ q.1 := fun he => hk (he ▸ List.mem_map_of_mem hq)
      rw [get?_insert_ne hne]
      exact hf q (List.mem_cons_of_mem _ hq)
    simp only [ownCells, updMap]
    iintro H
    imod genHeap_alloc hl $$ H with ⟨H, Hl, -⟩
    imod genHeap_alloc_cells (List.nodup_cons.mp hnd).2 hf' $$ H with ⟨H, Hs⟩
    imodintro
    iframe

/-- A points-to reads the store. -/
theorem interp_lookup {σ : IState H} {l : ILoc} {dq : DFrac} {c : ICell} :
    wasmInterp (GF := GF) σ ∗ pointsTo l dq c ==∗ ⌜cellOf σ.1 σ.2 l = some c⌝ := by
  unfold wasmInterp
  iintro ⟨⟨%m, %hm, H⟩, Hl⟩
  icases genHeap_valid $$ [$H $Hl] with >%hl
  ipureintro
  exact hm l c hl

/-- Owned cells read the store. -/
theorem interp_lookup_cells {σ : IState H} : ∀ {ps : List (ILoc × ICell)},
    wasmInterp (GF := GF) σ ∗ ownCells ps ==∗ ⌜∀ p ∈ ps, cellOf σ.1 σ.2 p.1 = some p.2⌝
  | [] => by
    iintro -
    imodintro
    ipureintro
    simp
  | (l, c) :: ps => by
    simp only [ownCells]
    iintro ⟨Hσ, Hl, Hs⟩
    ihave %h₁ : ⌜cellOf σ.1 σ.2 l = some c⌝ $$ [Hσ Hl]
    · icases interp_lookup $$ [$Hσ $Hl] with >%h
      itrivial
    ihave %h₂ : ⌜∀ p ∈ ps, cellOf σ.1 σ.2 p.1 = some p.2⌝ $$ [Hσ Hs]
    · icases interp_lookup_cells $$ [$Hσ $Hs] with >%h
      ipureintro
      exact h
    imodintro
    ipureintro
    exact List.forall_mem_cons.mpr ⟨h₁, h₂⟩

/-! ## Changing the store -/

/-- **The update of the state interpretation.** Along a change of the store and
the frame that keeps every cell outside the owned locations `ps`, gives the
owned locations the cells `ps'` and creates the fresh cells `qs`, the owned
cells `ps` become `ps'` and the cells `qs` are allocated. -/
theorem interp_change {s s' : Store H} {f f' : Frame} {ps ps' qs : List (ILoc × ICell)}
    (hfst : ps.map Prod.fst = ps'.map Prod.fst)
    (hnd : (ps'.map Prod.fst ++ qs.map Prod.fst).Nodup)
    (hfresh : ∀ q ∈ qs, cellOf s f q.1 = none)
    (hnew : ∀ p ∈ ps' ++ qs, cellOf s' f' p.1 = some p.2)
    (hold : ∀ l c, l ∉ ps.map Prod.fst → cellOf s f l = some c → cellOf s' f' l = some c) :
    wasmInterp (GF := GF) (s, f) ∗ ownCells ps ==∗
      wasmInterp (s', f') ∗ ownCells ps' ∗ ownCells qs := by
  have hnd₁ : (ps'.map Prod.fst).Nodup := (List.nodup_append.mp hnd).1
  have hnd₂ : (qs.map Prod.fst).Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj : ∀ q ∈ qs, q.1 ∉ ps'.map Prod.fst := fun q hq hm =>
    (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_map_of_mem hq) rfl
  unfold wasmInterp
  iintro ⟨⟨%m, %hm, H⟩, Hs⟩
  imod genHeap_update_cells hfst $$ [$H $Hs] with ⟨H, Hs⟩
  have hfr : ∀ q ∈ qs, get? (updMap m ps') q.1 = none := fun q hq => by
    rw [get?_updMap hnd₁, lookup_eq_none (hdisj q hq), Option.none_or]
    cases hg : get? m q.1 with
    | none => rfl
    | some c => exact absurd (hm _ _ hg) (by rw [hfresh q hq]; simp)
  imod genHeap_alloc_cells hnd₂ hfr $$ H with ⟨H, Hq⟩
  imodintro
  iframe
  ipureintro
  intro l c hl
  rcases get?_updMap₂_cases hnd hl with hmem | ⟨hn, hg⟩
  · exact hnew _ hmem
  · exact hold l c (hfst ▸ hn) (hm l c hg)

end Silmaril.Wasm.Logic.IrisWasm
