module

public import Silmaril.Games.Abstract.Cells.Defs
public import Silmaril.Games.Abstract.Hiding.Thms
public import Silmaril.Games.Abstract.Game.Thms

/-!
# Exported state: proofs

Hiding the cells of the embedded function-only model gives the model back,
and two models that differ only in what reads of an exported cell return have
the same function-only observation.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Cells

open Silmaril.Games.Abstract Silmaril.Games.Abstract.TraceModel

universe u

variable {G : Game.{u}} {N : Type u} {V : N → Type u}

theorem hide_map_ops (T : TraceModel G) :
    hide Game.PHom.hideCells (map (Game.Hom.ops (N := N) (V := V)) T) = T := by
  apply le_antisymm
  · refine generate_le_iff.2 ?_
    rintro _ ⟨q, ⟨hq, u, hu, p₀, w, rfl, hp₀, hw⟩, rfl⟩ hl
    rw [List.filterMap_append]
    rw [List.filterMap_append] at hl
    have h₀ : p₀.filterMap CMove.opOf ∈ T := by
      rcases hu with rfl | ⟨⟨s, hs, rfl⟩, -⟩
      · rw [List.prefix_nil.1 hp₀]; exact T.closed.nil_mem
      · have := hp₀.filterMap CMove.opOf
        rw [show List.map (Game.Hom.ops (N := N) (V := V)).map s = List.map CMove.op s from rfl,
          Game.filterMap_opOf_map_op] at this
        exact T.closed.of_prefix hs this
    refine append_mem_of_isO h₀ (fun o ho => ?_) hl
    obtain ⟨x, hx, hxo⟩ := List.mem_filterMap.1 ho
    have := hw x hx
    cases x <;> cases hxo
    exact this
  · intro s hs
    have h := filterMap_mem_hide (f := Game.PHom.hideCells)
      (subset_generate (S := (List.map (Game.Hom.ops (N := N) (V := V)).map) '' (T : Set _))
        ⟨s, hs, rfl⟩ ((Game.Hom.ops (N := N) (V := V)).legal (T.closed.legal hs)))
    rwa [show (s.map (Game.Hom.ops (N := N) (V := V)).map).filterMap
      (Game.PHom.hideCells (G := G) (N := N) (V := V)).map = s from
        Game.filterMap_opOf_map_op s] at h

/-! ## Reads distinguish what calls cannot -/

/-- No function moves. -/
abbrev G₀ : Game.{0} := Game.free PEmpty fun _ => False

/-- One boolean cell. -/
abbrev Gc : Game.{0} := G₀.withCells Unit fun _ => Bool

/-- The component whose cell always reads as `b`. -/
def readsAs (b : Bool) : TraceModel Gc where
  plays := {p | p ∈ Gc.Legal ∧ ∀ v, CMove.got () v ∈ p → v = b}
  closed := {
    nil_mem := ⟨Gc.nil_legal, by simp⟩
    legal := fun h => h.1
    of_prefix := fun ⟨ht, h⟩ hst => ⟨Gc.legal_of_prefix ht hst, fun v hv => h v (hst.subset hv)⟩
    receptive := fun {s o} ⟨_, h⟩ hl ho => ⟨hl, fun v hv => by
      rcases List.mem_append.1 hv with hv | hv
      · exact h v hv
      · rw [← List.mem_singleton.1 hv] at ho; exact ho.elim⟩ }

theorem filterMap_opOf_eq_nil (p : List Gc.Move) : p.filterMap CMove.opOf = [] := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    cases x with
    | op m => exact m.elim
    | _ => simp [CMove.opOf]

theorem image_readsAs (b : Bool) :
    (List.filterMap Game.PHom.hideCells.map) '' (SetLike.coe (readsAs b)) = {[]} := by
  ext q
  constructor
  · rintro ⟨p, -, rfl⟩
    exact filterMap_opOf_eq_nil p
  · rintro rfl
    exact ⟨[], (readsAs b).closed.nil_mem, rfl⟩

theorem hide_readsAs_eq :
    hide Game.PHom.hideCells (readsAs true) = hide Game.PHom.hideCells (readsAs false) := by
  unfold hide
  rw [image_readsAs, image_readsAs]

theorem readsAs_ne : readsAs true ≠ readsAs false := by
  intro h
  have hm : [CMove.get (), CMove.got () true] ∈ readsAs true := by
    refine ⟨⟨trivial, rfl, trivial⟩, fun v hv => ?_⟩
    simp only [List.mem_cons, reduceCtorEq, CMove.got.injEq, true_and, List.not_mem_nil,
      or_false, false_or] at hv
    exact eq_of_heq hv
  rw [h] at hm
  exact absurd (hm.2 true (by simp)) (by decide)

end Silmaril.Proofs.Games.Abstract.Cells
