module

public import Silmaril.Compiler.Mir.Semantics.Defs
@[expose] public section

/-! # The semantic view of interpreter frames -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

namespace Frame

/-- Registers and slots, viewed as the partial maps used by Lir. -/
def toLir (fr : Frame) : Lir.Frame Nat :=
  ⟨fun r => (fr.get r).map UInt64.toBitVec,
   fun n => (fr.getSlot n).map UInt64.toBitVec⟩

/-- The register values and written flags have the same extent. -/
def WellFormed (fr : Frame) : Prop := fr.vals.size = fr.defd.size

@[simp] theorem empty_wellFormed (n : Nat) : (empty n).WellFormed := by
  simp [WellFormed, empty, ByteArray.size]

@[simp] theorem empty_toLir (n : Nat) : (empty n).toLir = .empty := by
  change Lir.Frame.mk _ _ = Lir.Frame.mk _ _
  refine congrArg₂ Lir.Frame.mk ?_ ?_
  · funext r
    change ((empty n).get r).map UInt64.toBitVec = none
    by_cases hr : r < n
    · simp only [get, empty, ByteArray.size, Array.size_replicate, hr, decide_true,
        Bool.true_and]
      rw [getElem!_pos (ByteArray.mk (Array.replicate n 0)) r
        (by simpa only [ByteArray.size, Array.size_replicate] using hr)]
      simp only [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]
      rfl
    · simp only [get, empty, ByteArray.size, Array.size_replicate, hr, decide_false,
        Bool.false_and, Bool.false_eq_true, ite_false, Option.map_none]
  · funext r
    simp [getSlot, empty]

@[simp] theorem set_wellFormed (fr : Frame) (h : fr.WellFormed) (r : Nat) (v : UInt64) :
    (fr.set r v).WellFormed := by
  rcases fr with ⟨vals, ⟨defd⟩, slots⟩
  simp only [WellFormed, ByteArray.size] at h ⊢
  simp only [set]
  split <;> simp_all [ByteArray.size, ByteArray.set!, ByteArray.data_append]

private theorem byte_mk_get (xs : Array UInt8) (i : Nat) :
    (ByteArray.mk xs)[i]! = xs[i]! := by
  by_cases h : i < xs.size
  · rw [getElem!_pos (ByteArray.mk xs) i h, getElem!_pos xs i h]; rfl
  · rw [getElem!_neg (ByteArray.mk xs) i h, getElem!_neg xs i h]

private theorem append_zero_get (xs : Array UInt8) (n i : Nat) :
    (xs ++ Array.replicate n 0)[i]! = xs[i]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append,
    Array.getElem?_replicate]
  split
  · rfl
  · next h =>
    rw [getElem?_neg xs i h]
    split <;> rfl

private theorem get_grow (fr : Frame) (h : fr.WellFormed) (n s : Nat) :
    (Frame.mk (fr.vals ++ Array.replicate (n - fr.vals.size) 0)
      (fr.defd ++ ByteArray.mk (Array.replicate (n - fr.defd.size) 0)) fr.slots).get s =
      fr.get s := by
  rcases fr with ⟨vals, ⟨defd⟩, slots⟩
  change vals.size = defd.size at h
  have ha : ByteArray.mk defd ++ ByteArray.mk (Array.replicate (n - defd.size) 0) =
      ByteArray.mk (defd ++ Array.replicate (n - defd.size) 0) := by
    apply ByteArray.ext
    exact ByteArray.data_append
  simp only [ByteArray.size, ha]
  change (if s < (defd ++ Array.replicate (n - defd.size) 0).size &&
      (ByteArray.mk (defd ++ Array.replicate (n - defd.size) 0))[s]! != 0 then
      some (vals ++ Array.replicate (n - vals.size) 0)[s]! else none) =
    (if s < defd.size && (ByteArray.mk defd)[s]! != 0 then some vals[s]! else none)
  rw [byte_mk_get, byte_mk_get, append_zero_get]
  simp only [Array.size_append, Array.size_replicate]
  by_cases hs : s < defd.size
  · have hs' : s < defd.size + (n - defd.size) := by omega
    simp only [hs, hs', decide_true, Bool.true_and]
    split
    · rw [getElem!_pos (vals ++ Array.replicate (n - vals.size) 0) s
          (by simp only [Array.size_append, Array.size_replicate]; omega),
        Array.getElem_append_left (by omega), ← getElem!_pos vals s (by omega)]
    · rfl
  · rw [getElem!_neg defd s hs]
    simp only [show (default : UInt8) = 0 from rfl, bne_self_eq_false, Bool.and_false,
      Bool.false_eq_true, ite_false]

private theorem get_setWithin (fr : Frame) (r s : Nat) (v : UInt64)
    (hr : r < fr.vals.size) (hd : r < fr.defd.size) :
    (Frame.mk (fr.vals.set! r v) (fr.defd.set! r 1) fr.slots).get s =
      if s = r then some v else fr.get s := by
  simp only [get, ByteArray.size_set!]
  by_cases hs : s = r
  · subst s
    rw [ByteArray.getElem!_set!_self _ _ _ hd, Array.getElem!_set!_self _ _ _ hr]
    simp [hd]
  · rw [ByteArray.getElem!_set!_ne _ _ _ _ (Ne.symm hs),
      Array.getElem!_set!_ne _ _ _ _ (Ne.symm hs)]
    simp only [hs, ite_false]

@[simp] theorem get_set (fr : Frame) (h : fr.WellFormed) (r s : Nat) (v : UInt64) :
    (fr.set r v).get s = if s = r then some v else fr.get s := by
  rcases fr with ⟨vals, defd, slots⟩
  simp only [set]
  split
  · next hr =>
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hr
    exact get_setWithin ⟨vals, defd, slots⟩ r s v hr.1 hr.2
  · let grown := Frame.mk (vals ++ Array.replicate (r + 1 - vals.size) 0)
        (defd ++ ByteArray.mk (Array.replicate (r + 1 - defd.size) 0)) slots
    have hv : r < grown.vals.size := by
      simp only [grown, Array.size_append, Array.size_replicate]; omega
    have hd : r < grown.defd.size := by
      simp only [grown, ByteArray.size, ByteArray.data_append, Array.size_append, Array.size_replicate]; omega
    change (Frame.mk (grown.vals.set! r v) (grown.defd.set! r 1) slots).get s = _
    rw [get_setWithin grown r s v hv hd, get_grow ⟨vals, defd, slots⟩ h]

@[simp] theorem getSlot_set (fr : Frame) (r n : Nat) (v : UInt64) :
    (fr.set r v).getSlot n = fr.getSlot n := by
  rcases fr with ⟨vals, defd, slots⟩
  simp only [set]
  split <;> rfl

@[simp] theorem set_toLir (fr : Frame) (h : fr.WellFormed) (r : Nat) (v : UInt64) :
    (fr.set r v).toLir = fr.toLir.set r v.toBitVec := by
  change Lir.Frame.mk _ _ = Lir.Frame.mk _ _
  refine congrArg₂ Lir.Frame.mk ?_ ?_
  · funext s
    change ((fr.set r v).get s).map UInt64.toBitVec = _
    rw [get_set fr h]
    by_cases hs : s = r <;> simp [hs, toLir]
  · funext n
    simp only [toLir, getSlot_set]

@[simp] theorem setSlot_wellFormed (fr : Frame) (h : fr.WellFormed) (n : Nat) (v : UInt64) :
    (fr.setSlot n v).WellFormed := by
  rcases fr with ⟨vals, defd, slots⟩
  exact h

@[simp] theorem get_setSlot (fr : Frame) (r n : Nat) (v : UInt64) :
    (fr.setSlot n v).get r = fr.get r := by
  rcases fr with ⟨vals, defd, slots⟩
  rfl

private theorem append_none_get (xs : Array (Option UInt64)) (n i : Nat) :
    (xs ++ Array.replicate n none)[i]?.join = xs[i]?.join := by
  simp only [Array.getElem?_append, Array.getElem?_replicate]
  split
  · rfl
  · next h =>
    rw [getElem?_neg xs i h]
    split <;> rfl

@[simp] theorem getSlot_setSlot (fr : Frame) (n k : Nat) (v : UInt64) :
    (fr.setSlot n v).getSlot k = if k = n then some v else fr.getSlot k := by
  rcases fr with ⟨vals, defd, slots⟩
  simp only [setSlot, getSlot]
  split
  · next hn =>
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hk : k = n
    · simp [hk, hn]
    · simp [hk, Ne.symm hk]
  · next hn =>
    have hb : n < (slots ++ Array.replicate (n + 1 - slots.size) none).size := by
      simp only [Array.size_append, Array.size_replicate]; omega
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hk : k = n
    · have hb' : n < slots.size + (n + 1 - slots.size) := by omega
      simp [hk, hb']
    · simp only [hk, Ne.symm hk, ite_false, append_none_get]

@[simp] theorem setSlot_toLir (fr : Frame) (n : Nat) (v : UInt64) :
    (fr.setSlot n v).toLir = fr.toLir.setSlot n v.toBitVec := by
  change Lir.Frame.mk _ _ = Lir.Frame.mk _ _
  refine congrArg₂ Lir.Frame.mk ?_ ?_
  · funext r
    simp only [toLir, get_setSlot]
  · funext k
    change ((fr.setSlot n v).getSlot k).map UInt64.toBitVec = _
    rw [getSlot_setSlot]
    by_cases hk : k = n <;> simp [hk, toLir]

@[simp] theorem read_toLir (fr : Frame) (l : Lir.Loc Nat) :
    fr.toLir.read l = (fr.read l).map UInt64.toBitVec := by
  cases l <;> rfl

@[simp] theorem readAll_toLir (fr : Frame) (ls : List (Lir.Loc Nat)) :
    fr.toLir.readAll ls = (fr.readAll ls).map (List.map UInt64.toBitVec) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [Lir.Frame.readAll, readAll, List.mapM_cons, read_toLir] at *
    cases h : fr.read l <;> cases ht : List.mapM fr.read ls <;> simp_all

/-- Writing an argument or result list preserves the frame invariant. -/
theorem writeAll_wellFormed (fr : Frame) (h : fr.WellFormed)
    (ls : List (Lir.Loc Nat)) (vs : List UInt64) (fr' : Frame)
    (hw : fr.writeAll ls vs = some fr') : fr'.WellFormed := by
  induction ls generalizing fr vs with
  | nil => cases vs <;> cases hw; exact h
  | cons l ls ih =>
    cases vs with
    | nil => cases l <;> cases hw
    | cons v vs =>
      cases l with
      | reg r => exact ih _ (set_wellFormed fr h r v) _ hw
      | slot n => exact ih _ (setSlot_wellFormed fr h n v) _ hw

/-- Executable and semantic argument/result writes coincide. -/
theorem writeAll_toLir (fr : Frame) (h : fr.WellFormed)
    (ls : List (Lir.Loc Nat)) (vs : List UInt64) :
    fr.toLir.writeAll ls (vs.map UInt64.toBitVec) =
      (fr.writeAll ls vs).map Frame.toLir := by
  induction ls generalizing fr vs with
  | nil => cases vs <;> rfl
  | cons l ls ih =>
    cases vs with
    | nil => cases l <;> rfl
    | cons v vs =>
      cases l with
      | reg r =>
        simp only [writeAll, Lir.Frame.writeAll, List.map_cons, Lir.Frame.write]
        rw [← set_toLir fr h]
        exact ih _ (set_wellFormed fr h r v) _
      | slot n =>
        simp only [writeAll, Lir.Frame.writeAll, List.map_cons, Lir.Frame.write]
        rw [← setSlot_toLir]
        exact ih _ (setSlot_wellFormed fr h n v) _

end Frame
end Silmaril.Compile.Mir.Interp
