module

public import Silmaril.Process.Memory

/-! # Adding mapping permissions while retaining existing backing

This is a monotonicity interface, not a memory-well-formedness claim. In
particular extra regions may overlap; clients needing isolation must say so.
-/

@[expose] public section

namespace Silmaril.Process.Memory

structure RegionExtension (before after : Memory) : Prop where
  regions : before.regions ⊆ after.regions
  bytes : after.bytes = before.bytes

theorem RegionExtension.permits {before after : Memory} (extension : RegionExtension before after)
    {access : Access} {address : Nat} (permitted : before.permits access address = true) :
    after.permits access address = true := by
  simp only [Memory.permits, List.any_eq_true] at permitted ⊢
  obtain ⟨region, member, allowed⟩ := permitted
  exact ⟨region, extension.regions member, allowed⟩

theorem RegionExtension.permitted {before after : Memory} (extension : RegionExtension before after)
    {access : Access} {address length : Nat} (permitted : before.Permitted access address length) :
    after.Permitted access address length := by
  obtain ⟨start, limit, allowed⟩ := (checkSpan_iff _ _ _ _).mp permitted
  exact (checkSpan_iff _ _ _ _).mpr ⟨start, limit, fun _ bound => extension.permits (allowed _ bound)⟩

theorem RegionExtension.readWith {before after : Memory} (extension : RegionExtension before after)
    {access : Access} {address length : Nat} {bytes : List Byte}
    (read : before.readWith access address length = some bytes) :
    after.readWith access address length = some bytes := by
  have permitted := extension.permitted (readWith_permitted read)
  have size := readWith_length read
  subst length
  apply readWith_eq after access address bytes permitted
  intro index bound
  rw [extension.bytes]
  exact readWith_get read index bound

theorem regionExtension_cons (memory : Memory) (region : Region) :
    RegionExtension memory { memory with regions := region :: memory.regions } :=
  ⟨by intro _ member; exact List.mem_cons_of_mem _ member, rfl⟩

end Silmaril.Process.Memory
