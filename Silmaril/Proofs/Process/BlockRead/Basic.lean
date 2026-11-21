module

public import Silmaril.Process.BlockRead.Defs

/-! # A checked object slice is a permitted sub-read of its placed allocation -/

public section

namespace Silmaril.Proofs.Process.BlockRead

open Silmaril.Process.BlockRead

theorem read_placed {Block} {base : Block → Nat} {obj : Request Block} {flat : FlatRequest} {out}
    (related : Placed base obj flat) (ok : obj.read = some out) : flat.read = some out := by
  obtain ⟨layout, addr, width⟩ := related
  obtain ⟨bytes, live, slice⟩ := Option.bind_eq_some_iff.mp ok
  split at slice
  · rename_i bounds
    cases slice
    unfold FlatRequest.read
    rw [addr, width]
    exact Silmaril.Process.Memory.readBytes_sub_range (layout.contents _ _ live) (by omega) bounds.2
  · contradiction

end Silmaril.Proofs.Process.BlockRead
