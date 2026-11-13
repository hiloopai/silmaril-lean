module

public import Silmaril.Servers.WasiHttp.Defs

/-!
# `wasi:http` value encodings: paths read back
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiHttp

open Silmaril.Servers.WasiHttp

/-- A path read back. -/
theorem pathOf_pathV (p : Option (List UInt8)) : pathOf (some [pathV p]) = p := by
  cases p with
  | none => rfl
  | some p =>
    have h : ∀ b : UInt8, (Char.ofNat b.toNat).toNat.toUInt8 = b := by decide
    simp [pathOf, pathV, octetsOf, List.filterMap_map, h]

end Silmaril.Proofs.Servers.WasiHttp
