module

public import Silmaril.Servers.WasiHttp.Defs

/-!
# `wasi:http` value encodings: paths read back
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiHttp

open Silmaril.Servers.WasiHttp
open Silmaril.Wasm.Component (Val)

/-- The octet of the `char` of an octet. -/
theorem octet_ofNat : ∀ b : UInt8, octet (Char.ofNat b.toNat) = b := by decide

/-- A string of octets read back. -/
theorem octetsOf_map (p : List UInt8) :
    octetsOf (p.map fun b => Val.char (Char.ofNat b.toNat)) = p := by
  simp [octetsOf, List.filterMap_map, octet_ofNat]

/-- A path read back. -/
theorem pathOf_pathV (p : Option (List UInt8)) : pathOf (some [pathV p]) = p := by
  cases p with
  | none => rfl
  | some p => simp [pathOf, pathV, strV, octetsOf_map]

end Silmaril.Proofs.Servers.WasiHttp
