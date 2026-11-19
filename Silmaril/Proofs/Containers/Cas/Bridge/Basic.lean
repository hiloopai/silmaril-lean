module

public import Silmaril.Containers.Cas.Bridge.Defs

public section
namespace Silmaril.Proofs.Containers.Cas.Bridge
open Silmaril.Containers

theorem fetch_eq_bytes (L : Oci.Layout) (sound : Cas.Store.Sound Silmaril.Crypto.sha256 L.raw) :
    L.fetch = Oci.fetchBytes L.raw := by
  funext d
  cases h : L.raw d with
  | none => simp [Oci.Layout.fetch, Oci.fetchBytes, h]
  | some bs => simp [Oci.Layout.fetch, Oci.fetchBytes, h, sound d bs h]

end Silmaril.Proofs.Containers.Cas.Bridge
