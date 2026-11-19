module

public import Silmaril.Containers.Cas.Bridge.Defs
import Silmaril.Proofs.Containers.Cas.Bridge.Basic

public section
namespace Silmaril.Containers.Oci

theorem fetch_eq_bytes (L : Layout) (sound : Cas.Store.Sound Silmaril.Crypto.sha256 L.raw) :
    L.fetch = fetchBytes L.raw :=
  Silmaril.Proofs.Containers.Cas.Bridge.fetch_eq_bytes L sound

/-- Reuse a separately proved integrity certificate; no repeated digest evaluation is needed. -/
theorem load_checked_eq_bytes (L : Layout)
    (sound : Cas.Store.Sound Silmaril.Crypto.sha256 L.raw) (manifest : Digest) :
    load L manifest = loadBytes L.raw manifest := by
  simp only [load, loadBytes, fetch_eq_bytes L sound]

/-- Connect decoded bytes and abstract stores by their common flat image. The two loader
certificates are explicit; neither follows merely from having a digest or an external report. -/
theorem runtimeBytes_eq_layered {D P E : Type} (store : Cas.Store Digest (List UInt8))
    (R : Runtime (Flat (List UInt8)) P E) (S : Stores D (List UInt8)) (m : Layered D)
    (d : Digest) (flat : Flat (List UInt8)) (hm : m.flatten S = some flat)
    (hb : loadBytes store d = .ok flat) (b : Beh E) :
    (runtimeBytes store R).beh d b ↔ (Runtime.layered S R).beh m b := by
  simp [Runtime.beh, Runtime.layered, runtimeBytes, hm, hb, Except.bind]

end Silmaril.Containers.Oci
