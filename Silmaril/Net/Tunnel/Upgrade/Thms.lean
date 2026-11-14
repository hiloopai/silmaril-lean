module

public import Silmaril.Net.Tunnel.Upgrade.Defs

@[expose] public section

/-!
# HTTP Upgrade: theorems

PROVED (standard axioms):

* `validSwitch_offered`: a valid `101` switches only to protocols the client offered, and only
  on a request that carried `Connection: upgrade` (RFC 9110 §7.8);
* `afterAnswer_offered`: so the protocol the connection carries after a valid answer was
  offered by the client;
* `h2_rejects_upgrade`: an HTTP/2 message whose header section carries `upgrade` is malformed
  (RFC 9113 §8.2.2, §8.6), through the HTTP/2 track's `validRegular`.
-/

namespace Silmaril.Net.Tunnel

theorem validSwitch_offered {r : UpgradeRequest} {to : List UpgradeToken}
    (h : validSwitch r (.switch to) = true) :
    r.connectionUpgrade = true ∧ to ≠ [] ∧ ∀ t ∈ to, t ∈ r.offered := by
  simp only [validSwitch, UpgradeRequest.valid, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

theorem afterAnswer_offered {r : UpgradeRequest} {a : UpgradeAnswer} {t : UpgradeToken}
    (h : validSwitch r a = true) (ht : afterAnswer a = some t) : t ∈ r.offered := by
  cases a with
  | switch to =>
    obtain ⟨-, -, hall⟩ := validSwitch_offered h
    exact hall t (List.mem_of_getLast? ht)
  | ignore | required _ => simp [afterAnswer] at ht

theorem h2_rejects_upgrade (v : List UInt8) :
    Silmaril.Net.Http2.validRegular (upgradeEntry v) = false := by
  have : Silmaril.Net.Http2.connectionSpecific.contains (Silmaril.Net.Hpack.ascii "upgrade") =
    true := by decide
  simp only [Silmaril.Net.Http2.validRegular, upgradeEntry, this, Bool.not_true, Bool.and_false,
    Bool.false_and]

end Silmaril.Net.Tunnel
