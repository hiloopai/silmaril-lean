module

import Init.Omega

/-! A format-independent overlapping backward byte copy. -/

@[expose] public section

namespace Silmaril.Formats.Compression.HistoryCopy

/-- A match reads from the then-current history at each byte. The read byte
    extends history immediately, so the next byte can come from this match. -/
inductive Wire (distance : Nat) : List UInt8 → List UInt8 → Prop where
  | nil (history : List UInt8) : Wire distance history []
  | cons {history bytes : List UInt8} {byte : UInt8} :
      0 < distance → distance ≤ history.length →
      history[history.length - distance]? = some byte →
      Wire distance (history ++ [byte]) bytes →
      Wire distance history (byte :: bytes)

/-- Copy only with a proven in-bounds index. The growing array permits overlap. -/
def copy (distance : Nat) (positive : 0 < distance) :
    Nat → (data : Array UInt8) → distance ≤ data.size → Array UInt8
  | 0, data, _ => data
  | count + 1, data, available =>
    let byte := data[data.size - distance]'(by omega)
    copy distance positive count (data.push byte) (by simp; omega)

end Silmaril.Formats.Compression.HistoryCopy
