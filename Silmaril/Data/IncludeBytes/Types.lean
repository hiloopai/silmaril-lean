module

/-! Data-only compact byte decoder shared with the elaborator-side include utility. -/
@[expose] public section
namespace Silmaril.IncludeBytes

def bytesLE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat n :: bytesLE k (n / 256)


def bytesChunks (chunk : Nat) : Nat → List Nat → List UInt8
  | _, [] => []
  | len, c :: cs => bytesLE (min chunk len) c ++ bytesChunks chunk (len - chunk) cs


def decode (chunk len : Nat) (cs : List Nat) : ByteArray := ⟨⟨bytesChunks chunk len cs⟩⟩


end Silmaril.IncludeBytes
