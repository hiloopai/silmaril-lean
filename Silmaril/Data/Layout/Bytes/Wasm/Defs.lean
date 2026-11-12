module

public import Silmaril.Data.Layout.Bytes.Thms
public import Silmaril.Wasm.Execution.Core.Runtime

/-!
# Byte views over Wasm linear memories

A Wasm memory instance (`Silmaril.Wasm.Execution.Core.MemInst`) stores its bytes in a `ByteArray`. Lens reads past the
current size are `none`; lens writes past it are dropped (a trap is the caller's business:
check `ByteMem.Readable` first). Bytes are `UInt8` there and `BitVec 8` here, related by
`UInt8.toBitVec`/`UInt8.ofBitVec`.
-/

@[expose] public section

namespace Silmaril.Data.Layout

instance : ByteMem ByteArray where
  get? m a := m.data[a]?.map UInt8.toBitVec
  set m a v := ⟨m.data.setIfInBounds a (UInt8.ofBitVec v)⟩
  get?_set_self m a v h := by
    have : a < m.data.size := by
      by_contra hc; simp [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
    simp [Array.getElem?_setIfInBounds_self_of_lt this]
  get?_set_ne m a b v h := by simp [Array.getElem?_setIfInBounds_ne h]

open Silmaril.Wasm.Execution.Core in
instance : ByteMem MemInst where
  get? m a := ByteMem.get? m.bytes a
  set m a v := { m with bytes := ByteMem.set m.bytes a v }
  get?_set_self m a v h := ByteMem.get?_set_self (M := ByteArray) m.bytes a v h
  get?_set_ne m a b v h := ByteMem.get?_set_ne (M := ByteArray) m.bytes a b v h

end Silmaril.Data.Layout
