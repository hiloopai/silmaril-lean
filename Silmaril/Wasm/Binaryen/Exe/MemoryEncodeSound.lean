module

public import Silmaril.Wasm.Binaryen.Exe.MemoryEncode
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound

@[expose] public section

/-! # Soundness of scalar memory encodings against the Core binary grammar -/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem encMemArg_sound {x : MemIdx} {a : Wasm.MemArg} {bs : List UInt8}
    (h : encMemArg x a = .ok bs) : Memarg Forms.all bs (x, a) := by
  unfold encMemArg at h
  split at h
  · next hc =>
    split at h
    · next hx =>
      cases Except.ok.inj h
      have hx' : x = ⟨0⟩ := by
        cases x with
        | mk v => congr 1; exact Fin.ext hx
      subst x
      exact .mem0 (encU_sound a.align.isLt) hc (.u64 rfl (encU_sound a.offset.isLt))
    · cases Except.ok.inj h
      exact .memIdx rfl (encU_sound (by omega)) (by omega) (by omega) (by omega)
        (encIdx_sound x) (.u64 rfl (encU_sound a.offset.isLt))
  · exact absurd h throw_ne_ok

theorem intLoadOpcode_sound {t : IntType} {p : Option (PackSize × Signedness)} {b : UInt8}
    (h : intLoadOpcode t p = .ok b) : MemOp b (fun x a => .intLoad t p x a) := by
  unfold intLoadOpcode at h
  split at h <;> first
    | exact absurd h throw_ne_ok
    | (cases Except.ok.inj h; constructor)

theorem intStoreOpcode_sound {t : IntType} {p : Option PackSize} {b : UInt8}
    (h : intStoreOpcode t p = .ok b) : MemOp b (fun x a => .intStore t p x a) := by
  unfold intStoreOpcode at h
  split at h <;> first
    | exact absurd h throw_ne_ok
    | (cases Except.ok.inj h; constructor)

/-- Nonzero indices require the Core 3.0 index-immediate form. The previous
memory-zero-only encoder could prove this at either gate; that reserved-zero
case remains available separately in `encMemoryIdx_zero_sound`. -/
theorem encMemoryIdx_sound {x : MemIdx} {bs : List UInt8}
    (h : encMemoryIdx x = .ok bs) : ReservedIdx true bs x := by
  unfold encMemoryIdx at h
  cases Except.ok.inj h
  exact .idx rfl (encIdx_sound x)

/-- Memory zero retains the reserved-byte encoding, including at a disabled
index-immediate gate (the Wasm 1.0 form). -/
theorem encMemoryIdx_zero_sound {allow : Bool} {bs : List UInt8}
    (h : encMemoryIdx ⟨0⟩ = .ok bs) : ReservedIdx allow bs (⟨0⟩ : MemIdx) := by
  have hz : encMemoryIdx ⟨0⟩ = .ok [0x00] := by
    simp [encMemoryIdx, encIdx, encU, Idx.toNat, pure, Except.pure]
  rw [hz] at h
  cases Except.ok.inj h
  exact .zero

theorem encMemory_sound {m : MemoryType} {bs : List UInt8}
    (h : encMemory m = .ok bs) : MemType Forms.all bs m := by
  rcases m with ⟨addr, lo, hi⟩
  cases addr with
  | i32 =>
    simp only [encMemory] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases hi with
    | none =>
      cases Except.ok.inj h
      exact .mk (.i32 (.u32 (encU32_sound hb)))
    | some hi =>
      obtain ⟨c, hc, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .mk (.i32Max (.u32 (encU32_sound hb)) (.u32 (encU32_sound hc)))
  | i64 =>
    cases hi with
    | none =>
      cases Except.ok.inj h
      exact .mk (.i64 rfl (encU_sound lo.isLt))
    | some hi =>
      cases Except.ok.inj h
      exact .mk (.i64Max rfl (encU_sound lo.isLt) (encU_sound hi.isLt))

end Silmaril.Wasm.Binaryen.Exe
