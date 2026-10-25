module

public import Silmaril.Wasm.Binary.Core.Decode.Leb

@[expose] public section

/-! # Runs of the memory and data readers

Successful runs of `readLimits`, `readMemType`, `readMemArg` and `readData` against
`Limits`, `MemType`, `Memarg` and `Data` (every Core 3.0 form enabled), in the shape of
`Sound`; `DecodeSound.lean` states them as `Sound` lemmas. `readData` takes the
soundness of `readExpr` as a hypothesis. -/

namespace Silmaril.Wasm.Binary.Core.Decode

open Silmaril.Wasm

theorem readU_ok (N : Nat) {c c' : Cursor} {n : Nat} (h : (readU N).run c = .ok (n, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ UN N pre n := by
  simp only [readU] at h
  obtain ⟨m, c₁, hm, h⟩ := run_bind_ok h
  split at h
  · rename_i hlt
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨h₁, pre, k, h₂, rfl, hk⟩ := readU_go_ok _ hm
    rw [Nat.pow_zero, Nat.mul_one] at hlt ⊢
    exact ⟨h₁, pre, h₂, hk N (Nat.le_refl _) hlt⟩
  · exact (run_throw_ok h).elim

theorem readIdx_ok {k : IndexKind} {c c' : Cursor} {x : Idx k}
    (h : (readIdx (k := k)).run c = .ok (x, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ Index pre x := by
  simp only [readIdx] at h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  split at h
  · obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact readU_ok 32 hn
  · exact (decodeError_ok h).elim

theorem readLimits_readBound_ok (N : Nat) {c c' : Cursor} {a : Fin (2 ^ 64)}
    (h : (readLimits.readBound N).run c = .ok (a, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ UN N pre a.val := by
  simp only [readLimits.readBound] at h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  split at h
  · obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact readU_ok N hn
  · exact (decodeError_ok h).elim

theorem readLimits_ok {c c' : Cursor} {a : AddrType × Wasm.Limits}
    (h : readLimits.run c = .ok (a, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ Limits Forms.all pre a := by
  simp only [readLimits] at h
  obtain ⟨b, c₁, hb, h⟩ := run_bind_ok h
  obtain ⟨hb₁, hb₂⟩ := readByte_ok hb
  split at h
  · rename_i hf
    have : b = 0x00 := UInt8.toNat_inj.mp hf
    subst this
    obtain ⟨n, c₂, hn, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hn₁, pre, hn₂, hn₃⟩ := readLimits_readBound_ok 64 hn
    exact ⟨hn₁.trans hb₁, _ :: pre, by rw [hb₂, hn₂]; rfl, .i32 (.u64 rfl hn₃)⟩
  · rename_i hf
    have : b = 0x01 := UInt8.toNat_inj.mp hf
    subst this
    obtain ⟨n, c₂, hn, h⟩ := run_bind_ok h
    obtain ⟨m, c₃, hm, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hn₁, pre, hn₂, hn₃⟩ := readLimits_readBound_ok 64 hn
    obtain ⟨hm₁, pre', hm₂, hm₃⟩ := readLimits_readBound_ok 64 hm
    exact ⟨hm₁.trans (hn₁.trans hb₁), _ :: (pre ++ pre'),
      by rw [hb₂, hn₂, hm₂]; simp, .i32Max (.u64 rfl hn₃) (.u64 rfl hm₃)⟩
  · rename_i hf
    have : b = 0x04 := UInt8.toNat_inj.mp hf
    subst this
    obtain ⟨n, c₂, hn, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hn₁, pre, hn₂, hn₃⟩ := readLimits_readBound_ok 64 hn
    exact ⟨hn₁.trans hb₁, _ :: pre, by rw [hb₂, hn₂]; rfl, .i64 rfl hn₃⟩
  · rename_i hf
    have : b = 0x05 := UInt8.toNat_inj.mp hf
    subst this
    obtain ⟨n, c₂, hn, h⟩ := run_bind_ok h
    obtain ⟨m, c₃, hm, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hn₁, pre, hn₂, hn₃⟩ := readLimits_readBound_ok 64 hn
    obtain ⟨hm₁, pre', hm₂, hm₃⟩ := readLimits_readBound_ok 64 hm
    exact ⟨hm₁.trans (hn₁.trans hb₁), _ :: (pre ++ pre'),
      by rw [hb₂, hn₂, hm₂]; simp, .i64Max rfl hn₃ hm₃⟩
  · exact (decodeError_ok h).elim

theorem readMemType_ok {c c' : Cursor} {a : Wasm.MemoryType}
    (h : readMemType.run c = .ok (a, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ MemType Forms.all pre a := by
  simp only [readMemType] at h
  obtain ⟨⟨t, l⟩, c₁, hl, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ := run_pure_ok h
  obtain ⟨h₁, pre, h₂, h₃⟩ := readLimits_ok hl
  exact ⟨h₁, pre, h₂, .mk h₃⟩

theorem readMemArg_ok {c c' : Cursor} {a : MemIdx × Wasm.MemArg}
    (h : readMemArg.run c = .ok (a, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ Memarg Forms.all pre a := by
  simp only [readMemArg] at h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  obtain ⟨hn₁, pn, hn₂, hn₃⟩ := readU_ok 32 hn
  split at h
  · rename_i hlt
    obtain ⟨o, c₂, ho, h⟩ := run_bind_ok h
    obtain ⟨ho₁, po, ho₂, ho₃⟩ := readU_ok 64 ho
    split at h
    · obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨ho₁.trans hn₁, pn ++ po, by rw [hn₂, ho₂, List.append_assoc],
        .mem0 hn₃ hlt (.u64 rfl ho₃)⟩
    · exact (decodeError_ok h).elim
  · rename_i hge
    split at h
    · rename_i hlt
      obtain ⟨x, c₂, hx, h⟩ := run_bind_ok h
      obtain ⟨hx₁, px, hx₂, hx₃⟩ := readIdx_ok hx
      obtain ⟨o, c₃, ho, h⟩ := run_bind_ok h
      obtain ⟨ho₁, po, ho₂, ho₃⟩ := readU_ok 64 ho
      split at h
      · obtain ⟨rfl, rfl⟩ := run_pure_ok h
        exact ⟨ho₁.trans (hx₁.trans hn₁), pn ++ px ++ po, by rw [hn₂, hx₂, ho₂]; simp,
          .memIdx rfl hn₃ (by omega) hlt rfl hx₃ (.u64 rfl ho₃)⟩
      · exact (decodeError_ok h).elim
    · exact (decodeError_ok h).elim

theorem seq_byte_self : ∀ bs : List UInt8, Seq Byte bs bs
  | [] => .nil
  | b :: bs => .cons (b := [b]) (.mk b) (seq_byte_self bs)

theorem readCount_ok {c c' : Cursor} {n : Nat} (h : readCount.run c = .ok (n, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ U32 pre n := by
  simp only [readCount, remaining] at h
  obtain ⟨m, c₁, hm, h⟩ := run_bind_ok h
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind] at h
  split at h
  · obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact readU_ok 32 hm
  · exact (decodeError_ok h).elim

theorem readData_readByteVec_ok {c c' : Cursor} {a : ByteArray}
    (h : readData.readByteVec.run c = .ok (a, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ ∃ bs, ByteVec pre bs ∧ a = dataBytes bs := by
  simp only [readData.readByteVec] at h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  obtain ⟨hn₁, pn, hn₂, hn₃⟩ := readCount_ok hn
  obtain ⟨hb₁, hb₂, hb₃⟩ := readBytes_ok h
  refine ⟨hb₁.trans hn₁, pn ++ a.data.toList, by rw [hn₂, hb₂, List.append_assoc],
    a.data.toList, .mk (by rw [hb₃]; exact hn₃) (seq_byte_self _), ?_⟩
  simp [dataBytes]

theorem readData_ok
    (hE : ∀ ⦃c : Cursor⦄ ⦃e : Wasm.Expr⦄ ⦃c' : Cursor⦄, readExpr.run c = .ok (e, c') →
      c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ Expr Forms.all pre e)
    {c c' : Cursor} {a : Wasm.Data} (h : readData.run c = .ok (a, c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ Data Forms.all pre a := by
  simp only [readData] at h
  obtain ⟨k, c₁, hk, h⟩ := run_bind_ok h
  obtain ⟨hk₁, pk, hk₂, hk₃⟩ := readU_ok 32 hk
  split at h
  · obtain ⟨e, c₂, he, h⟩ := run_bind_ok h
    obtain ⟨he₁, pe, he₂, he₃⟩ := hE he
    obtain ⟨ba, c₃, hb, h⟩ := run_bind_ok h
    obtain ⟨hb₁, pb, hb₂, bs, hb₃, rfl⟩ := readData_readByteVec_ok hb
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨hb₁.trans (he₁.trans hk₁), pk ++ pe ++ pb, by rw [hk₂, he₂, hb₂]; simp,
      .k0 hk₃ he₃ hb₃⟩
  · obtain ⟨ba, c₂, hb, h⟩ := run_bind_ok h
    obtain ⟨hb₁, pb, hb₂, bs, hb₃, rfl⟩ := readData_readByteVec_ok hb
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨hb₁.trans hk₁, pk ++ pb, by rw [hk₂, hb₂, List.append_assoc], .k1 rfl hk₃ hb₃⟩
  · obtain ⟨x, c₂, hx, h⟩ := run_bind_ok h
    obtain ⟨hx₁, px, hx₂, hx₃⟩ := readIdx_ok hx
    obtain ⟨e, c₃, he, h⟩ := run_bind_ok h
    obtain ⟨he₁, pe, he₂, he₃⟩ := hE he
    obtain ⟨ba, c₄, hb, h⟩ := run_bind_ok h
    obtain ⟨hb₁, pb, hb₂, bs, hb₃, rfl⟩ := readData_readByteVec_ok hb
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨hb₁.trans (he₁.trans (hx₁.trans hk₁)), pk ++ px ++ pe ++ pb,
      by rw [hk₂, hx₂, he₂, hb₂]; simp, .k2 rfl hk₃ hx₃ he₃ hb₃⟩
  · exact (decodeError_ok h).elim

end Silmaril.Wasm.Binary.Core.Decode
