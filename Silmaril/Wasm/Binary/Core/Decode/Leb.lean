module

public import Silmaril.Wasm.Binary.Core.Decode

@[expose] public section

/-! # Runs of the decoder's byte and LEB128 readers

Inversion lemmas for successful runs of `DecodeM` (`bind`, `pure`, `throw`), and the
loops of `readU`/`readS` against the grammar's `UN`/`SN`, by induction on the fuel.
`DecodeSound.lean` turns them into the `Sound` lemmas. -/

namespace Silmaril.Wasm.Binary.Core.Decode

open Silmaril.Wasm

theorem run_bind_ok {α β : Type} {x : DecodeM α} {f : α → DecodeM β} {c c' : Cursor} {b : β}
    (h : (x >>= f).run c = .ok (b, c')) :
    ∃ a c₁, x.run c = .ok (a, c₁) ∧ (f a).run c₁ = .ok (b, c') := by
  simp only [StateT.run_bind] at h
  cases hx : x.run c with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem run_pure_ok {α : Type} {a b : α} {c c' : Cursor}
    (h : (pure a : DecodeM α).run c = .ok (b, c')) : a = b ∧ c = c' := by
  cases h; exact ⟨rfl, rfl⟩

theorem run_throw_ok {α : Type} {e : String} {c c' : Cursor} {b : α}
    (h : (throw e : DecodeM α).run c = .ok (b, c')) : False := by
  cases h

theorem decodeError_ok {α : Type} {msg : String} {c c' : Cursor} {b : α}
    (h : (decodeError msg : DecodeM α).run c = .ok (b, c')) : False := by
  cases h

theorem Cursor.rest_eq_cons {c : Cursor} (h : c.pos < c.bytes.size) :
    c.rest = c.bytes[c.pos] :: ({ c with pos := c.pos + 1 } : Cursor).rest := by
  simp only [Cursor.rest]
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp only [Array.getElem_toList]
  rfl

theorem readByte_ok {c c' : Cursor} {b : UInt8} (h : readByte.run c = .ok (b, c')) :
    c'.bytes = c.bytes ∧ c.rest = b :: c'.rest := by
  simp only [readByte, StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · rename_i hp
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] at h
    cases h
    exact ⟨rfl, Cursor.rest_eq_cons hp⟩
  · cases h

theorem readBytes_ok {n : Nat} {c c' : Cursor} {ba : ByteArray}
    (h : (readBytes n).run c = .ok (ba, c')) :
    c'.bytes = c.bytes ∧ c.rest = ba.data.toList ++ c'.rest ∧ ba.data.toList.length = n := by
  simp only [readBytes, StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · rename_i hp
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] at h
    cases h
    simp only [Cursor.rest, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      Nat.add_sub_cancel_left, List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data]
    refine ⟨trivial, ?_, by simp at hp ⊢; omega⟩
    rw [← List.drop_drop, List.take_append_drop]
  · exact (decodeError_ok h).elim

/-- The loop of `readU`: what it reads from `shift` is `2 ^ shift` times a value that
the bytes encode in `UN M`, for every `M` that allows `fuel` bytes and bounds the value. -/
theorem readU_go_ok (fuel : Nat) {shift : Nat} {c c' : Cursor} {v : Nat}
    (h : (readU.go shift fuel).run c = .ok (v, c')) :
    c'.bytes = c.bytes ∧ ∃ pre m, c.rest = pre ++ c'.rest ∧ v = m * 2 ^ shift ∧
      ∀ M, fuel ≤ (M + 6) / 7 → m < 2 ^ M → UN M pre m := by
  induction fuel generalizing shift c v with
  | zero => exact (run_throw_ok h).elim
  | succ fuel ih =>
    simp only [readU.go] at h
    obtain ⟨b, c₁, hb, h⟩ := run_bind_ok h
    obtain ⟨hb₁, hb₂⟩ := readByte_ok hb
    split at h
    · rename_i hlt
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      refine ⟨hb₁, [b], b.toNat, hb₂, by rw [Nat.mod_eq_of_lt hlt], fun M _ hM => ?_⟩
      exact UN.byte b hlt hM
    · rename_i hge
      obtain ⟨x, c₂, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hx₁, pre, m, hx₂, rfl, hm⟩ := ih hx
      have hb := b.toNat_lt
      refine ⟨hx₁.trans hb₁, b :: pre, 2 ^ 7 * m + (b.toNat - 2 ^ 7), by rw [hb₂, hx₂]; rfl,
        ?_, fun M hfuel hM => ?_⟩
      · rw [Nat.pow_add]
        simp only [Nat.reducePow] at hge hb ⊢
        rw [show b.toNat % 128 = b.toNat - 128 by omega]
        grind
      · cases fuel with
        | zero => exact (run_throw_ok hx).elim
        | succ fuel =>
          have hM7 : 2 ^ M = 2 ^ 7 * 2 ^ (M - 7) := by
            rw [← Nat.pow_add]; congr 1; omega
          refine UN.cont b (by omega) (by omega) (hm (M - 7) (by omega) ?_)
          rw [hM7] at hM
          simp only [Nat.reducePow] at hge hb hM ⊢
          omega

/-- The loop of `readS`: what it adds to `acc` from `shift` is `2 ^ shift` times a value
that the bytes encode in `SN M`, for every `M` that allows `fuel` bytes and bounds the
value. -/
theorem readS_go_ok (fuel : Nat) {shift : Nat} {acc : Int} {c c' : Cursor} {v : Int}
    (h : (readS.go shift fuel acc).run c = .ok (v, c')) :
    c'.bytes = c.bytes ∧ ∃ pre i, c.rest = pre ++ c'.rest ∧ v = acc + i * 2 ^ shift ∧
      ∀ M, fuel ≤ (M + 6) / 7 → -(2 : Int) ^ (M - 1) ≤ i → i < 2 ^ (M - 1) → SN M pre i := by
  induction fuel generalizing shift acc c v with
  | zero => exact (run_throw_ok h).elim
  | succ fuel ih =>
    simp only [readS.go] at h
    obtain ⟨b, c₁, hb, h⟩ := run_bind_ok h
    obtain ⟨hb₁, hb₂⟩ := readByte_ok hb
    have hb := b.toNat_lt
    split at h
    · rename_i hlt
      have hmod : b.toNat % 128 = b.toNat := Nat.mod_eq_of_lt hlt
      split at h
      · rename_i hneg
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hb₁, [b], (b.toNat : Int) - 2 ^ 7, hb₂, ?_, fun M _ hM _ => ?_⟩
        · rw [hmod, Int.pow_add]
          grind
        · exact SN.neg b hneg hlt (by omega)
      · rename_i hpos
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hb₁, [b], b.toNat, hb₂, by rw [hmod], fun M _ _ hM => ?_⟩
        exact SN.pos b (by omega) (by exact_mod_cast hM)
    · rename_i hge
      obtain ⟨hx₁, pre, i, hx₂, rfl, hi⟩ := ih h
      refine ⟨hx₁.trans hb₁, b :: pre, 2 ^ 7 * i + ((b.toNat : Int) - 2 ^ 7),
        by rw [hb₂, hx₂]; rfl, ?_, fun M hfuel hM₁ hM₂ => ?_⟩
      · rw [Int.pow_add, show b.toNat % 128 = b.toNat - 128 by omega]
        push_cast [show 128 ≤ b.toNat by omega]
        grind
      · cases fuel with
        | zero => exact (run_throw_ok h).elim
        | succ fuel =>
          have hM7 : (2 : Int) ^ (M - 1) = 2 ^ 7 * 2 ^ (M - 7 - 1) := by
            rw [← Int.pow_add]; congr 1; omega
          refine SN.cont b (by omega) (by omega) (hi (M - 7) (by omega) ?_ ?_)
          · rw [hM7] at hM₁
            simp only [Int.reducePow] at hM₁ ⊢
            omega
          · rw [hM7] at hM₂
            simp only [Int.reducePow] at hM₂ ⊢
            omega

end Silmaril.Wasm.Binary.Core.Decode
