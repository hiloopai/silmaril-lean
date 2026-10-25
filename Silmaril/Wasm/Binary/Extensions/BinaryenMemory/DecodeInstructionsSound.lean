module

public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.DecodeInstructions
public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.DecodeInstructionsSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Decode

open Core Core.Decode Wasm.Extensions.BinaryenMemory

theorem alternative_sound {α : Type} {G : Bytes → α → Prop} {p q : DecodeM α}
    (hp : Sound G p) (hq : Sound G q) : Sound G (alternative p q) := by
  intro c a c' h
  change (match p.run c with | .ok r => Except.ok r | .error _ => q.run c) = .ok (a, c') at h
  cases hrun : p.run c with
  | ok r => rw [hrun] at h; cases h; exact hp hrun
  | error e => rw [hrun] at h; exact hq h

theorem readArrayAccess_sound (opcode : UInt8) :
    Sound (fun pre i => ArrayAccess ([opcode] ++ pre) i) (readArrayAccess opcode.toNat) := by
  intro c a c' h
  unfold readArrayAccess at h
  split at h
  · next hop =>
    obtain ⟨flags, cf, hf, h⟩ := run_bind_ok h
    obtain ⟨hbf, pf, hrf, hgf⟩ := readU_sound 32 hf
    split at h
    · next hflags =>
      obtain ⟨offset, co, ho, h⟩ := run_bind_ok h
      obtain ⟨hbo, po, hro, hgo⟩ := readU_sound 32 ho
      split at h
      · next hoff =>
        obtain ⟨type, ct, ht, h⟩ := run_bind_ok h
        obtain ⟨hbt, pt, hrt, hgt⟩ := readIdx_sound ht
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hbt.trans (hbo.trans hbf), pf ++ po ++ pt, by simp [hrf, hro, hrt], ?_⟩
        have hopcode : ScalarOp.opcode ⟨⟨opcode.toNat - 0x28, by omega⟩⟩ = opcode := by
          simp only [ScalarOp.opcode]
          rw [Nat.add_sub_of_le hop.1]
          simp
        have hg := ArrayAccess.mk (op := (⟨⟨opcode.toNat - 0x28, by omega⟩⟩ : ScalarOp))
          (arg := (⟨⟨flags - 32, by omega⟩, ⟨offset, by omega⟩⟩ : MemArg))
          (by dsimp; omega) (by simpa only [Nat.add_sub_of_le hflags.1] using hgf) hgo hgt
        simpa only [hopcode, List.append_assoc] using hg
      · exact (decodeError_ok h).elim
    · exact (decodeError_ok h).elim
  · exact (decodeError_ok h).elim

theorem readVectorArrayAccess_sound :
    Sound (fun pre i => VectorArrayAccess ([0xfd] ++ pre) i) readVectorArrayAccess := by
  intro c a c' h
  unfold readVectorArrayAccess at h
  obtain ⟨subop, cc, hc, h⟩ := run_bind_ok h
  obtain ⟨hbc, pc, hrc, hgc⟩ := readU_sound 32 hc
  split at h
  · next hsub =>
    obtain ⟨flags, cf, hf, h⟩ := run_bind_ok h
    obtain ⟨hbf, pf, hrf, hgf⟩ := readU_sound 32 hf
    split at h
    · next hflags =>
      obtain ⟨offset, co, ho, h⟩ := run_bind_ok h
      obtain ⟨hbo, po, hro, hgo⟩ := readU_sound 32 ho
      split at h
      · next hoff =>
        obtain ⟨type, ct, ht, h⟩ := run_bind_ok h
        obtain ⟨hbt, pt, hrt, hgt⟩ := readIdx_sound ht
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hbt.trans (hbo.trans (hbf.trans hbc)), pc ++ pf ++ po ++ pt,
          by simp [hrc, hrf, hro, hrt], ?_⟩
        have hc : (if subop == 11 then 11 else 0) = subop := by
          rcases hsub with rfl | rfl <;> decide
        have hg := VectorArrayAccess.mk (store := (subop == 11))
          (arg := (⟨⟨flags - 32, by omega⟩, ⟨offset, by omega⟩⟩ : MemArg))
          (hc.symm ▸ hgc) (by dsimp; omega)
          (by simpa only [Nat.add_sub_of_le hflags.1] using hgf) hgo hgt
        simpa only [List.append_assoc] using hg
      · exact (decodeError_ok h).elim
    · exact (decodeError_ok h).elim
  · exact (decodeError_ok h).elim

theorem ofCode?_sound {byte : UInt8} {order : MemoryOrder}
    (h : MemoryOrder.ofCode? byte = some order) : byte = order.code := by
  unfold MemoryOrder.ofCode? at h
  split at h <;> cases h <;> rfl

theorem ofRMWCode?_sound {byte : UInt8} {order : MemoryOrder}
    (h : MemoryOrder.ofRMWCode? byte = some order) : byte = order.rmwCode := by
  unfold MemoryOrder.ofRMWCode? at h
  split at h <;> cases h <;> rfl

theorem readOrder_sound (op : Wasm.Extensions.AtomicMemory.Access) :
    Sound (fun pre order => pre = [order.accessCode op]) (readOrder op) := by
  intro c a c' h
  unfold readOrder at h
  obtain ⟨byte, cb, hb, h⟩ := run_bind_ok h
  obtain ⟨hbb, hrb⟩ := readByte_ok hb
  split at h
  · next order ho =>
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    refine ⟨hbb, [byte], hrb, ?_⟩
    have hc : byte = order.accessCode op := by
      unfold MemoryOrder.accessCode
      by_cases hm : isRMW op = true
      · simpa only [hm, ↓reduceIte] using ofRMWCode?_sound (by simpa only [hm, ↓reduceIte] using ho)
      · simpa only [hm, Bool.false_eq_true, ↓reduceIte] using ofCode?_sound (by simpa only [hm, Bool.false_eq_true, ↓reduceIte] using ho)
    rw [hc]
  · exact (decodeError_ok h).elim

theorem readOrderedMemarg_sound (op : Wasm.Extensions.AtomicMemory.Access) :
    Sound (OrderedMemarg op) (readOrderedMemarg op) := by
  intro c a c' h
  unfold readOrderedMemarg at h
  obtain ⟨flags, cf, hf, h⟩ := run_bind_ok h
  obtain ⟨hbf, pf, hrf, hgf⟩ := readU_sound 32 hf
  split at h
  · next hflags =>
    obtain ⟨order, cr, hr, h⟩ := run_bind_ok h
    obtain ⟨hbr, pr, hrr, rfl⟩ := readOrder_sound op hr
    obtain ⟨offset, co, ho, h⟩ := run_bind_ok h
    obtain ⟨hbo, po, hro, hgo⟩ := readU_sound 64 ho
    split at h
    · obtain ⟨rfl, rfl⟩ := run_pure_ok h
      refine ⟨hbo.trans (hbr.trans hbf), pf ++ [order.accessCode op] ++ po,
        by simp [hrf, hrr, hro], ?_⟩
      apply OrderedMemarg.zero (by dsimp; omega)
      · convert hgf using 1; dsimp; omega
      · exact hgo
    · exact (decodeError_ok h).elim
  · split at h
    · next hflags' =>
      obtain ⟨memory, cm, hm, h⟩ := run_bind_ok h
      obtain ⟨hbm, pm, hrm, hgm⟩ := readIdx_sound hm
      obtain ⟨order, cr, hr, h⟩ := run_bind_ok h
      obtain ⟨hbr, pr, hrr, rfl⟩ := readOrder_sound op hr
      obtain ⟨offset, co, ho, h⟩ := run_bind_ok h
      obtain ⟨hbo, po, hro, hgo⟩ := readU_sound 64 ho
      split at h
      · obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hbo.trans (hbr.trans (hbm.trans hbf)), pf ++ pm ++ [order.accessCode op] ++ po,
          by simp [hrf, hrm, hrr, hro], ?_⟩
        apply OrderedMemarg.indexed (by dsimp; omega)
        · convert hgf using 1; dsimp; omega
        · exact hgm
        · exact hgo
      · exact (decodeError_ok h).elim
    · exact (decodeError_ok h).elim

theorem readOrderedAtomic_sound :
    Sound (fun pre i => OrderedAtomic ([0xfe] ++ pre) i) readOrderedAtomic := by
  intro c a c' h
  unfold readOrderedAtomic at h
  obtain ⟨subop, cn, hn, h⟩ := run_bind_ok h
  obtain ⟨hbn, pn, hrn, hgn⟩ := readU_sound 32 hn
  split at h
  · next hthree =>
    have hthree : subop = 3 := by simpa using hthree
    subst subop
    obtain ⟨byte, cb, hb, h⟩ := run_bind_ok h
    obtain ⟨hbb, hrb⟩ := readByte_ok hb
    split at h
    · next order ho =>
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      have hc := ofCode?_sound ho
      subst byte
      exact ⟨hbb.trans hbn, pn ++ [order.code], by simp [hrn, hrb], .fence hgn⟩
    · exact (decodeError_ok h).elim
  · split at h
    · exact (decodeError_ok h).elim
    · next op hop =>
      split at h
      · next horder =>
        obtain ⟨⟨memory, arg, order⟩, cm, hm, h⟩ := run_bind_ok h
        obtain ⟨hbm, pm, hrm, hgm⟩ := readOrderedMemarg_sound op hm
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hbm.trans hbn, pn ++ pm, by simp [hrn, hrm], ?_⟩
        have hc := AtomicMemory.Decode.ofOpcode?_sound hop
        simpa only [List.append_assoc] using OrderedAtomic.access (bn := pn) (bm := pm) horder (hc.symm ▸ hgn) hgm
      · exact (decodeError_ok h).elim

theorem readLeaf_sound (op : UInt8) :
    Sound (fun pre i => Leaf Forms.all ([op] ++ pre) i) (readLeaf op.toNat) := by
  have hold : Sound (fun pre i => Leaf Forms.all ([op] ++ pre) i)
      ((AtomicMemory.Decode.readLeaf op.toNat).map Wasm.Extensions.BinaryenMemory.Leaf.base) :=
    sound_map (AtomicMemory.Decode.readLeaf_sound op) _ (fun _ _ h => .base h)
  unfold readLeaf
  split
  · next hop =>
    have hop : op = 0xfe := UInt8.toNat_inj.mp (by simpa using hop)
    subst op
    exact alternative_sound
      (by intro c a c' h; obtain ⟨hb, p, hr, hg⟩ := readOrderedAtomic_sound h; exact ⟨hb, p, hr, .ordered hg⟩) hold
  · split
    · next hop =>
      have hop : op = 0xfd := UInt8.toNat_inj.mp (by simpa using hop)
      subst op
      exact alternative_sound
        (by intro c a c' h; obtain ⟨hb, p, hr, hg⟩ := readVectorArrayAccess_sound h; exact ⟨hb, p, hr, .vectorArray hg⟩) hold
    · exact alternative_sound
        (by intro c a c' h; obtain ⟨hb, p, hr, hg⟩ := readArrayAccess_sound op h; exact ⟨hb, p, hr, .array hg⟩) hold

theorem readExpr_sound : Sound (Expr Forms.all) readExpr :=
  Structured.Decode.readExpr_sound readLeaf readLeaf_sound

end Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Decode
