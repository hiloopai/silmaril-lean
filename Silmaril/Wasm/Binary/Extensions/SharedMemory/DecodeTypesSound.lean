module

public import Silmaril.Wasm.Binary.Extensions.SharedMemory.DecodeTypes
public import Silmaril.Wasm.Binary.Core.DecodeSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode

open Core Core.Decode

theorem readMemType_sound : Sound (MemType Forms.all) readMemType := by
  intro c a c' h
  unfold readMemType at h
  obtain ⟨ob, cm, hob, h⟩ := bindOk h
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  split at h
  · rename_i he
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x03 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
    obtain ⟨m, ct, hm, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₁, hr₁⟩ := readByte_ok hx
    obtain ⟨hb₂, pn, hr₂, hgn⟩ := readLimits_readBound_ok 64 hn
    obtain ⟨hb₃, pm, hr₃, hgm⟩ := readLimits_readBound_ok 64 hm
    exact ⟨hb₃.trans (hb₂.trans hb₁), [0x03] ++ pn ++ pm,
      by simp [hr₁, hr₂, hr₃], .shared32 (.u64 rfl hgn) (.u64 rfl hgm)⟩
  · rename_i he
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x07 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
    obtain ⟨m, ct, hm, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₁, hr₁⟩ := readByte_ok hx
    obtain ⟨hb₂, pn, hr₂, hgn⟩ := readLimits_readBound_ok 64 hn
    obtain ⟨hb₃, pm, hr₃, hgm⟩ := readLimits_readBound_ok 64 hm
    exact ⟨hb₃.trans (hb₂.trans hb₁), [0x07] ++ pn ++ pm,
      by simp [hr₁, hr₂, hr₃], .shared64 rfl hgn hgm⟩
  · exact sound_map Core.Decode.readMemType_sound _ (fun _ _ hg => MemType.unshared hg) h

end Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode
