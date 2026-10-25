module

public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.DecodeInstructions
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode

open Core Core.Decode
open Wasm.Extensions.AtomicMemory

theorem ofOpcode?_sound {n : Nat} {op : Access} (h : Access.ofOpcode? n = some op) : op.opcode = n := by
  have hcode := List.find?_some (show Access.all.find? (fun op => op.opcode == n) = some op from h)
  exact beq_iff_eq.mp hcode

theorem readAtomic_sound :
    Sound (fun pre i => Atomic Forms.all ([0xfe] ++ pre) i) readAtomic := by
  intro c a c' h
  unfold readAtomic at h
  obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
  obtain ⟨hbn, pn, hrn, hgn⟩ := readU_sound 32 hn
  split at h
  · obtain ⟨b, cb, hb, h⟩ := run_bind_ok h
    obtain ⟨hbb, hrb⟩ := readByte_ok hb
    split at h
    · rename_i hz
      have hz : b = 0 := by simpa using hz
      subst b
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨hbb.trans hbn, pn ++ [0], by simp [hrn, hrb], .fence hgn⟩
    · obtain ⟨_, _, he, _⟩ := run_bind_ok h
      exact (decodeError_ok he).elim
  · obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨hbn, pn, hrn, .pause hgn⟩
  · split at h
    · exact (decodeError_ok h).elim
    · rename_i op ho
      obtain ⟨⟨m, arg⟩, cm, hm, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbm, pm, hrm, hgm⟩ := readMemArg_sound hm
      refine ⟨hbm.trans hbn, pn ++ pm, by simp [hrn, hrm], ?_⟩
      simpa only [List.append_assoc] using Atomic.access ((ofOpcode?_sound ho).symm ▸ hgn) hgm

theorem readLeaf_sound (op : UInt8) :
    Sound (fun pre i => Leaf Forms.all ([op] ++ pre) i) (readLeaf op.toNat) := by
  intro c a c' h
  unfold readLeaf at h
  split at h
  · exact (decodeError_ok h).elim
  · rename_i hcontrol
    split at h
    · rename_i he
      have he : op = 0xfe := UInt8.toNat_inj.mp (by simpa using he)
      subst op
      exact sound_map readAtomic_sound Wasm.Extensions.AtomicMemory.Leaf.atomic
        (fun _ _ hg => Leaf.atomic hg) h
    · rename_i hn
      exact sound_map (Core.Decode.readPlain_sound op) Wasm.Extensions.AtomicMemory.Leaf.core
        (fun _ _ hg => Leaf.core (by simp_all) hg) h

theorem readExpr_sound : Sound (Expr Forms.all) readExpr :=
  Structured.Decode.readExpr_sound readLeaf readLeaf_sound

end Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode
