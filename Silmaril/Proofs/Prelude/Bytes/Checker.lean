module

public import Silmaril.Prelude.Bytes.Checker.Defs
public import Silmaril.Prelude.Bytes.Thms
import Silmaril.Proofs.Prelude.Bytes.Digits

/-! Proofs for `Silmaril.Prelude.Bytes.Checker.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Prelude.Bytes

open Silmaril.KBytes

theorem cstringCheck_sound (b : KBytes) (s : List UInt8) (h : cstringCheck b s = true) :
    CString b s := by
  simp only [cstringCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨hw, hl⟩, hs⟩, hr⟩ := h
  refine ⟨?_, fun c hc => hs c hc⟩
  have hlen := length_toList b hw
  rw [read_eq b 0 _ hw (by omega), List.drop_zero, List.take_of_length_le (by omega)] at hr
  exact leVal_inj (by simp; omega) hr

end Silmaril.Proofs.Prelude.Bytes
