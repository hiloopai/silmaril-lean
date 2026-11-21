module

public import Silmaril.Parse.DecodeGraph.KBytes.Defs
public import Silmaril.Prelude.Bytes.Thms

public section

namespace Silmaril.Parse.DecodeGraph.Proofs

theorem kbyte_eq_byte (bytes : KBytes) (valid : bytes.wf = true) (stop pos : Nat) :
    kbyte bytes stop pos = ByteParse.byte bytes.toByteArray stop pos := by
  by_cases window : pos < stop
  · by_cases inside : pos < bytes.toByteArray.size
    · have inList : pos < bytes.toList.length := inside
      simp [kbyte, ByteParse.byte, window, inside, bytes.get?_eq valid, List.getElem?_eq_getElem inList]
      rfl
    · simp [kbyte, ByteParse.byte, window, inside, bytes.get?_eq valid,
        List.getElem?_eq_none (show bytes.toList.length ≤ pos from Nat.le_of_not_gt inside)]
  · simp [kbyte, ByteParse.byte, window]

end Silmaril.Parse.DecodeGraph.Proofs
