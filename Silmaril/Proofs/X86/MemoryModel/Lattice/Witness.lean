module

public import Silmaril.X86.MemoryModel.Lattice.Witness.Defs
public import Silmaril.X86.MemoryModel.Lattice.Thms

/-!
# Proofs: the Boolean verdict row is exact

`verdict_of_row`: when `hb` and `hbL` are closed, `Exec.row` gives the verdicts of `sc`, `tso`,
`ra`, `xl`, `cf` and `cfPlain`.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Lattice.Witness.Proofs

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Lattice

theorem verdict_of_row (x : Exec) (hc : x.hbClosedB = true) (hcL : x.hbLClosedB = true) :
    Verdict x x.row := by
  have hu := unsplitB_iff x
  have hd := drfB_iff hc
  have hdL := drfLB_iff hcL
  refine ⟨⟨fun h => decide_eq_true h, of_decide_eq_true⟩,
    ⟨fun h => decide_eq_true h, of_decide_eq_true⟩, ra_iff_check hc,
    ⟨fun h => decide_eq_true h, of_decide_eq_true⟩, ?_, ?_⟩
  · show (x.Unsplit → x.DrfL → x.Sc) ↔ (decide x.Sc || !x.unsplitB || !x.drfLB) = true
    cases hb1 : x.unsplitB <;> cases hb2 : x.drfLB <;> by_cases hs : x.Sc <;> simp_all
  · show (x.Unsplit → x.Drf → x.Sc) ↔ (decide x.Sc || !x.unsplitB || !x.drfB) = true
    cases hb1 : x.unsplitB <;> cases hb2 : x.drfB <;> by_cases hs : x.Sc <;> simp_all

end Silmaril.X86.MemoryModel.Lattice.Witness.Proofs
