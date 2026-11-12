module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs

/-!
# Round 7, memory SIMD: `stepRelOnly` on two halves of a chunk

The kernel checks of `stepRelOnly` run on chunks of the fixed wasm-3.0 script. Round 4 split the
slower chunks in two, so that each module stays under the time budget under parallel load;
`stepRelOnly_halves` puts the halves back together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

open Silmaril.SpecTec
open Round7.Script (items defsItems_append)

/-- `stepRelOnly` of a chunk of `n + n` definitions from its two halves. -/
theorem stepRelOnly_halves (s : IL.Script) (i n : Nat)
    (h₁ : stepRelOnly ((s.drop i).take n) = true)
    (h₂ : stepRelOnly ((s.drop (i + n)).take n) = true) :
    stepRelOnly ((s.drop i).take (n + n)) = true := by
  have hs : (s.drop i).take (n + n) = (s.drop i).take n ++ (s.drop (i + n)).take n := by
    rw [List.take_add, List.drop_drop]
  rw [hs]
  simp only [stepRelOnly, items, defsItems_append, List.all_append, Bool.and_eq_true]
  exact ⟨h₁, h₂⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
