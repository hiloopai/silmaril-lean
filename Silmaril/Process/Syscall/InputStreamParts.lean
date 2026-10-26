module

public import Silmaril.Process.Syscall.InputStreamSlices

/-! # Immutable input matches after a consumed prefix -/

@[expose] public section

namespace Silmaril.Process.Syscall

/-- The suffix of a matched input starts after the exact prefix extent. -/
theorem InputStream.Matches.right {stream : InputStream} {cursor : Nat}
    {first second : List Byte} (contents : stream.Matches cursor (first ++ second)) :
    stream.Matches (cursor + first.length) second := by
  intro index bound
  have within : first.length + index < (first ++ second).length := by
    simp only [List.length_append]; omega
  have byte := contents (first.length + index) within
  have nth : (first ++ second)[first.length + index]'within = second[index] := by
    rw [List.getElem_append_right (by omega : first.length ≤ first.length + index)]
    simp only [Nat.add_sub_cancel_left]
  simpa only [nth, Nat.add_assoc] using byte

end Silmaril.Process.Syscall
