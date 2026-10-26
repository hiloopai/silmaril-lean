module

public import Silmaril.Process.Syscall

/-! # Exact slices of immutable finite syscall input

The successful-read `Matches` relation bounds every returned chunk by the
available finite input and identifies its exact next bytes. No availability,
progress, syscall policy or finite bound on an arbitrary stream is asserted.
-/

@[expose] public section

namespace Silmaril.Process.Syscall

/-- A matched chunk at a valid finite-input cursor is exactly the available
slice of that length. The cursor premise also handles empty chunks correctly. -/
theorem InputStream.Matches.ofList_slice {message bytes : List Byte} {cursor : Nat}
    (matched : (InputStream.ofList message).Matches cursor bytes)
    (cursorBound : cursor ≤ message.length) :
    bytes.length ≤ message.length - cursor ∧
      bytes = (message.drop cursor).take bytes.length := by
  have fits : bytes.length ≤ message.length - cursor := by
    by_contra larger
    have byte := matched (message.length - cursor) (by omega)
    have endIndex : cursor + (message.length - cursor) = message.length := by omega
    simp only [InputStream.ofList_byteAt, endIndex, List.getElem?_length] at byte
    contradiction
  refine ⟨fits, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Nat.min_eq_left fits]
  · intro index left right
    have bound : cursor + index < message.length := by omega
    have byte := matched index left
    simp only [InputStream.ofList_byteAt, List.getElem?_eq_getElem bound] at byte
    simpa only [List.getElem_take, List.getElem_drop] using (Option.some.inj byte).symm

/-- The same bound in the cursor-update form used by streaming invariants. -/
theorem InputStream.Matches.ofList_cursor_bound {message bytes : List Byte} {cursor : Nat}
    (matched : (InputStream.ofList message).Matches cursor bytes)
    (cursorBound : cursor ≤ message.length) : cursor + bytes.length ≤ message.length := by
  have fits := (matched.ofList_slice cursorBound).1
  omega

end Silmaril.Process.Syscall
