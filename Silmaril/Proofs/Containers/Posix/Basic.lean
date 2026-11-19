module

public import Silmaril.Containers.Posix.Defs

public section
namespace Silmaril.Proofs.Containers.Posix
open Silmaril.Containers.Posix

theorem lookup_advance (s : State) (fd id count : Nat) (h : s.descriptors fd = some id) :
    (s.advance id count).lookup fd =
      (s.lookup fd).map (fun d => { d with offset := d.offset + count }) := by
  simp [State.lookup, State.advance, h]

theorem accepted_length (bs : Bytes) (reply : WriteReply bs) :
    (acceptedBytes bs reply).length ≤ bs.length := by
  cases reply with
  | error _ => simp [acceptedBytes]
  | accepted n hn => simpa [acceptedBytes, List.length_take, Nat.min_eq_left hn] using hn

end Silmaril.Proofs.Containers.Posix
