module

public import Silmaril.Containers.Posix.Defs
import Silmaril.Proofs.Containers.Posix.Basic

public section
namespace Silmaril.Containers.Posix

theorem lookup_advance (s : State) (fd id count : Nat) (h : s.descriptors fd = some id) :
    (s.advance id count).lookup fd =
      (s.lookup fd).map (fun d => { d with offset := d.offset + count }) :=
  Silmaril.Proofs.Containers.Posix.lookup_advance s fd id count h

theorem accepted_length (bs : Bytes) (reply : WriteReply bs) :
    (acceptedBytes bs reply).length ≤ bs.length :=
  Silmaril.Proofs.Containers.Posix.accepted_length bs reply

end Silmaril.Containers.Posix
