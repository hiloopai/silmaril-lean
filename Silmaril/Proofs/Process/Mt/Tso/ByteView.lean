module

public import Silmaril.Process.Mt.Tso.ByteView.Defs

public section

namespace Silmaril.Proofs.Process.Mt.Tso.ByteView

open Silmaril.Process (ByteMemory Memory)
open Silmaril.Process.Mt (TsoS BufEntry overlay tso)
open Silmaril.X86.MemoryModel.Tso

open Silmaril.Process.Mt.Tso.ByteView (byteState)

private theorem install_as_write (memory : ByteMemory) (base : Nat) (bytes : List Byte)
    (address : Nat) :
    (Memory.install memory base bytes).get? address =
      writeMem (fun a => memory.get? a) base bytes address := by
  by_cases low : base ≤ address
  · by_cases inSpan : address - base < bytes.length
    · unfold writeMem entryByte
      rw [ite_eq_left low, List.getElem?_eq_getElem inSpan]
      have installed := Memory.install_get memory base bytes (address - base) inSpan
      rwa [Nat.add_sub_of_le low] at installed
    · rw [Memory.install_outside memory base bytes address (.inr (by omega))]
      simp [writeMem, entryByte, low, List.getElem?_eq_none (by omega : bytes.length ≤ address - base)]
  · rw [Memory.install_outside memory base bytes address (.inl (by omega))]
    simp [writeMem, entryByte, low]

private theorem overlay_byte (memory : Memory) (buffer : List BufEntry) (address : Nat) :
    (overlay memory buffer).bytes.get? address =
      (readBufByte address buffer).or (memory.bytes.get? address) := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨base, bytes⟩ := entry
    change (overlay { memory with bytes := Memory.install memory.bytes base bytes } rest).bytes.get?
      address = _
    rw [ih, install_as_write]
    simp [writeMem, readBufByte, Option.or_assoc]

/-- Backing bytes of the real process overlay are the byte FIFO issuer view. -/
theorem view_projects (s : TsoS) (tid address : Nat) :
    (tso.view s tid).bytes.get? address = viewMem (byteState s) tid address :=
  overlay_byte s.mem (s.buf tid) address

/-- Propagation installs the same oldest entry in both models and preserves regions. -/
theorem silent_projects {s t : TsoS} (edge : tso.silent s t) :
    XFlush (byteState s) (byteState t) ∧ t.mem.regions = s.mem.regions := by
  obtain ⟨tid, ⟨base, bytes⟩, rest, oldest, rfl⟩ := edge
  constructor
  · have writes : (fun address => (Memory.install s.mem.bytes base bytes).get? address) =
        writeMem (byteState s).memory base bytes :=
      funext (install_as_write s.mem.bytes base bytes)
    have popped : Silmaril.Process.Mt.upd s.buf tid rest = Function.update (byteState s).buffer tid rest := by
      funext actor
      by_cases same : actor = tid
      · subst actor
        simp [Silmaril.Process.Mt.upd, byteState]
      · simp [Silmaril.Process.Mt.upd, byteState, same]
    change XFlush (byteState s)
      ⟨(fun address => (Memory.install s.mem.bytes base bytes).get? address),
        Silmaril.Process.Mt.upd s.buf tid rest⟩
    rw [writes, popped]
    exact .head _ tid base bytes rest oldest
  · rfl

theorem silent_path_projects {s t : TsoS} (path : Relation.ReflTransGen tso.silent s t) :
    XFlushes (byteState s) (byteState t) ∧ t.mem.regions = s.mem.regions := by
  induction path with
  | refl => exact ⟨.refl, rfl⟩
  | tail _ edge previous =>
    have ⟨flush, regions⟩ := silent_projects edge
    exact ⟨.tail previous.1 flush, regions.trans previous.2⟩

end Silmaril.Proofs.Process.Mt.Tso.ByteView
