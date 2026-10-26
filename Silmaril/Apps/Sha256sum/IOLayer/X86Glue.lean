module

public import Silmaril.Apps.Sha256sum.X86Sys

/-! # The I/O layer at the `syscall` boundary of an x86-64 binary

Status: **VERIFIED** (no `sorry`, no new axioms).

What a simulation of a buffered binary (`X86Sys.x86Machine`) by the I/O layer
(`IOLayer.lb`, `IOLayer.rb`) needs at each system call, independently of the binary:

* `decode_write` (**write requests**): if the bytes at `rsi` are the layer's pending bytes,
  the binary's `write` request *is* the layer's request (`Call.write fd rest`). For
  `sha256sum-min` the bytes at `rsi` are `obuf[olen - |rest|, olen)`.
* `resume_read` (**read replies**): after a `read` reply `data b`, the buffer at `rsi`
  holds exactly `b` (and `rax` its length); the rest of memory is unchanged. For
  `sha256sum-min` this is `iobuf` (hashing) and `rd.b` (`--check`), whose unread part is the
  layer's `unread`.
* `raxOf_*`: the sign of `rax`, which is all the binary's `write_all`/`rd_fill` loops test.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.X86Sys

open Silmaril.Apps.Sha256sum
open Silmaril.Apps.Sha256sum.Sys
open Silmaril.Process (Byte Memory)

@[simp] theorem toU8_ofU8 (b : UInt8) : toU8 (ofU8 b) = b := by
  simp only [toU8, ofU8]
  apply UInt8.toNat_inj.mp
  simp

@[simp] theorem map_toU8_ofU8 (bs : Bytes) : (bs.map ofU8).map toU8 = bs := by
  simp [List.map_map, Function.comp_def]

/-- **Write requests.** A `write` whose buffer holds `bs` is the request `write fd bs`. -/
theorem decode_write {c : Core} {m : Memory} {bs : Bytes} (hnr : (c.read .rax).toNat = 1)
    (hbuf : m.readBytes (c.read .rsi).toNat (c.read .rdx).toNat = some (bs.map ofU8)) :
    decode c m = some (.call (.write (fd32 (c.read .rdi)) bs)) := by
  have hid : (bs.map ofU8).map toU8 = bs := map_toU8_ofU8 bs
  simp only [decode, hnr, hbuf, Option.map_some, hid]
  simp

/-- **Read replies.** After `read` returns `data b` into a writable and readable buffer at
`rsi`, the buffer holds `b`, `rax` is its length, and nothing outside the buffer changed. -/
theorem resume_read {r11Of : Core → Silmaril.X86.Word} {s : XState} {c : Core} {fd n : Nat}
    {b : Bytes} (hw : s.memory.Permitted .write (c.read .rsi).toNat b.length)
    (hr : s.memory.Permitted .read (c.read .rsi).toNat b.length) :
    ∃ m', resume r11Of s c (.read fd n) (.data b) =
        { s with core := returnCore r11Of c (BitVec.ofNat 64 b.length), memory := m' } ∧
      m'.readBytes (c.read .rsi).toNat b.length = some (b.map ofU8) ∧
      Memory.WritesOnly s.memory m' (c.read .rsi).toNat b.length := by
  have hw' : s.memory.Permitted .write (c.read .rsi).toNat (b.map ofU8).length := by simpa using hw
  have hchk : s.memory.checkSpan .write (c.read .rsi).toNat (b.map ofU8).length = true := hw'
  obtain ⟨m', hm'⟩ : ∃ m', s.memory.writeBytes (c.read .rsi).toNat (b.map ofU8) = some m' :=
    ⟨_, by unfold Memory.writeBytes; rw [hchk]; rfl⟩
  refine ⟨m', by simp [resume, hm', raxOf], ?_, ?_⟩
  · have hregions : m'.regions = s.memory.regions := by
      unfold Memory.writeBytes at hm'; split at hm' <;> simp_all; cases hm'; rfl
    have hperm : m'.Permitted .read (c.read .rsi).toNat (b.map ofU8).length := by
      have : m'.checkSpan .read (c.read .rsi).toNat (b.map ofU8).length =
          s.memory.checkSpan .read (c.read .rsi).toNat (b.map ofU8).length := by
        simp [Memory.checkSpan, Memory.permits, hregions]
      show m'.checkSpan .read _ _ = true
      rw [this, List.length_map]; exact hr
    have := Memory.readWith_eq m' .read (c.read .rsi).toNat (b.map ofU8) hperm
      (fun i hi => Memory.writeBytes_get hm' i hi)
    simpa [Memory.readBytes] using this
  · simpa using Memory.writeBytes_writesOnly hm'

/-- A successful reply leaves the sign bit of `rax` clear. -/
theorem raxOf_ok_msb {n : Nat} (h : n < 2 ^ 63) : (raxOf (.ok n)).msb = false := by
  simp only [raxOf, BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  have : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  simp only [this, decide_eq_false_iff_not, not_le]
  omega

/-- An error reply sets the sign bit of `rax` (`-errno`). -/
theorem raxOf_err_msb (e : Errno) : (raxOf (.err e)).msb = true := by
  cases e <;> decide

end Silmaril.Apps.Sha256sum.X86Sys
