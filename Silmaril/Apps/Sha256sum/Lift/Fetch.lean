module

public import Silmaril.Apps.Sha256sum.X86Sys8
public import Silmaril.Apps.Sha256sum.Binary.Load

/-! # Fetching from `sha256sum-min`'s text: the step of the binary at a known address

The executable segment of `sha256sum-min` (`Binary.Image.seg1`, 0x401000 … 0x4053cb) is
read-only. `Code m` says the memory `m` holds it, fetchable, at its address. Under `Code`,
the ISA step at an address `a` depends only on the fixed 15-byte **window** `window a` of
the image (`step_of_decode`, `step_of_syscall`): the fetch, the decode and the `syscall`
test are computations on a literal byte list, which the kernel evaluates. This is what lets a
symbolic executor treat the binary as a *program* (address ↦ instruction) rather than as
bytes in a memory, with no per-instruction proof: `Listing.Ok` checks a whole lifted listing
by one `decide`.

`code_of_mapped` gives `Code` at launch (from `Image.Mapped` and the absence of a writable
mapping over the text); `Lift.Ro` keeps it across every step, with no address arithmetic.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Lift

open Silmaril.Process (Memory Byte)
open Silmaril.Process.CLI
open Silmaril.X86 (Word fetchWindow maxInstrLength)

def textBase : Nat := 0x401000
def textSize : Nat := 0x43cb
def text : List Byte := Binary.Image.seg1.contents

theorem text_length : text.length = textSize := by decide +kernel

/-- The text is in memory, fetchable, at its address, and no byte of it is writable (so no
store and no `read` reply can change it: `Code.of_ro`). -/
structure Code (m : Memory) : Prop where
  textAt : m.fetchBytes textBase textSize = some text
  ro : ∀ a, textBase ≤ a → a < textBase + textSize → m.permits .write a = false

theorem code_of_mapped {m : Memory} (h : Binary.Image.image.Mapped m)
    (hro : ∀ a, textBase ≤ a → a < textBase + textSize → m.permits .write a = false) :
    Code m := by
  refine ⟨?_, hro⟩
  have := Binary.readWith_segment h Binary.seg1_mem Binary.Image.image_wf (acc := .execute)
    (by decide) 0 textSize (by decide) (by decide)
  unfold Memory.fetchBytes
  have e : (text.drop 0).take textSize = text := by
    rw [List.drop_zero]; exact List.take_of_length_le (Nat.le_of_eq text_length)
  exact this.trans (congrArg some e)

/-- The 15 bytes the decoder sees at `a`. -/
def window (a : Nat) : List Byte := (text.drop (a - textBase)).take maxInstrLength

theorem Code.fetch {m : Memory} (h : Code m) {a n : Nat} (ha : textBase ≤ a)
    (hlen : a + n ≤ textBase + textSize) (hn : 0 < n) :
    m.fetchBytes a n = some ((text.drop (a - textBase)).take n) := by
  have := Memory.readWith_sub_range h.textAt (offset := a - textBase) (len := n) (by omega) (by omega)
  rwa [show textBase + (a - textBase) = a by omega] at this

/-- An address whose whole window lies in the text. -/
def InText (a : Nat) : Prop := textBase ≤ a ∧ a + maxInstrLength ≤ textBase + textSize

instance (a : Nat) : Decidable (InText a) := inferInstanceAs (Decidable (_ ∧ _))

theorem window_length {a : Nat} (ha : InText a) : (window a).length = maxInstrLength := by
  unfold window InText at *
  simp only [List.length_take, List.length_drop, text_length]
  unfold maxInstrLength at *; omega

theorem Code.fetchWindow {m : Memory} (h : Code m) {a : Nat} (ha : InText a) :
    fetchWindow m maxInstrLength a = window a := by
  have hf := h.fetch ha.1 ha.2 (by unfold maxInstrLength; omega)
  have hp := X86.fetchBytes_prefix_fetchWindow hf (Nat.le_refl _)
  have hl := X86.fetchWindow_length_le m maxInstrLength a
  have hl' := hp.length_le
  change window a <+: _ at hp
  change (window a).length ≤ _ at hl'
  exact (hp.eq_of_length (by rw [window_length ha] at hl' ⊢; omega)).symm

theorem Code.syscall_test {m : Memory} (h : Code m) {a : Nat} (ha : InText a) :
    m.fetchBytes a 2 = some ((window a).take 2) := by
  rw [h.fetch ha.1 (by have := ha.2; unfold maxInstrLength at this; omega) (by omega)]
  simp [window, List.take_take, maxInstrLength]

theorem Code.permitted {m : Memory} (h : Code m) {a n : Nat} (ha : InText a) (hn : 0 < n)
    (hn' : n ≤ maxInstrLength) : m.Permitted .execute a n :=
  Memory.readWith_permitted (h.fetch ha.1 (by have := ha.2; omega) hn)

/-! ## The step at an address -/

theorem decode8_new {w : List Byte} {i : X86.Ext8.New} {n : Nat}
    (h : X86.Ext8.decode w = some (.new i, n)) :
    X86.Ext.decode w = none ∧ X86.Ext8.decodeNew w = some (i, n) := by
  unfold X86.Ext8.decode at h
  split at h
  · simp at h
  · rename_i hn
    refine ⟨hn, ?_⟩
    cases e : X86.Ext8.decodeNew w with
    | none => simp [e] at h
    | some p => obtain ⟨i', n'⟩ := p; simp [e] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem Code.ext_fetch_base {m : Memory} (h : Code m) {a : Nat} (ha : InText a)
    {i : X86.Ext.Instr} {n : Nat} (hdec : X86.Ext.decode (window a) = some (i, n))
    (hn : 0 < n) (hn' : n ≤ maxInstrLength) : X86.Ext.fetch m a = .decoded i n := by
  unfold X86.Ext.fetch
  rw [h.fetchWindow ha, hdec]
  simp [h.permitted ha hn hn']

theorem Code.ext_fetch_none {m : Memory} (h : Code m) {a : Nat} (ha : InText a)
    (hdec : X86.Ext.decode (window a) = none) : X86.Ext.fetch m a = .undecodable := by
  unfold X86.Ext.fetch
  rw [h.fetchWindow ha]
  have hl := window_length ha
  generalize window a = w at hdec hl ⊢
  rw [hdec]
  generalize X86.Ext.parseRaw w = r
  cases r
  · rfl
  · show (if w.length < maxInstrLength then _ else _) = _
    rw [hl]; rfl
  · rfl

/-- **The ISA step at a text address** is the execution of the instruction decoded from the
window there (unless the window starts with `syscall`). -/
theorem Code.step {m : Memory} (h : Code m) {c : X86Sys.Core} {a : Nat} (ha : InText a)
    (hrip : c.rip.toNat = a) (hsys : (window a).take 2 ≠ X86Linux.syscallBytes)
    {i : X86.Ext8.Instr} {n : Nat} (hdec : X86.Ext8.decode (window a) = some (i, n))
    (hn : 0 < n) (hn' : n ≤ maxInstrLength) :
    X86Linux8.step c m = X86Linux.execResult (X86.Ext8.exec i c m n) := by
  unfold X86Linux8.step
  rw [hrip, h.syscall_test ha]
  simp only [Option.some.injEq, hsys, ite_false]
  cases i with
  | base i =>
    have hb := X86.Ext8.decode_base_iff.mp hdec
    have hf := h.ext_fetch_base ha hb hn hn'
    rw [X86.Ext8.fetch_of_ne_undecodable (by rw [hf]; simp), hf]
    rfl
  | new i =>
    obtain ⟨hnone, hnew⟩ := decode8_new hdec
    unfold X86.Ext8.fetch
    rw [h.ext_fetch_none ha hnone]
    simp only
    rw [h.fetchWindow ha, hnew]
    simp [h.permitted ha hn hn', X86.Ext8.exec]

/-- The ISA step at the `syscall` instruction. -/
theorem Code.step_syscall {m : Memory} (h : Code m) {c : X86Sys.Core} {a : Nat} (ha : InText a)
    (hrip : c.rip.toNat = a) (hsys : (window a).take 2 = X86Linux.syscallBytes) :
    X86Linux8.step c m = .syscall { c with rip := c.rip + 2 } := by
  unfold X86Linux8.step
  rw [hrip, h.syscall_test ha, hsys]
  simp

end Silmaril.Apps.Sha256sum.Lift
