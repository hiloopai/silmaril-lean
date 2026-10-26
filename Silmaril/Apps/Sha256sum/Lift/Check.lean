module

public import Silmaril.Apps.Sha256sum.Lift.Fetch
public import Silmaril.Apps.Sha256sum.Lift.Ro

/-! # Checking a lifted listing against the image, in one pass

A `Listing` is the decompiled program: address ↦ (`Ext8` instruction, length), proposed by
any untrusted lifter (here Lean's own decoder run by `#eval`, see
`scripts/sha256sum/gen_listing.py`). `Listing.check` walks the text **once** (each entry's
window is a `drop` of the previous entry's suffix, so the kernel never re-traverses the
17 KiB text from its start) and re-decodes every window with `Ext8.decode`. `Listing.sound`:
every entry of a checked listing is what `Code.step` needs.

`Code.of_ro`: the text survives every `RO` change of memory, i.e. every instruction
(`Ext.exec_ro`, `Ext8.exec8_ro`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Lift

open Silmaril.Process (Memory Byte)
open Silmaril.Process.CLI
open Silmaril.X86 (Word fetchWindow maxInstrLength)

abbrev Listing := List (Nat × X86.Ext8.Instr × Nat)

/-- An index register for a lifted memory operand. -/
def ix (r : X86.Reg) (scale : BitVec 2) (h : r ≠ .rsp := by decide) : X86.Ext.Index := ⟨r, scale, h⟩

/-- The per-window check. -/
def windowOk (w : List Byte) (i : X86.Ext8.Instr) (n : Nat) : Bool :=
  decide (w.length = maxInstrLength) && (w.take 2 != X86Linux.syscallBytes) &&
    decide (X86.Ext8.decode w = some (i, n)) && decide (0 < n) && decide (n ≤ maxInstrLength)

/-- Check sorted entries against `bs`, the text from address `pos` on. -/
def checkFrom : List Byte → Nat → Listing → Bool
  | _, _, [] => true
  | bs, pos, (a, i, n) :: rest =>
    decide (pos ≤ a) && windowOk ((bs.drop (a - pos)).take maxInstrLength) i n &&
      checkFrom (bs.drop (a - pos)) a rest

def Listing.check (L : Listing) : Bool := checkFrom text textBase L

/-- What `Code.step` needs at an address. -/
structure EntryOk (a : Nat) (i : X86.Ext8.Instr) (n : Nat) : Prop where
  inText : InText a
  notSyscall : (window a).take 2 ≠ X86Linux.syscallBytes
  decode : X86.Ext8.decode (window a) = some (i, n)
  pos : 0 < n
  le : n ≤ maxInstrLength

/-- `EntryOk` over an arbitrary byte list `T` in place of the text (so that no proof step can
unfold the 17 KiB literal). -/
structure EntryOkOf (T : List Byte) (a : Nat) (i : X86.Ext8.Instr) (n : Nat) : Prop where
  inText : InText a
  notSyscall : ((T.drop (a - textBase)).take maxInstrLength).take 2 ≠ X86Linux.syscallBytes
  decode : X86.Ext8.decode ((T.drop (a - textBase)).take maxInstrLength) = some (i, n)
  pos : 0 < n
  le : n ≤ maxInstrLength

theorem checkFrom_sound (T : List Byte) (hT : T.length = textSize) : ∀ (L : Listing) (pos : Nat),
    textBase ≤ pos → checkFrom (T.drop (pos - textBase)) pos L = true →
      ∀ e ∈ L, EntryOkOf T e.1 e.2.1 e.2.2
  | [], _, _, _, e, he => by simp at he
  | (a, i, n) :: rest, pos, hpos, h, e, he => by
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hle, hw⟩, hrest⟩ := h
    have hd : (T.drop (pos - textBase)).drop (a - pos) = T.drop (a - textBase) := by
      rw [List.drop_drop]
      have : a - pos + (pos - textBase) = a - textBase := by omega
      have h2 : pos - textBase + (a - pos) = a - textBase := by omega
      first | rw [this] | rw [h2]
    rw [hd] at hw hrest
    rcases List.mem_cons.mp he with rfl | he
    · simp only [windowOk, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hw
      obtain ⟨⟨⟨⟨hlen, hsys⟩, hdec⟩, hn⟩, hn'⟩ := hw
      refine ⟨⟨by omega, ?_⟩, hsys, hdec, hn, hn'⟩
      rw [List.length_take, List.length_drop, hT] at hlen
      unfold maxInstrLength at hlen ⊢
      omega
    · exact checkFrom_sound T hT rest a (by omega) hrest e he

theorem Listing.sound {L : Listing} (h : L.check = true) {a : Nat} {i : X86.Ext8.Instr} {n : Nat}
    (he : (a, i, n) ∈ L) : EntryOk a i n := by
  have := checkFrom_sound text text_length L textBase (Nat.le_refl _)
    (by rw [Nat.sub_self, List.drop_zero]; exact h) _ he
  exact ⟨this.1, this.2, this.3, this.4, this.5⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (a', b') :: rest, a, b, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      have : a = a' := by simpa [beq_iff_eq] using he
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem Listing.sound_lookup {L : Listing} (h : L.check = true) {a : Nat} {i : X86.Ext8.Instr}
    {n : Nat} (hl : L.lookup a = some (i, n)) : EntryOk a i n :=
  Listing.sound h (lookup_mem hl)

/-- Lookup in address-bounded chunks (shallow recursion, so `rfl` can evaluate it). -/
def lookupChunks : List (Nat × Listing) → Nat → Option (X86.Ext8.Instr × Nat)
  | [], _ => none
  | (b, p) :: rest, a => if a < b then p.lookup a else lookupChunks rest a

theorem lookupChunks_mem : ∀ {cs : List (Nat × Listing)} {a : Nat} {e : X86.Ext8.Instr × Nat},
    lookupChunks cs a = some e → (a, e) ∈ (cs.map Prod.snd).flatten
  | [], _, _, h => by simp [lookupChunks] at h
  | (b, p) :: rest, a, e, h => by
    simp only [lookupChunks] at h
    simp only [List.map_cons, List.flatten_cons, List.mem_append]
    split at h
    · exact .inl (lookup_mem h)
    · exact .inr (lookupChunks_mem h)

/-! ## The text survives every instruction -/

theorem Code.of_ro {m m' : Memory} (h : Code m) (hr : X86.Ext.RO m m') : Code m' := by
  refine ⟨?_, fun a h1 h2 => by rw [hr.permits]; exact h.ro a h1 h2⟩
  have e : m'.fetchBytes textBase textSize = m.fetchBytes textBase textSize := by
    unfold Memory.fetchBytes Memory.readWith
    have hcheck : m'.checkSpan .execute textBase textSize = m.checkSpan .execute textBase textSize := by
      unfold Memory.checkSpan; simp only [hr.permits]
    rw [hcheck, Memory.readBacking_congr (fun off hoff => hr.2 _ (h.ro _ (by omega) (by omega)))]
  rw [e]; exact h.textAt

end Silmaril.Apps.Sha256sum.Lift
