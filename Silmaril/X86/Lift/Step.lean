module

public import Silmaril.X86.Lift.Transcript
public import Silmaril.X86.Ext.SymExec

/-!
# Stepping from a transcription

A checked transcription (`Transcript.Verified`, or any `Region.decode? = some
listing`) is the single source of the decode facts a symbolic execution needs.
This module turns it into the two side conditions of `Ext.step_of_loaded` /
`Ext.stepOpt_of_loaded`, once, generically:

* `Region.decode?_slice`: each listed instruction is what `Ext.decode` reads
  from its slice of the bytes, and the slice fits.
* `stepOpt_of_listing`: a non-`ret` listed instruction at RIP retires with the
  effect `exec` gives it.

Per-instruction decode theorems in an execution proof (one closed `decide`
over a byte slice per occurrence) become lookups into the listing.

It also proves that decoding is compositional (`decodeFrom_append`) and that
fuel is monotone (`decodeFrom_mono`). With them, a listing of the *unrelocated*
bytes transfers to the relocated image at every layout, provided the patched
instruction is re-encoded canonically (`decodeFrom_splice`): the relocation
changes one instruction's operand and nothing else.
-/

@[expose] public section

namespace Silmaril.X86.Lift

open Silmaril.X86 (Word Byte State MState)
open Silmaril.Process (Memory)
open Silmaril.X86.Decompile
open Silmaril.X86.Ext (Loaded stepOpt step exec)

/-- `decide +kernel` evaluates `Except.toOption` but gets stuck in Batteries'
`DecidableEq (Except ε α)`; this moves a kernel-decided `toOption` equation
back to `Except`. -/
theorem ok_of_toOption {ε α : Type} {e : Except ε α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e <;> simp_all [Except.toOption]

/-! ## Decoding is compositional -/

/-- More fuel never changes a successful decode. -/
theorem decodeFrom_mono : ∀ {f g : Nat} {a : Nat} {bytes : List Byte} {ds : List Decoded},
    f ≤ g → decodeFrom f a bytes = .ok ds → decodeFrom g a bytes = .ok ds
  | _, _, _, [], _, _, h => by
    cases ‹Nat› <;> simp_all [decodeFrom]
  | 0, _, _, _ :: _, _, _, h => by simp [decodeFrom] at h
  | f + 1, g, a, b :: bs, ds, hle, h => by
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    simp only [decodeFrom] at h ⊢
    split at h
    · cases h
    · rename_i i n hdec
      split at h
      · cases h
      · rename_i hn
        simp only [hn] at h ⊢
        cases hrest : decodeFrom f (a + n) ((b :: bs).drop n) with
        | error e => rw [hrest] at h; cases h
        | ok rest =>
          rw [hrest] at h
          rw [decodeFrom_mono (by omega) hrest]
          exact h

/-- Decoding `xs ++ ys` is decoding `xs`, then `ys` from where `xs` ended,
when `xs` decodes on its own. `Ext.decode` reads only the canonical encoding
it returns (`decode_sound`, `decode_encode_append`), so what follows cannot
change it. -/
theorem decodeFrom_append : ∀ (f : Nat) {g a : Nat} {xs ys : List Byte} {ds₁ ds₂ : List Decoded},
    decodeFrom f a xs = .ok ds₁ → decodeFrom g (a + xs.length) ys = .ok ds₂ →
    decodeFrom (f + g) a (xs ++ ys) = .ok (ds₁ ++ ds₂)
  | f, g, a, [], ys, ds₁, ds₂, h₁, h₂ => by
    have : ds₁ = [] := by cases f <;> simp_all [decodeFrom]
    subst this
    simpa using decodeFrom_mono (by omega) h₂
  | 0, _, _, _ :: _, _, _, _, h₁, _ => by simp [decodeFrom] at h₁
  | f + 1, g, a, x :: xs, ys, ds₁, ds₂, h₁, h₂ => by
    simp only [decodeFrom] at h₁
    split at h₁
    · cases h₁
    · rename_i i n hdec
      split at h₁
      · cases h₁
      · rename_i hn
        cases hrest : decodeFrom f (a + n) ((x :: xs).drop n) with
        | error e => rw [hrest] at h₁; cases h₁
        | ok rest =>
          rw [hrest] at h₁
          simp only [Except.map] at h₁
          cases h₁
          obtain ⟨hlen, hsplit⟩ := Ext.decode_sound hdec
          have hnle : n ≤ (x :: xs).length := by
            have := congrArg List.length hsplit
            simp only [List.length_append] at this
            omega
          have hdec' : Ext.decode ((x :: xs) ++ ys) = some (i, n) := by
            rw [hsplit, List.append_assoc, Ext.decode_encode_append, ← hlen]
          rw [show f + 1 + g = (f + g) + 1 by omega, List.cons_append]
          simp only [decodeFrom]
          rw [← List.cons_append, hdec']
          simp only [hn, ↓reduceIte, List.drop_append_of_le_length hnle]
          have h₂' : decodeFrom g (a + n + ((x :: xs).drop n).length) ys = .ok ds₂ := by
            rw [List.length_drop, show a + n + ((x :: xs).length - n) = a + (x :: xs).length by
              omega]
            exact h₂
          rw [decodeFrom_append f hrest h₂']
          rfl

/-- **Patching one instruction.** If `pre ++ encode i ++ post` decodes to
`ds₁ ++ ⟨a + pre.length, i, n⟩ :: ds₂` because `pre` and `post` decode on their
own, then so does `pre ++ encode i' ++ post` with `i'` in place of `i`, for any
`i'` whose canonical encoding is equally long. A relocation that rewrites a
`disp32` is this, with `i'` the instruction carrying the patched displacement. -/
theorem decodeFrom_splice {f g : Nat} {a : Nat} {pre post : List Byte}
    {ds₁ ds₂ : List Decoded} (i' : Ext.Instr)
    (hpre : decodeFrom f a pre = .ok ds₁)
    (hpost : decodeFrom g (a + pre.length + (Ext.encode i').length) post = .ok ds₂) :
    decodeFrom (f + (1 + g)) a (pre ++ (Ext.encode i' ++ post)) =
      .ok (ds₁ ++ ⟨a + pre.length, i', (Ext.encode i').length⟩ :: ds₂) := by
  apply decodeFrom_append f hpre
  rw [Nat.add_comm 1 g]
  cases hb : Ext.encode i' with
  | nil =>
    have := (Ext.decode_length (Ext.decode_encode i')).2.1
    rw [hb] at this; simp at this
  | cons b bs =>
    simp only [decodeFrom, List.cons_append]
    rw [← List.cons_append, ← hb, Ext.decode_encode_append]
    have hpos : (Ext.encode i').length ≠ 0 := by rw [hb]; simp
    simp only [hpos, ↓reduceIte, List.drop_left, hpost]
    rfl

/-! ## Decode facts from a listing -/

/-- Each listed instruction is what `Ext.decode` reads from its own slice of
the region's bytes, and that slice lies inside the region. These are exactly
the side conditions `Ext.step_of_loaded` asks for. -/
theorem Region.decode?_slice {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) {d : Decoded} (hd : d ∈ ds) :
    Ext.decode ((r.bytes.drop (d.addr - r.base)).take d.size) = some (d.instr, d.size) ∧
      d.addr - r.base + d.size ≤ r.bytes.length := by
  obtain ⟨hlo, hhi⟩ := Region.decode?_within h d hd
  refine ⟨?_, by omega⟩
  rw [Region.decode?_bytes h d hd, Region.decode?_size h d hd]
  exact Ext.decode_encode _

/-- A listed non-`ret` instruction at RIP retires with `exec`'s effect. The
image is loaded at `base`, and listed addresses are offsets from `r.base`. -/
theorem stepOpt_of_listing {exit base : Word} {r : Region} {fuel : Nat} {ds : List Decoded}
    {m : MState} {d : Decoded} {core : State} {memory : Memory}
    (h : r.decode? fuel = some ds) (hd : d ∈ ds)
    (loaded : Loaded m.memory base r.bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 (d.addr - r.base))
    (not_ret : d.instr ≠ .ret)
    (executed : exec d.instr m.core m.memory = .ok core memory) :
    stepOpt exit m = some ⟨core, memory⟩ :=
  Ext.stepOpt_of_loaded loaded at_offset (Region.decode?_slice h hd).2
    (Region.decode?_slice h hd).1 not_ret executed

/-- The same through `at?`: the lookup a proof performs at a concrete
address. -/
theorem decode_of_at {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) {addr : Nat} {d : Decoded} (hat : at? ds addr = some d) :
    Ext.decode ((r.bytes.drop (d.addr - r.base)).take d.size) = some (d.instr, d.size) :=
  (Region.decode?_slice h (at?_eq_some hat).1).1

/-- A verified transcription's decode, as `decode?`. -/
theorem Transcript.Verified.slice {t : Transcript} (h : t.Verified) {d : Decoded}
    (hd : d ∈ t.listing) :
    Ext.decode ((t.region.bytes.drop (d.addr - t.region.base)).take d.size) =
      some (d.instr, d.size) :=
  (Region.decode?_slice h.decode? hd).1

end Silmaril.X86.Lift
