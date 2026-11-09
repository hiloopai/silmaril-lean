module

public import Silmaril.X86.Partition.Shard.Defs
public import Silmaril.X86.Partition.Thms
public import Silmaril.Proofs.X86.Partition.Sound

/-!
# The pieces of a sharded partition check compose to `check2`

Proofs for `Silmaril/X86/Partition/Shard/Thms.lean`. The chain is:

1. **Decoding** (`decodeAt_take`, `span_sound`): `decodeAt` reads at most `maxInstrLength`
   bytes, so a piece decoded from its own bytes plus bounded lookahead (`pieceBytes`) decodes
   the same way inside the whole region; `decodeFrom` over the region is the concatenation of
   the pieces' listings (`pieces_decode`), and that listing is a contiguous chain of
   instructions (`Chain`).
2. **Slots** (`slotOf_piece`): an instruction decoded in piece `j` lies in the slot that holds
   the piece, and `Proposal.slotOf` finds that slot because the layout tiles the region.
3. **Bitmaps** (`inBits_sound`): a bit of function `i`'s bitmap is the address of an
   instruction of `i`, by `coverOf` (the bit is inside a slot of `i`) and the piece check of the
   piece that holds that address (`addrBits` agrees with the bitmap there).
4. **The walk** (`walk_none_of`): every instruction passed `instrOk`, and each `edgeOk` implies
   the corresponding `Ctx.checkEdge`, using the chain to find the listed successor.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Partition.Shard

open Silmaril.X86.Partition Silmaril.X86.Partition.Shard Silmaril.Proofs.X86.Partition

open Silmaril.X86 (Byte maxInstrLength)
open Silmaril.X86.Decompile (Region Edge)

/-! ## `decodeAt` reads at most `maxInstrLength` bytes -/

theorem extDecode_take (bs : List Byte) :
    Silmaril.X86.Ext.decode bs = Silmaril.X86.Ext.decode (bs.take maxInstrLength) := by
  cases h : Silmaril.X86.Ext.decode bs with
  | some x =>
    obtain ⟨i, n⟩ := x
    have hl := (Silmaril.X86.Ext.decode_length h).2.2.1
    have h1 := Silmaril.X86.Ext.decode_take h
    have h2 := Silmaril.X86.Ext.decode_append ((bs.take maxInstrLength).drop n) h1
    have : bs.take n ++ (bs.take maxInstrLength).drop n = bs.take maxInstrLength := by
      have e : (bs.take maxInstrLength).take n = bs.take n := by
        rw [List.take_take]; congr 1; simp [maxInstrLength]; omega
      rw [← e, List.take_append_drop]
    rw [this] at h2
    exact h2.symm
  | none =>
    cases h' : Silmaril.X86.Ext.decode (bs.take maxInstrLength) with
    | none => rfl
    | some x =>
      obtain ⟨i, n⟩ := x
      have := Silmaril.X86.Ext.decode_append (bs.drop maxInstrLength) h'
      rw [List.take_append_drop, h] at this
      cases this

theorem decodeAt_take (bs : List Byte) : decodeAt bs = decodeAt (bs.take maxInstrLength) := by
  unfold decodeAt
  rw [extDecode_take bs]
  cases Silmaril.X86.Ext.decode (bs.take maxInstrLength) with
  | some x => rfl
  | none =>
    simp only
    cases h15 : Silmaril.X86.Ext8.decodeNew (bs.take maxInstrLength) with
    | some x =>
      obtain ⟨i, n⟩ := x
      have hle : n ≤ maxInstrLength := by
        have := Silmaril.X86.Ext8.decodeNew_le h15
        simp only [List.length_take] at this
        omega
      have hfull := Silmaril.X86.Ext8.decodeNew_append h15 (bs.drop maxInstrLength)
      rw [List.take_append_drop] at hfull
      rw [hfull]
      have e : (bs.take maxInstrLength).take n = bs.take n := by
        rw [List.take_take]; congr 1; omega
      simp only [e]
    | none =>
      cases hb : Silmaril.X86.Ext8.decodeNew bs with
      | none => rfl
      | some x =>
        obtain ⟨i, n⟩ := x
        simp only
        split
        · rename_i hc
          exfalso
          obtain ⟨-, hle, hn, -⟩ := hc
          have := Silmaril.X86.Ext8.decodeNew_append hn ((bs.take maxInstrLength).drop n)
          have e : bs.take n ++ (bs.take maxInstrLength).drop n = bs.take maxInstrLength := by
            have e' : (bs.take maxInstrLength).take n = bs.take n := by
              rw [List.take_take]; congr 1; omega
            rw [← e', List.take_append_drop]
          rw [e, h15] at this
          cases this
        · rfl

/-- `decodeAt` of a word followed by bytes depends only on the first `maxInstrLength` of
those bytes. -/
theorem decodeAt_append_congr {w X Y : List Byte}
    (h : X.take maxInstrLength = Y.take maxInstrLength) :
    decodeAt (w ++ X) = decodeAt (w ++ Y) := by
  rw [decodeAt_take (w ++ X), decodeAt_take (w ++ Y), List.take_append, List.take_append]
  congr 2
  have e : ∀ L : List Byte, L.take (maxInstrLength - w.length) =
      (L.take maxInstrLength).take (maxInstrLength - w.length) := by
    intro L; rw [List.take_take]; congr 1; omega
  rw [e X, e Y, h]

/-! ## Chains of instructions -/

/-- `ds` lists contiguous instructions from `a` to `b`. -/
inductive Chain : Nat → Nat → List D8 → Prop where
  | nil (a : Nat) : Chain a a []
  | cons {a b : Nat} {d : D8} {ds : List D8} (ha : d.addr = a) (hpos : 0 < d.size)
      (hrest : Chain (a + d.size) b ds) : Chain a b (d :: ds)

theorem Chain.le {a b : Nat} {ds : List D8} (h : Chain a b ds) : a ≤ b := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ hpos _ ih => omega

theorem Chain.mem {a b : Nat} {ds : List D8} (h : Chain a b ds) :
    ∀ d ∈ ds, a ≤ d.addr ∧ d.addr + d.size ≤ b ∧ 0 < d.size := by
  induction h with
  | nil => intro d hd; cases hd
  | cons ha hpos hrest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨by omega, by have := hrest.le; omega, hpos⟩
    · have := ih d hd
      omega

theorem Chain.append {a b c : Nat} {ds es : List D8} (h1 : Chain a b ds) (h2 : Chain b c es) :
    Chain a c (ds ++ es) := by
  induction h1 with
  | nil => exact h2
  | cons ha hpos _ ih => exact Chain.cons ha hpos (ih h2)

/-- The instruction after `d` in a chain starts where `d` stops; the last one stops at the
end. -/
theorem Chain.next {a b : Nat} {ds : List D8} (h : Chain a b ds) :
    ∀ (pre : List D8) (d : D8) (post : List D8), ds = pre ++ d :: post →
      (∀ d' ∈ post.head?, d'.addr = d.addr + d.size) ∧ (post = [] → d.addr + d.size = b) := by
  induction h with
  | nil => intro pre d post e; simp at e
  | @cons a b d0 ds ha hpos hrest ih =>
    intro pre d post e
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨?_, ?_⟩
      · intro d' hd'
        cases hrest with
        | nil => simp at hd'
        | cons ha' _ _ =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd'
          subst hd'
          omega
      · intro hp
        subst hp
        cases hrest
        omega
    | cons x pre =>
      simp only [List.cons_append, List.cons.injEq] at e
      exact ih pre d post e.2

/-- Addresses in a chain are distinct. -/
theorem Chain.addr_inj {a b : Nat} {ds : List D8} (h : Chain a b ds) :
    ∀ d ∈ ds, ∀ e ∈ ds, d.addr = e.addr → d = e := by
  induction h with
  | nil => intro d hd; cases hd
  | @cons a b d0 ds ha hpos hrest ih =>
    intro d hd e he hde
    have hm := hrest.mem
    rcases List.mem_cons.mp hd with h1 | h1 <;> rcases List.mem_cons.mp he with h2 | h2
    · rw [h1, h2]
    · have := hm e h2; subst h1; omega
    · have := hm d h1; subst h2; omega
    · exact ih d h1 e h2 hde

/-! ## Decoding a piece -/

theorem decodeSpan_stop (un : List (Nat × Nat)) (stop : Nat) :
    ∀ (f : Nat) (bs : List Byte), decodeSpan un stop f stop bs = .ok [] := by
  intro f bs
  cases f <;> cases bs <;> simp [decodeSpan]

theorem decodeSpan_le (un : List (Nat × Nat)) (stop : Nat) :
    ∀ (f a : Nat) (bs : List Byte) (ds : List D8), decodeSpan un stop f a bs = .ok ds → a ≤ stop := by
  intro f
  induction f with
  | zero =>
    intro a bs ds h
    simp only [decodeSpan] at h
    split at h
    · omega
    · cases h
  | succ f ih =>
    intro a bs ds h
    cases bs with
    | nil =>
      simp only [decodeSpan] at h
      split at h
      · omega
      · cases h
    | cons b t =>
      simp only [decodeSpan] at h
      split at h
      · omega
      · split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i n _ _ _
              cases hr : decodeSpan un stop f (a + n) ((b :: t).drop n) with
              | error e => rw [hr] at h; cases h
              | ok r =>
                have := ih _ _ _ hr
                omega
        · split at h
          · cases h
          · rename_i i n _
            split at h
            · cases h
            · rename_i hn0
              cases hr : decodeSpan un stop f (a + n) ((b :: t).drop n) with
              | error e => rw [hr] at h; cases h
              | ok r =>
                have := ih _ _ _ hr
                omega

/-! ## `decodeFrom` and fuel -/

theorem except_map_map {α β γ ε : Type} (e : Except ε α) (f : α → β) (g : β → γ) :
    (e.map f).map g = e.map (g ∘ f) := by
  cases e <;> rfl

theorem except_map_nil (e : Except Reject (List D8)) : e.map (fun x => [] ++ x) = e := by
  cases e <;> rfl

/-- `decodeFrom` does not depend on its fuel once the fuel covers the bytes. -/
theorem decodeFrom_fuel (un : List (Nat × Nat)) : ∀ (f g a : Nat) (bs : List Byte),
    bs.length ≤ f → bs.length ≤ g → decodeFrom un f a bs = decodeFrom un g a bs := by
  intro f
  induction f with
  | zero =>
    intro g a bs hf hg
    cases bs with
    | nil => cases g <;> simp [decodeFrom]
    | cons b t => simp at hf
  | succ f ih =>
    intro g a bs hf hg
    cases bs with
    | nil => cases g <;> simp [decodeFrom]
    | cons b t =>
      cases g with
      | zero => simp at hg
      | succ g =>
        have key : ∀ n, n ≠ 0 → decodeFrom un f (a + n) ((b :: t).drop n) =
            decodeFrom un g (a + n) ((b :: t).drop n) := by
          intro n hn
          apply ih <;> simp only [List.length_drop, List.length_cons] at hf hg ⊢ <;> omega
        simp only [decodeFrom]
        cases hl : un.lookup a with
        | some n =>
          simp only
          by_cases hc : n = 0 ∨ (b :: t).length < n
          · simp only [hc, ↓reduceIte]
          · have hn : n ≠ 0 := fun e => hc (Or.inl e)
            simp only [hc, ↓reduceIte, key n hn]
        | none =>
          simp only
          cases hd : decodeAt (b :: t) with
          | none => rfl
          | some x =>
            obtain ⟨i, n⟩ := x
            simp only
            by_cases hn : n = 0
            · simp only [hn, ↓reduceIte]
            · simp only [hn, ↓reduceIte, key n hn]

/-- **A piece decodes inside the region.** If piece bytes `w` followed by lookahead `X`
decode exactly to `stop`, then `decodeFrom` over `w` followed by any `Y` that agrees with `X`
on `maxInstrLength` bytes lists the same instructions, then continues at `stop`. -/
theorem span_sound (un : List (Nat × Nat)) (stop : Nat) :
    ∀ (f a : Nat) (w X Y : List Byte) (ds : List D8),
      decodeSpan un stop f a (w ++ X) = .ok ds → w.length = stop - a →
      X.take maxInstrLength = Y.take maxInstrLength →
      Chain a stop ds ∧ ∀ g, (w ++ Y).length ≤ g →
        decodeFrom un g a (w ++ Y) = (decodeFrom un Y.length stop Y).map (ds ++ ·) := by
  intro f
  induction f with
  | zero =>
    intro a w X Y ds h hw hxy
    simp only [decodeSpan] at h
    split at h
    · rename_i ha
      subst ha
      simp only [Except.ok.injEq] at h
      subst h
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw0
      refine ⟨Chain.nil _, fun g hg => ?_⟩
      rw [except_map_nil]
      exact decodeFrom_fuel un g Y.length _ Y (by simpa using hg) (Nat.le_refl _)
    · cases h
  | succ f ih =>
    intro a w X Y ds h hw hxy
    have hle := decodeSpan_le un stop _ _ _ _ h
    by_cases ha : a = stop
    · subst ha
      rw [decodeSpan_stop] at h
      simp only [Except.ok.injEq] at h
      subst h
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw0
      refine ⟨Chain.nil _, fun g hg => ?_⟩
      rw [except_map_nil]
      exact decodeFrom_fuel un g Y.length _ Y (by simpa using hg) (Nat.le_refl _)
    · obtain ⟨c, w', rfl⟩ : ∃ c w', w = c :: w' := by
        cases w with
        | nil => simp at hw; omega
        | cons c w' => exact ⟨c, w', rfl⟩
      have hdecXY : decodeAt (c :: (w' ++ X)) = decodeAt (c :: (w' ++ Y)) := by
        have := decodeAt_append_congr (w := c :: w') hxy
        simpa using this
      simp only [List.cons_append, decodeSpan, ha, ↓reduceIte] at h
      -- the recursive step, shared by both kinds of listed instruction
      have step : ∀ (it : Item) (n : Nat), 0 < n →
          (decodeSpan un stop f (a + n) ((c :: (w' ++ X)).drop n)).map (⟨a, it, n⟩ :: ·) = .ok ds →
          (∀ g, (c :: (w' ++ Y)).length ≤ g + 1 →
            decodeFrom un g (a + n) ((c :: (w' ++ Y)).drop n) =
              (decodeFrom un Y.length stop Y).map ((ds.drop 1) ++ ·)) ∧
          Chain a stop ds ∧ n ≤ (c :: w').length := by
        intro it n hn h
        cases hr : decodeSpan un stop f (a + n) ((c :: (w' ++ X)).drop n) with
        | error e => rw [hr] at h; cases h
        | ok ds' =>
          rw [hr] at h
          simp only [Except.map, Except.ok.injEq] at h
          subst h
          have hle' := decodeSpan_le un stop _ _ _ _ hr
          have hnw : n ≤ (c :: w').length := by simp only [List.length_cons] at hw ⊢; omega
          have hdX : (c :: (w' ++ X)).drop n = (c :: w').drop n ++ X := by
            rw [← List.cons_append, List.drop_append_of_le_length hnw]
          have hdY : (c :: (w' ++ Y)).drop n = (c :: w').drop n ++ Y := by
            rw [← List.cons_append, List.drop_append_of_le_length hnw]
          rw [hdX] at hr
          obtain ⟨hch, hdec⟩ := ih (a + n) ((c :: w').drop n) X Y ds' hr
            (by simp only [List.length_drop, List.length_cons] at hw ⊢; omega) hxy
          refine ⟨fun g hg => ?_, Chain.cons rfl hn hch, hnw⟩
          rw [hdY]
          simp only [List.drop_succ_cons, List.drop_zero]
          apply hdec
          simp only [List.length_append, List.length_drop, List.length_cons] at hg ⊢
          omega
      have finish : ∀ (it : Item) (n : Nat) (ds' : List D8), 0 < n → ds = ⟨a, it, n⟩ :: ds' →
          (∀ g, (c :: (w' ++ Y)).length ≤ g + 1 →
            decodeFrom un g (a + n) ((c :: (w' ++ Y)).drop n) =
              (decodeFrom un Y.length stop Y).map (ds' ++ ·)) →
          (∀ g', decodeFrom un (g' + 1) a (c :: (w' ++ Y)) =
            (decodeFrom un g' (a + n) ((c :: (w' ++ Y)).drop n)).map (⟨a, it, n⟩ :: ·)) →
          ∀ g, ((c :: w') ++ Y).length ≤ g →
            decodeFrom un g a ((c :: w') ++ Y) = (decodeFrom un Y.length stop Y).map (ds ++ ·) := by
        intro it n ds' hn hds hrec hunf g hg
        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hg; omega⟩
        rw [List.cons_append, hunf g', hrec g' (by simpa using hg), except_map_map, hds]
        rfl
      cases hl : un.lookup a with
      | some n =>
        simp only [hl] at h
        by_cases hc : n = 0 ∨ ((c :: (w' ++ X)).take n).length < n
        · simp only [hc, ↓reduceIte] at h; cases h
        · simp only [hc, ↓reduceIte] at h
          by_cases hd : (decodeAt (c :: (w' ++ X))).isSome = true
          · simp only [hd, ↓reduceIte] at h; cases h
          · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
            have hn : 0 < n := by omega
            obtain ⟨hrec, hch, hnw⟩ := step .unmodelled n hn h
            obtain ⟨ds', hds⟩ : ∃ ds', ds = ⟨a, .unmodelled, n⟩ :: ds' := by
              cases hr : decodeSpan un stop f (a + n) ((c :: (w' ++ X)).drop n) with
              | error e => rw [hr] at h; cases h
              | ok ds' =>
                rw [hr] at h
                simp only [Except.map, Except.ok.injEq] at h
                exact ⟨ds', h.symm⟩
            refine ⟨hch, finish .unmodelled n ds' hn hds (by rw [hds] at hrec; simpa using hrec) ?_⟩
            intro g'
            have hlen : ¬ (n = 0 ∨ (c :: (w' ++ Y)).length < n) := by
              simp only [List.length_cons, List.length_append] at hnw ⊢; omega
            have hd' : (decodeAt (c :: (w' ++ Y))).isSome = false := by
              rw [← hdecXY]; simpa using hd
            simp only [decodeFrom, hl, hlen, hd', ↓reduceIte, Bool.false_eq_true]
      | none =>
        simp only [hl] at h
        cases hdd : decodeAt (c :: (w' ++ X)) with
        | none => simp only [hdd] at h; cases h
        | some x =>
          obtain ⟨it, n⟩ := x
          simp only [hdd] at h
          by_cases hn0 : n = 0
          · simp only [hn0, ↓reduceIte] at h; cases h
          · simp only [hn0, ↓reduceIte] at h
            have hn : 0 < n := by omega
            obtain ⟨hrec, hch, hnw⟩ := step it n hn h
            obtain ⟨ds', hds⟩ : ∃ ds', ds = ⟨a, it, n⟩ :: ds' := by
              cases hr : decodeSpan un stop f (a + n) ((c :: (w' ++ X)).drop n) with
              | error e => rw [hr] at h; cases h
              | ok ds' =>
                rw [hr] at h
                simp only [Except.map, Except.ok.injEq] at h
                exact ⟨ds', h.symm⟩
            refine ⟨hch, finish it n ds' hn hds (by rw [hds] at hrec; simpa using hrec) ?_⟩
            intro g'
            have hd' : decodeAt (c :: (w' ++ Y)) = some (it, n) := by rw [← hdecXY, hdd]
            simp only [decodeFrom, hl, hd', hn0, ↓reduceIte]

/-! ## Inverting the checks -/

/-- The listing that the check of piece `j` decodes (`[]` if there is none). -/
def pieceListing (p : Proposal) (c : Cert) (j : Nat) : List D8 :=
  match c.pieces[j]? with
  | some P =>
    match decodeSpan p.unmodelled P.stop (P.stop - P.start) P.start (pieceBytes c j P) with
    | .ok ds => ds
    | .error _ => []
  | none => []

/-- The listings of pieces `j, …, j + m - 1`, concatenated. -/
def listingFrom (p : Proposal) (c : Cert) : Nat → Nat → List D8
  | _, 0 => []
  | j, m + 1 => pieceListing p c j ++ listingFrom p c (j + 1) m

theorem mem_listingFrom {p : Proposal} {c : Cert} {d : D8} :
    ∀ (m j : Nat), d ∈ listingFrom p c j m → ∃ k, j ≤ k ∧ k < j + m ∧ d ∈ pieceListing p c k := by
  intro m
  induction m with
  | zero => intro j h; simp [listingFrom] at h
  | succ m ih =>
    intro j h
    simp only [listingFrom, List.mem_append] at h
    rcases h with h | h
    · exact ⟨j, Nat.le_refl _, by omega, h⟩
    · obtain ⟨k, h1, h2, h3⟩ := ih (j + 1) h
      exact ⟨k, by omega, by omega, h3⟩

theorem checkPiece_inv {base : Nat} {p : Proposal} {c : Cert} {j : Nat}
    (h : checkPiece base p c j = none) :
    ∃ P s, c.pieces[j]? = some P ∧ p.layout[P.slot]? = some s ∧
      P.bytes.length = P.stop - P.start ∧
      decodeSpan p.unmodelled P.stop (P.stop - P.start) P.start (pieceBytes c j P) =
        .ok (pieceListing p c j) ∧
      (∀ a b, s = .padding a b → ∀ d ∈ pieceListing p c j, isNop d = true) ∧
      (∀ i a b, s = .code i a b →
        addrBits base (pieceListing p c j) = restrict (c.bitsOf i) (P.start - base) (P.stop - base) ∧
        ∀ d ∈ pieceListing p c j, instrOk base p i (c.bitsOf i) d = none) := by
  unfold checkPiece at h
  split at h
  · cases h
  · rename_i P hP
    split at h
    · cases h
    · rename_i hlen
      split at h
      · cases h
      · rename_i ds hds
        have hpl : pieceListing p c j = ds := by simp [pieceListing, hP, hds]
        split at h
        · cases h
        · rename_i a b hs
          refine ⟨P, _, hP, hs, by omega, by rw [hpl, hds], ?_, ?_⟩
          · intro a' b' _ d hd
            rw [hpl] at hd
            split at h
            · cases h
            · rename_i hf
              have := List.find?_eq_none.mp hf d hd
              simpa using this
          · intro i a' b' e
            cases e
        · rename_i i a b hs
          simp only at h
          split at h
          · rename_i hbits
            refine ⟨P, _, hP, hs, by omega, by rw [hpl, hds], ?_, ?_⟩
            · intro a' b' e; cases e
            · intro i' a' b' e
              cases e
              rw [hpl]
              exact ⟨hbits, List.findSome?_eq_none_iff.mp h⟩
          · cases h

theorem checkGlobal_inv {base len : Nat} {p : Proposal} {c : Cert}
    (h : checkGlobal base len p c = none) :
    tiling (base + len) base p.layout = none ∧
      p.layout.find? (fun s => (s.owner.map fun o => decide (p.funcs.length ≤ o)).getD false) = none ∧
      p.funcs.find? (fun f => f.exported && !f.conv.isAbi) = none ∧
      piecesTile (base + len) base c.pieces = true ∧
      (∀ P ∈ c.pieces, inSlot p P = true) ∧
      (∀ i < p.funcs.length, fnOk base p c i = true) := by
  unfold checkGlobal at h
  split at h
  · cases h
  · rename_i ht
    split at h
    · cases h
    · rename_i ho
      split at h
      · cases h
      · rename_i hx
        split at h
        · cases h
        · rename_i hpt
          split at h
          · cases h
          · rename_i hin
            split at h
            · cases h
            · split at h
              · cases h
              · rename_i hf
                refine ⟨ht, ho, hx, by simpa using hpt, ?_, ?_⟩
                · intro P hP
                  have := List.find?_eq_none.mp hin P hP
                  simpa using this
                · intro i hi
                  have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
                  simpa using this

theorem below_spec {P : Nat → Prop} : ∀ {n : Nat}, Below P n → ∀ i < n, P i := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h.1 i hi
    · exact h.2

/-! ## Bitmaps -/

theorem testBit_addrBits {base k : Nat} {ds : List D8} (h : (addrBits base ds).testBit k = true) :
    ∃ d ∈ ds, d.addr - base = k := by
  have gen : ∀ (ds : List D8) (acc : Nat),
      (ds.foldl (fun acc d => acc ||| 2 ^ (d.addr - base)) acc).testBit k = true →
        acc.testBit k = true ∨ ∃ d ∈ ds, d.addr - base = k := by
    intro ds
    induction ds with
    | nil => intro acc h; exact Or.inl h
    | cons d ds ih =>
      intro acc h
      rcases ih _ h with h | h
      · rw [Nat.testBit_or, Nat.testBit_two_pow] at h
        rcases Bool.or_eq_true_iff.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨d, List.mem_cons_self, by simpa using h⟩
      · obtain ⟨d', hd', e⟩ := h
        exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', e⟩
  rcases gen ds 0 h with h | h
  · simp at h
  · exact h

theorem testBit_restrict {bits a b k : Nat} :
    (restrict bits a b).testBit k = true ↔ a ≤ k ∧ k < b ∧ bits.testBit k = true := by
  unfold restrict
  rw [Nat.testBit_shiftLeft]
  by_cases hk : a ≤ k
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.add_sub_cancel' hk]
    simp only [ge_iff_le, hk, decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨trivial, by omega, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨by omega, h2⟩
  · simp only [ge_iff_le, hk, decide_false, Bool.false_and, Bool.false_eq_true, false_and]

theorem testBit_coverOf {base i bits k : Nat} {p : Proposal}
    (h : (coverOf base p i bits).testBit k = true) :
    ∃ s ∈ p.layout, s.owner = some i ∧
      (restrict bits (s.start - base) (s.stop - base)).testBit k = true := by
  have gen : ∀ (l : List Slot) (acc : Nat),
      (l.foldl (fun acc s => if s.owner = some i then
        acc ||| restrict bits (s.start - base) (s.stop - base) else acc) acc).testBit k = true →
        acc.testBit k = true ∨ ∃ s ∈ l, s.owner = some i ∧
          (restrict bits (s.start - base) (s.stop - base)).testBit k = true := by
    intro l
    induction l with
    | nil => intro acc h; exact Or.inl h
    | cons s l ih =>
      intro acc h
      rcases ih _ h with h | h
      · simp only at h
        split at h
        · rename_i ho
          rw [Nat.testBit_or] at h
          rcases Bool.or_eq_true_iff.mp h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨s, List.mem_cons_self, ho, h⟩
        · exact Or.inl h
      · obtain ⟨s', hs', e⟩ := h
        exact Or.inr ⟨s', List.mem_cons_of_mem _ hs', e⟩
  rcases gen p.layout 0 h with h | h
  · simp at h
  · exact h

/-! ## The pieces decode the region -/

theorem piecesTile_spec (limit : Nat) : ∀ (Ps : List Piece) (cur : Nat),
    piecesTile limit cur Ps = true →
      ∀ t, cur ≤ t → t < limit → ∃ k, ∃ hk : k < Ps.length, Ps[k].start ≤ t ∧ t < Ps[k].stop := by
  intro Ps
  induction Ps with
  | nil =>
    intro cur h t h1 h2
    simp only [piecesTile, decide_eq_true_eq] at h
    omega
  | cons P Ps ih =>
    intro cur h t h1 h2
    simp only [piecesTile, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hs, -⟩, hr⟩ := h
    by_cases ht : t < P.stop
    · exact ⟨0, by simp, by simp; omega, by simpa using ht⟩
    · obtain ⟨k, hk, h3, h4⟩ := ih P.stop hr t (by omega) h2
      exact ⟨k + 1, by simpa using hk, by simpa using h3, by simpa using h4⟩

theorem restBytes_cons {c : Cert} {j : Nat} (hj : j < c.pieces.length) :
    restBytes c j = c.pieces[j].bytes ++ restBytes c (j + 1) := by
  unfold restBytes
  rw [List.drop_eq_getElem_cons hj, List.map_cons, List.flatten_cons]

section

variable {base len : Nat} {p : Proposal} {c : Cert}

/-- **The pieces decode the region.** From piece `j` on, the region's bytes have the expected
length, list a chain of instructions, and `decodeFrom` lists exactly the pieces' listings. -/
theorem pieces_decode (hpieces : ∀ j < c.pieces.length, checkPiece base p c j = none) :
    ∀ (m j cur : Nat), c.pieces.length = j + m →
      piecesTile (base + len) cur (c.pieces.drop j) = true →
      (restBytes c j).length = base + len - cur ∧ Chain cur (base + len) (listingFrom p c j m) ∧
      ∀ g, (restBytes c j).length ≤ g →
        decodeFrom p.unmodelled g cur (restBytes c j) = .ok (listingFrom p c j m) := by
  intro m
  induction m with
  | zero =>
    intro j cur hlen ht
    have hd : c.pieces.drop j = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd] at ht
    simp only [piecesTile, decide_eq_true_eq] at ht
    subst ht
    have hr : restBytes c j = [] := by simp [restBytes, hd]
    refine ⟨by simp [hr], Chain.nil _, fun g _ => ?_⟩
    rw [hr]
    cases g <;> simp [decodeFrom, listingFrom]
  | succ m ih =>
    intro j cur hlen ht
    have hj : j < c.pieces.length := by omega
    rw [List.drop_eq_getElem_cons hj] at ht
    simp only [piecesTile, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨hstart, hlt⟩, hrest⟩ := ht
    obtain ⟨P, s, hP, -, hbl, hdec, -, -⟩ := checkPiece_inv (hpieces j hj)
    have hPe : c.pieces[j] = P := by
      rw [List.getElem?_eq_some_iff] at hP
      obtain ⟨_, e⟩ := hP
      exact e
    subst hPe
    obtain ⟨hl', hch', hdec'⟩ := ih (j + 1) _ (by omega) hrest
    unfold pieceBytes at hdec
    obtain ⟨hch, hsp⟩ := span_sound p.unmodelled _ _ _ _ _ (restBytes c (j + 1)) _ hdec
      (by omega) (by rw [List.take_take]; rfl)
    have hle := hch'.le
    refine ⟨?_, ?_, fun g hg => ?_⟩
    · rw [restBytes_cons hj, List.length_append, hl', hbl]
      omega
    · simp only [listingFrom]
      rw [← hstart]
      exact hch.append hch'
    · rw [restBytes_cons hj] at hg ⊢
      rw [← hstart, hsp g hg, hdec' _ (Nat.le_refl _)]
      rfl

end

/-! ## Slots -/

theorem slot_unique {l : List Slot} (hp : l.Pairwise (fun s s' => s.stop ≤ s'.start))
    {x y : Slot} (hx : x ∈ l) (hy : y ∈ l) {t : Nat}
    (h1 : x.start ≤ t ∧ t < x.stop) (h2 : y.start ≤ t ∧ t < y.stop) : x = y := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · rw [ex, ey]
    · have := hp.1 y hy'; subst ex; omega
    · have := hp.1 x hx'; subst ey; omega
    · exact ih hp.2 hx' hy'

theorem slotOf_eq {p : Proposal} (hp : p.layout.Pairwise (fun s s' => s.stop ≤ s'.start))
    {k : Nat} {s : Slot} (hs : p.layout[k]? = some s) {d : D8}
    (h1 : s.start ≤ d.addr) (h2 : d.addr + d.size ≤ s.stop) (hpos : 0 < d.size) :
    p.slotOf d = some s := by
  obtain ⟨hk, hks⟩ := List.getElem?_eq_some_iff.mp hs
  have hsplit : p.layout = p.layout.take k ++ s :: p.layout.drop (k + 1) := by
    conv => lhs; rw [← List.take_append_drop k p.layout]
    rw [List.drop_eq_getElem_cons hk, hks]
  unfold Proposal.slotOf
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simp [h1, h2], p.layout.take k, p.layout.drop (k + 1), hsplit, ?_⟩
  intro a ha
  rw [hsplit, List.pairwise_append] at hp
  have := hp.2.2 a ha s List.mem_cons_self
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_and, Nat.not_le]
  intro _
  omega

theorem mem_listingFrom_of {p : Proposal} {c : Cert} {d : D8} :
    ∀ (m j k : Nat), j ≤ k → k < j + m → d ∈ pieceListing p c k → d ∈ listingFrom p c j m := by
  intro m
  induction m with
  | zero => intro j k h1 h2; omega
  | succ m ih =>
    intro j k h1 h2 hd
    simp only [listingFrom, List.mem_append]
    by_cases hk : k = j
    · subst hk; exact Or.inl hd
    · exact Or.inr (ih (j + 1) k (by omega) (by omega) hd)

section

variable {base len : Nat} {p : Proposal} {c : Cert}

theorem piece_chain {k : Nat} (hpc : checkPiece base p c k = none) {P : Piece}
    (hP : c.pieces[k]? = some P) : Chain P.start P.stop (pieceListing p c k) := by
  obtain ⟨P', s, hP', -, hbl, hdec, -, -⟩ := checkPiece_inv hpc
  rw [hP] at hP'
  cases hP'
  unfold pieceBytes at hdec
  exact (span_sound p.unmodelled _ _ _ _ _ _ _ hdec (by omega) rfl).1

/-- An instruction decoded in piece `k` lies in the piece's slot, which `slotOf` finds. -/
theorem piece_slot (hg : checkGlobal base len p c = none)
    (hpc : ∀ j < c.pieces.length, checkPiece base p c j = none) {k : Nat}
    (hk : k < c.pieces.length) {d : D8} (hd : d ∈ pieceListing p c k) :
    ∃ P s, c.pieces[k]? = some P ∧ p.layout[P.slot]? = some s ∧ p.slotOf d = some s ∧
      P.start ≤ d.addr ∧ d.addr + d.size ≤ P.stop ∧
      (∀ a b, s = .padding a b → isNop d = true) ∧
      (∀ i a b, s = .code i a b →
        addrBits base (pieceListing p c k) =
          restrict (c.bitsOf i) (P.start - base) (P.stop - base) ∧
        instrOk base p i (c.bitsOf i) d = none) := by
  obtain ⟨ht, -, -, -, hin, -⟩ := checkGlobal_inv hg
  obtain ⟨-, hpw, -⟩ := tiling_spec _ _ _ ht
  obtain ⟨P, s, hP, hs, -, -, hpad, hcode⟩ := checkPiece_inv (hpc k hk)
  have hch := piece_chain (hpc k hk) hP
  obtain ⟨hd1, hd2, hpos⟩ := hch.mem d hd
  have hinP := hin P (List.mem_of_getElem? hP)
  unfold inSlot at hinP
  rw [hs] at hinP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hinP
  refine ⟨P, s, hP, hs, slotOf_eq hpw hs (by omega) (by omega) hpos, hd1, hd2,
    fun a b e => hpad a b e d hd, fun i a b e => ⟨(hcode i a b e).1, (hcode i a b e).2 d hd⟩⟩

/-- **Bitmaps are sound.** A bit of function `i`'s bitmap is the address of a listed
instruction that `i` owns. -/
theorem inBits_sound (hg : checkGlobal base len p c = none)
    (hpc : ∀ j < c.pieces.length, checkPiece base p c j = none) {i t : Nat}
    (hi : i < p.funcs.length) (h : inBits base (c.bitsOf i) t = true) :
    ∃ d ∈ listingFrom p c 0 c.pieces.length, d.addr = t ∧ p.owner d = some i := by
  obtain ⟨ht, -, -, hpt, hin, hfn⟩ := checkGlobal_inv hg
  obtain ⟨hsl, hpw, -⟩ := tiling_spec _ _ _ ht
  have hf := hfn i hi
  unfold fnOk at hf
  cases hfi : p.funcs[i]? with
  | none => simp [hfi] at hf
  | some f =>
    simp only [hfi, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨-, hcov⟩ := hf
    unfold inBits at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hbt, hbit⟩ := h
    rw [← hcov] at hbit
    obtain ⟨s, hs, hso, hr⟩ := testBit_coverOf hbit
    rw [testBit_restrict] at hr
    obtain ⟨hr1, hr2, hbit'⟩ := hr
    obtain ⟨hs1, hs2, hs3⟩ := hsl s hs
    obtain ⟨k, hk, hk1, hk2⟩ := piecesTile_spec _ c.pieces base hpt t (by omega) (by omega)
    obtain ⟨P, s', hP, hs', -, -, -, hcode⟩ := checkPiece_inv (hpc k hk)
    have hPe : c.pieces[k] = P := (List.getElem?_eq_some_iff.mp hP).2
    rw [hPe] at hk1 hk2
    have hinP := hin P (List.mem_of_getElem? hP)
    unfold inSlot at hinP
    rw [hs'] at hinP
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hinP
    have hss : s = s' := slot_unique (t := t) hpw hs (List.mem_of_getElem? hs')
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    subst hss
    obtain ⟨a, b, hab⟩ : ∃ a b, s = .code i a b := by
      cases s with
      | code o a b => simp only [Slot.owner, Option.some.injEq] at hso; subst hso; exact ⟨a, b, rfl⟩
      | padding a b => simp [Slot.owner] at hso
    obtain ⟨hbits, -⟩ := hcode i a b hab
    have hsP1 : s.start ≤ P.start := hinP.1
    have htb : (addrBits base (pieceListing p c k)).testBit (t - base) = true := by
      rw [hbits, testBit_restrict]
      exact ⟨by omega, by omega, hbit'⟩
    obtain ⟨d, hd, hda⟩ := testBit_addrBits htb
    obtain ⟨P2, s2, hP2, hs2', hslot, hd1, -, -, -⟩ := piece_slot hg hpc hk hd
    rw [hP] at hP2
    cases hP2
    rw [hs'] at hs2'
    cases hs2'
    refine ⟨d, mem_listingFrom_of _ 0 k (Nat.zero_le _) (by omega) hd, by omega, ?_⟩
    simp [Proposal.owner, hslot, hab, Slot.owner]

end

/-! ## The walk and `check2` -/

theorem walk_none_of (c : Ctx) : ∀ (ann : List (D8 × Option Nat)),
    (∀ pre d i post, ann = pre ++ (d, some i) :: post →
      ¬(d.item = .unmodelled ∧ c.p.noret i = true) ∧
        ∀ e ∈ d.edges, c.checkEdge i d post.head? e = none) →
    c.walk ann = none := by
  intro ann
  induction ann with
  | nil => intro _; rfl
  | cons x rest ih =>
    intro h
    obtain ⟨d, o⟩ := x
    have hrest : ∀ pre d i post, rest = pre ++ (d, some i) :: post →
        ¬(d.item = .unmodelled ∧ c.p.noret i = true) ∧
          ∀ e ∈ d.edges, c.checkEdge i d post.head? e = none := by
      intro pre d' i post e
      exact h ((d, o) :: pre) d' i post (by rw [e]; rfl)
    cases o with
    | none => simp only [Ctx.walk]; exact ih hrest
    | some i =>
      obtain ⟨h1, h2⟩ := h [] d i rest rfl
      simp only [Ctx.walk]
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), List.findSome?_eq_none_iff.mpr h2]
      exact ih hrest

theorem mem_bodies_of {p : Proposal} {ann : List (D8 × Option Nat)} {d : D8} {i : Nat}
    (h : (d, some i) ∈ ann) (hi : i < p.funcs.length) :
    d.addr ∈ (bodiesOf p ann).getD i [] := by
  rw [List.getD_eq_getElem?_getD]
  unfold bodiesOf
  rw [List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, List.mem_filterMap]
  exact ⟨(d, some i), h, by simp⟩

theorem check2_eq_none_of {r : Region} {p : Proposal} {fuel : Nat} {ds : List D8}
    (hds : decodeListing r p.unmodelled fuel = .ok ds)
    (ht : tiling (r.base + r.bytes.length) r.base p.layout = none)
    (ho : p.layout.find?
      (fun s => (s.owner.map fun o => decide (p.funcs.length ≤ o)).getD false) = none)
    (hsl : ∀ d ∈ ds, slotCheck p d = none)
    (hx : p.funcs.find? (fun f => f.exported && !f.conv.isAbi) = none)
    (hent : ∀ i < p.funcs.length,
      ((p.funcs[i]?.map fun f => decide (f.entry ∈ (bodiesOf p (annotate p ds)).getD i [])).getD
        false) = true)
    (hw : Ctx.walk ⟨p, bodiesOf p (annotate p ds)⟩ (annotate p ds) = none) :
    check2 r p fuel = none := by
  have hf : (List.range p.funcs.length).find? (fun i =>
      !((p.funcs[i]?.map fun f => decide (f.entry ∈ (bodiesOf p (annotate p ds)).getD i [])).getD
        false)) = none := by
    rw [List.find?_eq_none]
    intro i hi
    rw [hent i (List.mem_range.mp hi)]
    simp
  unfold check2
  simp only [hds, ht, ho, List.findSome?_eq_none_iff.mpr hsl, hx]
  rw [hf]
  exact hw

theorem callsNoreturn_eq (p : Proposal) (b : List (List Nat)) (d : D8) :
    Ctx.callsNoreturn ⟨p, b⟩ d = callsNoreturn p d := rfl

/-- **The pieces compose.** A global check, one check per piece, and the bytes of the pieces
being the region's bytes imply `check2`. -/
theorem check2_of_shards {r : Region} {p : Proposal} {c : Cert} {len fuel : Nat}
    (hbytes : r.bytes = (c.pieces.map Piece.bytes).flatten)
    (hg : checkGlobal r.base len p c = none)
    (hp : Below (fun j => checkPiece r.base p c j = none) c.pieces.length)
    (hfuel : len ≤ fuel) : check2 r p fuel = none := by
  have hpc := below_spec hp
  obtain ⟨ht, ho, hx, hpt, -, hfn⟩ := checkGlobal_inv hg
  have hrb : restBytes c 0 = r.bytes := by simp [restBytes, hbytes]
  obtain ⟨hlen, hch, hdec⟩ := pieces_decode (base := r.base) (len := len) hpc
    c.pieces.length 0 r.base (by simp) (by simpa using hpt)
  rw [hrb] at hlen hdec
  have hds : decodeListing r p.unmodelled fuel = .ok (listingFrom p c 0 c.pieces.length) :=
    hdec fuel (by omega)
  have howner : ∀ s ∈ p.layout, ∀ o, s.owner = some o → o < p.funcs.length := by
    intro s hs o hso
    have := List.find?_eq_none.mp ho s hs
    rw [hso] at this
    simpa using this
  -- the listing is the pieces' listings
  have hmem : ∀ d ∈ listingFrom p c 0 c.pieces.length,
      ∃ k, k < c.pieces.length ∧ d ∈ pieceListing p c k := by
    intro d hd
    obtain ⟨k, -, hk, hdk⟩ := mem_listingFrom _ _ hd
    exact ⟨k, by omega, hdk⟩
  apply check2_eq_none_of hds (by rw [show r.base + r.bytes.length = r.base + len by omega]; exact ht)
    ho _ hx _ _
  · -- every instruction lies in its slot; padding is NOPs
    intro d hd
    obtain ⟨k, hk, hdk⟩ := hmem d hd
    obtain ⟨P, s, -, -, hslot, -, -, hpad, -⟩ := piece_slot hg hpc hk hdk
    unfold slotCheck
    rw [hslot]
    cases s with
    | code o a b => rfl
    | padding a b =>
      have := hpad a b rfl
      simp only
      unfold isNop at this
      split at this
      · rename_i n heq
        rw [heq]
      · cases this
  · -- entries
    intro i hi
    have hf := hfn i hi
    unfold fnOk at hf
    cases hfi : p.funcs[i]? with
    | none => simp [hfi] at hf
    | some f =>
      simp only [hfi, Bool.and_eq_true] at hf
      obtain ⟨d, hd, hda, hown⟩ := inBits_sound hg hpc hi hf.1
      have hm : (d, some i) ∈ annotate p (listingFrom p c 0 c.pieces.length) :=
        mem_annotate.mpr ⟨hd, hown⟩
      have := mem_bodies_of hm hi
      rw [hda] at this
      simp only [Option.map_some, Option.getD_some, decide_eq_true_eq]
      exact this
  · -- the walk
    apply walk_none_of
    intro pre d i post hsplit
    unfold annotate at hsplit
    obtain ⟨l1, l2, hdsplit, -, hl2⟩ := List.map_eq_append_iff.mp hsplit
    obtain ⟨d0, l3, rfl, hd0, hl3⟩ := List.map_eq_cons_iff.mp hl2
    simp only [Prod.mk.injEq] at hd0
    obtain ⟨rfl, hown⟩ := hd0
    subst hl3
    have hd : d0 ∈ listingFrom p c 0 c.pieces.length := by rw [hdsplit]; simp
    obtain ⟨k, hk, hdk⟩ := hmem d0 hd
    obtain ⟨P, s, -, hs, hslot, -, -, -, hcode⟩ := piece_slot hg hpc hk hdk
    have hso : s.owner = some i := by
      simpa [Proposal.owner, hslot] using hown
    have hi : i < p.funcs.length := howner s (List.mem_of_getElem? hs) i hso
    obtain ⟨a, b, hab⟩ : ∃ a b, s = .code i a b := by
      cases s with
      | code o a b => simp only [Slot.owner, Option.some.injEq] at hso; subst hso; exact ⟨a, b, rfl⟩
      | padding a b => simp [Slot.owner] at hso
    have hins := (hcode i a b hab).2
    unfold instrOk at hins
    split at hins
    · cases hins
    · rename_i hnu
      refine ⟨hnu, fun e he => ?_⟩
      have hedge := List.findSome?_eq_none_iff.mp hins e he
      have hnext := hch.next l1 d0 l3 hdsplit
      cases e with
      | fallthrough t =>
        simp only [edgeOk] at hedge
        simp only [Ctx.checkEdge, callsNoreturn_eq]
        by_cases hcn : callsNoreturn p d0 = true
        · simp only [hcn, ↓reduceIte]
        · simp only [hcn, Bool.false_eq_true, ↓reduceIte] at hedge ⊢
          split at hedge
          · rename_i hok
            obtain ⟨htd, hbit⟩ := hok
            obtain ⟨e', he', he'a, he'o⟩ := inBits_sound hg hpc hi hbit
            cases l3 with
            | nil =>
              have hend := hnext.2 rfl
              have := hch.mem e' he'
              omega
            | cons d' l3' =>
              have hd'a := hnext.1 d' (by simp)
              have hd' : d' ∈ listingFrom p c 0 c.pieces.length := by rw [hdsplit]; simp
              have he : d' = e' := hch.addr_inj d' hd' e' he' (by omega)
              subst he
              have hat : d'.addr = t := by omega
              simp only [List.map_cons, List.head?_cons, he'o, hat, and_self, ↓reduceIte]
          · cases hedge
      | jump t | branch t =>
        simp only [edgeOk] at hedge
        simp only [Ctx.checkEdge]
        unfold jumpOk at hedge
        unfold Ctx.checkJump
        split at hedge
        · rename_i hbit
          obtain ⟨e', he', he'a, he'o⟩ := inBits_sound hg hpc hi hbit
          have hm : (e', some i) ∈ annotate p (listingFrom p c 0 c.pieces.length) :=
            mem_annotate.mpr ⟨he', he'o⟩
          have := mem_bodies_of hm hi
          rw [he'a] at this
          simp only [Ctx.body, this, ↓reduceIte]
        · split
          · rfl
          · exact hedge
      | call t => simpa [edgeOk, Ctx.checkEdge] using hedge
      | ret => simpa [edgeOk, Ctx.checkEdge] using hedge
      | halt => rfl

end Silmaril.Proofs.X86.Partition.Shard
