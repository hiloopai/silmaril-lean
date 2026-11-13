module

public import Silmaril.Proofs.Parse.ByteParse.Leb

/-!
# Loops, vectors, names and tags: soundness and completeness

* `many n p` reads `Seq G` of length `n` (`Spec.many`);
* `vec p` reads silmaril's `Vec G` (sound always; complete when `G` never
  relates the empty string, because the count is checked against the window);
* `untilEnd p` reads `Seq G` up to the end of its window; under `sized` it is
  complete (`complete_sized_untilEnd`);
* `name` is sound for silmaril's `Name` and complete for `Spec.name`, the
  canonical encoding `vec(byte)` of `s.toUTF8`;
* `tagged` dispatches on a tag byte (`Spec.tagged`).
-/

@[expose] public section

namespace Silmaril.Parse.ByteParse

open Silmaril.Wasm.Binary (Seq Vec UN U32 Name Byte Utf8)

variable {α : Type}

/-! ## `many` -/

theorem manyAux_sound {G : Bytes → α → Prop} {p : Parser α} (hp : Sound G p) (n : Nat) :
    ∀ (acc : Array α) {bs : ByteArray} {st i : Nat} {out : Array α} {j : Nat},
      i ≤ st → st ≤ bs.size → manyAux p n acc bs st i = .ok out j →
      i ≤ j ∧ j ≤ st ∧ ∃ xs, out = acc ++ xs.toArray ∧ Seq G (seg bs i j) xs ∧ xs.length = n := by
  induction n with
  | zero =>
    intro acc bs st i out j hi hs h
    simp only [manyAux] at h
    cases h
    exact ⟨Nat.le_refl _, hi, [], by simp, by rw [seg_self]; exact Seq.nil, rfl⟩
  | succ n ih =>
    intro acc bs st i out j hi hs h
    simp only [manyAux] at h
    split at h
    · next a k hpk =>
      obtain ⟨h1, h2, h3⟩ := hp hi hs hpk
      obtain ⟨h4, h5, xs, rfl, h6, h7⟩ := ih (acc.push a) h2 hs h
      refine ⟨by omega, h5, a :: xs, by simp, ?_, by simp [h7]⟩
      rw [seg_append bs h1 h4]
      exact Seq.cons h3 h6
    · cases h

theorem manyAux_complete {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p) {l : Bytes}
    {xs : List α} (hx : Seq G l xs) :
    ∀ (acc : Array α) {bs : ByteArray} {st i : Nat}, i + l.length ≤ st → st ≤ bs.size →
      seg bs i (i + l.length) = l →
      manyAux p xs.length acc bs st i = .ok (acc ++ xs.toArray) (i + l.length) := by
  induction hx with
  | nil => intro acc bs st i _ _ _; simp [manyAux]
  | @cons b bs' a as hg _ ih =>
    intro acc bs st i hl hs hseg
    have hb : i + (b ++ bs').length ≤ bs.size := Nat.le_trans hl hs
    obtain ⟨s1, s2⟩ := seg_split bs hb hseg
    simp only [List.length_append] at hl ⊢
    simp only [List.length_cons, manyAux]
    rw [hp hg (by omega) hs s1]
    simp only
    rw [ih (acc.push a) (by omega) hs s2]
    simp [Nat.add_assoc]

theorem sound_many {G : Bytes → α → Prop} {p : Parser α} (hp : Sound G p) (n : Nat) :
    Sound (Spec.many G n) (many n p) := by
  intro bs st i out j hi hs h
  obtain ⟨xs', h1, rfl⟩ := map_ok h
  obtain ⟨h2, h3, xs, rfl, h4, h5⟩ := manyAux_sound hp n #[] hi hs h1
  exact ⟨h2, h3, by simpa using h4, by simpa using h5⟩

theorem complete_many {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p) (n : Nat) :
    Complete (Spec.many G n) (many n p) := by
  intro l xs bs st i hg hl hs hseg
  obtain ⟨hx, rfl⟩ := hg
  simp only [many, Parser.map_apply', manyAux_complete hp hx #[] hl hs hseg]
  simp

/-! ## Counts and vectors -/

theorem Seq.length_le {G : Bytes → α → Prop} (hne : NonEmpty G) {l : Bytes} {xs : List α}
    (h : Seq G l xs) : xs.length ≤ l.length := by
  induction h with
  | nil => simp
  | @cons b bs a as hg _ ih =>
    have := hne hg
    have : 0 < b.length := List.length_pos_iff.mpr this
    simp only [List.length_cons, List.length_append]; omega

theorem sound_count : Sound (fun l n => U32 l n) count := by
  intro bs st i n j hi hs h
  unfold count at h
  split at h
  · next n' k hk =>
    split at h
    · cases h; exact sound_uN 32 hi hs hk
    · cases h
  · cases h

theorem sound_vec {G : Bytes → α → Prop} {p : Parser α} (hp : Sound G p) :
    Sound (Spec.vec G) (vec p) := by
  intro bs st i xs k hi hs h
  unfold vec at h
  split at h
  · next n j hc =>
    obtain ⟨h1, h2, h3⟩ := sound_count hi hs hc
    obtain ⟨h4, h5, h6, h7⟩ := sound_many hp n h2 hs h
    refine ⟨by omega, h5, ?_⟩
    rw [seg_append bs h1 h4]
    exact Vec.mk (h7 ▸ h3) h6
  · cases h

theorem complete_vec {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p)
    (hne : NonEmpty G) : Complete (Spec.vec G) (vec p) := by
  intro l xs bs st i hg hl hs hseg
  obtain ⟨hn, hx⟩ := hg
  rename_i nb b
  have hb : i + (nb ++ b).length ≤ bs.size := Nat.le_trans hl hs
  obtain ⟨s1, s2⟩ := seg_split bs hb hseg
  simp only [List.length_append] at hl ⊢
  have hu := complete_uN 32 hn (by omega) hs s1
  have hle := Seq.length_le hne hx
  unfold vec count
  simp only [u32, hu, show xs.length ≤ st - (i + nb.length) by omega, ↓reduceIte]
  rw [← Nat.add_assoc]
  exact complete_many hp xs.length ⟨hx, rfl⟩ (by omega) hs s2

/-! ## Repetition to the end of the window -/

/-- Inversion of a successful `untilEndAux` round. -/
theorem untilEndAux_ok {p : Parser α} {fuel : Nat} {acc : Array α} {bs : ByteArray} {st i : Nat}
    {out : Array α} {j : Nat} (h : untilEndAux p fuel acc bs st i = .ok out j) :
    (i = st ∧ out = acc ∧ j = i) ∨
      ∃ f a k, fuel = f + 1 ∧ i < k ∧ p bs st i = .ok a k ∧
        untilEndAux p f (acc.push a) bs st k = .ok out j := by
  cases fuel with
  | zero =>
    simp only [untilEndAux] at h
    split at h
    · cases h; exact .inl ⟨‹_›, rfl, rfl⟩
    · cases h
  | succ f =>
    simp only [untilEndAux] at h
    split at h
    · cases h; exact .inl ⟨‹_›, rfl, rfl⟩
    · split at h
      · split at h
        · exact .inr ⟨f, _, _, rfl, ‹_›, ‹_›, h⟩
        · cases h
      · cases h

theorem untilEndAux_sound {G : Bytes → α → Prop} {p : Parser α} (hp : Sound G p) (fuel : Nat) :
    ∀ (acc : Array α) {bs : ByteArray} {st i : Nat} {out : Array α} {j : Nat},
      i ≤ st → st ≤ bs.size → untilEndAux p fuel acc bs st i = .ok out j →
      j = st ∧ ∃ xs, out = acc ++ xs.toArray ∧ Seq G (seg bs i j) xs := by
  induction fuel with
  | zero =>
    intro acc bs st i out j hi hs h
    rcases untilEndAux_ok h with ⟨hi', ho, hj⟩ | ⟨f, a, k, hf, -, -, -⟩
    · exact ⟨hj.trans hi', [], by simp [ho], by rw [hj, seg_self]; exact Seq.nil⟩
    · cases hf
  | succ n ih =>
    intro acc bs st i out j hi hs h
    rcases untilEndAux_ok h with ⟨hi', ho, hj⟩ | ⟨f, a, k, hf, hik, hpk, hrec⟩
    · exact ⟨hj.trans hi', [], by simp [ho], by rw [hj, seg_self]; exact Seq.nil⟩
    · have hfn : f = n := Nat.succ.inj hf.symm
      obtain ⟨h1, h2, h3⟩ : i ≤ k ∧ k ≤ st ∧ G (seg bs i k) a := hp hi hs hpk
      obtain ⟨h4, xs, hout, h6⟩ : j = st ∧ ∃ xs, out = acc.push a ++ xs.toArray ∧
          Seq G (seg bs k j) xs := ih (acc.push a) h2 hs (hfn ▸ hrec)
      have hseg : seg bs i j = seg bs i k ++ seg bs k j := seg_append bs h1 (by omega)
      exact ⟨h4, a :: xs, by simp [hout], by rw [hseg]; exact Seq.cons h3 h6⟩

theorem untilEndAux_complete {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p)
    (hne : NonEmpty G) {l : Bytes} {xs : List α} (hx : Seq G l xs) :
    ∀ (fuel : Nat) (acc : Array α) {bs : ByteArray} {i : Nat}, l.length ≤ fuel →
      i + l.length ≤ bs.size → seg bs i (i + l.length) = l →
      untilEndAux p fuel acc bs (i + l.length) i = .ok (acc ++ xs.toArray) (i + l.length) := by
  induction hx with
  | nil =>
    intro fuel acc bs i _ _ _
    cases fuel <;> simp [untilEndAux]
  | @cons b bs' a as hg _ ih =>
    intro fuel acc bs i hf hs hseg
    have hb0 : 0 < b.length := List.length_pos_iff.mpr (hne hg)
    obtain ⟨s1, s2⟩ := seg_split bs hs hseg
    simp only [List.length_append] at hf hs ⊢
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [untilEndAux, show i ≠ i + (b.length + bs'.length) by omega, ↓reduceIte]
    rw [hp hg (by omega) hs s1]
    simp only [show i < i + b.length by omega, ↓reduceIte]
    have := ih f (acc.push a) (i := i + b.length) (by omega) (by omega) s2
    rw [Nat.add_assoc] at this
    rw [this]
    simp

theorem sound_untilEnd {G : Bytes → α → Prop} {p : Parser α} (hp : Sound G p) :
    Sound (Seq G) (untilEnd p) := by
  intro bs st i out j hi hs h
  unfold untilEnd at h
  obtain ⟨xs', h1, rfl⟩ := map_ok h
  obtain ⟨h2, xs, rfl, h4⟩ := untilEndAux_sound hp (st - i) #[] hi hs h1
  exact ⟨by omega, by omega, by simpa using h4⟩

/-- `untilEnd` reaches the end of its window. -/
theorem untilEnd_end {p : Parser α} {bs : ByteArray} {st i : Nat} {out : List α} {j : Nat}
    (hp : Sound (fun _ _ => True) p) (hi : i ≤ st) (hs : st ≤ bs.size)
    (h : untilEnd p bs st i = .ok out j) : j = st := by
  unfold untilEnd at h
  obtain ⟨xs', h1, rfl⟩ := map_ok h
  exact (untilEndAux_sound hp (st - i) #[] hi hs h1).1

theorem completeAtEnd_untilEnd {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p)
    (hne : NonEmpty G) : CompleteAtEnd (Seq G) (untilEnd p) := by
  intro l xs bs i hx hs hseg
  unfold untilEnd
  simp only [Parser.map_apply', show i + l.length - i = l.length by omega,
    untilEndAux_complete hp hne hx l.length #[] (Nat.le_refl _) hs hseg]
  simp

theorem complete_sized_untilEnd {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p)
    (hne : NonEmpty G) (n : Nat) : Complete (Spec.sized n (Seq G)) (sized n (untilEnd p)) :=
  (completeAtEnd_untilEnd hp hne).sized n

/-! ## Names -/

theorem seqByte (bs : Bytes) : Seq Byte bs bs := by
  induction bs with
  | nil => exact Seq.nil
  | cons b bs ih => exact Seq.cons (Byte.mk b) ih

theorem fromUTF8_eq {bs : ByteArray} {s : String} (h : String.fromUTF8? bs = some s) :
    s.toUTF8 = bs := by
  unfold String.fromUTF8? at h
  split at h
  next => cases h; rw [String.toUTF8_eq_toByteArray]; rfl
  next => cases h

theorem fromUTF8_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  rw [String.toUTF8_eq_toByteArray, dite_eq_left_of_eq_true (eq_true s.isValidUTF8)]
  rfl

theorem name_spec_name {l : Bytes} {s : String} (h : Spec.name l s) : Name l s := by
  obtain ⟨nb, rfl, hu⟩ := h
  refine Name.mk (Vec.mk ?_ (seqByte _)) (Silmaril.Wasm.Binary.Utf8.toUTF8 s)
  rwa [← size_eq_length]

theorem sound_name' : Sound Spec.name name := by
  intro bs st i str k hi hs h
  unfold name at h
  split at h
  · next n j hc =>
    obtain ⟨h1, h2, h3⟩ := sound_count hi hs hc
    unfold utf8 at h
    split at h
    · next hn =>
      split at h
      · next str' hstr =>
        cases h
        refine ⟨by omega, hn, seg bs i j, ?_, ?_⟩
        · rw [seg_append bs h1 (by omega), fromUTF8_eq hstr, seg_extract]
        · rw [fromUTF8_eq hstr, ByteArray.size_extract]
          convert h3 using 1; omega
      · cases h
    · cases h
  · cases h

/-- `name` is sound for silmaril's Wasm grammar `Name`. -/
theorem sound_name : Sound Name name := sound_name'.mono fun _ _ h => name_spec_name h

theorem complete_name : Complete Spec.name name := by
  intro l str bs st i hg hl hs hseg
  obtain ⟨nb, rfl, hu⟩ := hg
  have hb : i + (nb ++ str.toUTF8.data.toList).length ≤ bs.size := Nat.le_trans hl hs
  obtain ⟨s1, s2⟩ := seg_split bs hb hseg
  simp only [List.length_append] at hl ⊢
  have hlen : str.toUTF8.data.toList.length = str.toUTF8.size := (size_eq_length _).symm
  rw [hlen] at hl s2 ⊢
  have hcu := complete_uN 32 hu (by omega) hs s1
  unfold name count utf8
  simp only [u32, hcu, show str.toUTF8.size ≤ st - (i + nb.length) by omega, ↓reduceIte,
    show i + nb.length + str.toUTF8.size ≤ st by omega]
  have hx : bs.extract (i + nb.length) (i + nb.length + str.toUTF8.size) = str.toUTF8 := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [seg_extract, s2]
  rw [hx, fromUTF8_toUTF8, Nat.add_assoc]

/-! ## Tagged unions -/

theorem sound_tagged (what : String) {k : UInt8 → Option (Parser α)}
    {K : UInt8 → Option (Bytes → α → Prop)}
    (hk : ∀ b p, k b = some p → ∃ G, K b = some G ∧ Sound G p) :
    Sound (Spec.tagged K) (tagged what k) := by
  intro bs st i a j hi hs h
  unfold tagged at h
  split at h
  · next b j' hb =>
    obtain ⟨h1, h2, h3⟩ := sound_byte hi hs hb
    split at h
    · next p hp =>
      obtain ⟨G, hG, hsG⟩ := hk b p hp
      obtain ⟨h4, h5, h6⟩ := hsG h2 hs h
      refine ⟨by omega, h5, b, _, G, ?_, hG, h6⟩
      rw [seg_append bs h1 h4, h3]; rfl
    · cases h
  · cases h

theorem complete_tagged (what : String) {k : UInt8 → Option (Parser α)}
    {K : UInt8 → Option (Bytes → α → Prop)}
    (hk : ∀ b G, K b = some G → ∃ p, k b = some p ∧ Complete G p) :
    Complete (Spec.tagged K) (tagged what k) := by
  intro l a bs st i hg hl hs hseg
  obtain ⟨b, l', G, rfl, hK, hG⟩ := hg
  have hb : i + ([b] ++ l').length ≤ bs.size := Nat.le_trans hl hs
  obtain ⟨s1, s2⟩ := seg_split bs (l₁ := [b]) hb hseg
  simp only [List.length_cons, List.length_nil] at hl s1 s2 ⊢
  have hb1 := complete_byte (l := [b]) (a := b) rfl (by simp; omega) hs s1
  simp only [List.length_cons, List.length_nil] at hb1
  obtain ⟨p, hp, hcp⟩ := hk b G hK
  unfold tagged
  rw [hb1]
  simp only [hp]
  have := hcp hG (i := i + (0 + 1)) (by omega) hs (by simpa using s2)
  rw [this]; congr 1; omega

namespace Grammar

/-- A tagged choice between lawful grammars is lawful. -/
theorem Lawful.tagged {what : String} {k : UInt8 → Option (Grammar α)}
    (hk : ∀ b g, k b = some g → g.Lawful) : (tagged what k).Lawful where
  sound := sound_tagged what fun b p hp => by
    cases h : k b with
    | none => simp [h] at hp
    | some g =>
      have := hk b g h
      simp only [h, Option.map_some, Option.some.injEq] at hp ⊢
      exact ⟨_, rfl, hp ▸ g.sound⟩
  complete := complete_tagged what fun b G hG => by
    cases h : k b with
    | none => simp [h] at hG
    | some g =>
      have := hk b g h
      simp only [h, Option.map_some, Option.some.injEq] at hG ⊢
      exact ⟨_, rfl, hG ▸ g.complete⟩

theorem tagged_G (what : String) {k : UInt8 → Option (Grammar α)} {b : UInt8} {g : Grammar α}
    (hk : k b = some g) {l : Bytes} {a : α} (h : g.G l a) : (tagged what k).G (b :: l) a :=
  ⟨b, l, g.G, rfl, by simp [hk], h⟩

instance lawful_uN (N : Nat) : (uN N).Lawful := ⟨sound_uN N, complete_uN N⟩

instance lawful_u32 : u32.Lawful := lawful_uN 32

instance lawful_sN (N : Nat) : (sN N).Lawful := ⟨sound_sN N, complete_sN N⟩

instance lawful_le (n : Nat) : (le n).Lawful := ⟨sound_le n, complete_le n⟩

instance lawful_name : name.Lawful := ⟨sound_name', complete_name⟩

instance lawful_vec (g : Grammar α) (hne : NonEmpty g.G) [g.Lawful] : (vec g hne).Lawful :=
  ⟨sound_vec g.sound, complete_vec g.complete hne⟩

instance lawful_many (n : Nat) (g : Grammar α) [g.Lawful] : (many n g).Lawful :=
  ⟨sound_many g.sound n, complete_many g.complete n⟩

instance lawful_sizedItems (g : Grammar α) (hne : NonEmpty g.G) [g.Lawful] :
    (sizedItems g hne).Lawful :=
  @lawful_bind _ _ u32 _ _ fun n =>
    ⟨(sound_untilEnd g.sound).sized n, complete_sized_untilEnd g.complete hne n⟩

instance lawful_sizedBy (g : Grammar α) [g.Lawful] : (sizedBy g).Lawful :=
  inferInstanceAs (u32.bind fun n => sized n g).Lawful

theorem uN_G {N : Nat} {l : Bytes} {n : Nat} (h : Silmaril.Wasm.Binary.UN N l n) : (uN N).G l n := h

theorem name_G (s : String) {nb : Bytes} (h : U32 nb s.toUTF8.size) :
    name.G (nb ++ s.toUTF8.data.toList) s := ⟨nb, rfl, h⟩

theorem vec_G {g : Grammar α} {hne : NonEmpty g.G} {nb b : Bytes} {xs : List α}
    (hn : U32 nb xs.length) (hs : Seq g.G b xs) : (vec g hne).G (nb ++ b) xs := Vec.mk hn hs

theorem sizedBy_G {g : Grammar α} {nb l : Bytes} {a : α} (hn : U32 nb l.length) (h : g.G l a) :
    (sizedBy g).G (nb ++ l) a := bind_G (g := u32) hn (sized_G h rfl)

theorem sizedItems_G {g : Grammar α} {hne : NonEmpty g.G} {nb l : Bytes} {xs : List α}
    (hn : U32 nb l.length) (h : Seq g.G l xs) : (sizedItems g hne).G (nb ++ l) xs :=
  bind_G (g := u32) hn ⟨rfl, h⟩

end Grammar

end Silmaril.Parse.ByteParse
