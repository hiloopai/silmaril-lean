module

public import Silmaril.Parse.ByteParse.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Cursor parsers: segments, monad and combinator laws

* segments of the input: `seg_append`, `seg_cons`, `length_seg`, `seg_split`;
* the computation rules of `pure`, `>>=`, `<$>` on a cursor (`bind_apply`, …);
* `Sound`/`Complete` for `pure`, `bind`, `map`, `byte`, `expect`, `span`,
  `bytes`, `sized`, `opt`, and monotonicity in the grammar.
-/

@[expose] public section

namespace Silmaril.Parse.ByteParse

open Silmaril.Wasm.Binary (Seq Vec UN U32)

variable {α β : Type}

/-! ## Segments -/

theorem size_eq_length (bs : ByteArray) : bs.size = bs.data.toList.length := by
  simp only [ByteArray.size, Array.length_toList]

theorem length_seg (bs : ByteArray) (i j : Nat) :
    (seg bs i j).length = min (j - i) (bs.size - i) := by
  simp only [seg, List.extract, List.length_take, List.length_drop, size_eq_length]

theorem seg_self (bs : ByteArray) (i : Nat) : seg bs i i = [] := by
  simp [seg, List.extract]

theorem seg_append (bs : ByteArray) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    seg bs i k = seg bs i j ++ seg bs j k := by
  simp only [seg, List.extract]
  have : k - i = (j - i) + (k - j) := by omega
  rw [this, List.take_add, List.drop_drop]
  congr 3
  omega

theorem seg_cons (bs : ByteArray) {i k : Nat} (hi : i < bs.size) (hk : i < k) :
    seg bs i k = bs[i] :: seg bs (i + 1) k := by
  rw [seg_append bs (Nat.le_succ i) hk]
  have h1 : seg bs i (i + 1) = [bs[i]] := by
    simp only [seg, List.extract, Nat.add_sub_cancel_left]
    rw [List.drop_eq_getElem_cons (by rw [← size_eq_length]; exact hi)]
    simp [ByteArray.getElem_eq_getElem_data]
  rw [h1]; rfl

/-- A segment that is a concatenation splits at the first length. -/
theorem seg_split (bs : ByteArray) {i : Nat} {l₁ l₂ : Bytes}
    (hb : i + (l₁ ++ l₂).length ≤ bs.size)
    (h : seg bs i (i + (l₁ ++ l₂).length) = l₁ ++ l₂) :
    seg bs i (i + l₁.length) = l₁ ∧
      seg bs (i + l₁.length) (i + l₁.length + l₂.length) = l₂ := by
  rw [List.length_append] at hb h
  rw [seg_append bs (i := i) (j := i + l₁.length) (by omega) (by omega)] at h
  rw [← Nat.add_assoc] at h
  refine List.append_inj h ?_
  rw [length_seg]; omega

theorem seg_split_right (bs : ByteArray) {i : Nat} {l₁ l₂ : Bytes}
    (hb : i + (l₁ ++ l₂).length ≤ bs.size)
    (h : seg bs i (i + (l₁ ++ l₂).length) = l₁ ++ l₂) :
    seg bs (i + l₁.length) (i + l₁.length + l₂.length) = l₂ := (seg_split bs hb h).2

theorem seg_split_left (bs : ByteArray) {i : Nat} {l₁ l₂ : Bytes}
    (hb : i + (l₁ ++ l₂).length ≤ bs.size)
    (h : seg bs i (i + (l₁ ++ l₂).length) = l₁ ++ l₂) :
    seg bs i (i + l₁.length) = l₁ := (seg_split bs hb h).1

theorem seg_extract (bs : ByteArray) (i j : Nat) :
    (bs.extract i j).data.toList = seg bs i j := by
  simp [seg]

theorem seg_ofList (l : Bytes) : seg ⟨l.toArray⟩ 0 l.length = l := by
  simp [seg, List.extract]

theorem seg_ofList_append (l r : Bytes) : seg ⟨(l ++ r).toArray⟩ 0 l.length = l := by
  simp [seg, List.extract]

theorem size_ofList (l : Bytes) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  simp only [ByteArray.size, List.size_toArray]

/-! ## Computation rules -/

@[simp] theorem pure_apply (a : α) (bs : ByteArray) (st i : Nat) :
    (pure a : Parser α) bs st i = .ok a i := rfl

theorem bind_apply (p : Parser α) (f : α → Parser β) (bs : ByteArray) (st i : Nat) :
    (p >>= f) bs st i =
      (match p bs st i with
       | .ok a j => f a bs st j
       | .err e => .err e) := rfl

theorem map_apply (f : α → β) (p : Parser α) (bs : ByteArray) (st i : Nat) :
    (f <$> p) bs st i =
      (match p bs st i with
       | .ok a j => .ok (f a) j
       | .err e => .err e) := rfl

theorem Parser.map_apply' (f : α → β) (p : Parser α) (bs : ByteArray) (st i : Nat) :
    Parser.map f p bs st i =
      (match p bs st i with
       | .ok a j => .ok (f a) j
       | .err e => .err e) := rfl

theorem bind_ok {p : Parser α} {f : α → Parser β} {bs : ByteArray} {st i : Nat} {b : β} {k : Nat}
    (h : (p >>= f) bs st i = .ok b k) : ∃ a j, p bs st i = .ok a j ∧ f a bs st j = .ok b k := by
  rw [bind_apply] at h
  split at h
  · next a j hp => exact ⟨a, j, hp, h⟩
  · cases h

theorem map_ok {p : Parser α} {f : α → β} {bs : ByteArray} {st i : Nat} {b : β} {k : Nat}
    (h : Parser.map f p bs st i = .ok b k) : ∃ a, p bs st i = .ok a k ∧ f a = b := by
  rw [Parser.map_apply'] at h
  split at h
  · next a j hp => cases h; exact ⟨a, hp, rfl⟩
  · cases h

/-! ## Monotonicity -/

theorem Sound.mono {G G' : Bytes → α → Prop} {p : Parser α} (h : Sound G p)
    (hG : ∀ l a, G l a → G' l a) : Sound G' p := by
  intro bs st i a j hi hs hp
  obtain ⟨h1, h2, h3⟩ := h hi hs hp
  exact ⟨h1, h2, hG _ _ h3⟩

theorem Complete.anti {G G' : Bytes → α → Prop} {p : Parser α} (h : Complete G p)
    (hG : ∀ l a, G' l a → G l a) : Complete G' p :=
  fun _ _ _ _ _ hg => h (hG _ _ hg)

theorem Sound.congr {p q : Parser α} {G : Bytes → α → Prop} (h : Sound G p) (e : p = q) :
    Sound G q := e ▸ h

theorem Complete.congr {p q : Parser α} {G : Bytes → α → Prop} (h : Complete G p) (e : p = q) :
    Complete G q := e ▸ h

/-! ## `pure`, `bind`, `map` -/

theorem sound_pure (a : α) : Sound (Spec.pure a) (pure a) := by
  intro bs st i b j hi _ h
  cases h
  exact ⟨Nat.le_refl _, hi, seg_self bs i, rfl⟩

theorem complete_pure (a : α) : Complete (Spec.pure a) (pure a) := by
  intro l b bs st i hg _ _ _
  obtain ⟨rfl, rfl⟩ := hg
  rfl

theorem Sound.bind {G : Bytes → α → Prop} {H : α → Bytes → β → Prop} {p : Parser α}
    {f : α → Parser β} (hp : Sound G p) (hf : ∀ a, Sound (H a) (f a)) :
    Sound (Spec.bind G H) (p >>= f) := by
  intro bs st i b k hi hs h
  obtain ⟨a, j, h1, h2⟩ := bind_ok h
  obtain ⟨hij, hjs, hg⟩ := hp hi hs h1
  obtain ⟨hjk, hks, hh⟩ := hf a hjs hs h2
  exact ⟨Nat.le_trans hij hjk, hks, _, _, a, seg_append bs hij hjk, hg, hh⟩

theorem Complete.bind {G : Bytes → α → Prop} {H : α → Bytes → β → Prop} {p : Parser α}
    {f : α → Parser β} (hp : Complete G p) (hf : ∀ a, Complete (H a) (f a)) :
    Complete (Spec.bind G H) (p >>= f) := by
  intro l b bs st i hg hl hs hseg
  obtain ⟨l₁, l₂, a, rfl, h1, h2⟩ := hg
  have hb : i + (l₁ ++ l₂).length ≤ bs.size := Nat.le_trans hl hs
  obtain ⟨s1, s2⟩ := seg_split bs hb hseg
  simp only [List.length_append] at hl ⊢
  rw [bind_apply, hp h1 (by omega) hs s1]
  rw [← Nat.add_assoc]
  exact hf a h2 (by omega) hs s2

theorem Sound.map {G : Bytes → α → Prop} {p : Parser α} (f : α → β) (hp : Sound G p) :
    Sound (Spec.map f G) (Parser.map f p) := by
  intro bs st i b k hi hs h
  obtain ⟨a, h1, rfl⟩ := map_ok h
  obtain ⟨h2, h3, h4⟩ := hp hi hs h1
  exact ⟨h2, h3, a, h4, rfl⟩

theorem Complete.map {G : Bytes → α → Prop} {p : Parser α} (f : α → β) (hp : Complete G p) :
    Complete (Spec.map f G) (Parser.map f p) := by
  intro l b bs st i hg hl hs hseg
  obtain ⟨a, h1, rfl⟩ := hg
  rw [Parser.map_apply', hp h1 hl hs hseg]

/-! ## Bytes -/

theorem byte_apply (bs : ByteArray) (st i : Nat) (hs : i < st) (h : i < bs.size) :
    byte bs st i = .ok bs[i] (i + 1) := by
  simp [byte, hs, h]

theorem sound_byte : Sound Spec.byte byte := by
  intro bs st i a j hi hs hp
  unfold byte at hp
  split at hp
  · split at hp
    · next h1 h2 =>
      cases hp
      refine ⟨Nat.le_succ i, h1, ?_⟩
      rw [seg_cons bs h2 (Nat.lt_succ_self i), seg_self]; rfl
    · cases hp
  · cases hp

theorem complete_byte : Complete Spec.byte byte := by
  intro l a bs st i hg hl hs hseg
  subst hg
  simp only [List.length_singleton] at hl hseg ⊢
  have h2 : i < bs.size := by omega
  rw [byte_apply bs st i (by omega) h2]
  rw [seg_cons bs h2 (by omega), seg_self] at hseg
  cases hseg; rfl

theorem sound_expect (what : String) (b : UInt8) :
    Sound (fun l (_ : Unit) => l = [b]) (expect what b) := by
  intro bs st i a j hi hs hp
  unfold expect at hp
  split at hp
  · split at hp
    · split at hp
      · next h1 h2 h3 =>
        cases hp
        refine ⟨Nat.le_succ i, h1, ?_⟩
        rw [seg_cons bs h2 (Nat.lt_succ_self i), seg_self, h3]
      · cases hp
    · cases hp
  · cases hp

theorem complete_expect (what : String) (b : UInt8) :
    Complete (fun l (_ : Unit) => l = [b]) (expect what b) := by
  intro l a bs st i hg hl hs hseg
  subst hg
  simp only [List.length_singleton] at hl hseg ⊢
  have h2 : i < bs.size := by omega
  rw [seg_cons bs h2 (by omega), seg_self] at hseg
  injection hseg with hb
  simp [expect, show i < st by omega, h2, hb]

theorem sound_span (n : Nat) :
    Sound (fun l (r : Nat × Nat) => l.length = n ∧ r.2 = r.1 + n) (span n) := by
  intro bs st i a j hi hs hp
  unfold span at hp
  split at hp
  · cases hp
    refine ⟨by omega, by omega, ?_, rfl⟩
    rw [length_seg]; omega
  · cases hp

/-- The bytes `bytes n` returns are those it consumed. -/
theorem sound_bytes (n : Nat) :
    Sound (fun l (b : ByteArray) => l = b.data.toList ∧ l.length = n) (bytes n) := by
  intro bs st i a j hi hs hp
  unfold bytes at hp
  split at hp
  · cases hp
    refine ⟨by omega, by omega, (seg_extract bs _ _).symm, ?_⟩
    rw [length_seg]; omega
  · cases hp

theorem complete_bytes (n : Nat) :
    Complete (fun l (b : ByteArray) => l = b.data.toList ∧ l.length = n) (bytes n) := by
  intro l a bs st i hg hl hs hseg
  obtain ⟨rfl, rfl⟩ := hg
  simp only [ByteParse.bytes, hl, ↓reduceIte]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [seg_extract, hseg]

/-! ## Sized windows -/

theorem sized_apply {p : Parser α} (n : Nat) (bs : ByteArray) (st i : Nat) :
    sized n p bs st i =
      if i + n ≤ st then
        match p bs (i + n) i with
        | .ok a j => if j = i + n then .ok a j else .err ⟨j, .size n (j - i)⟩
        | .err e => .err e
      else .err ⟨i, .eof⟩ := rfl

theorem Sound.sized {G : Bytes → α → Prop} {p : Parser α} (n : Nat) (hp : Sound G p) :
    Sound (Spec.sized n G) (sized n p) := by
  intro bs st i a j hi hs h
  rw [sized_apply] at h
  split at h
  · next hn =>
    split at h
    · next a' j' hp' =>
      split at h
      · next hj =>
        cases h
        obtain ⟨h1, _, h3⟩ := hp (by omega) (by omega) hp'
        refine ⟨h1, by omega, ?_, h3⟩
        rw [length_seg]; omega
      · cases h
    · cases h
  · cases h

theorem Complete.sized {G : Bytes → α → Prop} {p : Parser α} (n : Nat) (hp : Complete G p) :
    Complete (Spec.sized n G) (sized n p) := by
  intro l a bs st i hg hl hs hseg
  obtain ⟨rfl, hg⟩ := hg
  simp only [sized_apply, hl, ↓reduceIte, hp hg (Nat.le_refl _) (by omega) hseg]

theorem Complete.atEnd {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p) :
    CompleteAtEnd G p :=
  fun _ _ _ _ hg hs hseg => hp hg (Nat.le_refl _) hs hseg

theorem CompleteAtEnd.sized {G : Bytes → α → Prop} {p : Parser α} (n : Nat)
    (hp : CompleteAtEnd G p) : Complete (Spec.sized n G) (sized n p) := by
  intro l a bs st i hg hl hs hseg
  obtain ⟨rfl, hg⟩ := hg
  simp only [sized_apply, hl, ↓reduceIte, hp hg (by omega) hseg]

theorem sound_eoi : Sound (fun l (_ : Unit) => l = []) eoi := by
  intro bs st i a j hi hs h
  unfold eoi at h
  split at h
  · cases h; exact ⟨Nat.le_refl _, hi, seg_self bs i⟩
  · cases h

/-! ## Options -/

theorem Sound.opt {G : Bytes → α → Prop} {p : Parser α} (what : String) (hp : Sound G p) :
    Sound (Spec.opt G) (opt what p) := by
  intro bs st i a j hi hs h
  unfold ByteParse.opt at h
  split at h
  · next j' hb =>
    cases h
    obtain ⟨h1, h2, h3⟩ := sound_byte hi hs hb
    exact ⟨h1, h2, h3⟩
  · next j' hb =>
    obtain ⟨h1, h2, h3⟩ := sound_byte hi hs hb
    obtain ⟨a', h4, rfl⟩ := map_ok h
    obtain ⟨h5, h6, h7⟩ := hp h2 hs h4
    refine ⟨by omega, h6, _, ?_, h7⟩
    rw [seg_append bs h1 h5, h3]; rfl
  · cases h
  · cases h

theorem Complete.opt {G : Bytes → α → Prop} {p : Parser α} (what : String) (hp : Complete G p) :
    Complete (Spec.opt G) (opt what p) := by
  intro l a bs st i hg hl hs hseg
  cases a with
  | none =>
    subst hg
    have hb := complete_byte (l := [0]) (a := 0) rfl hl hs hseg
    simp only [ByteParse.opt, hb]
  | some a =>
    obtain ⟨l', rfl, hg⟩ := hg
    have hb : i + ([1] ++ l').length ≤ bs.size := Nat.le_trans hl hs
    obtain ⟨s1, s2⟩ := seg_split bs (l₁ := [1]) hb hseg
    simp only [List.length_cons, List.length_nil] at hl s1 s2 ⊢
    have hb1 := complete_byte (l := [1]) (a := 1) rfl (by simp; omega) hs s1
    have hp1 := hp hg (i := i + 1) (by omega) hs (by simpa [Nat.zero_add] using s2)
    simp only [List.length_cons, List.length_nil] at hb1
    simp only [ByteParse.opt, hb1, Parser.map_apply', hp1]
    congr 1
    omega

/-! ## Running on a whole input -/

theorem Sound.runAll {G : Bytes → α → Prop} {p : Parser α} (hp : Sound G p) {bs : ByteArray}
    {a : α} (h : runAll p bs = .ok a) : G bs.data.toList a := by
  unfold ByteParse.runAll at h
  split at h
  · next a' j hp' =>
    split at h
    · next hj =>
      cases h
      obtain ⟨_, _, h3⟩ := hp (Nat.zero_le _) (Nat.le_refl _) hp'
      subst hj
      have : seg bs 0 bs.size = bs.data.toList := by
        simp only [seg, List.extract, size_eq_length, List.drop_zero, Nat.sub_zero, List.take_length]
      rwa [this] at h3
    · cases h
  · cases h

/-- Round trip: a parser complete for `G` reads any `G`-encoding back, whatever
follows it. -/
theorem Complete.run_append {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p)
    {l : Bytes} {a : α} (hg : G l a) (rest : Bytes) :
    p ⟨(l ++ rest).toArray⟩ (l ++ rest).length 0 = .ok a l.length := by
  have := hp (bs := ⟨(l ++ rest).toArray⟩) (st := (l ++ rest).length) (i := 0) hg
    (by simp) (by rw [size_ofList]) (by simp)
  simpa using this

theorem Complete.runAll {G : Bytes → α → Prop} {p : Parser α} (hp : Complete G p)
    {l : Bytes} {a : α} (hg : G l a) : runAll p ⟨l.toArray⟩ = .ok a := by
  have := hp.run_append hg []
  simp only [List.append_nil] at this
  unfold ByteParse.runAll
  rw [size_ofList, this]
  simp

/-! ## Grammars -/

namespace Grammar

/-- The parser of a lawful grammar is sound. -/
theorem sound (g : Grammar α) [h : g.Lawful] : Sound g.G g.parse := h.sound

/-- The parser of a lawful grammar is complete. -/
theorem complete (g : Grammar α) [h : g.Lawful] : Complete g.G g.parse := h.complete

instance lawful_pure (a : α) : (pure a).Lawful := ⟨sound_pure a, complete_pure a⟩

instance lawful_bind (g : Grammar α) (h : α → Grammar β) [g.Lawful] [∀ a, (h a).Lawful] :
    (g.bind h).Lawful :=
  ⟨g.sound.bind fun a => (h a).sound, g.complete.bind fun a => (h a).complete⟩

instance lawful_map (f : α → β) (g : Grammar α) [g.Lawful] : (g.map f).Lawful :=
  ⟨g.sound.map f, g.complete.map f⟩

instance lawful_byte : byte.Lawful := ⟨sound_byte, complete_byte⟩

instance lawful_expect (what : String) (b : UInt8) : (expect what b).Lawful :=
  ⟨sound_expect what b, complete_expect what b⟩

instance lawful_bytes (n : Nat) : (bytes n).Lawful := ⟨sound_bytes n, complete_bytes n⟩

instance lawful_sized (n : Nat) (g : Grammar α) [g.Lawful] : (sized n g).Lawful :=
  ⟨g.sound.sized n, g.complete.sized n⟩

instance lawful_opt (what : String) (g : Grammar α) [g.Lawful] : (opt what g).Lawful :=
  ⟨g.sound.opt what, g.complete.opt what⟩

instance lawful_seq (g : Grammar α) (h : Grammar β) [g.Lawful] [h.Lawful] : (g.seq h).Lawful :=
  inferInstanceAs (g.bind fun a => h.map fun b => (a, b)).Lawful

theorem pure_G {a : α} : (pure a).G [] a := ⟨rfl, rfl⟩

theorem bind_G {g : Grammar α} {h : α → Grammar β} {l₁ l₂ : Bytes} {a : α} {b : β}
    (h₁ : g.G l₁ a) (h₂ : (h a).G l₂ b) : (g.bind h).G (l₁ ++ l₂) b :=
  ⟨l₁, l₂, a, rfl, h₁, h₂⟩

theorem map_G {f : α → β} {g : Grammar α} {l : Bytes} {a : α} (h : g.G l a) :
    (g.map f).G l (f a) := ⟨a, h, rfl⟩

theorem seq_G {g : Grammar α} {h : Grammar β} {l₁ l₂ : Bytes} {a : α} {b : β}
    (h₁ : g.G l₁ a) (h₂ : h.G l₂ b) : (g.seq h).G (l₁ ++ l₂) (a, b) :=
  bind_G h₁ (map_G h₂)

theorem byte_G (b : UInt8) : byte.G [b] b := rfl

theorem expect_G (what : String) (b : UInt8) : (expect what b).G [b] () := rfl

theorem bytes_G (b : ByteArray) : (bytes b.size).G b.data.toList b := ⟨rfl, (size_eq_length b).symm⟩

theorem sized_G {n : Nat} {g : Grammar α} {l : Bytes} {a : α} (h : g.G l a) (hn : l.length = n) :
    (sized n g).G l a := ⟨hn, h⟩

theorem opt_none_G (what : String) (g : Grammar α) : (opt what g).G [0x00] none := rfl

theorem opt_some_G (what : String) {g : Grammar α} {l : Bytes} {a : α} (h : g.G l a) :
    (opt what g).G (0x01 :: l) (some a) := ⟨l, rfl, h⟩

/-- Round trip for a grammar and an encoder that the grammar accepts. -/
theorem roundTrip (g : Grammar α) [g.Lawful] {enc : α → Bytes} {a : α} (h : g.G (enc a) a) (rest : Bytes) :
    g.parse ⟨(enc a ++ rest).toArray⟩ (enc a ++ rest).length 0 = .ok a (enc a).length :=
  g.complete.run_append h rest

/-- Unambiguity: the parse of any encoding is determined by its bytes. -/
theorem functional (g : Grammar α) [g.Lawful] {l : Bytes} {a a' : α} (h : g.G l a) (h' : g.G l a') :
    a = a' := by
  have e1 := g.complete.run_append h []
  have e2 := g.complete.run_append h' []
  rw [e1] at e2
  cases e2; rfl

end Grammar

end Silmaril.Parse.ByteParse
