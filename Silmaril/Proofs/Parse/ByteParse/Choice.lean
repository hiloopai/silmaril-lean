module

public import Silmaril.Proofs.Parse.ByteParse.Encode

/-!
# Lookahead choice, filters, literals and non-emptiness

* `choice pred p q`: one byte of lookahead between two grammars whose
  encodings start with bytes on either side of `pred`;
* `filterMap`: partial post-processing (range checks);
* `lit l`: exactly the bytes `l` (magic numbers, preambles);
* `NonEmpty` facts for the combinators, as needed by `vec` and `items`.
-/

@[expose] public section

namespace Silmaril.Parse.ByteParse

open Silmaril.Wasm.Binary (UN SN U32 Seq)

variable {α β : Type}

theorem sound_choice {pred : UInt8 → Bool} {G H : Bytes → α → Prop} {p q : Parser α}
    (hp : Sound G p) (hq : Sound H q) : Sound (fun l a => G l a ∨ H l a) (choice pred p q) := by
  intro bs st i a j hi hs h
  unfold choice at h
  split at h
  · split at h
    · split at h
      · obtain ⟨h1, h2, h3⟩ := hp hi hs h; exact ⟨h1, h2, .inl h3⟩
      · obtain ⟨h1, h2, h3⟩ := hq hi hs h; exact ⟨h1, h2, .inr h3⟩
    · cases h
  · cases h

theorem choice_apply {pred : UInt8 → Bool} {p q : Parser α} {bs : ByteArray} {st i : Nat}
    (hst : i < st) (hsz : i < bs.size) :
    choice pred p q bs st i = if pred bs[i] then p bs st i else q bs st i := by
  simp only [choice, hst, hsz, ↓reduceDIte]

/-- The first byte of a non-empty encoding in the window. -/
theorem seg_first {bs : ByteArray} {st i : Nat} {b : UInt8} {l : Bytes}
    (hl : i + (b :: l).length ≤ st) (hs : st ≤ bs.size)
    (hseg : seg bs i (i + (b :: l).length) = b :: l) :
    ∃ hsz : i < bs.size, i < st ∧ bs[i] = b := by
  obtain ⟨hsz, hb, -⟩ := seg_head (Nat.le_trans hl hs) hseg
  exact ⟨hsz, by simp only [List.length_cons] at hl; omega, hb⟩

theorem complete_choice {pred : UInt8 → Bool} {G H : Bytes → α → Prop} {p q : Parser α}
    (hp : Complete G p) (hq : Complete H q) (hG : StartsWith (fun b => pred b = true) G)
    (hH : StartsWith (fun b => pred b = false) H) :
    Complete (fun l a => G l a ∨ H l a) (choice pred p q) := by
  intro l a bs st i hg hl hs hseg
  rcases hg with hg | hg
  · obtain ⟨b, l', hlb, hb⟩ : ∃ b l', l = b :: l' ∧ pred b = true := hG hg
    obtain ⟨hsz, hst, e⟩ := seg_first (hlb ▸ hl) hs (hlb ▸ hseg)
    have hpred : pred bs[i] = true := e ▸ hb
    simp only [choice_apply hst hsz, hpred, ↓reduceIte]
    exact hp hg hl hs hseg
  · obtain ⟨b, l', hlb, hb⟩ : ∃ b l', l = b :: l' ∧ pred b = false := hH hg
    obtain ⟨hsz, hst, e⟩ := seg_first (hlb ▸ hl) hs (hlb ▸ hseg)
    have hpred : pred bs[i] = false := e ▸ hb
    simp only [choice_apply hst hsz, hpred, Bool.false_eq_true, ↓reduceIte]
    exact hq hg hl hs hseg

theorem sound_filterMap (what : String) (f : α → Option β) {G : Bytes → α → Prop} {p : Parser α}
    (hp : Sound G p) : Sound (fun l b => ∃ a, G l a ∧ f a = some b) (filterMap what f p) := by
  intro bs st i b j hi hs h
  unfold filterMap at h
  split at h
  · next a k hk =>
    split at h
    · next b' hb => cases h; obtain ⟨h1, h2, h3⟩ := hp hi hs hk; exact ⟨h1, h2, a, h3, hb⟩
    · cases h
  · cases h

theorem complete_filterMap (what : String) (f : α → Option β) {G : Bytes → α → Prop}
    {p : Parser α} (hp : Complete G p) :
    Complete (fun l b => ∃ a, G l a ∧ f a = some b) (filterMap what f p) := by
  intro l b bs st i hg hl hs hseg
  obtain ⟨a, hg, hf⟩ := hg
  unfold filterMap
  rw [hp hg hl hs hseg]
  simp only [hf]

namespace Grammar

instance lawful_choice (pred : UInt8 → Bool) (g h : Grammar α) [g.Lawful] [h.Lawful]
    (hg : StartsWith (fun b => pred b = true) g.G) (hh : StartsWith (fun b => pred b = false) h.G) :
    (choice pred g h hg hh).Lawful :=
  ⟨sound_choice g.sound h.sound, complete_choice g.complete h.complete hg hh⟩

instance lawful_filterMap (what : String) (f : α → Option β) (g : Grammar α) [g.Lawful] :
    (filterMap what f g).Lawful :=
  ⟨sound_filterMap what f g.sound, complete_filterMap what f g.complete⟩

instance lawful_then (g : Grammar Unit) (h : Grammar α) [g.Lawful] [h.Lawful] :
    (then_ g h).Lawful :=
  inferInstanceAs (g.bind fun _ => h).Lawful

instance lawful_ite {c : Prop} [Decidable c] (g h : Grammar α) [g.Lawful] [h.Lawful] :
    (if c then g else h).Lawful := by
  split <;> assumption

instance lawful_lit : ∀ l : List UInt8, (lit l).Lawful
  | [] => inferInstanceAs (pure ()).Lawful
  | b :: bs => haveI := lawful_lit bs; inferInstanceAs ((expect "literal" b).then_ (lit bs)).Lawful

theorem choice_G_left {pred : UInt8 → Bool} {g h : Grammar α} {hg hh} {l : Bytes} {a : α}
    (H : g.G l a) : (choice pred g h hg hh).G l a := .inl H

theorem choice_G_right {pred : UInt8 → Bool} {g h : Grammar α} {hg hh} {l : Bytes} {a : α}
    (H : h.G l a) : (choice pred g h hg hh).G l a := .inr H

theorem filterMap_G {what : String} {f : α → Option β} {g : Grammar α} {l : Bytes} {a : α} {b : β}
    (H : g.G l a) (hf : f a = some b) : (filterMap what f g).G l b := ⟨a, H, hf⟩

theorem then_G {g : Grammar Unit} {h : Grammar α} {l₁ l₂ : Bytes} {a : α}
    (h₁ : g.G l₁ ()) (h₂ : h.G l₂ a) : (then_ g h).G (l₁ ++ l₂) a := bind_G h₁ h₂

theorem lit_G : ∀ l : List UInt8, (lit l).G l ()
  | [] => pure_G
  | b :: bs => by
    have := then_G (g := expect "literal" b) (h := lit bs) (expect_G "literal" b) (lit_G bs)
    simpa [lit] using this

end Grammar

end Silmaril.Parse.ByteParse
