module

public import Silmaril.Proofs.Parse.ByteParse.Loops

/-!
# Grammars that run to the end of their window

Some productions are delimited by their enclosing window rather than by their
own bytes: the trailing bytes of a custom section, an embedded module, the
sections of a module or component. Their parsers are only complete when the
window ends exactly after the encoding (`CompleteAtEnd`). `GrammarE` bundles
such a parser; `GrammarE.sized` turns it back into a `Grammar` under a size
prefix, and `GrammarE.runAll` reads a whole input.
-/

@[expose] public section

namespace Silmaril.Parse.ByteParse

open Silmaril.Wasm.Binary (Seq U32)

variable {α β : Type}

theorem Complete.bindAtEnd {G : Bytes → α → Prop} {H : α → Bytes → β → Prop} {p : Parser α}
    {f : α → Parser β} (hp : Complete G p) (hf : ∀ a, CompleteAtEnd (H a) (f a)) :
    CompleteAtEnd (Spec.bind G H) (p >>= f) := by
  intro l b bs i hg hs hseg
  obtain ⟨l₁, l₂, a, rfl, h1, h2⟩ := hg
  obtain ⟨s1, s2⟩ := seg_split bs hs hseg
  simp only [List.length_append] at hs ⊢
  rw [bind_apply, hp h1 (by omega) hs s1]
  have := hf a h2 (i := i + l₁.length) (by omega) s2
  rw [Nat.add_assoc] at this
  exact this

theorem CompleteAtEnd.map {G : Bytes → α → Prop} {p : Parser α} (f : α → β)
    (hp : CompleteAtEnd G p) : CompleteAtEnd (Spec.map f G) (Parser.map f p) := by
  intro l b bs i hg hs hseg
  obtain ⟨a, h1, rfl⟩ := hg
  rw [Parser.map_apply', hp h1 hs hseg]

theorem sound_rest : Sound (fun l (b : ByteArray) => l = b.data.toList) rest := by
  intro bs st i a j hi hs h
  unfold ByteParse.rest at h
  simp only [hi, ↓reduceIte] at h
  cases h; exact ⟨hi, Nat.le_refl _, (seg_extract bs _ _).symm⟩

theorem completeAtEnd_rest : CompleteAtEnd (fun l (b : ByteArray) => l = b.data.toList) rest := by
  intro l a bs i hg hs hseg
  subst hg
  simp only [rest, show i ≤ i + a.data.toList.length by omega, ↓reduceIte]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [seg_extract, hseg]

theorem CompleteAtEnd.runAll {G : Bytes → α → Prop} {p : Parser α} (hp : CompleteAtEnd G p)
    {l : Bytes} {a : α} (hg : G l a) : runAll p ⟨l.toArray⟩ = .ok a := by
  have := hp (bs := ⟨l.toArray⟩) (i := 0) hg (by rw [size_ofList]; omega) (by simp)
  unfold ByteParse.runAll
  rw [size_ofList]
  simp only [Nat.zero_add] at this
  rw [this]; simp

namespace GrammarE

/-- The parser of a lawful grammar is sound. -/
theorem sound (g : GrammarE α) [h : g.Lawful] : Sound g.G g.parse := h.sound

/-- The parser of a lawful grammar is complete up to the end of its window. -/
theorem complete (g : GrammarE α) [h : g.Lawful] : CompleteAtEnd g.G g.parse := h.complete

instance lawful_ofGrammar (g : Grammar α) [g.Lawful] : (ofGrammar g).Lawful :=
  ⟨g.sound, g.complete.atEnd⟩

instance lawful_rest : rest.Lawful := ⟨sound_rest, completeAtEnd_rest⟩

instance lawful_map (f : α → β) (g : GrammarE α) [g.Lawful] : (g.map f).Lawful :=
  ⟨g.sound.map f, g.complete.map f⟩

instance lawful_after (g : Grammar α) (h : α → GrammarE β) [g.Lawful] [∀ a, (h a).Lawful] :
    (after g h).Lawful :=
  ⟨g.sound.bind fun a => (h a).sound, g.complete.bindAtEnd fun a => (h a).complete⟩

instance lawful_items (g : Grammar α) (hne : NonEmpty g.G) [g.Lawful] : (items g hne).Lawful :=
  ⟨sound_untilEnd g.sound, completeAtEnd_untilEnd g.complete hne⟩

instance lawful_sized (n : Nat) (g : GrammarE α) [g.Lawful] : (sized n g).Lawful :=
  ⟨g.sound.sized n, g.complete.sized n⟩

instance lawful_sizedBy (g : GrammarE α) [g.Lawful] : (sizedBy g).Lawful :=
  inferInstanceAs (Grammar.u32.bind fun n => sized n g).Lawful

theorem rest_G (b : ByteArray) : rest.G b.data.toList b := rfl

theorem after_G {g : Grammar α} {h : α → GrammarE β} {l₁ l₂ : Bytes} {a : α} {b : β}
    (h₁ : g.G l₁ a) (h₂ : (h a).G l₂ b) : (after g h).G (l₁ ++ l₂) b := ⟨l₁, l₂, a, rfl, h₁, h₂⟩

theorem map_G {f : α → β} {g : GrammarE α} {l : Bytes} {a : α} (h : g.G l a) :
    (g.map f).G l (f a) := ⟨a, h, rfl⟩

theorem items_G {g : Grammar α} {hne : NonEmpty g.G} {l : Bytes} {xs : List α}
    (h : Seq g.G l xs) : (items g hne).G l xs := h

theorem sizedBy_G {g : GrammarE α} {nb l : Bytes} {a : α} (hn : U32 nb l.length) (h : g.G l a) :
    (sizedBy g).G (nb ++ l) a := Grammar.bind_G (g := Grammar.u32) hn ⟨rfl, h⟩

/-- Reading a whole input: soundness. -/
theorem runAll_sound (g : GrammarE α) [g.Lawful] {bs : ByteArray} {a : α} (h : runAll g.parse bs = .ok a) :
    g.G bs.data.toList a := g.sound.runAll h

/-- Reading a whole input: completeness (round trip). -/
theorem runAll_complete (g : GrammarE α) [g.Lawful] {l : Bytes} {a : α} (h : g.G l a) :
    runAll g.parse ⟨l.toArray⟩ = .ok a := g.complete.runAll h

end GrammarE

namespace Grammar

instance lawful_fail : (fail : Grammar α).Lawful :=
  ⟨(fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ h => h.elim)⟩

end Grammar

end Silmaril.Parse.ByteParse
