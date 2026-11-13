module

public import Silmaril.Proofs.Wasm.Component.BinaryP3.RoundTrip

/-!
# The async-aware grammar extends the old one

Every byte string the grammar of `Silmaril.Wasm.Component.Binary` (Binary.md at `8505ba7`, no
async built-ins) relates to a component `c` is related by the new grammar to `Ast.ofV0 c`;
with completeness of the new parser, `Binary.parse b = ok c → parse b = ok (Ast.ofV0 c)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Binary (Seq Vec U32)

namespace Conservative

/-- `g'` relates every string `g` relates to `a` to `f a`. -/
def Incl {α β : Type} (G : Bytes → α → Prop) (G' : Bytes → β → Prop) (f : α → β) : Prop :=
  ∀ l a, G l a → G' l (f a)

theorem tagged_incl {α β : Type} {w w' : String} {k : UInt8 → Option (Grammar α)}
    {k' : UInt8 → Option (Grammar β)} {f : α → β}
    (hk : ∀ b g, k b = some g → ∃ g', k' b = some g' ∧ Incl g.G g'.G f) :
    Incl (tagged w k).G (tagged w' k').G f := by
  rintro l a ⟨b, l', G, rfl, hK, hG⟩
  obtain ⟨g, hg, hgG⟩ : ∃ g, k b = some g ∧ g.G = G := by
    simpa only [Option.map_eq_some_iff] using hK
  obtain ⟨g', hg', hinc⟩ := hk b g hg
  exact tagged_G _ hg' (hinc _ _ (hgG ▸ hG))

theorem map_incl {α β γ : Type} {G : Bytes → α → Prop} {m : α → β} {m' : α → γ} {f : β → γ}
    (h : ∀ x, f (m x) = m' x) : Incl (Silmaril.Parse.ByteParse.Spec.map m G)
      (Silmaril.Parse.ByteParse.Spec.map m' G) f := by
  rintro l a ⟨x, hx, rfl⟩
  exact ⟨x, hx, (h x).symm⟩

theorem bind_incl {α β γ : Type} {G : Bytes → α → Prop} {H : α → Bytes → β → Prop}
    {H' : α → Bytes → γ → Prop} {f : β → γ} (h : ∀ a, Incl (H a) (H' a) f) :
    Incl (Silmaril.Parse.ByteParse.Spec.bind G H) (Silmaril.Parse.ByteParse.Spec.bind G H') f := by
  rintro l b ⟨l₁, l₂, a, rfl, h₁, h₂⟩
  exact ⟨l₁, l₂, a, rfl, h₁, h a _ _ h₂⟩

theorem sized_incl {α β : Type} {n : Nat} {G : Bytes → α → Prop} {G' : Bytes → β → Prop}
    {f : α → β} (h : Incl G G' f) :
    Incl (Silmaril.Parse.ByteParse.Spec.sized n G) (Silmaril.Parse.ByteParse.Spec.sized n G') f := by
  rintro l a ⟨hn, hg⟩
  exact ⟨hn, h _ _ hg⟩

theorem seq_incl {α β : Type} {G : Bytes → α → Prop} {G' : Bytes → β → Prop} {f : α → β}
    (h : Incl G G' f) : ∀ {l : Bytes} {xs : List α}, Seq G l xs → Seq G' l (xs.map f)
  | _, _, .nil => .nil
  | _, _, .cons hx hs => .cons (h _ _ hx) (seq_incl h hs)

theorem seq_incl' {α β : Type} {G : Bytes → α → Prop} {G' : Bytes → β → Prop} {f : α → β}
    (h : Incl G G' f) : Incl (Seq G) (Seq G') (List.map f) := fun _ _ hs => seq_incl h hs

theorem vec_incl {α β : Type} {G : Bytes → α → Prop} {G' : Bytes → β → Prop} {f : α → β}
    (h : Incl G G' f) : Incl (Vec G) (Vec G') (List.map f) := by
  rintro l xs ⟨hn, hs⟩
  exact Vec.mk (by rw [List.length_map]; exact hn) (seq_incl h hs)

theorem refl_incl {α : Type} (G : Bytes → α → Prop) : Incl G G id := fun _ _ h => h

/-- A branch of a tagged grammar: the old branch `g₀` is included in the new one `g'`. -/
theorem branch {α β : Type} {o : Option (Grammar β)} {g : Grammar α}
    {g₀ : Grammar α} {g' : Grammar β} {f : α → β} (hg : some g₀ = some g)
    (hk : o = some g') (hinc : Incl g₀.G g'.G f) :
    ∃ g', o = some g' ∧ Incl g.G g'.G f :=
  ⟨g', hk, Option.some.inj hg ▸ hinc⟩

theorem tag_eq {b b₀ : UInt8} (h : b.toNat = b₀.toNat) : b₀ = b := (UInt8.toNat_inj.mp h).symm

/-- The old built-ins are new built-ins with the same bytes. -/
theorem canon_incl : Incl Binary.canonG.G canonG.G Canon.ofV0 := by
  refine tagged_incl ?_
  intro b g hg
  split at hg
  next h =>
    have hb : (0x00 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (bind_incl fun _ => map_incl fun _ => rfl)
  next h =>
    have hb : (0x01 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (bind_incl fun _ => map_incl fun _ => rfl)
  next h =>
    have hb : (0x02 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x03 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x04 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next => nomatch hg

theorem map_incl' {α α' β γ : Type} {G : Bytes → α → Prop} {G' : Bytes → α' → Prop}
    {h : α → α'} {m : α → β} {m' : α' → γ} {f : β → γ} (hG : Incl G G' h)
    (hm : ∀ x, f (m x) = m' (h x)) :
    Incl (Silmaril.Parse.ByteParse.Spec.map m G) (Silmaril.Parse.ByteParse.Spec.map m' G') f := by
  rintro l a ⟨x, hx, rfl⟩
  exact ⟨h x, hG _ _ hx, (hm x).symm⟩

theorem listOfV0_eq : ∀ ss : List Binary.Section, Section.listOfV0 ss = ss.map Section.ofV0
  | [] => by simp only [Section.listOfV0, List.map_nil]
  | s :: ss => by simp only [Section.listOfV0, List.map_cons, listOfV0_eq ss]

/-- A section's tag selects a new branch including the old one. -/
theorem section_incl (k : Nat)
    (ih : Incl (Binary.componentG k).G (componentG k).G Ast.ofV0) :
    Incl (Binary.sectionG (Binary.componentG k) (Binary.defTypeG (k + 1))
        (Binary.defTypeG_nonEmpty _)).G
      (sectionG (componentG k) (Binary.defTypeG (k + 1)) (Binary.defTypeG_nonEmpty _)).G
      Section.ofV0 := by
  refine tagged_incl ?_
  intro b g hg
  split at hg
  next h =>
    have hb : (0x00 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (bind_incl fun _ => sized_incl (bind_incl fun _ => map_incl fun _ => rfl))
  next h =>
    have hb : (0x01 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (bind_incl fun _ => sized_incl (map_incl fun _ => rfl))
  next h =>
    have hb : (0x02 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x03 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x04 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (bind_incl fun _ => sized_incl (map_incl' ih fun _ => rfl))
  next h =>
    have hb : (0x05 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x06 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x07 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x08 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl
      (map_incl' (bind_incl fun _ => sized_incl (vec_incl canon_incl)) fun _ => rfl)
  next h =>
    have hb : (0x09 : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x0a : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x0b : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next h =>
    have hb : (0x0c : UInt8) = b := tag_eq h
    rw [← hb]
    exact branch hg rfl (map_incl fun _ => rfl)
  next => nomatch hg

/-- Components, by induction on the nesting bound. -/
theorem component_incl : ∀ k, Incl (Binary.componentG k).G (componentG k).G Ast.ofV0
  | 0 => fun _ _ h => h.elim
  | k + 1 => bind_incl fun _ => map_incl' (seq_incl' (section_incl k (component_incl k)))
      fun ss => by simp only [Ast.ofV0, listOfV0_eq]

end Conservative

/-- **Conservativity**: the new parser reads every component the old one reads, as the
embedding of the old result. -/
theorem parse_ofV0 {b : ByteArray} {c : Binary.Ast} (h : Binary.parse b = .ok c) :
    parse b = .ok (Ast.ofV0 c) := by
  have hG : (componentG (b.size + 1)).G b.data.toList (Ast.ofV0 c) :=
    Conservative.component_incl _ _ _ (Binary.parse_sound h)
  have hb : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by simp
  unfold parse
  rw [← hb]
  exact GrammarE.runAll_complete _ hG

end Silmaril.Wasm.Component.BinaryP3
