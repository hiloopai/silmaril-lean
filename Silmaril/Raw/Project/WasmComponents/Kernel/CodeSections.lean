module

public import Silmaril.Project.WasmComponents.Code.Thms
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Wasm.Component.Binary.Framing.Thms

/-!
# The framing determines the code (raw proofs)

Valid, unrefined proofs behind `Silmaril.Project.WasmComponents.Kernel.CodeSections.Thms` (the
header to import):

* **depth monotonicity**: `defTypeG_mono`, `componentG_mono`, `componentG_le`, `sectionG_le`:
  the component grammar at nesting depth `k` is contained in the grammar at every `k' ≥ k`, so
  the depth of `componentG k` (`k` the input size in `Binary.parse`) is only a bound;
* **the grammar's `u32` is the pilot's LEB framing**: `leb_of_U32`, `U32 l n → leb 4 (l ++ r) =
  some (n, r)`;
* `section_shape`: every section is `id :: nb ++ body` with `U32 nb |body|`, its value does not
  depend on how its size is spelled, and it is a custom section exactly when `id = 0`;
* `sections_of_seq`: the framing `sections` of a sequence of grammar sections;
* `parse_codeSections`: `Task.parse_codeSections`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Wasm.Component.Binary
open Silmaril.Parse.ByteParse (Bytes NonEmpty Grammar GrammarE)
open Silmaril.Wasm.Binary (Seq Vec UN U32)

/-! ## Inclusion of relations -/

/-- `R` is contained in `R'`. -/
def Sub {α : Type} (R R' : Bytes → α → Prop) : Prop := ∀ ⦃l a⦄, R l a → R' l a

theorem Sub.refl {α : Type} (R : Bytes → α → Prop) : Sub R R := fun _ _ h => h

theorem Sub.trans {α : Type} {R R' R'' : Bytes → α → Prop} (h : Sub R R') (h' : Sub R' R'') :
    Sub R R'' := fun _ _ x => h' (h x)

theorem sub_map {α β : Type} {f : α → β} {R R' : Bytes → α → Prop} (h : Sub R R') :
    Sub (Silmaril.Parse.ByteParse.Spec.map f R) (Silmaril.Parse.ByteParse.Spec.map f R') :=
  fun _ _ ⟨a, ha, e⟩ => ⟨a, h ha, e⟩

theorem sub_bind {α β : Type} {G : Bytes → α → Prop} {H H' : α → Bytes → β → Prop}
    (h : ∀ a, Sub (H a) (H' a)) :
    Sub (Silmaril.Parse.ByteParse.Spec.bind G H) (Silmaril.Parse.ByteParse.Spec.bind G H') :=
  fun _ _ ⟨l₁, l₂, a, e, h₁, h₂⟩ => ⟨l₁, l₂, a, e, h₁, h a h₂⟩

theorem sub_sized {α : Type} {n : Nat} {R R' : Bytes → α → Prop} (h : Sub R R') :
    Sub (Silmaril.Parse.ByteParse.Spec.sized n R) (Silmaril.Parse.ByteParse.Spec.sized n R') :=
  fun _ _ ⟨e, x⟩ => ⟨e, h x⟩

theorem sub_seq {α : Type} {R R' : Bytes → α → Prop} (h : Sub R R') : Sub (Seq R) (Seq R') := by
  intro l xs hs
  induction hs with
  | nil => exact Seq.nil
  | cons hx _ ih => exact Seq.cons (h hx) ih

theorem sub_vec {α : Type} {R R' : Bytes → α → Prop} (h : Sub R R') : Sub (Vec R) (Vec R') := by
  intro l xs hv
  cases hv with
  | mk hn hs => exact Vec.mk hn (sub_seq h hs)

/-- Tag tables, pointwise. -/
def SubK {α : Type} (k k' : UInt8 → Option (Grammar α)) : Prop :=
  ∀ b, (k b = none ∧ k' b = none) ∨ ∃ g g', k b = some g ∧ k' b = some g' ∧ Sub g.G g'.G

theorem sub_tagged {α : Type} {w w' : String} {k k' : UInt8 → Option (Grammar α)}
    (h : SubK k k') : Sub (Grammar.tagged w k).G (Grammar.tagged w' k').G := by
  rintro l a ⟨b, l', G, rfl, hK, hG⟩
  rcases h b with ⟨e, -⟩ | ⟨g, g', e, e', hs⟩
  · simp [e] at hK
  · simp only [e, Option.map_some, Option.some.injEq] at hK
    subst hK
    exact ⟨b, l', g'.G, rfl, by simp [e'], hs hG⟩

theorem subK_some {α : Type} {g g' : Grammar α} (h : Sub g.G g'.G) :
    (some g = none ∧ some g' = none) ∨
      ∃ x x', some g = some x ∧ some g' = some x' ∧ Sub x.G x'.G :=
  .inr ⟨g, g', rfl, rfl, h⟩

theorem subK_same {α : Type} (o : Option (Grammar α)) :
    (o = none ∧ o = none) ∨ ∃ x x', o = some x ∧ o = some x' ∧ Sub x.G x'.G := by
  cases o with
  | none => exact .inl ⟨rfl, rfl⟩
  | some g => exact .inr ⟨g, g, rfl, rfl, Sub.refl _⟩

/-! ## Depth monotonicity -/

/-- The tag table of `defTypeG (k + 1)`, with `defTypeG k` a parameter. -/
def typeBody (t : Grammar DefType) (b : UInt8) : Option (Grammar DefType) :=
  match b.toNat with
  | 0x40 => some ((funcTypeBodyG false).map .func)
  | 0x43 => some ((funcTypeBodyG true).map .func)
  | 0x41 => some ((Grammar.vec (Grammar.tagged "componentdecl" (componentDeclBody t))
      (Grammar.tagged_nonEmpty _ _)).map .component)
  | 0x42 => some ((Grammar.vec (Grammar.tagged "instancedecl" (instanceDeclBody t))
      (Grammar.tagged_nonEmpty _ _)).map .instance)
  | 0x3f => some (resourceBodyG.map fun p => .resource p.1 p.2)
  | _ => (defValTypeBody b).map (Grammar.map .val)

theorem defTypeG_succ (k : Nat) : defTypeG (k + 1) = Grammar.tagged "type" (typeBody (defTypeG k)) := rfl

theorem subK_instanceDeclBody {t t' : Grammar DefType} (h : Sub t.G t'.G) :
    SubK (instanceDeclBody t) (instanceDeclBody t') := by
  intro b
  unfold instanceDeclBody
  split
  · exact subK_same _
  · exact subK_some (sub_map h)
  · exact subK_same _
  · exact subK_same _
  · exact .inl ⟨rfl, rfl⟩

theorem subK_componentDeclBody {t t' : Grammar DefType} (h : Sub t.G t'.G) :
    SubK (componentDeclBody t) (componentDeclBody t') := by
  intro b
  unfold componentDeclBody
  split
  · exact subK_same _
  · rcases subK_instanceDeclBody h b with ⟨e, e'⟩ | ⟨g, g', e, e', hs⟩
    · exact .inl ⟨by rw [e]; rfl, by rw [e']; rfl⟩
    · exact .inr ⟨g.map .inst, g'.map .inst, by rw [e]; rfl, by rw [e']; rfl, sub_map hs⟩

theorem subK_typeBody {t t' : Grammar DefType} (h : Sub t.G t'.G) : SubK (typeBody t) (typeBody t') := by
  intro b
  unfold typeBody
  split
  · exact subK_same _
  · exact subK_same _
  · exact subK_some (sub_map (sub_vec (sub_tagged (subK_componentDeclBody h))))
  · exact subK_some (sub_map (sub_vec (sub_tagged (subK_instanceDeclBody h))))
  · exact subK_same _
  · exact subK_same _

/-- **Depth monotonicity of type definitions.** -/
theorem defTypeG_mono : ∀ k, Sub (defTypeG k).G (defTypeG (k + 1)).G
  | 0 => fun _ _ h => h.elim
  | k + 1 => by
    rw [defTypeG_succ (k + 1), defTypeG_succ k]
    exact sub_tagged (subK_typeBody (defTypeG_mono k))

/-- The tag table of `sectionG`. -/
theorem subK_sectionG {c c' : GrammarE Ast} {t t' : Grammar DefType} {ht : NonEmpty t.G}
    {ht' : NonEmpty t'.G} (hc : Sub c.G c'.G) (h : Sub t.G t'.G) :
    Sub (sectionG c t ht).G (sectionG c' t' ht').G := by
  apply sub_tagged
  intro b
  beta_reduce
  split
  · exact subK_same _
  · exact subK_same _
  · exact subK_same _
  · exact subK_same _
  · exact subK_some (sub_bind fun _ => sub_sized (sub_map hc))
  · exact subK_same _
  · exact subK_same _
  · exact subK_some (sub_map (sub_bind fun _ => sub_sized (sub_vec h)))
  · exact subK_same _
  · exact subK_same _
  · exact subK_same _
  · exact subK_same _
  · exact subK_same _
  · exact .inl ⟨rfl, rfl⟩

/-- **Depth monotonicity of components.** -/
theorem componentG_mono : ∀ k, Sub (componentG k).G (componentG (k + 1)).G
  | 0 => fun _ _ h => h.elim
  | k + 1 => sub_bind fun _ => sub_map (sub_seq (subK_sectionG (componentG_mono k) (defTypeG_mono (k + 1))))

theorem componentG_le {k k' : Nat} (h : k ≤ k') : Sub (componentG k).G (componentG k').G := by
  induction h with
  | refl => exact Sub.refl _
  | step _ ih => exact ih.trans (componentG_mono _)

theorem defTypeG_le {k k' : Nat} (h : k ≤ k') : Sub (defTypeG k).G (defTypeG k').G := by
  induction h with
  | refl => exact Sub.refl _
  | step _ ih => exact ih.trans (defTypeG_mono _)

/-- The sections of the component grammar at depth `k + 1`, at every larger depth. -/
theorem sectionG_le {k k' : Nat} (h : k ≤ k') :
    Sub (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _)).G
      (sectionG (componentG k') (defTypeG (k' + 1)) (defTypeG_nonEmpty _)).G :=
  subK_sectionG (componentG_le h) (defTypeG_le (by omega))

/-! ## The grammar's `u32` is the pilot's LEB framing -/

/-- **`U32` bytes read back under `leb`** (the framing of `codeSections`). -/
theorem leb_of_UN : ∀ {N : Nat} {l : Bytes} {n : Nat}, UN N l n →
    ∀ (f : Nat) (r : Bytes), N ≤ 7 * (f + 1) → Silmaril.Project.WasmComponents.leb f (l ++ r) = some (n, r)
  | _, _, _, .byte b h₁ _, f, r, _ => by
    cases f <;> simp [Silmaril.Project.WasmComponents.leb, show b.toNat < 128 by simpa using h₁]
  | N, _, _, .cont b (m := m) h₁ h₂ rest, f, r, hN => by
    have hb : ¬ b.toNat < 128 := by simp at h₁; omega
    have hlt : b.toNat < 256 := UInt8.toNat_lt b
    cases f with
    | zero => omega
    | succ f =>
      have ih := leb_of_UN rest f r (by omega)
      simp only [List.cons_append, Silmaril.Project.WasmComponents.leb, hb, ite_false, ih,
        Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

theorem leb_of_U32 {l : Bytes} {n : Nat} (h : U32 l n) (r : Bytes) :
    Silmaril.Project.WasmComponents.leb 4 (l ++ r) = some (n, r) :=
  leb_of_UN h 4 r (by omega)

/-! ## The shape of a section -/

/-- A relation whose bytes are a `u32` size and a body of that size, and whose value does not
depend on how the size is spelled. -/
def SizedRel {α : Type} (G : Bytes → α → Prop) : Prop :=
  ∀ ⦃l a⦄, G l a → ∃ nb body, l = nb ++ body ∧ U32 nb body.length ∧
    ∀ nb', U32 nb' body.length → G (nb' ++ body) a

theorem sizedRel_bind {α : Type} (R : Bytes → α → Prop) :
    SizedRel (Silmaril.Parse.ByteParse.Spec.bind (UN 32) fun n => Silmaril.Parse.ByteParse.Spec.sized n R) := by
  rintro l a ⟨nb, body, n, rfl, hn, hlen, hR⟩
  subst hlen
  exact ⟨nb, body, rfl, hn, fun nb' hn' => ⟨nb', body, _, rfl, hn', rfl, hR⟩⟩

theorem sizedRel_map {α β : Type} {f : α → β} {G : Bytes → α → Prop} (h : SizedRel G) :
    SizedRel (Silmaril.Parse.ByteParse.Spec.map f G) := by
  rintro l b ⟨a, ha, rfl⟩
  obtain ⟨nb, body, e, hn, hre⟩ := h ha
  exact ⟨nb, body, e, hn, fun nb' hn' => ⟨a, hre nb' hn', rfl⟩⟩

theorem section_shape {c : GrammarE Ast} {t : Grammar DefType} {ht : NonEmpty t.G} {l : Bytes}
    {s : Section} (h : (sectionG c t ht).G l s) :
    ∃ id nb body, l = id :: (nb ++ body) ∧ U32 nb body.length ∧
      (∀ nb', U32 nb' body.length → (sectionG c t ht).G (id :: (nb' ++ body)) s) ∧
      (isCustom s = true ↔ id = 0) := by
  obtain ⟨b, l', G, rfl, hK, hG⟩ := h
  revert hK
  beta_reduce
  split
  all_goals intro hK
  all_goals rename_i hb
  case h_14 => simp at hK
  all_goals
    have hK0 := hK
    simp only [vecSection, Option.map_some, Option.some.injEq] at hK
    subst hK
    have hc : isCustom s = true ↔ b = 0 := by
      have hG' := hG
      first
        | (obtain ⟨_, _, _, -, -, -, _, _, nm, -, -, d, -, rfl⟩ := hG'
           exact ⟨fun _ => UInt8.toNat_inj.mp (by simpa using hb), fun _ => rfl⟩)
        | (obtain ⟨_, _, _, -, -, -, a, -, rfl⟩ := hG'
           exact ⟨fun h => by simp [isCustom] at h, fun h => by subst h; simp at hb⟩)
    obtain ⟨nb, body, rfl, hn, hre⟩ : ∃ nb body, l' = nb ++ body ∧ U32 nb body.length ∧
        ∀ nb', U32 nb' body.length → _ := by
      first
        | exact sizedRel_bind _ hG
        | exact sizedRel_map (sizedRel_bind _) hG
    exact ⟨b, nb, body, rfl, hn, fun nb' hn' => ⟨b, nb' ++ body, _, rfl, by beta_reduce; rw [hb]; exact hK0, hre nb' hn'⟩, hc⟩

/-! ## The framing of a sequence of sections -/

/-- A section and its frame `(id, body)`: the value does not depend on how the size is spelled,
and it is a custom section exactly when `id = 0`. -/
def Framed (SG : Grammar Section) (s : Section) (p : UInt8 × Bytes) : Prop :=
  ∃ nb, U32 nb p.2.length ∧ (∀ nb', U32 nb' p.2.length → SG.G (p.1 :: (nb' ++ p.2)) s) ∧
    (isCustom s = true ↔ p.1 = 0)

theorem sections_of_seq {c : GrammarE Ast} {t : Grammar DefType} {ht : NonEmpty t.G}
    {L : Bytes} {ss : List Section} (hseq : Seq (sectionG c t ht).G L ss) :
    ∀ fuel, ss.length ≤ fuel →
      ∃ fr, Silmaril.Project.WasmComponents.sections fuel L = some fr ∧
        List.Forall₂ (Framed (sectionG c t ht)) ss fr := by
  induction hseq with
  | nil => exact fun fuel _ => ⟨[], by cases fuel <;> rfl, .nil⟩
  | @cons l L' s ss hs _ ih =>
    intro fuel hf
    obtain ⟨id, nb, body, rfl, hn, hre, hc⟩ := section_shape hs
    have hf' : ss.length + 1 ≤ fuel := by simpa using hf
    cases fuel with
    | zero => omega
    | succ f =>
      obtain ⟨fr, hfr, h2⟩ := ih f (by omega)
      refine ⟨(id, body) :: fr, ?_, .cons ⟨nb, hn, hre, hc⟩ h2⟩
      have hl : Silmaril.Project.WasmComponents.leb 4 (nb ++ (body ++ L')) =
          some (body.length, body ++ L') := leb_of_U32 hn _
      simp [Silmaril.Project.WasmComponents.sections, hl, hfr]

theorem framed_filter {SG : Grammar Section} :
    ∀ {ss : List Section} {fr : List (UInt8 × Bytes)}, List.Forall₂ (Framed SG) ss fr →
      List.Forall₂ (Framed SG) (ss.filter fun s => !isCustom s) (fr.filter (·.1 != 0))
  | [], [], .nil => .nil
  | s :: ss, p :: fr, .cons h hr => by
    have hc : isCustom s = true ↔ p.1 = 0 := by obtain ⟨_, _, _, hc⟩ := h; exact hc
    by_cases hs : isCustom s = true
    · have hp : p.1 = 0 := hc.mp hs
      simp only [List.filter_cons, hs, hp, Bool.not_true, bne_self_eq_false]
      exact framed_filter hr
    · have hp : p.1 ≠ 0 := fun e => hs (hc.mpr e)
      simp only [List.filter_cons, Bool.not_eq_true] at hs ⊢
      simp only [hs, Bool.not_false, ite_true, bne_iff_ne, ne_eq, hp, not_false_eq_true]
      exact .cons h (framed_filter hr)

/-- Two sections framed by the same `(id, body)` at any two depths are one section. -/
theorem framed_eq {k₁ k₂ : Nat} {s₁ s₂ : Section} {p : UInt8 × Bytes}
    (h₁ : Framed (sectionG (componentG k₁) (defTypeG (k₁ + 1)) (defTypeG_nonEmpty _)) s₁ p)
    (h₂ : Framed (sectionG (componentG k₂) (defTypeG (k₂ + 1)) (defTypeG_nonEmpty _)) s₂ p) :
    s₁ = s₂ := by
  obtain ⟨nb, hn, hre₁, -⟩ := h₁
  obtain ⟨-, -, hre₂, -⟩ := h₂
  have g₁ := sectionG_le (k' := max k₁ k₂) (by omega) (hre₁ nb hn)
  have g₂ := sectionG_le (k' := max k₁ k₂) (by omega) (hre₂ nb hn)
  exact Grammar.functional _ g₁ g₂

theorem eq_of_framed {k₁ k₂ : Nat} {xs ys : List Section} {fr : List (UInt8 × Bytes)}
    (h₁ : List.Forall₂ (Framed (sectionG (componentG k₁) (defTypeG (k₁ + 1)) (defTypeG_nonEmpty _))) xs fr)
    (h₂ : List.Forall₂ (Framed (sectionG (componentG k₂) (defTypeG (k₂ + 1)) (defTypeG_nonEmpty _))) ys fr) :
    xs = ys := by
  induction h₁ generalizing ys with
  | nil => cases h₂; rfl
  | cons h r ih =>
    cases h₂ with
    | cons h' r' => rw [framed_eq h h', ih r']

/-- A parse, its sections and their frames. -/
theorem frames_of_parse {x : ByteArray} {a : Ast} (h : parse x = .ok a) :
    ∃ fr, Silmaril.Project.WasmComponents.sections x.size (x.data.toList.drop 8) = some fr ∧
      List.Forall₂ (Framed (sectionG (componentG x.size) (defTypeG (x.size + 1))
        (defTypeG_nonEmpty _))) a.sections fr := by
  have g : (componentG (x.size + 1)).G x.data.toList a := parse_sound h
  obtain ⟨l₁, l₂, u, e, hlit, ss, hseq, rfl⟩ := g
  have hpre : l₁ = preambleBytes := Silmaril.Wasm.Component.Binary.Framing.lit_G_inv hlit
  have hdrop : x.data.toList.drop 8 = l₂ := by rw [e, hpre]; rfl
  have hlen : ss.length ≤ x.size := by
    have h1 := Silmaril.Parse.ByteParse.Seq.length_le (Grammar.tagged_nonEmpty _ _) hseq
    have h2 : l₂.length ≤ x.size := by
      rw [← hdrop]; simp only [List.length_drop]; exact Nat.sub_le _ _
    omega
  rw [hdrop]
  exact sections_of_seq hseq _ hlen

/-- **`Task.parse_codeSections`: the framing determines the code.** -/
theorem parse_codeSections : Silmaril.Project.WasmComponents.Task.parse_codeSections := by
  intro x y a b hx hy hc
  obtain ⟨frx, ex, fx⟩ := frames_of_parse hx
  obtain ⟨fry, ey, fy⟩ := frames_of_parse hy
  have e : frx.filter (·.1 != 0) = fry.filter (·.1 != 0) := by
    unfold Silmaril.Project.WasmComponents.codeSections at hc
    rw [ex, ey] at hc
    exact Option.some.inj hc
  have e' := eq_of_framed (framed_filter fx) (e ▸ framed_filter fy)
  cases a with
  | mk ssa => cases b with
    | mk ssb => exact congrArg Ast.mk e'

end Silmaril.Project.WasmComponents.Kernel

end
