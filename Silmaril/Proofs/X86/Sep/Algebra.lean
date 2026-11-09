module

public import Silmaril.X86.Sep.Defs

/-!
# Proofs: the fragment algebra, the separation-logic laws and the atom bridges

Behind `Silmaril/X86/Sep/Thms.lean`. Fragments form a partial commutative monoid under
disjoint union; separating conjunction is associative and commutative with unit `emp`. The
atom lemmas read machine facts (`Memory.readBytes`, `Memory.Permitted`, register values) off
a fragment contained in `toFrag m`, and transport atoms along `Frag.reval` (same domain,
values of a later state).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.Process (Memory Region Permissions Access addressLimit)
open Silmaril.X86.Sep

/-! ## Fragments -/

namespace Frag

open Silmaril.X86.Sep.Frag

theorem union_apply (h₁ h₂ : Frag) (l : Loc) :
    union h₁ h₂ l = match h₁ l with | some v => some v | none => h₂ l := rfl

theorem union_of_none {h₁ h₂ : Frag} {l : Loc} (h : h₁ l = none) : union h₁ h₂ l = h₂ l := by
  simp [union, h]

theorem union_of_some {h₁ h₂ : Frag} {l : Loc} {v : Val} (h : h₁ l = some v) :
    union h₁ h₂ l = some v := by
  simp [union, h]

theorem empty_union (h : Frag) : union empty h = h := by
  funext l; rfl

theorem union_empty (h : Frag) : union h empty = h := by
  funext l; simp only [union, empty]; cases h l <;> rfl

theorem union_assoc (a b c : Frag) : union (union a b) c = union a (union b c) := by
  funext l; simp only [union]; cases a l <;> rfl

theorem Disjoint.symm {a b : Frag} (h : Disjoint a b) : Disjoint b a :=
  fun l => (h l).symm

theorem disjoint_comm {a b : Frag} : Disjoint a b ↔ Disjoint b a := ⟨Disjoint.symm, Disjoint.symm⟩

theorem disjoint_empty_left (h : Frag) : Disjoint empty h := fun _ => .inl rfl
theorem disjoint_empty_right (h : Frag) : Disjoint h empty := fun _ => .inr rfl

theorem union_comm {a b : Frag} (h : Disjoint a b) : union a b = union b a := by
  funext l
  simp only [union]
  rcases h l with e | e <;> rw [e] <;> cases (b l) <;> cases (a l) <;> simp_all

theorem union_eq_none {a b : Frag} {l : Loc} : union a b l = none ↔ a l = none ∧ b l = none := by
  simp only [union]; cases a l <;> simp

theorem disjoint_union_left {a b c : Frag} :
    Disjoint (union a b) c ↔ Disjoint a c ∧ Disjoint b c := by
  constructor
  · intro h
    refine ⟨fun l => ?_, fun l => ?_⟩ <;> rcases h l with e | e
    · exact .inl (union_eq_none.mp e).1
    · exact .inr e
    · exact .inl (union_eq_none.mp e).2
    · exact .inr e
  · rintro ⟨h₁, h₂⟩ l
    rcases h₁ l with e₁ | e₁
    · rcases h₂ l with e₂ | e₂
      · exact .inl (union_eq_none.mpr ⟨e₁, e₂⟩)
      · exact .inr e₂
    · exact .inr e₁

theorem disjoint_union_right {a b c : Frag} :
    Disjoint a (union b c) ↔ Disjoint a b ∧ Disjoint a c := by
  rw [disjoint_comm, disjoint_union_left, disjoint_comm (a := b), disjoint_comm (a := c)]

theorem isSome_union {a b : Frag} {l : Loc} :
    (union a b l).isSome ↔ (a l).isSome ∨ (b l).isSome := by
  simp only [union]; cases a l <;> simp

theorem Disjoint.not_both {a b : Frag} (h : Disjoint a b) {l : Loc} (ha : (a l).isSome)
    (hb : (b l).isSome) : False := by
  rcases h l with e | e <;> simp_all

/-! ### Containment -/

theorem Le.refl (h : Frag) : Le h h := fun _ _ e => e

theorem Le.trans {a b c : Frag} (h₁ : Le a b) (h₂ : Le b c) : Le a c :=
  fun l v e => h₂ l v (h₁ l v e)

theorem le_union_left (a b : Frag) : Le a (union a b) := fun _ _ e => union_of_some e

theorem le_union_right {a b : Frag} (h : Disjoint a b) : Le b (union a b) := by
  intro l v e
  rcases h l with e' | e'
  · rw [union_of_none e', e]
  · simp_all

theorem Le.isSome {a b : Frag} (h : Le a b) {l : Loc} (ha : (a l).isSome) : (b l).isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ha
  rw [h l v hv]; rfl

theorem single_apply_self (l : Loc) (v : Val) : single l v l = some v := by simp [single]

theorem single_apply_ne {l l' : Loc} (v : Val) (h : l' ≠ l) : single l v l' = none := by
  simp [single, h]

theorem le_single {l : Loc} {v : Val} {s : Frag} : Le (single l v) s ↔ s l = some v := by
  constructor
  · intro h; exact h l v (single_apply_self l v)
  · intro h l' v' e
    by_cases hl : l' = l
    · subst hl; rw [single_apply_self] at e; cases e; exact h
    · rw [single_apply_ne _ hl] at e; cases e

theorem isSome_single {l l' : Loc} {v : Val} : (single l v l').isSome ↔ l' = l := by
  by_cases h : l' = l <;> simp [single, h]

/-! ### Re-valuation and difference -/

theorem reval_apply (h s : Frag) (l : Loc) : reval h s l = if (h l).isSome then s l else none :=
  rfl

theorem reval_union (a b s : Frag) : reval (union a b) s = union (reval a s) (reval b s) := by
  funext l
  simp only [reval, union]
  rcases Option.eq_none_or_eq_some (a l) with e | ⟨v, e⟩
  · simp [e]
  · simp only [e, Option.isSome_some, ↓reduceIte]
    cases s l <;> simp

theorem reval_disjoint {a b : Frag} (h : Disjoint a b) (s : Frag) :
    Disjoint (reval a s) (reval b s) := by
  intro l
  rcases h l with e | e <;> simp [reval, e]

theorem reval_le (h s : Frag) : Le (reval h s) s := by
  intro l v e
  simp only [reval] at e
  split at e
  · exact e
  · cases e

theorem reval_of_le {h s : Frag} (hl : Le h s) : reval h s = h := by
  funext l
  simp only [reval]
  cases e : h l with
  | none => rfl
  | some v => simp [hl l v e]

theorem isSome_reval {h s : Frag} {l : Loc} (hs : (s l).isSome) :
    (reval h s l).isSome ↔ (h l).isSome := by
  simp only [reval]; split <;> simp_all

theorem reval_single (l : Loc) (v w : Val) {s : Frag} (hs : s l = some w) :
    reval (single l v) s = single l w := by
  funext l'
  simp only [reval, single]
  by_cases h : l' = l
  · subst h; simp [hs]
  · simp [h]

theorem reval_empty (s : Frag) : reval empty s = empty := by
  funext l; rfl

/-- A fragment whose values did not change. -/
theorem reval_eq_of_agree {h s s' : Frag} (hl : Le h s)
    (agree : ∀ l, (h l).isSome → s' l = s l) : reval h s' = h := by
  funext l
  simp only [reval]
  cases e : h l with
  | none => rfl
  | some v => simp [agree l (by simp [e]), hl l v e]

theorem diff_disjoint (s h : Frag) : Disjoint h (diff s h) := by
  intro l
  simp only [diff]
  cases e : h l <;> simp

theorem union_diff {h s : Frag} (hl : Le h s) : union h (diff s h) = s := by
  funext l
  simp only [union, diff]
  cases e : h l with
  | none => simp
  | some v => simp [hl l v e]

end Frag

/-! ## The separation-logic laws -/

open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

theorem sep_comm (P Q : SProp) : (P ∗ Q) = (Q ∗ P) := by
  funext h
  apply propext
  constructor <;>
  · rintro ⟨a, b, hd, rfl, ha, hb⟩
    exact ⟨b, a, Frag.Disjoint.symm hd, Frag.union_comm hd, hb, ha⟩

theorem sep_assoc (P Q R : SProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  funext h
  apply propext
  constructor
  · rintro ⟨ab, c, hd, rfl, ⟨a, b, hab, rfl, ha, hb⟩, hc⟩
    rw [Frag.disjoint_union_left] at hd
    exact ⟨a, union b c, Frag.disjoint_union_right.mpr ⟨hab, hd.1⟩, Frag.union_assoc a b c,
      ha, b, c, hd.2, rfl, hb, hc⟩
  · rintro ⟨a, bc, hd, rfl, ha, ⟨b, c, hbc, rfl, hb, hc⟩⟩
    rw [Frag.disjoint_union_right] at hd
    exact ⟨union a b, c, Frag.disjoint_union_left.mpr ⟨hd.2, hbc⟩,
      (Frag.union_assoc a b c).symm, ⟨a, b, hd.1, rfl, ha, hb⟩, hc⟩

theorem emp_sep (P : SProp) : (emp ∗ P) = P := by
  funext h
  apply propext
  constructor
  · rintro ⟨a, b, -, rfl, rfl, hb⟩
    rwa [Frag.empty_union]
  · intro hp
    exact ⟨Frag.empty, h, Frag.disjoint_empty_left h, (Frag.empty_union h).symm, rfl, hp⟩

theorem sep_emp (P : SProp) : (P ∗ emp) = P := by
  rw [sep_comm, emp_sep]

theorem entails_refl (P : SProp) : P ⊢ₛ P := fun _ h => h

theorem entails_trans {P Q R : SProp} (h₁ : P ⊢ₛ Q) (h₂ : Q ⊢ₛ R) : P ⊢ₛ R :=
  fun h hp => h₂ h (h₁ h hp)

theorem entails_of_eq {P Q : SProp} (e : P = Q) : P ⊢ₛ Q := by subst e; exact entails_refl P

theorem sep_mono {P P' Q Q' : SProp} (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') : (P ∗ Q) ⊢ₛ (P' ∗ Q') := by
  rintro h ⟨a, b, hd, rfl, ha, hb⟩
  exact ⟨a, b, hd, rfl, hp a ha, hq b hb⟩

theorem sep_mono_left {P P' : SProp} (Q : SProp) (hp : P ⊢ₛ P') : (P ∗ Q) ⊢ₛ (P' ∗ Q) :=
  sep_mono hp (entails_refl Q)

theorem sep_mono_right (P : SProp) {Q Q' : SProp} (hq : Q ⊢ₛ Q') : (P ∗ Q) ⊢ₛ (P ∗ Q') :=
  sep_mono (entails_refl P) hq

theorem sexists_sep {α : Sort _} (P : α → SProp) (Q : SProp) :
    (sexists P ∗ Q) = sexists (fun x => P x ∗ Q) := by
  funext h
  apply propext
  constructor
  · rintro ⟨a, b, hd, rfl, ⟨x, hx⟩, hb⟩
    exact ⟨x, a, b, hd, rfl, hx, hb⟩
  · rintro ⟨x, a, b, hd, rfl, hx, hb⟩
    exact ⟨a, b, hd, rfl, ⟨x, hx⟩, hb⟩

theorem sep_sexists {α : Sort _} (P : SProp) (Q : α → SProp) :
    (P ∗ sexists Q) = sexists (fun x => P ∗ Q x) := by
  rw [sep_comm, sexists_sep]
  congr 1; funext x; exact sep_comm _ _

theorem sexists_intro {α : Sort _} {P : SProp} {Q : α → SProp} (x : α) (h : P ⊢ₛ Q x) :
    P ⊢ₛ sexists Q := fun f hp => ⟨x, h f hp⟩

theorem sexists_elim {α : Sort _} {P : α → SProp} {Q : SProp} (h : ∀ x, P x ⊢ₛ Q) :
    sexists P ⊢ₛ Q := fun f ⟨x, hx⟩ => h x f hx

theorem spure_sep_apply (φ : Prop) (P : SProp) (h : Frag) : (⌜φ⌝ ∗ P) h ↔ φ ∧ P h := by
  constructor
  · rintro ⟨a, b, -, rfl, ⟨rfl, hφ⟩, hb⟩
    rw [Frag.empty_union]; exact ⟨hφ, hb⟩
  · rintro ⟨hφ, hp⟩
    exact ⟨Frag.empty, h, Frag.disjoint_empty_left h, (Frag.empty_union h).symm, ⟨rfl, hφ⟩, hp⟩

theorem spure_sep_intro {φ : Prop} {P Q : SProp} (hφ : φ) (h : P ⊢ₛ Q) : P ⊢ₛ (⌜φ⌝ ∗ Q) :=
  fun f hp => (spure_sep_apply φ Q f).mpr ⟨hφ, h f hp⟩

theorem spure_sep_elim {φ : Prop} {P Q : SProp} (h : φ → P ⊢ₛ Q) : (⌜φ⌝ ∗ P) ⊢ₛ Q :=
  fun f hp => by
    obtain ⟨hφ, hp⟩ := (spure_sep_apply φ P f).mp hp
    exact h hφ f hp

theorem spure_true_emp : ⌜True⌝ = emp := by
  funext h; apply propext; simp [spure, emp]

theorem wand_intro {P Q R : SProp} (h : (P ∗ Q) ⊢ₛ R) : P ⊢ₛ (Q -∗ R) :=
  fun f hp f' hd hq => h _ ⟨f, f', hd, rfl, hp, hq⟩

theorem wand_elim {P Q R : SProp} (h : P ⊢ₛ (Q -∗ R)) : (P ∗ Q) ⊢ₛ R := by
  rintro f ⟨a, b, hd, rfl, ha, hb⟩
  exact h a ha b hd hb

/-! ## Holding of a machine state -/

theorem sep_le {P Q : SProp} {h s : Frag} (hpq : (P ∗ Q) h) (hl : Le h s) :
    ∃ a b, P a ∧ Q b ∧ Le a s ∧ Le b s ∧ Disjoint a b ∧ h = union a b := by
  obtain ⟨a, b, hd, rfl, ha, hb⟩ := hpq
  exact ⟨a, b, ha, hb, Frag.Le.trans (Frag.le_union_left a b) hl,
    Frag.Le.trans (Frag.le_union_right hd) hl,
    hd, rfl⟩

theorem holds_sep {P Q : SProp} {m : MState} (h : Holds (P ∗ Q) m) : Holds P m ∧ Holds Q m := by
  obtain ⟨f, hf, hl⟩ := h
  obtain ⟨a, b, ha, hb, hla, hlb, -⟩ := sep_le hf hl
  exact ⟨⟨a, ha, hla⟩, ⟨b, hb, hlb⟩⟩

theorem holds_mono {P Q : SProp} {m : MState} (h : P ⊢ₛ Q) (hp : Holds P m) : Holds Q m := by
  obtain ⟨f, hf, hl⟩ := hp
  exact ⟨f, h f hf, hl⟩

/-! ## Atoms on a state -/

theorem toFrag_isSome (m : MState) (l : Loc) : (toFrag m l).isSome := by
  cases l <;> rfl

theorem regPt_le {r : Reg} {v : Word} {h : Frag} {m : MState} (hp : regPt r v h)
    (hl : Le h (toFrag m)) : m.core.read r = v := by
  subst hp
  have := Frag.le_single.mp hl
  simp only [toFrag] at this
  exact Val.word.inj (Option.some.inj this)

theorem ripPt_le {v : Word} {h : Frag} {m : MState} (hp : ripPt v h) (hl : Le h (toFrag m)) :
    m.core.rip = v := by
  subst hp
  have := Frag.le_single.mp hl
  simp only [toFrag] at this
  exact Val.word.inj (Option.some.inj this)

theorem flagsPt_le {f : Flags} {h : Frag} {m : MState} (hp : flagsPt f h)
    (hl : Le h (toFrag m)) : m.core.flags = f := by
  subst hp
  have := Frag.le_single.mp hl
  simp only [toFrag] at this
  exact Val.flags.inj (Option.some.inj this)

theorem regionsPt_le {rs : List Region} {h : Frag} {m : MState} (hp : regionsPt rs h)
    (hl : Le h (toFrag m)) : m.memory.regions = rs := by
  subst hp
  have := Frag.le_single.mp hl
  simp only [toFrag] at this
  exact Val.regions.inj (Option.some.inj this)

theorem byteAt_le {need : Permissions → Prop} {a : Nat} {b : Byte} {h : Frag} {m : MState}
    (hp : byteAt need a b h) (hl : Le h (toFrag m)) :
    a < addressLimit ∧ m.memory.bytes.get? a = some b ∧ need (permsAt m.memory a) := by
  obtain ⟨ha, p, hn, rfl⟩ := hp
  have := Frag.le_single.mp hl
  simp only [toFrag, Option.some.injEq, Val.cell.injEq, Cell.mk.injEq] at this
  obtain ⟨e₁, e₂⟩ := this
  exact ⟨ha, e₁, e₂ ▸ hn⟩

theorem byteAny_le {a : Nat} {h : Frag} {m : MState} (hp : byteAny a h)
    (hl : Le h (toFrag m)) : a < addressLimit ∧ RW (permsAt m.memory a) := by
  obtain ⟨ha, c, hn, rfl⟩ := hp
  have := Frag.le_single.mp hl
  simp only [toFrag, Option.some.injEq, Val.cell.injEq] at this
  rw [← this] at hn
  exact ⟨ha, hn⟩

theorem bytesAt_le {need : Permissions → Prop} :
    ∀ {a : Nat} {bs : List Byte} {h : Frag} {m : MState}, bytesAt need a bs h →
      Le h (toFrag m) → ∀ i (hi : i < bs.length), a + i < addressLimit ∧
        m.memory.bytes.get? (a + i) = some bs[i] ∧ need (permsAt m.memory (a + i))
  | _, [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a, b :: bs, h, m, hp, hl, i, hi => by
    obtain ⟨x, y, hx, hy, hlx, hly, -⟩ := sep_le hp hl
    cases i with
    | zero => simpa using byteAt_le hx hlx
    | succ i =>
      have := bytesAt_le hy hly i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem blockAny_le :
    ∀ {a n : Nat} {h : Frag} {m : MState}, blockAny a n h → Le h (toFrag m) →
      ∀ i < n, a + i < addressLimit ∧ RW (permsAt m.memory (a + i))
  | _, 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a, n + 1, h, m, hp, hl, i, hi => by
    obtain ⟨x, y, hx, hy, hlx, hly, -⟩ := sep_le hp hl
    cases i with
    | zero => simpa using byteAny_le hx hlx
    | succ i =>
      have := blockAny_le hy hly i (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-! ## Memory accesses -/

theorem permitted_of {memory : Memory} {access : Access} {a n : Nat} (hn : 0 < n)
    (h : ∀ i < n, a + i < addressLimit ∧ memory.permits access (a + i) = true) :
    memory.Permitted access a n := by
  rw [Memory.Permitted, Memory.checkSpan_iff]
  have h0 := (h 0 hn).1
  have hl := (h (n - 1) (by omega)).1
  refine ⟨by simpa using h0, by omega, fun i hi => (h i hi).2⟩

theorem readWith_of_bytesAt {need : Permissions → Prop} {access : Access}
    (hacc : ∀ p, need p → p.allows access = true) {a : Nat} {bs : List Byte} {h : Frag}
    {m : MState} (hne : bs ≠ []) (hp : bytesAt need a bs h) (hl : Le h (toFrag m)) :
    m.memory.readWith access a bs.length = some bs := by
  have hb := bytesAt_le hp hl
  apply Memory.readWith_eq
  · apply permitted_of (List.length_pos_iff.mpr hne)
    intro i hi
    obtain ⟨h1, -, h3⟩ := hb i hi
    refine ⟨h1, ?_⟩
    have := hacc _ h3
    cases access <;> simpa [permsAt, Permissions.allows] using this
  · intro i hi
    exact (hb i hi).2.1

theorem readBytes_of_bytesPt {a : Nat} {bs : List Byte} {h : Frag} {m : MState} (hne : bs ≠ [])
    (hp : bytesPt a bs h) (hl : Le h (toFrag m)) : m.memory.readBytes a bs.length = some bs :=
  readWith_of_bytesAt (fun _ hp => hp.1) hne hp hl

theorem readBytes_of_bytesPtRO {a : Nat} {bs : List Byte} {h : Frag} {m : MState}
    (hne : bs ≠ []) (hp : bytesPtRO a bs h) (hl : Le h (toFrag m)) :
    m.memory.readBytes a bs.length = some bs :=
  readWith_of_bytesAt (fun _ hp => hp) hne hp hl

theorem fetchBytes_of_codePt {a : Nat} {bs : List Byte} {h : Frag} {m : MState} (hne : bs ≠ [])
    (hp : codePt a bs h) (hl : Le h (toFrag m)) : m.memory.fetchBytes a bs.length = some bs :=
  readWith_of_bytesAt (fun _ hp => hp) hne hp hl

theorem readBytes_of_wordPt {a : Nat} {w : Word} {h : Frag} {m : MState} (hp : wordPt a w h)
    (hl : Le h (toFrag m)) :
    m.memory.readBytes a 8 = some (Silmaril.Machine.LittleEndian.encodeWords [w]) := by
  have := readBytes_of_bytesPt (by simp [Silmaril.Machine.LittleEndian.encodeWords]) hp hl
  simpa using this

theorem permitted_of_blockAny {access : Access} (hacc : access = .read ∨ access = .write)
    {a n : Nat} {h : Frag} {m : MState} (hn : 0 < n) (hp : blockAny a n h)
    (hl : Le h (toFrag m)) : m.memory.Permitted access a n := by
  apply permitted_of hn
  intro i hi
  obtain ⟨h1, h2, h3⟩ := blockAny_le hp hl i hi
  refine ⟨h1, ?_⟩
  rcases hacc with rfl | rfl <;> simpa [permsAt] using ‹_›

/-! ## Domains -/

theorem byteAt_dom {need : Permissions → Prop} {a : Nat} {b : Byte} {h : Frag}
    (hp : byteAt need a b h) : (h (.mem a)).isSome := by
  obtain ⟨-, p, -, rfl⟩ := hp; simp [Frag.single]

theorem byteAny_dom {a : Nat} {h : Frag} (hp : byteAny a h) : (h (.mem a)).isSome := by
  obtain ⟨-, c, -, rfl⟩ := hp; simp [Frag.single]

theorem sep_dom_left {P Q : SProp} {h : Frag} {l : Loc} (hpq : (P ∗ Q) h)
    (hd : ∀ a, P a → (a l).isSome) : (h l).isSome := by
  obtain ⟨a, b, -, rfl, ha, -⟩ := hpq
  exact Frag.isSome_union.mpr (.inl (hd a ha))

theorem sep_dom_right {P Q : SProp} {h : Frag} {l : Loc} (hpq : (P ∗ Q) h)
    (hd : ∀ b, Q b → (b l).isSome) : (h l).isSome := by
  obtain ⟨a, b, -, rfl, -, hb⟩ := hpq
  exact Frag.isSome_union.mpr (.inr (hd b hb))

theorem bytesAt_dom {need : Permissions → Prop} :
    ∀ {a : Nat} {bs : List Byte} {h : Frag}, bytesAt need a bs h →
      ∀ i < bs.length, (h (.mem (a + i))).isSome
  | _, [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a, b :: bs, h, hp, i, hi => by
    cases i with
    | zero => exact sep_dom_left hp (fun _ hx => byteAt_dom hx)
    | succ i =>
      refine sep_dom_right hp (fun _ hy => ?_)
      have := bytesAt_dom hy i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem blockAny_dom : ∀ {a n : Nat} {h : Frag}, blockAny a n h → ∀ i < n,
    (h (.mem (a + i))).isSome
  | _, 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a, n + 1, h, hp, i, hi => by
    cases i with
    | zero => exact sep_dom_left hp (fun _ hx => byteAny_dom hx)
    | succ i =>
      refine sep_dom_right hp (fun _ hy => ?_)
      have := blockAny_dom hy i (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem regPt_dom {r : Reg} {v : Word} {h : Frag} (hp : regPt r v h) : (h (.reg r)).isSome := by
  subst hp; simp [Frag.single]

theorem regAny_dom {r : Reg} {h : Frag} (hp : regAny r h) : (h (.reg r)).isSome := by
  obtain ⟨v, hv⟩ := hp; exact regPt_dom hv

theorem ripPt_dom {v : Word} {h : Frag} (hp : ripPt v h) : (h .rip).isSome := by
  subst hp; simp [Frag.single]

theorem flagsAny_dom {h : Frag} (hp : flagsAny h) : (h .flags).isSome := by
  obtain ⟨f, rfl⟩ := hp; simp [Frag.single]

/-! ## Re-valuation of atoms -/

theorem sep_reval {P Q P' Q' : SProp} {h : Frag} (s : Frag) (hpq : (P ∗ Q) h)
    (hp : ∀ a, P a → P' (reval a s)) (hq : ∀ b, Q b → Q' (reval b s)) : (P' ∗ Q') (reval h s) := by
  obtain ⟨a, b, hd, rfl, ha, hb⟩ := hpq
  exact ⟨reval a s, reval b s, Frag.reval_disjoint hd s, Frag.reval_union a b s, hp a ha, hq b hb⟩

/-- `sep_reval`, with the pieces known to be contained in `s₀`. -/
theorem sep_reval_le {P Q P' Q' : SProp} {h s₀ : Frag} (s : Frag) (hpq : (P ∗ Q) h)
    (hl : Le h s₀) (hp : ∀ a, P a → Le a s₀ → P' (reval a s))
    (hq : ∀ b, Q b → Le b s₀ → Q' (reval b s)) : (P' ∗ Q') (reval h s) := by
  obtain ⟨a, b, hd, rfl, ha, hb⟩ := hpq
  exact ⟨reval a s, reval b s, Frag.reval_disjoint hd s, Frag.reval_union a b s,
    hp a ha (Frag.Le.trans (Frag.le_union_left a b) hl),
    hq b hb (Frag.Le.trans (Frag.le_union_right hd) hl)⟩

theorem regAny_reval_exact {r : Reg} {h : Frag} (m : MState) (hp : regAny r h) :
    regPt r (m.core.read r) (reval h (toFrag m)) := by
  obtain ⟨v, rfl⟩ := hp; exact Frag.reval_single _ _ _ rfl

theorem emp_reval {h : Frag} (s : Frag) (hp : emp h) : emp (reval h s) := by
  subst hp; exact Frag.reval_empty s

theorem spure_reval {φ : Prop} {h : Frag} (s : Frag) (hp : (⌜φ⌝) h) : (⌜φ⌝) (reval h s) := by
  obtain ⟨rfl, hφ⟩ := hp; exact ⟨Frag.reval_empty s, hφ⟩

theorem regPt_reval {r : Reg} {v : Word} {h : Frag} (m : MState) (hp : regPt r v h) :
    regPt r (m.core.read r) (reval h (toFrag m)) := by
  subst hp; exact Frag.reval_single _ _ _ rfl

theorem regAny_reval {r : Reg} {h : Frag} (m : MState) (hp : regAny r h) :
    regAny r (reval h (toFrag m)) := by
  obtain ⟨v, hv⟩ := hp; exact ⟨_, regPt_reval m hv⟩

theorem ripPt_reval {v : Word} {h : Frag} (m : MState) (hp : ripPt v h) :
    ripPt m.core.rip (reval h (toFrag m)) := by
  subst hp; exact Frag.reval_single _ _ _ rfl

theorem flagsAny_reval {h : Frag} (m : MState) (hp : flagsAny h) :
    flagsAny (reval h (toFrag m)) := by
  obtain ⟨f, rfl⟩ := hp; exact ⟨m.core.flags, Frag.reval_single _ _ _ rfl⟩

theorem byteAt_reval {need need' : Permissions → Prop} {a : Nat} {b b' : Byte} {h : Frag}
    {m : MState} (hp : byteAt need a b h) (hb : m.memory.bytes.get? a = some b')
    (hn : need' (permsAt m.memory a)) : byteAt need' a b' (reval h (toFrag m)) := by
  obtain ⟨ha, p, -, rfl⟩ := hp
  refine ⟨ha, _, hn, Frag.reval_single _ _ _ ?_⟩
  show some (Val.cell ⟨m.memory.bytes.get? a, _⟩) = _
  rw [hb]

theorem byteAny_reval {a : Nat} {h : Frag} {m : MState} (hp : byteAny a h)
    (hn : RW (permsAt m.memory a)) : byteAny a (reval h (toFrag m)) := by
  obtain ⟨ha, c, -, rfl⟩ := hp
  exact ⟨ha, _, hn, Frag.reval_single _ _ _ rfl⟩

theorem bytesAt_reval {need need' : Permissions → Prop} :
    ∀ {a : Nat} {bs bs' : List Byte} {h : Frag} {m : MState}, bytesAt need a bs h →
      bs'.length = bs.length →
      (∀ i (hi : i < bs'.length), m.memory.bytes.get? (a + i) = some bs'[i] ∧
        need' (permsAt m.memory (a + i))) →
      bytesAt need' a bs' (reval h (toFrag m))
  | _, [], [], h, _, hp, _, _ => by subst hp; exact Frag.reval_empty _
  | _, [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _, _ :: _, [], _, _, _, hlen, _ => by simp at hlen
  | a, b :: bs, b' :: bs', h, m, hp, hlen, hv => by
    refine sep_reval _ hp (fun x hx => ?_) (fun y hy => ?_)
    · have := hv 0 (by simp)
      exact byteAt_reval hx (by simpa using this.1) (by simpa using this.2)
    · refine bytesAt_reval hy (by simpa using hlen) (fun i hi => ?_)
      have := hv (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem blockAny_reval : ∀ {a n : Nat} {h : Frag} {m : MState}, blockAny a n h →
    (∀ i < n, RW (permsAt m.memory (a + i))) → blockAny a n (reval h (toFrag m))
  | _, 0, h, _, hp, _ => by subst hp; exact Frag.reval_empty _
  | a, n + 1, h, m, hp, hv => by
    refine sep_reval _ hp (fun x hx => ?_) (fun y hy => ?_)
    · exact byteAny_reval hx (by simpa using hv 0 (by omega))
    · refine blockAny_reval hy (fun i hi => ?_)
      have := hv (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem byteAny_reval_byte {a : Nat} {b' : Byte} {h : Frag} {m : MState} (hp : byteAny a h)
    (hb : m.memory.bytes.get? a = some b') (hn : RW (permsAt m.memory a)) :
    bytePt a b' (reval h (toFrag m)) := by
  obtain ⟨ha, c, -, rfl⟩ := hp
  refine ⟨ha, _, hn, Frag.reval_single _ _ _ ?_⟩
  show some (Val.cell ⟨m.memory.bytes.get? a, _⟩) = _
  rw [hb]

/-- A budget block, written: its re-valuation holds the bytes now there. -/
theorem blockAny_reval_bytes : ∀ {a n : Nat} {bs' : List Byte} {h : Frag} {m : MState},
    blockAny a n h → bs'.length = n →
    (∀ i (hi : i < bs'.length), m.memory.bytes.get? (a + i) = some bs'[i] ∧
      RW (permsAt m.memory (a + i))) →
    bytesPt a bs' (reval h (toFrag m))
  | _, 0, [], h, _, hp, _, _ => by subst hp; exact Frag.reval_empty _
  | _, 0, _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _, _ + 1, [], _, _, _, hlen, _ => by simp at hlen
  | a, n + 1, b' :: bs', h, m, hp, hlen, hv => by
    refine sep_reval _ hp (fun x hx => ?_) (fun y hy => ?_)
    · have := hv 0 (by simp)
      exact byteAny_reval_byte hx (by simpa using this.1) (by simpa using this.2)
    · refine blockAny_reval_bytes hy (by simpa using hlen) (fun i hi => ?_)
      have := hv (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-! ## Conversions -/

theorem byteAt_mono {need need' : Permissions → Prop} (hn : ∀ p, need p → need' p) (a : Nat)
    (b : Byte) : byteAt need a b ⊢ₛ byteAt need' a b := by
  rintro h ⟨ha, p, hp, rfl⟩; exact ⟨ha, p, hn p hp, rfl⟩

theorem bytesAt_mono {need need' : Permissions → Prop} (hn : ∀ p, need p → need' p) :
    ∀ (a : Nat) (bs : List Byte), bytesAt need a bs ⊢ₛ bytesAt need' a bs
  | _, [] => entails_refl _
  | a, _ :: bs => sep_mono (byteAt_mono hn _ _) (bytesAt_mono hn (a + 1) bs)

theorem bytePt_byteAny (a : Nat) (b : Byte) : bytePt a b ⊢ₛ byteAny a := by
  rintro h ⟨ha, p, hp, rfl⟩; exact ⟨ha, _, hp, rfl⟩

theorem bytesPt_blockAny : ∀ (a : Nat) (bs : List Byte), bytesPt a bs ⊢ₛ blockAny a bs.length
  | _, [] => entails_refl _
  | a, b :: bs => sep_mono (bytePt_byteAny a b) (bytesPt_blockAny (a + 1) bs)

theorem bytesAt_append {need : Permissions → Prop} :
    ∀ (a : Nat) (xs ys : List Byte),
      bytesAt need a (xs ++ ys) = (bytesAt need a xs ∗ bytesAt need (a + xs.length) ys)
  | a, [], ys => by simp [bytesAt, emp_sep]
  | a, x :: xs, ys => by
    simp only [List.cons_append, bytesAt]
    rw [bytesAt_append (a + 1) xs ys, sep_assoc]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem blockAny_add : ∀ (a m n : Nat), blockAny a (m + n) = (blockAny a m ∗ blockAny (a + m) n)
  | a, 0, n => by simp [blockAny, emp_sep]
  | a, m + 1, n => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [blockAny]
    rw [blockAny_add (a + 1) m n, sep_assoc]
    simp [Nat.add_assoc, Nat.add_comm 1]

end Silmaril.Proofs.X86.Sep
