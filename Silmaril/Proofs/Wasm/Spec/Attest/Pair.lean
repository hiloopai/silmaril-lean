module

public import Silmaril.Wasm.Spec.Attest.Defs
public import Silmaril.Games.Pair.Defs

/-!
# Side by side: may-call and trap propagation of a pairing

* `halves_append`: the halves of a concatenation;
* `inl_mem_halves`: a lower move of a play lies in one of its halves;
* `halves_injL`, `halves_injR`: a play of one side, embedded, has itself as its half;
* `mayCall_pair`: `σ₁.pair σ₂` may call iff `σ₁` or `σ₂` may;
* `pair_trapProp`: pairing preserves trap propagation;
* `injL_mem_pair`, `append_injR_mem_pair`: complete plays of the left side followed by plays of
  the right side are plays of the pairing.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Games.Split Silmaril.Wasm.Spec.Attest

universe u

variable {E F₁ F₂ : Sig.{u}}

/-! ### Halves -/

/-- The halves of a concatenation. -/
theorem halves_append : ∀ (b : Bool) (A B : List (Move E (F₁ ⊕ₛ F₂))),
    halves b (A ++ B) = ((halves b A).1 ++ (halves (side b A) B).1,
      (halves b A).2 ++ (halves (side b A) B).2)
  | _, [], _ => rfl
  | false, .inl e :: A, B => by simp only [List.cons_append, halves, side, halves_append false A B]
  | true, .inl e :: A, B => by simp only [List.cons_append, halves, side, halves_append true A B]
  | _, .inr (.ask (.inl q)) :: A, B => by
    simp only [List.cons_append, halves, side, halves_append false A B]
  | _, .inr (.ask (.inr q)) :: A, B => by
    simp only [List.cons_append, halves, side, halves_append true A B]
  | b, .inr (.ans (.inl q) r) :: A, B => by
    simp only [List.cons_append, halves, side, halves_append b A B]
  | b, .inr (.ans (.inr q) r) :: A, B => by
    simp only [List.cons_append, halves, side, halves_append b A B]

/-- **A lower move lies in one of the halves.** -/
theorem inl_mem_halves {x : Ev E} : ∀ (b : Bool) (p : List (Move E (F₁ ⊕ₛ F₂))),
    (.inl x : Move E (F₁ ⊕ₛ F₂)) ∈ p →
      (.inl x : Move E F₁) ∈ (halves b p).1 ∨ (.inl x : Move E F₂) ∈ (halves b p).2
  | _, [], h => absurd h List.not_mem_nil
  | false, .inl e :: p, h => by
    rcases List.mem_cons.1 h with h | h
    · obtain rfl : x = e := Sum.inl.inj h
      exact .inl (List.mem_cons_self ..)
    · rcases inl_mem_halves false p h with h' | h'
      · exact .inl (List.mem_cons_of_mem _ h')
      · exact .inr h'
  | true, .inl e :: p, h => by
    rcases List.mem_cons.1 h with h | h
    · obtain rfl : x = e := Sum.inl.inj h
      exact .inr (List.mem_cons_self ..)
    · rcases inl_mem_halves true p h with h' | h'
      · exact .inl h'
      · exact .inr (List.mem_cons_of_mem _ h')
  | _, .inr (.ask (.inl q)) :: p, h => by
    have hp : (.inl x : Move E (F₁ ⊕ₛ F₂)) ∈ p := by simpa using h
    rcases inl_mem_halves false p hp with h' | h'
    · exact .inl (List.mem_cons_of_mem _ h')
    · exact .inr h'
  | _, .inr (.ask (.inr q)) :: p, h => by
    have hp : (.inl x : Move E (F₁ ⊕ₛ F₂)) ∈ p := by simpa using h
    rcases inl_mem_halves true p hp with h' | h'
    · exact .inl h'
    · exact .inr (List.mem_cons_of_mem _ h')
  | b, .inr (.ans (.inl q) r) :: p, h => by
    have hp : (.inl x : Move E (F₁ ⊕ₛ F₂)) ∈ p := by simpa using h
    rcases inl_mem_halves b p hp with h' | h'
    · exact .inl (List.mem_cons_of_mem _ h')
    · exact .inr h'
  | b, .inr (.ans (.inr q) r) :: p, h => by
    have hp : (.inl x : Move E (F₁ ⊕ₛ F₂)) ∈ p := by simpa using h
    rcases inl_mem_halves b p hp with h' | h'
    · exact .inl h'
    · exact .inr (List.mem_cons_of_mem _ h')

/-! ### Embedding one side -/

/-- An upper event of the left side as an event of the sum. -/
def evL : Ev F₁ → Ev (F₁ ⊕ₛ F₂)
  | .ask q => .ask (.inl q)
  | .ans q r => .ans (.inl q) r

/-- An upper event of the right side as an event of the sum. -/
def evR : Ev F₂ → Ev (F₁ ⊕ₛ F₂)
  | .ask q => .ask (.inr q)
  | .ans q r => .ans (.inr q) r

/-- A move of the left side as a move of the pairing. -/
def injL : Move E F₁ → Move E (F₁ ⊕ₛ F₂) := Sum.map id evL

/-- A move of the right side as a move of the pairing. -/
def injR : Move E F₂ → Move E (F₁ ⊕ₛ F₂) := Sum.map id evR

/-- A position of the left side as a position of the pairing. -/
def posL : Pos E F₁ → Pos E (F₁ ⊕ₛ F₂)
  | .idle => .idle
  | .run q => .run (.inl q)
  | .wait q m => .wait (.inl q) m

/-- A position of the right side as a position of the pairing. -/
def posR : Pos E F₂ → Pos E (F₁ ⊕ₛ F₂)
  | .idle => .idle
  | .run q => .run (.inr q)
  | .wait q m => .wait (.inr q) m

theorem path_injL {x y : Pos E F₁} {p : List (Move E F₁)} (h : Path x p y) :
    Path (posL (F₂ := F₂) x) (p.map injL) (posL y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    refine .cons ?_ ih
    cases hs with
    | ask q => exact Step.ask (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inl q)
    | call q m => exact Step.call (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inl q) m
    | reply q m n => exact Step.reply (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inl q) m n
    | ret q r => exact Step.ret (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inl q) r

theorem path_injR {x y : Pos E F₂} {p : List (Move E F₂)} (h : Path x p y) :
    Path (posR (F₁ := F₁) x) (p.map injR) (posR y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    refine .cons ?_ ih
    cases hs with
    | ask q => exact Step.ask (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inr q)
    | call q m => exact Step.call (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inr q) m
    | reply q m n => exact Step.reply (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inr q) m n
    | ret q r => exact Step.ret (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inr q) r

/-- The left embedding keeps the round on the left. -/
theorem halves_injL : ∀ p : List (Move E F₁),
    halves false (p.map (injL (F₂ := F₂))) = (p, []) ∧ side false (p.map (injL (F₂ := F₂))) = false
  | [] => ⟨rfl, rfl⟩
  | .inl e :: p => by
    have ih := halves_injL p
    simp only [List.map_cons, injL, Sum.map_inl, id, halves, side] at ih ⊢
    exact ⟨by rw [ih.1], ih.2⟩
  | .inr (.ask q) :: p => by
    have ih := halves_injL p
    simp only [List.map_cons, injL, Sum.map_inr, evL, halves, side] at ih ⊢
    exact ⟨by rw [ih.1], ih.2⟩
  | .inr (.ans q r) :: p => by
    have ih := halves_injL p
    simp only [List.map_cons, injL, Sum.map_inr, evL, halves, side] at ih ⊢
    exact ⟨by rw [ih.1], ih.2⟩

/-- The right embedding, read with the round on the right. -/
theorem halves_injR_true : ∀ p : List (Move E F₂),
    halves true (p.map (injR (F₁ := F₁))) = ([], p)
  | [] => rfl
  | .inl e :: p => by
    have ih := halves_injR_true p
    simp only [List.map_cons, injR, Sum.map_inl, id, halves] at ih ⊢
    rw [ih]
  | .inr (.ask q) :: p => by
    have ih := halves_injR_true p
    simp only [List.map_cons, injR, Sum.map_inr, evR, halves] at ih ⊢
    rw [ih]
  | .inr (.ans q r) :: p => by
    have ih := halves_injR_true p
    simp only [List.map_cons, injR, Sum.map_inr, evR, halves] at ih ⊢
    rw [ih]

/-- A legal play starts with an upper question. -/
theorem legal_head {E F : Sig.{u}} {p : List (Move E F)} {y : Pos E F} (h : Path .idle p y) :
    p = [] ∨ ∃ q rest, p = .inr (.ask q) :: rest := by
  cases h with
  | nil => exact .inl rfl
  | cons hs _ => cases hs with
    | ask q => exact .inr ⟨q, _, rfl⟩

/-- A legal play of the right side, embedded: its halves, from either side. -/
theorem halves_injR {p : List (Move E F₂)} {y : Pos E F₂} (h : Path .idle p y) (b : Bool) :
    halves b (p.map (injR (F₁ := F₁))) = ([], p) := by
  rcases legal_head h with rfl | ⟨q, rest, rfl⟩
  · rfl
  · have ih := halves_injR_true (F₁ := F₁) rest
    simp only [List.map_cons, injR, Sum.map_inr, evR, halves] at ih ⊢
    rw [ih]

/-- **A play of the left side is a play of the pairing.** -/
theorem injL_mem_pair {σ₁ : Strategy E F₁} (σ₂ : Strategy E F₂) {p : List (Move E F₁)}
    (hp : p ∈ σ₁) : p.map injL ∈ σ₁.pair σ₂ := by
  obtain ⟨y, hy⟩ := σ₁.legal hp
  refine ⟨⟨_, path_injL hy⟩, ?_, ?_⟩
  · rw [(halves_injL p).1]; exact hp
  · rw [(halves_injL p).1]; exact σ₂.nil_mem

/-- **A complete play of the left side, then a play of the right side**, is a play of the
pairing. -/
theorem append_injR_mem_pair {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂} {p₁ : List (Move E F₁)}
    {p₂ : List (Move E F₂)} (hp₁ : p₁ ∈ σ₁) (hc : Path .idle p₁ .idle) (hp₂ : p₂ ∈ σ₂) :
    p₁.map injL ++ p₂.map injR ∈ σ₁.pair σ₂ := by
  obtain ⟨y, hy⟩ := σ₂.legal hp₂
  have hpath : Path .idle (p₁.map injL ++ p₂.map injR) (posR y) :=
    (path_injL (F₂ := F₂) hc).append (path_injR hy)
  have hh : halves false (p₁.map (injL (F₂ := F₂)) ++ p₂.map injR) = (p₁, p₂) := by
    rw [halves_append, (halves_injL p₁).1, halves_injR hy]
    simp
  refine ⟨⟨_, hpath⟩, ?_, ?_⟩
  · rw [hh]; exact hp₁
  · rw [hh]; exact hp₂

/-- `injL` keeps lower moves. -/
theorem injL_inl (x : Ev E) : (injL (F₁ := F₁) (F₂ := F₂) (.inl x)) = .inl x := rfl

/-- `injL` embeds upper moves. -/
theorem injL_inr (y : Ev F₁) : (injL (E := E) (F₂ := F₂) (.inr y)) = .inr (evL y) := rfl

/-- `injR` keeps lower moves. -/
theorem injR_inl (x : Ev E) : (injR (F₁ := F₁) (F₂ := F₂) (.inl x)) = .inl x := rfl

/-- `injR` embeds upper moves. -/
theorem injR_inr (y : Ev F₂) : (injR (E := E) (F₁ := F₁) (.inr y)) = .inr (evR y) := rfl

/-! ### May call -/

/-- **A pairing may call iff one of its sides may.** -/
theorem mayCall_pair (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    MayCall (σ₁.pair σ₂) ↔ MayCall σ₁ ∨ MayCall σ₂ := by
  constructor
  · rintro ⟨p, ⟨-, h₁, h₂⟩, m, hm⟩
    rcases inl_mem_halves false p hm with h | h
    · exact .inl ⟨_, h₁, m, h⟩
    · exact .inr ⟨_, h₂, m, h⟩
  · rintro (⟨p, hp, m, hm⟩ | ⟨p, hp, m, hm⟩)
    · exact ⟨_, injL_mem_pair σ₂ hp, m, List.mem_map.2 ⟨_, hm, rfl⟩⟩
    · have hnil : ([] : List (Move E F₁)) ∈ σ₁ := σ₁.nil_mem
      have hmem := append_injR_mem_pair hnil (.nil _) hp
      exact ⟨_, hmem, m, List.mem_append_right _ (List.mem_map.2 ⟨_, hm, rfl⟩)⟩

/-! ### Trap propagation -/

/-- The trap answers of a pairing, after a left round. -/
theorem halves_trap_left (m : E.Op) (n : E.Ar m) (q : F₁.Op) (r : F₁.Ar q) :
    halves false ([.inl (.ans m n), .inr (.ans (.inl q) r)] : List (Move E (F₁ ⊕ₛ F₂))) =
      ([.inl (.ans m n), .inr (.ans q r)], []) := rfl

/-- The trap answers of a pairing, after a right round. -/
theorem halves_trap_right (m : E.Op) (n : E.Ar m) (q : F₂.Op) (r : F₂.Ar q) :
    halves true ([.inl (.ans m n), .inr (.ans (.inr q) r)] : List (Move E (F₁ ⊕ₛ F₂))) =
      ([], [.inl (.ans m n), .inr (.ans q r)]) := rfl

/-- **Pairing preserves trap propagation.** -/
theorem pair_trapProp {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂} {stopE : ∀ m : E.Op, E.Ar m}
    {s₁ : ∀ q : F₁.Op, F₁.Ar q} {s₂ : ∀ q : F₂.Op, F₂.Ar q} (h₁ : TrapProp σ₁ stopE s₁)
    (h₂ : TrapProp σ₂ stopE s₂) : TrapProp (σ₁.pair σ₂) stopE (sumStop s₁ s₂) := by
  intro p q m ⟨_, hp₁, hp₂⟩ hw
  have hlegal : Legal (p ++ [.inl (.ans m (stopE m)), .inr (.ans q (sumStop s₁ s₂ q))]) :=
    ⟨_, hw.append (.cons (.reply q m _) (.single (.ret q _)))⟩
  obtain ⟨y₁, y₂, hy₁, hy₂, hr⟩ := halves_path hw (Rel.idle false)
  refine ⟨hlegal, ?_⟩
  rw [halves_append]
  generalize side false p = b at hr ⊢
  rcases q with q | q
  · cases hr with
    | waitL =>
      refine ⟨?_, ?_⟩
      · show (halves false p).1 ++ [.inl (.ans m (stopE m)), .inr (.ans q (s₁ q))] ∈ σ₁
        exact h₁ _ q m hp₁ hy₁
      · show (halves false p).2 ++ [] ∈ σ₂
        simpa using hp₂
  · cases hr with
    | waitR =>
      refine ⟨?_, ?_⟩
      · show (halves false p).1 ++ [] ∈ σ₁
        simpa using hp₁
      · show (halves false p).2 ++ [.inl (.ans m (stopE m)), .inr (.ans q (s₂ q))] ∈ σ₂
        exact h₂ _ q m hp₂ hy₂

end Silmaril.Proofs.Wasm.Spec.Attest
