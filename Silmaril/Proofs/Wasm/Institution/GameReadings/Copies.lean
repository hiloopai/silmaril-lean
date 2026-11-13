module

public import Silmaril.Wasm.Institution.GameInst.Defs
public import Silmaril.Games.Reduct.Thms

/-!
# Every family of strategies is the restriction of one strategy on the copies

For `τ : V → Strategy E S` there is a strategy `copiesStrategy τ : Strategy E (copies V S)` whose
restriction to copy `v` is `τ v` (`restrict_copiesStrategy`). So `GameInst.modOf` is surjective.

The game `E ↠ F` is single-threaded: a play is a sequence of sessions, each opened by one
upper question. The restriction to copy `v` only sees the plays all of whose upper questions are
in copy `v` (`Strategy.mem_restrict_iff`; the image of a move of `S` in copy `v` is `emb v`). So
`copiesStrategy τ` takes as plays the legal plays all of whose single-copy prefixes are plays of
the corresponding `τ v`. After a play that mixes copies it allows every legal continuation: it
is not a "product" that keeps each copy's state, but its restrictions are exactly the `τ v`.

* `emb v`, `posEmb v`: copy `v` of a move and of a position; `upRel_inj_iff`: the move relation
  of `inj v` is the graph of `emb v`;
* `path_emb`, `path_of_emb`, `legal_map_emb_iff`: legality is preserved and reflected;
* `mem_of_map_prefix`: a single-copy prefix of a play of `τ v`, read in copy `w`, is a play of
  `τ w` (the first move of a nonempty legal play is an upper question, so `w = v`).
-/

public section

namespace Silmaril.Proofs.Wasm.Institution.GameReadings

open Silmaril.Games Silmaril.Wasm.Institution.GameInst

variable {V : Type} {E S : Sig.{0}}

/-- Copy `v` of a move of `E ↠ S`. -/
def emb (v : V) : Move E S → Move E (copies V S)
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask (v, q))
  | .inr (.ans q r) => .inr (.ans (v, q) r)

/-- Copy `v` of a position of `E ↠ S`. -/
def posEmb (v : V) : Pos E S → Pos E (copies V S)
  | .idle => .idle
  | .run q => .run (v, q)
  | .wait q m => .wait (v, q) m

/-- The move relation of `inj v` is the graph of `emb v`. -/
theorem upRel_inj_iff (v : V) (a : Move E (copies V S)) (m : Move E S) :
    UpRel (inj (S := S) v) a m ↔ a = emb v m := by
  constructor
  · rintro (_ | _ | _) <;> rfl
  · rintro rfl
    rcases m with e | (q | ⟨q, r⟩)
    · exact .low e
    · exact .ask q
    · exact UpRel.ans (ρ := inj (S := S) v) q r

/-- Plays related by `inj v` are images under `emb v`. -/
theorem forall₂_upRel_inj_iff (v : V) :
    ∀ (s : List (Move E (copies V S))) (p : List (Move E S)),
      List.Forall₂ (UpRel (inj (S := S) v)) s p ↔ s = p.map (emb v)
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | a :: s, m :: p => by
    rw [List.forall₂_cons, upRel_inj_iff, forall₂_upRel_inj_iff v s p, List.map_cons,
      List.cons.injEq]

/-- `emb v` is injective. -/
theorem emb_injective (v : V) : Function.Injective (emb (E := E) (S := S) v) := by
  rintro (e | (q | ⟨q, r⟩)) (e' | (q' | ⟨q', r'⟩)) h <;> simp_all [emb]

/-- Steps are preserved by `emb v`. -/
theorem step_emb (v : V) {x y : Pos E S} {m : Move E S} (h : Step x m y) :
    Step (posEmb v x) (emb v m) (posEmb v y) := by
  cases h
  · exact .ask _
  · exact .call _ _
  · exact .reply _ _ _
  · exact Step.ret (E := E) (F := copies V S) (v, _) _

/-- Steps are reflected by `emb v`. -/
theorem step_of_emb (v : V) {x : Pos E S} {m : Move E S} {y' : Pos E (copies V S)}
    (h : Step (posEmb v x) (emb v m) y') : ∃ y, y' = posEmb v y ∧ Step x m y := by
  rcases x with _ | q | ⟨q, m'⟩ <;> rcases m with (⟨e⟩ | ⟨e, n⟩) | (⟨q'⟩ | ⟨q', r⟩) <;>
    cases h
  all_goals exact ⟨_, rfl, by constructor⟩

/-- Paths are preserved by `emb v`. -/
theorem path_emb (v : V) {x y : Pos E S} {p : List (Move E S)} (h : Path x p y) :
    Path (posEmb v x) (p.map (emb v)) (posEmb v y) := by
  induction h with
  | nil x => exact .nil _
  | cons hs _ ih => exact .cons (step_emb v hs) ih

/-- Paths are reflected by `emb v`. -/
theorem path_of_emb (v : V) :
    ∀ {p : List (Move E S)} {x : Pos E S} {y' : Pos E (copies V S)},
      Path (posEmb v x) (p.map (emb v)) y' → ∃ y, y' = posEmb v y ∧ Path x p y
  | [], x, _, h => by
    cases h
    exact ⟨x, rfl, .nil _⟩
  | m :: p, x, _, .cons hs hp => by
    obtain ⟨z, rfl, hz⟩ := step_of_emb v hs
    obtain ⟨y, rfl, hy⟩ := path_of_emb v hp
    exact ⟨y, rfl, .cons hz hy⟩

/-- **Legality is preserved and reflected by `emb v`.** -/
theorem legal_map_emb_iff (v : V) {p : List (Move E S)} : Legal (p.map (emb v)) ↔ Legal p :=
  ⟨fun ⟨_, h⟩ => (path_of_emb v (x := .idle) h).elim fun y hy => ⟨y, hy.2⟩,
    fun ⟨_, h⟩ => ⟨_, path_emb v h⟩⟩

/-- `emb v` reflects Opponent moves. -/
theorem isO_of_emb (v : V) {m : Move E S} (h : Move.IsO (emb v m)) : Move.IsO m := by
  rcases m with (_ | _) | (_ | _) <;> exact h

/-- A nonempty legal play starts with an upper question. -/
theorem exists_ask_of_legal {m : Move E S} {p : List (Move E S)} (h : Legal (m :: p)) :
    ∃ q, m = .inr (.ask q) := by
  obtain ⟨_, hp⟩ := h
  cases hp with
  | cons hs _ =>
    cases hs
    exact ⟨_, rfl⟩

/-- Prefixes of images under an injective map are images of prefixes. -/
theorem prefix_of_map_prefix {α β : Type} {f : α → β} (hf : Function.Injective f)
    {l₁ l₂ : List α} (h : l₁.map f <+: l₂.map f) : l₁ <+: l₂ := by
  have h' : l₁.map f = (l₂.take l₁.length).map f := by
    rw [List.map_take, ← List.length_map (f := f)]
    exact List.prefix_iff_eq_take.1 h
  have he : l₁ = l₂.take l₁.length := List.map_injective_iff.2 hf h'
  rw [he]
  exact List.take_prefix _ _

/-- Copies `v` and `w` of two plays, the first one nonempty and the second legal, agree on their
first move only when `w = v`. -/
theorem eq_of_map_prefix {v w : V} {m' : Move E S} {p' p : List (Move E S)} (hp : Legal p)
    (h : (m' :: p').map (emb w) <+: p.map (emb v)) : w = v := by
  rcases p with _ | ⟨m, p⟩
  · exact absurd (List.eq_nil_of_prefix_nil h) (List.cons_ne_nil _ _)
  obtain ⟨q, rfl⟩ := exists_ask_of_legal hp
  have hm : emb w m' = emb v (.inr (.ask q)) := (List.cons_prefix_cons.1 h).1
  rcases m' with (_ | _) | (q' | _) <;> simp_all [emb]

/-- **A single-copy prefix of a play of copy `v` is a play of the strategy of its copy.** -/
theorem mem_of_map_prefix (τ : V → Strategy E S) {v w : V} {p p' : List (Move E S)}
    (hp : p ∈ τ v) (h : p'.map (emb w) <+: p.map (emb v)) : p' ∈ τ w := by
  rcases p' with _ | ⟨m', p'⟩
  · exact (τ w).nil_mem
  obtain rfl : w = v := eq_of_map_prefix ((τ v).legal hp) h
  exact (τ w).of_prefix hp (prefix_of_map_prefix (emb_injective w) h)

/-- The plays of `copiesStrategy τ`: legal plays all of whose single-copy prefixes, in copy `v`,
are plays of `τ v`. -/
def copiesPlays (τ : V → Strategy E S) : Set (List (Move E (copies V S))) :=
  {s | Legal s ∧ ∀ v (p : List (Move E S)), p.map (emb v) <+: s → p ∈ τ v}

theorem copiesPlays_nil (τ : V → Strategy E S) : [] ∈ copiesPlays τ := by
  refine ⟨⟨_, .nil _⟩, fun v p hp => ?_⟩
  have hp' : p = [] := List.map_eq_nil_iff.1 (List.eq_nil_of_prefix_nil hp)
  rw [hp']
  exact (τ v).nil_mem

theorem copiesPlays_of_prefix (τ : V → Strategy E S) {s t : List (Move E (copies V S))}
    (ht : t ∈ copiesPlays τ) (hst : s <+: t) : s ∈ copiesPlays τ :=
  ⟨ht.1.of_prefix hst, fun v p hp => ht.2 v p (hp.trans hst)⟩

/-- The receptiveness step: a single-copy play ending in an Opponent move whose prefix is a play
of `τ v` is a play of `τ v`. -/
theorem mem_concat_of_map (τ : V → Strategy E S) {v : V} {s : List (Move E (copies V S))}
    {o : Move E (copies V S)} {p₀ : List (Move E S)} {m : Move E S} (hp₀ : p₀ ∈ τ v)
    (hl : Legal (s ++ [o])) (ho : Move.IsO o) (hs : p₀.map (emb v) = s) (hm : emb v m = o) :
    p₀ ++ [m] ∈ τ v := by
  have hl' : Legal ((p₀ ++ [m]).map (emb v)) := by
    rw [List.map_append, List.map_singleton, hs, hm]
    exact hl
  obtain ⟨y, hy⟩ := (legal_map_emb_iff v).1 hl'
  obtain ⟨x, hx, hxy⟩ := Path.concat_iff.1 hy
  exact (τ v).receptive hp₀ hx hxy (isO_of_emb v (hm ▸ ho))

theorem copiesPlays_receptive (τ : V → Strategy E S) {s : List (Move E (copies V S))}
    {x y : Pos E (copies V S)} {o : Move E (copies V S)} (hs : s ∈ copiesPlays τ)
    (hx : Path .idle s x) (hxy : Step x o y) (ho : Move.IsO o) : s ++ [o] ∈ copiesPlays τ := by
  have hl : Legal (s ++ [o]) := ⟨y, hx.append (Path.single hxy)⟩
  refine ⟨hl, fun v p hp => ?_⟩
  rcases List.prefix_concat_iff.1 hp with h | h
  · rcases List.eq_nil_or_concat p with rfl | ⟨p₀, m, rfl⟩
    · exact (τ v).nil_mem
    rw [List.concat_eq_append]
    have h' : p₀.map (emb v) ++ [emb v m] = s ++ [o] := by
      rw [← h, List.concat_eq_append, List.map_append, List.map_singleton]
    obtain ⟨hs', hm⟩ := List.append_inj' h' rfl
    have hm' : emb v m = o := List.singleton_inj.1 hm
    exact mem_concat_of_map τ (hs.2 v p₀ (hs' ▸ List.prefix_refl _)) hl ho hs' hm'
  · exact hs.2 v p h

/-- **The strategy on the copies with the given restrictions.** -/
def copiesStrategy (τ : V → Strategy E S) : Strategy E (copies V S) where
  plays := copiesPlays τ
  nil_mem := copiesPlays_nil τ
  legal h := h.1
  of_prefix ht hst := copiesPlays_of_prefix τ ht hst
  receptive hs hx hxy ho := copiesPlays_receptive τ hs hx hxy ho

/-- **The restriction of `copiesStrategy τ` to copy `v` is `τ v`.** -/
theorem restrict_copiesStrategy (τ : V → Strategy E S) (v : V) :
    (copiesStrategy τ).restrict (inj v) = τ v := by
  ext p
  rw [Strategy.mem_restrict_iff]
  constructor
  · rintro ⟨-, s, hs, hr⟩
    have hs' : s = p.map (emb v) := (forall₂_upRel_inj_iff v s p).1 hr
    exact hs.2 v p (hs' ▸ List.prefix_refl _)
  · intro hp
    have hl : Legal p := (τ v).legal hp
    have hmem : p.map (emb v) ∈ copiesStrategy τ :=
      ⟨(legal_map_emb_iff v).2 hl, fun _ _ h => mem_of_map_prefix τ hp h⟩
    exact ⟨hl, _, hmem, (forall₂_upRel_inj_iff v _ p).2 rfl⟩

end Silmaril.Proofs.Wasm.Institution.GameReadings
