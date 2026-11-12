module

public import Silmaril.Proofs.Wasm.Spec.Attest.Pair
public import Silmaril.Proofs.Wasm.Spec.Attest.Comp
public import Silmaril.Games.Zip.Thms

/-!
# The encoding of positive formulas: soundness and completeness

* `first_inl`, `first_call`: the first lower move of a play is a question, asked from a
  running position after upper moves only;
* `mayCall_and_mp`, `mayCall_and_mpr`: the conjunction law;
* `andM_trapProp`, `orM_trapProp`, `enc_trapProp`: trap propagation of the encodings;
* `mayCall_enc`: the encoding may attest iff the formula holds.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Spec.Attest

universe u

variable {E F G : Sig.{u}}

/-! ### The first call -/

/-- A list with a left element starts with right elements up to its first left element. -/
theorem first_inl {α β : Type u} : ∀ {q : List (α ⊕ β)} {a : α}, .inl a ∈ q →
    ∃ (w : List β) (a' : α) (rest : List (α ⊕ β)), q = w.map .inr ++ .inl a' :: rest
  | .inl a' :: rest, _, _ => ⟨[], a', rest, rfl⟩
  | .inr b :: q, a, h => by
    have hq : .inl a ∈ q := by simpa using h
    obtain ⟨w, a', rest, rfl⟩ := first_inl hq
    exact ⟨b :: w, a', rest, rfl⟩

/-- Upper moves only, from the idle position, end idle or running. -/
theorem path_upper {E F : Sig.{u}} : ∀ {x y : Pos E F} (w : List (Ev F)),
    (x = .idle ∨ ∃ f, x = .run f) → Path x (w.map .inr) y → y = .idle ∨ ∃ f, y = .run f
  | _, _, [], hx, h => by cases h; exact hx
  | x, y, e :: w, hx, h => by
    rw [List.map_cons] at h
    cases h with
    | cons hst hp =>
      refine path_upper w ?_ hp
      cases hst with
      | ask q => exact .inr ⟨q, rfl⟩
      | ret q r => exact .inl rfl

/-- **The first call of a play**: if a play makes a lower move, a prefix of it is upper moves,
from the idle position to a running one, followed by a lower question. -/
theorem first_call {σ : Strategy E F} {q : List (Move E F)} {m : E.Op} (hq : q ∈ σ)
    (hm : (.inl (.ask m) : Move E F) ∈ q) :
    ∃ (w : List (Ev F)) (a : E.Op) (f : F.Op), w.map .inr ++ [.inl (.ask a)] ∈ σ ∧
      Path .idle (w.map .inr ++ [.inl (.ask a)]) (.wait f a) := by
  obtain ⟨w, x, rest, rfl⟩ := first_inl hm
  have hpre : w.map .inr ++ [.inl x] ∈ σ := σ.of_prefix hq ⟨rest, by simp⟩
  obtain ⟨z, hz⟩ := σ.legal hpre
  obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hz
  have hyrun : y = .idle ∨ ∃ f, y = .run f := path_upper w (.inl rfl) hy
  cases hst with
  | call f a => exact ⟨w, a, f, hpre, hz⟩
  | reply f a n => rcases hyrun with h | ⟨_, h⟩ <;> cases h

/-! ### Conjunction -/

section And

variable (K : Kit E) {stopE : ∀ m : E.Op, E.Ar m}

/-- **Only if**: the conjunction may attest only if both conjuncts may. -/
theorem mayCall_and_mp (hK : K.Ok stopE) (M N : AMod E) (h : MayCall (andM K M N).σ) :
    MayCall M.σ ∧ MayCall N.σ := by
  obtain ⟨p, ⟨s, hs, t, ⟨-, h₁, h₂⟩, hz⟩, m, hm⟩ := h
  have hms : (.inl (.ask m) : Move E K.G) ∈ s := zip_inl_mem hz hm
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.safe s hs ⟨m, hms⟩
  have hta : (.inl (.ask (K.ι₁.op a)) : Move K.G (M.F ⊕ₛ N.F)) ∈ t := zip_inr_mem hz ha
  have htb : (.inl (.ask (K.ι₂.op b)) : Move K.G (M.F ⊕ₛ N.F)) ∈ t := zip_inr_mem hz hb
  obtain ⟨q₁, hq₁, he₁⟩ := h₁
  obtain ⟨q₂, hq₂, he₂⟩ := h₂
  constructor
  · rcases inl_mem_halves false t hta with h | h
    · obtain ⟨y, hy, hev⟩ := inl_mem_map_move K.ι₁ (he₁ ▸ h)
      obtain ⟨a', rfl, -⟩ := ev_eq_ask K.ι₁ hev
      exact ⟨q₁, hq₁, a', hy⟩
    · obtain ⟨y, -, hev⟩ := inl_mem_map_move K.ι₂ (he₂ ▸ h)
      obtain ⟨b', -, hb'⟩ := ev_eq_ask K.ι₂ hev
      exact absurd hb'.symm (hK.disjoint a b')
  · rcases inl_mem_halves false t htb with h | h
    · obtain ⟨y, -, hev⟩ := inl_mem_map_move K.ι₁ (he₁ ▸ h)
      obtain ⟨a', -, ha'⟩ := ev_eq_ask K.ι₁ hev
      exact absurd ha' (hK.disjoint a' b)
    · obtain ⟨y, hy, hev⟩ := inl_mem_map_move K.ι₂ (he₂ ▸ h)
      obtain ⟨b', rfl, -⟩ := ev_eq_ask K.ι₂ hev
      exact ⟨q₂, hq₂, b', hy⟩

/-- The left conjunct's complete play up to its first call, then trapped, relabelled. -/
theorem left_play_map (M : AMod E) (w : List (Ev M.F)) (a : E.Op) (f : M.F.Op)
    (hstop : (K.ι₁.ar a).symm (stopE a) = K.stopG (K.ι₁.op a)) :
    ((w.map (Sum.inr : Ev M.F → Move E M.F) ++ ([.inl (.ask a)] : List (Move E M.F))) ++
        ([.inl (.ans a (stopE a)), .inr (.ans f (M.stop f))] : List (Move E M.F))).map
          K.ι₁.move =
      w.map (Sum.inr : Ev M.F → Move K.G M.F) ++ ([.inl (.ask (K.ι₁.op a)),
        .inl (.ans (K.ι₁.op a) (K.stopG (K.ι₁.op a))), .inr (.ans f (M.stop f))] :
          List (Move K.G M.F)) := by
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Relabel.move,
    Sum.map_inl, Sum.map_inr, Relabel.ev, hstop, id, List.append_assoc, List.cons_append,
    List.nil_append]
  rfl

/-- The right conjunct's play up to its first call, relabelled. -/
theorem right_play_map (N : AMod E) (w : List (Ev N.F)) (a : E.Op) :
    (w.map (Sum.inr : Ev N.F → Move E N.F) ++ ([.inl (.ask a)] : List (Move E N.F))).map
        K.ι₂.move =
      w.map (Sum.inr : Ev N.F → Move K.G N.F) ++
        ([.inl (.ask (K.ι₂.op a))] : List (Move K.G N.F)) := by
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Relabel.move,
    Sum.map_inl, Relabel.ev]
  rfl

/-- Embedded upper moves are visible moves of an interaction. -/
theorem map_inr_injL {M N : Sig.{u}} (w : List (Ev M)) :
    (w.map (.inr : Ev M → Move K.G M)).map (injL (F₂ := N)) = (w.map evL).map .inr := by
  simp only [List.map_map]
  rfl

/-- Embedded upper moves of the right side. -/
theorem map_inr_injR {M N : Sig.{u}} (w : List (Ev N)) :
    (w.map (.inr : Ev N → Move K.G N)).map (injR (F₁ := M)) = (w.map evR).map .inr := by
  simp only [List.map_map]
  rfl

/-- **If**: when the left conjunct propagates traps, the conjunction may attest if both may. -/
theorem mayCall_and_mpr (hK : K.Ok stopE) (M N : AMod E) (hM : TrapProp M.σ stopE M.stop)
    (h₁ : MayCall M.σ) (h₂ : MayCall N.σ) : MayCall (andM K M N).σ := by
  obtain ⟨q₁, hq₁, m₁, hm₁⟩ := h₁
  obtain ⟨q₂, hq₂, m₂, hm₂⟩ := h₂
  obtain ⟨w₁, a₁, f₁, hc₁, hw₁⟩ := first_call hq₁ hm₁
  obtain ⟨w₂, a₂, f₂, hc₂, -⟩ := first_call hq₂ hm₂
  have hstop : (K.ι₁.ar a₁).symm (stopE a₁) = K.stopG (K.ι₁.op a₁) :=
    (Equiv.symm_apply_eq _).2 (hK.stop₁ a₁).symm
  have hd₁ := hM _ f₁ a₁ hc₁ hw₁
  have hidle : Path .idle ((w₁.map .inr ++ [.inl (.ask a₁)]) ++
      [.inl (.ans a₁ (stopE a₁)), .inr (.ans f₁ (M.stop f₁))]) .idle :=
    hw₁.append (.cons (.reply f₁ a₁ _) (.single (.ret f₁ _)))
  have hr₁ : _ ∈ relabel M.σ K.ι₁ := ⟨_, hd₁, rfl⟩
  have hr₂ : _ ∈ relabel N.σ K.ι₂ := ⟨_, hc₂, rfl⟩
  have hpair := append_injR_mem_pair hr₁ (path_map K.ι₁ hidle) hr₂
  rw [left_play_map K M w₁ a₁ f₁ hstop, right_play_map K N w₂ a₂] at hpair
  obtain ⟨m, hm⟩ := hK.live a₁ a₂
  have hlast : (.inl (.ask m) : Move E (M.F ⊕ₛ N.F)) ∈ (w₁.map evL).map .inr ++
      (.inr (evL (F₂ := N.F) (.ans f₁ (M.stop f₁))) :: ((w₂.map evR).map .inr ++
        [.inl (.ask m)])) := by simp
  refine ⟨_, ⟨_, hm, _, hpair, ?_⟩, m, hlast⟩
  have hz : Zip [(.inr (.ask (K.ι₁.op a₁)) : Move E K.G),
      .inr (.ans (K.ι₁.op a₁) (K.stopG (K.ι₁.op a₁))), .inr (.ask (K.ι₂.op a₂)), .inl (.ask m)]
      (.inl (.ask (K.ι₁.op a₁)) :: .inl (.ans (K.ι₁.op a₁) (K.stopG (K.ι₁.op a₁))) ::
        .inr (evL (.ans f₁ (M.stop f₁))) :: ((w₂.map evR).map .inr ++
          [.inl (.ask (K.ι₂.op a₂))]))
      (.inr (evL (F₂ := N.F) (.ans f₁ (M.stop f₁))) :: ((w₂.map evR).map .inr ++
        [.inl (.ask m)])) :=
    .sync _ (.sync _ (.right _ ((Zip.left (Ev.ask m) .nil |>.sync _).prepend_right _)))
  have hz' := hz.prepend_right (w₁.map evL)
  simpa only [List.map_append, List.map_cons, List.map_nil, map_inr_injL, map_inr_injR,
    List.append_assoc, List.cons_append, List.nil_append, injL_inl, injL_inr, injR_inl,
    injR_inr] using hz'

/-- **The conjunction propagates traps** when both conjuncts do. -/
theorem andM_trapProp (hK : K.Ok stopE) {M N : AMod E} (hM : TrapProp M.σ stopE M.stop)
    (hN : TrapProp N.σ stopE N.stop) : TrapProp (andM K M N).σ stopE (andM K M N).stop :=
  comp_trapProp hK.gate_tp (pair_trapProp (relabel_trapProp hM hK.stop₁)
    (relabel_trapProp hN hK.stop₂))

end And

/-! ### The encoding -/

/-- **Disjunction propagates traps.** -/
theorem orM_trapProp {stopE : ∀ m : E.Op, E.Ar m} {M N : AMod E} (hM : TrapProp M.σ stopE M.stop)
    (hN : TrapProp N.σ stopE N.stop) : TrapProp (orM M N).σ stopE (orM M N).stop :=
  pair_trapProp hM hN

/-- **Every encoding propagates traps.** -/
theorem enc_trapProp {V : Type u} {K : Kit E} {stopE : ∀ m : E.Op, E.Ar m} (hK : K.Ok stopE)
    {μ : V → AMod E} (hμ : ∀ x, TrapProp (μ x).σ stopE (μ x).stop) :
    ∀ φ : PForm V, TrapProp (enc K μ φ).σ stopE (enc K μ φ).stop
  | .var x => hμ x
  | .tt => hK.tt_tp
  | .ff => hK.ff_tp
  | .or φ ψ => orM_trapProp (enc_trapProp hK hμ φ) (enc_trapProp hK hμ ψ)
  | .and φ ψ => andM_trapProp K hK (enc_trapProp hK hμ φ) (enc_trapProp hK hμ ψ)

/-- **Soundness and completeness of the encoding.** -/
theorem mayCall_enc {V : Type u} {K : Kit E} {stopE : ∀ m : E.Op, E.Ar m} (hK : K.Ok stopE)
    {μ : V → AMod E} (hμ : ∀ x, TrapProp (μ x).σ stopE (μ x).stop) :
    ∀ φ : PForm V, MayCall (enc K μ φ).σ ↔ φ.Holds (valOf μ)
  | .var _ => Iff.rfl
  | .tt => iff_true_intro hK.tt_may
  | .ff => iff_false_intro hK.ff_not
  | .or φ ψ => (mayCall_pair _ _).trans (or_congr (mayCall_enc hK hμ φ) (mayCall_enc hK hμ ψ))
  | .and φ ψ =>
    ⟨fun h => (mayCall_and_mp K hK _ _ h).imp (mayCall_enc hK hμ φ).1 (mayCall_enc hK hμ ψ).1,
      fun ⟨h₁, h₂⟩ => mayCall_and_mpr K hK _ _ (enc_trapProp hK hμ φ)
        ((mayCall_enc hK hμ φ).2 h₁) ((mayCall_enc hK hμ ψ).2 h₂)⟩

end Silmaril.Proofs.Wasm.Spec.Attest
