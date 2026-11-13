module

public import Silmaril.Proofs.Wasm.Game.Start.Main

/-!
# Linking instantiates the provider first: the converse

The proof follows the first moves of a consumer trace (`InstSystem.consumerLTS`)
through the interaction (`Zip`) with the provider. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.LinkStart

open Silmaril.Games Silmaril.Games.Inst

variable {X E F : Sig.{0}} {R : Type} {S : InstSystem E F R}

/-! ### Runs of the consumer system from its first states -/

/-- A state without silent steps starts a run with a visible step. -/
theorem run_cons_of_nosilent {L : LTS E F} {x z : L.State} {o : Move E F} {w : List (Move E F)}
    (hx : ∀ y, ¬ L.step x none y) (h : L.Run x (o :: w) z) :
    ∃ y, L.step x (some o) y ∧ L.Run y w z := by
  cases h with
  | tau hs _ => exact (hx _ hs).elim
  | vis hs hr => exact ⟨_, hs, hr⟩

theorem run_fresh {o : Move (E.withInst R) (F.withInst R)} {w : List _} {z : S.St}
    (h : S.consumerLTS.Run .fresh (o :: w) z) :
    o = .inr (.ask none) ∧ S.consumerLTS.Run .pstart w z := by
  obtain ⟨y, hs, hr⟩ := run_cons_of_nosilent (fun _ h => by cases h) h
  cases hs with
  | askInst => exact ⟨rfl, hr⟩

theorem run_pstart {o : Move (E.withInst R) (F.withInst R)} {w : List _} {z : S.St}
    (h : S.consumerLTS.Run .pstart (o :: w) z) :
    o = .inl (.ask none) ∧ S.consumerLTS.Run .pwait w z := by
  obtain ⟨y, hs, hr⟩ := run_cons_of_nosilent (fun _ h => by cases h) h
  cases hs with
  | pcall => exact ⟨rfl, hr⟩

theorem run_pwait_fail {r : R} {o : Move (E.withInst R) (F.withInst R)} {w : List _}
    {z : S.St}
    (h : S.consumerLTS.Run .pwait (.inl (.ans (m := none) (.fail r)) :: o :: w) z) :
    o = .inr (.ans (m := none) (.fail r)) := by
  obtain ⟨y, hs, hr⟩ := run_cons_of_nosilent (fun _ h => by cases h) h
  cases hs with
  | pfail r =>
    obtain ⟨y', hs', -⟩ := run_cons_of_nosilent (fun _ h => by cases h) hr
    cases hs' with
    | preport => rfl

/-! ### Consumer traces -/

/-- A P-ending prefix of a play of `ofLTS L` is a trace of `L`. -/
theorem trace_of_prefix {L : LTS E F} {t u : List (Move E F)} {o : Move E F}
    (ht : t ∈ Strategy.ofLTS L) (hu : u ++ [o] <+: t) (ho : o.IsP) : u ++ [o] ∈ L.Traces :=
  Start.trace_of_mem_ofLTS ((Strategy.ofLTS L).of_prefix ht hu) ho

theorem not_trace_ask_ans {g : Ev (F.withInst R)} :
    [.inr (.ask none), .inr g] ∉ S.consumerLTS.Traces := by
  rintro ⟨z, hz⟩
  obtain ⟨-, hr⟩ := run_fresh hz
  obtain ⟨h, -⟩ := run_pstart hr
  cases h

theorem not_trace_ask_call_ans {b : Ev (E.withInst R)} {g : Ev (F.withInst R)} :
    [.inr (.ask none), .inl b, .inr g] ∉ S.consumerLTS.Traces := by
  rintro ⟨z, hz⟩
  obtain ⟨-, hr⟩ := run_fresh hz
  obtain ⟨-, hr'⟩ := run_pstart hr
  obtain ⟨y, hs, -⟩ := run_cons_of_nosilent (fun _ h => by cases h) hr'
  cases hs

theorem trace_ask_call {m : (E.withInst R).Op}
    (h : [.inr (.ask none), .inl (.ask m)] ∈ S.consumerLTS.Traces) : m = none := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨-, hr⟩ := run_fresh hz
  obtain ⟨h, -⟩ := run_pstart hr
  cases h
  rfl

theorem trace_fail_next {r : R} {o : Move (E.withInst R) (F.withInst R)}
    (h : [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (.fail r)), o] ∈
      S.consumerLTS.Traces) : o = .inr (.ans (m := none) (.fail r)) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨-, hr⟩ := run_fresh hz
  obtain ⟨-, hr'⟩ := run_pstart hr
  exact run_pwait_fail hr'

/-! ### Legality of the first moves -/

theorem legal_second {b : Ev (E.withInst R)}
    {w : List (Move (E.withInst R) (F.withInst R))}
    (h : Legal (.inr (.ask none) :: .inl b :: w)) : ∃ m, b = .ask m := by
  obtain ⟨y, hp⟩ := h
  cases hp with
  | cons hs hp' =>
    cases hs with
    | ask _ =>
      cases hp' with
      | cons hs' _ => cases hs' with | call _ m => exact ⟨m, rfl⟩

theorem legal_third {m : (E.withInst R).Op} {b : Ev (E.withInst R)}
    {w : List (Move (E.withInst R) (F.withInst R))}
    (h : Legal (.inr (.ask none) :: .inl (.ask m) :: .inl b :: w)) :
    ∃ n, b = .ans m n := by
  obtain ⟨y, hp⟩ := h
  cases hp with
  | cons hs hp' =>
    cases hs with
    | ask _ =>
      cases hp' with
      | cons hs' hp'' =>
        cases hs' with
        | call _ _ =>
          cases hp'' with
          | cons hs'' _ => cases hs'' with | reply _ _ n => exact ⟨n, rfl⟩

theorem legal_fourth {n : InstAns R} {b : Ev (E.withInst R)}
    {w : List (Move (E.withInst R) (F.withInst R))}
    (h : Legal (.inr (.ask none) :: .inl (.ask none) :: .inl (.ans (m := none) n) :: .inl b :: w)) :
    ∃ m, b = .ask m := by
  obtain ⟨y, hp⟩ := h
  cases hp with
  | cons hs hp' =>
    cases hs with
    | ask _ =>
      cases hp' with
      | cons hs' hp'' =>
        cases hs' with
        | call _ _ =>
          cases hp'' with
          | cons hs'' hp''' =>
            cases hs'' with
            | reply _ _ _ =>
              cases hp''' with
              | cons hs''' _ => cases hs''' with | call _ m => exact ⟨m, rfl⟩

/-! ### The provider is ready first -/

/-- The consumer's play cannot start with a lower move. -/
theorem not_legal_inl {b : Ev (E.withInst R)} {w : List (Move (E.withInst R) (F.withInst R))} :
    ¬ Legal (.inl b :: w) := by
  rintro ⟨y, hp⟩
  cases hp with
  | cons hs _ => cases hs

/-- After the provider's failure the consumer answers nothing else. -/
theorem after_fail {r : R} {t₀ : List (Move (E.withInst R) (F.withInst R))}
    {s : List (Move X (E.withInst R))}
    (ht : [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (InstAns.fail r))] ++ t₀ ∈
      Strategy.ofLTS S.consumerLTS)
    (hz : Zip s t₀ [.inr (.ans (m := none) InstAns.ready)]) : False := by
  have hl : Legal ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (InstAns.fail r))] ++ t₀) :=
    (Strategy.ofLTS S.consumerLTS).legal ht
  cases hz with
  | right c _ =>
    have htr := trace_of_prefix ht ⟨_, rfl⟩ (o := .inr (.ans (m := none) InstAns.ready))
      (u := [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (InstAns.fail r))]) trivial
    cases trace_fail_next htr
  | sync b _ =>
    obtain ⟨m, rfl⟩ : ∃ m, b = .ask m := legal_fourth hl
    have htr := trace_of_prefix ht ⟨_, rfl⟩ (o := .inl (.ask m))
      (u := [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (InstAns.fail r))]) trivial
    cases trace_fail_next htr

/-- After the provider's instantiation question and its call, the provider's answer is
`ready` if the consumer answers `ready`. -/
theorem ready_after_call {δ : DStrategy X (E.withInst R)} {s : List (Move X (E.withInst R))}
    {t : List (Move (E.withInst R) (F.withInst R))}
    (hs : .inr (.ask none) :: s ∈ δ.toStrategy)
    (ht : .inr (.ask none) :: .inl (.ask none) :: t ∈ Strategy.ofLTS S.consumerLTS)
    (hz : Zip s t [.inr (.ans (m := none) .ready)]) : δ.InstReady := by
  have hlt : Legal (.inr (.ask none) :: .inl (.ask none) :: t) :=
    (Strategy.ofLTS S.consumerLTS).legal ht
  cases hz with
  | right c'' _ =>
    exact absurd (trace_of_prefix ht ⟨_, rfl⟩ (u := [_, _]) trivial) not_trace_ask_call_ans
  | sync b₂ hz₃ =>
    obtain ⟨n, rfl⟩ := legal_third hlt
    cases n with
    | fail r => exact (after_fail ht hz₃).elim
    | ready => exact δ.toStrategy.of_prefix hs ⟨_, rfl⟩

/-- **Linking is ready only after the provider** (any provider strategy, any consumer
system): if the linked component may answer `ready` to the instantiation question, so may
the provider. -/
theorem link_instReady_imp {δ : DStrategy X (E.withInst R)} (h : (δ.link S).InstReady) :
    δ.InstReady := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  have hlt : Legal t := (Strategy.ofLTS S.consumerLTS).legal ht
  cases hz with
  | sync b _ => exact absurd hlt not_legal_inl
  | right c hz₁ =>
    cases hz₁ with
    | right c' _ => exact absurd (trace_of_prefix ht ⟨_, rfl⟩ (u := [_]) trivial) not_trace_ask_ans
    | sync b₁ hz₂ =>
      obtain ⟨m, rfl⟩ := legal_second hlt
      have hm : m = none := trace_ask_call (trace_of_prefix ht ⟨_, rfl⟩ (u := [_]) trivial)
      exact ready_after_call (hm ▸ hs) (hm ▸ ht) hz₂

end Silmaril.Proofs.Wasm.Game.LinkStart
