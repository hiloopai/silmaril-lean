module

public import Silmaril.Proofs.Wasm.Game.Adequacy.Main

/-!
# Adequacy after any history of the closed program

The closed program `K.strategy ≫ I.strategy P s` is stateful: after it has
answered an export call `f` with `w`, it continues as the closed program at
the store left by some Core run of that call (`closedWith_after_iff`, every
profile); in a deterministic profile that run, hence the store, is unique
(`closedWith_after`). With adequacy at every well-formed store this gives
adequacy of every later observation of the closed program itself
(`adequacy_after_profile` for the terminating observations under every
profile, `adequacy_after` for all observations under `profile o`), by
induction for any finite history of answered calls.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- Core reduction under an induced host has the one-step diamond property. -/
theorem hostOf_join {o : GrowOracle} {ts : List FnType} {K : Silmaril.Wasm.Game.Env (ifaceSig ts)}
    {x a b : Config Nat} (ha : Step (profile o) (hostOf ts K) x a)
    (hb : Step (profile o) (hostOf ts K) x b) :
    Det.Join (Step (profile o) (hostOf ts K)) a b := by
  have hu : ∀ h s args out₁ out₂, hostOf ts K h s args out₁ → hostOf ts K h s args out₂ →
      out₁ = out₂ := fun _ _ _ _ _ h₁ h₂ => hostOf_out_unique h₁ h₂
  cases hd : decompose? x.store x.code with
  | none => exact Step.deterministic_profile hd ha hb
  | some y =>
    rw [Step.eq_of_callout hu hd ha hb]
    exact Det.Join.rfl'

/-- Runs to results under an induced host are unique (deterministic profiles). -/
theorem steps_result_unique {o : GrowOracle} {ts : List FnType}
    {K : Silmaril.Wasm.Game.Env (ifaceSig ts)} {c c₁ c₂ : Config Nat} {r₁ r₂ : Result}
    (h₁ : Steps (profile o) (hostOf ts K) c c₁) (f₁ : c₁.code = r₁.toAdmin)
    (h₂ : Steps (profile o) (hostOf ts K) c c₂) (f₂ : c₂.code = r₂.toAdmin) : c₁ = c₂ :=
  nf_unique_of_join (fun ha hb => hostOf_join ha hb) h₁ h₂
    (fun _ h => Step.not_result f₁ h) (fun _ h => Step.not_result f₂ h)

namespace Env

variable {E : Sig.{0}} {K : Silmaril.Wasm.Game.Env E}

open Silmaril.Wasm.Game.Env

theorem Agrees.append {l m : List (Ev E)} (hl : K.Agrees l) (he : Even l.length)
    (hm : K.Agrees m) : K.Agrees (l ++ m) := by
  induction hl with
  | nil => exact hm
  | pending e => simp at he
  | answered hw _ ih =>
    exact .answered hw (ih (by simpa [Nat.even_add_one, parity_simps] using he))

theorem Agrees.of_append {l m : List (Ev E)} (hl : K.Agrees l) (he : Even l.length)
    (h : K.Agrees (l ++ m)) : K.Agrees m := by
  induction hl with
  | nil => exact h
  | pending e => simp at he
  | answered _ _ ih =>
    cases h with
    | answered _ h' => exact ih (by simpa [Nat.even_add_one, parity_simps] using he) h'

end Env

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance}

/-- Lower events between two running positions of the same question come in answered
pairs. -/
theorem even_of_path_run {f : I.F.Op} :
    ∀ (l : List (Ev I.E)), Silmaril.Games.Path (Pos.run f) (l.map .inl : List (Move I.E I.F))
      (Pos.run f) → Even l.length
  | [], _ => ⟨0, rfl⟩
  | [_], h => by
    cases h with
    | cons h₁ h₂ => cases h₁; cases h₂
  | _ :: _ :: l, h => by
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      cases h₂ with
      | cons h₃ h₄ =>
        cases h₃
        have := even_of_path_run l h₄
        simpa [Nat.even_add_one, parity_simps] using this

/-- The run `t` splits at the answer `w` of the question `f` asked of thread `th` at store
`s`: the conclusion of `split_at_answer`. -/
private def SplitsAt (P : Profile) (K : Silmaril.Wasm.Game.Env I.E) (f : I.F.Op)
    (w : I.F.Ar f) (s : Store Nat) (th : Thread) (q : I.HState) (u : List (Ev I.F))
    (t : List (Move I.E I.F)) : Prop :=
  ∃ (t₁ t₂ : List (Move I.E I.F)) (c' : Config Nat) (r : Result), t = t₁ ++ t₂ ∧
    Steps P (hostOf I.imports K) (th.config s) c' ∧ c'.code = r.toAdmin ∧
    Answer.ofResult? (I.exports.get f.1) r = some w ∧
    I.Path P (.idle c'.store) t₂ q ∧ upper t₂ = u ∧ K.Agrees (lower t₂) ∧
    K.Agrees (lower t₁) ∧ Even (lower t₁).length

/-- A split of the run after an import call answered as `K` answers it is a split of the
run with that call in front. -/
private theorem SplitsAt.answered {P : Profile} {K : Silmaril.Wasm.Game.Env I.E}
    {f : I.F.Op} {w : I.F.Ar f} {s s' : Store Nat} {th t' : Thread} {q : I.HState}
    {u : List (Ev I.F)} {rest : List (Move I.E I.F)} {h : Nat} {args : List Val}
    {e : I.E.Op} {v : I.E.Ar e} (run : Reach P (s, th) (s', t'))
    (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hans : K.Answers e v)
    (hs : SplitsAt P K f w s' (resumeResult s' t' (Answer.toResult (ft := I.imports.get e.1) v))
      q u rest) :
    SplitsAt P K f w s th q u (.inl (.ask e) :: .inl (.ans e v) :: rest) := by
  obtain ⟨t₁, t₂, c', r, ht, hsteps, hfinal, hans', hp₂, hu₂, hK₂, hK₁, he₁⟩ := hs
  have hcall : Steps P (hostOf I.imports K) (th.config s)
      ((resumeResult s' t' (Answer.toResult (ft := I.imports.get e.1) v)).config s') :=
    (Reach.steps (host := hostOf I.imports K) run).tail
      (calloutAt_step (P := P) (host := hostOf I.imports K) callout ⟨_, op, Or.inl ⟨_, hans, rfl⟩⟩)
  refine ⟨.inl (.ask _) :: .inl (.ans _ v) :: t₁, t₂, c', r, by rw [ht]; rfl, hcall.trans hsteps,
    hfinal, hans', hp₂, hu₂, hK₂, by simpa using Silmaril.Wasm.Game.Env.Agrees.answered hans hK₁,
    by simpa [Nat.even_add_one, parity_simps] using he₁⟩

/-- Splitting a run from a running state at the answer of its question. -/
theorem split_at_answer {P : Profile} {K : Silmaril.Wasm.Game.Env I.E} {f : I.F.Op}
    {w : I.F.Ar f} : ∀ (n : Nat) (t : List (Move I.E I.F)) (s : Store Nat) (th : Thread)
      (q : I.HState) (u : List (Ev I.F)), t.length ≤ n → I.Path P (.running f s th) t q →
      upper t = .ans f w :: u → K.Agrees (lower t) →
      ∃ (t₁ t₂ : List (Move I.E I.F)) (c' : Config Nat) (r : Result), t = t₁ ++ t₂ ∧
        Steps P (hostOf I.imports K) (th.config s) c' ∧ c'.code = r.toAdmin ∧
        Answer.ofResult? (I.exports.get f.1) r = some w ∧
        I.Path P (.idle c'.store) t₂ q ∧ upper t₂ = u ∧ K.Agrees (lower t₂) ∧
        K.Agrees (lower t₁) ∧ Even (lower t₁).length := by
  intro n
  induction n with
  | zero =>
    intro t s th q u hn _ hu _
    exact absurd hu (by simp [List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)])
  | succ n ih =>
    intro t s th q u hn hp hu hK
    rcases hp with _ | ⟨_ | ⟨run, callout, op⟩ | _ | ⟨run, final, answer⟩, hrest⟩
    · exact absurd hu (by simp)
    · rcases hrest with _ | ⟨_ | _ | ⟨v⟩ | _, hrest'⟩
      · exact absurd hu (by simp)
      · obtain _ | _ | ⟨hans, hK'⟩ := hK
        exact SplitsAt.answered run callout op hans
          (ih _ _ _ _ _ (Nat.le_of_succ_le (Nat.le_of_succ_le_succ hn)) hrest' hu hK')
    · obtain ⟨hw, hu'⟩ := List.cons.inj hu
      cases hw
      exact ⟨[.inr (.ans f _)], _, _, _, rfl, Reach.steps run, final, answer,
        by rwa [Thread.config_store], hu', by simpa using hK, .nil, ⟨0, rfl⟩⟩

/-- **The closed program after an answered call, every profile.** After the moves `f`, `w`,
the closed program at `s` continues as the closed program at the store `c'.store` left by
*some* Core run of `f` under the induced host that ends in a result read as `w`. Under a
nondeterministic profile several such runs, hence several stores, may exist. -/
theorem closedWith_after_iff {P : Profile} {s : Store Nat}
    {K : Silmaril.Wasm.Game.Env I.E} {f : I.F.Op} {w : I.F.Ar f}
    (p : List (Move Sig.empty I.F)) :
    [.inr (.ask f), .inr (.ans f w)] ++ p ∈ I.closedWith P s K ↔
      ∃ (c' : Config Nat) (r : Result),
        Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
        c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        p ∈ I.closedWith P c'.store K := by
  unfold Silmaril.Wasm.Game.ScalarInstance.closedWith
  rw [Env.mem_comp_iff]
  refine ⟨fun ⟨t, ht, hK', hp⟩ => ?_, fun ⟨c', r, run, final, hr, hp'⟩ => ?_⟩
  · show ∃ (c' : Config Nat) (r : Result),
      Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
      c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
      p ∈ (K.strategy.comp (I.strategy P c'.store))
    obtain ⟨q, hq⟩ : ∃ q, I.Path P (.idle s) t q := mem_strategy_iff.1 ht
    obtain ⟨f', t', rfl, hrest⟩ : ∃ f' t', t = .inr (.ask f') :: t' ∧
        I.Path P (.running f' s (I.initThread f')) t' q := by
      rcases hq with _ | ⟨⟨⟩, hrest⟩
      · exact absurd hp (by simp)
      · exact ⟨_, _, rfl, hrest⟩
    obtain ⟨hf, h2⟩ := List.cons.inj hp
    obtain rfl : f = f' := Ev.ask.inj (Sum.inr.inj hf)
    obtain ⟨x, u, hx, hxw, hu⟩ := List.map_eq_cons_iff.1 h2.symm
    obtain rfl : x = Ev.ans f w := Sum.inr.inj hxw
    have hK'' : K.Agrees (lower t') := hK'
    obtain ⟨-, t₂, c', r', -, hsteps, hfinal, hr', hp₂', hu₂, hK₂, -, -⟩ :=
      split_at_answer _ _ _ _ _ _ (Nat.le_refl _) hrest hx hK''
    refine ⟨c', r', hsteps, hfinal, hr', ?_⟩
    rw [Env.mem_comp_iff]
    exact ⟨t₂, mem_strategy_iff.2 ⟨_, hp₂'⟩, hK₂, by rw [hu₂]; simpa using hu.symm⟩
  · show ∃ t ∈ I.strategy P s, K.Agrees (lower t) ∧
      [.inr (.ask f), .inr (.ans f w)] ++ p = (upper t).map .inr
    obtain ⟨t₂, ht₂, hK₂, hp⟩ := Env.mem_comp_iff.1 hp'
    show ∃ t ∈ I.strategy P s, K.Agrees (lower t) ∧
      [.inr (.ask f), .inr (.ans f w)] ++ p = (upper t).map .inr
    obtain ⟨q, hq⟩ : ∃ q, I.Path P (.idle c'.store) t₂ q := mem_strategy_iff.1 ht₂
    obtain ⟨l, hl, hpath⟩ : ∃ l : List (Ev I.E), K.Agrees l ∧
        I.Path P (.running f s (I.initThread f)) (l.map .inl ++ [.inr (.ans f w)])
          (.idle c'.store) :=
      path_of_steps (K := K) hr run final s (I.initThread f) rfl
    have heven : Even l.length := by
      obtain ⟨x, hx, hxs⟩ := Silmaril.Games.Path.concat_iff.1 (Path.legal hpath)
      cases hxs
      exact even_of_path_run l hx
    refine ⟨.inr (.ask f) :: (l.map .inl ++ [.inr (.ans f w)]) ++ t₂,
      mem_strategy_iff.2 ⟨q, Path.append_iff.2 ⟨_, .cons (.call s f) hpath, hq⟩⟩, ?_, ?_⟩
    · simpa using Env.Agrees.append hl heven hK₂
    · simp [hp]

/-- **The closed program after an answered call, deterministic profiles.** If the Core run of
the export call `f` under the induced host ends in `c'` with a result read as `w`, then after
the moves `f`, `w` the closed program at `s` continues as the closed program at `c'.store`. -/
theorem closedWith_after {o : GrowOracle} {s : Store Nat}
    {K : Silmaril.Wasm.Game.Env I.E} {f : I.F.Op}
    {w : I.F.Ar f} {c' : Config Nat} {r : Result}
    (run : Steps (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (hr : Answer.ofResult? (I.exports.get f.1) r = some w)
    (p : List (Move Sig.empty I.F)) :
    [.inr (.ask f), .inr (.ans f w)] ++ p ∈ I.closedWith (profile o) s K ↔
      p ∈ I.closedWith (profile o) c'.store K := by
  rw [closedWith_after_iff]
  constructor
  · rintro ⟨c'', r', hsteps, hfinal, -, hp⟩
    obtain rfl : c'' = c' := steps_result_unique hsteps hfinal run final
    exact hp
  · intro hp
    exact ⟨c', r, run, final, hr, hp⟩

/-- **Adequacy after an answered call, every profile.** After the closed program has answered
`f` with `w`, its terminating observations (returns, traps, exceptions) for the next question
`f'` are the Core results of `f'` at the stores left by the Core runs of `f` that end in a
result read as `w`. -/
theorem adequacy_after_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {w : I.F.Ar f} (f' : I.F.Op) (b : Behaviour Val) (hb : b ≠ .diverges) :
    b ∈ compositeObsAfter (I.closedWith P s K) [.inr (.ask f), .inr (.ans f w)] f' ↔
      ∃ (c' : Config Nat) (r : Result),
        Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
        c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        b ∈ behaviours P (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 := by
  have hafter : b ∈ compositeObsAfter (I.closedWith P s K) [.inr (.ask f), .inr (.ans f w)] f' ↔
      ∃ w', [.inr (.ask f), .inr (.ans f w)] ++ [.inr (.ask f'), .inr (.ans f' w')] ∈
        I.closedWith P s K ∧ b = Answer.toBehaviour (ft := I.exports.get f'.1) w' :=
    ⟨fun h => h.resolve_right fun hd => hb hd.1, Or.inl⟩
  have hat : ∀ {c' : Config Nat} {r : Result},
      Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' → c'.code = r.toAdmin →
      (b ∈ behaviours P (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 ↔
        ∃ w', Responds (I.closedWith P c'.store K) f' w' ∧
          b = Answer.toBehaviour (ft := I.exports.get f'.1) w') := fun run final => by
    obtain ⟨hw', hK'⟩ := wellFormed_after_run hw hK run final
    exact (adequacy_answers hw' K hK' f' b hb).trans
      ⟨fun h => h.resolve_right fun hd => hb hd.1, Or.inl⟩
  rw [hafter]
  constructor
  · rintro ⟨w', hw', hbw⟩
    obtain ⟨c', r, run, final, hr, hresp⟩ := (closedWith_after_iff _).1 hw'
    exact ⟨c', r, run, final, hr, (hat run final).2 ⟨w', hresp, hbw⟩⟩
  · rintro ⟨c', r, run, final, hr, hmem⟩
    obtain ⟨w', hresp, hbw⟩ := (hat run final).1 hmem
    exact ⟨w', (closedWith_after_iff _).2 ⟨c', r, run, final, hr, hresp⟩, hbw⟩

/-- **Adequacy after an answered call, deterministic profiles.** After the closed program has
answered `f` with `w` (the Core run of `f` ending in `c'`), its observations for the next
question `f'` are the Core behaviours of `f'` at the store `c'.store`. -/
theorem adequacy_after {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {w : I.F.Ar f} {c' : Config Nat} {r : Result}
    (run : Steps (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (hr : Answer.ofResult? (I.exports.get f.1) r = some w)
    (f' : I.F.Op) :
    compositeObsAfter (I.closedWith (profile o) s K) [.inr (.ask f), .inr (.ans f w)] f' =
      behaviours (profile o) (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 := by
  rw [adequacy_later hw K hK run final f']
  unfold Silmaril.Wasm.Game.compositeObsAfter Silmaril.Wasm.Game.compositeObs Silmaril.Wasm.Game.Responds
  simp only [closedWith_after run final hr]

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
