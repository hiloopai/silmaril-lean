module

public import Silmaril.Proofs.Wasm.Game.StatefulEnv.Runs

/-!
# Adequacy against stateful, nondeterministic hosts: proofs

* `srun_of_answer`, `sanswer_of_run`: answers of the closed program
  `L.strategy q ≫ I.strategy P s` are exactly the results of finite product
  runs from `(invoke …, q)`;
* `sdiverges_of_no_answer`: no answer means an infinite product run;
* `sadequacy`: the behaviours against the stateful host are the composite
  observations together with may-divergence;
* `closedS_after_iff`: after an answered call the closed program continues
  as the closed program at the store **and** the host state left by some
  product run of that call.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ScalarInstance

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {I : Silmaril.Wasm.Game.ScalarInstance}

/-- **Game to operations, stateful host.** An answer of the closed program comes from a
finite product run to a result. -/
theorem srun_of_answer {P : Profile} {s : Store Nat} {L : Silmaril.Wasm.Game.SEnv I.E}
    {q : L.S} {f : I.F.Op} {w : I.F.Ar f} (h : Responds (I.closedS P s L q) f w) :
    ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q') ∧
      c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w := by
  obtain ⟨p, hp, henv, hx⟩ := Silmaril.Proofs.Wasm.Game.SEnv.mem_comp_iff.1 h
  obtain ⟨x, hpath⟩ := mem_strategy_iff.1 hp
  cases hpath with
  | nil => simp at hx
  | cons htr hrest =>
    cases htr with
    | call s f' =>
      simp only [upper_cons_inr, List.map_cons, List.cons.injEq, Sum.inr.injEq] at hx
      obtain ⟨hf, hx⟩ := hx
      cases hf
      have hu : upper _ = [Ev.ans f w] :=
        List.map_injective_iff.2 Sum.inr_injective hx.symm
      obtain ⟨-, -, c', q', r, -, hs, hf, ha, -⟩ :=
        ssplit_at_answer _ _ _ _ _ _ _ (Nat.le_refl _) hrest hu
          (by simpa only [lower_cons_inr] using henv)
      exact ⟨c', q', r, hs, hf, ha⟩

/-- **Operations to game, stateful host.** A finite product run to a result is a complete
activation of the instance whose import events drive the host, and is answered by the closed
program. -/
theorem sactivation_of_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : Silmaril.Wasm.Game.SEnv I.E} (hL : L.ThrowsBelow s.exns.length) {q q' : L.S}
    {f : I.F.Op} {c' : Config Nat} {r : Result}
    (run : SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q'))
    (final : c'.code = r.toAdmin) :
    ∃ (l : List (Ev I.E)) (w : I.F.Ar f),
      Answer.ofResult? (I.exports.get f.1) r = some w ∧ L.Drive q l q' ∧
      I.Activation P s (.inr (.ask f) :: (l.map .inl ++ [.inr (.ans f w)])) c'.store := by
  obtain ⟨w, hw'⟩ := sresult_typed hw hL run final
  obtain ⟨l, hl, hp⟩ := path_of_ssteps hw' run final s (I.initThread f) rfl
  exact ⟨l, w, hw', hl, .cons (.call s f) hp⟩

theorem sanswer_of_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : Silmaril.Wasm.Game.SEnv I.E} (hL : L.ThrowsBelow s.exns.length) {q q' : L.S}
    {f : I.F.Op} {c' : Config Nat} {r : Result}
    (run : SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q'))
    (final : c'.code = r.toAdmin) :
    ∃ w, Answer.ofResult? (I.exports.get f.1) r = some w ∧
      Responds (I.closedS P s L q) f w := by
  obtain ⟨l, w, hw', hl, hp⟩ := sactivation_of_run hw hL run final
  refine ⟨w, hw', Silmaril.Proofs.Wasm.Game.SEnv.mem_comp_iff.2 ⟨_, mem_strategy_iff.2 ⟨_, hp⟩,
    ?_, by simp⟩⟩
  simpa using Silmaril.Proofs.Wasm.Game.SEnv.Drive.agrees hl

/-- **No answer is divergence, stateful host** (every profile). -/
theorem sdiverges_of_no_answer {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : Silmaril.Wasm.Game.SEnv I.E} (hL : L.ThrowsBelow s.exns.length) {q : L.S} {f : I.F.Op}
    (hno : ∀ w, ¬ Responds (I.closedS P s L q) f w) :
    InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q) := by
  refine InfiniteTrace.coinduct (fun y => SSteps P L (invoke s (I.addr f.1) f.2.1, q) y)
    ?_ Relation.ReflTransGen.refl
  intro y run
  have hg : Good s ((I.exports.get f.1).results.map ScalarType.toC) y.1 :=
    good_ssteps hw hL (good_invoke_results hw f) run
  rcases good_sprogress (P := P) hw y.2 hg with ⟨r, hr⟩ | ⟨y', hy'⟩
  · obtain ⟨w, -, hans⟩ := sanswer_of_run hw hL run hr
    exact absurd hans (hno w)
  · exact ⟨y', hy', run.tail hy'⟩

/-- **Adequacy against a stateful host** (every profile). -/
theorem sadequacy {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (L : Silmaril.Wasm.Game.SEnv I.E) (hL : L.ThrowsBelow s.exns.length) (q : L.S) (f : I.F.Op) :
    sbehavioursOf P L q (invoke s (I.addr f.1) f.2.1) =
      compositeObs (I.closedS P s L q) f ∪
        {b | b = .diverges ∧ InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q)} := by
  ext b
  constructor
  · rintro (⟨c', q', r, run, final, rfl⟩ | hdiv)
    · obtain ⟨w, hw', hans⟩ := sanswer_of_run hw hL run final
      have hb : r.toBehaviour = Answer.toBehaviour (ft := I.exports.get f.1) w := by
        unfold Answer.toBehaviour
        rw [Answer.toResult_of_ofResult? hw']
      exact Or.inl (Or.inl ⟨w, hans, hb⟩)
    · exact Or.inr hdiv
  · rintro ((⟨w, hans, rfl⟩ | ⟨rfl, hno⟩) | hdiv)
    · obtain ⟨c', q', r, run, final, hr⟩ := srun_of_answer hans
      have hb : Answer.toBehaviour (ft := I.exports.get f.1) w = r.toBehaviour := by
        unfold Answer.toBehaviour
        rw [Answer.toResult_of_ofResult? hr]
      exact Or.inl ⟨c', q', r, run, final, hb⟩
    · exact Or.inr ⟨rfl, sdiverges_of_no_answer hw hL hno⟩
    · exact Or.inr hdiv

/-- **The closed program after an answered call, stateful host.** After the moves `f`, `w`,
the closed program at `(s, q)` continues as the closed program at the store `c'.store` and the
host state `q'` left by *some* product run of `f` ending in a result read as `w`: both the
module store and the host state persist. -/
theorem closedS_after_iff {P : Profile} {s : Store Nat} {L : Silmaril.Wasm.Game.SEnv I.E}
    {q : L.S} {f : I.F.Op} {w : I.F.Ar f} (p : List (Move Sig.empty I.F)) :
    [.inr (.ask f), .inr (.ans f w)] ++ p ∈ I.closedS P s L q ↔
      ∃ (c' : Config Nat) (q' : L.S) (r : Result),
        SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q') ∧
        c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        p ∈ I.closedS P c'.store L q' := by
  unfold Silmaril.Wasm.Game.ScalarInstance.closedS
  rw [Silmaril.Proofs.Wasm.Game.SEnv.mem_comp_iff]
  refine ⟨fun ⟨t, ht, hL', hp⟩ => ?_, fun ⟨c', q', r, run, final, hr, hp'⟩ => ?_⟩
  · show ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q') ∧
      c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
      p ∈ ((L.strategy q').comp (I.strategy P c'.store))
    obtain ⟨x, hx⟩ : ∃ x, I.Path P (.idle s) t x := mem_strategy_iff.1 ht
    obtain ⟨f', t', rfl, hrest⟩ : ∃ f' t', t = .inr (.ask f') :: t' ∧
        I.Path P (.running f' s (I.initThread f')) t' x := by
      rcases hx with _ | ⟨⟨⟩, hrest⟩
      · exact absurd hp (by simp)
      · exact ⟨_, _, rfl, hrest⟩
    obtain ⟨hf, h2⟩ := List.cons.inj hp
    obtain rfl : f = f' := Ev.ask.inj (Sum.inr.inj hf)
    obtain ⟨y, u, hy, hyw, hu⟩ := List.map_eq_cons_iff.1 h2.symm
    obtain rfl : y = Ev.ans f w := Sum.inr.inj hyw
    have hL'' : L.Agrees q (lower t') := hL'
    obtain ⟨-, t₂, c', q', r', -, hsteps, hfinal, hr', hp₂', hu₂, -, hA₂⟩ :=
      ssplit_at_answer _ _ _ _ _ _ _ (Nat.le_refl _) hrest hy hL''
    refine ⟨c', q', r', hsteps, hfinal, hr', ?_⟩
    rw [Silmaril.Proofs.Wasm.Game.SEnv.mem_comp_iff]
    exact ⟨t₂, mem_strategy_iff.2 ⟨_, hp₂'⟩, hA₂, by rw [hu₂]; simpa using hu.symm⟩
  · show ∃ t ∈ I.strategy P s, L.Agrees q (lower t) ∧
      [.inr (.ask f), .inr (.ans f w)] ++ p = (upper t).map .inr
    obtain ⟨t₂, ht₂, hA₂, hp⟩ := Silmaril.Proofs.Wasm.Game.SEnv.mem_comp_iff.1 hp'
    obtain ⟨x, hx⟩ : ∃ x, I.Path P (.idle c'.store) t₂ x := mem_strategy_iff.1 ht₂
    obtain ⟨l, hl, hpath⟩ : ∃ l : List (Ev I.E), L.Drive q l q' ∧
        I.Path P (.running f s (I.initThread f)) (l.map .inl ++ [.inr (.ans f w)])
          (.idle c'.store) :=
      path_of_ssteps hr run final s (I.initThread f) rfl
    refine ⟨.inr (.ask f) :: (l.map .inl ++ [.inr (.ans f w)]) ++ t₂,
      mem_strategy_iff.2 ⟨x, Path.append_iff.2 ⟨_, .cons (.call s f) hpath, hx⟩⟩, ?_, ?_⟩
    · simpa using Silmaril.Proofs.Wasm.Game.SEnv.Drive.append_agrees hl hA₂
    · simp [hp]

end Silmaril.Proofs.Wasm.Game.ScalarInstance
