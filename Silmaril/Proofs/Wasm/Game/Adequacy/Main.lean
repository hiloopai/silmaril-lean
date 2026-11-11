module

public import Silmaril.Proofs.Wasm.Game.Adequacy.Progress
public import Silmaril.Proofs.Wasm.Game.Adequacy.Preservation
public import Silmaril.Wasm.Behaviour.Semantics.Core
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Adequacy of the instance strategy against closed-world behaviours: proofs

The two inclusions between the Core closed-world behaviours of an export call
under `hostOf K` and the observations `compositeObs` of
`K.strategy ≫ I.strategy P s`, both covering divergence; the closed and
diverging-host special cases; later calls.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : ScalarInstance}

/-! ### The diverging host against the silent environment

`divHost` diverges on every host call, `hostOf ts (Silmaril.Wasm.Game.Env.silent _)` only on valid import calls
(`hostOf_silent`). Along runs from a well-formed invocation every callout is a valid import
call (`good_callout_valid`), so the two hosts have the same runs and divergences. -/

theorem divHost_step_hostOf {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {ts : List CValType} {c c' : Config Nat} (hg : Good s ts c)
    (h : Step P Silmaril.Wasm.Game.divHost c c') :
    Step P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _)) c c' :=
  step_host_congr h fun _ _ _ _ _ hd hout => by
    obtain ⟨e, he⟩ := good_callout_valid (P := P) hw (throwsBelow_silent _ _) hg hd
    exact (hostOf_silent _ _ _ _ _).mpr ⟨by rw [he]; rfl, hout⟩

theorem hostOf_silent_step_divHost {P : Profile} {c c' : Config Nat}
    (h : Step P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _)) c c') :
    Step P Silmaril.Wasm.Game.divHost c c' :=
  step_host_congr h fun _ _ _ _ _ _ hout => ((hostOf_silent _ _ _ _ _).mp hout).2

theorem divHost_steps_iff {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {ts : List CValType} {c₀ : Config Nat} (hg : Good s ts c₀) (c' : Config Nat) :
    Steps P Silmaril.Wasm.Game.divHost c₀ c' ↔
      Steps P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _)) c₀ c' := by
  constructor
  · intro h
    have key : Steps P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _)) c₀ c' ∧ Good s ts c' := by
      induction h with
      | refl => exact ⟨.refl, hg⟩
      | tail _ hst ih =>
        have hst' := divHost_step_hostOf hw ih.2 hst
        exact ⟨ih.1.tail hst', good_step hw (throwsBelow_silent _ _) ih.2 hst'⟩
    exact key.1
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail (hostOf_silent_step_divHost hst)

theorem divHost_diverges_iff {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {ts : List CValType} {c₀ : Config Nat} (hg : Good s ts c₀) :
    Diverges P Silmaril.Wasm.Game.divHost c₀ ↔
      Diverges P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _)) c₀ := by
  constructor
  · intro h
    show InfiniteTrace (Step P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))) c₀
    refine InfiniteTrace.coinduct
      (fun c => Good s ts c ∧ InfiniteTrace (Step P Silmaril.Wasm.Game.divHost) c) ?_ ⟨hg, h⟩
    rintro c ⟨hgc, hinf⟩
    obtain ⟨b, hb, hinf'⟩ := hinf.unfold
    have hb' := divHost_step_hostOf hw hgc hb
    exact ⟨b, hb', good_step hw (throwsBelow_silent _ _) hgc hb', hinf'⟩
  · intro h
    exact InfiniteTrace.map id (fun _ _ hst => hostOf_silent_step_divHost hst) h

/-- From a well-formed store, `divHost` and the host induced by the silent environment have
the same behaviours. -/
theorem behaviours_divHost_eq {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (f : I.F.Op) :
    behaviours P Silmaril.Wasm.Game.divHost s (I.addr f.1) f.2.1 =
      behaviours P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _)) s (I.addr f.1) f.2.1 := by
  obtain ⟨ts, hg⟩ := good_invoke hw f
  ext b
  simp only [behaviours_eq, behavioursOf, Set.mem_union, Set.mem_ofPred_eq,
    divHost_steps_iff (P := P) hw hg, divHost_diverges_iff (P := P) hw hg]

/-! ### Adequacy (M2) -/

/-- Terminating operational behaviours are answers of the composite (every profile). -/
theorem result_mem_compositeObs {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op)
    {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) : r.toBehaviour ∈ compositeObs (I.closedWith P s K) f := by
  obtain ⟨w, hw', hans⟩ := answer_of_run hw hK run final
  refine Or.inl ⟨w, hans, ?_⟩
  unfold Answer.toBehaviour
  rw [Answer.toResult_of_ofResult? hw']

/-- **Operational behaviours are composite observations or divergence (every profile).** -/
theorem behaviours_subset_compositeObs_union {P : Profile} {s : Store Nat}
    (hw : I.WellFormed s) (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length)
    (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 ⊆
      compositeObs (I.closedWith P s K) f ∪
        {b | b = .diverges ∧ Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1)} := by
  intro b hb
  simp only [behaviours_eq, behavioursOf, Set.mem_union, Set.mem_ofPred_eq] at hb
  rcases hb with ⟨c', r, run, final, rfl⟩ | hdiv
  · exact Or.inl (result_mem_compositeObs hw K hK f run final)
  · exact Or.inr hdiv

/-- Operational behaviours are composite observations, including divergence (deterministic
profiles). -/
theorem behaviours_subset_compositeObs {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours (profile o) (hostOf I.imports K) s (I.addr f.1) f.2.1 ⊆
      compositeObs (I.closedWith (profile o) s K) f := by
  intro b hb
  rcases behaviours_subset_compositeObs_union hw K hK f hb with h | ⟨rfl, hdiv⟩
  · exact h
  · exact Or.inr ⟨rfl, (diverges_iff_no_answer hw hK).mp hdiv⟩

/-- **Composite observations are operational behaviours** (including divergence as the
absence of an answer), every profile. -/
theorem compositeObs_subset_behaviours {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    compositeObs (I.closedWith P s K) f ⊆
      behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 := by
  intro b hb
  simp only [compositeObs, Set.mem_union, Set.mem_ofPred_eq] at hb
  rw [behaviours_eq]
  rcases hb with ⟨w, hans, rfl⟩ | ⟨rfl, hno⟩
  · obtain ⟨c', r, run, final, hr⟩ := run_of_answer hans
    have hb : Answer.toBehaviour w = r.toBehaviour := by
      unfold Answer.toBehaviour
      rw [Answer.toResult_of_ofResult? hr]
    rw [hb]
    exact mem_behavioursOf run final
  · exact diverges_mem_behavioursOf_iff.mpr (diverges_of_no_answer hw hK hno)

/-- **M2 for every profile.** The closed-world behaviours of an export call are the
observations of the composite together with may-divergence: the answers of
`K.strategy ≫ I.strategy P s` are exactly the terminating behaviours, the absence of an
answer is divergence, and divergence is a behaviour exactly when the invocation has an
infinite run. -/
theorem adequacy_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s K) f ∪
        {b | b = .diverges ∧ Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1)} := by
  refine Set.Subset.antisymm (behaviours_subset_compositeObs_union hw K hK f) ?_
  rintro b (hb | ⟨rfl, hdiv⟩)
  · exact compositeObs_subset_behaviours hw K hK f hb
  · exact diverges_mem_behavioursOf_iff.mpr hdiv

/-- **M2 for every profile, terminating observations.** A return, trap or uncaught exception
is a closed-world behaviour exactly when it is an answer of the composite. -/
theorem adequacy_answers {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op)
    (b : Behaviour Val) (hb : b ≠ .diverges) :
    b ∈ behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 ↔
      b ∈ compositeObs (I.closedWith P s K) f := by
  rw [adequacy_profile hw K hK f]
  constructor
  · rintro (h | ⟨rfl, -⟩)
    · exact h
    · exact absurd rfl hb
  · exact Or.inl

/-- **M2 for every profile, exact form.** If the invocation cannot both diverge and answer
(always the case in a deterministic profile), the closed-world behaviours are exactly the
composite observations. -/
theorem adequacy_of_no_mixed {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op)
    (hmixed : Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) →
      ∀ w, ¬ Responds (I.closedWith P s K) f w) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s K) f := by
  rw [adequacy_profile hw K hK f]
  refine Set.union_eq_left.mpr ?_
  rintro b ⟨rfl, hdiv⟩
  exact Or.inr ⟨rfl, hmixed hdiv⟩

/-- **M2 (adequacy), deterministic profiles.** For a strategy-definable host whose
environment throws only existing exceptions, the closed-world behaviours of an export call
are exactly the observations of the composite: the behaviours of its answers for terminating
runs, and `diverges` for the absence of an answer. -/
theorem adequacy {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours (profile o) (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith (profile o) s K) f :=
  adequacy_of_no_mixed hw K hK f (diverges_iff_no_answer hw hK).mp

/-- Environment answers in a play built from events agreeing with `K` throw below `n`. -/
theorem playThrowsBelow_of_agrees {K : Silmaril.Wasm.Game.Env I.E} {n : Nat}
    (hK : ThrowsBelow K n) {f : I.F.Op} {l : List (Ev I.E)} (hl : K.Agrees l) (w : I.F.Ar f) :
    I.PlayThrowsBelow n (.inr (.ask f) :: (l.map .inl ++ [.inr (.ans f w)])) := by
  intro e v hmem
  simp only [List.mem_cons, List.mem_append, List.mem_map, reduceCtorEq, false_or,
    List.not_mem_nil, or_false] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  cases hxe
  exact hK e v (Env.Agrees.answers hl hx)

/-- The store left by a closed-world run of an export call to a result is well formed, and
the environment still throws only existing exceptions there (every profile). -/
theorem wellFormed_after_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) :
    I.WellFormed c'.store ∧ ThrowsBelow K c'.store.exns.length := by
  obtain ⟨l, w, -, hl, hact⟩ := activation_of_run hw hK run final
  obtain ⟨hw', hle⟩ := WellFormed.activation hw (playThrowsBelow_of_agrees hK hl w) hact
  exact ⟨hw', throwsBelow_mono hK hle⟩

/-- **M2, later calls, every profile.** After a closed-world run of the export call `f` to a
result in configuration `c'`, the next export call `f'` is adequate (in the sense of
`adequacy_profile`) at the store `c'.store` that the run leaves. -/
theorem adequacy_later_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (f' : I.F.Op) :
    behaviours P (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 =
      compositeObs (I.closedWith P c'.store K) f' ∪
        {b | b = .diverges ∧
          Diverges P (hostOf I.imports K) (invoke c'.store (I.addr f'.1) f'.2.1)} := by
  obtain ⟨hw', hK'⟩ := wellFormed_after_run hw hK run final
  exact adequacy_profile hw' K hK' f'

/-- **M2, later calls, deterministic profiles.** After a closed-world run of the export call
`f` to a result in configuration `c'`, the next export call `f'` is adequate at the store
`c'.store` that the run leaves, which is the store the strategy persists
(`activation_of_run`). -/
theorem adequacy_later {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    (K : Silmaril.Wasm.Game.Env I.E) (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {c' : Config Nat} {r : Result}
    (run : Steps (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (f' : I.F.Op) :
    behaviours (profile o) (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 =
      compositeObs (I.closedWith (profile o) c'.store K) f' := by
  obtain ⟨hw', hK'⟩ := wellFormed_after_run hw hK run final
  exact adequacy hw' K hK' f'

/-- With no imports, the induced host is the empty host. -/
theorem hostOf_of_imports_nil (hI : I.imports = []) (K : Silmaril.Wasm.Game.Env I.E) :
    hostOf I.imports K = (fun _ _ _ _ => False : HostSemantics Nat) ∧
      ∀ n, ThrowsBelow K n := by
  have hE : ∀ e : I.E.Op, False := fun e => absurd e.1.2 (by simp [hI])
  refine ⟨?_, fun _ e => (hE e).elim⟩
  funext h s' args out
  apply propext
  constructor
  · rintro ⟨e, -⟩
    exact (hE e).elim
  · intro h
    exact h.elim

/-- Adequacy for closed programs under the empty host, every profile: with no imports, the
behaviours under `noHost` are the observations of the closed strategy together with
may-divergence. -/
theorem adequacy_closed_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (hI : I.imports = []) (K : Silmaril.Wasm.Game.Env I.E) (f : I.F.Op) :
    behaviours P (fun _ _ _ _ => False : HostSemantics Nat) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s K) f ∪
        {b | b = .diverges ∧
          Diverges P (fun _ _ _ _ => False : HostSemantics Nat) (invoke s (I.addr f.1) f.2.1)} := by
  obtain ⟨hhost, hK⟩ := hostOf_of_imports_nil hI K
  have := adequacy_profile (P := P) hw K (hK _) f
  rwa [hhost] at this

/-- Adequacy for closed programs under the empty host (`noHost`), deterministic profiles: with
no imports, the behaviours under `noHost` are the observations of the closed strategy
(composed with the unique environment over the empty interface). -/
theorem adequacy_closed {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    (hI : I.imports = []) (K : Silmaril.Wasm.Game.Env I.E) (f : I.F.Op) :
    behaviours (profile o) (fun _ _ _ _ => False : HostSemantics Nat) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith (profile o) s K) f := by
  obtain ⟨hhost, hK⟩ := hostOf_of_imports_nil hI K
  have := adequacy (o := o) hw K (hK _) f
  rwa [hhost] at this

/-- Adequacy under the diverging host, every profile: against the silent environment,
`divHost` behaviours are the composite observations together with may-divergence. -/
theorem adequacy_divHost_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (f : I.F.Op) :
    behaviours P Silmaril.Wasm.Game.divHost s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s (Silmaril.Wasm.Game.Env.silent _)) f ∪
        {b | b = .diverges ∧ Diverges P (hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
          (invoke s (I.addr f.1) f.2.1)} := by
  rw [behaviours_divHost_eq hw f]
  exact adequacy_profile hw _ (throwsBelow_silent _ _) f

/-- Adequacy under the diverging host, deterministic profiles: against the silent
environment, `divHost` behaviours are the composite observations. -/
theorem adequacy_divHost {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s) (f : I.F.Op) :
    behaviours (profile o) Silmaril.Wasm.Game.divHost s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith (profile o) s (Silmaril.Wasm.Game.Env.silent _)) f := by
  rw [behaviours_divHost_eq hw f]
  exact adequacy hw _ (throwsBelow_silent _ _) f

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
