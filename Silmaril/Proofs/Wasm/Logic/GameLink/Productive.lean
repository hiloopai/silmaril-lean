module

public import Silmaril.Proofs.Wasm.Logic.GameLink.Link

/-!
# The logic and the Wasm game: productivity and divergence-aware composition

* `GameSat.of_total`: total correctness under the terminating environment
  `gameHostT` implies partial correctness under `gameHost` (which may also
  diverge: a diverging import call is a stuttering step, which total
  correctness of the configuration covers at every index);
* `dstrategy_productive`: a totally correct instance is `Productive`: in an
  infinite play whose Opponent moves are good there are infinitely many export
  moves. Otherwise, from some stage on, the run of `I.dlts P s` makes only
  silent steps and import calls with good answers (`LowStep`), which from a
  totally correct thread is an infinite Core run under `gameHostT`
  (`no_lowTrace`);
* `dcomp_sound`: the divergence-aware assume/guarantee strategies compose
  along `DStrategy.comp` when the upper strategy is productive (generic, by
  `OpenTotal.opp_zip` and `OpenTotal.no_chatter`);
* `dlink_parts_sound`: for a static link, the divergence-observing composite of
  the provider's and the consumer's strategies refines `dagStrat Ii Ie` when
  both parts are totally correct.

The extraction of a low run from an infinite run follows
`Silmaril.Proofs.Wasm.Logic.OpenTotal.Productive` (`OnRun`, `onRun_step`), with
the transition system `I.dlts P s` in place of `Open.modRed`; its generic
lemmas (`InfRun.seg`, `exists_max_of_bounded`, `Run.cons_inv`,
`lower_of_ucount_zero`) are reused. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.GameLink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded (Thread decompose? resumeResult)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (ISpec agStrat AG MoveGood comp_refines)
open Silmaril.Wasm.Logic.OpenTotal (OppGood dagStrat Productive ucount opp_zip no_chatter
  ucount_mono)

variable {I : ScalarInstance} {P : Profile} {Inv : Store Nat → Prop} {Ii : ISpec I.E}
  {Ie : ISpec I.F}

/-! ## Total correctness implies partial correctness -/

/-- A step under the game's environment is a step under the terminating one, or a
diverging import call (a stutter). -/
theorem step_gameHost_inv {c c' : Config Nat} (h : Step P (gameHost I Ii) c c') :
    Step P (gameHostT I Ii) c c' ∨ c' = c := by
  rcases SingleThreaded.Step.split_host h with h0 | ⟨E, a, k, args, hd, ⟨s', r, hr, rfl⟩ | ⟨-, rfl⟩⟩
  · exact .inl (Step.of_noHost _ h0)
  · exact .inl (Open.redex_step_ret hd hr)
  · exact .inr rfl

/-- A step under the terminating environment is a step under the game's environment. -/
theorem step_gameHostT {c c' : Config Nat} (h : Step P (gameHostT I Ii) c c') :
    Step P (gameHost I Ii) c c' :=
  Open.Step.host_mono (fun _ _ _ o ⟨S, hS, hpre, ho⟩ => ⟨S, hS, hpre, by
    cases o with
    | returned s' r => exact ho
    | diverged => exact ho.elim⟩) h

/-- A totally correct configuration is safe under the game's environment. -/
theorem safe_of_tsafe {Q : Post Nat} :
    ∀ (n : Nat) {c : Config Nat}, TSafe P (gameHostT I Ii) Q c → Safe P (gameHost I Ii) Q n c
  | 0, _, _ => trivial
  | n + 1, _, .exit o he hq => .inl ⟨o, he, hq⟩
  | n + 1, c, .step ⟨c', hc'⟩ hall => .inr ⟨⟨c', step_gameHostT hc'⟩, fun c'' hst => by
      rcases step_gameHost_inv hst with h | rfl
      · exact safe_of_tsafe n (hall c'' h)
      · exact safe_of_tsafe n (.step ⟨c', hc'⟩ hall)⟩

/-- **Total correctness implies partial correctness.** -/
theorem GameSat.of_total (hm : TGameSat P I Inv Ii Ie) : GameSat P I Inv Ii Ie :=
  fun j n s args hpre f vs₀ c hc => safe_of_tsafe n (hm j s args hpre f vs₀ c hc)

/-! ## Low runs -/

/-- A step of the instance that is silent, or a move at the import interface that is good
if it is Opponent's. -/
def LowStep (P : Profile) (I : ScalarInstance) (Ii : ISpec I.E) (Ie : ISpec I.F)
    (x y : I.HState) : Prop :=
  I.DTrans P x none y ∨
    ∃ e, I.DTrans P x (some (.inl e)) y ∧
      (Move.IsO (Sum.inl e : Move I.E I.F) → MoveGood Ii Ie (Sum.inl e : Move I.E I.F))

/-- After an import call, a low step is a good answer, and the resumed thread is a Core
successor under the terminating environment. -/
theorem low_resume {Q : Post Nat} {f : I.F.Op} {s : Store Nat} {t : Thread} {k : Nat}
    {args : List Val} {e : I.E.Op} {y : I.HState}
    (hsafe : TSafe P (gameHostT I Ii) Q (t.config s)) (callout : CalloutAt s t k args)
    (op : I.importOp? k args = some e) (hs : LowStep P I Ii Ie (.waiting f s t e) y) :
    ∃ t', y = .running f s t' ∧ Step P (gameHostT I Ii) (t.config s) (t'.config s) := by
  obtain ⟨E, a, hd⟩ := callout
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, k, args) := by
    rw [config_store]
    exact hd
  have hpre : Ii.pre e := by
    have hspec := OpenTotal.timport_pre hsafe hd'
    rw [config_store] at hspec
    exact import_pre_of_spec op hspec
  rcases hs with hs | ⟨e', hs, hg⟩
  · cases hs
  · cases hs with
    | uret v => exact ⟨_, rfl, resume_step hd (gameHostT_answer op hpre (hg trivial))⟩

/-- An infinite low run from a running, totally correct thread is a Core divergence. -/
theorem diverges_of_lowTrace {Q : Post Nat} {f : I.F.Op} {s : Store Nat} {t : Thread}
    (hsafe : TSafe P (gameHostT I Ii) Q (t.config s))
    (hd : Silmaril.InfiniteTrace (LowStep P I Ii Ie) (.running f s t)) :
    Diverges P (gameHostT I Ii) (t.config s) := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun c => ∃ s t, c = t.config s ∧ TSafe P (gameHostT I Ii) Q c ∧
      Silmaril.InfiniteTrace (LowStep P I Ii Ie) (.running f s t))
    (fun c ⟨s, t, hc, hsafe, ht⟩ => ?_) ⟨s, t, rfl, hsafe, hd⟩
  obtain ⟨y, hs, hy⟩ := Silmaril.InfiniteTrace.unfold ht
  rcases hs with hs | ⟨e, hs, -⟩
  · cases hs with
    | tau h =>
      have hst : Step P (gameHostT I Ii) c _ := hc ▸ internal_step h
      exact ⟨_, hst, _, _, rfl, hsafe.step_inv hst, hy⟩
  · cases hs with
    | ucall callout op =>
      obtain ⟨y', hs', hy'⟩ := Silmaril.InfiniteTrace.unfold hy
      obtain ⟨t', rfl, hst⟩ := low_resume (hc ▸ hsafe) callout op hs'
      have hst' : Step P (gameHostT I Ii) c (t'.config s) := hc ▸ hst
      exact ⟨_, hst', _, _, rfl, hsafe.step_inv hst', hy'⟩

/-- **No infinite low run from a state of the total invariant.** -/
theorem no_lowTrace {x : I.HState} (hx : TGood P I Inv Ii Ie x)
    (hd : Silmaril.InfiniteTrace (LowStep P I Ii Ie) x) : False := by
  cases x with
  | idle s =>
    obtain ⟨y, hs, -⟩ := Silmaril.InfiniteTrace.unfold hd
    rcases hs with hs | ⟨e, hs, -⟩ <;> cases hs
  | running f s t =>
    obtain ⟨s₀, h⟩ := hx
    exact TSafe.not_diverges h (diverges_of_lowTrace h hd)
  | waiting f s t e =>
    obtain ⟨y, hs, hy⟩ := Silmaril.InfiniteTrace.unfold hd
    obtain ⟨s₀, h⟩ := hx
    rcases hs with hs | ⟨e', hs, hg⟩
    · cases hs
    · cases hs with
      | uret v =>
        have h' := h v (hg trivial)
        exact TSafe.not_diverges h' (diverges_of_lowTrace h' hy)

/-! ## Extracting a low run from an infinite run -/

section Extract

variable {s : Store Nat}

/-- A position on the way of an infinite run, past stage `N`. -/
def OnRun (r : (I.dlts P s).InfRun) (N : Nat) (x : I.HState) : Prop :=
  ∃ n, N ≤ n ∧ ∃ w pre, (I.dlts P s).Run x w (r.st n) ∧ r.tr n = pre ++ w ∧ r.tr N <+: pre

theorem later_of_longer (r : (I.dlts P s).InfRun) {n m : Nat}
    (hm : (r.tr n).length + 1 ≤ (r.tr m).length) : n ≤ m := by
  by_contra h
  have hp : (r.tr m).length ≤ (r.tr n).length := (r.mono.le (by omega)).length_le
  omega

theorem ne_nil_of_longer {a b w : List (Move I.E I.F)} (hw : b = a ++ w)
    (hm : a.length + 1 ≤ b.length) : w ≠ [] := by
  intro h
  have hb : b.length = a.length := by simp [hw, h]
  omega

/-- The export moves after stage `N` are none. -/
theorem low_after (r : (I.dlts P s).InfRun) {N m : Nat}
    (hN : ucount (r.tr m) = ucount (r.tr N)) {u ww : List (Move I.E I.F)}
    (htrm : r.tr m = (r.tr N ++ u) ++ ww) : ucount (u ++ ww) = 0 := by
  have h₁ : ucount (r.tr N) + ucount (u ++ ww) = ucount (r.tr N) := by
    rw [← OpenTotal.ucount_append, ← List.append_assoc, ← htrm, hN]
  omega

/-- The next low step of a position, given the run to a later stage. -/
theorem onRun_cons (r : (I.dlts P s).InfRun) {N m : Nat} (hNm : N ≤ m)
    (hg : OppGood Ii Ie (r.tr m)) {x : I.HState}
    {o : Move I.E I.F} {rest u pre : List (Move I.E I.F)}
    (hrun : (I.dlts P s).Run x (o :: rest) (r.st m)) (hu : r.tr N ++ u = pre)
    (htrm : r.tr m = pre ++ (o :: rest)) (hlow : ucount (u ++ (o :: rest)) = 0) :
    ∃ y, LowStep P I Ii Ie x y ∧ OnRun r N y := by
  rcases OpenTotal.Run.cons_inv hrun with ⟨y, hs, hr₂⟩ | ⟨y, hs, hr₂⟩
  · exact ⟨y, .inl hs, m, hNm, _, pre, hr₂, htrm, ⟨u, hu⟩⟩
  · obtain ⟨e, rfl⟩ := OpenTotal.lower_of_ucount_zero hlow
      (List.mem_append_right _ (List.mem_cons_self ..))
    have hgo := hg (.inl e) (by rw [htrm]; exact List.mem_append_right _ (List.mem_cons_self ..))
    refine ⟨y, .inr ⟨e, hs, hgo⟩, m, hNm, rest, pre ++ [.inl e], hr₂, by simp [htrm], ?_⟩
    exact ⟨u ++ [.inl e], by rw [← hu]; simp⟩

/-- From a position of an infinite run whose export moves stop at stage `N`, the run makes
a low step to another position. -/
theorem onRun_step (r : (I.dlts P s).InfRun) (hu : r.tr.Unbounded) {N : Nat}
    (hN : ∀ m, N ≤ m → ucount (r.tr m) = ucount (r.tr N))
    (hg : ∀ n, OppGood Ii Ie (r.tr n)) {x : I.HState}
    (hx : OnRun r N x) : ∃ y, LowStep P I Ii Ie x y ∧ OnRun r N y := by
  obtain ⟨n, hn, w, pre, hr, htr, hpre⟩ := hx
  obtain ⟨m, hm⟩ : ∃ m, (r.tr n).length + 1 ≤ (r.tr m).length := hu _
  have hnm : n ≤ m := later_of_longer r hm
  obtain ⟨w', hw', hr'⟩ : ∃ w', r.tr m = r.tr n ++ w' ∧
      (I.dlts P s).Run (r.st n) w' (r.st m) := OpenTotal.InfRun.seg r hnm
  obtain ⟨o, rest, hww⟩ : ∃ o rest, w ++ w' = o :: rest :=
    List.exists_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil w (ne_nil_of_longer hw' hm))
  obtain ⟨u, hu'⟩ : ∃ u, r.tr N ++ u = pre := hpre
  have htrm : r.tr m = pre ++ (o :: rest) := by rw [hw', htr, List.append_assoc, hww]
  have hlow : ucount (u ++ (o :: rest)) = 0 := low_after r (hN m (by omega)) (by rw [htrm, hu'])
  have hrun : (I.dlts P s).Run x (o :: rest) (r.st m) := hww ▸ hr.append hr'
  exact onRun_cons r (by omega) (hg m) hrun hu' htrm hlow

end Extract

/-- **Totally correct instances are productive.** -/
theorem dstrategy_productive (hm : TGameSat P I Inv Ii Ie) {s : Store Nat} (hs : Inv s) :
    Productive Ii Ie (I.dstrategy P s) := by
  rintro J ⟨⟨r, hu, rfl⟩, -⟩ hJ k
  by_contra hk
  have hb : ∀ n, ucount (r.tr n) < k + 1 := fun n => by
    by_contra h
    exact hk ⟨r.tr n, Chain.mem_lim_self _ n, by omega⟩
  obtain ⟨N, hN⟩ := OpenTotal.exists_max_of_bounded (fun n => ucount (r.tr n)) hb
  have hconst : ∀ m, N ≤ m → ucount (r.tr m) = ucount (r.tr N) := fun m hm' =>
    le_antisymm (hN m) (ucount_mono (r.mono.le hm'))
  have hg : ∀ n, OppGood Ii Ie (r.tr n) := fun n => hJ _ (Chain.mem_lim_self _ n)
  have htrace : Silmaril.InfiniteTrace (LowStep P I Ii Ie) (r.st N) :=
    Silmaril.InfiniteTrace.coinduct (OnRun r N) (fun _ hx => onRun_step r hu hconst hg hx)
      ⟨N, le_rfl, [], r.tr N, .nil _, by simp, List.prefix_refl _⟩
  exact no_lowTrace (run_tgood hm (r.run N) hs (hg N)) htrace

/-! ## Divergence-aware composition -/

/-- **Divergence-aware assume/guarantee strategies compose** when the upper strategy is
productive. -/
theorem dcomp_sound {E F G : Sig.{0}} {Ii : ISpec E} {Im : ISpec F} {Ie : ISpec G}
    {σ : DStrategy E F} {τ : DStrategy F G} (hσ : σ ≤ dagStrat Ii Im) (hτ : τ ≤ dagStrat Im Ie)
    (hprod : Productive Im Ie τ) : σ.comp τ ≤ dagStrat Ii Ie := by
  have hfin : (σ.comp τ).toStrategy ≤ agStrat Ii Ie := comp_refines hσ.1 hτ.1
  have hdiv : ∀ p ∈ (σ.comp τ).div, ¬ OppGood Ii Ie p := by
    intro p hp hg
    rcases hp with ⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩
    · exact (hσ.2.1 hs).2.2 (opp_zip hz (hσ.1 (σ.div_mem hs)).2 (hτ.1 ht).2 hg).1
    · exact (hτ.2.1 ht).2.2 (opp_zip hz (hσ.1 hs).2 (hτ.1 (τ.div_mem ht)).2 hg).2
    · exact no_chatter hσ.1 hτ.1 hprod i hi hg
  refine ⟨hfin, fun p hp => ⟨hfin (DStrategy.div_mem _ hp), DStrategy.div_run _ hp,
    hdiv p hp⟩, fun J hJ => ⟨DStrategy.inf_isInf _ hJ, fun q hq =>
      hfin (DStrategy.inf_sub _ hJ hq)⟩⟩

/-- **Totally correct parts of a static link**, divergence-aware: the divergence-observing
composite of the provider's and the consumer's strategies refines `dagStrat Ii Ie`. -/
theorem dlink_parts_sound (S : Setup) (P : Profile) {Ii : ISpec (ifaceSig [])}
    {Im : ISpec (ifaceSig S.stubTypes)} {Ie : ISpec (ifaceSig S.exportTypes)}
    {Invp Invc : Store Nat → Prop} (hp : TGameSat P S.providerI Invp Ii Im) (hp₀ : Invp S.sp)
    (hc : TGameSat P S.consumerI Invc Im Ie) (hc₀ : Invc S.scs) :
    (S.providerI.dstrategy P S.sp).comp (S.consumerI.dstrategy P S.scs) ≤ dagStrat Ii Ie :=
  dcomp_sound (dstrategy_sound hp hp₀) (dstrategy_sound hc hc₀) (dstrategy_productive hc hc₀)

/-- **Verified static linking from total correctness** (finite plays): the strategy of the
linked module refines `agStrat Ii Ie`. -/
theorem linked_sound_total (S : Setup) (hS : S.Scalar) (P : Profile) {Ii : ISpec (ifaceSig [])}
    {Im : ISpec (ifaceSig S.stubTypes)} {Ie : ISpec (ifaceSig S.exportTypes)}
    {Invp Invc : Store Nat → Prop} (hp : TGameSat P S.providerI Invp Ii Im) (hp₀ : Invp S.sp)
    (hc : TGameSat P S.consumerI Invc Im Ie) (hc₀ : Invc S.scs) :
    S.linkedI.σ P ≤ agStrat Ii Ie :=
  linked_sound S hS P (GameSat.of_total hp) hp₀ (GameSat.of_total hc) hc₀

end Silmaril.Wasm.Logic.GameLink
