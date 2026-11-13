module

public import Silmaril.Proofs.Wasm.Logic.OpenTotal.Link

/-!
# Open modules with total correctness: productivity

`dmodStrat_productive`: a totally correct open module is `Productive`: in an
infinite play whose Opponent moves are good there are infinitely many moves at
the upper interface. Otherwise, from some stage on, the run only makes silent
steps and import calls with their (good) answers (`LowStep`). From a state of
the invariant `TGood` such a run is an infinite closed-world run under
`specHostT` (each silent step is a host-free step; each call with its answer is
one host step, `redex_step_ret`), which total correctness excludes
(`no_lowTrace`). The infinite low run is extracted from the infinite run of the
transition system (`onRun_step`, by `Silmaril.InfiniteTrace.coinduct`). Hence
`dlink_refines_total`: linked totally correct modules refine the
divergence-aware assume/guarantee strategy, with no productivity hypothesis.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.OpenTotal

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Open
open Silmaril.Wasm.Logic.Strategy (WCall ctxSpec MoveGood)

variable {H : Type} {P : Profile} {M : OMod H} {bind : H → Nat} {Γi Γe : Ctx H}

/-- A step of the module that is silent, or a move at the lower interface that is
good if it is Opponent's. -/
def LowStep (P : Profile) (M : OMod H) (bind : H → Nat) (Γi Γe : Ctx H)
    (x y : (modRed P M bind).State) : Prop :=
  (modRed P M bind).toLTS.step x none y ∨
    ∃ e, (modRed P M bind).toLTS.step x (some (.inl e)) y ∧
      (Move.IsO (Sum.inl e : Move (WCall H) (WCall H)) →
        MoveGood (ctxSpec Γi) (ctxSpec Γe) (Sum.inl e : Move (WCall H) (WCall H)))

/-! ## Infinite low runs are closed-world divergence -/

/-- The resumed configuration after an import call and a good answer. -/
theorem low_resume {Q : Post H} {q : Nat × Store H × List Val} {c : Config H}
    {m : Nat × Store H × List Val} {k : Store H × Result → Config H}
    {y : (modRed P M bind).State} (hsafe : TSafe P (specHostT bind Γi) Q c)
    (hc : (modRed P M bind).call (q := q) c m k)
    (hs : LowStep P M bind Γi Γe (.wait q m k) y) :
    ∃ ans, y = .run q (k ans) ∧ Step P (specHostT bind Γi) c (k ans) := by
  obtain ⟨-, E, a, hh, args, hd, rfl, rfl⟩ := hc
  obtain ⟨S, hS, hpre⟩ := timport_pre hsafe hd
  rcases hs with hs | ⟨e, hs, hg⟩
  · cases hs
  · cases hs with
    | resume q m k ans =>
      exact ⟨ans, rfl, redex_step_ret hd ⟨S, hS, hpre, hg trivial S hS⟩⟩

/-- An infinite low run from a running, totally correct configuration is a
closed-world divergence. -/
theorem diverges_of_lowTrace {Q : Post H} {q : Nat × Store H × List Val} {c : Config H}
    (hsafe : TSafe P (specHostT bind Γi) Q c)
    (hd : Silmaril.InfiniteTrace (LowStep P M bind Γi Γe) (.run q c)) :
    Diverges P (specHostT bind Γi) c := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun c => TSafe P (specHostT bind Γi) Q c ∧
      Silmaril.InfiniteTrace (LowStep P M bind Γi Γe) (.run q c))
    (fun c ⟨hc, ht⟩ => ?_) ⟨hsafe, hd⟩
  obtain ⟨y, hs, hy⟩ := Silmaril.InfiniteTrace.unfold ht
  rcases hs with hs | ⟨e, hs, -⟩
  · cases hs with
    | tau h =>
      have hst : Step P (specHostT bind Γi) c _ := Step.of_noHost _ h.2
      exact ⟨_, hst, hc.step_inv hst, hy⟩
  · cases hs with
    | call hcall =>
      obtain ⟨y', hs', hy'⟩ := Silmaril.InfiniteTrace.unfold hy
      obtain ⟨ans, rfl, hst⟩ := low_resume hc hcall hs'
      exact ⟨_, hst, hc.step_inv hst, hy'⟩

/-- **No infinite low run from a state of the invariant.** -/
theorem no_lowTrace {x : (modRed P M bind).State} (hx : TGood P M bind Γi Γe x)
    (hd : Silmaril.InfiniteTrace (LowStep P M bind Γi Γe) x) : False := by
  cases x with
  | idle =>
    obtain ⟨y, hs, -⟩ := Silmaril.InfiniteTrace.unfold hd
    rcases hs with hs | ⟨e, hs, -⟩ <;> cases hs
  | run q c =>
    obtain ⟨S, -, h⟩ := hx
    exact TSafe.not_diverges h (diverges_of_lowTrace h hd)
  | wait q m k =>
    obtain ⟨y, hs, hy⟩ := Silmaril.InfiniteTrace.unfold hd
    obtain ⟨S, hS, h⟩ := hx
    rcases hs with hs | ⟨e, hs, hg⟩
    · cases hs
    · cases hs with
      | resume q m k ans =>
        have h' := h ans (hg trivial)
        exact TSafe.not_diverges h' (diverges_of_lowTrace h' hy)

/-! ## Extracting a low run from an infinite run -/

section Extract

variable {E F : Sig} {L : LTS E F}

/-- The run between two stages of an infinite run. -/
theorem InfRun.seg (r : L.InfRun) {n m : Nat} (h : n ≤ m) :
    ∃ w, r.tr m = r.tr n ++ w ∧ L.Run (r.st n) w (r.st m) := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨[], by simp, .nil _⟩
  | succ m _ ih =>
    obtain ⟨w, hw, hr⟩ := ih
    obtain ⟨w', hw', hr'⟩ := r.step m
    exact ⟨w ++ w', by rw [hw', hw, List.append_assoc], hr.append hr'⟩

/-- A bounded sequence of naturals reaches its maximum. -/
theorem exists_max_of_bounded (g : Nat → Nat) {k : Nat} (hb : ∀ n, g n < k) :
    ∃ N, ∀ m, g m ≤ g N := by
  by_contra h
  have h' : ∀ N, ∃ m, g N < g m := fun N => by
    by_contra hN
    exact h ⟨N, fun m => by
      by_contra hm
      exact hN ⟨m, by omega⟩⟩
  have hgrow : ∀ i, ∃ n, i ≤ g n := by
    intro i
    induction i with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ i ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm⟩ := h' n
      exact ⟨m, by omega⟩
  obtain ⟨n, hn⟩ := hgrow k
  exact absurd (hb n) (by omega)

/-- The first step of a run with a visible move. -/
theorem Run.cons_inv {x z : L.State} {o : Move E F} {rest : List (Move E F)}
    (h : L.Run x (o :: rest) z) :
    (∃ y, L.step x none y ∧ L.Run y (o :: rest) z) ∨ (∃ y, L.step x (some o) y ∧ L.Run y rest z) := by
  cases h with
  | tau hs hr => exact .inl ⟨_, hs, hr⟩
  | vis hs hr => exact .inr ⟨_, hs, hr⟩

theorem ucount_append (a b : List (Move E F)) : ucount (a ++ b) = ucount a + ucount b := by
  simp [ucount, upper, List.filterMap_append]

theorem lower_of_ucount_zero {b : List (Move E F)} (h : ucount b = 0) {o : Move E F}
    (ho : o ∈ b) : ∃ e, o = .inl e := by
  rcases o with e | e
  · exact ⟨e, rfl⟩
  · exfalso
    have hmem : e ∈ upper b := List.mem_filterMap.mpr ⟨.inr e, ho, rfl⟩
    have hlen : 0 < (upper b).length := List.length_pos_of_mem hmem
    simp only [ucount] at h
    omega

end Extract

/-- A position on the way of an infinite run, past stage `N`. -/
def OnRun (r : (modRed P M bind).toLTS.InfRun) (N : Nat) (x : (modRed P M bind).State) : Prop :=
  ∃ n, N ≤ n ∧ ∃ w pre, (modRed P M bind).toLTS.Run x w (r.st n) ∧ r.tr n = pre ++ w ∧
    r.tr N <+: pre

theorem later_of_longer (r : (modRed P M bind).toLTS.InfRun) {n m : Nat}
    (hm : (r.tr n).length + 1 ≤ (r.tr m).length) : n ≤ m := by
  by_contra h
  have hp : (r.tr m).length ≤ (r.tr n).length := (r.mono.le (by omega)).length_le
  omega

theorem ne_nil_of_longer {a b w : List (Move (WCall H) (WCall H))} (hw : b = a ++ w)
    (hm : a.length + 1 ≤ b.length) : w ≠ [] := by
  intro h
  have hb : b.length = a.length := by simp [hw, h]
  omega

/-- The upper moves after stage `N` are none. -/
theorem low_after (r : (modRed P M bind).toLTS.InfRun) {N m : Nat}
    (hN : ucount (r.tr m) = ucount (r.tr N)) {u ww : List (Move (WCall H) (WCall H))}
    (htrm : r.tr m = (r.tr N ++ u) ++ ww) : ucount (u ++ ww) = 0 := by
  have h₁ : ucount (r.tr N) + ucount (u ++ ww) = ucount (r.tr N) := by
    rw [← ucount_append, ← List.append_assoc, ← htrm, hN]
  omega

/-- The next low step of a position, given the run to a later stage. -/
theorem onRun_cons (r : (modRed P M bind).toLTS.InfRun) {N m : Nat} (hNm : N ≤ m)
    (hg : OppGood (ctxSpec Γi) (ctxSpec Γe) (r.tr m)) {x : (modRed P M bind).State}
    {o : Move (WCall H) (WCall H)} {rest u pre : List (Move (WCall H) (WCall H))}
    (hrun : (modRed P M bind).toLTS.Run x (o :: rest) (r.st m)) (hu : r.tr N ++ u = pre)
    (htrm : r.tr m = pre ++ (o :: rest)) (hlow : ucount (u ++ (o :: rest)) = 0) :
    ∃ y, LowStep P M bind Γi Γe x y ∧ OnRun r N y := by
  rcases Run.cons_inv hrun with ⟨y, hs, hr₂⟩ | ⟨y, hs, hr₂⟩
  · exact ⟨y, .inl hs, m, hNm, _, pre, hr₂, htrm, ⟨u, hu⟩⟩
  · obtain ⟨e, rfl⟩ := lower_of_ucount_zero hlow (List.mem_append_right _ (List.mem_cons_self ..))
    have hgo := hg (.inl e) (by rw [htrm]; exact List.mem_append_right _ (List.mem_cons_self ..))
    refine ⟨y, .inr ⟨e, hs, hgo⟩, m, hNm, rest, pre ++ [.inl e], hr₂, by simp [htrm], ?_⟩
    exact ⟨u ++ [.inl e], by rw [← hu]; simp⟩

/-- From a position of an infinite run whose upper moves stop at stage `N`, the
run makes a low step to another position. -/
theorem onRun_step (r : (modRed P M bind).toLTS.InfRun) (hu : r.tr.Unbounded) {N : Nat}
    (hN : ∀ m, N ≤ m → ucount (r.tr m) = ucount (r.tr N))
    (hg : ∀ n, OppGood (ctxSpec Γi) (ctxSpec Γe) (r.tr n)) {x : (modRed P M bind).State}
    (hx : OnRun r N x) : ∃ y, LowStep P M bind Γi Γe x y ∧ OnRun r N y := by
  obtain ⟨n, hn, w, pre, hr, htr, hpre⟩ := hx
  obtain ⟨m, hm⟩ : ∃ m, (r.tr n).length + 1 ≤ (r.tr m).length := hu _
  have hnm : n ≤ m := later_of_longer r hm
  obtain ⟨w', hw', hr'⟩ : ∃ w', r.tr m = r.tr n ++ w' ∧
      (modRed P M bind).toLTS.Run (r.st n) w' (r.st m) := InfRun.seg r hnm
  obtain ⟨o, rest, hww⟩ : ∃ o rest, w ++ w' = o :: rest :=
    List.exists_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil w (ne_nil_of_longer hw' hm))
  obtain ⟨u, hu'⟩ : ∃ u, r.tr N ++ u = pre := hpre
  have htrm : r.tr m = pre ++ (o :: rest) := by rw [hw', htr, List.append_assoc, hww]
  have hlow : ucount (u ++ (o :: rest)) = 0 := low_after r (hN m (by omega)) (by rw [htrm, hu'])
  have hrun : (modRed P M bind).toLTS.Run x (o :: rest) (r.st m) := hww ▸ hr.append hr'
  exact onRun_cons r (by omega) (hg m) hrun hu' htrm hlow

/-- **Totally correct modules are productive.** -/
theorem dmodStrat_productive (hm : TModuleSat P M bind Γi Γe) :
    Productive (ctxSpec Γi) (ctxSpec Γe) (dmodStrat P M bind) := by
  rintro J ⟨⟨r, hu, rfl⟩, -⟩ hJ k
  by_contra hk
  have hb : ∀ n, ucount (r.tr n) < k + 1 := fun n => by
    by_contra h
    exact hk ⟨r.tr n, Chain.mem_lim_self _ n, by omega⟩
  obtain ⟨N, hN⟩ := exists_max_of_bounded (fun n => ucount (r.tr n)) hb
  have hconst : ∀ m, N ≤ m → ucount (r.tr m) = ucount (r.tr N) := fun m hm' =>
    le_antisymm (hN m) (ucount_mono (r.mono.le hm'))
  have hg : ∀ n, OppGood (ctxSpec Γi) (ctxSpec Γe) (r.tr n) := fun n => hJ _ (Chain.mem_lim_self _ n)
  have htrace : Silmaril.InfiniteTrace (LowStep P M bind Γi Γe) (r.st N) :=
    Silmaril.InfiniteTrace.coinduct (OnRun r N) (fun _ hx => onRun_step r hu hconst hg hx)
      ⟨N, le_rfl, [], r.tr N, .nil _, by simp, List.prefix_refl _⟩
  exact no_lowTrace (run_tgood hm (r.run N) trivial (hg N)) htrace

/-- **Linking totally correct modules**, divergence-aware: if `M₁` meets `Γm`
totally under `Γi` and `M₂` meets `Γe` totally under `Γm`, their composite
(`DStrategy.comp`, observing divergence from infinite hidden interaction)
refines the divergence-aware assume/guarantee strategy of `Γi` and `Γe`. -/
theorem dlink_refines_total {M₁ M₂ : OMod H} {bind₁ bind₂ : H → Nat} {Γm : Ctx H}
    (h₁ : TModuleSat P M₁ bind₁ Γi Γm) (h₂ : TModuleSat P M₂ bind₂ Γm Γe) :
    (dmodStrat P M₁ bind₁).comp (dmodStrat P M₂ bind₂) ≤ dagStrat (ctxSpec Γi) (ctxSpec Γe) :=
  dlink_refines h₁ h₂ (dmodStrat_productive h₂)

end Silmaril.Wasm.Logic.OpenTotal
