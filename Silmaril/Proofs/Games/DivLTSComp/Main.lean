module

public import Silmaril.Proofs.Games.DivLTSComp.Proj

/-!
# The divergence-observing strategy of a composite system: proofs

`DStrategy.ofLTS (L₁.comp L₂) = (DStrategy.ofLTS L₁).comp (DStrategy.ofLTS L₂)`
for systems denoting their strategies that diverge only in running positions
(`Silmaril.Games.DivLTSComp.Thms`). The finite plays are `LTS.Denotes.comp`.

**Composite to components.**

* *Divergence* (`div_comp_of_div`): an infinite silent run of the composite
  after `p` is enumerated (`exists_seq`). If it synchronises infinitely often,
  its projections form an infinite interaction whose visible part stays `p`
  (`Proj.toInf`), i.e. hidden chatter. Otherwise, from some stage on it only
  makes silent steps of one side or the other, and the side that steps
  infinitely often diverges (`diverges_of_seq`): local divergence, after a
  running play by `LTS.DivRunning`.
* *Infinite plays* (`inf_comp_of_inf`): an infinite run of the composite
  projects to an infinite interaction with the same visible chain.

**Components to composite.** An infinite interaction of `ofLTS L₁` and
`ofLTS L₂` is followed by one coherent run on each side
(`exists_cover`, `stages_of_cover`); their product is a staged run of the
composite (`comp_stages`). Hidden chatter makes it diverge, since every
growth of the hidden part is at least one silent step
(`transGen_of_zip_nil`); an unbounded visible part is an infinite run. Local
divergence lifts directly (`run_comp`).

New proofs.
-/

public section

namespace Silmaril.Proofs.Games.DivLTSComp

open Silmaril.Games Silmaril

universe u v

variable {E F G : Sig.{u}}

/-! ## Infinite sequences -/

/-- An infinite trace is an enumerated sequence of steps. -/
theorem exists_seq {α : Type v} {R : α → α → Prop} {a : α} (h : InfiniteTrace R a) :
    ∃ f : ℕ → α, f 0 = a ∧ ∀ n, R (f n) (f (n + 1)) := by
  have key : ∀ x, InfiniteTrace R x → ∃ y, R x y ∧ InfiniteTrace R y := fun _ hx => hx.unfold
  choose! g hg using key
  let f : ℕ → α := fun n => g^[n] a
  have hf : ∀ n, InfiniteTrace R (f n) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      show InfiniteTrace R (g^[n + 1] a)
      rw [Function.iterate_succ_apply']
      exact (hg _ ih).2
  refine ⟨f, rfl, fun n => ?_⟩
  show R (g^[n] a) (g^[n + 1] a)
  rw [Function.iterate_succ_apply']
  exact (hg _ (hf n)).1

theorem rtg_of_seq {β : Type v} {R : β → β → Prop} {h : ℕ → β} {N : ℕ}
    (hr : ∀ n, N ≤ n → Relation.ReflTransGen R (h n) (h (n + 1))) {n m : ℕ} (hn : N ≤ n)
    (hnm : n ≤ m) : Relation.ReflTransGen R (h n) (h m) := by
  induction hnm with
  | refl => exact .refl
  | step hle ih => exact ih.trans (hr _ (hn.trans hle))

/-- A sequence that, from stage `N` on, moves by `R*` and infinitely often by `R` has an
infinite `R`-trace from stage `N`. -/
theorem diverges_of_seq {β : Type v} {R : β → β → Prop} (h : ℕ → β) (N : ℕ)
    (hr : ∀ n, N ≤ n → Relation.ReflTransGen R (h n) (h (n + 1)))
    (hinf : ∀ M, ∃ n, M ≤ n ∧ N ≤ n ∧ R (h n) (h (n + 1))) : InfiniteTrace R (h N) := by
  refine InfiniteTrace.coinduct (fun x => ∃ n, N ≤ n ∧ Relation.ReflTransGen R x (h n)) ?_
    ⟨N, le_refl N, .refl⟩
  rintro x ⟨n, hn, hx⟩
  obtain ⟨m, hnm, hNm, hm⟩ := hinf n
  have ht : Relation.TransGen R x (h (m + 1)) :=
    Relation.TransGen.trans_right (hx.trans (rtg_of_seq hr hn hnm)) (.single hm)
  obtain ⟨x₁, hx₁, hrest⟩ := Relation.TransGen.head'_iff.1 ht
  exact ⟨x₁, hx₁, m + 1, hNm.trans (Nat.le_succ m), hrest⟩

/-! ## Composite to components -/

section Forward

variable {L₁ : LTS E F} {L₂ : LTS F G} {σ : Strategy E F} {τ : Strategy F G}

/-- Traces of a system denoting its strategy are its plays. -/
theorem trace_of_mem {L : LTS E F} {ρ : Strategy E F} (hL : L.Denotes ρ)
    {u : List (Move E F)} (h : u ∈ (DStrategy.ofLTS L).toStrategy) : ∃ y, L.Run L.init u y := by
  have hu : u ∈ Strategy.ofLTS L := h
  rw [hL.ofLTS_eq] at hu
  exact (hL u).2 hu

/-- A hidden synchronisation at stage `n` of a sequence of composite states. -/
def SyncAt (f : ℕ → (L₁.comp L₂).State) (n : ℕ) : Prop :=
  ∃ b, L₁.step (f n).1 (some (.inr b)) (f (n + 1)).1 ∧ L₂.step (f n).2 (some (.inl b)) (f (n + 1)).2

/-- The silent sequence reached at every stage from its start. -/
theorem run_seq {f : ℕ → (L₁.comp L₂).State} (hf : ∀ n, (L₁.comp L₂).Silent (f n) (f (n + 1)))
    (n : ℕ) : (L₁.comp L₂).Run (f 0) [] (f n) :=
  run_nil_of_silent (rtg_of_seq (fun k _ => .single (hf k)) (le_refl 0) (Nat.zero_le n))

/-- One silent step of the composite, projected with a non-empty lower increment at a
synchronisation. -/
theorem seq_step {f : ℕ → (L₁.comp L₂).State} (hf : ∀ n, (L₁.comp L₂).Silent (f n) (f (n + 1)))
    (p : List (Move E G)) (n : ℕ) : ∃ ds dt dp, p = p ++ dp ∧ Zip ds dt dp ∧
      L₁.Run (f n).1 ds (f (n + 1)).1 ∧ L₂.Run (f n).2 dt (f (n + 1)).2 ∧
      (SyncAt f n → ds ≠ []) := by
  by_cases hs : SyncAt f n
  · obtain ⟨b, h₁, h₂⟩ := hs
    exact ⟨[.inr b], [.inl b], [], (List.append_nil p).symm, .sync b .nil, .vis h₁ (.nil _), .vis h₂ (.nil _),
      fun _ => List.cons_ne_nil _ _⟩
  · rcases compStep_silent_cases (hf n) with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩ | ⟨b, h₁, h₂⟩
    · exact ⟨[], [], [], (List.append_nil p).symm, .nil, .tau h₁ (.nil _), h₂ ▸ .nil _, fun h => (hs h).elim⟩
    · exact ⟨[], [], [], (List.append_nil p).symm, .nil, h₁ ▸ .nil _, .tau h₂ (.nil _), fun h => (hs h).elim⟩
    · exact (hs ⟨b, h₁, h₂⟩).elim

/-- **Infinite hidden chatter.** A silent sequence of the composite after `p` that
synchronises infinitely often is an infinite interaction with visible part `p`. -/
theorem chatter_of_seq (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) {p : List (Move E G)}
    {f : ℕ → (L₁.comp L₂).State} (hr : (L₁.comp L₂).Run (L₁.comp L₂).init p (f 0))
    (hf : ∀ n, (L₁.comp L₂).Silent (f n) (f (n + 1)))
    (hsync : ∀ N, ∃ n, N ≤ n ∧ SyncAt f n) :
    ∃ i : DStrategy.InfInteraction (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂), ∀ n, i.p n = p := by
  obtain ⟨s₀, t₀, hr₁, hr₂, hz₀⟩ := comp_run hr
  obtain ⟨π, rfl, hπp, hπ⟩ := exists_proj f (fun _ => p) hz₀ hr₁ hr₂
    (fun n ds _ => SyncAt f n → ds ≠ []) (seq_step hf p)
  have hlong : ∀ k, ∃ n, k ≤ (π.s n).length := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      show ∃ n, k + 1 ≤ (π.s n).length
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hnm, hm⟩ := hsync n
      obtain ⟨ds, -, hds, -, hne⟩ := hπ m
      have hle : (π.s n).length ≤ (π.s m).length := (Chain.Mono.le π.st₁.mono hnm).length_le
      have hpos : 0 < ds.length := List.length_pos_iff.2 (hne hm)
      refine ⟨m + 1, ?_⟩
      rw [hds, List.length_append]
      omega
  have hu : ∀ k, ∃ n, k ≤ (π.s n).length + (π.t n).length := fun k => by
    obtain ⟨n, hn⟩ := hlong k
    exact ⟨n, hn.trans (Nat.le_add_right _ _)⟩
  obtain ⟨i, -, -, hip⟩ := π.toInf h₁ h₂ hu
  exact ⟨i, fun n => by rw [hip, hπp]⟩

/-- Local divergence of the lower side at stage `K` of the silent sequence. -/
theorem local_left (h₂ : L₂.Denotes τ) (d₁ : L₁.DivRunning) {p : List (Move E G)}
    {f : ℕ → (L₁.comp L₂).State} (hr : (L₁.comp L₂).Run (L₁.comp L₂).init p (f 0))
    (hf : ∀ n, (L₁.comp L₂).Silent (f n) (f (n + 1))) (K : ℕ) (hd : L₁.Diverges (f K).1) :
    p ∈ DStrategy.compDiv (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂) := by
  obtain ⟨s, t, hr₁, hr₂, hz⟩ := comp_run (hr.append (run_seq hf K))
  have hs : s ∈ (DStrategy.ofLTS L₁).div := ⟨⟨_, hr₁, hd⟩, d₁ hr₁ hd⟩
  exact .inl ⟨s, t, by simpa using hz, .inl ⟨hs, mem_ofLTS_of_run h₂ hr₂⟩⟩

/-- Local divergence of the upper side at stage `K` of the silent sequence. -/
theorem local_right (h₁ : L₁.Denotes σ) (d₂ : L₂.DivRunning) {p : List (Move E G)}
    {f : ℕ → (L₁.comp L₂).State} (hr : (L₁.comp L₂).Run (L₁.comp L₂).init p (f 0))
    (hf : ∀ n, (L₁.comp L₂).Silent (f n) (f (n + 1))) (K : ℕ) (hd : L₂.Diverges (f K).2) :
    p ∈ DStrategy.compDiv (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂) := by
  obtain ⟨s, t, hr₁, hr₂, hz⟩ := comp_run (hr.append (run_seq hf K))
  have ht : t ∈ (DStrategy.ofLTS L₂).div := ⟨⟨_, hr₂, hd⟩, d₂ hr₂ hd⟩
  exact .inl ⟨s, t, by simpa using hz, .inr ⟨mem_ofLTS_of_run h₁ hr₁, ht⟩⟩

/-- From stage `N` on without synchronisation, each step moves one side silently. -/
theorem no_sync_step {f : ℕ → (L₁.comp L₂).State} (hf : ∀ n, (L₁.comp L₂).Silent (f n) (f (n + 1)))
    {n : ℕ} (hn : ¬ SyncAt f n) :
    (L₁.Silent (f n).1 (f (n + 1)).1 ∧ (f (n + 1)).2 = (f n).2) ∨
      (L₂.Silent (f n).2 (f (n + 1)).2 ∧ (f (n + 1)).1 = (f n).1) := by
  rcases compStep_silent_cases (hf n) with h | h | ⟨b, h₁, h₂⟩
  · exact .inl h
  · exact .inr h
  · exact (hn ⟨b, h₁, h₂⟩).elim

/-- **Finitely many synchronisations: local divergence** of the side that steps infinitely
often. -/
theorem local_of_seq (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) (d₁ : L₁.DivRunning)
    (d₂ : L₂.DivRunning) {p : List (Move E G)} {f : ℕ → (L₁.comp L₂).State}
    (hr : (L₁.comp L₂).Run (L₁.comp L₂).init p (f 0))
    (hf : ∀ n, (L₁.comp L₂).Silent (f n) (f (n + 1))) {N : ℕ} (hN : ∀ n, N ≤ n → ¬ SyncAt f n) :
    p ∈ DStrategy.compDiv (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂) := by
  have hcase : ∀ n, N ≤ n → (L₁.Silent (f n).1 (f (n + 1)).1 ∧ (f (n + 1)).2 = (f n).2) ∨
      (L₂.Silent (f n).2 (f (n + 1)).2 ∧ (f (n + 1)).1 = (f n).1) :=
    fun n hn => no_sync_step hf (hN n hn)
  by_cases hinf : ∀ M, ∃ n, M ≤ n ∧ N ≤ n ∧ L₁.Silent (f n).1 (f (n + 1)).1
  · have hrefl : ∀ n, N ≤ n → Relation.ReflTransGen L₁.Silent (f n).1 (f (n + 1)).1 := by
      intro n hn
      rcases hcase n hn with ⟨h, -⟩ | ⟨-, h⟩
      · exact .single h
      · rw [h]
    exact local_left h₂ d₁ hr hf N (diverges_of_seq (fun n => (f n).1) N hrefl hinf)
  · show p ∈ DStrategy.compDiv (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂)
    obtain ⟨M, hM⟩ : ∃ M, ∀ n, M ≤ n → N ≤ n → ¬ L₁.Silent (f n).1 (f (n + 1)).1 := by
      push Not at hinf
      exact hinf
    have hstep : ∀ n, max M N ≤ n → L₂.Silent (f n).2 (f (n + 1)).2 := by
      intro n hn
      rcases hcase n ((le_max_right M N).trans hn) with ⟨h, -⟩ | ⟨h, -⟩
      · exact (hM n ((le_max_left M N).trans hn) ((le_max_right M N).trans hn) h).elim
      · exact h
    have hd : L₂.Diverges (f (max M N)).2 :=
      diverges_of_seq (fun n => (f n).2) (max M N) (fun n hn => .single (hstep n hn))
        (fun K => ⟨max K (max M N), le_max_left _ _, le_max_right _ _,
          hstep _ (le_max_right _ _)⟩)
    exact local_right h₁ d₂ hr hf _ hd

/-- **Divergence of the composite system is divergence of the composite strategy.** -/
theorem div_comp_of_div (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) (d₁ : L₁.DivRunning)
    (d₂ : L₂.DivRunning) {p : List (Move E G)} (hp : p ∈ (DStrategy.ofLTS (L₁.comp L₂)).div) :
    p ∈ DStrategy.compDiv (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂) := by
  obtain ⟨⟨z, hr, hd⟩, -⟩ := hp
  obtain ⟨f, rfl, hf⟩ := exists_seq hd
  by_cases hsync : ∀ N, ∃ n, N ≤ n ∧ SyncAt f n
  · obtain ⟨i, hi⟩ := chatter_of_seq h₁ h₂ hr hf hsync
    exact .inr ⟨i, hi⟩
  · obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → ¬ SyncAt f n := by
      push Not at hsync
      exact hsync
    exact local_of_seq h₁ h₂ d₁ d₂ hr hf hN

/-- **Infinite plays of the composite system are infinite plays of the composite
strategy.** -/
theorem inf_comp_of_inf (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) {I : Set (List (Move E G))}
    (hI : I ∈ (DStrategy.ofLTS (L₁.comp L₂)).inf) :
    ∃ i : DStrategy.InfInteraction (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂),
      i.p.Unbounded ∧ I = i.p.lim := by
  obtain ⟨⟨r, hu, rfl⟩, -⟩ := hI
  have hz₀ : Zip ([] : List (Move E F)) ([] : List (Move F G)) (r.tr 0) := by rw [r.tr_zero]; exact .nil
  have hr₁ : L₁.Run L₁.init [] (r.st 0).1 := r.st_zero ▸ .nil _
  have hr₂ : L₂.Run L₂.init [] (r.st 0).2 := r.st_zero ▸ .nil _
  have hstep : ∀ n, ∃ ds dt dp, r.tr (n + 1) = r.tr n ++ dp ∧ Zip ds dt dp ∧
      L₁.Run (r.st n).1 ds (r.st (n + 1)).1 ∧ L₂.Run (r.st n).2 dt (r.st (n + 1)).2 ∧ True := by
    intro n
    obtain ⟨w, hw, hrun⟩ := r.step n
    obtain ⟨ds, dt, hd₁, hd₂, hz⟩ := comp_run hrun
    exact ⟨ds, dt, w, hw, hz, hd₁, hd₂, trivial⟩
  obtain ⟨π, -, hπp, -⟩ := exists_proj r.st r.tr hz₀ hr₁ hr₂ (fun _ _ _ => True) hstep
  have hbound : ∀ k, ∃ n, k ≤ (π.s n).length + (π.t n).length := fun k => by
    obtain ⟨n, hn⟩ := hu k
    exact ⟨n, hn.trans (hπp ▸ zip_length (π.zip n))⟩
  obtain ⟨i, -, -, hip⟩ := π.toInf h₁ h₂ hbound
  exact ⟨i, by rw [hip, hπp]; exact hu, by rw [hip, hπp]⟩

end Forward

/-! ## Components to composite -/

section Backward

variable {L₁ : LTS E F} {L₂ : LTS F G} {σ : Strategy E F} {τ : Strategy F G}

/-- Each side of an infinite interaction is followed by one coherent run. -/
theorem follow_inter (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ)
    (i : DStrategy.InfInteraction (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂)) :
    ∃ (a : ℕ → L₁.State) (b : ℕ → L₂.State), Stages L₁ a i.s ∧ Stages L₂ b i.t := by
  obtain ⟨r₁, hc₁⟩ := exists_cover h₁ i.mono_s i.mem_s i.lim_s
  obtain ⟨r₂, hc₂⟩ := exists_cover h₂ i.mono_t i.mem_t i.lim_t
  obtain ⟨a, ha⟩ := stages_of_cover r₁ i.mono_s hc₁
  obtain ⟨b, hb⟩ := stages_of_cover r₂ i.mono_t hc₂
  exact ⟨a, b, ha, hb⟩

/-- The segment between two stages of a pair of staged runs of an interaction. -/
theorem seg_of_stages {a : ℕ → L₁.State} {b : ℕ → L₂.State} {s : Chain (Move E F)}
    {t : Chain (Move F G)} {p : Chain (Move E G)} (ha : Stages L₁ a s) (hb : Stages L₂ b t)
    (hz : ∀ n, Zip (s n) (t n) (p n)) {n m : ℕ} (hnm : n ≤ m) {dp : List (Move E G)}
    (hp : p m = p n ++ dp) :
    ∃ ds dt, s m = s n ++ ds ∧ t m = t n ++ dt ∧ Zip ds dt dp ∧
      L₁.Run (a n) ds (a m) ∧ L₂.Run (b n) dt (b m) := by
  obtain ⟨ds, hds, hr₁⟩ := ha.run_le hnm
  obtain ⟨dt, hdt, hr₂⟩ := hb.run_le hnm
  have hzm : Zip (s n ++ ds) (t n ++ dt) (p n ++ dp) := by
    rw [← hds, ← hdt, ← hp]
    exact hz m
  exact ⟨ds, dt, hds, hdt, zip_drop (hz n) hzm, hr₁, hr₂⟩

/-- The product of the staged runs of an interaction is a staged run of the composite. -/
theorem comp_stages {a : ℕ → L₁.State} {b : ℕ → L₂.State} {s : Chain (Move E F)}
    {t : Chain (Move F G)} {p : Chain (Move E G)} (ha : Stages L₁ a s) (hb : Stages L₂ b t)
    (hz : ∀ n, Zip (s n) (t n) (p n)) (hm : p.Mono) :
    Stages (L₁.comp L₂) (fun n => (a n, b n)) p := by
  refine ⟨run_comp (hz 0) ha.1 hb.1, fun n => ?_⟩
  obtain ⟨dp, hdp⟩ := hm n
  obtain ⟨ds, dt, -, -, hzd, hr₁, hr₂⟩ := seg_of_stages ha hb hz (Nat.le_succ n) hdp.symm
  exact ⟨dp, hdp.symm, run_comp hzd hr₁ hr₂⟩

/-- **Hidden chatter makes the composite system diverge.** -/
theorem div_of_chatter (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ)
    (i : DStrategy.InfInteraction (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂))
    {p : List (Move E G)} (hp : ∀ n, i.p n = p) :
    ∃ y, (L₁.comp L₂).Run (L₁.comp L₂).init p y ∧ (L₁.comp L₂).Diverges y := by
  obtain ⟨a, b, ha, hb⟩ := follow_inter h₁ h₂ i
  have hz0 : Zip (i.s 0) (i.t 0) p := hp 0 ▸ i.zip 0
  refine ⟨(a 0, b 0), run_comp hz0 ha.1 hb.1, ?_⟩
  refine InfiniteTrace.coinduct
    (fun x => ∃ n, Relation.ReflTransGen (L₁.comp L₂).Silent x (a n, b n)) ?_ ⟨0, .refl⟩
  rintro x ⟨n, hx⟩
  obtain ⟨m, hm⟩ := i.unbounded ((i.s n).length + (i.t n).length + 1)
  have hpm : i.p (max n m) = i.p n ++ [] := by rw [hp, hp, List.append_nil]
  obtain ⟨ds, dt, hds, hdt, hzd, hr₁, hr₂⟩ := seg_of_stages ha hb i.zip (le_max_left n m) hpm
  have hle : (i.s m).length + (i.t m).length ≤ (i.s (max n m)).length + (i.t (max n m)).length :=
    Nat.add_le_add (Chain.Mono.le i.mono_s (le_max_right n m)).length_le
      (Chain.Mono.le i.mono_t (le_max_right n m)).length_le
  have hne : ds ≠ [] ∨ dt ≠ [] := by
    by_contra hc
    push Not at hc
    rw [hds, hdt, hc.1, hc.2] at hle
    simp only [List.append_nil] at hle
    omega
  have ht : Relation.TransGen (L₁.comp L₂).Silent x (a (max n m), b (max n m)) :=
    Relation.TransGen.trans_right hx (transGen_of_zip_nil hzd hne hr₁ hr₂)
  obtain ⟨x₁, hx₁, hrest⟩ := Relation.TransGen.head'_iff.1 ht
  exact ⟨x₁, hx₁, max n m, hrest⟩

/-- **Infinite plays of the composite strategy are infinite plays of the composite
system.** -/
theorem inf_of_inter (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ)
    (i : DStrategy.InfInteraction (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂))
    (hu : i.p.Unbounded) : i.p.lim ∈ (L₁.comp L₂).InfTraces := by
  obtain ⟨a, b, ha, hb⟩ := follow_inter h₁ h₂ i
  obtain ⟨r, hr, hru⟩ := infRun_of_stages (comp_stages ha hb i.zip i.mono_p)
  exact ⟨r, hru hu, hr.symm⟩

/-- Local divergence of a side is divergence of the composite system. -/
theorem div_of_local (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (hz : Zip s t p)
    (h : (s ∈ (DStrategy.ofLTS L₁).div ∧ t ∈ (DStrategy.ofLTS L₂).toStrategy) ∨
      (s ∈ (DStrategy.ofLTS L₁).toStrategy ∧ t ∈ (DStrategy.ofLTS L₂).div)) :
    ∃ y, (L₁.comp L₂).Run (L₁.comp L₂).init p y ∧ (L₁.comp L₂).Diverges y := by
  rcases h with ⟨⟨⟨x, hx, hd⟩, -⟩, ht⟩ | ⟨hs, ⟨⟨y, hy, hd⟩, -⟩⟩
  · obtain ⟨y, hy⟩ := trace_of_mem h₂ ht
    exact ⟨(x, y), run_comp hz hx hy,
      InfiniteTrace.map (fun x => (x, y)) (fun _ _ h => LTS.CompStep.tau₁ h) hd⟩
  · obtain ⟨x, hx⟩ := trace_of_mem h₁ hs
    exact ⟨(x, y), run_comp hz hx hy,
      InfiniteTrace.map (fun y => (x, y)) (fun _ _ h => LTS.CompStep.tau₂ h) hd⟩

end Backward

end Silmaril.Proofs.Games.DivLTSComp
