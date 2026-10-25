module

public import Silmaril.Wasm.Binaryen.InlUnwrap

@[expose] public section

/-! Closed-host block unwrapping over arbitrary host-state types. Host calls may
be stuck; preservation uses the always-diverging host, without assuming progress
for the closed host. -/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- Closed-host steps are classified without a typing hypothesis. -/
theorem classif_closed (c : Config H) : Classif P closedHost c :=
  fun _ h => .inl h

theorem steps_of_closed_unwrap {P : Numerics.Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Steps P closedHost c c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (Step.of_noHost host hs)

theorem evalGlobals_of_closed_unwrap {P : Numerics.Profile} (host : HostSemantics H) {s s' : Store H}
    {f f' : Frame} {gs : List CGlobalType} {es : List Expr} {vs : List Val}
    (h : EvalGlobals P closedHost s f gs es s' f' vs) : EvalGlobals P host s f gs es s' f' vs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (steps_of_closed_unwrap host he) ih

theorem evalExprs_of_closed_unwrap {P : Numerics.Profile} (host : HostSemantics H) {s s' : Store H}
    {f f' : Frame} {es : List Expr} {rs : List Ref}
    (h : EvalExprs P closedHost s f es s' f' rs) : EvalExprs P host s f es s' f' rs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (steps_of_closed_unwrap host he) ih

theorem evalExprss_of_closed_unwrap {P : Numerics.Profile} (host : HostSemantics H) {s s' : Store H}
    {f f' : Frame} {ess : List (List Expr)} {rss : List (List Ref)}
    (h : EvalExprss P closedHost s f ess s' f' rss) : EvalExprss P host s f ess s' f' rss := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (evalExprs_of_closed_unwrap host he) ih

theorem instantiate_of_closed_unwrap {P : Numerics.Profile} (host : HostSemantics H) {s : Store H} {M : Module}
    {xas : List ExternAddr} {c : Config H} (h : Instantiate P closedHost s M xas c) :
    Instantiate P host s M xas c where
  valid := h.valid
  bounded := h.bounded
  run := by
    obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hg, ht, he, ha, hc⟩ := h.run
    exact ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, evalGlobals_of_closed_unwrap host hg,
      evalExprs_of_closed_unwrap host ht, evalExprss_of_closed_unwrap host he, ha, hc⟩

/-- Closed-host runs preserve typing even when the host-state type is inhabited. -/
theorem preserves_closed {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (h : Steps P closedHost c c') : ConfigOk c' ts :=
  (Steps.safe divHost_ok hc (steps_of_closed_unwrap divHost h)).1

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}
local notation "PD" => Numerics.Profile.deterministic o

/-- Reaching any closed-host normal form excludes divergence. -/
theorem nf_not_div_closed {c x : Config H} (hx : Steps PD closedHost c x)
    (hnf : ∀ z, ¬ Step PD closedHost x z) : ¬ Diverges PD closedHost c := by
  have hj : ∀ {a b d : Config H}, Det.DStep o a b → Det.DStep o a d → Det.Join (Det.DStep o) b d :=
    fun ha hb => Det.DStep.join' ha hb
  obtain ⟨k₀, hk₀⟩ := NSteps.of_rtg hx
  have aux : ∀ (k m : Nat) (y : Config H), sizeOf y.code = m →
      NSteps (Det.DStep o) k y x → ¬ Diverges PD closedHost y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro y hm hk hdiv
    obtain ⟨y₁, hn, hdiv₁⟩ := InfiniteTrace.unfold hdiv
    cases hk with
    | refl => exact hnf _ hn
    | @head _ a' _ j h₁ hrest =>
      obtain ⟨ys, yf, ycode⟩ := y
      rcases Det.DStep.shrink _ ys yf ycode a' y₁ rfl h₁ hn with heq | ⟨-, -, -, hlt⟩
      · subst heq
        exact ihk j (by omega) _ _ rfl hrest hdiv₁
      · obtain ⟨m', hm', hpath⟩ := NSteps.of_step_join hj hnf (.head h₁ hrest) hn
        rcases Nat.lt_or_eq_of_le hm' with hlt' | rfl
        · exact ihk m' hlt' _ _ rfl hpath hdiv₁
        · exact ihm _ (by simp only at hm; omega) _ rfl hpath hdiv₁
  exact aux k₀ _ c rfl hk₀

/-- A call redex stays a call redex in every evaluation context. -/
theorem redex_fill_closed {s : Store H} {xs : List Admin} {E₀ : Ctx} {a : Nat}
    {hh : H} {args : List Val}
    (hd : decompose? s xs = some (E₀, a, hh, args)) (E : Ctx) :
    ∃ F, decompose? s (E.fill xs) = some (F, a, hh, args) := by
  induction E with
  | top pre rest => exact ⟨_, decompose?_wrap pre rest hd⟩
  | label pre n cont E rest ih =>
    obtain ⟨F, hF⟩ := ih
    have hb : decompose? s [.label n cont (E.fill xs)] =
        some (.label [] n cont F [], a, hh, args) := by
      rw [decompose?_eq]
      simp [splitVals, Admin.val?, decompTop, decompHead, hF]
    exact ⟨_, decompose?_wrap pre rest hb⟩
  | handler pre n cs E rest ih =>
    obtain ⟨F, hF⟩ := ih
    have hb : decompose? s [.handler n cs (E.fill xs)] =
        some (.handler [] n cs F [], a, hh, args) := by
      rw [decompose?_eq]
      simp [splitVals, Admin.val?, decompTop, decompHead, hF]
    exact ⟨_, decompose?_wrap pre rest hb⟩
  | frame pre n f E rest ih =>
    obtain ⟨F, hF⟩ := ih
    have hb : decompose? s [.frame n f (E.fill xs)] =
        some (.frame [] n f F [], a, hh, args) := by
      rw [decompose?_eq]
      simp [splitVals, Admin.val?, decompTop, decompHead, hF]
    exact ⟨_, decompose?_wrap pre rest hb⟩

/-- Unwrapping transports an unresolved closed-host call. -/
theorem redex_transport_closed {c d : Config H} (hMR : MR p c d)
    (hSR : SR p c.store d.store) {E : Ctx} {a : Nat} {hh : H} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args)) :
    ∃ F, decompose? d.store d.code = some (F, a, hh, args) := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, hshape⟩ := decompose?_sound hd
  have hag : a ≠ p.ag := by
    rintro rfl; rw [hSR.hg] at hfi; cases hfi; simp [gL] at hcode
  have hfi' : d.store.funcs[a]? = some fi := by
    rw [hSR.get a]; simp only [hag, ↓reduceIte]; exact hfi
  obtain ⟨E', hE'⟩ := callout_transport hyy E (hshape ▸ hMR.2)
  rw [hE']
  exact redex_fill_closed (decompose?_redex hyy hfi' he hlen hcode) E'

/-- A typed nonterminal closed-host normal form is stuck on a host call,
which is also stuck in the related configuration. -/
theorem stuck_transport_closed {c d : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hnt : ¬ c.Terminal)
    (hnf : ∀ y, ¬ Step PD closedHost c y) (hMR : MR p c d)
    (hSR : SR p c.store d.store) :
    ¬ d.Terminal ∧ (∀ y, ¬ Step PD closedHost d y) := by
  obtain ht | ⟨c₁, hs⟩ := Config.progress (P := PD) divHost_ok hc
  · exact (hnt ht).elim
  rcases Step.split_host hs with hn | ⟨E, a, hh, args, hd, hret | hdiv⟩
  · exact (hnf _ hn).elim
  · obtain ⟨s', r, hret, _⟩ := hret
    cases hret
  · obtain ⟨F, hF⟩ := redex_transport_closed hMR hSR hd
    refine ⟨?_, ?_⟩
    · intro ht
      rw [decompose?_terminal ht] at hF
      cases hF
    · intro y hs
      rw [decompose?_none_of_noRedex (Step.noRedex hs)] at hF
      cases hF

/-- Execution terminates, exposes a corresponding stuck call, or diverges. -/
theorem run_trichotomy_closed (hok : PrmOk p) {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hMR : MR p c c') (hSR : SR p c.store c'.store) :
    (∃ x, Steps PD closedHost c x ∧ x.Terminal) ∨
    (∃ x x', Steps PD closedHost c x ∧ Steps PD closedHost c' x' ∧
      ¬ x'.Terminal ∧ (∀ y, ¬ Step PD closedHost x' y)) ∨
    Diverges PD closedHost c := by
  classical
  by_cases hd : Diverges PD closedHost c
  · exact .inr (.inr hd)
  have hnf : ∃ x, Steps PD closedHost c x ∧ ∀ y, ¬ Step PD closedHost x y := by
    by_contra hne
    simp only [not_exists, not_and, not_forall, not_not] at hne
    exact hd (InfiniteTrace.coinduct (fun x => Steps PD closedHost c x)
      (fun x hx => let ⟨y, hy⟩ := hne x hx; ⟨y, hy, hx.tail hy⟩) .refl)
  obtain ⟨x, hx, hnf⟩ := hnf
  by_cases ht : x.Terminal
  · exact .inl ⟨x, hx, ht⟩
  obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hok hx (fun x _ => classif_closed x) hMR hSR
  obtain ⟨hnt', hnf'⟩ := stuck_transport_closed (preserves_closed hc hx) ht hnf hMR' hSR'
  exact .inr (.inl ⟨x, x', hx, hx', hnt', hnf'⟩)

/-- Terminating results and divergence correspond under the closed host. -/
theorem runs_corr_closed (hok : PrmOk p) {c c' : Config H} {ts ts' : List CValType}
    (hc : ConfigOk c ts) (_hc' : ConfigOk c' ts') (hMR : MR p c c')
    (hSR : SR p c.store c'.store) :
    (∀ x, Steps PD closedHost c x → x.Terminal →
      ∃ x', Steps PD closedHost c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges PD closedHost c → Diverges PD closedHost c') ∧
    (∀ x', Steps PD closedHost c' x' → x'.Terminal →
      ∃ x, Steps PD closedHost c x ∧ x.code = x'.code ∧ SR p x.store x'.store) ∧
    (Diverges PD closedHost c' → Diverges PD closedHost c) := by
  have hclO : ∀ x, Steps PD closedHost c x → Classif PD closedHost x :=
    fun x _ => classif_closed x
  have hclN : ∀ x, Steps PD closedHost c' x → Classif PD closedHost x :=
    fun x _ => classif_closed x
  have R1 : ∀ x, Steps PD closedHost c x → x.Terminal →
      ∃ x', Steps PD closedHost c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store := by
    intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hok hx hclO hMR hSR
    exact ⟨x', hx', by rw [terminal_code hMR' hr, hr], hSR'⟩
  have R2 : Diverges PD closedHost c → Diverges PD closedHost c' := fun hd =>
    div_sim hok closedHost_respectsCode hd hclO hMR hSR
  refine ⟨R1, R2, ?_, ?_⟩
  · intro x' hx' hxT'
    rcases run_trichotomy_closed hok hc hMR hSR with hterm | hstuck | hdiv
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, hSR''⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      have := nf_unique_classif hx'' hx' hxT'' hxT' hclN
      subst this
      exact ⟨x, hx, hcode.symm, hSR''⟩
    · obtain ⟨x, y, _, hy, hnt, hnf⟩ := hstuck
      have he : y = x' := nf_unique_of_join (fun ha hb => Det.DStep.join' ha hb)
        hy hx' hnf (terminal_no_step hxT')
      exact (hnt (he.symm ▸ hxT')).elim
    · exact (term_not_div hx' hxT' hclN (R2 hdiv)).elim
  · intro hd'
    rcases run_trichotomy_closed hok hc hMR hSR with hterm | hstuck | hdiv
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, -⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      exact (term_not_div hx'' hxT'' hclN hd').elim
    · obtain ⟨x, y, _, hy, _, hnf⟩ := hstuck
      exact (nf_not_div_closed hy hnf hd').elim
    · exact hdiv

/-- **Sessions of the right module are sessions of the left one.** -/
theorem session_corr₁_closed (hok : PrmOk p) {mi : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD closedHost mi t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreOk t → SR p s t → Session PD closedHost mi s script bs := by
  induction h with
  | nil => exact fun _ _ _ => .nil
  | stop h => exact fun _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of hSR hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, R3, -⟩ := runs_corr_closed hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (preserves_closed hcO hx'))
      (ConfigOk.storeOk (preserves_closed hcN run)) hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr_closed hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the left module are sessions of the right one.** -/
theorem session_corr₂_closed (hok : PrmOk p) {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD closedHost mi s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → SR p s t → Session PD closedHost mi t script bs := by
  induction h with
  | nil => exact fun _ _ _ => .nil
  | stop h => exact fun _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨R1, -, -, -⟩ := runs_corr_closed hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (preserves_closed hcO run))
      (ConfigOk.storeOk (preserves_closed hcN hx')) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr_closed hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)

/-! ## Module observations -/

theorem obs_corr_closed
    {M M' : Module} {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {c c' : Config H}
    (hi : Instantiate PD closedHost s M xas c) (hi' : Instantiate PD closedHost s M' xas c')
    (hok : PrmOk p) (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
    (hSR : SR p c.store c'.store) (script : List Call) :
    (∀ bs, ((∃ c₁ bs', Steps PD closedHost c' c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c' ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps PD closedHost c c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c ∧ bs = [.diverges]))) ∧
    (∀ bs, ((∃ c₁ bs', Steps PD closedHost c c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps PD closedHost c' c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c' ∧ bs = [.diverges]))) := by
  have hc := Instantiate.ok divHost_ok hs (instantiate_of_closed_unwrap divHost hi)
  have hc' := Instantiate.ok divHost_ok hs (instantiate_of_closed_unwrap divHost hi')
  have hMR : MR p c c' := ⟨hfr.symm, by rw [hcode]; exact UL.refl _⟩
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr_closed hok hc hc' hMR hSR
  refine ⟨fun bs h => ?_, fun bs h => ?_⟩
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₁_closed hok h₃ (ConfigOk.storeOk (preserves_closed hc hx))
        (ConfigOk.storeOk (preserves_closed hc' h₁)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₂_closed hok h₃ (ConfigOk.storeOk (preserves_closed hc h₁))
        (ConfigOk.storeOk (preserves_closed hc' hx)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr_closed {M M' : Module} (h : InstCorr (o := o) (closedHost (H := H)) M M') :
    ExportEquiv (· = ·) PD (closedHost (H := H)) M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', p, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, p, hok, hi, hfr, hcode, hSR⟩ := h₂ s xas c' hs hi'
    exact ⟨bs, ⟨c, hi, (obs_corr_closed hs hi hi' hok hfr hcode hSR script).1 bs hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, p, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', p, hok, hi', hfr, hcode, hSR⟩ := h₁ s xas c hs hi
    exact ⟨bs, ⟨c', hi', (obs_corr_closed hs hi hi' hok hfr hcode hSR script).2 bs hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

end Silmaril.Wasm.Binaryen.Unwrap

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics Unwrap

/-- **Unwrapping a branch-free block is an equivalence.** In any function body of any
module, `block bt region` may be replaced by `region` when `region` is inside the profile
(`any = false`), has no free branch target (`labelsList = []`) and no `return`
(`branchesOut = false`), under the closed host, for arbitrary host-state types. -/
theorem block_unwrap_exportEquiv_closed {m : BModule} {g : Nat} {K : BCtx} {bt : BlockType}
    {region : List BExpr} (hg : g < m.funcs.length)
    (hok : (m.withBody g (K.plug [.block bt region])).Ok) (hfree : BExpr.labelsList region = [])
    (hany : (effectsList region).any = false) (hret : (effectsList region).branchesOut = false)
    (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) (m.withBody g (K.plug region)).lower
      (m.withBody g (K.plug [.block bt region])).lower := by
  obtain ⟨fg, hfg⟩ : ∃ fg, m.funcs[g]? = some fg := ⟨_, List.getElem?_eq_getElem hg⟩
  obtain ⟨mt₀, hmt₀⟩ := hok
  have hbase : ∀ B, (m.withBody g B).base = m.base := fun _ => rfl
  have hL : (m.withBody g (K.plug [.block bt region])).lower.funcs[g]? =
      some (({ fg with body := K.plug [.block bt region] } : BFunc).mapBody BExpr.lowerList) := by
    simp only [BModule.lower, withBody_eq_set hfg, List.getElem?_map]
    rw [List.getElem?_set_self hg]
    rfl
  have hRm : (m.withBody g (K.plug region)).lower =
      { (m.withBody g (K.plug [.block bt region])).lower with
        funcs := (m.withBody g (K.plug [.block bt region])).lower.funcs.set g
          (({ fg with body := K.plug region } : BFunc).mapBody BExpr.lowerList) } := by
    simp only [BModule.lower, hbase, withBody_eq_set hfg, List.map_set, List.set_set]
  rw [hRm]
  refine Unwrap.exportEquiv_of_instCorr_closed (instCorr_of_set hL rfl (fun mt => ?_)
    (fun mi dg ag => ⟨rfl, lower_plug K bt region, ⟨_, region_bud hfree hany hret⟩, hfree⟩))
  rw [← hRm]
  constructor
  · exact block_unwrap_valid_mt hfree hany hret
  · intro h'
    have h₀ := block_unwrap_valid_mt hfree hany hret hmt₀
    rw [ModuleOk.unique h' h₀]
    exact hmt₀


end Silmaril.Wasm.Binaryen
