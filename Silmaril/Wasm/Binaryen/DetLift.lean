module

public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.Binaryen.InlDet
public import Silmaril.Wasm.Binaryen.Equiv

@[expose] public section

/-! # The determinism lift: one-way export refinement under three hosts

A code simulation whose left side is the target gives `ExportRefines (· = ·) P X tgt src`
for every host `X` it respects. `exportRefines_symm_of_hosts` turns that into the converse
`ExportRefines (· = ·) P closedHost src tgt` under the deterministic profile, from the
three hosts `closedHost`, `SingleThreaded.divHost` and `trapHost` (every host call traps):

* **Source side** (`obs_det`): an observation of a module under the closed host is its
  only observation under any host. A closed-host run that terminates or diverges never
  reaches a host call (a host-call redex has no host-free step, and a reachable normal
  form is unique and excludes divergence), so every step of any host along it is a
  closed-host step (`Total.step`).
* **Target side** (`tgt_cases`): a module that instantiates under the closed host either
  has a closed-host observation, or some prefix of the script stops at a host call. Then
  the same prefix diverges under `divHost` and traps under `trapHost`.
* **Assembly**: in the second case both observations transfer to the source by the
  one-way refinements, where the source side makes both equal to its closed-host
  observation of that prefix, so `.diverges = .traps`.

Totality of the closed host is false for a store with host functions (a host call is a
non-terminal normal form), which is why one host does not suffice.
-/

namespace Silmaril.Wasm.Binaryen.DetLift

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Numerics
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Binaryen.InlS
open Silmaril.Wasm.SingleThreaded.Exec.BehaviourRefinement

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool}

/-- The host whose every call returns a trap and leaves the store unchanged. -/
def trapHost : HostSemantics H := fun _ s _ out => out = .returned s .trap

/-! ## Closed-host runs -/

theorem terminal_nf {P : Profile} {host : HostSemantics H} {t : Config H} (ht : t.Terminal) :
    ∀ z, ¬ Step P host t z := InlR.terminal_no_step ht

/-- A closed-host normal form reachable from `c` excludes closed-host divergence
(`InlR.term_not_div` with terminality replaced by the absence of steps: the closed host
makes no host calls). -/
theorem nf_not_div {c x : Config H} (hx : Steps (Profile.deterministic o) closedHost c x)
    (hnfx : ∀ z, ¬ Step (Profile.deterministic o) closedHost x z) :
    ¬ Diverges (Profile.deterministic o) closedHost c := by
  have hnf : ∀ z, ¬ Det.DStep o x z := hnfx
  have hj : ∀ {a b d : Config H}, Det.DStep o a b → Det.DStep o a d →
      Det.Join (Det.DStep o) b d :=
    fun ha hb => Det.DStep.join' ha hb
  obtain ⟨k₀, hk₀⟩ := NSteps.of_rtg (hx : Relation.ReflTransGen (Det.DStep o) c x)
  have aux : ∀ (k m : Nat) (y : Config H), sizeOf y.code = m →
      NSteps (Det.DStep o) k y x → ¬ Diverges (Profile.deterministic o) closedHost y := by
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

/-- A closed-host run from `c` that terminates or diverges. -/
def Total (o : GrowKind → Nat → Nat → Nat → Bool) (c : Config H) : Prop :=
  (∃ t, Steps (Profile.deterministic o) closedHost c t ∧ t.Terminal) ∨
    Diverges (Profile.deterministic o) closedHost c

/-- Along a total closed-host run, every step of any host is a closed-host step. -/
theorem Total.step {X : HostSemantics H} {c y y' : Config H} (hc : Total o c)
    (hy : Steps (Profile.deterministic o) closedHost c y)
    (hs : Step (Profile.deterministic o) X y y') :
    Step (Profile.deterministic o) closedHost y y' := by
  rcases Step.split_host hs with h | ⟨E, a, hh, args, hd, -⟩
  · exact h
  · exfalso
    have hnf : ∀ z, ¬ Step (Profile.deterministic o) closedHost y z := fun z hz => by
      rw [decompose?_none_of_noRedex (Step.noRedex hz)] at hd
      cases hd
    rcases hc with ⟨t, ht, htT⟩ | hdiv
    · obtain rfl := steps_det_nf ht hy (terminal_nf htT) hnf
      rw [decompose?_terminal htT] at hd
      cases hd
    · exact nf_not_div hy hnf hdiv

theorem Total.steps {X : HostSemantics H} {c y : Config H} (hc : Total o c)
    (h : Steps (Profile.deterministic o) X c y) : Steps (Profile.deterministic o) closedHost c y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hc.step ih hs)

theorem Total.diverges {X : HostSemantics H} {c : Config H} (hc : Total o c)
    (h : Diverges (Profile.deterministic o) X c) : Diverges (Profile.deterministic o) closedHost c :=
  InfiniteTrace.coinduct (fun y => Steps (Profile.deterministic o) closedHost c y ∧
      Diverges (Profile.deterministic o) X y)
    (fun y ⟨hy, hd⟩ => by
      obtain ⟨y₁, hs, hd₁⟩ := InfiniteTrace.unfold hd
      have hs' := hc.step hy hs
      exact ⟨y₁, hs', hy.tail hs', hd₁⟩) ⟨.refl, h⟩

/-- A terminating closed-host run fixes the end of every terminating run of any host. -/
theorem term_eq {X : HostSemantics H} {c t y : Config H}
    (ht : Steps (Profile.deterministic o) closedHost c t) (htT : t.Terminal)
    (hy : Steps (Profile.deterministic o) X c y) (hyT : y.Terminal) : y = t :=
  steps_det_nf (Total.steps (Or.inl ⟨t, ht, htT⟩) hy) ht (terminal_nf hyT) (terminal_nf htT)

/-- A terminating closed-host run excludes divergence under any host. -/
theorem term_not_div {X : HostSemantics H} {c t : Config H}
    (ht : Steps (Profile.deterministic o) closedHost c t) (htT : t.Terminal) :
    ¬ Diverges (Profile.deterministic o) X c :=
  fun hd => nf_not_div ht (terminal_nf htT) (Total.diverges (Or.inl ⟨t, ht, htT⟩) hd)

/-- A diverging closed-host run excludes termination under any host. -/
theorem div_not_term {X : HostSemantics H} {c y : Config H}
    (hd : Diverges (Profile.deterministic o) closedHost c)
    (hy : Steps (Profile.deterministic o) X c y) (hyT : y.Terminal) : False :=
  nf_not_div (Total.steps (Or.inr hd) hy) (terminal_nf hyT) hd

theorem result_eq {c : Config H} {r r' : Result} (h : c.code = r.toAdmin)
    (h' : c.code = r'.toAdmin) : r = r' :=
  Option.some.inj ((outcome?_eq_some_of_code h).symm.trans (outcome?_eq_some_of_code h'))

/-! ## Source side: a closed-host observation is the only one -/

theorem session_det {X : HostSemantics H} {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs bs' : List (Behaviour Val)}
    (h : Session (Profile.deterministic o) closedHost mi s script bs)
    (h' : Session (Profile.deterministic o) X mi s script bs') : bs' = bs := by
  induction h generalizing bs' with
  | nil => cases h'; rfl
  | stop hn =>
    cases h' with
    | stop => rfl
    | done ha hok => exact absurd hok (hn _ ha)
    | diverge ha hok => exact absurd hok (hn _ ha)
  | done ha hok run hr _ ih =>
    cases h' with
    | stop hn => exact absurd hok (hn _ ha)
    | done ha' hok' run' hr' tail' =>
      obtain rfl := Option.some.inj (ha.symm.trans ha')
      obtain rfl := term_eq run ⟨_, hr⟩ run' ⟨_, hr'⟩
      obtain rfl := result_eq hr' hr
      rw [ih tail']
    | diverge ha' hok' hd =>
      obtain rfl := Option.some.inj (ha.symm.trans ha')
      exact absurd hd (term_not_div run ⟨_, hr⟩)
  | diverge ha hok hd =>
    cases h' with
    | stop hn => exact absurd hok (hn _ ha)
    | done ha' hok' run' hr' =>
      obtain rfl := Option.some.inj (ha.symm.trans ha')
      exact (div_not_term hd run' ⟨_, hr'⟩).elim
    | diverge => rfl

theorem evalExpr_det_mixed {X : HostSemantics H} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {e : Expr}
    {v₁ v₂ : List Val}
    (h₁ : EvalExpr (Profile.deterministic o) closedHost s f e s₁ f₁ v₁)
    (h₂ : EvalExpr (Profile.deterministic o) X s f e s₂ f₂ v₂) :
    s₂ = s₁ ∧ f₂ = f₁ ∧ v₂ = v₁ := by
  have := term_eq h₁ ⟨.values v₁, rfl⟩ h₂ ⟨.values v₂, rfl⟩
  simp only [Config.mk.injEq, SingleThreaded.Det.vals_inj] at this
  exact this

theorem evalGlobals_det_mixed {X : HostSemantics H} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame}
    {gs : List CGlobalType} {es : List Expr} {vs₁ vs₂ : List Val}
    (h₁ : EvalGlobals (Profile.deterministic o) closedHost s f gs es s₁ f₁ vs₁)
    (h₂ : EvalGlobals (Profile.deterministic o) X s f gs es s₂ f₂ vs₂) :
    s₂ = s₁ ∧ f₂ = f₁ ∧ vs₂ = vs₁ := by
  induction h₁ generalizing s₂ f₂ vs₂ with
  | nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | cons he _ ih =>
    cases h₂ with
    | cons he' hs' =>
      obtain ⟨rfl, rfl, h⟩ := evalExpr_det_mixed he he'
      simp only [List.cons.injEq, and_true] at h
      subst h
      obtain ⟨rfl, rfl, rfl⟩ := ih hs'
      exact ⟨rfl, rfl, rfl⟩

theorem evalExprs_det_mixed {X : HostSemantics H} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame}
    {es : List Expr} {rs₁ rs₂ : List Ref}
    (h₁ : EvalExprs (Profile.deterministic o) closedHost s f es s₁ f₁ rs₁)
    (h₂ : EvalExprs (Profile.deterministic o) X s f es s₂ f₂ rs₂) :
    s₂ = s₁ ∧ f₂ = f₁ ∧ rs₂ = rs₁ := by
  induction h₁ generalizing s₂ f₂ rs₂ with
  | nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | cons he _ ih =>
    cases h₂ with
    | cons he' hs' =>
      obtain ⟨rfl, rfl, h⟩ := evalExpr_det_mixed he he'
      simp only [List.cons.injEq, and_true, Val.ref.injEq] at h
      subst h
      obtain ⟨rfl, rfl, rfl⟩ := ih hs'
      exact ⟨rfl, rfl, rfl⟩

theorem evalExprss_det_mixed {X : HostSemantics H} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame}
    {ess : List (List Expr)} {rss₁ rss₂ : List (List Ref)}
    (h₁ : EvalExprss (Profile.deterministic o) closedHost s f ess s₁ f₁ rss₁)
    (h₂ : EvalExprss (Profile.deterministic o) X s f ess s₂ f₂ rss₂) :
    s₂ = s₁ ∧ f₂ = f₁ ∧ rss₂ = rss₁ := by
  induction h₁ generalizing s₂ f₂ rss₂ with
  | nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | cons he _ ih =>
    cases h₂ with
    | cons he' hs' =>
      obtain ⟨rfl, rfl, rfl⟩ := evalExprs_det_mixed he he'
      obtain ⟨rfl, rfl, rfl⟩ := ih hs'
      exact ⟨rfl, rfl, rfl⟩

/-- A closed-host instantiation is the only instantiation under any host. -/
theorem instantiate_det_mixed {X : HostSemantics H} {s : Store H} {M : Module}
    {xas : List ExternAddr} {c₁ c₂ : Config H}
    (h₁ : Instantiate (Profile.deterministic o) closedHost s M xas c₁)
    (h₂ : Instantiate (Profile.deterministic o) X s M xas c₂) : c₂ = c₁ := by
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hg, ht, he, ha, rfl⟩ := h₁.run
  obtain ⟨s₁', s₂', s₃', s₄', f₁', f₂', f₃', vG', rT', rE', mi', hg', ht', he', ha', rfl⟩ := h₂.run
  obtain ⟨rfl, rfl, rfl⟩ := evalGlobals_det_mixed hg hg'
  obtain ⟨rfl, rfl, rfl⟩ := evalExprs_det_mixed ht ht'
  obtain ⟨rfl, rfl, rfl⟩ := evalExprss_det_mixed he he'
  rw [ha] at ha'
  cases ha'
  rfl

theorem terminal_of_nil {d : Config H} (h : d.code = []) : d.Terminal :=
  ⟨.values [], by rw [h]; rfl⟩

/-- **Source side.** An observation under the closed host is the only observation of the
same script under any host. -/
theorem obs_det {X : HostSemantics H} {s : Store H} {xas : List ExternAddr} {m : Module}
    {script : List Call} {bs bs' : List (Behaviour Val)}
    (h : bs ∈ moduleObs (Profile.deterministic o) closedHost s xas m script)
    (h' : bs' ∈ moduleObs (Profile.deterministic o) X s xas m script) : bs' = bs := by
  obtain ⟨c, hI, hc⟩ := h
  obtain ⟨c', hI', hc'⟩ := h'
  obtain rfl := instantiate_det_mixed hI hI'
  rcases hc with ⟨c₁, bs₁, hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩ <;>
    rcases hc' with ⟨c₂, bs₂, hS', hcode', hsess', rfl⟩ | ⟨c₂, r', hS', hcode', hr', rfl⟩ |
      ⟨hd', rfl⟩
  · obtain rfl := term_eq hS (terminal_of_nil hcode) hS' (terminal_of_nil hcode')
    rw [session_det hsess hsess']
  · obtain rfl := term_eq hS (terminal_of_nil hcode) hS' ⟨r', hcode'⟩
    exact absurd (result_eq (r := .values []) (by rw [hcode]; rfl) hcode').symm hr'
  · exact absurd hd' (term_not_div hS (terminal_of_nil hcode))
  · obtain rfl := term_eq hS ⟨r, hcode⟩ hS' (terminal_of_nil hcode')
    exact absurd (result_eq (r := .values []) (by rw [hcode']; rfl) hcode).symm hr
  · obtain rfl := term_eq hS ⟨r, hcode⟩ hS' ⟨r', hcode'⟩
    obtain rfl := result_eq hcode' hcode
    rfl
  · exact absurd hd' (term_not_div hS ⟨r, hcode⟩)
  · exact (div_not_term hd hS' (terminal_of_nil hcode')).elim
  · exact (div_not_term hd hS' ⟨r', hcode'⟩).elim
  · rfl

/-! ## Prefixes of a script -/

theorem session_take {P : Profile} {host : HostSemantics H} {mi : ModuleInst} {s : Store H}
    {script : List Call} {bs : List (Behaviour Val)} (h : Session P host mi s script bs) :
    ∀ k, ∃ bs', Session P host mi s (script.take k) bs' := by
  induction h with
  | nil => intro k; exact ⟨[], by simpa using Session.nil⟩
  | stop hn =>
    intro k
    cases k with
    | zero => exact ⟨[], .nil⟩
    | succ k => exact ⟨[], .stop hn⟩
  | done ha hok run hr _ ih =>
    intro k
    cases k with
    | zero => exact ⟨[], .nil⟩
    | succ k =>
      obtain ⟨bs', ht⟩ := ih k
      exact ⟨_, .done ha hok run hr ht⟩
  | diverge ha hok hd =>
    intro k
    cases k with
    | zero => exact ⟨[], .nil⟩
    | succ k => exact ⟨_, .diverge ha hok hd⟩

theorem obs_take {P : Profile} {host : HostSemantics H} {s : Store H} {xas : List ExternAddr}
    {m : Module} {script : List Call} {bs : List (Behaviour Val)}
    (h : bs ∈ moduleObs P host s xas m script) (k : Nat) :
    ∃ bs', bs' ∈ moduleObs P host s xas m (script.take k) := by
  obtain ⟨c, hI, hc⟩ := h
  rcases hc with ⟨c₁, bs₁, hS, hcode, hsess, rfl⟩ | h2 | h3
  · obtain ⟨bs', hs'⟩ := session_take hsess k
    exact ⟨_, c, hI, Or.inl ⟨c₁, bs', hS, hcode, hs', rfl⟩⟩
  · exact ⟨bs, c, hI, Or.inr (Or.inl h2)⟩
  · exact ⟨bs, c, hI, Or.inr (Or.inr h3)⟩

/-! ## Target side: terminate, diverge, or stop at a host call -/

/-- Classically, a closed-host run terminates, diverges, or stops at a non-terminal
normal form. -/
theorem run_cases (c : Config H) :
    (∃ t, Steps (Profile.deterministic o) closedHost c t ∧ t.Terminal) ∨
      Diverges (Profile.deterministic o) closedHost c ∨
      ∃ z, Steps (Profile.deterministic o) closedHost c z ∧
        (∀ w, ¬ Step (Profile.deterministic o) closedHost z w) ∧ ¬ z.Terminal := by
  by_cases hnf : ∃ z, Steps (Profile.deterministic o) closedHost c z ∧
      ∀ w, ¬ Step (Profile.deterministic o) closedHost z w
  · obtain ⟨z, hz, hn⟩ := hnf
    by_cases hT : z.Terminal
    · exact Or.inl ⟨z, hz, hT⟩
    · exact Or.inr (Or.inr ⟨z, hz, hn, hT⟩)
  · refine Or.inr (Or.inl (InfiniteTrace.coinduct
      (fun y => Steps (Profile.deterministic o) closedHost c y) (fun y hy => ?_) .refl))
    have : ∃ w, Step (Profile.deterministic o) closedHost y w := by
      by_contra hw
      push Not at hw
      exact hnf ⟨y, hy, hw⟩
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw, hy.tail hw⟩

/-- A typed non-terminal closed-host normal form is a host call: `divHost` stutters there. -/
theorem stuck_div {z : Config H} {ts : List CValType} (hz : ConfigOk z ts)
    (hnf : ∀ w, ¬ Step (Profile.deterministic o) closedHost z w) (hT : ¬ z.Terminal) :
    Step (Profile.deterministic o) SingleThreaded.divHost z z := by
  rcases Config.progress (P := Profile.deterministic o) SingleThreaded.divHost_ok hz with
    h | ⟨z', hz'⟩
  · exact absurd h hT
  · rcases Step.split_host hz' with h | ⟨E, a, hh, args, -, ⟨s', r, hr, -⟩ | ⟨-, rfl⟩⟩
    · exact absurd h (hnf z')
    · exact absurd hr (by simp [SingleThreaded.divHost])
    · exact hz'

/-- A trap in a callout context reaches the top, with the store unchanged. -/
theorem fill_trap_steps {P : Profile} {host : HostSemantics H} (s : Store H) :
    ∀ (E : Ctx) (f : Frame), ∃ f', Steps P host ⟨s, f, E.fill [.trap]⟩ ⟨s, f', [.trap]⟩ := by
  have top : ∀ (g : Frame) (pre : List Val) (rest : List Admin),
      Steps P host ⟨s, g, vals pre ++ [.trap] ++ rest⟩ ⟨s, g, [.trap]⟩ := by
    intro g pre rest
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact .single (Step.trapInstrs hne)
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals] using (Relation.ReflTransGen.refl : Steps P host ⟨s, g, [.trap]⟩ _)
  intro E
  induction E with
  | top pre rest => intro f; exact ⟨f, top f pre rest⟩
  | label pre n cont E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih f
    exact ⟨f', ((Steps.ctxtInstrs (vs := pre) (rest := rest) (Steps.label (n := n) (cont := cont) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapLabel))).trans (top f' pre rest)⟩
  | handler pre n cs E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih f
    exact ⟨f', ((Steps.ctxtInstrs (vs := pre) (rest := rest) (Steps.handler (n := n) (cs := cs) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapHandler))).trans (top f' pre rest)⟩
  | frame pre n fi E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih fi
    exact ⟨f, ((Steps.ctxtInstrs (vs := pre) (rest := rest) (Steps.frame (f := f) (n := n) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapFrame))).trans (top f pre rest)⟩

/-- At a typed non-terminal closed-host normal form, `trapHost` runs to a trap. -/
theorem stuck_trap {z : Config H} {ts : List CValType} (hz : ConfigOk z ts)
    (hnf : ∀ w, ¬ Step (Profile.deterministic o) closedHost z w) (hT : ¬ z.Terminal) :
    ∃ f', Steps (Profile.deterministic o) trapHost z ⟨z.store, f', [.trap]⟩ := by
  rcases Config.progress (P := Profile.deterministic o) SingleThreaded.divHost_ok hz with
    h | ⟨z', hz'⟩
  · exact absurd h hT
  rcases Step.split_host hz' with h | ⟨E, a, hh, args, hd, -⟩
  · exact absurd h (hnf z')
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
  have h1 : Step (Profile.deterministic o) trapHost z ⟨z.store, z.frame, E.fill [.trap]⟩ := by
    obtain ⟨s, f, code⟩ := z
    simp only at hcode ⊢
    subst hcode
    exact E.step_fill (fun g => Step.callRefHost (r := .trap) hyy hf he hn hc rfl) f
  obtain ⟨f', h2⟩ := fill_trap_steps (P := Profile.deterministic o) (host := trapHost) z.store E
    z.frame
  exact ⟨f', Relation.ReflTransGen.head h1 h2⟩

theorem diverges_of_stutter {P : Profile} {host : HostSemantics H} {z : Config H}
    (h : Step P host z z) : Diverges P host z :=
  ⟨fun _ => z, rfl, fun _ => h⟩

/-- The target-side case split for a session from a typed store. -/
theorem session_cases {mi : ModuleInst} : ∀ (script : List Call) (s : Store H), StoreOk s →
    (∃ bs, Session (Profile.deterministic o) closedHost mi s script bs) ∨
    ∃ k pre, Session (Profile.deterministic o) SingleThreaded.divHost mi s (script.take k)
        (pre ++ [.diverges]) ∧
      Session (Profile.deterministic o) trapHost mi s (script.take k) (pre ++ [.traps])
  | [], _, _ => Or.inl ⟨[], .nil⟩
  | (x, vs) :: rest, s, hs => by
    by_cases hex : ∃ a, exportFunc? mi x = some a ∧ InvokeOk s a vs
    · obtain ⟨a, ha, hok⟩ := hex
      obtain ⟨fi, ps, rs, -, -, hcfg⟩ := invoke_ok hs hok
      rcases run_cases (o := o) (invoke s a vs) with ⟨t, ht, r, hr⟩ | hd | ⟨z, hz, hnf, hT⟩
      · have hst : StoreOk t.store := ConfigOk.storeOk (closed_preserves hcfg ht)
        rcases session_cases rest t.store hst with ⟨bs, hb⟩ | ⟨k, pre, hD, hT⟩
        · exact Or.inl ⟨_, .done ha hok ht hr hb⟩
        · exact Or.inr ⟨k + 1, r.toBehaviour :: pre, .done ha hok (steps_of_closed _ ht) hr hD,
            .done ha hok (steps_of_closed _ ht) hr hT⟩
      · exact Or.inl ⟨_, .diverge ha hok hd⟩
      · have hzok := closed_preserves hcfg hz
        obtain ⟨f', hf'⟩ := stuck_trap hzok hnf hT
        exact Or.inr ⟨1, [], .diverge ha hok (InfiniteTrace.of_steps (steps_of_closed _ hz)
            (diverges_of_stutter (stuck_div hzok hnf hT))),
          .done (c := ⟨z.store, f', [.trap]⟩) (r := .trap) ha hok
            ((steps_of_closed _ hz).trans hf') rfl .nil⟩
    · push Not at hex
      exact Or.inl ⟨[], .stop fun a ha hok => hex a ha hok⟩

/-- **Target side.** A module that instantiates under the closed host on a typed store has
a closed-host observation of the script, or some prefix of the script diverges under
`divHost` and traps under `trapHost` after the same observations. -/
theorem tgt_cases {s : Store H} {xas : List ExternAddr} {m : Module} {c₀ : Config H}
    (hs : StoreOk s) (hI : Instantiate (Profile.deterministic o) closedHost s m xas c₀)
    (script : List Call) :
    (∃ bs, bs ∈ moduleObs (Profile.deterministic o) closedHost s xas m script) ∨
    ∃ k pre, pre ++ [.diverges] ∈
        moduleObs (Profile.deterministic o) SingleThreaded.divHost s xas m (script.take k) ∧
      pre ++ [.traps] ∈ moduleObs (Profile.deterministic o) trapHost s xas m (script.take k) := by
  have hID := instantiate_of_closed (SingleThreaded.divHost (H := H)) hI
  have hIT := instantiate_of_closed (trapHost (H := H)) hI
  have hcfg : ConfigOk c₀ [] := Instantiate.ok SingleThreaded.divHost_ok hs hID
  rcases run_cases (o := o) c₀ with ⟨t, ht, r, hr⟩ | hd | ⟨z, hz, hnf, hT⟩
  · by_cases hr0 : r = .values []
    · subst hr0
      have hst : StoreOk t.store := ConfigOk.storeOk (closed_preserves hcfg ht)
      rcases session_cases (o := o) (mi := c₀.frame.module) script t.store hst with
        ⟨bs, hb⟩ | ⟨k, pre, hD, hT⟩
      · exact Or.inl ⟨_, c₀, hI, Or.inl ⟨t, bs, ht, hr, hb, rfl⟩⟩
      · exact Or.inr ⟨k, .returns [] :: pre,
          ⟨c₀, hID, Or.inl ⟨t, _, steps_of_closed _ ht, hr, hD, rfl⟩⟩,
          ⟨c₀, hIT, Or.inl ⟨t, _, steps_of_closed _ ht, hr, hT, rfl⟩⟩⟩
    · exact Or.inl ⟨_, c₀, hI, Or.inr (Or.inl ⟨t, r, ht, hr, hr0, rfl⟩)⟩
  · exact Or.inl ⟨_, c₀, hI, Or.inr (Or.inr ⟨hd, rfl⟩)⟩
  · have hzok := closed_preserves hcfg hz
    obtain ⟨f', hf'⟩ := stuck_trap hzok hnf hT
    exact Or.inr ⟨0, [],
      ⟨c₀, hID, Or.inr (Or.inr ⟨InfiniteTrace.of_steps (steps_of_closed _ hz)
        (diverges_of_stutter (stuck_div hzok hnf hT)), rfl⟩)⟩,
      ⟨c₀, hIT, Or.inr (Or.inl ⟨⟨z.store, f', [.trap]⟩, .trap, (steps_of_closed _ hz).trans hf',
        rfl, fun h => Result.noConfusion h, rfl⟩)⟩⟩

/-! ## The lift -/

theorem sessionRel_eq {bs bs' : List (Behaviour Val)} (h : SessionRel (· = ·) bs bs') :
    bs = bs' := by
  induction h with
  | nil => rfl
  | cons hb _ ih => rw [hb, ih]
  | ub hb => exact absurd ((hb .diverges).trans (hb .traps).symm) (fun h => by cases h)

/-- **The determinism lift.** One-way export refinement of `m` against `m'` under the
closed host, `divHost` and `trapHost`, with instantiation of `m'` whenever `m`
instantiates, gives the converse refinement under the closed host. -/
theorem exportRefines_symm_of_hosts {m m' : Module}
    (hC : ExportRefines (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m')
    (hD : ExportRefines (· = ·) (Profile.deterministic o) (SingleThreaded.divHost (H := H)) m m')
    (hT : ExportRefines (· = ·) (Profile.deterministic o) (trapHost (H := H)) m m')
    (hinst : ∀ (s : Store H) xas c, StoreOk s →
      Instantiate (Profile.deterministic o) closedHost s m xas c →
      ∃ c', Instantiate (Profile.deterministic o) closedHost s m' xas c') :
    ExportRefines (· = ·) (Profile.deterministic o) (closedHost (H := H)) m' m := by
  refine ⟨fun s xas c hs hI => hinst s xas c hs hI, fun s xas script hs bs' hbs' => ?_⟩
  obtain ⟨cS, hIS, -⟩ := id hbs'
  obtain ⟨cT, hIT⟩ := hC.instantiates s xas cS hs hIS
  rcases tgt_cases hs hIT script with ⟨bs, hbs⟩ | ⟨k, pre, hdv, htr⟩
  · obtain ⟨bs'', hbs'', hrel⟩ := hC.obs s xas script hs bs hbs
    obtain rfl := sessionRel_eq hrel
    obtain rfl := obs_det hbs' hbs''
    exact ⟨bs, hbs, SessionRel.refl (fun _ => rfl) _⟩
  · exfalso
    obtain ⟨b₀, hb₀⟩ := obs_take hbs' k
    obtain ⟨b₁, hb₁, hr₁⟩ := hD.obs s xas _ hs _ hdv
    obtain ⟨b₂, hb₂, hr₂⟩ := hT.obs s xas _ hs _ htr
    obtain rfl := sessionRel_eq hr₁
    obtain rfl := sessionRel_eq hr₂
    have h := List.append_cancel_left ((obs_det hb₀ hb₁).trans (obs_det hb₀ hb₂).symm)
    simp at h

end Silmaril.Wasm.Binaryen.DetLift
