module

public import Silmaril.Wasm.Component.Reference.LegalBoundaryRuns.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Thms

/-!
# Twin mid-call configurations have the same rests (proofs)

For any engine, profile, host readiness and dispatcher: two `StepTwin` configurations have the
same nonempty runs, the same divergences and infinite runs (internal or with host events), the
same rests of a session call (`SessRest`), the same quiet divergences (`QuietRest`) and the same
host chatter (`HostProdRest`). And the rests compose with a prefix of the call into the session
observations (`Calls`, `SessStep`, `CallDiverges`, `CallQuietDiverges`, `CallHostProd`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.LegalBoundaryRuns
open Silmaril.Games.Abstract (streamTake)

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-! ## Infinite traces with the same first steps -/

theorem infiniteTrace_congr {A : Type} {R : A → A → Prop} {a b : A}
    (h : ∀ z, R a z ↔ R b z) : Silmaril.InfiniteTrace R a ↔ Silmaril.InfiniteTrace R b := by
  constructor
  · intro d
    obtain ⟨z, s, d'⟩ := d.unfold
    exact d'.fold ((h z).1 s)
  · intro d
    obtain ⟨z, s, d'⟩ := d.unfold
    exact d'.fold ((h z).2 s)

/-! ## Twins -/


variable {x y : Config E σ}

theorem twin_symm (t : StepTwin prof hr dispatch x y) : StepTwin prof hr dispatch y x :=
  ⟨fun l m' => (t.step l m').symm, t.store.symm, t.core.symm, t.host.symm, t.ctl_y, t.ctl_x⟩

theorem twin_steps_cons (t : StepTwin prof hr dispatch x y) {l : Label E σ} {tr : List (Label E σ)}
    {m' : Config E σ} :
    Steps prof hr dispatch x (l :: tr) m' ↔ Steps prof hr dispatch y (l :: tr) m' := by
  rw [Steps.cons_iff, Steps.cons_iff]
  exact exists_congr fun z => and_congr_left' (t.step l z)

theorem twin_anyStep (t : StepTwin prof hr dispatch x y) (z : Config E σ) :
    AnyStep prof hr dispatch x z ↔ AnyStep prof hr dispatch y z :=
  exists_congr fun l => t.step l z

theorem twin_internalStep (t : StepTwin prof hr dispatch x y) (z : Config E σ) :
    InternalStep prof hr dispatch x z ↔ InternalStep prof hr dispatch y z :=
  exists_congr fun l => and_congr_right' (t.step l z)

theorem twin_diverges (t : StepTwin prof hr dispatch x y) :
    Diverges prof hr dispatch x ↔ Diverges prof hr dispatch y :=
  infiniteTrace_congr (twin_internalStep t)

theorem twin_divergesWithHost (t : StepTwin prof hr dispatch x y) :
    DivergesWithHost prof hr dispatch x ↔ DivergesWithHost prof hr dispatch y :=
  infiniteTrace_congr (twin_anyStep t)

theorem twin_holds (t : StepTwin prof hr dispatch x y) (c : CallId) (out : CallOutcome) :
    out.Holds hr c x ↔ out.Holds hr c y := by
  have hx := t.ctl_x
  have hy := t.ctl_y
  cases out with
  | resolved r => simp [CallOutcome.Holds, hx, hy]
  | trap => simp [CallOutcome.Holds, Trapped, t.store]
  | deadlock => simp [CallOutcome.Holds, Deadlocked, hx, hy]

theorem twin_resumeCfg_eq [∀ a b, Decidable (E.ExternSub a b)] (t : StepTwin prof hr dispatch x y)
    (m₀ : Config E σ) : resumeCfg m₀ x = resumeCfg m₀ y := by
  simp [resumeCfg, t.core, t.host]

/-- One direction of `sessRest`. -/
theorem twin_sessRest_of [∀ a b, Decidable (E.ExternSub a b)] {h : Host E σ}
    {x y : Config E σ} (t : StepTwin prof h.hr h.dispatch x y) {m₀ m₁ : Config E σ} {n : Nat}
    {o : Option (List Value.Val)} (r : SessRest prof h m₀ x n o m₁) :
    SessRest prof h m₀ y n o m₁ := by
  cases r with
  | ret c =>
    obtain ⟨tr, s, hev, hint, hout⟩ := c
    cases tr with
    | nil =>
      cases s
      exact absurd hout.1 t.ctl_x
    | cons l tr => exact .ret ⟨l :: tr, (twin_steps_cons t).1 s, hev, hint, hout⟩
  | trap c =>
    obtain ⟨tr, s, hev, hint, hout⟩ := c
    cases tr with
    | nil =>
      cases s
      rw [(twin_resumeCfg_eq t)]
      exact .trap ⟨[], .refl _, hev, hint, ((twin_holds t) _ _).1 hout⟩
    | cons l tr => exact .trap ⟨l :: tr, (twin_steps_cons t).1 s, hev, hint, hout⟩

theorem twin_sessRest [∀ a b, Decidable (E.ExternSub a b)] {h : Host E σ}
    {x y : Config E σ} (t : StepTwin prof h.hr h.dispatch x y) {m₀ m₁ : Config E σ} {n : Nat}
    {o : Option (List Value.Val)} : SessRest prof h m₀ x n o m₁ ↔ SessRest prof h m₀ y n o m₁ :=
  ⟨twin_sessRest_of t, twin_sessRest_of (twin_symm t)⟩

theorem twin_quietSeg (t : StepTwin prof hr dispatch x y) (st : σ) (z : Config E σ) :
    QuietSeg prof hr dispatch st x z ↔ QuietSeg prof hr dispatch st y z := by
  unfold QuietSeg
  rw [t.host]
  refine and_congr_right' (and_congr_right' (exists_congr fun tr => ?_))
  constructor
  · rintro ⟨s, hne, hh⟩
    obtain ⟨l, tr, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨(twin_steps_cons t).1 s, hne, hh⟩
  · rintro ⟨s, hne, hh⟩
    obtain ⟨l, tr, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨(twin_steps_cons t).2 s, hne, hh⟩

theorem twin_quietDiverges (t : StepTwin prof hr dispatch x y) (st : σ) :
    QuietDiverges prof hr dispatch st x ↔ QuietDiverges prof hr dispatch st y :=
  infiniteTrace_congr ((twin_quietSeg t) st)

theorem twin_quietRest_of (t : StepTwin prof hr dispatch x y) {st : σ}
    (r : QuietRest prof hr dispatch st x) : QuietRest prof hr dispatch st y := by
  obtain ⟨tr, m₂, s, hh, d⟩ := r
  cases tr with
  | nil =>
    cases s
    exact ⟨[], y, .refl _, hh, ((twin_quietDiverges t) st).1 d⟩
  | cons l tr => exact ⟨l :: tr, m₂, (twin_steps_cons t).1 s, hh, d⟩

theorem twin_quietRest (t : StepTwin prof hr dispatch x y) (st : σ) :
    QuietRest prof hr dispatch st x ↔ QuietRest prof hr dispatch st y :=
  ⟨(twin_quietRest_of t), (twin_quietRest_of (twin_symm t))⟩

theorem twin_hostProdRest_of {ε : Type} {hr : HostReady (σ × List ε)}
    {dispatch : Call E → P E (σ × List ε) (Ret E)} {x y : Config E (σ × List ε)}
    (t : StepTwin prof hr dispatch x y) {base : List ε} {ev : ℕ → ε}
    (r : HostProdRest prof hr dispatch base x ev) : HostProdRest prof hr dispatch base y ev := by
  obtain ⟨u, h0, hs, hl⟩ := r
  let u' : ℕ → Config E (σ × List ε) := fun n => match n with | 0 => y | n + 1 => u (n + 1)
  have hhost : ∀ p, (u' p).host = (u p).host := by
    intro p
    cases p with
    | zero => simp [u', h0, t.host]
    | succ p => rfl
  refine ⟨u', rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
      have := hs 0
      rw [h0] at this
      exact ((twin_internalStep t) _).1 this
    | succ n => exact hs (n + 1)
  · intro N
    obtain ⟨n, p, hN, hp⟩ := hl N
    exact ⟨n, p, hN, by rw [hhost]; exact hp⟩

theorem twin_hostProdRest {ε : Type} {hr : HostReady (σ × List ε)}
    {dispatch : Call E → P E (σ × List ε) (Ret E)} {x y : Config E (σ × List ε)}
    (t : StepTwin prof hr dispatch x y) (base : List ε) (ev : ℕ → ε) :
    HostProdRest prof hr dispatch base x ev ↔ HostProdRest prof hr dispatch base y ev :=
  ⟨(twin_hostProdRest_of t), (twin_hostProdRest_of (twin_symm t))⟩


/-! ## Composing a prefix of the call with its rest -/

theorem steps_append {m₁ m₂ m₃ : Config E σ} {tr₁ tr₂ : List (Label E σ)}
    (h₁ : Steps prof hr dispatch m₁ tr₁ m₂) (h₂ : Steps prof hr dispatch m₂ tr₂ m₃) :
    Steps prof hr dispatch m₁ (tr₁ ++ tr₂) m₃ := by
  induction h₁ with
  | refl => exact h₂
  | cons s _ ih => exact .cons s (ih h₂)

theorem callRest_of_steps {x x' m' : Config E σ} {tr : List (Label E σ)} {c : CallId}
    {out : CallOutcome} (h : Steps prof hr dispatch x tr x')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent c ev)
    (hint : out = .trap → ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : CallRest prof hr dispatch x' c m' out) : CallRest prof hr dispatch x c m' out := by
  obtain ⟨tr', s, hev', hint', hout⟩ := r
  refine ⟨tr ++ tr', steps_append h s, ?_, ?_, hout⟩
  · intro ev hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hev ev hm
    · exact hev' ev hm
  · intro ho msg hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hint ho msg hm
    · exact hint' ho msg hm

theorem calls_iff {m m' : Config E σ} {c : CallId} {f : FuncId} {args : List Value.Val}
    {out : CallOutcome} :
    Calls prof hr dispatch m c f args m' out ↔
      ∃ x, Step prof hr dispatch m (.host (invokeTop c f args)) x ∧
        CallRest prof hr dispatch x c m' out := by
  constructor
  · rintro ⟨tr, s, hev, hint, hout⟩
    obtain ⟨x, s₁, s₂⟩ := Steps.cons_iff.1 s
    exact ⟨x, s₁, tr, s₂, hev, hint, hout⟩
  · rintro ⟨x, s₁, tr, s₂, hev, hint, hout⟩
    exact ⟨tr, .cons s₁ s₂, hev, hint, hout⟩

theorem calls_of_callRest {m x m' : Config E σ} {c : CallId} {f : FuncId} {args : List Value.Val}
    {tr : List (Label E σ)} {out : CallOutcome}
    (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent c ev)
    (hint : out = .trap → ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : CallRest prof hr dispatch x c m' out) : Calls prof hr dispatch m c f args m' out := by
  obtain ⟨x₁, s₁, s₂⟩ := Steps.cons_iff.1 h
  exact calls_iff.2 ⟨x₁, s₁, callRest_of_steps s₂ hev hint r⟩

section Sess

variable [∀ a b, Decidable (E.ExternSub a b)] {h : Host E σ}

theorem sessStep_iff {m₀ m₁ : Config E σ} {n : Nat} {f : FuncId} {args : List Value.Val}
    {o : Option (List Value.Val)} :
    SessStep prof h m₀ n f args o m₁ ↔
      ∃ x, Step prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ f args)) x ∧
        SessRest prof h m₀ x n o m₁ := by
  constructor
  · rintro (c | c)
    · obtain ⟨x, s, r⟩ := calls_iff.1 c
      exact ⟨x, s, .ret r⟩
    · obtain ⟨x, s, r⟩ := calls_iff.1 c
      exact ⟨x, s, .trap r⟩
  · rintro ⟨x, s, r | r⟩
    · exact .ret (calls_iff.2 ⟨x, s, r⟩)
    · exact .trap (calls_iff.2 ⟨x, s, r⟩)

theorem sessStep_of_sessRest {m₀ x m₁ : Config E σ} {n : Nat} {f : FuncId} {args : List Value.Val}
    {tr : List (Label E σ)} {o : Option (List Value.Val)}
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ f args) :: tr) x)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : o = none → ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : SessRest prof h m₀ x n o m₁) : SessStep prof h m₀ n f args o m₁ := by
  cases r with
  | ret c => exact .ret (calls_of_callRest h₁ hev (fun h => nomatch h) c)
  | trap c => exact .trap (calls_of_callRest h₁ hev (fun _ => hint rfl) c)

theorem sessCalls_cons {m₀ m₁ : Config E σ} {n : Nat} {f : FuncId} {args : List Value.Val}
    {o : Option (List Value.Val)} {cs : List (FuncId × List Value.Val)}
    {outs : List (Option (List Value.Val))}
    (s : SessStep prof h m₀ n f args o m₁) (r : SessCalls prof h m₁ (n + 1) cs outs) :
    SessCalls prof h m₀ n ((f, args) :: cs) (o :: outs) := by
  cases s with
  | ret c => exact .ret c r
  | trap c => exact .trap c r

theorem sessDiv_cons {m₀ m₁ : Config E σ} {n : Nat} {f : FuncId} {args : List Value.Val}
    {o : Option (List Value.Val)} {cs : List (FuncId × List Value.Val)}
    {outs : List (Option (List Value.Val))}
    {g : FuncId} {gargs : List Value.Val}
    (s : SessStep prof h m₀ n f args o m₁) (r : SessDiv prof h m₁ (n + 1) cs outs g gargs) :
    SessDiv prof h m₀ n ((f, args) :: cs) (o :: outs) g gargs := by
  cases s with
  | ret c => exact .ret c r
  | trap c => exact .trap c r

theorem sessRun_cons {m₀ m₁ m' : Config E σ} {n : Nat} {f : FuncId} {args : List Value.Val}
    {o : Option (List Value.Val)} {cs : List (FuncId × List Value.Val)}
    {outs : List (Option (List Value.Val))}
    (s : SessStep prof h m₀ n f args o m₁)
    (r : LinkedSession.SessRun prof h m₁ (n + 1) cs outs m') :
    LinkedSession.SessRun prof h m₀ n ((f, args) :: cs) (o :: outs) m' := by
  cases s with
  | ret c => exact .ret c r
  | trap c => exact .trap c r

theorem sessRun_sessCalls {m₀ m' : Config E σ} {n : Nat}
    {cs cs' : List (FuncId × List Value.Val)} {outs outs' : List (Option (List Value.Val))}
    (r : LinkedSession.SessRun prof h m₀ n cs outs m')
    (c : SessCalls prof h m' (n + cs.length) cs' outs') :
    SessCalls prof h m₀ n (cs ++ cs') (outs ++ outs') := by
  induction r with
  | nil => simpa using c
  | ret s _ ih =>
    refine .ret s (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1] using c
  | trap s _ ih =>
    refine .trap s (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1] using c

theorem sessRun_sessDiv {m₀ m' : Config E σ} {n : Nat}
    {cs cs' : List (FuncId × List Value.Val)} {outs outs' : List (Option (List Value.Val))}
    {g : FuncId} {gargs : List Value.Val}
    (r : LinkedSession.SessRun prof h m₀ n cs outs m')
    (c : SessDiv prof h m' (n + cs.length) cs' outs' g gargs) :
    SessDiv prof h m₀ n (cs ++ cs') (outs ++ outs') g gargs := by
  induction r with
  | nil => simpa using c
  | ret s _ ih =>
    refine .ret s (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1] using c
  | trap s _ ih =>
    refine .trap s (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1] using c

theorem sessRun_append {m₀ m' m'' : Config E σ} {n : Nat}
    {cs cs' : List (FuncId × List Value.Val)} {outs outs' : List (Option (List Value.Val))}
    (r : LinkedSession.SessRun prof h m₀ n cs outs m')
    (c : LinkedSession.SessRun prof h m' (n + cs.length) cs' outs' m'') :
    LinkedSession.SessRun prof h m₀ n (cs ++ cs') (outs ++ outs') m'' := by
  induction r with
  | nil => simpa using c
  | ret s _ ih =>
    refine .ret s (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1] using c
  | trap s _ ih =>
    refine .trap s (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1] using c

end Sess

theorem diverges_of_steps {x x' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch x tr x') (hh : ∀ ev, Label.host ev ∉ tr)
    (d : Diverges prof hr dispatch x') : Diverges prof hr dispatch x := by
  induction h with
  | refl => exact d
  | @cons _ _ _ l _ s _ ih =>
    refine (ih (fun ev hm => hh ev (List.mem_cons_of_mem _ hm)) d).fold ⟨l, ?_, s⟩
    rintro ev rfl
    exact hh ev List.mem_cons_self

theorem callDiverges_of_diverges {m x : Config E σ} {c : CallId} {f : FuncId}
    {args : List Value.Val}
    {tr : List (Label E σ)} (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hh : ∀ ev, Label.host ev ∉ tr) (d : Diverges prof hr dispatch x) :
    CallDiverges prof hr dispatch m c f args := by
  obtain ⟨x₁, s₁, s₂⟩ := Steps.cons_iff.1 h
  exact ⟨x₁, s₁, diverges_of_steps s₂ hh d⟩

theorem callQuietDiverges_iff {m : Config E σ} {c : CallId} {f : FuncId} {args : List Value.Val}
    {st : σ} :
    CallQuietDiverges prof hr dispatch m c f args st ↔
      ∃ x, Step prof hr dispatch m (.host (invokeTop c f args)) x ∧
        QuietRest prof hr dispatch st x := by
  constructor
  · rintro ⟨x, tr, m₂, s, s', hh, d⟩
    exact ⟨x, s, tr, m₂, s', hh, d⟩
  · rintro ⟨x, s, tr, m₂, s', hh, d⟩
    exact ⟨x, tr, m₂, s, s', hh, d⟩

theorem callQuietDiverges_of_quietRest {m x : Config E σ} {c : CallId} {f : FuncId}
    {args : List Value.Val} {tr : List (Label E σ)} {st : σ}
    (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hh : ∀ ev, Label.host ev ∉ tr) (r : QuietRest prof hr dispatch st x) :
    CallQuietDiverges prof hr dispatch m c f args st := by
  obtain ⟨x₁, s₁, s₂⟩ := Steps.cons_iff.1 h
  obtain ⟨tr', m₂, s', hh', d⟩ := r
  refine callQuietDiverges_iff.2 ⟨x₁, s₁, tr ++ tr', m₂, steps_append s₂ s', ?_, d⟩
  intro ev hm
  rcases List.mem_append.1 hm with hm | hm
  · exact hh ev hm
  · exact hh' ev hm

section Chatter

variable {ε : Type} {hr : HostReady (σ × List ε)} {dispatch : Call E → P E (σ × List ε) (Ret E)}

theorem callHostProd_iff {m : Config E (σ × List ε)} {c : CallId} {f : FuncId}
    {args : List Value.Val} {ev : ℕ → ε} :
    CallHostProd prof hr dispatch m c f args ev ↔
      ∃ x, Step prof hr dispatch m (.host (invokeTop c f args)) x ∧
        HostProdRest prof hr dispatch m.host.2 x ev := by
  constructor
  · rintro ⟨t, s, hs, hl⟩
    exact ⟨t 0, s, t, rfl, hs, hl⟩
  · rintro ⟨x, s, t, rfl, hs, hl⟩
    exact ⟨t, s, hs, hl⟩

theorem hostProdRest_of_internalStep {x x' : Config E (σ × List ε)} {base : List ε}
    {ev : ℕ → ε} (s : InternalStep prof hr dispatch x x')
    (r : HostProdRest prof hr dispatch base x' ev) : HostProdRest prof hr dispatch base x ev := by
  obtain ⟨t, h0, hs, hl⟩ := r
  let t' : ℕ → Config E (σ × List ε) := fun n => match n with | 0 => x | n + 1 => t n
  refine ⟨t', rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero => simpa [t', h0] using s
    | succ n => exact hs n
  · intro N
    obtain ⟨n, p, hN, hp⟩ := hl N
    exact ⟨n, p + 1, hN, hp⟩

theorem hostProdRest_of_steps {x x' : Config E (σ × List ε)} {tr : List (Label E (σ × List ε))}
    {base : List ε} {ev : ℕ → ε} (h : Steps prof hr dispatch x tr x')
    (hh : ∀ e, Label.host e ∉ tr) (r : HostProdRest prof hr dispatch base x' ev) :
    HostProdRest prof hr dispatch base x ev := by
  induction h with
  | refl => exact r
  | @cons _ _ _ l _ s _ ih =>
    refine hostProdRest_of_internalStep ⟨l, ?_, s⟩
      (ih (fun e hm => hh e (List.mem_cons_of_mem _ hm)) r)
    rintro e rfl
    exact hh e List.mem_cons_self

theorem callHostProd_of_hostProdRest {m x : Config E (σ × List ε)} {c : CallId} {f : FuncId}
    {args : List Value.Val} {tr : List (Label E (σ × List ε))} {ev : ℕ → ε}
    (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hh : ∀ e, Label.host e ∉ tr) (r : HostProdRest prof hr dispatch m.host.2 x ev) :
    CallHostProd prof hr dispatch m c f args ev := by
  obtain ⟨x₁, s₁, s₂⟩ := Steps.cons_iff.1 h
  exact callHostProd_iff.2 ⟨x₁, s₁, hostProdRest_of_steps s₂ hh r⟩

end Chatter

end Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns
