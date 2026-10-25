module

public import Silmaril.Wasm.SingleThreaded.Locality
public import Silmaril.Wasm.SingleThreaded.Boundary
public import Silmaril.Wasm.SingleThreaded.CalloutTyping

@[expose] public section

/-! # Soundness corollaries for the single-threaded machine (U28)

From Core preservation and progress (`Execution/Core/Soundness.lean`):

* a typed thread on a valid store is never `stuck`;
* resuming a callout with values of the host function's result type yields a
  `running` or `returned` thread (the component model's `ResumeLawful`);
* internal steps preserve thread typing and extend the store.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

attribute [local simp] Thread.config_store

/-- A thread is typed with result type `ts` on store `s`. -/
def ThreadOk (s : Store H) (t : Thread) (ts : List CValType) : Prop := ConfigOk (t.config s) ts

/-! ## Helpers -/

/-- The host that always diverges: it satisfies `HostOk`, and Core progress and
preservation for it transfer to host-free (internal) steps. -/
def divHost : HostSemantics H := fun _ _ _ out => out = .diverged

theorem divHost_ok : HostOk (divHost (H := H)) := by
  intro _ _ _ _ _ _ _ _ _ _ _
  refine ⟨⟨.diverged, rfl⟩, fun out h => ?_⟩
  cases h
  trivial

theorem ConfigOk.storeOk {c : Config H} {ts : List CValType} (h : ConfigOk c ts) :
    StoreOk c.store := by
  obtain ⟨_, ⟨hs, _⟩, _⟩ := h
  exact hs

theorem status_stuck_inv {o : GrowOracle} {s : Store H} {t : Thread}
    (h : status o s t = .stuck) :
    (¬ ∃ vs, (t.config s).code = vals vs) ∧ (t.config s).code ≠ [.trap] ∧
      (¬ ∃ a, (t.config s).code = throwing a) ∧ decompose? s (t.config s).code = none ∧
      ¬ ∃ y, Internal o (s, t) y := by
  unfold status at h
  dsimp only at h
  by_cases h1 : ∃ vs, (t.config s).code = vals vs
  · rw [dite_eq_left h1] at h; cases h
  rw [dite_eq_right h1] at h
  by_cases h2 : (t.config s).code = [.trap]
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  by_cases h3 : ∃ a, (t.config s).code = throwing a
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h
  cases hd : decompose? s (t.config s).code with
  | some x =>
    rw [hd] at h
    obtain ⟨_, _, _, _⟩ := x
    cases h
  | none =>
    rw [hd] at h
    dsimp only at h
    by_cases h5 : ∃ y, Internal o (s, t) y
    · rw [ite_eq_left h5] at h; cases h
    · exact ⟨h1, h2, h3, rfl, h5⟩

theorem status_callout_inv {o : GrowOracle} {s : Store H} {t : Thread} {hc : H}
    {args : List Val} (h : status o s t = .callout hc args) :
    ∃ E a, decompose? s (t.config s).code = some (E, a, hc, args) := by
  unfold status at h
  dsimp only at h
  split_ifs at h
  all_goals
    revert h
    rcases decompose? s (Thread.config s t).code with _ | ⟨E, a, h', args'⟩
    · intro h
      simp at h
    · intro h
      simp only [Status.callout.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨E, a, rfl⟩

/-- **Milestone.** Typed threads on valid stores are never stuck. -/
theorem status_ne_stuck {o : GrowOracle} {s : Store H} {t : Thread} {ts : List CValType}
    (_hs : StoreOk s) (ht : ThreadOk s t ts) : status o s t ≠ .stuck := by
  intro hst
  obtain ⟨h1, h2, h3, hd, hni⟩ := status_stuck_inv hst
  rcases Config.progress (P := profile o) (host := divHost) divHost_ok ht with
    ⟨r, hr⟩ | ⟨c', hc'⟩
  · cases r with
    | values vs => exact h1 ⟨vs, hr⟩
    | throw a => exact h3 ⟨a, hr⟩
    | trap => exact h2 hr
  · rcases (step_iff o divHost s t c').mp hc' with ⟨s', f', code', -, hi⟩ | ⟨E, a, h, args, hd', -⟩
    · exact hni ⟨_, hi⟩
    · rw [hd] at hd'; cases hd'

/-- **Milestone.** Internal steps preserve typing and extend the store. -/
theorem Internal.preserves {o : GrowOracle} {s s' : Store H} {t t' : Thread} {ts : List CValType}
    (_hs : StoreOk s) (ht : ThreadOk s t ts) (h : Internal o (s, t) (s', t')) :
    StoreOk s' ∧ ThreadOk s' t' ts ∧ Extend s s' := by
  obtain ⟨f', code', rfl, hst⟩ := h
  obtain ⟨hok, hext⟩ :=
    Step.preservation (P := profile o) divHost_ok ht (Step.of_noHost divHost hst)
  exact ⟨ConfigOk.storeOk hok, hok, by simpa using hext⟩

theorem splitVals_vals_append_nonval (pre : List Val) (x : Admin) (rest : List Admin)
    (hx : x.val? = none) : splitVals (vals pre ++ x :: rest) = (pre, x :: rest) := by
  induction pre with
  | nil => simp [vals, splitVals, hx]
  | cons v pre ih =>
    simp only [vals, List.map_cons, List.cons_append] at ih ⊢
    rw [splitVals]
    simp [ih]

theorem hostArity?_extend {s s' : Store H} (he : Extend s s') {a : Nat} {p : H × Nat}
    (h : hostArity? s a = some p) : hostArity? s' a = some p := by
  unfold hostArity? at h ⊢
  cases hf : s.funcs[a]? with
  | none => simp [hf] at h
  | some fi =>
    obtain ⟨fi', hf', hty, -, -, hhost⟩ := he.funcs.2 a fi hf
    rw [hf] at h
    rw [hf']
    dsimp only at h ⊢
    rw [← hty]
    revert h
    cases hc : fi.code with
    | wasm c => simp
    | host h₀ => rw [hhost h₀ hc]; exact id

/-- `decompose?` succeeds with the same answer on an extended store. -/
theorem decompose?_extend {s s' : Store H} (he : Extend s s') (code : List Admin)
    {x : Ctx × Nat × H × List Val} (hd : decompose? s code = some x) :
    decompose? s' code = some x := by
  induction code using decompose?.induct (s := s) generalizing x
  all_goals (rw [decompose?] at hd ⊢; split at hd <;> simp_all)
  all_goals first
    | (obtain ⟨a, b, c, d, h1, h2⟩ := hd; exact ⟨a, b, c, d, by simp_all, h2⟩)
    | (rw [hostArity?_extend he ‹hostArity? s _ = some _›]; simp_all)
    | (exfalso; obtain ⟨-, h2, -⟩ := ‹_ = _ ∧ _ = _ ∧ _ = _›; subst h2; simp_all)

/-- The Core typing obligation behind `resume_typed`: replacing a typed host-call
redex in an evaluation context by values of the callee's result type, over an
extended valid store, preserves configuration typing.

(Fixed statement: added `hn : args.length = ps.length`. Without it the statement
is false: with `E = .top [v] []`, `args = []` and a host function `$h : [i32] → []`,
the redex `i32.const 1; ref.func $h; call_ref` has type `[] → []`, but the
replacement `i32.const 1` has type `[] → [i32]`. `decompose?_sound` provides it.) -/
theorem Ctx.fill_callout_typed {s s' : Store H} {f : Frame} {E : Ctx} {a : Nat}
    {fi : FuncInst H} {yy : Admin} {ps rs : Ty (.list .val)} {args vs : List Val}
    {ts : List CValType}
    (hok : ConfigOk ⟨s, f, E.fill (vals args ++ [.ref (.func a), yy])⟩ ts)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hyy : yy.IsCallRef)
    (hn : args.length = ps.length)
    (hs' : StoreOk s') (hext : Extend s s') (hvs : List.Forall₂ (ValOk s') vs rs.toList) :
    ConfigOk ⟨s', f, E.fill (vals vs)⟩ ts := by
  obtain ⟨C, ⟨hs, hfr⟩, hc⟩ := hok
  refine ⟨C, ⟨hs', FrameOk.extend_of_storeOk hs hext hfr⟩, ?_⟩
  refine co_fill hs hext ?_ E C _ (CoCI.ofFrame hfr) hc
  intro C it pre rest hC h
  have e : vals pre ++ (vals args ++ [.ref (.func a), yy]) ++ rest =
      vals (pre ++ (args ++ [Val.ref (.func a)])) ++ yy :: rest := by
    simp [vals, Val.toAdmin]
  rw [e] at h
  obtain ⟨-, -, O1, -⟩ := co_top hs hext (pre := pre) (Q := args ++ [Val.ref (.func a)])
    (vs := vs) (r := Val.ref (.func a)) (yy := yy) (by simp) CoCI
    (fun C xs hC => hC.initLocals xs)
    (fun C it₀ ha => co_base0 hyy ha)
    (fun C it₀ A' tvs Z₂ hC ha hp hz hl =>
      co_base hs hf he hyy hn hvs C it₀ A' tvs Z₂ hC ha hp hz hl)
    h hC _ rest rfl
  simpa using O1 [] pre rfl rfl

theorem Thread.config_extend {s s' : Store H} (he : Extend s s') (t : Thread)
    {x : Ctx × Nat × H × List Val} (hd : decompose? s (t.config s).code = some x) :
    t.config s' = ⟨s', (t.config s).frame, (t.config s).code⟩ := by
  cases t with
  | active f code => rfl
  | pending a args =>
    simp only [Thread.config, Execution.Core.invoke] at hd ⊢
    congr 2
    cases hf : s.funcs[a]? with
    | none =>
      exfalso
      have hsv := splitVals_vals_append_nonval (args ++ [.ref (.func a)])
        (.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) [] rfl
      simp only [vals_append, List.append_assoc] at hsv
      rw [decompose?] at hd
      split at hd <;> simp_all [vals, Val.toAdmin, hostArity?, Admin.isCallRef]
      all_goals (obtain ⟨rfl, -, -⟩ := ‹_ ∧ _ ∧ _›; simp [List.getElem?_eq_none hf] at hd)
    | some fi =>
      obtain ⟨fi', hf', hty, -⟩ := he.funcs.2 a fi hf
      simp [hf', hty]

/-- Typed resumption (helper for `resume_progress`): plugging values of the host
function's result type into the callout context, over an extended valid store,
gives a typed thread. -/
theorem resume_typed {o : GrowOracle} {s s' : Store H} {t : Thread} {ts : List CValType}
    {hc : H} {args vs : List Val}
    (_hs : StoreOk s) (ht : ThreadOk s t ts) (hco : status o s t = .callout hc args)
    (hs' : StoreOk s') (he : Extend s s')
    (hvs : ∀ E a args', decompose? s (t.config s).code = some (E, a, hc, args') →
      ∃ (fi : FuncInst H) (ps rs : Ty (.list .val)), s.funcs[a]? = some fi ∧
        Expand fi.type (.func ps rs) ∧ List.Forall₂ (ValOk s') vs rs.toList) :
    ThreadOk s' (resume s' t (.values vs)) ts := by
  obtain ⟨E, a, hd⟩ := status_callout_inv hco
  obtain ⟨fi, yy, ps₀, rs₀, hf, -, hyy, he₀, hn₀, hcode⟩ := decompose?_sound hd
  obtain ⟨fi', ps, rs, hf', hexp, hvs'⟩ := hvs E a args hd
  rw [hf] at hf'
  cases hf'
  have hc := Thread.config_extend he t hd
  have hd' := decompose?_extend he _ hd
  have hr : resume s' t (.values vs) = .active (t.config s).frame (E.fill (vals vs)) := by
    simp only [resume, hc, hd', CallResult.toAdmin]
  rw [hr]
  unfold ThreadOk at ht ⊢
  have ht' : ConfigOk ⟨s, (t.config s).frame, (t.config s).code⟩ ts := by
    have : t.config s = ⟨s, (t.config s).frame, (t.config s).code⟩ := by
      cases t <;> rfl
    rw [← this]; exact ht
  rw [hcode] at ht'
  have hps : ps₀ = ps := by
    have := Expand.func_eq he₀ hexp
    simp only [Ty.func.injEq] at this
    exact this.1
  subst hps
  exact Ctx.fill_callout_typed ht' hf hexp hyy hn₀ hs' he hvs'

/-- **Milestone (typed resume progress).** Resuming a callout with values typed by
the host function's result type gives a typed thread that is running, returned,
or immediately at another callout.

(Fixed statement: the skeleton omitted the `callout` case, which is false — e.g.
`call $h1; call_ref $t` where the host function `$h1` returns a reference to a
nullary host function `$h2`: after resumption the thread is at the callout of
`$h2`.) -/
theorem resume_progress {o : GrowOracle} {s s' : Store H} {t : Thread} {ts : List CValType}
    {hc : H} {args vs : List Val}
    (hs : StoreOk s) (ht : ThreadOk s t ts) (hco : status o s t = .callout hc args)
    (hs' : StoreOk s') (he : Extend s s')
    (hvs : ∀ E a args', decompose? s (t.config s).code = some (E, a, hc, args') →
      ∃ (fi : FuncInst H) (ps rs : Ty (.list .val)), s.funcs[a]? = some fi ∧
        Expand fi.type (.func ps rs) ∧ List.Forall₂ (ValOk s') vs rs.toList) :
    status o s' (resume s' t (.values vs)) = .running ∨
      (∃ r, status o s' (resume s' t (.values vs)) = .returned r) ∨
      ∃ hc' args', status o s' (resume s' t (.values vs)) = .callout hc' args' := by
  have hok := resume_typed hs ht hco hs' he hvs
  have hne := status_ne_stuck (o := o) hs' hok
  generalize status o s' (resume s' t (.values vs)) = st at hne ⊢
  cases st with
  | running => exact Or.inl rfl
  | returned r => exact Or.inr (Or.inl ⟨r, rfl⟩)
  | callout h a => exact Or.inr (Or.inr ⟨h, a, rfl⟩)
  | stuck => exact absurd rfl hne

theorem reachable_typed {o : GrowOracle} {ts : List CValType} {x y : Store H × Thread}
    (h : Relation.ReflTransGen (Internal o) x y) (hs : StoreOk x.1) (ht : ThreadOk x.1 x.2 ts) :
    StoreOk y.1 ∧ ThreadOk y.1 y.2 ts := by
  induction h with
  | refl => exact ⟨hs, ht⟩
  | tail _ hst ih =>
    obtain ⟨hs₁, ht₁⟩ := ih
    obtain ⟨hs₂, ht₂, -⟩ := Internal.preserves hs₁ ht₁ hst
    exact ⟨hs₂, ht₂⟩

/-- **Milestone (boundary obligation).** A run of internal steps from a typed
invocation never reaches a stuck thread: every reachable thread is running, at a
callout, or returned — and an exception escaping the outermost activation is
`.returned .trap` (`status_throw`). This is the component model's
`call_and_trap_on_throw` obligation (strengthens `invoke_throw_trap`). -/
theorem invoke_reachable_not_stuck {o : GrowOracle} {s s' : Store H} {a : Nat}
    {args : List Val} {t : Thread} (hs : StoreOk s) (hinv : InvokeOk s a args)
    (h : Relation.ReflTransGen (Internal o) (s, Thread.invoke a args) (s', t)) :
    status o s' t ≠ .stuck := by
  obtain ⟨_, _, rs, -, -, hok⟩ := invoke_ok hs hinv
  obtain ⟨hs', ht'⟩ := reachable_typed (ts := rs.toList) h hs hok
  exact status_ne_stuck hs' ht'

/-! ## Trap resumption -/

theorem Ctx.fill_trap_step {P : Profile} (E : Ctx) (s : Store H) (f : Frame) :
    E.fill [.trap] = [.trap] ∨
      ∃ f' c', Step P (fun _ _ _ _ => False) ⟨s, f, E.fill [.trap]⟩ ⟨s, f', c'⟩ := by
  induction E generalizing f with
  | top pre rest =>
    simp only [Ctx.fill]
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact Or.inr ⟨f, _, Step.trapInstrs hne⟩
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      left; rfl
  | label pre n cont E rest ih =>
    have hin : ∃ f' c', Step P (fun _ _ _ _ => False) ⟨s, f, [.label n cont (E.fill [.trap])]⟩
        ⟨s, f', c'⟩ := by
      rcases ih f with h | ⟨f', c', h⟩
      · rw [h]; exact ⟨f, _, Step.trapLabel⟩
      · exact ⟨f', _, Step.ctxtLabel h⟩
    right
    obtain ⟨f', c', hst⟩ := hin
    simp only [Ctx.fill]
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact ⟨f', _, Step.ctxtInstrs hst hne⟩
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      exact ⟨f', c', by simpa [vals] using hst⟩
  | handler pre n cs E rest ih =>
    have hin : ∃ f' c', Step P (fun _ _ _ _ => False) ⟨s, f, [.handler n cs (E.fill [.trap])]⟩
        ⟨s, f', c'⟩ := by
      rcases ih f with h | ⟨f', c', h⟩
      · rw [h]; exact ⟨f, _, Step.trapHandler⟩
      · exact ⟨f', _, Step.ctxtHandler h⟩
    right
    obtain ⟨f', c', hst⟩ := hin
    simp only [Ctx.fill]
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact ⟨f', _, Step.ctxtInstrs hst hne⟩
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      exact ⟨f', c', by simpa [vals] using hst⟩
  | frame pre n fr E rest ih =>
    have hin : ∃ f' c', Step P (fun _ _ _ _ => False) ⟨s, f, [.frame n fr (E.fill [.trap])]⟩
        ⟨s, f', c'⟩ := by
      rcases ih fr with h | ⟨f', c', h⟩
      · rw [h]; exact ⟨f, _, Step.trapFrame⟩
      · exact ⟨f, _, Step.ctxtFrame h⟩
    right
    obtain ⟨f', c', hst⟩ := hin
    simp only [Ctx.fill]
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact ⟨f', _, Step.ctxtInstrs hst hne⟩
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      exact ⟨f', c', by simpa [vals] using hst⟩

theorem Ctx.fill_trap_shape (E : Ctx) :
    ∃ pre x rest, E.fill [.trap] = vals pre ++ x :: rest ∧ x.val? = none := by
  cases E with
  | top pre rest => exact ⟨pre, .trap, rest, by simp [Ctx.fill], rfl⟩
  | label pre n cont E rest => exact ⟨pre, .label n cont (E.fill [.trap]), rest, by simp [Ctx.fill], rfl⟩
  | handler pre n cs E rest => exact ⟨pre, .handler n cs (E.fill [.trap]), rest, by simp [Ctx.fill], rfl⟩
  | frame pre n fr E rest => exact ⟨pre, .frame n fr (E.fill [.trap]), rest, by simp [Ctx.fill], rfl⟩

theorem Ctx.fill_trap_not_vals (E : Ctx) : ¬ ∃ vs, E.fill [.trap] = vals vs := by
  rintro ⟨vs, hvs⟩
  obtain ⟨pre, x, rest, hfill, hx⟩ := E.fill_trap_shape
  have hmem : x ∈ vals vs := by rw [← hvs, hfill]; simp
  simp only [vals, List.mem_map] at hmem
  obtain ⟨v, -, rfl⟩ := hmem
  simp at hx

theorem Ctx.decompose?_fill_trap (s : Store H) (E : Ctx) : decompose? s (E.fill [.trap]) = none := by
  induction E with
  | top pre rest =>
    have hsv := splitVals_vals_append_nonval pre .trap rest rfl
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at hsv ⊢
    rw [decompose?]
    split <;> simp_all [Admin.isCallRef]
  | label pre n cont E rest ih =>
    have hsv := splitVals_vals_append_nonval pre (.label n cont (E.fill [.trap])) rest rfl
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at hsv ⊢
    rw [decompose?]
    split <;> simp_all
  | handler pre n cs E rest ih =>
    have hsv := splitVals_vals_append_nonval pre (.handler n cs (E.fill [.trap])) rest rfl
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at hsv ⊢
    rw [decompose?]
    split <;> simp_all
  | frame pre n fr E rest ih =>
    have hsv := splitVals_vals_append_nonval pre (.frame n fr (E.fill [.trap])) rest rfl
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at hsv ⊢
    rw [decompose?]
    split <;> simp_all

/-- A trapping resumption returns a trap or keeps running (traps propagate). -/
theorem resume_trap {o : GrowOracle} {s : Store H} {t : Thread} {hc : H} {args : List Val}
    (hco : status o s t = .callout hc args) :
    status o s (resume s t .trap) = .running ∨ status o s (resume s t .trap) = .returned .trap := by
  obtain ⟨E, a, hd⟩ := status_callout_inv hco
  have hr : resume s t .trap = .active (t.config s).frame (E.fill [.trap]) := by
    simp only [resume, hd, CallResult.toAdmin]
  rw [hr]
  generalize (t.config s).frame = fr
  have hex : E.fill [.trap] ≠ [.trap] → ∃ y, Internal o (s, .active fr (E.fill [.trap])) y := by
    intro hne
    rcases E.fill_trap_step (P := profile o) s fr with h | ⟨f', c', hst⟩
    · exact absurd h hne
    · exact ⟨(s, .active f' c'), f', c', rfl, hst⟩
  unfold status
  dsimp only [Thread.config]
  rw [dite_eq_right E.fill_trap_not_vals]
  split_ifs with h2 h3 h4
  all_goals first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | exact absurd (hex h2) h4
    | (rw [E.decompose?_fill_trap s]
       exact Or.inl rfl)

end Silmaril.Wasm.SingleThreaded
