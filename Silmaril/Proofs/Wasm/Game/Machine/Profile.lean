module

public import Silmaril.Wasm.Game.Machine.Defs
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.SingleThreaded.HeadInversion
public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# The single-threaded machine under an arbitrary profile

silmaril-lean states the single-threaded machine (`Internal o`, `status o`)
and its soundness corollaries for the deterministic profile `profile o`. Their
proofs only use Core facts that hold for every profile (`Step.split_host`,
`Step.of_noHost`, `Step.preservation`, `Config.progress`, `Step.framesLocal`).
This file restates the facts the game semantics needs for `InternalP P` and
`statusP P`, for an arbitrary profile `P`, and identifies the deterministic
instances (`internalP_profile`).

Source: proofs copied from silmaril-lean at the pinned revision,
`Silmaril/Wasm/SingleThreaded/{Agreement,Soundness,Interface,Locality}.lean`
(`step_iff`, `Internal.toStep`, `status_stuck_inv`, `status_callout_inv`,
`status_ne_stuck`, `Internal.preserves`, `resume_typed`, `reachable_typed`,
`status_returned_values`, `Internal.funcs_prefix`), with `profile o` replaced
by `P`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

attribute [local simp] Thread.config_store

/-! ### The deterministic instances -/

/-- For the deterministic profile `profile o`, `InternalP` is silmaril-lean's `Internal o`. -/
theorem internalP_profile (o : GrowOracle) : InternalP (H := H) (profile o) = Internal o := by
  funext x y
  rcases x with ⟨s, t⟩
  rcases y with ⟨s', t'⟩
  rfl

/-! ### Agreement with Core steps -/

/-- Host-free steps are Core steps for any host. -/
theorem InternalP.toStep (P : Profile) (host : HostSemantics H) {x y : Store H × Thread}
    (h : InternalP P x y) : Step P host (x.2.config x.1) (y.2.config y.1) := by
  rcases x with ⟨s, t⟩
  rcases y with ⟨s', t'⟩
  obtain ⟨f', code', rfl, h⟩ := h
  exact Step.of_noHost host h

/-- The right-hand side of the agreement `stepP_iff`: an internal step, or a host call at the
callout redex. -/
def StepShape (P : Profile) (host : HostSemantics H) (s : Store H) (t : Thread) (c' : Config H) :
    Prop :=
  (∃ s' f' code', c' = ⟨s', f', code'⟩ ∧ InternalP P (s, t) (s', .active f' code')) ∨
    (∃ E a h args, decompose? s (t.config s).code = some (E, a, h, args) ∧
      ((∃ s' r, host h s args (.returned s' r) ∧ c' = (resumeResult s t r).config s') ∨
       (host h s args .diverged ∧ c' = t.config s)))

/-- Agreement, `→`: a Core step from a thread has the shape `StepShape`. -/
theorem stepShape_of_step {host : HostSemantics H} {s : Store H} {t : Thread} {c' : Config H}
    (hstep : Step P host (t.config s) c') : StepShape P host s t c' := by
  rcases Step.split_host hstep with h | ⟨E, a, hh, args, hd, ⟨s', r, hr, heq⟩ | ⟨hdiv, heq⟩⟩
  · obtain ⟨s', f', code'⟩ := c'
    exact Or.inl ⟨s', f', code', rfl, f', code', rfl, h⟩
  · have hd' : decompose? s (t.config s).code = some (E, a, hh, args) := by simpa using hd
    have hr' : host hh s args (.returned s' r) := by simpa using hr
    have hc : c' = (resumeResult s t r).config s' := by rw [heq, resumeResult_config hd']
    exact Or.inr ⟨E, a, hh, args, hd', Or.inl ⟨s', r, hr', hc⟩⟩
  · have hd' : decompose? s (t.config s).code = some (E, a, hh, args) := by simpa using hd
    have hdiv' : host hh s args .diverged := by simpa using hdiv
    exact Or.inr ⟨E, a, hh, args, hd', Or.inr ⟨hdiv', heq⟩⟩

/-- Agreement, `←`: every `StepShape` is a Core step. -/
theorem step_of_stepShape {host : HostSemantics H} {s : Store H} {t : Thread} {c' : Config H}
    (h : StepShape P host s t c') : Step P host (t.config s) c' := by
  rcases h with ⟨s', f', code', rfl, f'', code'', heq, hi⟩ |
    ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · have hcfg : (⟨s', f', code'⟩ : Config H) = ⟨s', f'', code''⟩ := by cases heq; rfl
    exact hcfg ▸ Step.of_noHost host hi
  · obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
    have hres : (resumeResult s t r).config s' =
        ⟨s', (t.config s).frame, E.fill r.toAdmin⟩ := resumeResult_config hd
    rw [hres, Thread.config_eta s t, hcode]
    exact E.step_fill (fun g => Step.callRefHost hyy hf he hn hc hr) _
  · obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
    rw [Thread.config_eta s t, hcode]
    exact E.step_fill (fun g => Step.callRefHostDiv hyy hf he hn hc hdiv) _

/-- **Agreement** (`step_iff` for every profile): a Core step from a thread is an internal
step, or a host call at the callout redex. -/
theorem stepP_iff (P : Profile) (host : HostSemantics H) (s : Store H) (t : Thread)
    (c' : Config H) :
    Step P host (t.config s) c' ↔
      (∃ s' f' code', c' = ⟨s', f', code'⟩ ∧ InternalP P (s, t) (s', .active f' code')) ∨
      (∃ E a h args, decompose? s (t.config s).code = some (E, a, h, args) ∧
        ((∃ s' r, host h s args (.returned s' r) ∧ c' = (resumeResult s t r).config s') ∨
         (host h s args .diverged ∧ c' = t.config s))) :=
  ⟨stepShape_of_step, step_of_stepShape⟩

/-- Function instances are never modified by internal steps. -/
theorem InternalP.funcs_prefix {s s' : Store H} {t t' : Thread}
    (h : InternalP P (s, t) (s', t')) : s'.funcs = s.funcs := by
  obtain ⟨f', code', -, h⟩ := h
  have hl := Step.framesLocal h
  simp only [Thread.config_store] at hl
  exact hl.1

/-! ### Status -/

theorem statusP_stuck_inv {s : Store H} {t : Thread} (h : statusP P s t = .stuck) :
    (¬ ∃ vs, (t.config s).code = vals vs) ∧ (t.config s).code ≠ [.trap] ∧
      (¬ ∃ a, (t.config s).code = throwing a) ∧ decompose? s (t.config s).code = none ∧
      ¬ ∃ y, InternalP P (s, t) y := by
  unfold statusP at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h5 <;>
    rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩ <;>
    rw [hd] at h <;> first | exact ⟨h1, h2, h3, rfl, h5⟩ | cases h

theorem statusP_callout_inv {s : Store H} {t : Thread} {hc : H} {args : List Val}
    (h : statusP P s t = .callout hc args) :
    ∃ E a, decompose? s (t.config s).code = some (E, a, hc, args) := by
  unfold statusP at h
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

theorem statusP_returned_values {s : Store H} {t : Thread} {vs : List Val}
    (h : statusP P s t = .returned (.values vs)) : (t.config s).code = vals vs := by
  unfold statusP at h
  simp only at h
  split at h
  · rename_i hex
    simp only [Status.returned.injEq, CallResult.values.injEq] at h
    subst h
    exact hex.choose_spec
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h

theorem statusP_running_inv {s : Store H} {t : Thread} (h : statusP P s t = .running) :
    ∃ y, InternalP P (s, t) y := by
  by_contra hne
  unfold statusP at h
  simp only at h
  split_ifs at h
  first
    | cases h
    | (revert h; rcases decompose? s (Thread.config s t).code with _ | ⟨E, a, h', args'⟩ <;>
        simp_all)

theorem statusP_returned_trap_inv {s : Store H} {t : Thread}
    (h : statusP P s t = .returned .trap) :
    (t.config s).code = [.trap] ∨ ∃ a, (t.config s).code = throwing a := by
  unfold statusP at h
  simp only at h
  split_ifs at h
  all_goals first
    | exact .inl ‹_›
    | exact .inr ‹_›
    | cases h
    | (revert h; rcases decompose? s (Thread.config s t).code with _ | ⟨E, a, h', args'⟩ <;>
        simp_all)

/-! ### Soundness -/

/-- Typed threads on valid stores are never stuck, for every profile. -/
theorem statusP_ne_stuck {s : Store H} {t : Thread} {ts : List CValType}
    (_hs : StoreOk s) (ht : ThreadOk s t ts) : statusP P s t ≠ .stuck := by
  intro hst
  obtain ⟨h1, h2, h3, hd, hni⟩ := statusP_stuck_inv hst
  rcases Config.progress (P := P) (host := divHost) divHost_ok ht with
    ⟨r, hr⟩ | ⟨c', hc'⟩
  · cases r with
    | values vs => exact h1 ⟨vs, hr⟩
    | throw a => exact h3 ⟨a, hr⟩
    | trap => exact h2 hr
  · rcases (stepP_iff P divHost s t c').mp hc' with ⟨s', f', code', -, hi⟩ |
      ⟨E, a, h, args, hd', -⟩
    · exact hni ⟨_, hi⟩
    · rw [hd] at hd'; cases hd'

/-- Internal steps preserve typing and extend the store, for every profile. -/
theorem InternalP.preserves {s s' : Store H} {t t' : Thread} {ts : List CValType}
    (_hs : StoreOk s) (ht : ThreadOk s t ts) (h : InternalP P (s, t) (s', t')) :
    StoreOk s' ∧ ThreadOk s' t' ts ∧ Extend s s' := by
  obtain ⟨f', code', rfl, hst⟩ := h
  obtain ⟨hok, hext⟩ := Step.preservation (P := P) divHost_ok ht (Step.of_noHost divHost hst)
  exact ⟨ConfigOk.storeOk hok, hok, by simpa using hext⟩

/-- Typing along host-free runs, for every profile. -/
theorem reachableP_typed {ts : List CValType} {x y : Store H × Thread}
    (h : Relation.ReflTransGen (InternalP P) x y) (hs : StoreOk x.1)
    (ht : ThreadOk x.1 x.2 ts) : StoreOk y.1 ∧ ThreadOk y.1 y.2 ts := by
  induction h with
  | refl => exact ⟨hs, ht⟩
  | tail _ hst ih =>
    obtain ⟨hs₁, ht₁⟩ := ih
    obtain ⟨hs₂, ht₂, -⟩ := InternalP.preserves hs₁ ht₁ hst
    exact ⟨hs₂, ht₂⟩

/-- Resuming at a callout redex plugs the values into its context. -/
theorem resume_values_at {s s' : Store H} {t : Thread} {E : Ctx} {a : Nat} {hc : H}
    {args vs : List Val} (he : Extend s s')
    (hd : decompose? s (t.config s).code = some (E, a, hc, args)) :
    resume s' t (.values vs) = .active (t.config s).frame (E.fill (vals vs)) := by
  have hc' := Thread.config_extend he t hd
  have hd' := decompose?_extend he _ hd
  simp only [resume, hc', hd', CallResult.toAdmin]

/-- The typing of a thread, read on its explicit configuration. -/
theorem threadOk_config {s : Store H} {t : Thread} {ts : List CValType} (ht : ThreadOk s t ts) :
    ConfigOk ⟨s, (t.config s).frame, (t.config s).code⟩ ts := by
  have hcfg : t.config s = ⟨s, (t.config s).frame, (t.config s).code⟩ := by
    cases t <;> rfl
  exact hcfg ▸ ht

/-- Typed resumption (`resume_typed` for every profile). -/
theorem resumeP_typed {s s' : Store H} {t : Thread} {ts : List CValType}
    {hc : H} {args vs : List Val}
    (_hs : StoreOk s) (ht : ThreadOk s t ts) (hco : statusP P s t = .callout hc args)
    (hs' : StoreOk s') (he : Extend s s')
    (hvs : ∀ E a args', decompose? s (t.config s).code = some (E, a, hc, args') →
      ∃ (fi : FuncInst H) (ps rs : Ty (.list .val)), s.funcs[a]? = some fi ∧
        Expand fi.type (.func ps rs) ∧ List.Forall₂ (ValOk s') vs rs.toList) :
    ThreadOk s' (resume s' t (.values vs)) ts := by
  obtain ⟨E, a, hd⟩ := statusP_callout_inv hco
  obtain ⟨fi, yy, ps₀, rs₀, hf, -, hyy, he₀, hn₀, hcode⟩ := decompose?_sound hd
  obtain ⟨fi', ps, rs, hf', hexp, hvs'⟩ := hvs E a args hd
  have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have hexp' : Expand fi.type (.func ps rs) := hfi ▸ hexp
  have hps : ps₀ = ps := by
    have hty : Ty.func ps₀ rs₀ = Ty.func ps rs := Expand.func_eq he₀ hexp'
    exact (by simpa only [Ty.func.injEq] using hty : ps₀ = ps ∧ rs₀ = rs).1
  have hn : args.length = ps.length := hps ▸ hn₀
  have ht' : ConfigOk ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ ts :=
    hcode ▸ threadOk_config ht
  show ConfigOk ((resume s' t (.values vs)).config s') ts
  rw [resume_values_at he hd]
  exact Ctx.fill_callout_typed ht' hf hexp' hyy hn hs' he hvs'

/-! ### The first step of an invocation is deterministic, for every profile -/

/-- The shape of a host-free step from an invocation `$invoke(a, vs)`: the callee is a Wasm
function and the step enters its frame (no numeric choice is involved). -/
theorem invoke_step_shape {s : Store H} {a : Nat} {vs : List Val} {c : Config H}
    (h : Step P Det.noHost (invoke s a vs) c) :
    ∃ (pre args : List Val) (fi : FuncInst H) (ps rs : Ty (.list .val)) (code : Func),
      vs = pre ++ args ∧ s.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
      args.length = ps.length ∧ fi.code = .wasm code ∧
      c = ⟨s, {}, vals pre ++ [.frame rs.length (Frame.forCall fi.module args code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  let ty : DefType := (s.funcs[a]?.map FuncInst.type).getD default
  have hcode : (invoke s a vs).code = vals (vs ++ [.ref (.func a)]) ++ [.callRefType ty] := by
    simp [invoke, vals, Val.toAdmin, ty]
  have hcfg : invoke s a vs = ⟨s, {}, vals (vs ++ [.ref (.func a)]) ++ .callRefType ty :: []⟩ :=
    by rw [← hcode]; rfl
  rw [hcfg] at h
  obtain ⟨pre, args', c₀, hW, hh, rfl⟩ := hostFree_head_inv rfl (by simp) (by simp) h
  have hcall : (Admin.callRefType ty).IsCallRef := trivial
  have hctl : Det.famOf (Admin.callRefType ty) = .control := Det.IsCallRef.famOf hcall
  cases hh with
  | parametric h' => exact absurd ((Det.famOf_of_shape (Det.ParametricStep.shape h')).2) (by
      rw [hctl]; simp)
  | numeric h' => exact absurd ((Det.famOf_of_shape (Det.NumericStep.shape h')).2) (by
      rw [hctl]; simp)
  | vector h' => exact absurd ((Det.famOf_of_shape (Det.VectorStep.shape h')).2) (by
      rw [hctl]; simp)
  | «variable» h' => exact absurd ((Det.famOf_of_shape (Det.VariableStep.shape h')).2) (by
      rw [hctl]; simp)
  | table h' => exact absurd ((Det.famOf_of_shape (Det.TableStep.shape h')).2) (by
      rw [hctl]; simp)
  | memory h' => exact absurd ((Det.famOf_of_shape (Det.MemoryStep.shape h')).2) (by
      rw [hctl]; simp)
  | reference h' => exact absurd ((Det.famOf_of_shape (Det.RefStep.shape h')).2) (by
      rw [hctl]; simp)
  | aggregate h' => exact absurd ((Det.famOf_of_shape (Det.AggregateStep.shape h')).2) (by
      rw [hctl]; simp)
  | callRefNull hc =>
    exfalso
    have hlast := congrArg List.getLast? hW
    simp at hlast
  | @callRefFunc _ _ _ vs' a' fi ps rs code ha hc hf he hn hfc =>
    subst ha
    have hW' : vs ++ [Val.ref (.func a)] = (pre ++ vs') ++ [Val.ref (.func a')] := by
      simpa using hW
    obtain ⟨hpre, ha'⟩ := List.append_inj' hW' rfl
    cases ha'
    refine ⟨pre, vs', fi, ps, rs, code, hpre, hf, he, hn, hfc, ?_⟩
    simp

/-- **The first step of an invocation is unique, for every profile.** -/
theorem invoke_step_unique {s : Store H} {a : Nat} {vs : List Val} {c₁ c₂ : Config H}
    (h₁ : Step P Det.noHost (invoke s a vs) c₁) (h₂ : Step P Det.noHost (invoke s a vs) c₂) :
    c₁ = c₂ := by
  obtain ⟨pre₁, args₁, fi₁, ps₁, rs₁, code₁, hv₁, hf₁, he₁, hn₁, hc₁, rfl⟩ := invoke_step_shape h₁
  obtain ⟨pre₂, args₂, fi₂, ps₂, rs₂, code₂, hv₂, hf₂, he₂, hn₂, hc₂, rfl⟩ := invoke_step_shape h₂
  obtain rfl : fi₁ = fi₂ := Option.some.inj (hf₁.symm.trans hf₂)
  obtain rfl : code₁ = code₂ := by
    rw [hc₁] at hc₂
    exact (FuncCode.wasm.inj hc₂)
  have hty : Ty.func ps₁ rs₁ = Ty.func ps₂ rs₂ := Expand.func_eq he₁ he₂
  simp only [Ty.func.injEq] at hty
  obtain ⟨rfl, rfl⟩ := hty
  have hlen : args₁.length = args₂.length := hn₁.trans hn₂.symm
  obtain ⟨rfl, rfl⟩ := List.append_inj (hv₁.symm.trans hv₂) (by
    have := congrArg List.length (hv₁.symm.trans hv₂)
    simp only [List.length_append] at this
    omega)
  rfl

/-- The internal step of a pending invocation is unique, for every profile. -/
theorem InternalP.pending_unique {s : Store H} {a : Nat} {vs : List Val}
    {y₁ y₂ : Store H × Thread} (h₁ : InternalP P (s, .pending a vs) y₁)
    (h₂ : InternalP P (s, .pending a vs) y₂) : y₁ = y₂ := by
  rcases y₁ with ⟨s₁, t₁⟩
  rcases y₂ with ⟨s₂, t₂⟩
  obtain ⟨f₁, code₁, rfl, hs₁⟩ := h₁
  obtain ⟨f₂, code₂, rfl, hs₂⟩ := h₂
  have heq := invoke_step_unique hs₁ hs₂
  simp only [Config.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  rfl

/-- A run to a normal form passes through the unique successor of its start. -/
theorem reach_of_unique_step {α : Type _} {R : α → α → Prop} {x y z : α}
    (hu : ∀ y', R x y' → y' = y) (hxz : Relation.ReflTransGen R x z) (hz : ∀ w, ¬ R z w)
    (hxy : R x y) : Relation.ReflTransGen R y z := by
  rcases Relation.ReflTransGen.cases_head hxz with rfl | ⟨x₁, hx₁, hrest⟩
  · exact absurd hxy (hz y)
  · exact (hu x₁ hx₁) ▸ hrest

end Silmaril.Proofs.Wasm.Game
