module

public import Silmaril.Proofs.Wasm.Verify.Flow.Step
public import Silmaril.Proofs.Wasm.Verify.Guard.Plays
public import Silmaril.Proofs.Wasm.Verify.Check.Assert

/-!
# The flow analysis: no play calls the assertion with `false`

`FlowIn I G fs i` collects what the checker establishes with the flow analysis: the reachable
functions `G` are closed for calls (`CallPl`), every body in `G` passes the flow check for some
list of stable locals (`BodiesFlow`), the store and the exports are in `G`, `G` avoids the
assertion `i`, which takes one parameter. Then, every profile:

* `flow_guard`: a call of the assertion under the flow invariant is preceded by a value other than
  `i32 0` (a nonzero `i32`, or not an `i32`);
* `step_invF`, `reach_invF`: host-free runs keep threads invariant (`InvF`) or stop at a guarded
  call (`GuardedF`), a callout of the assertion with that value as argument;
* `strategy_assertOk_flow`: every question of the assertion in every play of
  `I.strategy P I.store` has a first argument other than `i32 0`;
* **`assertNeverFalse_of_flowIn`**: the program of `I` satisfies `assertNeverFalse i`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-- What the checker establishes with the flow analysis for the assertion import `i`. -/
structure FlowIn (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) : Prop where
  ok : I.Ok
  closed : FuncsClosed G fs (CallPl G (isHost I.store i) fs) I.store.funcs
  bodies : BodiesFlow G (isHost I.store i) fs I.store.funcs
  store : StoreIn G I.store
  exports : ∀ j, G (I.addr j)
  avoids : Avoids G I.store.funcs i
  arity : ∀ hi : i < I.imports.length, (I.imports.get ⟨i, hi⟩).params.length = 1

section
variable {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat} {i : Nat}

/-- The flow invariant of a running thread. -/
def InvF (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) (c : Config Nat) : Prop :=
  CfgIn G fs (CallPl G (isHost I.store i) fs) c ∧
    (∃ K, SeqOK K (isHost I.store i) fs c.frame c.code ∧
      ∀ b ∈ scopeSeqs c.code, SeqOK K (isHost I.store i) fs c.frame b) ∧
    FramesOK (isHost I.store i) fs c.code

/-- A thread standing at a call of the assertion whose argument is not `i32 0`. -/
def GuardedF (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) (c : Config Nat) :
    Prop :=
  ∃ (E : Ctx) (v : Val) (b : Nat) (d : DefType), v ≠ Val.i32 0 ∧ isHost I.store i b = true ∧
    c.code = E.fill (vals [v] ++ [.ref (.func b), .callRefType d]) ∧
    ∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvF I G fs i ⟨c.store, c.frame, E.fill r.toAdmin⟩

/-! ## Replacing the hole of a context -/

/-- **Replacing the hole of an evaluation context keeps the flow invariant.** -/
theorem fill_flow {bad : Nat → Bool} {X Y : List Admin}
    (h : ∀ (s : Store Nat) (f : Frame), FlowPost bad fs (⟨s, f, Y⟩ : Config Nat) ⟨s, f, X⟩) :
    ∀ (E : Ctx) (s : Store Nat) (f : Frame),
      FlowPost bad fs (⟨s, f, E.fill Y⟩ : Config Nat) ⟨s, f, E.fill X⟩
  | .top pre rest, s, f => by
    simpa only [Ctx.fill] using flow_ctxtInstrs (vs := pre) (rest := rest) (h s f)
  | .label pre n k E rest, s, f => by
    simpa only [Ctx.fill] using flow_ctxtInstrs (vs := pre) (rest := rest)
      (flow_ctxtLabel (n := n) (cont := k) (fill_flow h E s f))
  | .handler pre n cs E rest, s, f => by
    simpa only [Ctx.fill] using flow_ctxtInstrs (vs := pre) (rest := rest)
      (flow_ctxtHandler (n := n) (cs := cs) (fill_flow h E s f))
  | .frame pre n fr E rest, s, f => by
    simpa only [Ctx.fill] using flow_ctxtInstrs (vs := pre) (rest := rest)
      (flow_ctxtFrame (n := n) (f := f) (fill_flow h E s fr))

/-- A step that keeps the invariant of the reachability analysis keeps the flow invariant. -/
theorem invF_of_post {c c' : Config Nat} (hc : InvF I G fs i c)
    (hp : FlowPost (isHost I.store i) fs c c')
    (hc' : CfgIn G fs (CallPl G (isHost I.store i) fs) c') : InvF I G fs i c' := by
  obtain ⟨-, ⟨K, ⟨S, hS, hch⟩, hsc⟩, hfr⟩ := hc
  obtain ⟨-, ⟨S', -, hS', hok⟩, hsc', hfr'⟩ :=
    hp K S .other [] nofun hS (by simpa using hch) hsc hfr
  exact ⟨hc', ⟨K, ⟨S', hS', by simpa using hok⟩, hsc'⟩, hfr'⟩

/-! ## The argument of a call of the assertion -/

theorem other_ne_ex : Top.other ≠ Top.ex := nofun

theorem topOfVal_ne_zero {v : Val} (h : topOfVal v = .gd ∨ topOfVal v = .nonI32) :
    v ≠ Val.i32 0 := by
  rintro rfl
  have h0 : topOfVal (Val.i32 0) = .zero := by simp [topOfVal_i32]
  rw [h0] at h
  rcases h with h | h <;> cases h

/-- A value prefix after which a call of a bad function is allowed ends with a good value. -/
theorem vals_last_good {pre : List Val}
    (h : (pre.getLast?.map topOfVal).getD .other = .gd ∨
      (pre.getLast?.map topOfVal).getD .other = .nonI32) :
    ∃ (pre' : List Val) (v : Val), pre = pre' ++ [v] ∧ v ≠ Val.i32 0 := by
  rcases List.eq_nil_or_concat pre with rfl | ⟨pre', v, rfl⟩
  · simp at h
  · have hv : topOfVal v = .gd ∨ topOfVal v = .nonI32 := by simpa using h
    exact ⟨pre', v, by rw [List.concat_eq_append], topOfVal_ne_zero hv⟩

/-- The call is at the top of a checked sequence: a good value precedes it. -/
theorem guard_top {bad : Nat → Bool} {K S : List Nat} {x : FuncIdx} {a : Nat}
    (hx : fs[x.toNat]? = some a) (hb : bad a = true) {pre : List Val} {rest : List Admin}
    (hch : okA K bad fs ⟨S, .other⟩ (vals pre ++ [.plain (.call x)] ++ rest) = true) :
    ∃ (pre' : List Val) (v : Val), pre = pre' ++ [v] ∧ v ≠ Val.i32 0 := by
  have h₁ : okA K bad fs ⟨S, (pre.getLast?.map topOfVal).getD .other⟩
      ([.plain (.call x)] ++ rest) = true := by
    rw [← okA_vals_append other_ne_ex]
    simpa only [List.append_assoc] using hch
  have hbad : isBadCall bad fs (.call x) = true := by simp [isBadCall, hx, hb]
  have hne : (pre.getLast?.map topOfVal).getD .other ≠ .ex := topVals_ne_ex other_ne_ex pre
  have h₂ : reqI K bad fs ⟨S, (pre.getLast?.map topOfVal).getD .other⟩ (.call x) = true := by
    have h₂' : reqI K bad fs ⟨S, (pre.getLast?.map topOfVal).getD .other⟩ (.call x) = true ∧
        okA K bad fs (nextX K ⟨S, (pre.getLast?.map topOfVal).getD .other⟩ (.plain (.call x)))
          rest = true := by
      simpa [okA, hne, okX, okI] using h₁
    exact h₂'.1
  have h₃ : (pre.getLast?.map topOfVal).getD .other = .gd ∨
      (pre.getLast?.map topOfVal).getD .other = .nonI32 := by
    simpa [reqI, hbad, isSetK, or_assoc] using h₂
  exact vals_last_good h₃

/-- **A call of the assertion is preceded by a value other than `i32 0`.** -/
theorem flow_guard {bad : Nat → Bool} {x : FuncIdx} {a : Nat} (hx : fs[x.toNat]? = some a)
    (hb : bad a = true) :
    ∀ (E : Ctx) (K : List Nat) (f : Frame), SeqOK K bad fs f (E.fill [.plain (.call x)]) →
      (∀ b ∈ scopeSeqs (E.fill [.plain (.call x)]), SeqOK K bad fs f b) →
      FramesOK bad fs (E.fill [.plain (.call x)]) →
      ∃ (E' : Ctx) (v : Val), v ≠ Val.i32 0 ∧ ∀ Y, E.fill Y = E'.fill (vals [v] ++ Y)
  | .top pre rest, _, _, ⟨_, _, hch⟩, _, _ => by
    obtain ⟨pre', v, rfl, hv⟩ := guard_top hx hb (by simpa only [Ctx.fill] using hch)
    exact ⟨.top pre' rest, v, hv, fun Y => by simp [Ctx.fill, vals]⟩
  | .label pre n k E rest, K, f, _, hsc, hfr => by
    have hsv : scopeSeqs (vals pre) = [] ∧ frameScopes (vals pre) = [] :=
      scopes_of_codeBodies (by simp)
    have hmem : ∀ b ∈ E.fill [.plain (.call x)] :: scopeSeqs (E.fill [.plain (.call x)]),
        b ∈ scopeSeqs (Ctx.fill (.label pre n k E rest) [.plain (.call x)]) := by
      intro b hb
      simp only [Ctx.fill, scopeSeqs_append, hsv.1, scopeSeqs_label, List.nil_append,
        List.mem_append, List.mem_cons] at hb ⊢
      rcases hb with hb | hb
      · exact .inl (.inl hb)
      · exact .inl (.inr (.inl hb))
    have hfr' : FramesOK bad fs (E.fill [.plain (.call x)]) := fun p hp =>
      hfr p (by simp [Ctx.fill, frameScopes_append, hsv.2, hp])
    obtain ⟨E', v, hv, hE⟩ := flow_guard hx hb E K f (hsc _ (hmem _ (by simp)))
      (fun b hb => hsc b (hmem b (by simp [hb]))) hfr'
    exact ⟨.label pre n k E' rest, v, hv, fun Y => by simp [Ctx.fill, hE Y]⟩
  | .handler pre n cs E rest, K, f, _, hsc, hfr => by
    have hsv : scopeSeqs (vals pre) = [] ∧ frameScopes (vals pre) = [] :=
      scopes_of_codeBodies (by simp)
    have hmem : ∀ b ∈ E.fill [.plain (.call x)] :: scopeSeqs (E.fill [.plain (.call x)]),
        b ∈ scopeSeqs (Ctx.fill (.handler pre n cs E rest) [.plain (.call x)]) := by
      intro b hb
      simp only [Ctx.fill, scopeSeqs_append, hsv.1, scopeSeqs_handler, List.nil_append,
        List.mem_append, List.mem_cons] at hb ⊢
      rcases hb with hb | hb
      · exact .inl (.inl hb)
      · exact .inl (.inr (.inl hb))
    have hfr' : FramesOK bad fs (E.fill [.plain (.call x)]) := fun p hp =>
      hfr p (by simp [Ctx.fill, frameScopes_append, hsv.2, hp])
    obtain ⟨E', v, hv, hE⟩ := flow_guard hx hb E K f (hsc _ (hmem _ (by simp)))
      (fun b hb => hsc b (hmem b (by simp [hb]))) hfr'
    exact ⟨.handler pre n cs E' rest, v, hv, fun Y => by simp [Ctx.fill, hE Y]⟩
  | .frame pre n fr E rest, _, _, _, _, hfr => by
    have hsv : scopeSeqs (vals pre) = [] ∧ frameScopes (vals pre) = [] :=
      scopes_of_codeBodies (by simp)
    obtain ⟨K', hb', hsc'⟩ := hfr (fr, E.fill [.plain (.call x)])
      (by simp [Ctx.fill, frameScopes_append, hsv.2])
    have hfr' : FramesOK bad fs (E.fill [.plain (.call x)]) := fun p hp =>
      hfr p (by simp [Ctx.fill, frameScopes_append, hsv.2, hp])
    obtain ⟨E', v, hv, hE⟩ := flow_guard hx hb E K' fr hb' hsc' hfr'
    exact ⟨.frame pre n fr E' rest, v, hv, fun Y => by simp [Ctx.fill, hE Y]⟩

/-! ## One step -/

theorem flow_guardCall {bad : Nat → Bool} {s : Store Nat} {f : Frame} {v : Val} {x : FuncIdx}
    (r : Result) :
    FlowPost bad fs (⟨s, f, vals [v] ++ [.plain (.call x)]⟩ : Config Nat) ⟨s, f, r.toAdmin⟩ := by
  have hL : ∀ y ∈ vals [v] ++ [Admin.plain (.call x)], FlatX y :=
    flatX_vals_append [v] fun y hy =>
      (List.mem_singleton.1 hy) ▸ flatX_of_other (x := Admin.plain (.call x)) fun _ _ => rfl
  have hlast : ∀ e, (vals [v] ++ [Admin.plain (.call x)]).getLast? = some e → OtherX e := by
    intro e he
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at he
    exact he ▸ fun _ _ => rfl
  exact flow_flat hL (by simp) hlast (trivX_result r) (codeBodies_result r)

theorem invF_fill {s : Store Nat} {f : Frame} {E : Ctx} {Y : List Admin} {r : Result}
    (hc : InvF I G fs i ⟨s, f, E.fill Y⟩)
    (hY : ∀ (s : Store Nat) (f : Frame),
      FlowPost (isHost I.store i) fs (⟨s, f, Y⟩ : Config Nat) ⟨s, f, r.toAdmin⟩)
    (hr : ∀ x ∈ codeRefs r.toAdmin, RefIn G x) : InvF I G fs i ⟨s, f, E.fill r.toAdmin⟩ :=
  invF_of_post hc (fill_flow hY E s f)
    ⟨hc.1.1, hc.1.2.1, CodeIn.fill hc.1.2.2 (CodeIn.toAdmin hr)⟩

/-- A call of the assertion leads to a thread standing at a guarded call. -/
theorem guardedF_of_badStep {c c' : Config Nat} (hc : InvF I G fs i c)
    (hb : BadStep (fun a => isHost I.store i a = true) fs c c') : GuardedF I G fs i c' := by
  obtain ⟨E, x, a, d, hcode, rfl, hx, ha⟩ := hb
  obtain ⟨K, hseq, hsc⟩ := hc.2.1
  obtain ⟨E', v, hv, hE⟩ := flow_guard hx ha E K c.frame (hcode ▸ hseq) (hcode ▸ hsc)
    (hcode ▸ hc.2.2)
  refine ⟨E', v, a, d, hv, ha, hE _, fun r hr => ?_⟩
  have hc₀ : InvF I G fs i ⟨c.store, c.frame, E'.fill (vals [v] ++ [.plain (.call x)])⟩ := by
    rw [← hE, ← hcode]
    exact hc
  exact invF_fill hc₀ (fun _ _ => flow_guardCall r) hr

/-- **One host-free step from an invariant thread** (every profile). -/
theorem step_invF {P : Profile} {c c' : Config Nat} (hR : FlowIn I G fs i)
    (h : Step P Det.noHost c c') (hf : c.store.funcs = I.store.funcs) (hc : InvF I G fs i c) :
    (InvF I G fs i c' ∨ GuardedF I G fs i c') ∧ c'.store.funcs = c.store.funcs := by
  have hcl : FuncsClosed G fs (CallPl G (isHost I.store i) fs) c.store.funcs := hf ▸ hR.closed
  have hbf : BodiesFlow G (isHost I.store i) fs c.store.funcs := hf ▸ hR.bodies
  have hp : FlowPost (isHost I.store i) fs c c' := Step.flow h hc.1 hbf
  obtain ⟨hc' | hb, hfun⟩ := Step.cfgIn callPl_plainOK hostIn_noHost h hcl hc.1
  · exact ⟨.inl (invF_of_post hc hp hc'), hfun⟩
  · exact ⟨.inr (guardedF_of_badStep hc hb), hfun⟩

/-! ## Callouts of guarded calls -/

/-- **A thread at a guarded call is at a callout of the assertion with argument `[v]`.** -/
theorem guardedF_decompose (hR : FlowIn I G fs i) {c : Config Nat}
    (hf : c.store.funcs = I.store.funcs) {E : Ctx} {v : Val} {b : Nat} {d : DefType}
    (hb : isHost I.store i b = true)
    (hcode : c.code = E.fill (vals [v] ++ [.ref (.func b), .callRefType d])) :
    decompose? c.store c.code = some (E, b, i, [v]) := by
  obtain ⟨fi, hfi, hhost⟩ := isHost_iff.1 hb
  obtain ⟨hlt, hexp⟩ := hR.ok.host_type b fi i hfi hhost
  have hfi' : c.store.funcs[b]? = some fi := hf ▸ hfi
  have hn : [v].length =
      (Ty.ofList ((I.imports.get ⟨i, hlt⟩).params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList, List.length_map, hR.arity hlt]
    rfl
  rw [hcode]
  exact decompose_fill hfi' hexp hhost (c := .callRefType d) trivial hn E

/-! ## Host-free runs -/

/-- **Host-free runs keep threads invariant, or stop at a guarded call** (every profile). -/
theorem reach_invF {P : Profile} (hR : FlowIn I G fs i) {x y : Store Nat × Thread}
    (h : Reach P x y) (hf : x.1.funcs = I.store.funcs) (hc : InvF I G fs i (x.2.config x.1)) :
    (InvF I G fs i (y.2.config y.1) ∨ GuardedF I G fs i (y.2.config y.1)) ∧
      y.1.funcs = I.store.funcs := by
  induction h with
  | refl => exact ⟨.inl hc, hf⟩
  | @tail y' z _ hst ih =>
    obtain ⟨hy | hy, hfy⟩ := ih
    · obtain ⟨f', code', ht, hstep⟩ := hst
      have hf₀ : (y'.2.config y'.1).store.funcs = I.store.funcs := by
        rw [Thread.config_store]; exact hfy
      obtain ⟨hz, hfz⟩ := step_invF hR hstep hf₀ hy
      rw [ht]
      exact ⟨hz, hfz.trans hf₀⟩
    · obtain ⟨E, v, b, d, -, hb, hcode, -⟩ := hy
      have hf₀ : (y'.2.config y'.1).store.funcs = I.store.funcs := by
        rw [Thread.config_store]; exact hfy
      have hd := guardedF_decompose hR hf₀ hb hcode
      rw [Thread.config_store] at hd
      exact absurd hst (calloutAt_no_internal ⟨E, b, hd⟩ _)

/-! ## The transitions -/

/-- The invariant of the hidden states. -/
def HInvF (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) : I.HState → Prop
  | .idle s => StoreIn G s ∧ s.funcs = I.store.funcs
  | .running _ s t => InvF I G fs i (t.config s) ∧ s.funcs = I.store.funcs
  | .waiting _ s t _ => (∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvF I G fs i ((resumeResult s t r).config s)) ∧ s.funcs = I.store.funcs

theorem invF_invoke {s : Store Nat} (hs : StoreIn G s) {a : Nat} (ha : G a) {args : List Val}
    (hargs : ∀ r, Val.ref r ∈ args → RefIn G r) : InvF I G fs i (invoke s a args) := by
  have hcb : codeBodies (invoke s a args).code = [] := by simp [invoke]
  obtain ⟨hs₀, hf₀⟩ := scopes_of_codeBodies hcb
  have hv : okA [] (isHost I.store i) fs ⟨[], .other⟩ (invoke s a args).code = true := by
    simp only [invoke]
    rw [okA_vals_append other_ne_ex]
    simp [okA, okX, nextX]
  refine ⟨invoke_cfgIn hs ha hargs, ⟨[], ⟨[], sound_nil, hv⟩, ?_⟩, ?_⟩
  · intro b hb
    simp only [hs₀, List.not_mem_nil] at hb
  · intro p hp
    simp only [hf₀, List.not_mem_nil] at hp

/-- Resuming an invariant thread at a callout keeps the invariant. -/
theorem resume_invF {s : Store Nat} {t : Thread} (hc : InvF I G fs i (t.config s)) (r : Result)
    (hr : ∀ x ∈ codeRefs r.toAdmin, RefIn G x) : InvF I G fs i ((resumeResult s t r).config s) := by
  rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h, args⟩
  · have ht : resumeResult s t r = t := by unfold resumeResult; simp only [hd]
    rw [ht]; exact hc
  · rw [resumeResult_config hd]
    obtain ⟨_, yy, _, _, _, _, hyy, _, _, hfill⟩ := decompose?_sound hd
    have h₀ : t.config s = ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := by
      rw [← hfill]
      cases t <;> rfl
    have hc' : InvF I G fs i ⟨s, (t.config s).frame,
        E.fill (vals args ++ [.ref (.func a), yy])⟩ := h₀ ▸ hc
    exact invF_fill hc' (fun _ _ => flow_host hyy) hr

/-- At a callout of an invariant thread: not the assertion; resuming keeps the invariant. -/
theorem ucall_invF {s' : Store Nat} {t' : Thread} {h : Nat} {args : List Val} {e : I.E.Op}
    (hR : FlowIn I G fs i) (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hy : InvF I G fs i (t'.config s')) (hfy : s'.funcs = I.store.funcs) :
    (∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvF I G fs i ((resumeResult s' t' r).config s')) ∧ (e.1.val = i → assertOk e.2.1) := by
  obtain ⟨a, fi, ha, hf, hcode⟩ := callout_mem callout hy.1
  have hne : h ≠ i := fun hh => hR.avoids a fi ha (hfy ▸ hf) (hh ▸ hcode)
  exact ⟨fun r hr => resume_invF hy r hr, fun he => absurd ((ifaceOp?_fst op).symm.trans he) hne⟩

/-- At a callout of a guarded call: the assertion, with an argument other than `i32 0`. -/
theorem ucall_guardedF {s' : Store Nat} {t' : Thread} {h : Nat} {args : List Val} {e : I.E.Op}
    (hR : FlowIn I G fs i) (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hy : GuardedF I G fs i (t'.config s')) (hfy : s'.funcs = I.store.funcs) :
    (∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvF I G fs i ((resumeResult s' t' r).config s')) ∧ (e.1.val = i → assertOk e.2.1) := by
  obtain ⟨E, v, b, d, hv, hb, hcode, hres⟩ := hy
  have hf₀ : (t'.config s').store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
  have hd : decompose? s' (t'.config s').code = some (E, b, i, [v]) := by
    simpa [Thread.config_store] using guardedF_decompose hR hf₀ hb hcode
  obtain ⟨E₀, a₀, hd₀⟩ := callout
  have heq : (E₀, a₀, h, args) = (E, b, i, [v]) := Option.some.inj (hd₀.symm.trans hd)
  have hargs : args = [v] := by cases heq; rfl
  have hok : assertOk [v] := fun hc => hv (Option.some.inj hc)
  refine ⟨fun r hr => ?_, fun _ => (ifaceOp?_snd op).symm ▸ hargs.symm ▸ hok⟩
  rw [resumeResult_config hd]
  simpa [Thread.config_store] using hres r hr

theorem trans_ucallF {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {h : Nat}
    {args : List Val} {e : I.E.Op} (hR : FlowIn I G fs i) (run : Reach P (s, t) (s', t'))
    (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hq : HInvF I G fs i (.running f s t)) :
    HInvF I G fs i (.waiting f s' t' e) ∧ (e.1.val = i → assertOk e.2.1) := by
  obtain ⟨hy | hy, hfy⟩ := reach_invF hR run hq.2 hq.1
  · obtain ⟨h₁, h₂⟩ := ucall_invF hR callout op hy hfy
    exact ⟨⟨h₁, hfy⟩, h₂⟩
  · obtain ⟨h₁, h₂⟩ := ucall_guardedF hR callout op hy hfy
    exact ⟨⟨h₁, hfy⟩, h₂⟩

theorem trans_oretF {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {r : Result}
    (hR : FlowIn I G fs i) (run : Reach P (s, t) (s', t')) (final : ResultAt s' t' r)
    (hq : HInvF I G fs i (.running f s t)) : HInvF I G fs i (.idle s') := by
  obtain ⟨hy | hy, hfy⟩ := reach_invF hR run hq.2 hq.1
  · exact ⟨Thread.config_store s' t' ▸ hy.1.1, hfy⟩
  · obtain ⟨E, v, b, d, -, hb, hcode, -⟩ := hy
    have hf₀ : (t'.config s').store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
    have hd := guardedF_decompose hR hf₀ hb hcode
    rw [final, decompose_toAdmin_none] at hd
    cases hd

/-- **One transition keeps the invariant; questions of the assertion have a true argument.** -/
theorem trans_hInvF {P : Profile} {q q' : I.HState} {m : Move I.E I.F} (h : I.Trans P q m q')
    (hR : FlowIn I G fs i) (hq : HInvF I G fs i q) :
    HInvF I G fs i q' ∧ ∀ e, m = .inl (.ask e) → e.1.val = i → assertOk e.2.1 := by
  cases h with
  | call s f =>
    exact ⟨⟨invF_invoke hq.1 (hR.exports f.1) (typed_refIn f.2.2), hq.2⟩, fun _ he => by cases he⟩
  | ucall run callout op =>
    obtain ⟨hq', hok⟩ := trans_ucallF hR run callout op hq
    exact ⟨hq', fun _ he => by cases he; exact hok⟩
  | uret v => exact ⟨⟨hq.1 _ (answer_refIn v), hq.2⟩, fun _ he => by cases he⟩
  | oret run final answer => exact ⟨trans_oretF hR run final hq, fun _ he => by cases he⟩

theorem path_hInvF {P : Profile} {q q' : I.HState} {p : List (Move I.E I.F)}
    (h : I.Path P q p q') (hR : FlowIn I G fs i) (hq : HInvF I G fs i q) :
    ∀ e, (.inl (.ask e) : Move I.E I.F) ∈ p → e.1.val = i → assertOk e.2.1 := by
  induction h with
  | nil => intro e he; cases he
  | cons ht _ ih =>
    intro e he
    obtain ⟨hq', hm⟩ := trans_hInvF ht hR hq
    rcases List.mem_cons.1 he with he | he
    · exact hm e he.symm
    · exact ih hq' e he

/-- **Every question of the assertion import in every play has a first argument other than
`i32 0`** (every profile). -/
theorem strategy_assertOk_flow (hR : FlowIn I G fs i) (P : Profile) {q : List (Move I.E I.F)}
    (hq : q ∈ I.strategy P I.store) :
    ∀ e, (.inl (.ask e) : Move I.E I.F) ∈ q → e.1.val = i → assertOk e.2.1 := by
  obtain ⟨q', hpath⟩ := ScalarInstance.mem_strategy_iff.1 hq
  exact path_hInvF hpath hR ⟨hR.store, rfl⟩

end

/-- **Soundness of the flow analysis for "assert is never called with `false`"**
(every profile). -/
theorem assertNeverFalse_of_flowIn {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat}
    {i : (ifaceOf I).Imp} (hR : FlowIn I G fs i.val) (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I) i := by
  rw [models_iff]
  rintro t ⟨q, hq, rfl⟩ a hc
  obtain ⟨m, hm, hme⟩ := List.mem_map.1 hc
  obtain ⟨e, hei, rfl⟩ := moveEvent_icall hme
  have hea : moveEvent (X := ifaceOf I) (.inl (.ask e)) = Event.icall i a := hme
  have ha : e.2.1 = a := by
    simp only [moveEvent, Sum.map_inl, evOf, Event.icall, Sum.inl.injEq, SideEv.ask.injEq] at hea
    exact hea.2
  exact ha ▸ strategy_assertOk_flow hR P hq e hm (by rw [hei])

end Silmaril.Wasm.Verify
