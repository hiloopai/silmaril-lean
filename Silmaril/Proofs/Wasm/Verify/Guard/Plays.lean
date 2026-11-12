module

public import Silmaril.Proofs.Wasm.Verify.Guard.Callout
public import Silmaril.Proofs.Wasm.Verify.Reach.Plays
public import Silmaril.Wasm.Game.Machine.Thms

/-!
# Guarded calls: every assertion call of every play has a true first argument

`GuardIn I G fs i` collects what the checker establishes about an instance `I` and its
assertion import `i`: the invariant hypotheses of the reachability analysis for the
instruction predicate `GuardPl G B fs` (with `B = HostOf I.store.funcs i`, the host functions
of import `i`), guarded function bodies, and the arity `1` of the import.

Along every play, threads satisfy `InvA` (reachability invariant and guard discipline), or
stand at a guarded call (`GuardedA`: `E.fill [i32.const c, ref.func b, call_ref]`, `c ≠ 0`,
`b` the assertion), where they are at a callout of the assertion with argument `[c]`
(`guardedA_callout`). Hence every import question of `i` has a nonzero first argument
(`strategy_assertOk`), and the program satisfies `assertNeverFalse i`
(`assertNeverFalse_of_guardIn`). Every profile.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-- The host functions of import `i`. -/
def HostOf (funcs : List (FuncInst Nat)) (i b : Nat) : Prop :=
  ∃ fi, funcs[b]? = some fi ∧ fi.code = .host i

/-- What the checker establishes for "the assertion import `i` is never called with `false`". -/
structure GuardIn (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) : Prop where
  ok : I.Ok
  closed : FuncsClosed G fs (GuardPl G (HostOf I.store.funcs i) fs) I.store.funcs
  bodies : BodiesGuarded G (HostOf I.store.funcs i) fs I.store.funcs
  store : StoreIn G I.store
  exports : ∀ j, G (I.addr j)
  avoids : Avoids G I.store.funcs i
  arity : ∀ hi : i < I.imports.length, (I.imports.get ⟨i, hi⟩).params.length = 1

section
variable {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat} {i : Nat}

/-- The invariant of a running thread. -/
def InvA (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) (c : Config Nat) : Prop :=
  CfgIn G fs (GuardPl G (HostOf I.store.funcs i) fs) c ∧
    Chain (HostOf I.store.funcs i) fs .other c.code ∧ DeepP (HostOf I.store.funcs i) fs c.code

/-- A thread standing at a guarded call of the assertion. -/
def GuardedA (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) (c : Config Nat) :
    Prop :=
  ∃ (E : Ctx) (v : BitVec IntType.i32.width) (b : Nat) (d : DefType), v ≠ 0 ∧
    HostOf I.store.funcs i b ∧
    c.code = E.fill (vals [.num ⟨.int .i32, v⟩] ++ [.ref (.func b), .callRefType d]) ∧
    ∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvA I G fs i ⟨c.store, c.frame, E.fill r.toAdmin⟩

/-! ## Replacing a redex by a result -/

theorem invA_fill {s : Store Nat} {f : Frame} {E : Ctx} {Y : List Admin} {r : Result}
    (hc : InvA I G fs i ⟨s, f, E.fill Y⟩)
    (hY : PairPost (HostOf I.store.funcs i) fs (⟨s, f, Y⟩ : Config Nat) ⟨s, f, r.toAdmin⟩)
    (hr : ∀ x ∈ codeRefs r.toAdmin, RefIn G x) : InvA I G fs i ⟨s, f, E.fill r.toAdmin⟩ := by
  have hp : PairPost (HostOf I.store.funcs i) fs (⟨s, f, E.fill Y⟩ : Config Nat)
      ⟨s, f, E.fill r.toAdmin⟩ := fill_pair hY E s f
  obtain ⟨hch, hd⟩ := hp hc.2.2
  exact ⟨⟨hc.1.1, hc.1.2.1, CodeIn.fill hc.1.2.2 (CodeIn.toAdmin hr)⟩,
    by simpa using hch .other [] (by simpa using hc.2.1), hd⟩

theorem pair_guardCall {s : Store Nat} {f : Frame} {v : BitVec IntType.i32.width} {x : FuncIdx}
    (r : Result) :
    PairPost (HostOf I.store.funcs i) fs
      (⟨s, f, vals [.num ⟨.int .i32, v⟩] ++ [.plain (.call x)]⟩ : Config Nat) ⟨s, f, r.toAdmin⟩ :=
  fun _ => ⟨pair_flat (lastVals_ex rfl) (by simp) (lastVals_gd rfl) (toAdmin_noBad r),
    by cases r <;> exact deepP_flat (by simp [Result.toAdmin]) (by simp [Result.toAdmin])⟩

/-! ## One step -/

theorem invA_of_cfgIn {c c' : Config Nat} (hc : InvA I G fs i c)
    (hp : PairPost (HostOf I.store.funcs i) fs c c')
    (hc' : CfgIn G fs (GuardPl G (HostOf I.store.funcs i) fs) c') : InvA I G fs i c' := by
  obtain ⟨hch, hd⟩ := hp hc.2.2
  exact ⟨hc', by simpa using hch .other [] (by simpa using hc.2.1), hd⟩

/-- A guarded call leads to a thread standing at the guarded call. -/
theorem guardedA_of_badStep {c c' : Config Nat} (hc : InvA I G fs i c)
    (hb : BadStep (HostOf I.store.funcs i) fs c c') : GuardedA I G fs i c' := by
  obtain ⟨E, x, a, d, hcode, rfl, hx, ha⟩ := hb
  have hbad : BadI (HostOf I.store.funcs i) fs (.call x) := ⟨x, a, rfl, hx, ha⟩
  obtain ⟨E', v, hv, hE⟩ := guard_ctx hbad E (hcode ▸ hc.2.1) (hcode ▸ hc.2.2)
  refine ⟨E', v, a, d, hv, ha, hE _, fun r hr => ?_⟩
  have hc₀ : InvA I G fs i ⟨c.store, c.frame,
      E'.fill (vals [.num ⟨.int .i32, v⟩] ++ [.plain (.call x)])⟩ := by
    rw [← hE]; rw [← hcode]; exact hc
  exact invA_fill hc₀ (pair_guardCall r) hr

/-- **One host-free step from an invariant thread** (every profile). -/
theorem step_invA {P : Profile} {c c' : Config Nat} (hR : GuardIn I G fs i)
    (h : Step P Det.noHost c c') (hf : c.store.funcs = I.store.funcs) (hc : InvA I G fs i c) :
    (InvA I G fs i c' ∨ GuardedA I G fs i c') ∧ c'.store.funcs = c.store.funcs := by
  have hcl : FuncsClosed G fs (GuardPl G (HostOf I.store.funcs i) fs) c.store.funcs :=
    hf ▸ hR.closed
  have hbg : BodiesGuarded G (HostOf I.store.funcs i) fs c.store.funcs := hf ▸ hR.bodies
  have hp : PairPost (HostOf I.store.funcs i) fs c c' := Step.pair h hc.1 hbg
  obtain ⟨hc' | hb, hfun⟩ := Step.cfgIn guardPl_plainOK hostIn_noHost h hcl hc.1
  · exact ⟨.inl (invA_of_cfgIn hc hp hc'), hfun⟩
  · exact ⟨.inr (guardedA_of_badStep hc hb), hfun⟩

/-! ## Callouts of guarded calls -/

/-- **A thread at a guarded call is at a callout of the assertion with argument `[c]`.** -/
theorem guardedA_decompose (hR : GuardIn I G fs i) {c : Config Nat}
    (hf : c.store.funcs = I.store.funcs) {E : Ctx} {v : BitVec IntType.i32.width} {b : Nat}
    {d : DefType} (hb : HostOf I.store.funcs i b)
    (hcode : c.code = E.fill (vals [.num ⟨.int .i32, v⟩] ++ [.ref (.func b), .callRefType d])) :
    decompose? c.store c.code = some (E, b, i, [.num ⟨.int .i32, v⟩]) := by
  obtain ⟨fi, hfi, hhost⟩ := hb
  obtain ⟨hlt, hexp⟩ := hR.ok.host_type b fi i hfi hhost
  have hfi' : c.store.funcs[b]? = some fi := hf ▸ hfi
  have hn : [Val.num ⟨.int .i32, v⟩].length =
      (Ty.ofList ((I.imports.get ⟨i, hlt⟩).params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList, List.length_map, hR.arity hlt]
    rfl
  rw [hcode]
  exact decompose_fill hfi' hexp hhost (c := .callRefType d) trivial hn E

theorem decompose_toAdmin_none {s : Store Nat} (r : Result) : decompose? s r.toAdmin = none := by
  cases r with
  | values vs => exact decompose?_vals_nil
  | trap =>
    show decompose? s [.trap] = none
    simpa [Ctx.fill, vals] using Ctx.decompose?_fill_trap s (.top [] [])
  | throw a =>
    have hs : splitVals (throwing a) = ([.ref (.exn a)], [.plain .throwRef]) := by
      simp [splitVals, Admin.val?]
    rw [show Result.toAdmin (.throw a) = throwing a from rfl, decompose?_of_split hs]
    simp [decompHead, Admin.isCallRef]

/-! ## Host-free runs -/

/-- **Host-free runs keep threads invariant, or stop at a guarded call** (every profile). -/
theorem reach_invA {P : Profile} (hR : GuardIn I G fs i) {x y : Store Nat × Thread}
    (h : Reach P x y) (hf : x.1.funcs = I.store.funcs) (hc : InvA I G fs i (x.2.config x.1)) :
    (InvA I G fs i (y.2.config y.1) ∨ GuardedA I G fs i (y.2.config y.1)) ∧
      y.1.funcs = I.store.funcs := by
  induction h with
  | refl => exact ⟨.inl hc, hf⟩
  | @tail y' z _ hst ih =>
    obtain ⟨hy | hy, hfy⟩ := ih
    · obtain ⟨f', code', ht, hstep⟩ := hst
      have hf₀ : (y'.2.config y'.1).store.funcs = I.store.funcs := by
        rw [Thread.config_store]; exact hfy
      obtain ⟨hz, hfz⟩ := step_invA hR hstep hf₀ hy
      rw [ht]
      exact ⟨hz, hfz.trans hf₀⟩
    · obtain ⟨E, v, b, d, -, hb, hcode, -⟩ := hy
      have hf₀ : (y'.2.config y'.1).store.funcs = I.store.funcs := by
        rw [Thread.config_store]; exact hfy
      have hd := guardedA_decompose hR hf₀ hb hcode
      rw [Thread.config_store] at hd
      exact absurd hst (calloutAt_no_internal ⟨E, b, hd⟩ _)

/-! ## The transitions -/

/-- The invariant of the hidden states. -/
def HInvA (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) : I.HState → Prop
  | .idle s => StoreIn G s ∧ s.funcs = I.store.funcs
  | .running _ s t => InvA I G fs i (t.config s) ∧ s.funcs = I.store.funcs
  | .waiting _ s t _ => (∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvA I G fs i ((resumeResult s t r).config s)) ∧ s.funcs = I.store.funcs

theorem invA_invoke {s : Store Nat} (hs : StoreIn G s) {a : Nat} (ha : G a) {args : List Val}
    (hargs : ∀ r, Val.ref r ∈ args → RefIn G r) : InvA I G fs i (invoke s a args) := by
  refine ⟨invoke_cfgIn hs ha hargs, chain_of_noBad ?_ _, deepP_flat ?_ ?_⟩
  · intro x hx
    simp only [invoke, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
      exact isBadA_toAdmin v
    · exact isBadA_ref _
    · exact isBadA_callRefType _
  · simp [invoke]
  · simp [invoke]

/-- Resuming an invariant thread at a callout keeps the invariant. -/
theorem resume_invA {s : Store Nat} {t : Thread} (hc : InvA I G fs i (t.config s)) (r : Result)
    (hr : ∀ x ∈ codeRefs r.toAdmin, RefIn G x) : InvA I G fs i ((resumeResult s t r).config s) := by
  rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h, args⟩
  · have ht : resumeResult s t r = t := by unfold resumeResult; simp only [hd]
    rw [ht]; exact hc
  · rw [resumeResult_config hd]
    obtain ⟨_, yy, _, _, _, _, hyy, _, _, hfill⟩ := decompose?_sound hd
    have h₀ : t.config s = ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := by
      rw [← hfill]
      cases t <;> rfl
    have hc' : InvA I G fs i ⟨s, (t.config s).frame,
        E.fill (vals args ++ [.ref (.func a), yy])⟩ := h₀ ▸ hc
    exact invA_fill hc' (pair_host hyy) hr

/-- At a callout of an invariant thread: not the assertion; resuming keeps the invariant. -/
theorem ucall_invA {s' : Store Nat} {t' : Thread} {h : Nat} {args : List Val} {e : I.E.Op}
    (hR : GuardIn I G fs i) (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hy : InvA I G fs i (t'.config s')) (hfy : s'.funcs = I.store.funcs) :
    (∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvA I G fs i ((resumeResult s' t' r).config s')) ∧ (e.1.val = i → assertOk e.2.1) := by
  obtain ⟨a, fi, ha, hf, hcode⟩ := callout_mem callout hy.1
  have hne : h ≠ i := fun hh => hR.avoids a fi ha (hfy ▸ hf) (hh ▸ hcode)
  exact ⟨fun r hr => resume_invA hy r hr, fun he => absurd ((ifaceOp?_fst op).symm.trans he) hne⟩

/-- At a callout of a guarded call: the assertion, with argument `[c]`, `c ≠ 0`. -/
theorem ucall_guardedA {s' : Store Nat} {t' : Thread} {h : Nat} {args : List Val} {e : I.E.Op}
    (hR : GuardIn I G fs i) (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hy : GuardedA I G fs i (t'.config s')) (hfy : s'.funcs = I.store.funcs) :
    (∀ r : Result, (∀ x ∈ codeRefs r.toAdmin, RefIn G x) →
      InvA I G fs i ((resumeResult s' t' r).config s')) ∧ (e.1.val = i → assertOk e.2.1) := by
  obtain ⟨E, v, b, d, hv, hb, hcode, hres⟩ := hy
  have hf₀ : (t'.config s').store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
  have hd : decompose? s' (t'.config s').code = some (E, b, i, [.num ⟨.int .i32, v⟩]) := by
    simpa [Thread.config_store] using guardedA_decompose hR hf₀ hb hcode
  obtain ⟨E₀, a₀, hd₀⟩ := callout
  have heq : (E₀, a₀, h, args) = (E, b, i, [.num ⟨.int .i32, v⟩]) :=
    Option.some.inj (hd₀.symm.trans hd)
  have hargs : args = [.num ⟨.int .i32, v⟩] := by cases heq; rfl
  have hok : assertOk [.num ⟨.int .i32, v⟩] := fun hc => hv (by
    have h₁ : Val.num ⟨.int .i32, v⟩ = Val.i32 0 := Option.some.inj hc
    cases h₁
    rfl)
  refine ⟨fun r hr => ?_, fun _ => (ifaceOp?_snd op).symm ▸ hargs.symm ▸ hok⟩
  rw [resumeResult_config hd]
  simpa [Thread.config_store] using hres r hr

theorem trans_ucallA {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {h : Nat}
    {args : List Val} {e : I.E.Op} (hR : GuardIn I G fs i) (run : Reach P (s, t) (s', t'))
    (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hq : HInvA I G fs i (.running f s t)) :
    HInvA I G fs i (.waiting f s' t' e) ∧ (e.1.val = i → assertOk e.2.1) := by
  obtain ⟨hy | hy, hfy⟩ := reach_invA hR run hq.2 hq.1
  · obtain ⟨h₁, h₂⟩ := ucall_invA hR callout op hy hfy
    exact ⟨⟨h₁, hfy⟩, h₂⟩
  · obtain ⟨h₁, h₂⟩ := ucall_guardedA hR callout op hy hfy
    exact ⟨⟨h₁, hfy⟩, h₂⟩

theorem trans_oretA {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {r : Result}
    (hR : GuardIn I G fs i) (run : Reach P (s, t) (s', t')) (final : ResultAt s' t' r)
    (hq : HInvA I G fs i (.running f s t)) : HInvA I G fs i (.idle s') := by
  obtain ⟨hy | hy, hfy⟩ := reach_invA hR run hq.2 hq.1
  · exact ⟨Thread.config_store s' t' ▸ hy.1.1, hfy⟩
  · obtain ⟨E, v, b, d, -, hb, hcode, -⟩ := hy
    have hf₀ : (t'.config s').store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
    have hd := guardedA_decompose hR hf₀ hb hcode
    rw [final, decompose_toAdmin_none] at hd
    cases hd

/-- **One transition keeps the invariant; questions of the assertion have a true argument.** -/
theorem trans_hInvA {P : Profile} {q q' : I.HState} {m : Move I.E I.F} (h : I.Trans P q m q')
    (hR : GuardIn I G fs i) (hq : HInvA I G fs i q) :
    HInvA I G fs i q' ∧ ∀ e, m = .inl (.ask e) → e.1.val = i → assertOk e.2.1 := by
  cases h with
  | call s f =>
    exact ⟨⟨invA_invoke hq.1 (hR.exports f.1) (typed_refIn f.2.2), hq.2⟩, fun _ he => by cases he⟩
  | ucall run callout op =>
    obtain ⟨hq', hok⟩ := trans_ucallA hR run callout op hq
    exact ⟨hq', fun _ he => by cases he; exact hok⟩
  | uret v => exact ⟨⟨hq.1 _ (answer_refIn v), hq.2⟩, fun _ he => by cases he⟩
  | oret run final answer => exact ⟨trans_oretA hR run final hq, fun _ he => by cases he⟩

theorem path_hInvA {P : Profile} {q q' : I.HState} {p : List (Move I.E I.F)}
    (h : I.Path P q p q') (hR : GuardIn I G fs i) (hq : HInvA I G fs i q) :
    ∀ e, (.inl (.ask e) : Move I.E I.F) ∈ p → e.1.val = i → assertOk e.2.1 := by
  induction h with
  | nil => intro e he; cases he
  | cons ht _ ih =>
    intro e he
    obtain ⟨hq', hm⟩ := trans_hInvA ht hR hq
    rcases List.mem_cons.1 he with he | he
    · exact hm e he.symm
    · exact ih hq' e he

/-- **Every question of the assertion import in every play has a true first argument**
(every profile). -/
theorem strategy_assertOk (hR : GuardIn I G fs i) (P : Profile) {q : List (Move I.E I.F)}
    (hq : q ∈ I.strategy P I.store) :
    ∀ e, (.inl (.ask e) : Move I.E I.F) ∈ q → e.1.val = i → assertOk e.2.1 := by
  obtain ⟨q', hpath⟩ := ScalarInstance.mem_strategy_iff.1 hq
  exact path_hInvA hpath hR ⟨hR.store, rfl⟩

end

/-- **Soundness of the guarded-call analysis for "assert is never called with `false`"**
(every profile). -/
theorem assertNeverFalse_of_guardIn {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat}
    {i : (ifaceOf I).Imp} (hR : GuardIn I G fs i.val) (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I) i := by
  rw [models_iff]
  rintro t ⟨q, hq, rfl⟩ a hc
  obtain ⟨m, hm, hme⟩ := List.mem_map.1 hc
  obtain ⟨e, hei, rfl⟩ := moveEvent_icall hme
  have hea : moveEvent (X := ifaceOf I) (.inl (.ask e)) = Event.icall i a := hme
  have ha : e.2.1 = a := by
    simp only [moveEvent, Sum.map_inl, evOf, Event.icall, Sum.inl.injEq, SideEv.ask.injEq] at hea
    exact hea.2
  exact ha ▸ strategy_assertOk hR P hq e hm (by rw [hei])

end Silmaril.Wasm.Verify
