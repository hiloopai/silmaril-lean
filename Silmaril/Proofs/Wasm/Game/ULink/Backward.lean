module

public import Silmaril.Proofs.Wasm.Game.ULink.Forward
public import Silmaril.Proofs.Wasm.Game.ULink.Fill

/-!
# The linked module is simulated by the composite (`≥`)

`BRel y x` relates a state `y` of the linked module to a state `x` of the composite: the
consumer runs the same thread in the stubbed store (`cons`), or the provider runs provider code
`Y` (`ProvCode`) whose context-filled form is the linked thread (`prov`, `provWait`), or a
call is being forwarded (`fwdWait`).

* `back_cons`: a linked step of the consumer's code is a consumer step, or a call of a
  provider function, which is the composite's synchronisation starting the provider
  (`linked_step`, `stub_callout`);
* `back_prov`: a linked step inside the provider code is a provider step (`step_fill_inv`);
  a finished provider first returns to the consumer;
* visible moves: callouts of the consumer are forwarded, callouts of the provider asked, and
  answers returned.

Each linked silent step is at least one composite silent step, so divergence transfers.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Proofs.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.Linking.Split

variable {L : ULink} {P : Profile}

/-- The backward simulation relation. -/
inductive BRel (L : ULink) : L.U.State → RState × L.U.State → Prop where
  | idle : BRel L .idle (.idle, .idle)
  | cons {f : L.U.F.Op} {s : Store Nat} {t : Thread} (hq : L.Layout f.store) (hl : L.Layout s) :
      BRel L (.running f s t) (.idle, .running (L.stubQ f) (L.stubS s) t)
  | prov {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat} {args : List Val}
      {Y : List Admin} (hq : L.Layout f.store) (hl : L.Layout s)
      (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (hp : ProvCode s Y) :
      BRel L (.running f s (.active (t.config σ₀).frame (E.fill Y)))
        (.running ⟨k, σ₀, args⟩ s (.active {} Y), .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩)
  | provWait {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
      {args : List Val} {Y : List Admin} {h' : Nat} {args' : List Val} (hq : L.Layout f.store)
      (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (hp : ProvLive s Y)
      (hco : CalloutAt s (.active {} Y) h' args') :
      BRel L (.waiting f s (.active (t.config σ₀).frame (E.fill Y)) ⟨h', s, args'⟩)
        (.waiting ⟨k, σ₀, args⟩ s (.active {} Y) ⟨h', s, args'⟩,
          .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩)
  | fwdWait {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
      (hq : L.Layout f.store) (hl : L.Layout s) (ht : L.target h = none)
      (hco : CalloutAt (L.stubS s) t h args) :
      BRel L (.waiting f s t ⟨h, s, args⟩)
        (.fwdWait ⟨h, L.stubS s, args⟩, .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩)

/-! ### Provider results return to the consumer -/

/-- A finished provider returns to the consumer: one silent synchronisation. -/
theorem prov_return {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} {r : Result} (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) :
    (Cmp L P).step (.running ⟨k, σ₀, args⟩ s (.active {} r.toAdmin),
        .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩) none
      (.idle, .running (L.stubQ f) (L.stubS s) (.active (t.config σ₀).frame (E.fill r.toAdmin))) := by
  have hres : resumeResult σ₀ t r = .active (t.config σ₀).frame (E.fill r.toAdmin) :=
    resume_active hd r
  rw [← hres]
  exact .sync (Ev.ans (⟨k, σ₀, args⟩ : UCall Nat) ⟨L.stubS s, r⟩) (RTrans.oret rfl)
    (UInstance.Trans.uret ⟨L.stubS s, r⟩)

/-! ### Silent steps -/

/-- The resolver starts a stub call in the real store. -/
theorem rcall {e : UCall Nat} {s : Store Nat} (hus : L.unstubS e.store = s) {a : Nat}
    {fi : FuncInst Nat} {ps rs : Ty (.list .val)} {code : Func} (ht : L.target e.target = some a)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : e.args.length = ps.length) (hc : fi.code = .wasm code) :
    L.RTrans P .idle (some (.inr (.ask e))) (.running e s (.active {} (callCode fi rs code e.args))) := by
  subst hus
  exact .call e ht hf he hn hc

/-- A Wasm function that stubbing changes is a stub. -/
theorem stub_of_ne {s : Store Nat} {a : Nat} {fi : FuncInst Nat} (hf : s.funcs[a]? = some fi)
    (hX : (L.stubS s).funcs[a]? ≠ some fi) : ∃ k c, L.stub a = some (k, c) := by
  cases hs : L.stub a with
  | none => exact (hX (by rw [stubS_get, hf, Option.map_some, stubFI_none hs])).elim
  | some kc => exact ⟨kc.1, kc.2, rfl⟩

/-- **A linked call into the provider is the composite's synchronisation starting it.** -/
theorem back_call {f : L.U.F.Op} {s s' : Store Nat} {t : Thread} {f' : Frame} {code' : List Admin}
    (hq : L.Layout f.store) (hl : L.Layout s)
    (hcall : CallAt (L.stubS s).funcs ⟨s, (t.config s).frame, (t.config s).code⟩ ⟨s', f', code'⟩) :
    ∃ x', Relation.TransGen (Cmp L P).Silent (.idle, .running (L.stubQ f) (L.stubS s) t) x' ∧
      BRel L (.running f s' (.active f' code')) x' := by
  obtain ⟨E, vs, a, cr, fi, ps, rs, cd, hcode, hcr, hf, he, hn, hcd, hX, heq⟩ := hcall
  have heq' : s' = s ∧ f' = (t.config s).frame ∧ code' = E.fill (callCode fi rs cd vs) := by
    simpa only [Config.mk.injEq, callCode] using heq
  obtain ⟨k, c₀, hs⟩ := stub_of_ne hf hX
  have ht : L.target k = some a := (L.target_iff k a).2 ⟨c₀, hs⟩
  have hfσ : (L.stubS s).funcs[a]? = some { fi with code := .host k } := by
    rw [stubS_get, hf, Option.map_some, stubFI_some hs]
  have hcode' : (t.config (L.stubS s)).code = E.fill (vals vs ++ [.ref (.func a), cr]) := by
    rw [config_stub]
    exact hcode
  have hd : decompose? (L.stubS s) (t.config (L.stubS s)).code = some (E, a, k, vs) := by
    rw [hcode']
    exact decompose?_fill E hcr hfσ he hn rfl
  have hsync : (Cmp L P).step (.idle, .running (L.stubQ f) (L.stubS s) t) none
      (.running ⟨k, L.stubS s, vs⟩ s (.active {} (callCode fi rs cd vs)),
        .waiting (L.stubQ f) (L.stubS s) t ⟨k, L.stubS s, vs⟩) :=
    .sync (Ev.ask (⟨k, L.stubS s, vs⟩ : UCall Nat)) (rcall (unstub_stub hl) ht hf he hn hcd)
      (UInstance.Trans.ucall ⟨E, a, hd⟩)
  have hframe : (t.config (L.stubS s)).frame = (t.config s).frame := by rw [config_stub]
  have hR : BRel L (.running f s (.active (t.config (L.stubS s)).frame
      (E.fill (callCode fi rs cd vs)))) _ := .prov hq hl hd (.inl (.inl ⟨_, _, _, rfl⟩))
  refine ⟨_, .single hsync, ?_⟩
  rw [heq'.1, heq'.2.1, heq'.2.2, ← hframe]
  exact hR

/-- **A linked step of the consumer's code.** -/
theorem back_cons {f : L.U.F.Op} {s s' : Store Nat} {t t' : Thread} (hq : L.Layout f.store)
    (hl : L.Layout s) (hi : InternalP P (s, t) (s', t')) :
    ∃ x', Relation.TransGen (Cmp L P).Silent (.idle, .running (L.stubQ f) (L.stubS s) t) x' ∧
      BRel L (.running f s' t') x' := by
  obtain ⟨f', code', rfl, hstep⟩ := hi
  have hstep' : Execution.Core.Step P (fun _ _ _ _ => False)
      ⟨s, (t.config s).frame, (t.config s).code⟩ ⟨s', f', code'⟩ := by
    rw [← Thread.config_eta]
    exact hstep
  have hfun : s'.funcs = s.funcs := (Step.framesLocal hstep').1
  rcases linked_step hstep' with hc | hcall
  · have hi' : InternalP P (L.stubS s, t) (L.stubS s', .active f' code') := by
      refine ⟨f', code', rfl, ?_⟩
      rw [config_stub]
      exact hc
    exact ⟨_, .single (.tau₂ (UInstance.Trans.tau hi')), .cons hq (Layout.of_funcs hl hfun)⟩
  · exact back_call hq hl hcall

/-- **A linked step inside the provider code.** -/
theorem back_prov {f : L.U.F.Op} {σ₀ s s' : Store Nat} {t t' : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} {Y : List Admin} (hq : L.Layout f.store) (hl : L.Layout s)
    (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (hp : ProvCode s Y)
    (hi : InternalP P (s, .active (t.config σ₀).frame (E.fill Y)) (s', t')) :
    ∃ x', Relation.TransGen (Cmp L P).Silent (.running ⟨k, σ₀, args⟩ s (.active {} Y),
        .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩) x' ∧ BRel L (.running f s' t') x' := by
  rcases hp with hlive | ⟨r, rfl⟩
  · obtain ⟨f', code', rfl, hstep⟩ := hi
    obtain ⟨s'', Y', hd', hp', hst⟩ := step_fill_inv E hlive hstep
    obtain ⟨rfl, rfl, rfl⟩ : s' = s'' ∧ f' = (t.config σ₀).frame ∧ code' = E.fill Y' := by
      simpa only [Config.mk.injEq] using hd'
    have hfun : s'.funcs = s.funcs := (Step.framesLocal hst).1
    have hpi : InternalP P (s, .active {} Y) (s', .active {} Y') := ⟨{}, Y', rfl, hst⟩
    exact ⟨_, .single (.tau₁ (RTrans.tau hpi)), .prov hq (Layout.of_funcs hl hfun) hd hp'⟩
  · obtain ⟨x', hx', hR⟩ := back_cons hq hl hi
    exact ⟨x', .head (prov_return hd) hx', hR⟩

/-- **Silent linked steps.** -/
theorem bsim_tau {y y' : L.U.State} {x : (Cmp L P).State} (hR : BRel L y x)
    (hs : (L.U.lts P).step y none y') :
    ∃ x', Relation.TransGen (Cmp L P).Silent x x' ∧ BRel L y' x' := by
  cases hR with
  | idle => cases hs
  | cons hq hl =>
    cases hs with
    | tau hi => exact back_cons hq hl hi
  | prov hq hl hd hp =>
    cases hs with
    | tau hi => exact back_prov hq hl hd hp hi
  | provWait => cases hs
  | fwdWait => cases hs

/-! ### Visible steps -/

/-- Forwarding a call: the reply comes back. -/
theorem cstep_fwdAsk {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hl : L.Layout s) :
    (Cmp L P).step (.fwd ⟨h, L.stubS s, args⟩, .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩)
      (some (.inl (.ask ⟨h, s, args⟩)))
      (.fwdWait ⟨h, L.stubS s, args⟩, .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) := by
  have hq' : L.fwdQ ⟨h, L.stubS s, args⟩ = ⟨h, s, args⟩ := by simp [ULink.fwdQ, unstub_stub hl]
  rw [← hq']
  exact .left _ (RTrans.fwdAsk _)

theorem cstep_fwdAns {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hl : L.Layout s) (ans : UReply) :
    (Cmp L P).step (.fwdWait ⟨h, L.stubS s, args⟩,
        .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩)
      (some (.inl (.ans ⟨h, s, args⟩ ans)))
      (.fwdRet ⟨h, L.stubS s, args⟩ ans, .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) := by
  have hq' : L.fwdQ ⟨h, L.stubS s, args⟩ = ⟨h, s, args⟩ := by simp [ULink.fwdQ, unstub_stub hl]
  rw [← hq']
  exact .left _ (RTrans.fwdAns _ ans)

theorem cstep_fwdRet {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hco : CalloutAt (L.stubS s) t h args) (ht : L.target h = none) (ans : UReply) :
    (Cmp L P).step (.fwdRet ⟨h, L.stubS s, args⟩ ans,
        .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) none
      (.idle, .running (L.stubQ f) (L.stubS ans.store) (resumeResult s t ans.result)) := by
  obtain ⟨E, a, hd⟩ := hco
  rw [← resume_stub hd ht]
  exact .sync (Ev.ans (⟨h, L.stubS s, args⟩ : UCall Nat) ⟨L.stubS ans.store, ans.result⟩)
    (RTrans.fwdRet _ ans) (UInstance.Trans.uret ⟨L.stubS ans.store, ans.result⟩)

/-- A callout of the consumer's code is forwarded. -/
theorem bvis_cons_ucall {f : L.U.F.Op} {s : Store Nat} {t : Thread} (hq : L.Layout f.store)
    (hl : L.Layout s) {h : Nat} {args : List Val} (callout : CalloutAt s t h args) :
    ∃ x', (Cmp L P).Run (.idle, .running (L.stubQ f) (L.stubS s) t)
      [L.stubUp (.inl (.ask ⟨h, s, args⟩))] x' ∧ BRel L (.waiting f s t ⟨h, s, args⟩) x' := by
  obtain ⟨E, a, hd⟩ := callout
  obtain ⟨hd', ht⟩ := decompose_stub_of_real hl hd
  have hcode : (t.config (L.stubS s)).code = (t.config s).code := by rw [config_stub]
  have hco : CalloutAt (L.stubS s) t h args := ⟨E, a, hcode ▸ hd'⟩
  have hsync : (Cmp L P).step (.idle, .running (L.stubQ f) (L.stubS s) t) none
      (.fwd ⟨h, L.stubS s, args⟩, .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) :=
    .sync (Ev.ask (⟨h, L.stubS s, args⟩ : UCall Nat)) (RTrans.fwdCall _ ht)
      (UInstance.Trans.ucall hco)
  exact ⟨_, .tau hsync (.vis (cstep_fwdAsk hl) (.nil _)), .fwdWait hq hl ht hco⟩

theorem bvis_cons {f : L.U.F.Op} {s : Store Nat} {t : Thread} (hq : L.Layout f.store)
    (hl : L.Layout s) {m : Move UImp L.U.F} {y' : L.U.State}
    (hs : (L.U.lts P).step (.running f s t) (some m) y') :
    ∃ x', (Cmp L P).Run (.idle, .running (L.stubQ f) (L.stubS s) t) [L.stubUp m] x' ∧
      BRel L y' x' := by
  have hcode : (t.config (L.stubS s)).code = (t.config s).code := by rw [config_stub]
  cases hs with
  | ucall callout => exact bvis_cons_ucall hq hl callout
  | @oret _ _ _ r final =>
    have final' : ResultAt (L.stubS s) t r := by
      show (t.config (L.stubS s)).code = r.toAdmin
      rw [hcode]
      exact final
    exact ⟨_, .vis (.right _ (UInstance.Trans.oret final')) (.nil _), .idle⟩

theorem topRedex_self {s : Store Nat} {vs : List Val} {a : Nat} {fi : FuncInst Nat}
    {ps rs : Ty (.list .val)} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) :
    topRedex s (vs ++ [Val.ref (.func a)]) [] =
      (hostArity? s a).map fun p => (Ctx.top [] [], a, p.1, vs) := by
  unfold topRedex
  simp only [List.getLast?_concat, List.dropLast_concat]
  cases hh : hostArity? s a with
  | none => rfl
  | some hn' =>
    obtain ⟨h, n⟩ := hn'
    obtain ⟨fi', ps', rs', hf', -, he', rfl⟩ := hostArity?_eq_some hh
    have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    subst hfi
    have hps : ps' = ps := (Ty.func.inj (Expand.func_eq he' he)).1
    subst hps
    rw [← hn]
    simp

theorem provCode_resume_frame {s : Store Nat} {n : Nat} {F : Frame} {B : List Admin} {E' : Ctx}
    {a h : Nat} {args : List Val} (hd : decompose? s [.frame n F B] = some (E', a, h, args))
    (s' : Store Nat) (r : Result) : ProvCode s' (E'.fill r.toAdmin) := by
  have h₁ := decompose_frame_top s [] [] n F B
  simp only [vals, List.map_nil, List.nil_append, List.append_nil] at h₁
  rw [h₁] at hd
  obtain ⟨⟨E₀, a', h', args'⟩, -, hE⟩ := Option.map_eq_some_iff.mp hd
  simp only [Prod.mk.injEq] at hE
  rw [← hE.1]
  exact .inl (.inl ⟨_, _, _, rfl⟩)

theorem provCode_resume_call {s : Store Nat} {vs : List Val} {a₀ : Nat} {c : Admin}
    {fi : FuncInst Nat} {ps rs : Ty (.list .val)} (hc : c.IsCallRef) (hf : s.funcs[a₀]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) {E' : Ctx} {a h : Nat}
    {args : List Val} (hd : decompose? s (vals vs ++ [.ref (.func a₀), c]) = some (E', a, h, args))
    (s' : Store Nat) (r : Result) : ProvCode s' (E'.fill r.toAdmin) := by
  have hsp : splitVals (vals vs ++ [.ref (.func a₀), c]) = (vs ++ [Val.ref (.func a₀)], [c]) := by
    simpa using splitVals_call (pre := vs) (a := a₀) hc []
  rw [decompose?_of_split hsp, decompHead_of_IsCallRef hc, topRedex_self hf he hn] at hd
  obtain ⟨⟨h', n'⟩, -, hE⟩ := Option.map_eq_some_iff.mp hd
  simp only [Prod.mk.injEq] at hE
  rw [← hE.1]
  exact .inr ⟨r, by simp [Ctx.fill]⟩

theorem decompose_null {s : Store Nat} {c : Admin} (hc : c.IsCallRef) :
    decompose? s [.ref .null, c] = none := by
  have hsp : splitVals [.ref .null, c] = ([Val.ref .null], [c]) := by
    simpa [toAdmin_ref] using SingleThreaded.splitVals_vals_cons (vs := [Val.ref .null])
      (Det.IsCallRef.val_none hc) []
  rw [decompose?_of_split hsp, decompHead_of_IsCallRef hc]
  simp [topRedex]

theorem provCode_resume {s : Store Nat} {Y : List Admin} (hp : ProvLive s Y) {E' : Ctx} {a h : Nat}
    {args : List Val} (hd : decompose? s Y = some (E', a, h, args)) (s' : Store Nat) (r : Result) :
    ProvCode s' (E'.fill r.toAdmin) := by
  rcases hp with ⟨n, F, B, rfl⟩ | ⟨vs, a₀, c, fi, ps, rs, rfl, hc, hf, he, hn⟩ | ⟨c, rfl, hc⟩
  · exact provCode_resume_frame hd s' r
  · exact provCode_resume_call hc hf he hn hd s' r
  · rw [decompose_null hc] at hd
    cases hd

theorem bvis_prov {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} {Y : List Admin} (hq : L.Layout f.store) (hl : L.Layout s)
    (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (hp : ProvCode s Y)
    {m : Move UImp L.U.F} {y' : L.U.State}
    (hs : (L.U.lts P).step (.running f s (.active (t.config σ₀).frame (E.fill Y))) (some m) y') :
    ∃ x', (Cmp L P).Run (.running ⟨k, σ₀, args⟩ s (.active {} Y),
        .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩) [L.stubUp m] x' ∧ BRel L y' x' := by
  rcases hp with hlive | ⟨r, rfl⟩
  · cases hs with
    | @ucall _ _ _ h args' callout =>
      obtain ⟨E'', a', hd'⟩ := callout
      have hd'' : decompose? s (E.fill Y) = some (E'', a', h, args') := hd'
      rw [decompose_fill hlive E] at hd''
      obtain ⟨⟨E', a₁, h₁, args₁⟩, hY, heq⟩ := Option.map_eq_some_iff.mp hd''
      obtain ⟨-, rfl, rfl, rfl⟩ : Ctx.comp E E' = E'' ∧ a₁ = a' ∧ h₁ = h ∧ args₁ = args' := by
        simpa [compR] using heq
      have hco : CalloutAt s (.active {} Y) h₁ args₁ := ⟨E', a₁, hY⟩
      exact ⟨_, .vis (.left _ (RTrans.ucall hco)) (.nil _), .provWait hq hd hlive hco⟩
    | @oret _ _ _ r final =>
      exact (fill_ne_result hlive E r final).elim
  · obtain ⟨x', hx', hR⟩ := bvis_cons (P := P) hq hl hs
    exact ⟨x', .tau (prov_return hd) hx', hR⟩

theorem bvis_provWait {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} {Y : List Admin} {h' : Nat} {args' : List Val} (hq : L.Layout f.store)
    (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (hp : ProvLive s Y)
    (hco : CalloutAt s (.active {} Y) h' args') {m : Move UImp L.U.F} {y' : L.U.State}
    (hs : (L.U.lts P).step (.waiting f s (.active (t.config σ₀).frame (E.fill Y)) ⟨h', s, args'⟩)
      (some m) y') (hml : L.MoveLayout m) :
    ∃ x', (Cmp L P).Run (.waiting ⟨k, σ₀, args⟩ s (.active {} Y) ⟨h', s, args'⟩,
        .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩) [L.stubUp m] x' ∧ BRel L y' x' := by
  cases hs with
  | uret ans =>
    obtain ⟨E', a₀, hdY⟩ := hco
    have hdY' : decompose? s Y = some (E', a₀, h', args') := hdY
    have hdL : decompose? s ((Thread.active (t.config σ₀).frame (E.fill Y)).config s).code =
        some (Ctx.comp E E', a₀, h', args') := by
      show decompose? s (E.fill Y) = _
      rw [decompose_fill hp E, hdY']
      rfl
    have hrP : resumeResult s (.active {} Y) ans.result = .active {} (E'.fill ans.result.toAdmin) :=
      resume_active (t := .active {} Y) hdY ans.result
    have hrL : resumeResult s (.active (t.config σ₀).frame (E.fill Y)) ans.result =
        .active (t.config σ₀).frame (E.fill (E'.fill ans.result.toAdmin)) := by
      rw [resume_active hdL, Ctx.comp_fill]
      rfl
    refine ⟨_, .vis (.left _ (RTrans.uret ans)) (.nil _), ?_⟩
    rw [hrP, hrL]
    exact .prov hq hml hd (provCode_resume hp hdY' ans.store ans.result)

theorem bvis_fwdWait {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hq : L.Layout f.store) (hl : L.Layout s) (ht : L.target h = none)
    (hco : CalloutAt (L.stubS s) t h args) {m : Move UImp L.U.F} {y' : L.U.State}
    (hs : (L.U.lts P).step (.waiting f s t ⟨h, s, args⟩) (some m) y') (hml : L.MoveLayout m) :
    ∃ x', (Cmp L P).Run (.fwdWait ⟨h, L.stubS s, args⟩,
        .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) [L.stubUp m] x' ∧ BRel L y' x' := by
  cases hs with
  | uret ans =>
    exact ⟨_, .vis (cstep_fwdAns hl ans) (.tau (cstep_fwdRet hco ht ans) (.nil _)), .cons hq hml⟩

/-- **Visible linked steps, read through `stubUp`.** -/
theorem bsim_vis {y y' : L.U.State} {x : (Cmp L P).State} {m : Move UImp L.U.F}
    (hR : BRel L y x) (hs : (L.U.lts P).step y (some m) y') (hml : L.MoveLayout m) :
    ∃ x', (Cmp L P).Run x [L.stubUp m] x' ∧ BRel L y' x' := by
  cases hR with
  | idle =>
    cases hs with
    | call f => exact ⟨_, .vis (.right _ (UInstance.Trans.call (L.stubQ f))) (.nil _), .cons hml hml⟩
  | cons hq hl => exact bvis_cons hq hl hs
  | prov hq hl hd hp => exact bvis_prov hq hl hd hp hs
  | provWait hq hd hp hco => exact bvis_provWait hq hd hp hco hs hml
  | fwdWait hq hl ht hco => exact bvis_fwdWait hq hl ht hco hs hml

/-! ### Runs and divergence -/

theorem run_of_transGen {x x' : (Cmp L P).State} (h : Relation.TransGen (Cmp L P).Silent x x') :
    (Cmp L P).Run x [] x' := by
  induction h with
  | single h => exact .tau h (.nil _)
  | tail _ h ih => exact ih.append (.tau h (.nil _))

/-- **Linked runs along a play are composite runs along its stubbed form.** -/
theorem run_bsim {y y' : (L.U.lts P).State} {p : List (Move UImp L.U.F)} (h : (L.U.lts P).Run y p y') :
    ∀ x, BRel L y x → L.LayoutPlay p → ∃ x', (Cmp L P).Run x (p.map L.stubUp) x' ∧ BRel L y' x' := by
  induction h with
  | nil y => exact fun x hR _ => ⟨x, .nil _, hR⟩
  | tau hs _ ih =>
    intro x hR hl
    obtain ⟨x₁, hx₁, hR₁⟩ := bsim_tau hR hs
    obtain ⟨x', hr, hR'⟩ := ih x₁ hR₁ hl
    exact ⟨x', (run_of_transGen hx₁).append hr, hR'⟩
  | @vis _ _ _ m p₀ hs _ ih =>
    intro x hR hl
    obtain ⟨x₁, hx₁, hR₁⟩ := bsim_vis hR hs (hl m (List.mem_cons_self ..))
    obtain ⟨x', hr, hR'⟩ := ih x₁ hR₁ (fun m' hm' => hl m' (List.mem_cons_of_mem _ hm'))
    exact ⟨x', hx₁.append hr, hR'⟩

/-- **Linked divergence is composite divergence.** -/
theorem diverges_bsim {y : L.U.State} {x : (Cmp L P).State} (hR : BRel L y x)
    (hd : (L.U.lts P).Diverges y) : (Cmp L P).Diverges x := by
  refine InfiniteTrace.coinduct
    (fun x => ∃ x₁ y, Relation.ReflTransGen (Cmp L P).Silent x x₁ ∧ BRel L y x₁ ∧
      (L.U.lts P).Diverges y) ?_ ⟨x, y, .refl, hR, hd⟩
  rintro x ⟨x₁, y, hxx, hR, hd⟩
  rcases Relation.ReflTransGen.cases_head hxx with rfl | ⟨x', hx', hrest⟩
  · obtain ⟨y₁, hy, hd₁⟩ := hd.unfold
    obtain ⟨x₂, hx₂, hR₂⟩ := bsim_tau hR hy
    obtain ⟨x', hx', hrest⟩ := Relation.TransGen.head'_iff.mp hx₂
    exact ⟨x', hx', x₂, y₁, hrest, hR₂, hd₁⟩
  · exact ⟨x', hx', x₁, y, hrest, hR, hd⟩

/-! ### Positions -/

/-- The stubbed game position. -/
def posUp (L : ULink) : Pos UImp L.U.F → Pos UImp L.U.F
  | .idle => .idle
  | .run f => .run (L.stubQ f)
  | .wait f e => .wait (L.stubQ f) e

theorem path_stubUp {x z : Pos UImp L.U.F} {p : List (Move UImp L.U.F)}
    (h : Silmaril.Games.Path x p z) : Silmaril.Games.Path (posUp L x) (p.map L.stubUp) (posUp L z) := by
  induction h with
  | nil x => exact .nil _
  | cons hs _ ih =>
    refine .cons ?_ ih
    cases hs with
    | ask f => exact .ask _
    | call f e => exact .call _ _
    | reply f e n => exact .reply _ _ _
    | ret f r => exact .ret _ _

/-- **Finite plays: the linked module is contained in the composite.** -/
theorem link_le_comp {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p) (h : p ∈ L.U.strategy P) :
    p.map L.stubUp ∈ L.compStrategy P := by
  obtain ⟨y, hy⟩ := Untyped.mem_strategy_iff.1 h
  obtain ⟨x, hx, -⟩ := run_bsim hy _ .idle hl
  exact (comp_denotes P _).1 ⟨x, hx⟩

/-- **Divergence: the linked module's is contained in the composite's.** -/
theorem link_div_le_comp {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p)
    (h : p ∈ (L.U.dstrategy P).div) : p.map L.stubUp ∈ (L.compDStrategy P).div := by
  obtain ⟨⟨y, hy, hd⟩, q, hq⟩ := h
  obtain ⟨x, hx, hR⟩ := run_bsim hy _ .idle hl
  rw [compD_eq_ofLTS]
  exact DStrategy.mem_div_ofLTS_of_run hx (diverges_bsim hR hd) (path_stubUp (L := L) hq)

/-- **M3 in the untyped game, finite plays, every profile**: for plays whose stores have the
link's layout, the linked module's strategy is the composite of the provider's and the
consumer's, with the store relation applied to the moves. -/
theorem link_eq_comp {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p) :
    p ∈ L.U.strategy P ↔ p.map L.stubUp ∈ L.compStrategy P :=
  ⟨link_le_comp hl, comp_le_link hl⟩

/-- **M3 in the untyped game, divergence, every profile.** -/
theorem link_div_eq_comp {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p) :
    p ∈ (L.U.dstrategy P).div ↔ p.map L.stubUp ∈ (L.compDStrategy P).div :=
  ⟨link_div_le_comp hl, comp_div_le_link hl⟩

end Silmaril.Proofs.Wasm.Game.ULink
