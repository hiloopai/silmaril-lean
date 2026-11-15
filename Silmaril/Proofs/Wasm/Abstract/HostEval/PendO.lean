module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Reach

/-!
# Pending calls of an invocation, reached in Core (proofs)

`pendO_atCall`, every profile: a pending call of an invocation (`PendO`: reached
in a Wasm callee body, finitely deep) is reached by a Core run, at the call, under
the frames and labels of the callees entered on the way. Each descent is the
`call_ref` step into the Wasm callee (a step independent of the outer frame,
lifted through the context, `ACtx.step_fill`), then the callee body's reach
(`reach_atCall`), lifted through the callee frame and the context
(`ACtx.steps_frame`). From an invocation (`invoke_pendO_atCall`), a pending call of
a host function with no outcome is a reachable blocked configuration, and one the
host may diverge on makes the invocation diverge in Core.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- Evaluation contexts of `AtCall`: values, labels and frames. -/
inductive ACtx where
  | top (ws : List Val) (rest : List Admin)
  | label (ws : List Val) (n : Nat) (cont : List Instr) (E : ACtx) (rest : List Admin)
  | frame (ws : List Val) (n : Nat) (F : Frame) (E : ACtx) (rest : List Admin)

/-- Plugging code into a context. -/
def ACtx.fill : ACtx → List Admin → List Admin
  | .top ws rest, xs => vals ws ++ xs ++ rest
  | .label ws n cont E rest, xs => vals ws ++ .label n cont (E.fill xs) :: rest
  | .frame ws n F E rest, xs => vals ws ++ .frame n F (E.fill xs) :: rest

/-- An `AtCall` configuration is a call in a context. -/
theorem atCall_ctx {s : Store H} {a : Nat} {us : List Val} {c : List Admin}
    (h : AtCall s a us c) :
    ∃ (fi : FuncInst H) (E : ACtx), s.funcs[a]? = some fi ∧
      c = E.fill (vals us ++ [.ref (.func a), .callRefType fi.type]) := by
  induction h with
  | @here ws fi rest hf => exact ⟨fi, .top ws rest, hf, by simp [ACtx.fill]⟩
  | @label ws n cont es rest _ ih =>
    obtain ⟨fi, E, hf, rfl⟩ := ih
    exact ⟨fi, .label ws n cont E rest, hf, rfl⟩
  | @frame ws n F es rest _ ih =>
    obtain ⟨fi, E, hf, rfl⟩ := ih
    exact ⟨fi, .frame ws n F E rest, hf, rfl⟩

/-- A step independent of the frame lifts through a context. -/
theorem ACtx.step_fill (E : ACtx) {s s' : Store H} {xs ys : List Admin}
    (h : ∀ g : Frame, Step P host ⟨s, g, xs⟩ ⟨s', g, ys⟩) (f : Frame) :
    Step P host ⟨s, f, E.fill xs⟩ ⟨s', f, E.fill ys⟩ := by
  induction E generalizing f with
  | top ws rest => exact Silmaril.Wasm.Logic.Core.Step.ctx ws rest (h f)
  | label ws n cont E rest ih =>
    simpa [ACtx.fill] using Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtLabel (ih f))
  | frame ws n F E rest ih =>
    simpa [ACtx.fill] using Silmaril.Wasm.Logic.Core.Step.ctx ws rest
      (Step.ctxtFrame (f := f) (ih F))

/-- A run inside a frame lifts through a context. -/
theorem ACtx.steps_frame (E : ACtx) {s s' : Store H} {F F' : Frame} {n : Nat}
    {b b' : List Admin} (h : Steps P host ⟨s, F, b⟩ ⟨s', F', b'⟩) (f : Frame) :
    Steps P host ⟨s, f, E.fill [.frame n F b]⟩ ⟨s', f, E.fill [.frame n F' b']⟩ := by
  suffices key : ∀ x y, Steps P host x y → ∀ s F b s' F' b', x = ⟨s, F, b⟩ → y = ⟨s', F', b'⟩ →
      Steps P host ⟨s, f, E.fill [.frame n F b]⟩ ⟨s', f, E.fill [.frame n F' b']⟩ from
    key _ _ h _ _ _ _ _ _ rfl rfl
  intro x y hxy
  induction hxy with
  | refl =>
    intro s F b s' F' b' hx hy
    subst hx
    cases hy
    exact .refl
  | @tail y₁ z _ hst ih =>
    intro s F b s' F' b' hx hz
    subst hx hz
    rcases y₁ with ⟨s₁, F₁, b₁⟩
    exact (ih _ _ _ _ _ _ rfl rfl).tail
      (E.step_fill (fun g => Step.ctxtFrame (f := g) hst) f)

/-- A call reached in a callee body is reached in the context of the callee frame. -/
theorem atCall_fill {s : Store H} {a : Nat} {us : List Val} {b : List Admin} {n : Nat}
    {F : Frame} (h : AtCall s a us b) (E : ACtx) :
    AtCall s a us (E.fill [.frame n F [.label n [] b]]) := by
  have h₀ : AtCall s a us [.label n [] b] := by
    have := AtCall.label (ws := []) (n := n) (cont := []) (rest := []) h
    simpa [vals] using this
  induction E with
  | top ws rest =>
    have := AtCall.frame (ws := ws) (n := n) (F := F) (rest := rest) h₀
    simpa [ACtx.fill] using this
  | label ws n' cont E rest ih => exact AtCall.label ih
  | frame ws n' F' E rest ih => exact AtCall.frame ih

/-- **A pending call of a call is reached in Core**, every profile: from a
configuration at the call `x` (under any context), a Core run reaches a
configuration at its pending call `y`. -/
theorem pendO_atCall (hH : Interp.NativeHostSlice host) {x y : (wasmOShape H).self.Op}
    (hp : PendO (hostCall host) x y) :
    CallFacts x → ∀ (f : Frame) (c : List Admin), AtCall x.2.2 x.1 x.2.1 c →
      ∃ (f' : Frame) (c' : List Admin),
        Steps P host ⟨x.2.2, f, c⟩ ⟨y.2.2, f', c'⟩ ∧ AtCall y.2.2 y.1 y.2.1 c' ∧ CallFacts y := by
  -- entering a Wasm callee, then its body's reach
  have enter : ∀ {x z : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func},
      x.2.2.funcs[x.1]? = some fi → fi.code = .wasm fn →
      ReachO (hostCall host) x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body) z →
      CallFacts x → ∀ (f : Frame) (c : List Admin), AtCall x.2.2 x.1 x.2.1 c →
      ∃ (f' : Frame) (c' : List Admin),
        Steps P host ⟨x.2.2, f, c⟩ ⟨z.2.2, f', c'⟩ ∧ AtCall z.2.2 z.1 z.2.1 c' ∧ CallFacts z := by
    intro x z fi fn hf hcode hr hcf f c hat
    obtain ⟨hS, fi', ps, rs, hf', hty, hlen⟩ := hcf
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    obtain ⟨fi'', E, hf'', rfl⟩ := atCall_ctx hat
    rw [hf] at hf''
    obtain rfl := Option.some.inj hf''
    obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
    have hn : x.2.1.length = ps'.length := hlen.trans hpl.symm
    -- the `call_ref` step into the callee
    have hst := E.step_fill (P := P) (host := host)
      (fun g => Step.callRefFunc (f := g) (c := .callRefType fi.type) trivial hf hex hn hcode) f
    -- the callee body, checked
    obtain ⟨ob, hb, -⟩ := Interp.endsAt_eq (hS x.1 fi fn ps rs hf hcode hty)
    have hbc : Interp.chk x.2.2.funcs (Frame.forCall fi.module x.2.1 fn.locals).module
        (Frame.forCall fi.module x.2.1 fn.locals).locals.length rs.length [rs.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [Interp.forCall_length _ _ hlen]; exact hb
    obtain ⟨F', cb, hrb, hatb, hcfz⟩ := reach_atCall (P := P) hH hr hS hbc
    have hrb' : Steps P host ⟨x.2.2, Frame.forCall fi.module x.2.1 fn.locals,
        [.label rs'.length [] (expression fn.body)]⟩ ⟨z.2.2, F', [.label rs'.length [] cb]⟩ := by
      have := Silmaril.Wasm.Logic.Core.Steps.label (P := P) (host := host) rs'.length [] hrb
      simpa [Binaryen.lowerList_liftInstrs, vals] using this
    refine ⟨f, E.fill [.frame rs'.length F' [.label rs'.length [] cb]], ?_, atCall_fill hatb E, hcfz⟩
    exact (Relation.ReflTransGen.single hst).trans (E.steps_frame hrb' f)
  induction hp with
  | body hf hcode hr => exact enter hf hcode hr
  | desc hf hcode hr _ ih =>
    intro hcf f c hat
    obtain ⟨f₁, c₁, h₁, hat₁, hcf₁⟩ := enter hf hcode hr hcf f c hat
    obtain ⟨f₂, c₂, h₂, hat₂, hcf₂⟩ := ih hcf₁ f₁ c₁ hat₁
    exact ⟨f₂, c₂, h₁.trans h₂, hat₂, hcf₂⟩

/-- An invocation is at its call. -/
theorem invoke_atCall {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    (hf : s.funcs[a]? = some fi) : AtCall s a vs (invoke s a vs).code := by
  have := AtCall.here (s := s) (a := a) (us := vs) (ws := []) (rest := []) hf
  simpa [invoke, hf, vals] using this

/-- What is known at an invocation, from a typed invocation of a checked store. -/
theorem callFacts_invoke {s : Store H} {a : Nat} {vs : List Val} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) : CallFacts (H := H) ⟨a, (vs, s)⟩ := by
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  have hty := Interp.funcType_of_expand he
  exact ⟨hS, fi, _, _, hfi, hty, Interp.args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty⟩

/-- **A pending call of an invocation is reached in Core**, every profile. -/
theorem invoke_pendO_atCall (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} {y : (wasmOShape H).self.Op} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hp : PendO (hostCall host) ⟨a, (vs, s)⟩ y) :
    ∃ (f' : Frame) (c : List Admin),
      Steps P host (invoke s a vs) ⟨y.2.2, f', c⟩ ∧ AtCall y.2.2 y.1 y.2.1 c ∧ CallFacts y := by
  obtain ⟨fi, -, -, hfi, -, -⟩ := id hok
  exact pendO_atCall (P := P) hH hp (callFacts_invoke hS hok) {} _ (invoke_atCall hfi)

/-- **A pending host call with no outcome of an invocation is a reachable blocked
configuration**, every profile. -/
theorem invoke_pendO_blocked (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} {y : (wasmOShape H).self.Op} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hp : PendO (hostCall host) ⟨a, (vs, s)⟩ y) {fi : FuncInst H} {hh : H}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .host hh)
    (hno : ∀ o, ¬ host hh y.2.2 y.2.1 o) :
    ∃ c : Config H, Steps P host (invoke s a vs) c ∧ Pending host c.store c.code ∧
      ∀ c', ¬ Step P host c c' := by
  obtain ⟨f', c, hr, hat, -, fi', ps, rs, hf', hty, hlen⟩ := invoke_pendO_atCall (P := P) hH hS hok hp
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  obtain ⟨ps', rs', hex, hpl, -⟩ := Interp.expand_of_funcType hty
  have hpend := atCall_pending hf hcode hex (hlen.trans hpl.symm) hno hat
  exact ⟨⟨y.2.2, f', c⟩, hr, hpend, pending_stuck hpend f'⟩

/-- **A pending host call of an invocation that the host may diverge on makes the
invocation diverge in Core**, every profile. -/
theorem invoke_pendO_diverges (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} {y : (wasmOShape H).self.Op} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hp : PendO (hostCall host) ⟨a, (vs, s)⟩ y) {fi : FuncInst H} {hh : H}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .host hh)
    (hdiv : host hh y.2.2 y.2.1 .diverged) :
    Diverges P host (invoke s a vs) := by
  obtain ⟨f', c, hr, hat, -, fi', ps, rs, hf', hty, hlen⟩ := invoke_pendO_atCall (P := P) hH hS hok hp
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  obtain ⟨ps', rs', hex, hpl, -⟩ := Interp.expand_of_funcType hty
  exact InfiniteTrace.of_steps hr
    (pendingDiv_diverges (f := f') (atCall_pendingDiv hf hcode hex (hlen.trans hpl.symm) hdiv hat))

end Silmaril.Proofs.Wasm.Abstract.HostEval
