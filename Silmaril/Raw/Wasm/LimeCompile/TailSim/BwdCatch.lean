module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdPend

/-!
# The backward simulation of the tail-call rewrite: the catch-up of a pending frame

* `TSegRed`, `BCER`, `BCEM`: a step of a target callee segment on its own, the results of a
  callee segment of arity `k` seen backwards, and the matching conclusion;
* **`ce_frame_pend`**: the target's call in a pending frame is matched by the source's whole
  tail call: bubbling out of its labels, `return_call_ref-frame-addr` (or `-frame-null`) and the
  same call. The callee's arity is the frame's by the source's typing (`frameAddr_arity`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- A step of a target callee segment on its own. -/
inductive TSegRed (P : Numerics.Profile) (host : HostSemantics H) (g : Frame) :
    Store H → List Admin → Store H → List Admin → Prop where
  | frame {t t' : Store H} {n : Nat} {fi : Frame} {b is₀ : List Admin} :
      Closure.FrameRedex P host t g n fi b t' g is₀ → TSegRed P host g t [.frame n fi b] t' is₀
  | call {t t' : Store H} {vs : List Val} {a : Nat} {d : DefType} {is₀ : List Admin} :
      CallHead host t (vs ++ [.ref (.func a)]) (.callRefType d) t' is₀ →
      TSegRed P host g t (vals vs ++ [.ref (.func a), .callRefType d]) t' is₀

/-- The results of a callee segment of arity `k`, seen backwards. -/
def BCER (k : Nat) (xs ys : List Admin) : Prop :=
  CE false k xs ys ∨ (xs = [.trap] ∧ TA ys) ∨ (∃ e, xs = throwing e ∧ TT e ys) ∨
    ∃ ws : List Val, xs = vals ws ∧ ys = vals ws ∧ ws.length = k

/-- The backward conclusion of a target callee step. -/
def BCEM (P : Numerics.Profile) (host : HostSemantics H) (k : Nat) (ys ys' : List Admin)
    (s : Store H) (f : Frame) (xs : List Admin) (t' : Store H) : Prop :=
  ∃ (s' : Store H) (xs' : List Admin), (Relation.TransGen (Step P host) ⟨s, f, xs⟩ ⟨s', f, xs'⟩ ∨
      (s' = s ∧ xs' = xs ∧ codeSize ys' < codeSize ys)) ∧
    StoreRel FRel s' t' ∧ BCER k xs' ys'

/-- `return_call_ref` leaves a label with its values. -/
theorem rcr_label {c : Admin} (hc : c.IsReturnCallRef) (s : Store H) (g : Frame) (n : Nat)
    (cont : List Instr) (vs : List Val) (rest : List Admin) :
    Step P host ⟨s, g, [.label n cont (vals vs ++ [c] ++ rest)]⟩ ⟨s, g, vals vs ++ [c]⟩ :=
  .returnCallRefLabel hc

/-- `CallHead` with any `CALL_REF` annotation, for the Wasm and host cases. -/
theorem CallHead.retag_func {s : Store H} {vs : List Val} {a : Nat} {c₂ : Admin}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
    (hcode : fi.code = .wasm code) :
    CallHead host s (vs ++ [.ref (.func a)]) c₂ s
      [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]] :=
  .func hf he hn hcode

/-- The four call head rules, as an explicit disjunction. -/
theorem CallHead.cases' {t t' : Store H} {us : List Val} {c : Admin} {is₂ : List Admin}
    (h : CallHead host t us c t' is₂) :
    (us = [.ref .null] ∧ t' = t ∧ is₂ = [.trap]) ∨
    (∃ (vs : List Val) (a : Nat) (fi : FuncInst H) (ps rs : Ty (.list .val)) (code : Func),
      us = vs ++ [.ref (.func a)] ∧ t' = t ∧ t.funcs[a]? = some fi ∧
      Expand fi.type (.func ps rs) ∧ vs.length = ps.length ∧ fi.code = .wasm code ∧
      is₂ = [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]) ∨
    (∃ (vs : List Val) (a : Nat) (fi : FuncInst H) (ps rs : Ty (.list .val)) (hh : H) (r : Result),
      us = vs ++ [.ref (.func a)] ∧ t.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
      vs.length = ps.length ∧ fi.code = .host hh ∧ host hh t vs (.returned t' r) ∧
      is₂ = r.toAdmin) ∨
    (∃ (vs : List Val) (a : Nat) (fi : FuncInst H) (ps rs : Ty (.list .val)) (hh : H),
      us = vs ++ [.ref (.func a)] ∧ t' = t ∧ t.funcs[a]? = some fi ∧
      Expand fi.type (.func ps rs) ∧ vs.length = ps.length ∧ fi.code = .host hh ∧
      host hh t vs .diverged ∧ is₂ = vals vs ++ [.ref (.func a), c]) := by
  cases h with
  | null => exact .inl ⟨rfl, rfl, rfl⟩
  | func hf he hn hcode => exact .inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, hf, he, hn, hcode, rfl⟩)
  | host hf he hn hcode hh =>
    exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, rfl, hf, he, hn, hcode, hh, rfl⟩))
  | div hf he hn hcode hh =>
    exact .inr (.inr (.inr ⟨_, _, _, _, _, _, rfl, rfl, hf, he, hn, hcode, hh, rfl⟩))

theorem FRel.wasm_back {fn gn : FuncInst H} (h : FRel fn gn) {code' : Func}
    (hc : gn.code = .wasm code') :
    ∃ code, fn.code = .wasm code ∧ code'.locals = code.locals ∧
      ∀ (fw : Bool) (n : Nat), R fw true [.label n [] (expression code.body)]
        [.label n [] (expression code'.body)] := by
  have hcr := h.2.2
  cases hf : fn.code with
  | host h' => rw [hf, hc] at hcr; exact hcr.elim
  | wasm code =>
    obtain ⟨code₂, hc₂, hl, hb⟩ := FRel.wasm h hf
    rw [hc] at hc₂
    cases hc₂
    exact ⟨code, rfl, hl, hb⟩

theorem FRel.host_back {fn gn : FuncInst H} (h : FRel fn gn) {hh : H} (hc : gn.code = .host hh) :
    fn.code = .host hh := by
  have hcr := h.2.2
  rw [hc] at hcr
  cases hf : fn.code with
  | wasm g => rw [hf] at hcr; exact hcr.elim
  | host h' => rw [hf] at hcr; exact congrArg _ hcr

/-- **The catch-up of a pending frame.** -/
theorem ce_frame_pend (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host)
    {k : Nat} {fc : Frame} {b b' : List Admin} (hp : PendR b b')
    {s t t' : Store H} {f fc' : Frame} {W : List Val} {rest b₂' : List Admin}
    (hst : StoreRel FRel s t) (hTs : ContextTyped ⟨s, f, vals W ++ [.frame k fc b] ++ rest⟩)
    (hs : Step P host ⟨t, fc, b'⟩ ⟨t', fc', b₂'⟩) :
    BCEM P host k [.frame k fc b'] [.frame k fc' b₂'] s f [.frame k fc b] t' := by
  obtain ⟨Nt, Ns, V, c, c', X, Y, hcc, rfl, rfl⟩ := PendR.shape hp
  have hc' : c'.IsCallRef := RCRPair.isCallRef hcc
  have hc : c.IsReturnCallRef := RCRPair.isReturnCallRef hcc
  obtain ⟨X', hX, rfl⟩ := fill_inv hc' Nt hs
  rcases Step.split_head (Admin.val?_of_isCallRef hc') hX with ⟨ws, us, is', rfl, hs', rfl⟩ |
      ⟨hc₁, -⟩ | ⟨hc₁, -⟩
  rotate_left
  · subst hc₁; exact hc'.elim
  · subst hc₁; exact hc'.elim
  obtain ⟨hff, ws₂, us₁, is₂, rfl, rfl, hch⟩ := call_inv hc' hs'
  subst fc'
  -- the source bubbles out of its labels
  obtain ⟨W₀, X'', hbub⟩ := bubble (P := P) (host := host) (rcr_label hc) s fc Ns
    (ws ++ (ws₂ ++ us₁)) X
  have hrun : Steps P host ⟨s, f, [.frame k fc (Ns.fill (vals (ws ++ (ws₂ ++ us₁)) ++ c :: X))]⟩
      ⟨s, f, [.frame k fc (vals (W₀ ++ (ws ++ (ws₂ ++ us₁))) ++ c :: X'')]⟩ := Steps.frame hbub
  have hTs' : ContextTyped ⟨s, f, vals W ++ .frame k fc
      (vals (W₀ ++ ws ++ ws₂) ++ vals us₁ ++ [] ++ c :: X'') :: rest⟩ := by
    have h1 := CT_steps hok hTs (Steps.ctxtInstrs (vs := W) (rest := rest) hrun)
    simpa using h1
  -- the target's innermost code after its call
  have htgt : ∀ (is₃ : List Admin), Nt.fill (vals ws ++ (vals ws₂ ++ is₃) ++ .plain .return_ :: Y) =
      Nt.fill (vals (ws ++ ws₂) ++ is₃ ++ .plain .return_ :: Y) := by intro; simp
  rw [htgt]
  rcases CallHead.cases' hch with ⟨rfl, rfl, rfl⟩ |
      ⟨vs, a, gn, ps, rs, code', rfl, rfl, hg, he, hn, hcode, rfl⟩ |
      ⟨vs, a, gn, ps, rs, hh, r, rfl, hg, he, hn, hcode, hho, rfl⟩ |
      ⟨vs, a, gn, ps, rs, hh, rfl, rfl, hg, he, hn, hcode, hho, rfl⟩
  · -- `return_call_ref-frame-null`
    have hstep := Step.returnCallRefFrameNull (P := P) (host := host) (s := s) (f := f) (fi := fc)
      (k := k) (vs := W₀ ++ (ws ++ ws₂)) (rest := X'') hc
    have hstep' : Step P host
        ⟨s, f, [.frame k fc (vals (W₀ ++ (ws ++ (ws₂ ++ [.ref .null]))) ++ c :: X'')]⟩
        ⟨s, f, [.trap]⟩ := by simpa [vals, Val.toAdmin] using hstep
    have hTA : TA (vals (ws ++ ws₂) ++ [Admin.trap] ++ .plain .return_ :: Y) := by
      simpa using TA.base (ws ++ ws₂) (.plain .return_ :: Y)
    exact ⟨s, [.trap], Or.inl (Relation.TransGen.tail' hrun hstep'), hst,
      Or.inr (Or.inl ⟨rfl, TA.wrap (TA.fill hTA Nt)⟩)⟩
  · obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he₃ : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    obtain ⟨code, hcode₃, hl, hbody⟩ := FRel.wasm_back hfg' hcode
    obtain ⟨hk, d, hrt, har, -⟩ := frameAddr_arity (vs' := W₀ ++ ws ++ ws₂) (vs := vs)
      (a := a) (by simpa [vals, Val.toAdmin] using hTs') hc hf he₃ hn
    have hfa := Step.returnCallRefFrameAddr (P := P) (host := host) (s := s) (f := f) (fi := fc)
      (k := k) (vs' := W₀ ++ (ws ++ ws₂)) (vs := vs) (rest := X'') hc hf he₃ hn
    have hfa' : Step P host
        ⟨s, f, [.frame k fc (vals (W₀ ++ (ws ++ (ws₂ ++ (vs ++ [.ref (.func a)])))) ++ c :: X'')]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fc.module]⟩ := by
      simpa [vals, Val.toAdmin] using hfa
    have hcall : Step P host ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fc.module]⟩
        ⟨s, f, [.frame rs.length (Frame.forCall fn.module vs code.locals)
          [.label rs.length [] (expression code.body)]]⟩ := by
      rw [hrt]; exact .callRefFunc (crt_isCallRef d) hf he₃ hn hcode₃
    refine ⟨s, _, Or.inl (Relation.TransGen.tail' (hrun.tail hfa') hcall), hst, Or.inl ?_⟩
    have hmod : gn.module = fn.module := hfg'.2.1.symm
    rw [hmod, hl]
    subst hk
    exact CE.wrap (CE.frame (hbody false _)) ⟨Nt, ws ++ ws₂, Y, by simp⟩
  · obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he₃ : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    have hcode₃ := FRel.host_back hfg' hcode
    obtain ⟨out', hout', hrel⟩ := hhostB _ _ _ _ _ hst.symm hho
    cases out' with
    | diverged => simp [OutcomeRel] at hrel
    | returned s'' r' =>
    simp only [OutcomeRel, Execution.Host.Outcome.Sim_returned_returned, id] at hrel
    obtain ⟨hst'', hrr⟩ := hrel
    subst r'
    have hst' : StoreRel FRel s'' t' := hst''.symm
    obtain ⟨hk, d, hrt, har, -⟩ := frameAddr_arity (vs' := W₀ ++ ws ++ ws₂) (vs := vs)
      (a := a) (by simpa [vals, Val.toAdmin] using hTs') hc hf he₃ hn
    have hfa := Step.returnCallRefFrameAddr (P := P) (host := host) (s := s) (f := f) (fi := fc)
      (k := k) (vs' := W₀ ++ (ws ++ ws₂)) (vs := vs) (rest := X'') hc hf he₃ hn
    have hfa' : Step P host
        ⟨s, f, [.frame k fc (vals (W₀ ++ (ws ++ (ws₂ ++ (vs ++ [.ref (.func a)])))) ++ c :: X'')]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fc.module]⟩ := by
      simpa [vals, Val.toAdmin] using hfa
    have hTcall : ContextTyped ⟨s, f, vals (W ++ vs) ++ [.ref (.func a), .callRefType d] ++ rest⟩ := by
      have h1 := CT_steps hok hTs (Steps.ctxtInstrs (vs := W) (rest := rest)
        (hrun.tail hfa'))
      rw [hrt] at h1
      simpa using h1
    obtain ⟨hargs, -⟩ := callRef_types (c := .callRefType d) hTcall trivial hf he₃ hn
    have hsok : StoreOk s := by obtain ⟨_, _, _, hs0, -⟩ := hTcall.fragment_ctx; exact hs0
    have hv := host_values hok hsok hf hcode₃ he₃ hargs hout'
    have hcall : Step P host ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fc.module]⟩
        ⟨s'', f, r.toAdmin⟩ := by
      rw [hrt]; exact .callRefHost (crt_isCallRef d) hf he₃ hn hcode₃ hout'
    refine ⟨s'', r.toAdmin, Or.inl (Relation.TransGen.tail' (hrun.tail hfa') hcall), hst', ?_⟩
    have hk' : ∀ ws', r = .values ws' → ws'.length = k := fun ws' hw => by rw [hv ws' hw, hk]
    cases r with
    | values ws' =>
      have hpw : PW (vals ws') (Nt.fill (vals (ws ++ ws₂) ++ (Result.values ws').toAdmin ++
          .plain .return_ :: Y)) := ⟨Nt, ws ++ ws₂, Y, by simp [Result.toAdmin]⟩
      exact Or.inl (CE.vals (hk' ws' rfl) hpw)
    | trap =>
      have hTA : TA (vals (ws ++ ws₂) ++ Result.trap.toAdmin ++ .plain .return_ :: Y) := by
        simpa [Result.toAdmin] using TA.base (ws ++ ws₂) (.plain .return_ :: Y)
      exact Or.inr (Or.inl ⟨rfl, TA.wrap (TA.fill hTA Nt)⟩)
    | throw e =>
      have hTT : TT e (vals (ws ++ ws₂) ++ (Result.throw e).toAdmin ++ .plain .return_ :: Y) := by
        simpa [Result.toAdmin] using TT.base (a := e) (ws ++ ws₂) (.plain .return_ :: Y)
      exact Or.inr (Or.inr (Or.inl ⟨e, rfl, TT.wrap (TT.fill hTT Nt)⟩))
  · obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he₃ : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    obtain ⟨hk, d, hrt, har, -⟩ := frameAddr_arity (vs' := W₀ ++ ws ++ ws₂) (vs := vs)
      (a := a) (by simpa [vals, Val.toAdmin] using hTs') hc hf he₃ hn
    have hfa := Step.returnCallRefFrameAddr (P := P) (host := host) (s := s) (f := f) (fi := fc)
      (k := k) (vs' := W₀ ++ (ws ++ ws₂)) (vs := vs) (rest := X'') hc hf he₃ hn
    have hfa' : Step P host
        ⟨s, f, [.frame k fc (vals (W₀ ++ (ws ++ (ws₂ ++ (vs ++ [.ref (.func a)])))) ++ c :: X'')]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fc.module]⟩ := by
      simpa [vals, Val.toAdmin] using hfa
    refine ⟨s, _, Or.inl (Relation.TransGen.tail' hrun hfa'), hst, Or.inl ?_⟩
    rw [hrt]
    refine CE.pend har ⟨Nt, c', Y, hcc, ?_⟩ (List.suffix_append (ws ++ ws₂) _) hrt
    simp [vals, Val.toAdmin]

end Silmaril.Raw.Wasm.LimeCompile.TailSim
