module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdWrap

/-!
# The backward simulation of the tail-call rewrite: callee frames and call redexes

* `bce_frame`: a target step of a callee frame related to a source frame: a pending body is
  caught up (`ce_frame_pend`); otherwise inner steps by the induction hypothesis, and the
  frame's exits by the same rule on the source after its body reaches the same kernel;
* `bce_call`: a target call of a call redex related to itself: the same call on the source.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A target step of a callee frame.** -/
theorem bce_frame (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host)
    {k : Nat} {fc : Frame} {b b' : List Admin} (hb : R false true b b')
    {s t t' : Store H} {f g : Frame} {W W' : List Val} {rest rest' ys' : List Admin}
    (ih : BIH P host (codeSize [Admin.frame k fc b'])) (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ [.frame k fc b] ++ rest⟩)
    (hTt : ContextTyped ⟨t, g, vals W' ++ [.frame k fc b'] ++ rest'⟩)
    (hfr : Closure.FrameRedex P host t g k fc b' t' g ys') :
    BCEM P host k [.frame k fc b'] ys' s f [.frame k fc b] t' := by
  cases hfr with
  | ctxt hs =>
    rename_i fc' b₂'
    by_cases hp : PendR b b'
    · exact ce_frame_pend hhostB hok hp hst hTs hs
    · obtain ⟨s', b₂, hm, hst', hR'⟩ := ih (Closure.codeSize_frame_lt [] k fc b' [] |>.trans_eq'
        (by simp)) hst hb hp (ContextTyped.frame hTs) (ContextTyped.frame hTt) hs
      refine ⟨s', [.frame k fc' b₂], ?_, hst', Or.inl (CE.frame hR')⟩
      rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
      · exact Or.inl (trans_frame hT)
      · exact Or.inr ⟨rfl, rfl, by simpa using LawfulCodeRank.frame_lt [] [] k _ hlt⟩
  | values hn =>
    rename_i vs
    rw [R.vals_tinv hb]
    exact ⟨s, vals vs, Or.inl (.single (.frameVals hn)), hst, Or.inr (Or.inr (Or.inr
      ⟨vs, rfl, rfl, hn⟩))⟩
  | ret hn =>
    rename_i vs₁ vs rest₁
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := .plain .return_) (V := vs₁ ++ vs) (rest' := rest₁)
      (.inl trivial) (by simpa using hb)
    have hstep := Step.returnFrame (P := P) (host := host) (s := s) (f := f) (fi := fc) (n := k)
      (vs' := vs₁) (vs := vs) (rest := x') hn
    exact ⟨s, vals vs, Or.inl (.single (by simpa using hstep)), hst,
      Or.inr (Or.inr (Or.inr ⟨vs, rfl, rfl, hn⟩))⟩
  | callNull hc =>
    rename_i vs c rest₁
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := c) (V := vs ++ [.ref .null]) (rest' := rest₁)
      (.inr hc) (by simpa [vals, Val.toAdmin] using hb)
    have hstep := Step.returnCallRefFrameNull (P := P) (host := host) (s := s) (f := f) (fi := fc)
      (k := k) (vs := vs) (rest := x') hc
    exact ⟨s, [.trap], Or.inl (.single (by simpa [vals, Val.toAdmin] using hstep)), hst,
      Or.inr (Or.inl ⟨rfl, by simpa [Sim.vals_nil'] using TA.base [] []⟩)⟩
  | callAddr hc hg he hn =>
    rename_i vs₁ vs a c rest₁ gn ps rs
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := c) (V := vs₁ ++ vs ++ [.ref (.func a)])
      (rest' := rest₁) (.inr hc) (by rw [← pend_eq]; exact hb)
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    obtain ⟨hk, d, hrt, har, -⟩ := frameAddr_arity (V := W) (L := rest) (vs' := vs₁) (vs := vs)
      (a := a) (by rw [pend_eq]; simpa using hTs) hc hf he' hn
    have hstep := Step.returnCallRefFrameAddr (P := P) (host := host) (s := s) (f := f)
      (fi := fc) (k := k) (vs' := vs₁) (vs := vs) (rest := x') hc hf he' hn
    rw [pend_eq] at hstep
    refine ⟨s, _, Or.inl (.single hstep), hst, Or.inl ?_⟩
    rw [hrt]
    exact CE.call har
  | throw =>
    rename_i a
    obtain ⟨us, x', rfl⟩ := R.throw_tinv (V := []) (rest' := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun := Steps.frame (f := f) (n := k) (disc_throw (P := P) (host := host) a s fc us x')
    exact ⟨s, throwing a, Or.inl (Relation.TransGen.tail' hrun .throwRefFrame), hst,
      Or.inr (Or.inr (Or.inl ⟨a, rfl, by simpa [Sim.vals_nil'] using TT.base (a := a) [] []⟩))⟩
  | trap =>
    obtain ⟨us, x', rfl⟩ := R.trap_tinv (V := []) (rest' := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun := Steps.frame (f := f) (n := k) (disc_trap (P := P) (host := host) s fc us x')
    exact ⟨s, [.trap], Or.inl (Relation.TransGen.tail' hrun .trapFrame), hst,
      Or.inr (Or.inl ⟨rfl, by simpa [Sim.vals_nil'] using TA.base [] []⟩)⟩

/-- **A target call of a call redex related to itself.** -/
theorem bce_call (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host)
    {k : Nat} {vs : List Val} {a : Nat} {d : DefType} (har : Arity d k vs)
    {s t t' : Store H} {f : Frame} {W : List Val} {rest ys' : List Admin}
    (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest⟩)
    (hch : CallHead host t (vs ++ [.ref (.func a)]) (.callRefType d) t' ys') :
    BCEM P host k (vals vs ++ [.ref (.func a), .callRefType d]) ys' s f
      (vals vs ++ [.ref (.func a), .callRefType d]) t' := by
  have hsok : StoreOk s := by obtain ⟨_, _, _, hs0, -⟩ := hTs.fragment_ctx; exact hs0
  rcases CallHead.cases' hch with ⟨hu, rfl, rfl⟩ |
      ⟨vs₂, a₂, gn, ps, rs, code', hu, rfl, hg, he, hn, hcode, rfl⟩ |
      ⟨vs₂, a₂, gn, ps, rs, hh, r, hu, hg, he, hn, hcode, hho, rfl⟩ |
      ⟨vs₂, a₂, gn, ps, rs, hh, hu, rfl, hg, he, hn, hcode, hho, rfl⟩
  · have := congrArg List.getLast? hu
    simp at this
  · obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    obtain ⟨code, hcode₃, hl, hbody⟩ := FRel.wasm_back hfg' hcode
    obtain ⟨-, hk⟩ := call_counts har hTs hf he' hn
    have hstep : Step P host ⟨s, f, vals vs ++ [.ref (.func a), .callRefType d]⟩
        ⟨s, f, [.frame rs.length (Frame.forCall fn.module vs code.locals)
          [.label rs.length [] (expression code.body)]]⟩ :=
      .callRefFunc (crt_isCallRef d) hf he' hn hcode₃
    refine ⟨s, _, Or.inl (.single hstep), hst, Or.inl ?_⟩
    have hmod : gn.module = fn.module := hfg'.2.1.symm
    rw [hmod, hl]
    subst hk
    exact CE.frame (hbody false _)
  · obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    have hcode₃ := FRel.host_back hfg' hcode
    obtain ⟨hargs, hk⟩ := call_counts har hTs hf he' hn
    obtain ⟨out', hout', hrel⟩ := hhostB _ _ _ _ _ hst.symm hho
    cases out' with
    | diverged => simp [OutcomeRel] at hrel
    | returned s'' r' =>
    simp only [OutcomeRel, Execution.Host.Outcome.Sim_returned_returned, id] at hrel
    obtain ⟨hst'', hrr⟩ := hrel
    subst r'
    have hv := host_values hok hsok hf hcode₃ he' hargs hout'
    have hstep : Step P host ⟨s, f, vals vs ++ [.ref (.func a), .callRefType d]⟩
        ⟨s'', f, r.toAdmin⟩ := .callRefHost (crt_isCallRef d) hf he' hn hcode₃ hout'
    refine ⟨s'', r.toAdmin, Or.inl (.single hstep), hst''.symm, ?_⟩
    cases r with
    | values ws => exact Or.inr (Or.inr (Or.inr ⟨ws, rfl, rfl, by rw [hv ws rfl, hk]⟩))
    | trap =>
      exact Or.inr (Or.inl ⟨rfl, by simpa [Sim.vals_nil', Result.toAdmin] using TA.base [] []⟩)
    | throw e =>
      exact Or.inr (Or.inr (Or.inl ⟨e, rfl, by
        simpa [Sim.vals_nil', Result.toAdmin, throwing] using TT.base (a := e) [] []⟩))
  · obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    have hcode₃ := FRel.host_back hfg' hcode
    obtain ⟨out', hout', hrel⟩ := hhostB _ _ _ _ _ hst.symm hho
    cases out' with
    | returned s'' r' => simp [OutcomeRel] at hrel
    | diverged =>
    have hstep : Step P host ⟨s, f, vals vs ++ [.ref (.func a), .callRefType d]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), .callRefType d]⟩ :=
      .callRefHostDiv (crt_isCallRef d) hf he' hn hcode₃ hout'
    exact ⟨s, _, Or.inl (.single hstep), hst, Or.inl (CE.call har)⟩

end Silmaril.Raw.Wasm.LimeCompile.TailSim
