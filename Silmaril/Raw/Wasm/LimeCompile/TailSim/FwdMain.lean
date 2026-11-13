module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdCE
public import Silmaril.Wasm.Execution.Core.Sim.Behaviour

/-!
# The forward simulation of the tail-call rewrite

* `ce_fwd`: every callee segment (frames, call redexes, pending wrappers, nested wrappers);
* **`fstep`**: the one-step obligation of the forward relation, by strong induction on the size
  of the source's code;
* `fwd_terminal`: a terminal source is matched by a target run to the same result;
* **`fwdSim`**: the forward relation between typed configurations (`FRelCfg`) is a stuttering
  forward simulation of `Step` with itself (`ConfigSim`), with result transport, at every
  profile and every host that respects `FRel` and meets `HostOk`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem FrameRedex.frame_eq {s s' : Store H} {f f' fi : Frame} {n : Nat} {b is₀ : List Admin}
    (h : Closure.FrameRedex P host s f n fi b s' f' is₀) : f' = f := by
  cases h <;> rfl

theorem call_redex_inj {vs vs' : List Val} {a a' : Nat} {d d' : DefType}
    (h : vals vs ++ [Admin.ref (.func a), .callRefType d] =
      vals vs' ++ [Admin.ref (.func a'), .callRefType d']) : vs = vs' ∧ a = a' ∧ d = d' := by
  have h' : vals vs ++ [Admin.ref (.func a), .callRefType d] ++ [] =
      vals vs' ++ [Admin.ref (.func a'), .callRefType d'] ++ [] := by simpa using h
  rw [call_redex_eq, call_redex_eq] at h'
  obtain ⟨h1, h2, -⟩ := vals_append_cons_inj (val?_crt _) (val?_crt _) h'
  obtain ⟨rfl, rfl⟩ := snoc_ref_inj h1
  cases h2
  exact ⟨rfl, rfl, rfl⟩

/-- The arity of a callee segment that is a call redex. -/
theorem CE.arity_call : ∀ {fw : Bool} {k : Nat} {xs ys : List Admin}, CE fw k xs ys →
    ∀ {vs : List Val} {a : Nat} {d : DefType}, xs = vals vs ++ [.ref (.func a), .callRefType d] →
      fw = true → Arity d k vs
  | _, _, _, _, .frame _, vs, a, d, hx, _ => by
    have := congrArg List.getLast? hx
    simp at this
  | _, _, _, _, .call har, vs, a, d, hx, _ => by
    obtain ⟨rfl, rfl, rfl⟩ := call_redex_inj hx
    exact har
  | _, _, _, _, .pend har _ _ _, vs, a, d, hx, _ => by
    obtain ⟨rfl, rfl, rfl⟩ := call_redex_inj hx
    exact har
  | _, _, _, _, .wrap hin _, vs, a, d, hx, hfw => CE.arity_call hin hx hfw
  | _, _, _, _, .vals _ _, _, _, _, _, hfw => by cases hfw

/-- **Every callee segment.** -/
theorem ce_fwd (hhost : HostRespects FRel host) (hok : HostOk host) :
    ∀ {fw : Bool} {k : Nat} {xs ys : List Admin}, CE fw k xs ys → fw = true →
    ∀ {s t s' : Store H} {f g : Frame} {W W' : List Val} {rest rest' xs' : List Admin},
      FIH P host (codeSize xs) → StoreRel FRel s t →
      ContextTyped ⟨s, f, vals W ++ xs ++ rest⟩ → ContextTyped ⟨t, g, vals W' ++ ys ++ rest'⟩ →
      SegRed P host f s xs s' xs' → CEM P host k xs s' xs' t g ys
  | _, _, _, _, .frame hb, hfw, s, t, s', f, g, W, W', rest, rest', xs', ih, hst, hTs, hTt, hred => by
    subst hfw
    generalize hx : [Admin.frame _ _ _] = xs at hred
    cases hred with
    | frame hfr =>
      simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ce_frame hb ih hst hTs hTt hfr
    | call hch =>
      have := congrArg List.getLast? hx
      simp at this
  | _, _, _, _, .call har, _, s, t, s', f, g, W, W', rest, rest', xs', ih, hst, hTs, hTt, hred => by
    generalize hx : vals _ ++ [Admin.ref (.func _), .callRefType _] = xs at hred
    cases hred with
    | frame hfr =>
      have := congrArg List.getLast? hx
      simp at this
    | call hch =>
      obtain ⟨rfl, rfl, rfl⟩ := call_redex_inj hx
      exact ce_call hhost hok har hst hTs hch
  | _, _, _, _, .pend har hpt hsuf hrt, _, s, t, s', f, g, W, W', rest, rest', xs', ih, hst, hTs,
      hTt, hred => by
    generalize hx : vals _ ++ [Admin.ref (.func _), .callRefType _] = xs at hred
    cases hred with
    | frame hfr =>
      have := congrArg List.getLast? hx
      simp at this
    | call hch =>
      obtain ⟨rfl, rfl, rfl⟩ := call_redex_inj hx
      exact ce_pend hhost hok har hpt hsuf hrt hst hTs hch
  | _, k, xs, _, @CE.wrap _ _ _ ys₀ fi B hin hpw, hfw, s, t, s', f, g, W, W', rest, rest', xs', ih,
      hst, hTs, hTt, hred => by
    obtain ⟨N, pre, Y, rfl⟩ := hpw
    have hTt' : ContextTyped ⟨t, fi, vals pre ++ ys₀ ++ (.plain .return_ :: Y)⟩ := by
      have h1 := ContextTyped.frame (by simpa using hTt)
      exact CT_fill N (by simpa using h1)
    obtain ⟨t', ys₀', hm, hst', hcer⟩ := ce_fwd hhost hok hin hfw ih hst hTs hTt' hred
    rcases hcer with hce | ⟨r, rfl, rfl, hr⟩
    · refine ⟨t', [.frame k fi (N.fill (vals pre ++ ys₀' ++ .plain .return_ :: Y))], ?_, hst',
        Or.inl (CE.wrap hce ⟨N, pre, Y, rfl⟩)⟩
      rcases hm with hT | ⟨rfl, rfl, hlt⟩
      · exact Or.inl (trans_frame (fill_trans (trans_mid hT pre (.plain .return_ :: Y)) N))
      · exact Or.inr ⟨rfl, rfl, hlt⟩
    · refine ⟨t', r.toAdmin, Or.inl ?_, hst', Or.inr ⟨r, rfl, rfl, hr⟩⟩
      have hin : Steps P host ⟨t, fi, ys₀⟩ ⟨t', fi, r.toAdmin⟩ := by
        rcases hm with hT | ⟨rfl, rfl, -⟩
        · exact hT.to_reflTransGen
        · exact .refl
      have hin' : Steps P host ⟨t, fi, vals pre ++ ys₀ ++ (Admin.plain .return_ :: Y)⟩
          ⟨t', fi, vals pre ++ r.toAdmin ++ (Admin.plain .return_ :: Y)⟩ :=
        Steps.ctxtInstrs hin
      have hrun : Steps P host
          ⟨t, g, [.frame k fi (N.fill (vals pre ++ ys₀ ++ .plain .return_ :: Y))]⟩
          ⟨t', g, [.frame k fi (N.fill (vals pre ++ r.toAdmin ++ .plain .return_ :: Y))]⟩ :=
        Steps.frame (fill_steps hin' N)
      refine Relation.TransGen.trans_right hrun ?_
      cases r with
      | values ws => exact wrap_ret N pre ws Y (hr ws rfl)
      | trap =>
        have hT : TA [.frame k fi (N.fill (vals pre ++ [Admin.trap] ++ .plain .return_ :: Y))] :=
          TA.wrap (TA.fill (by simpa using TA.base pre (.plain .return_ :: Y)) N)
        exact steps_trans_of_ne (TA.run hT) (by
          intro h; simp only [Config.mk.injEq] at h
          exact toAdmin_ne_frame .trap _ _ _ h.2.2.symm)
      | throw e =>
        have hT : TT e [.frame k fi (N.fill (vals pre ++ throwing e ++ .plain .return_ :: Y))] :=
          TT.wrap (TT.fill (by simpa using TT.base (a := e) pre (.plain .return_ :: Y)) N)
        exact steps_trans_of_ne (TT.run hT) (by
          intro h; simp only [Config.mk.injEq] at h
          exact toAdmin_ne_frame (.throw e) _ _ _ h.2.2.symm)
  | _, _, _, _, .vals _ _, hfw, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases hfw

end Silmaril.Raw.Wasm.LimeCompile.TailSim
