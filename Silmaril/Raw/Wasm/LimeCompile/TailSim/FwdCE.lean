module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdFrame

/-!
# The forward simulation of the tail-call rewrite: callee segments

* `ce_call`: a call redex related to itself, inside a callee segment of arity `k`: the same call;
  the callee returns `k` values (its type has the counts of the annotation, `callRef_types`, and
  the annotation has arity `k`); a host callee's values have that count (silmaril's `HostOk`);
* `ce_pend`: the source's call after leaving the frame, against the target's pending wrapper:
  the target takes the same call inside its wrapper (`CE.wrap`), or reaches the host's outcome
  and returns it out of the wrapper;
* **`ce_fwd`**: every callee segment, by recursion on the nesting of wrappers.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The values returned by a host callee have the callee's result count. -/
theorem host_values {s s' : Store H} {fi : FuncInst H} {h : H} {vs : List Val}
    {ps rs : Ty (.list .val)} {a : Nat} {r : Result} (hok : HostOk host) (hs : StoreOk s)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (he : Expand fi.type (.func ps rs))
    (hargs : List.Forall₂ (ValOk s) vs ps.toList) (hh : host h s vs (.returned s' r)) :
    ∀ ws, r = .values ws → ws.length = rs.length := by
  intro ws hr
  subst hr
  obtain ⟨-, -, hrt⟩ := (hok s fi h vs ps rs hs (List.mem_of_getElem? hf) hcode he hargs).2 _ hh
  have := hrt.length_eq
  simpa [Ty.length] using this

theorem snoc_ref_inj {vs vs' : List Val} {a a' : Nat}
    (h : vs ++ [Val.ref (.func a)] = vs' ++ [.ref (.func a')]) : vs = vs' ∧ a = a' := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, Val.ref.injEq, Ref.func.injEq, and_true] at h2
  exact ⟨h1, h2⟩

/-- The callee of a typed call redex returns its annotation's count of values. -/
theorem call_counts {s : Store H} {f : Frame} {W vs : List Val} {a k : Nat} {d : DefType}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)} (har : Arity d k vs)
    (hT : ContextTyped ⟨s, f, vals W ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest⟩)
    (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length) :
    List.Forall₂ (ValOk s) vs ps.toList ∧ rs.length = k := by
  obtain ⟨hargs, hd⟩ := callRef_types (W := W) (vs := vs) (c := .callRefType d) (rest := rest)
    (by simpa using hT) trivial hf he hn
  obtain ⟨psd, rsd, hed, -, hl⟩ := hd d rfl
  exact ⟨hargs, by rw [← hl]; exact (har psd rsd hed).1⟩

theorem toAdmin_ne_frame (r : Result) (n : Nat) (fc : Frame) (b : List Admin) :
    r.toAdmin ≠ [.frame n fc b] := by
  intro h
  cases r with
  | values ws =>
    have hm : Admin.frame n fc b ∈ vals ws := by
      simp only [Result.toAdmin] at h; rw [h]; simp
    obtain ⟨w, hw⟩ := PC.mem_vals hm
    rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hw
  | throw e => simp [Result.toAdmin] at h
  | trap => simp [Result.toAdmin] at h

theorem crt_isCallRef (d : DefType) : (Admin.callRefType d).IsCallRef := trivial

/-- **A call redex related to itself.** -/
theorem ce_call (hhost : HostRespects FRel host) (hok : HostOk host) {k : Nat} {vs : List Val}
    {a : Nat} {d : DefType} (har : Arity d k vs) {s t s' : Store H} {f g : Frame}
    {W : List Val} {rest xs' : List Admin} (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest⟩)
    (hch : CallHead host s (vs ++ [.ref (.func a)]) (.callRefType d) s' xs') :
    CEM P host k (vals vs ++ [.ref (.func a), .callRefType d]) s' xs' t g
      (vals vs ++ [.ref (.func a), .callRefType d]) := by
  have hs : StoreOk s := by obtain ⟨_, _, _, hs, -⟩ := hTs.fragment_ctx; exact hs
  obtain ⟨t', is'', hch', hst', hres⟩ := CallHead.match hhost hst hch
  have hstep : Step P host ⟨t, g, vals vs ++ [.ref (.func a), .callRefType d]⟩ ⟨t', g, is''⟩ := by
    rw [← vals_snoc_ref]; exact hch'.step (crt_isCallRef d) g
  generalize hu : vs ++ [Val.ref (.func a)] = us at hch hch'
  cases hch with
  | null =>
    have := congrArg List.getLast? hu
    simp at this
  | @func _ vs₂ a₂ fn ps rs code hf he hn hcode =>
    obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨-, hk⟩ := call_counts har hTs hf he hn
    subst hk
    refine ⟨t', is'', Or.inl (.single hstep), hst', Or.inl ?_⟩
    rcases hres with rfl | ⟨n, fc, b, b', heq, rfl, hb⟩
    · exact CE.frame (R.refl true true _)
    · simp only [List.cons.injEq, Admin.frame.injEq, and_true] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact CE.frame (hb true)
  | @host _ vs₂ a₂ fn ps rs h s'' r hf he hn hcode hh =>
    obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨hargs, hk⟩ := call_counts har hTs hf he hn
    have hv := host_values hok hs hf hcode he hargs hh
    rcases hres with rfl | ⟨n, fc, b, b', heq, -, -⟩
    · exact ⟨t', r.toAdmin, Or.inl (.single hstep), hst',
        Or.inr ⟨r, rfl, rfl, fun ws hw => by rw [hv ws hw, hk]⟩⟩
    · exact absurd heq (toAdmin_ne_frame r n fc b)
  | @div _ vs₂ a₂ fn ps rs h hf he hn hcode hh =>
    obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    rcases hres with rfl | ⟨n, fc, b, b', heq, -, -⟩
    · exact ⟨t', _, Or.inl (.single hstep), hst', Or.inl (CE.call har)⟩
    · have := congrArg List.getLast? heq
      simp at this

/-- **The source's call against the target's pending wrapper.** -/
theorem ce_pend (hhost : HostRespects FRel host) (hok : HostOk host) {k : Nat}
    {vs ws : List Val} {a : Nat} {d : DefType} {fi : Frame} {B : List Admin} {c : Admin}
    (har : Arity d k vs) (hpt : PT ws c B) (hsuf : vs ++ [.ref (.func a)] <:+ ws)
    (hrt : c.retToCallIn fi.module = .callRefType d)
    {s t s' : Store H} {f g : Frame} {W : List Val} {rest xs' : List Admin}
    (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest⟩)
    (hch : CallHead host s (vs ++ [.ref (.func a)]) (.callRefType d) s' xs') :
    CEM P host k (vals vs ++ [.ref (.func a), .callRefType d]) s' xs' t g [.frame k fi B] := by
  have hs : StoreOk s := by obtain ⟨_, _, _, hs, -⟩ := hTs.fragment_ctx; exact hs
  obtain ⟨N, c', Y, hcc, rfl⟩ := hpt
  obtain ⟨ws₁, rfl⟩ := hsuf
  have hc' : c'.IsCallRef := RCRPair.isCallRef hcc
  -- the target's call, lifted into its wrapper
  have lift : ∀ {t' : Store H} {is'' : List Admin},
      Step P host ⟨t, fi, vals (vs ++ [.ref (.func a)]) ++ [c']⟩ ⟨t', fi, is''⟩ →
      Step P host ⟨t, g, [.frame k fi (N.fill (vals (ws₁ ++ (vs ++ [.ref (.func a)])) ++
          c' :: .plain .return_ :: Y))]⟩
        ⟨t', g, [.frame k fi (N.fill (vals ws₁ ++ is'' ++ .plain .return_ :: Y))]⟩ := by
    intro t' is'' hstep
    have h1 := step_mid hstep ws₁ (.plain .return_ :: Y)
    have e : vals ws₁ ++ (vals (vs ++ [.ref (.func a)]) ++ [c']) ++ .plain .return_ :: Y =
        vals (ws₁ ++ (vs ++ [.ref (.func a)])) ++ c' :: .plain .return_ :: Y := by simp
    rw [e] at h1
    exact .ctxtFrame (fill_step h1 N)
  generalize hu : vs ++ [Val.ref (.func a)] = us at hch
  cases hch with
  | null =>
    have := congrArg List.getLast? hu
    simp at this
  | @func _ vs₂ a₂ fn ps rs code hf he hn hcode =>
    obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨-, hk⟩ := call_counts har hTs hf he hn
    obtain ⟨t', is'', hch', hst', hres⟩ := CallHead.match hhost hst
      (CallHead.func (c := c') hf he hn hcode)
    have hstep := lift (hch'.step hc' fi)
    subst hk
    refine ⟨t', _, Or.inl (.single hstep), hst', Or.inl ?_⟩
    rcases hres with rfl | ⟨n, fc, b, b', heq, rfl, hb⟩
    · exact CE.wrap (CE.frame (R.refl true true _)) ⟨N, ws₁, Y, by simp⟩
    · simp only [List.cons.injEq, Admin.frame.injEq, and_true] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact CE.wrap (CE.frame (hb true)) ⟨N, ws₁, Y, by simp⟩
  | @host _ vs₂ a₂ fn ps rs h s'' r hf he hn hcode hh =>
    obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨hargs, hk⟩ := call_counts har hTs hf he hn
    have hv := host_values hok hs hf hcode he hargs hh
    obtain ⟨t', is'', hch', hst', hres⟩ := CallHead.match hhost hst
      (CallHead.host (c := c') hf he hn hcode hh)
    have hstep := lift (hch'.step hc' fi)
    rcases hres with rfl | ⟨n, fc, b, b', heq, -, -⟩
    swap
    · exact absurd heq (toAdmin_ne_frame r n fc b)
    refine ⟨t', r.toAdmin, Or.inl ?_, hst', Or.inr ⟨r, rfl, rfl, fun ws hw => by
      rw [hv ws hw, hk]⟩⟩
    refine Relation.TransGen.head' hstep ?_
    cases r with
    | values ws' =>
      have hk' : ws'.length = k := by rw [hv ws' rfl, hk]
      have := wrap_ret (P := P) (host := host) (s := t') (f := g) (fi := fi) N ws₁ ws' Y hk'
      exact this.to_reflTransGen
    | trap =>
      have hT : TA [.frame k fi (N.fill (vals ws₁ ++ [Admin.trap] ++ .plain .return_ :: Y))] :=
        TA.wrap (TA.fill (by simpa using TA.base ws₁ (.plain .return_ :: Y)) N)
      exact TA.run hT
    | throw e =>
      have hT : TT e [.frame k fi (N.fill (vals ws₁ ++ throwing e ++ .plain .return_ :: Y))] :=
        TT.wrap (TT.fill (by simpa using TT.base (a := e) ws₁ (.plain .return_ :: Y)) N)
      exact TT.run hT
  | @div _ vs₂ a₂ fn ps rs h hf he hn hcode hh =>
    obtain ⟨rfl, rfl⟩ := snoc_ref_inj hu
    obtain ⟨t', is'', hch', hst', hres⟩ := CallHead.match hhost hst
      (CallHead.div (c := c') hf he hn hcode hh)
    have hstep := lift (hch'.step hc' fi)
    rcases hres with rfl | ⟨n, fc, b, b', heq, -, -⟩
    · refine ⟨t', _, Or.inl (.single hstep), hst', Or.inl ?_⟩
      refine CE.pend har ⟨N, c', Y, hcc, ?_⟩ (List.suffix_append ws₁ _) hrt
      simp [Val.toAdmin]
    · have := congrArg List.getLast? heq
      simp at this
      subst this
      exact hc'.elim

end Silmaril.Raw.Wasm.LimeCompile.TailSim
