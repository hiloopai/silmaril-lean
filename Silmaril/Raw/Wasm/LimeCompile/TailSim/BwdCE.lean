module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdFrame

/-!
# The backward simulation of the tail-call rewrite: callee segments

* `frameRedex_ctxt`: a frame whose body's first non-value is a `CALL_REF`, a label or a frame
  steps only inside;
* `call_split_t`: the operands of a target call at a call-redex head are the segment's values;
* `bcem_wrap`: a target step of a callee inside a wrapper is matched as the callee's step;
* `bce_pend`: the target's call inside a pending wrapper, against the source's call redex;
* `bce_vals`: a wrapper holding the callee's values steps `RETURN` out of its labels and frame.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- A head at which a frame steps only inside. -/
def CtxHead (b : Admin) : Prop :=
  b.IsCallRef ∨ (∃ n cont bb, b = .label n cont bb) ∨ ∃ n fi bb, b = .frame n fi bb

theorem CtxHead.val?_eq {b : Admin} (h : CtxHead b) : b.val? = none := by
  rcases h with h | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact Admin.val?_of_isCallRef h
  · rfl
  · rfl

/-- **A frame whose body's active head is a call, a label or a frame steps only inside.** -/
theorem frameRedex_ctxt {t t' : Store H} {g g' fi : Frame} {k : Nat} {B ys' : List Admin}
    (hfr : Closure.FrameRedex P host t g k fi B t' g' ys') {V : List Val} {b : Admin}
    {r : List Admin} (hB : B = vals V ++ b :: r) (hb : CtxHead b) :
    ∃ fi' B₂, Step P host ⟨t, fi, B⟩ ⟨t', fi', B₂⟩ ∧ ys' = [.frame k fi' B₂] := by
  have hbv := hb.val?_eq
  have hnk : ∀ k' : Admin, k' = b → k' ≠ .trap ∧ k' ≠ .plain .return_ ∧ ¬ k'.IsReturnCallRef ∧
      k' ≠ .plain .throwRef := by
    rintro k' rfl
    rcases hb with h | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact ⟨fun h' => by subst h'; exact h, fun h' => by subst h'; exact h,
        fun h' => Admin.IsCallRef.not_isReturnCallRef h h', fun h' => by subst h'; exact h⟩
    all_goals exact ⟨by simp, by simp, by simp [Admin.IsReturnCallRef], by simp⟩
  cases hfr with
  | ctxt hs => exact ⟨_, _, hs, rfl⟩
  | @values _ _ _ vs hn =>
    exfalso
    have hm : b ∈ vals vs := by rw [hB]; simp
    obtain ⟨w, rfl⟩ := PC.mem_vals hm
    simp at hbv
  | @ret _ _ _ vs₁ vs rest hn =>
    exfalso
    have h2 : vals V ++ b :: r = vals (vs₁ ++ vs) ++ Admin.plain .return_ :: rest := by
      rw [← hB]; simp
    exact (hnk b rfl).2.1 (vals_append_cons_inj hbv rfl h2).2.1
  | @callNull _ _ _ vs c rest hc =>
    exfalso
    have h2 : vals V ++ b :: r = vals (vs ++ [.ref .null]) ++ c :: rest := by
      rw [← hB]; simp [vals, Val.toAdmin]
    have := (vals_append_cons_inj hbv (Admin.val?_of_isReturnCallRef hc) h2).2.1
    exact (hnk b rfl).2.2.1 (this ▸ hc)
  | @callAddr _ _ _ vs₁ vs a c rest _ _ _ hc _ _ _ =>
    exfalso
    have h2 : vals V ++ b :: r = vals (vs₁ ++ vs ++ [.ref (.func a)]) ++ c :: rest := by
      rw [← hB]; simp [vals, Val.toAdmin]
    have := (vals_append_cons_inj hbv (Admin.val?_of_isReturnCallRef hc) h2).2.1
    exact (hnk b rfl).2.2.1 (this ▸ hc)
  | @throw _ _ _ a =>
    exfalso
    have h2 : vals V ++ b :: r = vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      rw [← hB]; simp [throwing, vals, Val.toAdmin]
    exact (hnk b rfl).2.2.2 (vals_append_cons_inj hbv rfl h2).2.1
  | trap =>
    exfalso
    have h2 : vals V ++ b :: r = vals [] ++ Admin.trap :: [] := by
      rw [← hB]; simp
    exact (hnk b rfl).1 (vals_append_cons_inj hbv rfl h2).2.1

/-- A step inside a frame shrinks the frame's code when the body's code shrinks. -/
theorem codeSize_fill_lt {X X' : List Admin} (h : codeSize X' < codeSize X) :
    ∀ N : NCtx, codeSize (N.fill X') < codeSize (N.fill X)
  | .hole => h
  | .label V n cont N L => by
    have := LawfulCodeRank.label_lt (vals V) L n cont (codeSize_fill_lt h N)
    simpa [NCtx.fill] using this

/-- **The operands of a target call** at a call-redex head are the segment's values. -/
theorem call_split_t {s t t' : Store H} {f : Frame} {W pre vs ws₁ us₁ : List Val} {a k : Nat}
    {d : DefType} {rest is₂ : List Admin} (har : Arity d k vs) (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest⟩)
    (hV : pre ++ (vs ++ [.ref (.func a)]) = ws₁ ++ us₁)
    {c : Admin} (hch : CallHead host t us₁ c t' is₂) :
    us₁ = vs ++ [.ref (.func a)] ∧ ws₁ = pre := by
  have key : ∀ (vs₂ : List Val) (a₂ : Nat) (gn : FuncInst H) (ps rs : Ty (.list .val)),
      us₁ = vs₂ ++ [.ref (.func a₂)] → t.funcs[a₂]? = some gn → Expand gn.type (.func ps rs) →
      vs₂.length = ps.length → us₁ = vs ++ [.ref (.func a)] ∧ ws₁ = pre := by
    intro vs₂ a₂ gn ps rs hu hg he hn
    subst hu
    have hlast := congrArg List.getLast? hV
    simp at hlast
    subst hlast
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    have hvl : vs.length = vs₂.length := by
      obtain ⟨psd, rsd, hed, hl, -⟩ := callRef_counts (W := W ++ vs) (rest := rest)
        (by simpa using hTs) hf he'
      rw [(har psd rsd hed).2, hl, hn]
    have hV' : pre ++ vs = ws₁ ++ vs₂ := by
      have := hV
      rw [← List.append_assoc, ← List.append_assoc] at this
      exact List.append_inj_left' this rfl
    obtain ⟨rfl, rfl⟩ := List.append_inj' hV'.symm hvl.symm
    exact ⟨rfl, rfl⟩
  rcases CallHead.cases' hch with ⟨rfl, -, -⟩ |
      ⟨vs₂, a₂, gn, ps, rs, code', hu, -, hg, he, hn, -, -⟩ |
      ⟨vs₂, a₂, gn, ps, rs, hh, r, hu, hg, he, hn, -, -, -⟩ |
      ⟨vs₂, a₂, gn, ps, rs, hh, hu, -, hg, he, hn, -, -, -⟩
  · have hlast := congrArg List.getLast? hV
    simp at hlast
  · exact key _ _ _ _ _ hu hg he hn
  · exact key _ _ _ _ _ hu hg he hn
  · exact key _ _ _ _ _ hu hg he hn

theorem codeSize_le_fill (X : List Admin) : ∀ N : NCtx, codeSize X ≤ codeSize (N.fill X)
  | .hole => le_rfl
  | .label V n cont N L => by
    have h1 := codeSize_le_fill X N
    have h2 := LawfulCodeRank.label_body_lt (rank := codeSize) (vals V) L n cont (N.fill X)
    have e : NCtx.fill (.label V n cont N L) X = vals V ++ [.label n cont (N.fill X)] ++ L := by
      simp [NCtx.fill]
    rw [e]; omega

/-- **A step of a callee inside a wrapper** is matched as the callee's step. -/
theorem bcem_wrap {k : Nat} {ys₀ is₀ xs : List Admin} {s t' : Store H} {f fi : Frame}
    (N : NCtx) (pre : List Val) (Y : List Admin) (h : BCEM P host k ys₀ is₀ s f xs t') :
    BCEM P host k [.frame k fi (N.fill (vals pre ++ ys₀ ++ .plain .return_ :: Y))]
      [.frame k fi (N.fill (vals pre ++ is₀ ++ .plain .return_ :: Y))] s f xs t' := by
  obtain ⟨s', xs', hm, hst, hr⟩ := h
  refine ⟨s', xs', ?_, hst, ?_⟩
  · rcases hm with ht | ⟨rfl, rfl, hlt⟩
    · exact .inl ht
    · refine .inr ⟨rfl, rfl, ?_⟩
      have h1 := LawfulCodeRank.context_lt (vals pre) (.plain .return_ :: Y) hlt
      have h2 := codeSize_fill_lt h1 N
      simpa using LawfulCodeRank.frame_lt [] [] k fi h2
  · rcases hr with hce | ⟨rfl, hTA⟩ | ⟨e, rfl, hTT⟩ | ⟨ws, rfl, rfl, hn⟩
    · exact .inl (CE.wrap hce ⟨N, pre, Y, rfl⟩)
    · exact .inr (.inl ⟨rfl, TA.wrap (TA.fill (TA.append (TA.prefix hTA pre) _) N)⟩)
    · exact .inr (.inr (.inl ⟨e, rfl, TT.wrap (TT.fill (TT.append (TT.prefix hTT pre) _) N)⟩))
    · exact .inl (CE.vals hn ⟨N, pre, Y, rfl⟩)

/-- **The target's call inside a pending wrapper**, against the source's call redex. -/
theorem bce_pend (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host)
    {k : Nat} {vs ws : List Val} {a : Nat} {d : DefType} {fi : Frame} {B : List Admin} {c : Admin}
    (har : Arity d k vs) (hpt : PT ws c B) (hsuf : (vs ++ [.ref (.func a)]) <:+ ws)
    (hrt : c.retToCallIn fi.module = .callRefType d)
    {s t t' : Store H} {f g : Frame} {W : List Val} {rest ys' : List Admin}
    (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest⟩)
    (hfr : Closure.FrameRedex P host t g k fi B t' g ys') :
    BCEM P host k [.frame k fi B] ys' s f (vals vs ++ [.ref (.func a), .callRefType d]) t' := by
  obtain ⟨N, c', Y, hcc, rfl⟩ := hpt
  have hc' : c'.IsCallRef := RCRPair.isCallRef hcc
  obtain ⟨V₁, b₁, r₁, hB₁, hb₁⟩ := fill_head N (V := ws) (Y := .plain .return_ :: Y) hc'
  have hctx : CtxHead b₁ := by
    rcases hb₁ with rfl | h
    · exact .inl hc'
    · exact .inr (.inl h)
  obtain ⟨fi', B₂, hs, rfl⟩ := frameRedex_ctxt hfr hB₁ hctx
  obtain ⟨X', hX, rfl⟩ := fill_inv hc' N hs
  rcases Step.split_head (Admin.val?_of_isCallRef hc') hX with ⟨ws₀, us, is', rfl, hs', rfl⟩ |
      ⟨hc₁, -⟩ | ⟨hc₁, -⟩
  rotate_left
  · subst hc₁; exact hc'.elim
  · subst hc₁; exact hc'.elim
  obtain ⟨rfl, ws₂, us₁, is₂, rfl, rfl, hch⟩ := call_inv hc' hs'
  obtain ⟨pre, hpre⟩ := hsuf
  obtain ⟨rfl, rfl⟩ := call_split_t (pre := pre) (ws₁ := ws₀ ++ ws₂) har hst hTs
    (by rw [hpre]; simp) hch
  have htgt : ∀ is₃ : List Admin, N.fill (vals ws₀ ++ (vals ws₂ ++ is₃) ++ .plain .return_ :: Y) =
      N.fill (vals (ws₀ ++ ws₂) ++ is₃ ++ .plain .return_ :: Y) := by intro; simp
  rw [htgt]
  have hsok : StoreOk s := by obtain ⟨_, _, _, hs0, -⟩ := hTs.fragment_ctx; exact hs0
  rcases CallHead.cases' hch with ⟨hu, -, -⟩ |
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
    exact CE.wrap (CE.frame (hbody false _)) ⟨N, ws₀ ++ ws₂, Y, by simp⟩
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
    | values ws' =>
      exact Or.inl (CE.vals (by rw [hv ws' rfl, hk]) ⟨N, ws₀ ++ ws₂, Y, by simp [Result.toAdmin]⟩)
    | trap =>
      have hTA : TA (vals (ws₀ ++ ws₂) ++ Result.trap.toAdmin ++ .plain .return_ :: Y) := by
        simpa [Result.toAdmin] using TA.base (ws₀ ++ ws₂) (.plain .return_ :: Y)
      exact Or.inr (Or.inl ⟨rfl, TA.wrap (TA.fill hTA N)⟩)
    | throw e =>
      have hTT : TT e (vals (ws₀ ++ ws₂) ++ (Result.throw e).toAdmin ++ .plain .return_ :: Y) := by
        simpa [Result.toAdmin] using TT.base (a := e) (ws₀ ++ ws₂) (.plain .return_ :: Y)
      exact Or.inr (Or.inr (Or.inl ⟨e, rfl, TT.wrap (TT.fill hTT N)⟩))
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
    refine ⟨s, _, Or.inl (.single hstep), hst, Or.inl ?_⟩
    refine CE.pend (ws := (ws₀ ++ ws₂) ++ (vs ++ [.ref (.func a)])) har ⟨N, c', Y, hcc, ?_⟩
      (List.suffix_append _ _) hrt
    simp [vals, Val.toAdmin]

/-- **A wrapper holding the callee's values** steps `RETURN` out of its labels, then its frame;
the source waits. -/
theorem bce_vals {k : Nat} {ws : List Val} {fi : Frame} {B : List Admin} (hn : ws.length = k)
    (hpw : PW (vals ws) B) {s t t' : Store H} {f g : Frame} {ys' : List Admin}
    (hst : StoreRel FRel s t) (hfr : Closure.FrameRedex P host t g k fi B t' g ys') :
    BCEM P host k [.frame k fi B] ys' s f (vals ws) t' := by
  obtain ⟨N, pre, Y, rfl⟩ := hpw
  obtain ⟨V₁, b₁, r₁, hB₁, hb₁⟩ := fill_head' N (V := pre ++ ws) (b := .plain .return_) (Y := Y)
  have hB : N.fill (vals pre ++ vals ws ++ .plain .return_ :: Y) = vals V₁ ++ b₁ :: r₁ := by
    rw [← hB₁]; simp
  have hb₁v : b₁.val? = none := by rcases hb₁ with rfl | ⟨_, _, _, rfl⟩ <;> rfl
  have hbad : ∀ (V : List Val) (e : Admin) (r : List Admin), e.val? = none →
      N.fill (vals pre ++ vals ws ++ .plain .return_ :: Y) = vals V ++ e :: r →
      e = .plain .return_ ∨ ∃ n cont bb, e = .label n cont bb := by
    intro V e r he hx
    rw [hB] at hx
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hb₁v he hx
    exact hb₁
  generalize hBB : N.fill (vals pre ++ vals ws ++ .plain .return_ :: Y) = BB at hfr
  cases hfr with
  | ctxt hs =>
    rw [← hBB] at hs
    obtain ⟨rfl, rfl, N', pre', Y', rfl, hlt⟩ := pw_step N hs
    subst hBB
    exact ⟨s, vals ws, Or.inr ⟨rfl, rfl, by simpa using LawfulCodeRank.frame_lt [] [] k _ hlt⟩,
      hst, Or.inl (CE.vals hn ⟨N', pre', Y', rfl⟩)⟩
  | @values _ _ _ vs _ =>
    exfalso
    have hm : b₁ ∈ vals vs := by rw [← hBB, hB]; simp
    obtain ⟨w, rfl⟩ := PC.mem_vals hm
    simp at hb₁v
  | @ret _ _ _ vs' vs rest hn' =>
    cases N with
    | hole =>
      have h2 : vals (pre ++ ws) ++ Admin.plain .return_ :: Y =
          vals (vs' ++ vs) ++ Admin.plain .return_ :: rest := by
        simp only [NCtx.fill] at hBB; simpa using hBB
      obtain ⟨h3, -, -⟩ := vals_append_cons_inj rfl rfl h2
      obtain ⟨rfl, rfl⟩ := List.append_inj' h3 (by omega)
      refine ⟨s, vals ws, Or.inr ⟨rfl, rfl, ?_⟩, hst, Or.inr (Or.inr (Or.inr ⟨ws, rfl, rfl, hn⟩))⟩
      have h1 := Closure.codeSize_le_ctx pre (vals ws) (.plain .return_ :: Y)
      have h4 := Closure.codeSize_frame_lt [] k fi (vals pre ++ vals ws ++ .plain .return_ :: Y) []
      simp only [Sim.vals_nil', List.nil_append, List.append_nil] at h4
      rw [← hBB]
      exact Nat.lt_of_le_of_lt h1 h4
    | label V₀ n cont N' L =>
      exfalso
      have h3 : vals V₀ ++ Admin.label n cont (N'.fill (vals pre ++ vals ws ++ .plain .return_ :: Y))
          :: L = vals (vs' ++ vs) ++ Admin.plain .return_ :: rest := by
        simp only [NCtx.fill] at hBB; rw [hBB]; simp
      obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl h3
      cases h
  | @callNull _ _ _ vs c rest hc =>
    exfalso
    rcases hbad (vs ++ [.ref .null]) c rest (Admin.val?_of_isReturnCallRef hc)
      (by rw [hBB]; simp [vals, Val.toAdmin]) with h | ⟨_, _, _, h⟩
    · subst h; exact hc
    · subst h; exact hc
  | @callAddr _ _ _ vs₁ vs a c rest _ _ _ hc _ _ _ =>
    exfalso
    rcases hbad (vs₁ ++ vs ++ [.ref (.func a)]) c rest (Admin.val?_of_isReturnCallRef hc)
      (by rw [hBB]; simp [vals, Val.toAdmin]) with h | ⟨_, _, _, h⟩
    · subst h; exact hc
    · subst h; exact hc
  | @throw _ _ _ a =>
    exfalso
    rcases hbad [.ref (.exn a)] (.plain .throwRef) [] rfl
      (by rw [hBB]; simp [throwing, vals, Val.toAdmin]) with h | ⟨_, _, _, h⟩ <;> cases h
  | trap =>
    exfalso
    rcases hbad [] .trap [] rfl (by rw [hBB]; simp) with h | ⟨_, _, _, h⟩ <;>
      cases h

end Silmaril.Raw.Wasm.LimeCompile.TailSim
