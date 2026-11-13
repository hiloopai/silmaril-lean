module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdLabel
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame

/-!
# The forward simulation of the tail-call rewrite: callee frames

* `SegRed`: a step of a callee segment on its own (a frame redex, or a call);
* `CER k xs ys`: the result of a callee segment of arity `k`: again a callee segment, or the
  same outcome on both sides (values of length `k`, a trap, a throw);
* **`ce_frame`**: a step of a callee frame related to a target frame. Inner steps by the
  induction hypothesis; the frame's exits by the same rule on the target. At
  `return_call_ref-frame-addr` with the same kernel on the target, both sides continue with the
  same call redex, whose annotation has the frame's arity (`frameAddr_arity`); with a pending
  target (`rcr` or `bub`), the source leaves the frame alone and the target stutters: the pair
  becomes `CE.pend`. Here the operand count of the target's `CALL_REF` comes from the target's
  typing (`callRef_operands`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- A step of a callee segment on its own. -/
inductive SegRed (P : Numerics.Profile) (host : HostSemantics H) (f : Frame) :
    Store H → List Admin → Store H → List Admin → Prop where
  | frame {s s' : Store H} {n : Nat} {fc : Frame} {b is₀ : List Admin} :
      Closure.FrameRedex P host s f n fc b s' f is₀ → SegRed P host f s [.frame n fc b] s' is₀
  | call {s s' : Store H} {vs : List Val} {a : Nat} {d : DefType} {is₀ : List Admin} :
      CallHead host s (vs ++ [.ref (.func a)]) (.callRefType d) s' is₀ →
      SegRed P host f s (vals vs ++ [.ref (.func a), .callRefType d]) s' is₀

/-- The result of a callee segment of arity `k`. -/
def CER (k : Nat) (xs ys : List Admin) : Prop :=
  CE true k xs ys ∨ ∃ r : Result, xs = r.toAdmin ∧ ys = r.toAdmin ∧
    ∀ ws, r = .values ws → ws.length = k

/-- The conclusion of a callee step. -/
def CEM (P : Numerics.Profile) (host : HostSemantics H) (k : Nat) (xs : List Admin)
    (s' : Store H) (xs' : List Admin) (t : Store H) (g : Frame) (ys : List Admin) : Prop :=
  ∃ (t' : Store H) (ys' : List Admin), (Relation.TransGen (Step P host) ⟨t, g, ys⟩ ⟨t', g, ys'⟩ ∨
      (t' = t ∧ ys' = ys ∧ codeSize xs' < codeSize xs)) ∧
    StoreRel FRel s' t' ∧ CER k xs' ys'

theorem steps_trans_of_ne {c c' : Config H} (h : Steps P host c c') (hne : c ≠ c') :
    Relation.TransGen (Step P host) c c' := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | ht
  · exact absurd rfl hne
  · exact ht

theorem sizeOf_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (fi : Frame) :
    sizeOf (c.retToCallIn fi.module) < sizeOf c + sizeOf fi := by
  rcases fi with ⟨locals, mi⟩
  cases c with
  | returnCallRefType d => simp [Admin.retToCallIn]
  | plain i =>
    cases i <;> simp [Admin.IsReturnCallRef] at hc
    rename_i y
    simp only [Admin.retToCallIn]
    split
    · rename_i d hd
      have h1 : sizeOf d < sizeOf mi.types := List.sizeOf_lt_of_mem (List.mem_of_getElem? hd)
      rcases mi
      simp_all
      omega
    · simp
  | _ => exact absurd hc (by simp [Admin.IsReturnCallRef])

theorem codeSize_frameAddr' (k : Nat) (fi : Frame) (L : List Admin) (c c' : Admin)
    (pre rest : List Admin) (h0 : sizeOf c' < sizeOf c + sizeOf fi) :
    codeSize (L ++ [c']) < codeSize [.frame k fi (pre ++ (L ++ [c]) ++ rest)] := by
  have hc' : codeSize [c'] < codeSize [c] + sizeOf fi := by
    rw [codeSize_cons, codeSize_cons]; omega
  have hX : codeSize (L ++ [c']) < codeSize (L ++ [c]) + sizeOf fi := by
    have h2 := codeSize_append L [c']
    have h3 := codeSize_append L [c]
    omega
  have hY : codeSize (L ++ [c]) ≤ codeSize (pre ++ (L ++ [c]) ++ rest) := by
    have := codeSize_append (pre ++ (L ++ [c])) rest
    have := codeSize_append pre (L ++ [c])
    have := codeSize_pos pre
    have := codeSize_pos rest
    omega
  have hF : codeSize [Admin.frame k fi (pre ++ (L ++ [c]) ++ rest)] =
      1 + (1 + sizeOf k + sizeOf fi + codeSize (pre ++ (L ++ [c]) ++ rest)) + codeSize [] := by
    rw [codeSize_cons, Closure.sizeOf_frame]
  omega

/-- Leaving a frame with a pending tail call shrinks the source's code. -/
theorem codeSize_frameAddr {k : Nat} {fi : Frame} {vs' vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) :
    codeSize (vals vs ++ [.ref (.func a), c.retToCallIn fi.module]) <
      codeSize [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)] := by
  have := codeSize_frameAddr' k fi (vals vs ++ [.ref (.func a)]) c (c.retToCallIn fi.module)
    (vals vs') rest (sizeOf_retToCallIn hc fi)
  simpa using this

theorem pend_eq (vs' vs : List Val) (a : Nat) (c : Admin) (rest : List Admin) :
    vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
      vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest := by
  simp [vals, Val.toAdmin]

/-- **A step of a callee frame.** -/
theorem ce_frame {k : Nat} {fc : Frame} {b b' : List Admin} (hb : R true true b b')
    {s t s' : Store H} {f g : Frame} {W W' : List Val} {rest rest' xs' : List Admin}
    (ih : FIH P host (codeSize [Admin.frame k fc b])) (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ [.frame k fc b] ++ rest⟩)
    (hTt : ContextTyped ⟨t, g, vals W' ++ [.frame k fc b'] ++ rest'⟩)
    (hfr : Closure.FrameRedex P host s f k fc b s' f xs') :
    CEM P host k [.frame k fc b] s' xs' t g [.frame k fc b'] := by
  cases hfr with
  | ctxt hs =>
    rename_i fc' b₂
    obtain ⟨t', b₂', hm, hst', hR'⟩ := ih (Closure.codeSize_frame_lt [] k fc b [] |>.trans_eq'
      (by simp)) hst hb (ContextTyped.frame hTs) (ContextTyped.frame hTt) hs
    refine ⟨t', [.frame k fc' b₂'], ?_, hst', Or.inl (CE.frame hR')⟩
    rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
    · exact Or.inl (trans_frame hT)
    · exact Or.inr ⟨rfl, rfl, by simpa using LawfulCodeRank.frame_lt [] [] k _ hlt⟩
  | values hn =>
    rename_i vs
    rw [R.vals_inv hb]
    exact ⟨t, vals vs, Or.inl (.single (.frameVals hn)), hst,
      Or.inr ⟨.values vs, rfl, rfl, fun ws h => by cases h; exact hn⟩⟩
  | ret hn =>
    rename_i vs₁ vs rest₁
    obtain ⟨y', rfl, -⟩ := R.kernel_inv (k := .plain .return_) (V := vs₁ ++ vs) (rest := rest₁)
      trivial (by simpa using hb)
    have hstep := Step.returnFrame (P := P) (host := host) (s := t) (f := g) (fi := fc) (n := k)
      (vs' := vs₁) (vs := vs) (rest := y') hn
    exact ⟨t, vals vs, Or.inl (.single (by simpa using hstep)), hst,
      Or.inr ⟨.values vs, rfl, rfl, fun ws h => by cases h; exact hn⟩⟩
  | callNull hc =>
    rename_i vs c rest₁
    have hb₁ : R true true (vals (vs ++ [.ref .null]) ++ c :: rest₁) b' := by
      simpa [vals, Val.toAdmin] using hb
    obtain ⟨V₀, V₁, y₀, hV, rfl, hh⟩ := R.split (Admin.val?_of_isReturnCallRef hc) hb₁
    refine ⟨t, [.trap], Or.inl ?_, hst, Or.inr ⟨.trap, rfl, rfl, fun ws h => by cases h⟩⟩
    have hsame : ∀ y₁, V₁ = [] → y₀ = c :: y₁ → Relation.TransGen (Step P host)
        ⟨t, g, [.frame k fc (vals V₀ ++ y₀)]⟩ ⟨t, g, [.trap]⟩ := by
      intro y₁ hV₁ hy
      subst hV₁ hy
      simp only [List.append_nil] at hV
      subst hV
      have := Step.returnCallRefFrameNull (P := P) (host := host) (s := t) (f := g) (fi := fc)
        (k := k) (vs := vs) (rest := y₁) hc
      exact .single (by simpa [vals, Val.toAdmin] using this)
    cases hh with
    | @same _ _ _ y₁ _ _ => exact hsame y₁ rfl rfl
    | @instr i _ y₁ _ =>
      have hti : tailI i = [i] := by
        cases i <;> simp_all [Admin.IsReturnCallRef, Silmaril.Wasm.LimeCompile.Tail.tailI]
      exact hsame y₁ rfl (by rw [hti]; rfl)
    | @rcr _ c' _ y₁ hcc _ =>
      simp only [List.append_nil] at hV
      subst hV
      have h₁ := step_mid (Step.callRefNull (P := P) (host := host) (s := t) (f := fc)
        (RCRPair.isCallRef hcc)) vs (.plain .return_ :: y₁)
      have h₂ := TA.run (P := P) (host := host) (s := t) (g := fc)
        (TA.base vs (.plain .return_ :: y₁))
      have e1 : vals (vs ++ [.ref .null]) ++ c' :: .plain .return_ :: y₁ =
          vals vs ++ [.ref .null, c'] ++ (.plain .return_ :: y₁) := by simp [vals, Val.toAdmin]
      have e2 : vals vs ++ [.trap] ++ (.plain .return_ :: y₁) =
          vals vs ++ .trap :: .plain .return_ :: y₁ := by simp
      rw [e2] at h₁
      have hin : Relation.TransGen (Step P host)
          ⟨t, fc, vals (vs ++ [.ref .null]) ++ c' :: .plain .return_ :: y₁⟩ ⟨t, fc, [.trap]⟩ := by
        rw [e1]
        exact Relation.TransGen.head' h₁ h₂
      exact (trans_frame (n := k) (f := g) hin).tail .trapFrame
    | @bub ws₀ _ B U X hp =>
      obtain ⟨V₂, n₂, cont₂, N, L₂, c', Y, hcc, rfl⟩ := hp
      have hTin : ContextTyped ⟨t, fc, vals ws₀ ++ c' :: .plain .return_ :: Y⟩ := by
        have h1 := ContextTyped.frame hTt
        have h2 : ContextTyped ⟨t, fc, vals (V₀ ++ V₂) ++
            [.label n₂ cont₂ (N.fill (vals ws₀ ++ c' :: .plain .return_ :: Y))] ++ L₂⟩ := by
          simpa using h1
        exact CT_fill N (ContextTyped.label h2)
      have hone := callRef_operand_one hTin (RCRPair.isCallRef hcc)
      obtain ⟨ws₁, w, rfl⟩ : ∃ ws₁ w, ws₀ = ws₁ ++ [w] := by
        rcases List.eq_nil_or_concat ws₀ with h | ⟨L, w, h⟩
        · subst h; simp at hone
        · exact ⟨L, w, by rw [h, List.concat_eq_append]⟩
      have hw : w = .ref .null := by
        have := congrArg List.getLast? hV
        simp at this; exact this.symm
      subst hw
      have h₁ := step_mid (Step.callRefNull (P := P) (host := host) (s := t) (f := fc)
        (RCRPair.isCallRef hcc)) ws₁ (.plain .return_ :: Y)
      have h₂ := TA.run (P := P) (host := host) (s := t) (g := fc)
        (TA.prefix (TA.label (V₀ ++ V₂) n₂ cont₂ L₂ (TA.fill (TA.base ws₁
          (.plain .return_ :: Y)) N)) [])
      have e1 : vals (ws₁ ++ [.ref .null]) ++ c' :: .plain .return_ :: Y =
          vals ws₁ ++ [.ref .null, c'] ++ (.plain .return_ :: Y) := by simp [vals, Val.toAdmin]
      have e2 : vals ws₁ ++ [.trap] ++ (.plain .return_ :: Y) =
          vals ws₁ ++ .trap :: .plain .return_ :: Y := by simp
      rw [e2] at h₁
      have h₃ := step_mid (Step.ctxtLabel (n := n₂) (cont := cont₂) (fill_step h₁ N)) (V₀ ++ V₂) L₂
      have e3 : ∀ X, vals (V₀ ++ V₂) ++ [Admin.label n₂ cont₂ (N.fill X)] ++ L₂ =
          vals V₀ ++ (vals V₂ ++ .label n₂ cont₂ (N.fill X) :: L₂) := by intro X; simp
      rw [e3, e3] at h₃
      have e4 : vals [] ++ (vals (V₀ ++ V₂) ++ Admin.label n₂ cont₂
          (N.fill (vals ws₁ ++ .trap :: .plain .return_ :: Y)) :: L₂) =
          vals V₀ ++ (vals V₂ ++ .label n₂ cont₂
            (N.fill (vals ws₁ ++ .trap :: .plain .return_ :: Y)) :: L₂) := by simp
      rw [e4] at h₂
      have hin : Relation.TransGen (Step P host)
          ⟨t, fc, vals V₀ ++ (vals V₂ ++ .label n₂ cont₂
            (N.fill (vals (ws₁ ++ [.ref .null]) ++ c' :: .plain .return_ :: Y)) :: L₂)⟩
          ⟨t, fc, [.trap]⟩ := by
        rw [e1]
        exact Relation.TransGen.head' h₃ h₂
      exact (trans_frame (n := k) (f := g) hin).tail .trapFrame
    | label => exact hc.elim
    | handler => exact hc.elim
    | frame => exact hc.elim
    | call => exact hc.elim
    | trap => exact hc.elim
    | throw => exact hc.elim
  | callAddr hc hf he hn =>
    rename_i vs₁ vs a c rest₁ fn ps rs
    obtain ⟨hk, d, hrt, har, ps₀, rs₀, he₀⟩ := frameAddr_arity (V := W) (L := rest)
      (by simpa using hTs) hc hf he hn
    have hb₁ : R true true (vals (vs₁ ++ vs ++ [.ref (.func a)]) ++ c :: rest₁) b' := by
      rw [← pend_eq]; exact hb
    obtain ⟨gn, hg, hfg⟩ := funcRel_get hst hf
    have he' : Expand gn.type (.func ps rs) := by rw [← hfg.1]; exact he
    obtain ⟨V₀, V₁, y₀, hV, rfl, hh⟩ := R.split (Admin.val?_of_isReturnCallRef hc) hb₁
    have hsame : ∀ y₁, V₁ = [] → y₀ = c :: y₁ →
        CEM P host k [.frame k fc (vals vs₁ ++ vals vs ++ [.ref (.func a), c] ++ rest₁)] s
          (vals vs ++ [.ref (.func a), c.retToCallIn fc.module]) t g
          [.frame k fc (vals V₀ ++ y₀)] := by
      intro y₁ hV₁ hy
      subst hV₁ hy
      simp only [List.append_nil] at hV
      subst hV
      have hstep := Step.returnCallRefFrameAddr (P := P) (host := host) (s := t) (f := g)
        (fi := fc) (k := k) (vs' := vs₁) (vs := vs) (rest := y₁) hc hg he' hn
      rw [pend_eq] at hstep
      refine ⟨t, _, Or.inl (.single hstep), hst, Or.inl ?_⟩
      rw [hrt]
      exact CE.call har
    cases hh with
    | @same _ _ _ y₁ _ _ => exact hsame y₁ rfl rfl
    | @instr i _ y₁ _ =>
      have hti : tailI i = [i] := by
        cases i <;> simp_all [Admin.IsReturnCallRef, Silmaril.Wasm.LimeCompile.Tail.tailI]
      exact hsame y₁ rfl (by rw [hti]; rfl)
    | @rcr _ c' _ y₁ hcc _ =>
      simp only [List.append_nil] at hV
      subst hV
      refine ⟨t, _, Or.inr ⟨rfl, rfl, codeSize_frameAddr hc⟩, hst, Or.inl ?_⟩
      rw [hrt]
      exact CE.pend har ⟨.hole, c', y₁, hcc, rfl⟩
        (by simp) hrt
    | @bub ws₀ _ B U X hp =>
      refine ⟨t, _, Or.inr ⟨rfl, rfl, codeSize_frameAddr hc⟩, hst, Or.inl ?_⟩
      rw [hrt]
      have hpt : PT ws₀ c (vals V₀ ++ y₀) := PTL.toPT (PTL.prefix hp V₀)
      refine CE.pend har hpt ?_ hrt
      -- the target's `CALL_REF` has its operands among the innermost values
      obtain ⟨V₂, n₂, cont₂, N, L₂, c', Y, hcc, rfl⟩ := hp
      have hTin : ContextTyped ⟨t, fc, vals ws₀ ++ c' :: .plain .return_ :: Y⟩ := by
        have h1 := ContextTyped.frame hTt
        have h2 : ContextTyped ⟨t, fc, vals (V₀ ++ V₂) ++
            [.label n₂ cont₂ (N.fill (vals ws₀ ++ c' :: .plain .return_ :: Y))] ++ L₂⟩ := by
          simpa using h1
        exact CT_fill N (ContextTyped.label h2)
      have hres : Resolves fc.module c' d := by
        cases c with
        | returnCallRefType d₀ =>
          simp only [Admin.retToCallIn, Admin.callRefType.injEq] at hrt
          subst hrt
          exact .inl hcc
        | plain i =>
          cases i <;> simp [Admin.IsReturnCallRef] at hc
          rename_i y
          simp only [Admin.retToCallIn] at hrt
          split at hrt
          · rename_i d₀ hd₀
            simp only [Admin.callRefType.injEq] at hrt
            subst hrt
            exact .inr ⟨y, hcc, hd₀⟩
          · cases hrt
        | _ => exact hc.elim
      have hops := callRef_operands hTin (RCRPair.isCallRef hcc) hres he₀
      have hlen := (har ps₀ rs₀ he₀).2
      have hs1 : vs ++ [Val.ref (.func a)] <:+ vs₁ ++ vs ++ [.ref (.func a)] := by
        simp
      have hs2 : ws₀ <:+ vs₁ ++ vs ++ [.ref (.func a)] := by
        rw [hV]; simpa using List.suffix_append (V₀ ++ U) ws₀
      exact List.suffix_of_suffix_length_le hs1 hs2 (by simp; omega)
    | label => exact hc.elim
    | handler => exact hc.elim
    | frame => exact hc.elim
    | call => exact hc.elim
    | trap => exact hc.elim
    | throw => exact hc.elim
  | throw =>
    rename_i a
    have hT := R.throw_inv (V := []) (rest := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun := Steps.frame (f := g) (n := k) (TT.run (P := P) (host := host) (s := t) (g := fc) hT)
    refine ⟨t, throwing a, Or.inl (Relation.TransGen.tail' hrun .throwRefFrame), hst,
      Or.inr ⟨.throw a, rfl, rfl, fun ws h => by cases h⟩⟩
  | trap =>
    have hT := R.trap_inv (V := []) (rest := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun := Steps.frame (f := g) (n := k) (TA.run (P := P) (host := host) (s := t) (g := fc) hT)
    refine ⟨t, [.trap], Or.inl (Relation.TransGen.tail' hrun .trapFrame), hst,
      Or.inr ⟨.trap, rfl, rfl, fun ws h => by cases h⟩⟩

end Silmaril.Raw.Wasm.LimeCompile.TailSim
