module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdStep

/-!
# The backward simulation of the tail-call rewrite: flat heads

The backward cases at a target head that is not a label, handler or callee:

* `bwd_same`: an identical instruction (the same step on the source's store; a discard on the
  target around a trap or throw, while the source stutters);
* `bwd_instr`: the head of a rewritten instruction: the target's `call x` (`call_indirect`) is
  matched by the source's `return_call x` (`return_call_indirect`), and `block`/`loop`/`if` by
  the same rule on the source;
* `bwd_trap`, `bwd_throw`: steps of trap- and throw-active target code (the source stutters).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **An identical head** (target on the left). -/
theorem bwd_same (hhostB : HostRespects (fun g f => FRel f g) host) {tl : Bool}
    {s t t' : Store H} {f f' : Frame} {V : List Val} {b : Admin} {rest' x y' : List Admin}
    (hst : StoreRel FRel s t) (hc : ¬ b.IsCtx) (hr : R false tl x rest') (hb : b.val? = none)
    (h : Step P host ⟨t, f, vals V ++ b :: rest'⟩ ⟨t', f', y'⟩) :
    BM P host tl t' f' y' s f (vals V ++ b :: x) (codeSize (vals V ++ b :: rest')) := by
  rcases Step.split_head hb h with ⟨ws, us, is', rfl, hs, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, e, r, r', rfl, rfl, hne, rfl⟩
  · by_cases hcall : b.IsCallRef
    · obtain ⟨hff, ws₂, us₁, is₂, rfl, rfl, hch⟩ := call_inv hcall hs
      subst f'
      obtain ⟨s', is'', hch', hst', hres⟩ := CallHead.match_back hhostB hst hch
      have hstep : Step P host ⟨s, f, vals (ws ++ (ws₂ ++ us₁)) ++ b :: x⟩
          ⟨s', f, vals (ws ++ ws₂) ++ is'' ++ x⟩ := by
        have := step_mid (hch'.step (P := P) hcall f) (ws ++ ws₂) x
        simpa using this
      refine BM.of_trans (.single hstep) hst' ?_
      have hR : R false tl (is'' ++ x) (is₂ ++ rest') := by
        rcases hres with rfl | ⟨n, fc, b₁, b₁', rfl, rfl, hb₁⟩
        · exact R.append hr (R.refl false tl _)
        · exact R.callee (CE.frame (hb₁ false)) hr
      simpa using R.valPre hR (ws ++ ws₂)
    · obtain ⟨s', hs', hst'⟩ := Step.transport_storeRel hst.symm hc hcall hs
      have hstep : Step P host ⟨s, f, vals (ws ++ us) ++ b :: x⟩ ⟨s', f', vals ws ++ is' ++ x⟩ := by
        have := step_mid hs' ws x
        simpa using this
      refine BM.of_trans (.single hstep) hst'.symm ?_
      simpa using R.valPre (R.append hr (R.refl false tl is')) ws
  · refine BM.of_stutter ?_ hst (R.trapC (ws ++ us) x (by simpa using TA.base ws r'))
    have := codeSize_discard_lt ws us [.trap] r r' hne
    simpa using this
  · refine BM.of_stutter ?_ hst ?_
    · have := codeSize_discard_lt ws us (throwing e) r r' hne
      simpa [throwing, Val.toAdmin] using this
    · have := R.throwC (fw := false) (tl := tl) (ws ++ us) x (TT.base (a := e) ws r')
      simpa [throwing, Val.toAdmin] using this

/-- The source's control head for the target's control head of a rewritten instruction. -/
theorem bwd_ctl {s t : Store H} {f : Frame} {us₁ : List Val} {i : Instr}
    {is₂ : List Admin} (hst : StoreRel FRel s t)
    (hi : (∃ x, i = .returnCall x) ∨ (∃ x y, i = .returnCallIndirect x y) ∨
      (∃ bt b, i = .block bt b) ∨ (∃ bt b, i = .loop bt b) ∨ (∃ bt b₁ b₂, i = .if_ bt b₁ b₂))
    {j : Instr} (hj : (tailI i).head? = some j) (hh : CtlHead t f us₁ j is₂)
    {rest x : List Admin} (hr : R false true x rest) :
    ∃ is'', Step P host ⟨s, f, vals us₁ ++ [.plain i]⟩ ⟨s, f, is''⟩ ∧
      R false true (is'' ++ x) (is₂ ++ ((tailI i).tail.map .plain ++ rest)) := by
  rcases hi with ⟨x', rfl⟩ | ⟨x', y', rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩
  · rw [tailI_returnCall] at hj ⊢
    simp only [List.head?_cons, Option.some.injEq] at hj
    subst hj
    cases hh with
    | @call _ a gn hx hg =>
      obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst.symm.funcs hg
      have hfg' : FRel fn gn := hfg
      refine ⟨[.ref (.func a), .returnCallRefType fn.type], CtlHead.step (.returnCall hx hf), ?_⟩
      rw [hfg'.1]
      exact .same (by simp [Admin.IsCtx]) (.rcr rfl hr)
  · rw [tailI_returnCallIndirect] at hj ⊢
    simp only [List.head?_cons, Option.some.injEq] at hj
    subst hj
    cases hh with
    | callIndirect =>
      refine ⟨_, CtlHead.step (.returnCallIndirect (x := x') (y := y')), ?_⟩
      exact .same (by simp [Admin.IsCtx]) (.same (by simp [Admin.IsCtx]) (.rcr rfl hr))
  · rw [tailI_block] at hj ⊢
    simp only [List.head?_cons, Option.some.injEq] at hj
    subst hj
    cases hh with
    | @block _ _ _ t₁ t₂ hbt hm =>
      refine ⟨_, CtlHead.step (CtlHead.block (body := b) hbt hm), ?_⟩
      simpa using R.label (Or.inl rfl) (R.valPre (R.expr_tailL false b) us₁) hr
  · rw [tailI_loop] at hj ⊢
    simp only [List.head?_cons, Option.some.injEq] at hj
    subst hj
    cases hh with
    | @loop _ _ _ t₁ t₂ hbt hm =>
      refine ⟨_, CtlHead.step (CtlHead.loop (body := b) hbt hm), ?_⟩
      have := R.label (tl := true) (n := t₁.length) (cont := [.loop bt b])
        (cont' := [.loop bt (tailL b)]) (Or.inr ⟨rfl, by rw [tailL_single, tailI_loop]⟩)
        (R.valPre (R.expr_tailL false b) us₁) hr
      simpa using this
  · rw [tailI_if] at hj ⊢
    simp only [List.head?_cons, Option.some.injEq] at hj
    subst hj
    cases hh with
    | @ifTrue c _ _ _ hc =>
      refine ⟨_, CtlHead.step (CtlHead.ifTrue (b₁ := b₁) (b₂ := b₂) (bt := bt) hc), ?_⟩
      have := R.instr (i := .block bt b₁) hr
      rw [tailI_block] at this
      simpa using this
    | ifFalse =>
      refine ⟨_, CtlHead.step (CtlHead.ifFalse (b₁ := b₁) (b₂ := b₂) (bt := bt)), ?_⟩
      have := R.instr (i := .block bt b₂) hr
      rw [tailI_block] at this
      simpa using this

/-- **The head of a rewritten instruction** on the target. -/
theorem bwd_instr (hhostB : HostRespects (fun g f => FRel f g) host) {s t t' : Store H}
    {f f' : Frame} {V : List Val} {i : Instr} {b : Admin} {rest' x y y' : List Admin}
    (hst : StoreRel FRel s t) (hr : R false true x y) (hb : b.val? = none)
    (heq : (tailI i).map .plain ++ y = b :: rest')
    (h : Step P host ⟨t, f, vals V ++ b :: rest'⟩ ⟨t', f', y'⟩) :
    BM P host true t' f' y' s f (vals V ++ .plain i :: x) (codeSize (vals V ++ b :: rest')) := by
  rcases tailI_cases i with hti | hi
  · rw [hti] at heq
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact bwd_same hhostB hst (by simp [Admin.IsCtx]) hr hb h
  · have hhead : ∃ j, (tailI i).head? = some j ∧ b = .plain j ∧
        rest' = (tailI i).tail.map .plain ++ y := by
      cases hti' : tailI i with
      | nil => exact absurd hti' (tailI_ne_nil i)
      | cons j js =>
        rw [hti'] at heq
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at heq
        exact ⟨j, rfl, heq.1.symm, by rw [← heq.2]; rfl⟩
    obtain ⟨j, hj, rfl, rfl⟩ := hhead
    have hjc : IsCtl j := by
      rcases hi with ⟨x', rfl⟩ | ⟨x', y'', rfl⟩ | ⟨bt, bd, rfl⟩ | ⟨bt, bd, rfl⟩ |
        ⟨bt, b₁, b₂, rfl⟩
      · rw [tailI_returnCall] at hj; simp at hj; subst hj; trivial
      · rw [tailI_returnCallIndirect] at hj; simp at hj; subst hj; trivial
      · rw [tailI_block] at hj; simp at hj; subst hj; trivial
      · rw [tailI_loop] at hj; simp at hj; subst hj; trivial
      · rw [tailI_if] at hj; simp at hj; subst hj; trivial
    rcases Step.split_head hb h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc', -⟩ | ⟨hc', -⟩
    · obtain ⟨rfl, rfl, ws₁, us₁, is₂, rfl, rfl, hh⟩ := ctl_inv hjc hs
      obtain ⟨is'', hstep, hR⟩ := bwd_ctl (P := P) (host := host) hst hi hj hh hr
      refine BM.of_trans (x' := vals (ws ++ ws₁) ++ is'' ++ x) (.single ?_) hst ?_
      · have := step_mid hstep (ws ++ ws₁) x
        simpa using this
      · simpa using R.valPre hR (ws ++ ws₁)
    · cases hc'
    · cases hc'
      exact (hjc : False).elim

/-- **Trap-active target code**: the source stutters. -/
theorem bwd_trap {tl : Bool} {s t t' : Store H} {f f' : Frame} {us : List Val}
    {x y y' : List Admin} (hst : StoreRel FRel s t) (hy : TA y)
    (h : Step P host ⟨t, f, y⟩ ⟨t', f', y'⟩) :
    BM P host tl t' f' y' s f (vals us ++ .trap :: x) (codeSize y) := by
  obtain ⟨rfl, rfl, hy', hlt⟩ := TA.step hy h
  exact BM.of_stutter hlt hst (R.trapC us x hy')

/-- **Throw-active target code**: the source stutters. -/
theorem bwd_throw {tl : Bool} {s t t' : Store H} {f f' : Frame} {us : List Val} {e : Nat}
    {x y y' : List Admin} (hst : StoreRel FRel s t) (hy : TT e y)
    (h : Step P host ⟨t, f, y⟩ ⟨t', f', y'⟩) :
    BM P host tl t' f' y' s f (vals us ++ throwing e ++ x) (codeSize y) := by
  obtain ⟨rfl, rfl, hy', hlt⟩ := TT.step hy h
  exact BM.of_stutter hlt hst (R.throwC us x hy')

end Silmaril.Raw.Wasm.LimeCompile.TailSim
