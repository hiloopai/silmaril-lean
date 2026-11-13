module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdBase
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame

/-!
# The forward simulation of the tail-call rewrite: flat heads

The forward cases at a source head that is not a label, handler or callee:

* `fwd_same`: an identical instruction (the same step on the related store, or the same call
  with related callee bodies; a trap or throw discards on the source while the target is
  trap- or throw-active);
* `fwd_instr`: a rewritten instruction: `return_call x` against `call x; return`
  (`return_call_indirect` against `call_indirect; return`) gives the `rcr` pair, and
  `block`/`loop`/`if` take the same rule with rewritten bodies;
* `fwd_stuck`: a `RETURN_CALL_REF` at the head does not step on its own;
* `fwd_trap`, `fwd_throw`: the source discards around its trap or throw.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim
open Silmaril.Proofs.Wasm.LimeCompile.Tail (tailL_nil tailL_cons)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **An identical head.** -/
theorem fwd_same (hhost : HostRespects FRel host) {tl : Bool} {s t s' : Store H} {f f' : Frame}
    {V : List Val} {a : Admin} {rest y x' : List Admin} (hst : StoreRel FRel s t)
    (hc : ¬ a.IsCtx) (hr : R true tl rest y) (ha : a.val? = none)
    (h : Step P host ⟨s, f, vals V ++ a :: rest⟩ ⟨s', f', x'⟩) :
    FM P host tl s' f' x' t f (vals V ++ a :: y) (codeSize (vals V ++ a :: rest)) := by
  rcases Step.split_head ha h with ⟨ws, us, is', rfl, hs, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, x, r, r', rfl, rfl, hne, rfl⟩
  · by_cases hcall : a.IsCallRef
    · obtain ⟨hff, ws₂, us₁, is₂, rfl, rfl, hch⟩ := call_inv hcall hs
      subst f'
      obtain ⟨t', is'', hch', hst', hres⟩ := CallHead.match hhost hst hch
      have hstep : Step P host ⟨t, f, vals (ws ++ (ws₂ ++ us₁)) ++ a :: y⟩
          ⟨t', f, vals (ws ++ ws₂) ++ is'' ++ y⟩ := by
        have := step_mid (hch'.step (P := P) hcall f) (ws ++ ws₂) y
        simpa using this
      refine FM.of_trans (.single hstep) hst' ?_
      have hR : R true tl (is₂ ++ rest) (is'' ++ y) := by
        rcases hres with rfl | ⟨n, fc, b, b', rfl, rfl, hb⟩
        · exact R.append hr (R.refl true tl _)
        · exact R.callee (CE.frame (hb true)) hr
      simpa using R.valPre hR (ws ++ ws₂)
    · obtain ⟨t', hs', hst'⟩ := Step.transport_storeRel hst hc hcall hs
      have hstep : Step P host ⟨t, f, vals (ws ++ us) ++ a :: y⟩ ⟨t', f', vals ws ++ is' ++ y⟩ := by
        have := step_mid hs' ws y
        simpa using this
      exact FM.of_trans (.single hstep) hst' (by simpa using R.valPre (R.append hr (R.refl true tl is')) ws)
  · refine FM.of_stutter ?_ hst (by simpa using R.trapC (fw := true) (tl := tl) ws r' (TA.base (ws ++ us) y))
    have := codeSize_discard_lt ws us [.trap] r r' hne
    simpa using this
  · refine FM.of_stutter ?_ hst (R.throwC ws r' ?_)
    · have := codeSize_discard_lt ws us (throwing x) r r' hne
      simpa [throwing, Val.toAdmin] using this
    · have := TT.base (a := x) (ws ++ us) y
      simpa [throwing, Val.toAdmin] using this

/-- The rewritten instructions; every other instruction is unchanged by `tailI`. -/
theorem tailI_cases (i : Instr) :
    tailI i = [i] ∨ (∃ x, i = .returnCall x) ∨ (∃ x y, i = .returnCallIndirect x y) ∨
      (∃ bt b, i = .block bt b) ∨ (∃ bt b, i = .loop bt b) ∨ (∃ bt b₁ b₂, i = .if_ bt b₁ b₂) := by
  cases i <;> first
    | exact .inr (.inl ⟨_, rfl⟩)
    | exact .inr (.inr (.inl ⟨_, _, rfl⟩))
    | exact .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    | exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩))))
    | exact .inr (.inr (.inr (.inr (.inr ⟨_, _, _, rfl⟩))))
    | (left; simp [Silmaril.Wasm.LimeCompile.Tail.tailI])

theorem tailI_returnCall (x : FuncIdx) : tailI (.returnCall x) = [.call x, .return_] := by
  simp [Silmaril.Wasm.LimeCompile.Tail.tailI]

theorem tailI_returnCallIndirect (x : TableIdx) (y : TypeIdx) :
    tailI (.returnCallIndirect x y) = [.callIndirect x y, .return_] := by
  simp [Silmaril.Wasm.LimeCompile.Tail.tailI]

theorem tailI_block (bt : BlockType) (b : List Instr) :
    tailI (.block bt b) = [.block bt (tailL b)] := by
  simp [Silmaril.Wasm.LimeCompile.Tail.tailI]

theorem tailI_loop (bt : BlockType) (b : List Instr) :
    tailI (.loop bt b) = [.loop bt (tailL b)] := by
  simp [Silmaril.Wasm.LimeCompile.Tail.tailI]

theorem tailI_if (bt : BlockType) (b₁ b₂ : List Instr) :
    tailI (.if_ bt b₁ b₂) = [.if_ bt (tailL b₁) (tailL b₂)] := by
  simp [Silmaril.Wasm.LimeCompile.Tail.tailI]

theorem tailL_single (i : Instr) : tailL [i] = tailI i := by
  rw [tailL_cons, tailL_nil, List.append_nil]

/-- A control head of the source and its rewrite in the target: the matched target step and the
related results. -/
theorem fwd_ctl {tl : Bool} {s t : Store H} {f : Frame} {us₁ : List Val} {i : Instr}
    {is₂ : List Admin} (hst : StoreRel FRel s t) (htl : tl = true)
    (hi : (∃ x, i = .returnCall x) ∨ (∃ x y, i = .returnCallIndirect x y) ∨
      (∃ bt b, i = .block bt b) ∨ (∃ bt b, i = .loop bt b) ∨ (∃ bt b₁ b₂, i = .if_ bt b₁ b₂))
    (hh : CtlHead s f us₁ i is₂) {rest y : List Admin} (hr : R true tl rest y) :
    ∃ is'', Step P host ⟨t, f, vals us₁ ++ (tailI i).map .plain ++ y⟩ ⟨t, f, is'' ++ y⟩ ∧
      R true tl (is₂ ++ rest) (is'' ++ y) := by
  subst htl
  rcases hi with ⟨x, rfl⟩ | ⟨x, y', rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩
  · cases hh with
    | @returnCall _ a fi hx hf =>
      obtain ⟨gn, hg, hfg⟩ := funcRel_get hst hf
      refine ⟨[.ref (.func a), .callRefType gn.type, .plain .return_], ?_, ?_⟩
      · rw [tailI_returnCall]
        have := Step.append_right (CtlHead.step (P := P) (host := host) (CtlHead.call hx hg))
          (.plain .return_ :: y)
        simpa [Sim.vals_nil'] using this
      · rw [← hfg.1]
        exact .same (by simp [Admin.IsCtx]) (.rcr rfl hr)
  · cases hh with
    | returnCallIndirect =>
      refine ⟨[.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y'⟩), .plain (.callRef y'),
        .plain .return_], ?_, ?_⟩
      · rw [tailI_returnCallIndirect]
        have := Step.append_right (CtlHead.step (P := P) (host := host) (s := t) (f := f)
          (CtlHead.callIndirect (x := x) (y := y'))) (.plain .return_ :: y)
        simpa [Sim.vals_nil'] using this
      · exact .same (by simp [Admin.IsCtx]) (.same (by simp [Admin.IsCtx]) (.rcr rfl hr))
  · cases hh with
    | @block _ _ _ t₁ t₂ hbt hm =>
      refine ⟨[.label t₂.length [] (vals us₁ ++ expression (tailL b))], ?_, ?_⟩
      · rw [tailI_block]
        have := Step.append_right (CtlHead.step (P := P) (host := host) (s := t)
          (CtlHead.block (body := tailL b) hbt hm)) y
        simpa using this
      · exact .label (Or.inl rfl) (R.valPre (R.expr_tailL true b) us₁) hr
  · cases hh with
    | @loop _ _ _ t₁ t₂ hbt hm =>
      refine ⟨[.label t₁.length [.loop bt (tailL b)] (vals us₁ ++ expression (tailL b))], ?_, ?_⟩
      · rw [tailI_loop]
        have := Step.append_right (CtlHead.step (P := P) (host := host) (s := t)
          (CtlHead.loop (body := tailL b) hbt hm)) y
        simpa using this
      · refine .label (Or.inr ⟨rfl, ?_⟩) (R.valPre (R.expr_tailL true b) us₁) hr
        rw [tailL_single, tailI_loop]
  · cases hh with
    | @ifTrue c _ _ _ hc =>
      refine ⟨[.plain (.block bt (tailL b₁))], ?_, ?_⟩
      · rw [tailI_if]
        have := Step.append_right (CtlHead.step (P := P) (host := host) (s := t) (f := f)
          (CtlHead.ifTrue (b₁ := tailL b₁) (b₂ := tailL b₂) (bt := bt) hc)) y
        simpa using this
      · have := R.instr (i := .block bt b₁) hr
        rw [tailI_block] at this
        simpa using this
    | ifFalse =>
      refine ⟨[.plain (.block bt (tailL b₂))], ?_, ?_⟩
      · rw [tailI_if]
        have := Step.append_right (CtlHead.step (P := P) (host := host) (s := t) (f := f)
          (CtlHead.ifFalse (b₁ := tailL b₁) (b₂ := tailL b₂) (bt := bt))) y
        simpa using this
      · have := R.instr (i := .block bt b₂) hr
        rw [tailI_block] at this
        simpa using this

theorem isCtl_of_cases {i : Instr}
    (hi : (∃ x, i = .returnCall x) ∨ (∃ x y, i = .returnCallIndirect x y) ∨
      (∃ bt b, i = .block bt b) ∨ (∃ bt b, i = .loop bt b) ∨ (∃ bt b₁ b₂, i = .if_ bt b₁ b₂)) :
    IsCtl i := by
  rcases hi with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ <;>
    trivial

/-- **A rewritten instruction** (or an unchanged one) at the head. -/
theorem fwd_instr (hhost : HostRespects FRel host) {s t s' : Store H} {f f' : Frame}
    {V : List Val} {i : Instr} {rest y x' : List Admin} (hst : StoreRel FRel s t)
    (hr : R true true rest y) (ha : (Admin.plain i).val? = none)
    (h : Step P host ⟨s, f, vals V ++ .plain i :: rest⟩ ⟨s', f', x'⟩) :
    FM P host true s' f' x' t f (vals V ++ ((tailI i).map .plain ++ y))
      (codeSize (vals V ++ .plain i :: rest)) := by
  rcases tailI_cases i with hti | hi
  · rw [hti]
    exact fwd_same hhost hst (by simp [Admin.IsCtx]) hr ha h
  · have hc := isCtl_of_cases hi
    rcases Step.split_head ha h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc', -⟩ | ⟨hc', -⟩
    · have hs' : Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', is'⟩ := hs
      obtain ⟨rfl, rfl, ws₁, us₁, is₂, rfl, rfl, hh⟩ := ctl_inv hc hs'
      obtain ⟨is'', hstep, hR⟩ := fwd_ctl (P := P) (host := host) hst rfl hi hh hr
      refine FM.of_trans (y' := vals (ws ++ ws₁) ++ is'' ++ y) (.single ?_) hst ?_
      · have := step_mid hstep (ws ++ ws₁) []
        simpa using this
      · simpa using R.valPre hR (ws ++ ws₁)
    · cases hc'
    · cases hc'
      exact (hc : False).elim

/-- **A `RETURN_CALL_REF` at the head** does not step on its own. -/
theorem fwd_stuck {s s' : Store H} {f f' : Frame} {V : List Val} {c : Admin}
    {rest x' : List Admin} (hc : c.IsReturnCallRef)
    (h : Step P host ⟨s, f, vals V ++ c :: rest⟩ ⟨s', f', x'⟩) : False := by
  rcases Step.split_head (Admin.val?_of_isReturnCallRef hc) h with
      ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Closure.Step.returnCallRef_stuck_aux hs us c hc rfl
  · exact hc
  · exact hc

/-- **The source discards around its trap.** -/
theorem fwd_trap {tl : Bool} {s t s' : Store H} {f f' : Frame} {V : List Val}
    {rest y x' : List Admin} (hst : StoreRel FRel s t) (hy : TA y)
    (h : Step P host ⟨s, f, vals V ++ .trap :: rest⟩ ⟨s', f', x'⟩) :
    FM P host tl s' f' x' t f y (codeSize (vals V ++ .trap :: rest)) := by
  rcases Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ |
      ⟨-, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ | ⟨hc, -⟩
  · obtain ⟨hs', hf', p, w, q, rfl, hw, he⟩ := Step.trap_redex_aux hs us rfl
    dsimp only at hs' hf' he
    subst hs' hf' he
    refine FM.of_stutter ?_ hst (by simpa using R.trapC (fw := true) (tl := tl) (ws ++ (p ++ q)) rest hy)
    have := codeSize_drop_vals_lt (ws ++ p) w q (.trap :: rest) hw
    simpa using this
  · refine FM.of_stutter ?_ hst (by simpa using R.trapC (fw := true) (tl := tl) ws r' hy)
    have := codeSize_discard_lt ws us [.trap] r r' hne
    simpa using this
  · cases hc

/-- **The source discards around its throw.** -/
theorem fwd_throw {tl : Bool} {s t s' : Store H} {f f' : Frame} {V : List Val} {e : Nat}
    {rest y x' : List Admin} (hst : StoreRel FRel s t) (hy : TT e y)
    (h : Step P host ⟨s, f, vals (V ++ [.ref (.exn e)]) ++ .plain .throwRef :: rest⟩
      ⟨s', f', x'⟩) :
    FM P host tl s' f' x' t f y (codeSize (vals (V ++ [.ref (.exn e)]) ++ .plain .throwRef :: rest)) := by
  rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨hc, -⟩ |
      ⟨-, rfl, rfl, ws, us, x, r, r', hV, rfl, hne, rfl⟩
  · obtain ⟨hs', hf', hcase⟩ := Step.throwRef_redex_aux hs us rfl
    dsimp only at hs' hf' hcase
    subst hs' hf'
    rcases hcase with ⟨p, w, q, a, rfl, hw, he⟩ | ⟨u, u', rfl, -⟩
    · have hea : a = e := by
        have := congrArg List.getLast? hV
        simp at this; exact this.symm
      subst hea
      rw [he]
      have hV' : V = ws ++ p ++ w ++ q := by
        have := hV
        rw [show ws ++ (p ++ w ++ q ++ [Val.ref (.exn a)]) = (ws ++ p ++ w ++ q) ++ [.ref (.exn a)]
          by simp] at this
        exact List.append_inj_left' this rfl
      subst hV'
      refine FM.of_stutter ?_ hst ?_
      · have := codeSize_drop_vals_lt (ws ++ p) w (q ++ [.ref (.exn a)]) (.plain .throwRef :: rest) hw
        simpa [throwing, Val.toAdmin] using this
      · have := R.throwC (fw := true) (tl := tl) (ws ++ (p ++ q)) rest hy
        simpa [throwing, Val.toAdmin] using this
    · have := congrArg List.getLast? hV
      simp at this
  · cases hc
  · have hxe : x = e := by
      have := congrArg List.getLast? hV
      simp at this; exact this.symm
    subst hxe
    refine FM.of_stutter ?_ hst (R.throwC ws r' hy)
    have hV' : V = ws ++ us := by
      have := hV
      rw [show ws ++ us ++ [Val.ref (.exn x)] = (ws ++ us) ++ [.ref (.exn x)] by simp] at this
      exact List.append_inj_left' this rfl
    subst hV'
    have := codeSize_discard_lt ws us (throwing x) r r' hne
    simpa [throwing, Val.toAdmin] using this

end Silmaril.Raw.Wasm.LimeCompile.TailSim
