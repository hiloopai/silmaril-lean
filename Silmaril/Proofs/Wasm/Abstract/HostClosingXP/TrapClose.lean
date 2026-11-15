module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapFwd
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Closure

/-!
# The trapping behaviours of the canonical closure are logged Core runs (proofs)

A trapping resolution (`subst_trap`) either resolves every call by a returning callee and ends in
the open behaviour's trap, or stops at a call whose callee traps (`Shape.Subst.intTrap`), anything
after it dropped. By least-fixpoint induction (`close_le_trapC`), every trapping closed behaviour
with a consistent log is a Core run of the call to a trap with exactly that log, in some store:

* a Wasm body ending in a trap: `evalLXPh_fwd` in its frame, the trap (or Core's pending null tail
  call) leaving the label and frame;
* a Wasm body cut at a trapping callee, in its body or at its pending tail call:
  `evalLXPh_trap` in its frame, or the body's run to the pending tail call, the frame left and
  the tail callee's trap;
* a host callee answering a trap: its one event.

A cut call (`callCut`, `indCut`, `refCut`) contributes exactly through the second case: it is
resolved only by `intTrap`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (tailFlow)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Trapping resolutions -/

universe u

/-- **A trapping resolution**: every call resolved by a returning callee and the open end a
trap, or a prefix resolved and then a call whose callee traps. -/
theorem subst_trap {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (h : Shape.Subst c x e y) (hy : y.2 = .trap) :
    (e = .trap ∧ Shape.SubstPre c x y.1) ∨
      ∃ (u w : List (Call (sh.E ⊕ₛ sh.self))) (g : sh.F) (a : sh.A g) (s : sh.S)
        (ans : sh.B g × sh.S) (q c₁ : List (Call sh.E)),
        x = u ++ ⟨.inr ⟨g, (a, s)⟩, ans⟩ :: w ∧ Shape.SubstPre c u q ∧
          (c₁, .trap) ∈ c g s a ∧ y.1 = q ++ c₁ := by
  induction h with
  | nil e => exact .inl ⟨hy, .nil⟩
  | @ext m n rest e y _ ih =>
    rcases ih hy with ⟨he, hp⟩ | ⟨u, w, g, a, s, ans, q, c₁, rfl, hp, hc, hq⟩
    · exact .inl ⟨he, .ext hp⟩
    · exact .inr ⟨⟨.inl m, n⟩ :: u, w, g, a, s, ans, ⟨m, n⟩ :: q, c₁, rfl, .ext hp, hc,
        by simp [hq]⟩
  | @int g' a' s' b s₂ rest e c₀ y hm _ ih =>
    rcases ih hy with ⟨he, hp⟩ | ⟨u, w, g, a, s, ans, q, c₁, rfl, hp, hc, hq⟩
    · exact .inl ⟨he, .int hm hp⟩
    · exact .inr ⟨⟨.inr ⟨g', (a', s')⟩, (b, s₂)⟩ :: u, w, g, a, s, ans, c₀ ++ q, c₁, rfl,
        .int hm hp, hc, by simp [hq]⟩
  | @intTrap g a s ans rest e c₁ hc =>
    exact .inr ⟨[], rest, g, a, s, ans, [], c₁, rfl, .nil, hc, rfl⟩
  | intDiv _ => cases hy

theorem substPre_mono {sh : Silmaril.Games.Abstract.Shape.{u}} {c c' : sh.ClosedMod} (h : c ≤ c')
    {x : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} (hs : Shape.SubstPre c x q) :
    Shape.SubstPre c' x q := by
  induction hs with
  | nil => exact .nil
  | ext _ ih => exact .ext ih
  | int hm _ ih => exact .int (h _ _ _ hm) ih

theorem substPre_ext_single {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod}
    {m : sh.E.Op} {n : sh.E.Ar m} {q : List (Call sh.E)}
    (hs : Shape.SubstPre c [⟨.inl m, n⟩] q) : q = [⟨m, n⟩] := by
  cases hs with
  | ext h => cases h; rfl

theorem lift_eq_mk{z : OCall H} {g : Nat} {a : List Val} {s : Store H}
    {ans : (List Val ⊕ Nat) × Store H}
    (h : OCall.lift z = ⟨.inr ⟨g, (a, s)⟩, ans⟩) : z = OCall.mk g a s ans.1 ans.2 := by
  rcases z with ⟨⟨⟩ | ⟨g', a', s'⟩, ⟨b, s₂⟩⟩
  cases h
  rfl

/-- A log whose lift splits at an internal call splits there. -/
theorem map_lift_split {l : List (OCall H)} {u w : List (HCall H)} {g : Nat} {a : List Val}
    {s : Store H} {ans : (List Val ⊕ Nat) × Store H}
    (h : l.map OCall.lift = u ++ ⟨.inr ⟨g, (a, s)⟩, ans⟩ :: w) :
    ∃ l₁ l₂, l = l₁ ++ OCall.mk g a s ans.1 ans.2 :: l₂ ∧ l₁.map OCall.lift = u := by
  obtain ⟨l₁, l₂', rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp h
  obtain ⟨z, l₂, rfl, hz, -⟩ := List.map_eq_cons_iff.mp h₂
  exact ⟨l₁, l₂, by rw [lift_eq_mk hz], h₁⟩

theorem mk_inj {a a' : Nat} {args args' : List Val} {s₁ s₁' s₂ s₂' : Store H}
    {b b' : List Val ⊕ Nat} (h : OCall.mk a args s₁ b s₂ = OCall.mk a' args' s₁' b' s₂') :
    a = a' ∧ args = args' ∧ s₁ = s₁' := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem tailAns_ne_trap {m n : Nat} {b : List Val ⊕ Nat} {s : Store H} :
    tailAns m n b s ≠ .trap := by
  rcases b with ws | t <;> simp [tailAns, ansFlow, tailFlow, exitFlow, endOfFlow]

/-- A closed behaviour names a typed function. -/
theorem close_fn {a : Nat} {s : Store H} {us : List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : y ∈ Shape.close wasmHOpenXP a s us) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) := by
  rw [← Shape.resolve_close] at h
  obtain ⟨x, hx, -⟩ := h
  rcases hx with ⟨fi, -, ps, rs, -, -, -, -, -, hfi, -, hty, -⟩ |
    ⟨fi, -, ps, rs, -, -, -, -, -, -, -, -, hfi, -, hty, -⟩ |
    ⟨fi, -, ps, rs, -, -, -, hfi, -, hty, -⟩ <;> exact ⟨fi, ps, rs, hfi, hty⟩

/-! ## The trapping closed behaviours -/

/-- **Trapping closed behaviours that are logged Core runs**: closed behaviours that, trapping
with a consistent log, are on stores with the tag invariants and the store check, for typed
arguments, Core runs of the call to a trap with exactly that log. -/
def TrapC (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    (wasmHShape H).ClosedMod := fun a s us =>
  {y | y ∈ Shape.close wasmHOpenXP a s us ∧ (y.2 = .trap → Cons host y.1 →
    ∀ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi →
      Validation.DefType.funcType? fi.type = some (ps, rs) → TagsOk tags s →
      StoreChkE (ehExt tags) s.funcs → us.length = ps.length → CalleeTrap P host s a us y.1)}

theorem trapC_le_goodCX {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) : TrapC tags P host ≤ GoodCX tags P host :=
  fun a s us _ h => close_le_goodCX hH hE a s us h.1

/-- The callee of a split call traps, from `TrapC`. -/
theorem trapAt_of_trapC {tags : List TagInst} {a : Nat} {args : List Val} {s₁ : Store H}
    {ans : (List Val ⊕ Nat) × Store H} {c₁ : List (Call (wasmHostSig H))}
    (hm : (c₁, .trap) ∈ TrapC tags P host a s₁ args) (hc : Cons host c₁) :
    TrapAt tags P host (OCall.mk a args s₁ ans.1 ans.2) c₁ := by
  intro a' args' s₁' b s₂ h fi ps rs hfi hty hts hS hn
  obtain ⟨rfl, rfl, rfl⟩ := mk_inj h
  exact hm.2 rfl hc fi ps rs hfi hty hts hS hn

/-- **Every closed behaviour is in `TrapC`**: least-fixpoint induction. -/
theorem close_le_trapC {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) : Shape.close (wasmHOpenXP (H := H)) ≤ TrapC tags P host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s us y ⟨x, hx, hS⟩
  have hle : TrapC tags P host ≤ Shape.close (wasmHOpenXP (H := H)) := fun _ _ _ _ h => h.1
  have hmem : y ∈ Shape.close wasmHOpenXP a s us := by
    rw [← Shape.resolve_close]
    exact ⟨x, hx, hS.mono hle⟩
  refine ⟨hmem, fun hy hq fi₀ ps₀ rs₀ hfi₀ hty₀ hts hSt hn f c hcr => ?_⟩
  have hG : TrapC tags P host ≤ GoodCX tags P host := trapC_le_goodCX hH hE
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hcode, hty, hE', hxf, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b₀, l, hfi, hcode, hty, hE', rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hcode, hty, hxf, rfl⟩
  all_goals
    obtain rfl : fi₀ = fi := Option.some.inj (hfi₀.symm.trans hfi)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty₀.symm.trans hty))
  · -- a Wasm body ending in a flow
    obtain ⟨ob, hob, hb'⟩ := body_chk hSt hfi hcode hty hn
    rcases subst_trap hS hy with ⟨he, hp⟩ | ⟨u, w, g, a₁, s₀, ans, q, c₁, hsplit, hp, hc₁, hq₁⟩
    · -- the body traps
      have hfl : fl = .trap := by rcases fl <;> simp_all [endOfFlow]
      subst hfl
      have hbfl : bfl = .trap := by
        rcases bfl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [exitFlow]
      subst hbfl
      obtain ⟨d, cl⟩ := evalLXPh_fwd (P := P) hH hE hE' y.1 (substPre_mono hG hp) hq
      have hwb := cl hts hSt hb'
      rw [Binaryen.lowerList_liftInstrs] at hwb
      obtain ⟨s'', f'', c', o, hrun, he', hm⟩ := hwb
      have inner := evRun_wrap (Wfr rs₀.length f) (hW_fr _ f) hrun
      rcases matchP_flow_iff.mp hm with ⟨rfl, rfl, hfm⟩ | ⟨-, vs, c₀, rfl, hc₀, rfl, rfl⟩
      · rcases o with _ | _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hfm
        have hc' : c' = [.trap] := he'
        subst hc'
        refine ⟨s'', ?_⟩
        have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
          (evRun_trans inner (evRun_of_free (steps_trap_frame (P := P))))
        simpa [vals] using this
      · obtain ⟨-, rest, rfl⟩ := he'
        refine ⟨s'', ?_⟩
        have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
          (evRun_trans inner (evRun_of_free (frame_tailNull (P := P) (host := NH) hc₀)))
        simpa [vals] using this
    · -- the body cut at a trapping callee
      obtain ⟨l₁, l₂, rfl, rfl⟩ := map_lift_split hsplit
      rw [hq₁] at hq ⊢
      rw [cons_append] at hq
      have hz := trapAt_of_trapC (ans := ans) hc₁ hq.2
      have hwb := evalLXPh_trap (P := P) hH hE hE' l₁ _ l₂ rfl q c₁ (substPre_mono hG hp) hz
        ((cons_append).2 hq) hts hSt hb'
      rw [Binaryen.lowerList_liftInstrs] at hwb
      obtain ⟨s'', f'', c', o, hrun, he', ho⟩ := hwb
      rw [trap_of_ends he' ho] at hrun
      have inner := evRun_wrap (Wfr rs₀.length f) (hW_fr _ f) hrun
      refine ⟨s'', ?_⟩
      have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
        (evRun_trans inner (evRun_of_free (steps_trap_frame (P := P))))
      simpa [vals] using this
  · -- a Wasm body ending in a pending tail call
    obtain ⟨ob, hob, hb'⟩ := body_chk hSt hfi hcode hty hn
    rcases subst_trap hS hy with ⟨he, -⟩ | ⟨u, w, g, a₁, s₀, ans, q, c₁, hsplit, hp, hc₁, hq₁⟩
    · exact absurd he tailAns_ne_trap
    · obtain ⟨l₁, l₂, hl, rfl⟩ := map_lift_split hsplit
      rw [hq₁] at hq ⊢
      rw [cons_append] at hq
      have hz := trapAt_of_trapC (ans := ans) hc₁ hq.2
      rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, hzl⟩
      · -- in the body
        have hwb := evalLXPh_trap (P := P) hH hE hE' l₁ _ m rfl q c₁ (substPre_mono hG hp) hz
          ((cons_append).2 hq) hts hSt hb'
        rw [Binaryen.lowerList_liftInstrs] at hwb
        obtain ⟨s'', f'', c', o, hrun, he', ho⟩ := hwb
        rw [trap_of_ends he' ho] at hrun
        have inner := evRun_wrap (Wfr rs₀.length f) (hW_fr _ f) hrun
        refine ⟨s'', ?_⟩
        have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
          (evRun_trans inner (evRun_of_free (steps_trap_frame (P := P))))
        simpa [vals] using this
      · -- at the pending tail call, made at the frame
        obtain ⟨rfl, rfl, rfl⟩ := mk_inj hzl.symm
        obtain ⟨d, cl⟩ := evalLXPh_fwd (P := P) hH hE hE' q (substPre_mono hG hp) hq.1
        obtain ⟨t₁, hA, -⟩ := evalOXP_host_good (P := P) hH hE d hts
        obtain ⟨-, hinv, hw⟩ := hA hSt hb'
        obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, -⟩ := hw a' args n rfl
        obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
        have hS₁ : StoreChkE (ehExt tags) s₁.funcs := hinv.1.2.1 hSt
        have hwb := cl hts hSt hb'
        rw [Binaryen.lowerList_liftInstrs] at hwb
        obtain ⟨s'', f'', c', o, hrun, he', hm⟩ := hwb
        obtain ⟨vs₁, c₀, rfl, hc₀, rfl, rfl⟩ := matchP_tail_iff.mp hm
        obtain ⟨-, rest, rfl⟩ := he'
        have inner := evRun_wrap (Wfr rs₀.length f) (hW_fr _ f) hrun
        have ex := frame_tail_exit (P := P) (host := NH) (s := s'') (f := f) (k := rs₀.length)
          (F := f'') (vs₁ := vs₁) (rest := rest) hc₀ hfi₂ hex₂ (hargs.trans hpl₂.symm)
        obtain ⟨s₃, hcl⟩ := hc₁.2 rfl hq.2 fi₂ ps₂ rs₂ hfi₂ hty₂ t₁ hS₁ hargs f _
          (isCallRef_retToCallIn hc₀ f''.module)
        refine ⟨s₃, ?_⟩
        have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
          (evRun_trans inner (evRun_trans (evRun_of_free ex) hcl))
        simpa [vals] using this
  · -- a host function answering a trap: its one event
    rcases subst_trap hS hy with ⟨he, hp⟩ | ⟨u, w, g, a₁, s₀, ans, q, c₁, hsplit, -, -, -⟩
    · rw [substPre_ext_single hp] at hq ⊢
      have hm : host hh s us (.returned s' r) := hq _ List.mem_cons_self
      obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
      have hstep := hEvStep_host_callRef (P := P) (f := f) hcr hfi he' (hn.trans hpl.symm)
        hcode hm
      rcases r with w | t | _
      · simp only [resFlow, exitFlow, Option.some.injEq] at hxf
        subst hxf
        cases he
      · exact absurd hm (hH.noThrow _ _ _ _ _)
      · exact ⟨s', .event hstep (.refl _)⟩
    · rcases u with _ | ⟨u₀, u⟩
      · cases hsplit
      · obtain ⟨-, h⟩ := List.cons.inj hsplit
        simp at h

/-- **A trapping closed behaviour with a consistent log is a Core run of the call to a trap**
with exactly that log, in any frame and any `call_ref` form, every profile. -/
theorem close_trap_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {a : Nat} {s : Store H} {us : List Val}
    {c₁ : List (Call (wasmHostSig H))} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hm : (c₁, .trap) ∈ Shape.close wasmHOpenXP a s us) (hc : Cons host c₁)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    CalleeTrap P host s a us c₁ :=
  (close_le_trapC hH hE a s us hm).2 rfl hc fi ps rs hfi hty hts hS hn

/-- **A trapping behaviour of an invocation with a consistent log is a Core run of the
invocation to a trap with exactly that log**, in some store, every profile. -/
theorem wasmEvFunXP_trap_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val}
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .trap) ∈ wasmEvFunXP s (a, vs))
    (hc : Cons host cs) : ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ := by
  obtain ⟨fi, ps, rs, hfi, hty⟩ := close_fn h
  rw [invoke_eq hfi]
  exact close_trap_evRun hH hE h hc hts hS hfi hty (invokeOk_length hok hfi hty) {} _ trivial

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
