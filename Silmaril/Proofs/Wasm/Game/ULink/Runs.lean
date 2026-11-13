module

public import Silmaril.Wasm.Game.ULink.Runs.Defs
public import Silmaril.Proofs.Wasm.Game.ULink.Backward

/-!
# A linked run splits into a consumer run answered by provider runs

`linked_oruns`: a host-free run of the linked module in a real store `s` with the link's
layout, from `⟨s, f, code⟩` to a result, is a run (`ORuns`) of the consumer from
`⟨L.stubS s, f, code⟩` to the stubbed final configuration, whose calls are stub calls answered
by host-free runs of the provider's invocations in the real store (`ULink.provAns`).

The proof follows the linked run from its head. While the consumer runs (`CMode`), a linked
step is a consumer step in the stubbed store or a call of a provider function (`linked_step`).
After such a call (`PMode`), the linked code is provider code `Y` in the consumer's callout
context `E`, and a linked step is a provider step of `Y` (`step_fill_inv`); when `Y` is a
result, the consumer resumes in the stubbed store of the provider's final store. The run
cannot end inside live provider code (`fill_ne_result`). No typing is needed: the backward
step lemmas are those of the untyped link (`Silmaril.Proofs.Wasm.Game.ULink.Backward`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Proofs.Wasm.Game.Linking

variable {L : ULink} {P : Profile}

/-- Prepend a host-free step to a run. -/
theorem ORuns.head {Ans : Store Nat → Nat → List Val → Result → Store Nat → Prop}
    {c c' d : Config Nat} {tr : List OCall} (h : Step P Det.noHost c c')
    (hr : ORuns P Ans c' tr d) : ORuns P Ans c tr d := by
  cases hr with
  | stop hs => exact .stop (.head h hs)
  | call hs hd hA hk => exact .call (.head h hs) hd hA hk

/-- The final configuration, in the stubbed store. -/
abbrev stubFin (L : ULink) (d : Config Nat) : Config Nat := ⟨L.stubS d.store, d.frame, d.code⟩

/-- The consumer runs at `x` on the way to `d`. -/
def CMode (L : ULink) (P : Profile) (d x : Config Nat) : Prop :=
  ∀ s f code, x = ⟨s, f, code⟩ → L.Layout s →
    ∃ tr, ORuns P (L.provAns P) ⟨L.stubS s, f, code⟩ tr (stubFin L d)

/-- Provider code runs at `x` inside a parked stub call `c₀` of the consumer, on the way to
`d`. -/
def PMode (L : ULink) (P : Profile) (d x : Config Nat) : Prop :=
  ∀ (σ₀ : Store Nat) (F : Frame) (c₀ : List Admin) (E : Ctx) (a k : Nat) (args : List Val)
    (s : Store Nat) (Y : List Admin), L.Layout σ₀ →
    decompose? (L.stubS σ₀) c₀ = some (E, a, k, args) → L.target k = some a →
    x = ⟨s, F, E.fill Y⟩ → L.Layout s → ProvCode s Y →
    Steps P Det.noHost (invoke σ₀ a args) ⟨s, {}, Y⟩ →
    ∃ tr, ORuns P (L.provAns P) ⟨L.stubS σ₀, F, c₀⟩ tr (stubFin L d)

/-- A finished provider answers the parked stub call. -/
theorem finish {d : Config Nat} {σ₀ s : Store Nat} {F : Frame} {c₀ : List Admin} {E : Ctx}
    {a k : Nat} {args : List Val} {r : Result} (hl₀ : L.Layout σ₀)
    (hd : decompose? (L.stubS σ₀) c₀ = some (E, a, k, args)) (ht : L.target k = some a)
    (hrun : Steps P Det.noHost (invoke σ₀ a args) ⟨s, {}, r.toAdmin⟩)
    (hc : ∃ tr, ORuns P (L.provAns P) ⟨L.stubS s, F, E.fill r.toAdmin⟩ tr (stubFin L d)) :
    ∃ tr, ORuns P (L.provAns P) ⟨L.stubS σ₀, F, c₀⟩ tr (stubFin L d) := by
  obtain ⟨tr, hk⟩ := hc
  exact ⟨_, .call (d := ⟨L.stubS σ₀, F, c₀⟩) .refl hd ⟨σ₀, a, s, rfl, hl₀, ht, hrun, rfl⟩ hk⟩

theorem cmode_refl (d : Config Nat) : CMode L P d d := by
  rintro s f code rfl -
  exact ⟨[], .stop .refl⟩

theorem pmode_refl {d : Config Nat} {r : Result} (hfin : d.code = r.toAdmin) : PMode L P d d := by
  rintro σ₀ F c₀ E a k args s Y hl₀ hd ht rfl hl hp hrun
  rcases hp with hlive | ⟨r', rfl⟩
  · exact absurd hfin (fill_ne_result hlive E r)
  · exact finish hl₀ hd ht hrun ⟨[], .stop .refl⟩

/-- The provider's invocation enters the provider function. -/
theorem invoke_step {s : Store Nat} {a : Nat} {vs : List Val} {fi : FuncInst Nat}
    {ps rs : Ty (.list .val)} {cd : Func} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) (hcd : fi.code = .wasm cd) :
    Step P Det.noHost (invoke s a vs) ⟨s, {}, callCode fi rs cd vs⟩ :=
  Step.callRefFunc (c := .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) trivial hf
    he hn hcd

/-- **A linked call of a provider function from consumer code starts the provider.** -/
theorem cmode_call {d : Config Nat} {s s' : Store Nat} {f f' : Frame} {code code' : List Admin}
    (hl : L.Layout s) (hcall : CallAt (L.stubS s).funcs ⟨s, f, code⟩ ⟨s', f', code'⟩)
    (ih : PMode L P d ⟨s', f', code'⟩) :
    ∃ tr, ORuns P (L.provAns P) ⟨L.stubS s, f, code⟩ tr (stubFin L d) := by
  obtain ⟨E, vs, a, cr, fi, ps, rs, cd, hcode, hcr, hf, he, hn, hcd, hX, heq⟩ := hcall
  have heq' : s' = s ∧ f' = f ∧ code' = E.fill (callCode fi rs cd vs) := by
    simpa only [Config.mk.injEq, callCode] using heq
  obtain ⟨k, c₀, hs⟩ := stub_of_ne hf hX
  have ht : L.target k = some a := (L.target_iff k a).2 ⟨c₀, hs⟩
  have hfσ : (L.stubS s).funcs[a]? = some { fi with code := .host k } := by
    rw [stubS_get, hf, Option.map_some, stubFI_some hs]
  have hcode' : code = E.fill (vals vs ++ [.ref (.func a), cr]) := hcode
  have hd : decompose? (L.stubS s) code = some (E, a, k, vs) :=
    hcode' ▸ decompose?_fill E hcr hfσ he hn rfl
  have ih' : PMode L P d ⟨s, f, E.fill (callCode fi rs cd vs)⟩ := by
    rw [← heq'.1, ← heq'.2.1, ← heq'.2.2]
    exact ih
  exact ih' s f code E a k vs s _ hl hd ht rfl hl (.inl (.inl ⟨_, _, _, rfl⟩))
    (.single (invoke_step hf he hn hcd))

/-- A linked step from consumer code. -/
theorem cmode_step {d x y : Config Nat} (h : Step P Det.noHost x y) (ihc : CMode L P d y)
    (ihp : PMode L P d y) : CMode L P d x := by
  rintro s f code rfl hl
  obtain ⟨s', f', code'⟩ := y
  have hfun : s'.funcs = s.funcs := (Step.framesLocal h).1
  rcases linked_step h with hc | hcall
  · obtain ⟨tr, hr⟩ := ihc s' f' code' rfl (Layout.of_funcs hl hfun)
    exact ⟨tr, ORuns.head hc hr⟩
  · exact cmode_call hl hcall ihp

/-- A linked step inside provider code, or the return of a finished provider. -/
theorem pmode_step {d x y : Config Nat} (h : Step P Det.noHost x y) (ihc : CMode L P d y)
    (ihp : PMode L P d y) : PMode L P d x := by
  rintro σ₀ F c₀ E a k args s Y hl₀ hd ht rfl hl hp hrun
  rcases hp with hlive | ⟨r', rfl⟩
  · obtain ⟨s', Y', rfl, hp', hst⟩ := step_fill_inv E hlive h
    have hfun : s'.funcs = s.funcs := (Step.framesLocal hst).1
    exact ihp σ₀ F c₀ E a k args s' Y' hl₀ hd ht rfl (Layout.of_funcs hl hfun) hp'
      (hrun.tail hst)
  · exact finish hl₀ hd ht hrun (cmode_step h ihc ihp s F _ rfl hl)

theorem modes {d : Config Nat} {r : Result} (hfin : d.code = r.toAdmin) {x : Config Nat}
    (h : Steps P Det.noHost x d) : CMode L P d x ∧ PMode L P d x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨cmode_refl d, pmode_refl hfin⟩
  | head hxy _ ih => exact ⟨cmode_step hxy ih.1 ih.2, pmode_step hxy ih.1 ih.2⟩

/-- **A linked run to a result is a consumer run answered by provider runs.** -/
theorem linked_oruns {s : Store Nat} {f : Frame} {code : List Admin} {d : Config Nat}
    {r : Result} (hl : L.Layout s) (h : Steps P Det.noHost ⟨s, f, code⟩ d)
    (hfin : d.code = r.toAdmin) :
    ∃ tr, ORuns P (L.provAns P) ⟨L.stubS s, f, code⟩ tr ⟨L.stubS d.store, d.frame, d.code⟩ :=
  (modes hfin h).1 s f code rfl hl

end Silmaril.Proofs.Wasm.Game.ULink
