module

public import Silmaril.Elf.Link.Dyn.ProcX.Defs
public import Silmaril.Elf.Link.Dyn.ProcG.Thms
public import Silmaril.X86.Sse9.Thms

/-! # `ProcX` is `ProcG` at the `Sse9` instance

`ProcX.procX W` (the process with silmaril's `Sse9` in the image) is the general extended
process `ProcG.procG L W` at `L = Sse9.extendsOpen9`, up to the state isomorphism
`toG`/`ofG` (`XPState = {p : PState, x : XFile}` against `GState Sse9.XState = {x : Sse9.XState, g : Ghost}`).

PROVED (standard axioms): `step_ok_iff`, `step_stop_iff` (the steps correspond), and the transfers
`mustX_of_mustG`, `mustG_of_mustX` both ways. So `ProcX`'s SSE stepping lemmas (`mustX_sse`,
`mustX_blkX_at`, `wpx_store_ups`, …) are lemmas about `procG Sse9.extendsOpen9`, and results
over `procG` with any other extension of `Open9` (e.g. `Str9G.extendsOpen9`) use `ProcG.must_lift`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.ProcX

open Silmaril.X86.RelIsa (Res Must)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.ProcG

/-- The `Sse9` extension of `Open9` (the XMM file is the frame). -/
abbrev L9 : Silmaril.X86.Open9.isa.Extends Silmaril.X86.Sse9.isa := Silmaril.X86.Sse9.extendsOpen9

def toG (s : XPState) : GState Silmaril.X86.Sse9.XState := ⟨⟨s.p.m, s.x⟩, s.p.g⟩
def ofG (y : GState Silmaril.X86.Sse9.XState) : XPState := ⟨⟨y.x.m, y.g⟩, y.x.xmm⟩

@[simp] theorem toG_ofG (y : GState Silmaril.X86.Sse9.XState) : toG (ofG y) = y := rfl
@[simp] theorem ofG_toG (s : XPState) : ofG (toG s) = s := rfl

theorem step_stop_iff (W : World) (s : XPState) :
    (procG L9 W).step (toG s) .stop ↔ (procX W).step s .stop := by
  show stepG L9 W (toG s) .stop ↔ step W s .stop
  unfold stepG step
  cases hd : s.p.g.done with
  | some _ => simp [toG, hd]
  | none =>
    simp only [toG, hd]
    by_cases hin : W.InImage s.p.m.core.rip.toNat
    · simp only [hin, ↓reduceIte]
      cases Silmaril.X86.Sse9.step ⟨s.p.m, s.x⟩ <;> simp
    · simp only [hin, ↓reduceIte]
      constructor
      · intro h; exact ⟨.stop, h, trivial⟩
      · rintro ⟨r', h1, h2⟩
        cases r' with
        | ok t => cases h2
        | stop => exact h1

theorem step_ok_iff (W : World) (s : XPState) (y : GState Silmaril.X86.Sse9.XState) :
    (procG L9 W).step (toG s) (.ok y) ↔ (procX W).step s (.ok (ofG y)) := by
  show stepG L9 W (toG s) (.ok y) ↔ step W s (.ok (ofG y))
  unfold stepG step
  cases hd : s.p.g.done with
  | some _ => simp [toG, hd]
  | none =>
    simp only [toG, hd]
    by_cases hin : W.InImage s.p.m.core.rip.toNat
    · simp only [hin, ↓reduceIte]
      cases h : Silmaril.X86.Sse9.step ⟨s.p.m, s.x⟩ with
      | none => simp
      | some x' =>
        simp only [Res.ok.injEq]
        constructor
        · rintro rfl; rfl
        · intro he
          obtain ⟨⟨ym, yx⟩, yg⟩ := y
          obtain ⟨xm, xx⟩ := x'
          simp only [ofG, XPState.mk.injEq, PState.mk.injEq] at he
          obtain ⟨⟨h1, h2⟩, h3⟩ := he
          subst h1 h2 h3; rfl
    · simp only [hin, ↓reduceIte]
      constructor
      · rintro ⟨t, h1, h2, h3⟩
        refine ⟨.ok t, h1, ?_⟩
        show (⟨y.x.m, y.g⟩ : PState) = t
        rw [h2, h3]
      · rintro ⟨r', h1, h2⟩
        cases r' with
        | stop => cases h2
        | ok t =>
          have h2' : (⟨y.x.m, y.g⟩ : PState) = t := h2
          refine ⟨t, h1, by rw [← h2'], by rw [← h2']⟩

/-- **From the general process at the `Sse9` instance to `ProcX`.** -/
theorem mustX_of_mustG {W : World} {Q : GState Silmaril.X86.Sse9.XState → Prop}
    {y : GState Silmaril.X86.Sse9.XState} (h : Must (procG L9 W) (fun _ => True) Q y) :
    MustX W (fun s => Q (toG s)) (ofG y) := by
  induction h with
  | @done y hq => exact .done hq
  | @step y _ hns _ ih =>
    refine .step trivial (fun hs => hns ((step_stop_iff W (ofG y)).2 hs)) ?_
    intro t ht
    have := ih (toG t) ((step_ok_iff W (ofG y) (toG t)).2 ht)
    simpa using this

/-- **From `ProcX` to the general process at the `Sse9` instance.** -/
theorem mustG_of_mustX {W : World} {Q : XPState → Prop} {s : XPState} (h : MustX W Q s) :
    Must (procG L9 W) (fun _ => True) (fun y => Q (ofG y)) (toG s) := by
  induction h with
  | @done s hq => exact .done hq
  | @step s _ hns _ ih =>
    refine .step trivial (fun hs => hns ((step_stop_iff W s).1 hs)) ?_
    intro y hy
    have := ih (ofG y) ((step_ok_iff W s y).1 hy)
    simpa using this

end Silmaril.Elf.Link.Dyn.ProcX
