module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.Rel

/-!
# The spill simulation: pure steps, returns, the code before a call
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type} {imps : List (Nat × Nat)} {gs : List FnSeg}

/-- A pure instruction that traps, in both programs. -/
theorem simS_pure_trap {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid nres : Nat}
    {B : Nat} {ls ex ops : List W} {i : Instr} {cs ct : List Instr}
    (hR : SRel imps gs (c, s) (yc, ys)) (hcs : c.frames = ⟨fid, ls, ops, i :: cs, nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, ops, i :: ct, nres⟩ :: tw) (hl : ls.length = B)
    (hi : PureShape B i) (hp : pexec i ls ops = none) : SimS imps gs H (c, s) (yc, ys) := by
  have hctl : ctlOf i = none := ctlOf_pure hi
  have hs : step (segEnv imps gs) c = .trap := step_trap_seg hcs rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, hp])
  have ht : step (spEnv imps gs) yc = .trap := step_trap_seg hct rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, pexec_ext hi hl, hp])
  have hsrc : srcStep (segEnv imps gs) H (c, s) = .stop (.trap s) := by simp only [srcStep, hs]
  have hys : ys = s := hR.host
  have htgt : runN (srcStep (spEnv imps gs) H) 1 (yc, ys) = .stop (.trap s) := by
    simp [runN, srcStep, ht, hys]
  refine ⟨fun o ho => ⟨1, ?_⟩, fun x' hx => ?_⟩
  · rw [← SRes.stop.inj (hsrc.symm.trans ho)]
    exact htgt
  · cases hsrc.symm.trans hx

/-- A pure instruction that continues, in both programs. -/
theorem simS_pure_ok {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid : Nat}
    {g : FnSeg} {ls ex ops ls' ops' : List W} {i : Instr} {q : List Instr}
    {r : List (Site × List Instr)} (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨fid, ls, ops, i :: (q ++ flatCalls r), g.nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, ops, i :: (q ++ spCalls g.nloc g.maxD r), g.nres⟩ :: tw)
    (hch : SChain imps gs fid sw tw) (hg : segAt imps gs fid = some g) (hl : ls.length = g.nloc)
    (hex : ex.length = g.ntmp) (hsuf : SufOf g r) (hi : PureShape g.nloc i)
    (hp : pexec i ls ops = some (ls', ops'))
    (hc : chainOk (segEnv imps gs).sig g.nloc g.nres ops'.length q r = true) :
    SimS imps gs H (c, s) (yc, ys) := by
  have hs : step (segEnv imps gs) c =
      .next ⟨⟨fid, ls', ops', q ++ flatCalls r, g.nres⟩ :: sw, c.globals, c.mem⟩ :=
    step_seg hcs rfl (s' := ⟨ls', ops', c.globals, c.mem⟩) (by
      rw [segStep_pure hi]; simp [Frame.ls, hp])
  have ht : step (spEnv imps gs) yc =
      .next ⟨⟨fid, ls' ++ ex, ops', q ++ spCalls g.nloc g.maxD r, g.nres⟩ :: tw, yc.globals,
        yc.mem⟩ :=
    step_seg hct rfl (s' := ⟨ls' ++ ex, ops', yc.globals, yc.mem⟩) (by
      rw [segStep_pure hi]; simp [Frame.ls, pexec_ext hi hl, hp])
  have hl' : ls'.length = g.nloc := by rw [pexec_len hi hp]; exact hl
  have hsrc : srcStep (segEnv imps gs) H (c, s) =
      .next (⟨⟨fid, ls', ops', q ++ flatCalls r, g.nres⟩ :: sw, c.globals, c.mem⟩, s) := by
    simp only [srcStep, hs]
  have htop := TopS.seg hg hl' hex hsuf hc
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  exact ⟨1, (⟨⟨fid, ls' ++ ex, ops', q ++ spCalls g.nloc g.maxD r, g.nres⟩ :: tw, yc.globals,
    yc.mem⟩, ys), by simp only [runN, srcStep, ht],
    ⟨hR.host, hR.globals, hR.mem, ⟨_, _, sw, tw, rfl, rfl, htop, hch⟩⟩, Nat.one_pos⟩

/-- A pure step inside a segment. -/
theorem simS_pure {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid : Nat}
    {g : FnSeg} {ls ex ops : List W} {i : Instr} {q : List Instr}
    {r : List (Site × List Instr)} (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨fid, ls, ops, i :: (q ++ flatCalls r), g.nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, ops, i :: (q ++ spCalls g.nloc g.maxD r), g.nres⟩ :: tw)
    (hch : SChain imps gs fid sw tw) (hg : segAt imps gs fid = some g) (hl : ls.length = g.nloc)
    (hex : ex.length = g.ntmp) (hsuf : SufOf g r)
    (hc : chainOk (segEnv imps gs).sig g.nloc g.nres ops.length (i :: q) r = true) :
    SimS imps gs H (c, s) (yc, ys) := by
  have hi : PureShape g.nloc i := (chainOk_cons (ls := ls) (ls' := ls) (ops' := ops) hc).1
  cases hp : pexec i ls ops with
  | none => exact simS_pure_trap hR hcs hct hl hi hp
  | some res => exact simS_pure_ok hR hcs hct hch hg hl hex hsuf hi hp ((chainOk_cons hc).2 hp)

/-- The bottom frame returns. -/
theorem simS_ret_bottom {H : Host σ} {c yc : Cfg} {s ys : σ} {fid nres : Nat} {ls tl ops : List W}
    (hR : SRel imps gs (c, s) (yc, ys)) (hcs : c.frames = [⟨fid, ls, ops, [], nres⟩])
    (hct : yc.frames = [⟨fid, tl, ops, [], nres⟩]) : SimS imps gs H (c, s) (yc, ys) := by
  have hs : step (segEnv imps gs) c = ret c ops [] := step_ret hcs rfl
  have ht : step (spEnv imps gs) yc = ret yc ops [] := step_ret hct rfl
  have hsrc : srcStep (segEnv imps gs) H (c, s) = .stop (.done ops s) := by
    simp only [srcStep, hs, ret]
  have hys : ys = s := hR.host
  have htgt : runN (srcStep (spEnv imps gs) H) 1 (yc, ys) = .stop (.done ops s) := by
    simp [runN, srcStep, ht, ret, hys]
  refine ⟨fun o ho => ⟨1, ?_⟩, fun x' hx => ?_⟩
  · rw [← SRes.stop.inj (hsrc.symm.trans ho)]
    exact htgt
  · cases hsrc.symm.trans hx

/-- A frame returns to the frame waiting on its call. -/
theorem simS_ret_wait {H : Host σ} {c yc : Cfg} {s ys : σ} {ss ts : List Frame} {g g1 : FnSeg}
    {fid1 : Nat} {ls ex ops ls1 ex1 live : List W} {s1 : Site} {c1 : List Instr}
    {r1 : List (Site × List Instr)} (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨s1.f.value.val, ls, ops, [], g.nres⟩ ::
      ⟨fid1, ls1, live, c1 ++ flatCalls r1, g1.nres⟩ :: ss)
    (hct : yc.frames = ⟨s1.f.value.val, ls ++ ex, ops, [], g.nres⟩ ::
      ⟨fid1, ls1 ++ ex1, [], spillPost g1.nloc g1.maxD s1 ++ c1 ++ spCalls g1.nloc g1.maxD r1,
        g1.nres⟩ :: ts)
    (hch' : SChain imps gs fid1 ss ts) (hg : segAt imps gs s1.f.value.val = some g)
    (hd : ops.length = g.nres) (hg1 : segAt imps gs fid1 = some g1) (hl1 : ls1.length = g1.nloc)
    (hex1 : ex1.length = g1.ntmp) (hsuf1 : SufOf g1 ((s1, c1) :: r1))
    (hlive : (ex1.take (s1.d - s1.n)).reverse = live) (hn1 : s1.n ≤ s1.d)
    (hsig1 : (segEnv imps gs).sig s1.f.value.val = some (s1.n, s1.m))
    (hc1 : chainOk (segEnv imps gs).sig g1.nloc g1.nres (s1.d - s1.n + s1.m) c1 r1 = true) :
    SimS imps gs H (c, s) (yc, ys) := by
  have hm : g.nres = s1.m := (Prod.mk.inj (Option.some.inj ((sig_segAt hg).symm.trans hsig1))).2
  have hsrc : srcStep (segEnv imps gs) H (c, s) = .next (⟨⟨fid1, ls1, ops ++ live,
      c1 ++ flatCalls r1, g1.nres⟩ :: ss, c.globals, c.mem⟩, s) := by
    simp only [srcStep, step_ret hcs rfl, ret]
  have ht : step (spEnv imps gs) yc = .next ⟨⟨fid1, ls1 ++ ex1, ops, spillPost g1.nloc g1.maxD s1 ++
      c1 ++ spCalls g1.nloc g1.maxD r1, g1.nres⟩ :: ts, yc.globals, yc.mem⟩ := by
    rw [step_ret hct rfl]; simp [ret]
  have htop := TopS.after hg1 hl1 hex1 hsuf1 (hd.trans hm) hlive hn1 hc1
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  exact ⟨1, (⟨⟨fid1, ls1 ++ ex1, ops, spillPost g1.nloc g1.maxD s1 ++ c1 ++
    spCalls g1.nloc g1.maxD r1, g1.nres⟩ :: ts, yc.globals, yc.mem⟩, ys),
    by simp only [runN, srcStep, ht],
    ⟨hR.host, hR.globals, hR.mem, ⟨_, _, ss, ts, rfl, rfl, htop, hch'⟩⟩, Nat.one_pos⟩

/-- A frame at the end of its code returns. -/
theorem simS_ret {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid : Nat}
    {g : FnSeg} {ls ex ops : List W} (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨fid, ls, ops, [], g.nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, ops, [], g.nres⟩ :: tw)
    (hch : SChain imps gs fid sw tw) (hg : segAt imps gs fid = some g)
    (hd : ops.length = g.nres) : SimS imps gs H (c, s) (yc, ys) := by
  cases hch with
  | nil => exact simS_ret_bottom hR hcs hct
  | cons hw hch' =>
    cases hw with
    | mk hg1 hl1 hex1 hsuf1 hlive hn1 hsig1 hc1 =>
      exact simS_ret_wait hR hcs hct hch' hg hd hg1 hl1 hex1 hsuf1 hlive hn1 hsig1 hc1

/-- The target's code before a call: spill the operands, reload the arguments. -/
theorem steps_spillPre {fid : Nat} {g : FnSeg} {ls ex ops : List W} {s1 : Site} {K : List Instr}
    {tw : List Frame} {yg : List W} {ym : Nat → W} (hl : ls.length = g.nloc)
    (hex : ex.length = g.ntmp) (hw : ops.length = s1.d) (hn : s1.n ≤ s1.d) (hd : s1.d ≤ g.ntmp)
    (hB : g.nloc + g.ntmp < 2 ^ 32) :
    Steps (spEnv imps gs) (spillPre g.nloc s1).length
      ⟨⟨fid, ls ++ ex, ops, spillPre g.nloc s1 ++ K, g.nres⟩ :: tw, yg, ym⟩
      ⟨⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), ops.take s1.n, K, g.nres⟩ :: tw, yg, ym⟩ := by
  have h := spillPre_run (B := g.nloc) (s := s1) (ops := []) (gs := yg) (mem := ym) (ex := ex)
    hl hw hn (by omega) (by omega)
  have e := steps_seg (E := spEnv imps gs) (fr := ⟨fid, ls ++ ex, ops, [], g.nres⟩) (rest := tw)
    (code := K) (g := yg) (m := ym) (by simpa using h)
  simpa using e

/-- The live operands are the low part of the spilled ones. -/
theorem live_of_spill {ops ex : List W} {d n : Nat} (hw : ops.length = d) (hn : n ≤ d) :
    (((ops.reverse ++ ex.drop d).take (d - n)).reverse) = ops.drop n := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_reverse, List.reverse_reverse, hw,
    show d - (d - n) = n by omega]

end Silmaril.Wasm.FX.Asyncify.Tool
