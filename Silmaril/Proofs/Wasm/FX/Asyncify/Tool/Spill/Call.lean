module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.Step

/-!
# The spill simulation: call sites
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type} {imps : List (Nat × Nat)} {gs : List FnSeg}

/-- A call of an import whose arguments are on top of the stack. -/
theorem step_imp_args {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {f : FuncIdx}
    {K : List Instr} {args low : List W} {n m : Nat} (hf : c.frames = fr :: rest)
    (hcode : fr.code = .call f :: K) (hops : fr.ops = args.reverse ++ low)
    (himp : f.value.val < E.imps.length) (hi : E.imps[f.value.val] = (n, m))
    (hn : args.length = n) :
    step E c = .ask f.value.val args ⟨{ fr with ops := low, code := K } :: rest, c.globals, c.mem⟩ := by
  have htk : fr.ops.take n = args.reverse := by rw [hops, ← hn]; exact List.take_left' (by simp)
  have hdr : fr.ops.drop n = low := by rw [hops, ← hn]; exact List.drop_left' (by simp)
  rw [step_call_imp hf hcode himp (by rw [hi, hops, ← hn]; simp), hi]
  simp only [htk, hdr, List.reverse_reverse]

/-- The pair of a configuration and a host state is the configuration with its parts. -/
theorem cfg_eta {yc : Cfg} {fs : List Frame} (h : yc.frames = fs) : yc = ⟨fs, yc.globals, yc.mem⟩ := by
  rw [← h]

/-- A call site to an import: the source asks, the target spills, asks, and both push the answer. -/
theorem simS_call_imp {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid : Nat}
    {g : FnSeg} {ls ex ops : List W} {s1 : Site} {c1 : List Instr} {r : List (Site × List Instr)}
    (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨fid, ls, ops, .call s1.f :: (c1 ++ flatCalls r), g.nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, ops, spillPre g.nloc s1 ++ .call s1.f ::
      (spillPost g.nloc g.maxD s1 ++ c1 ++ spCalls g.nloc g.maxD r), g.nres⟩ :: tw)
    (hch : SChain imps gs fid sw tw) (hg : segAt imps gs fid = some g) (hl : ls.length = g.nloc)
    (hex : ex.length = g.ntmp) (hsuf : SufOf g ((s1, c1) :: r)) (hok : SegOk imps gs)
    (hc : chainOk (segEnv imps gs).sig g.nloc g.nres ops.length [] ((s1, c1) :: r) = true)
    (hf : s1.f.value.val < imps.length) : SimS imps gs H (c, s) (yc, ys) := by
  obtain ⟨hd, hsig, hn, hc1⟩ := chainOk_site hc
  have himp : imps[s1.f.value.val] = (s1.n, s1.m) := sig_imp hsig hf
  have hB : g.nloc + g.ntmp < 2 ^ 32 := hok.bound (segAt_mem hg).1
  have hD : s1.d ≤ g.maxD ∧ s1.m ≤ g.maxM := hsuf.bounds
  have hys : ys = s := hR.host
  let args := (ops.take s1.n).reverse
  let ans := H.answer s s1.f.value.val args
  let K := spillPost g.nloc g.maxD s1 ++ c1 ++ spCalls g.nloc g.maxD r
  have hT : g.ntmp = g.maxD + g.maxM := rfl
  have hargs : args.length = s1.n := by simp [args]; omega
  have hops : ops = args.reverse ++ ops.drop s1.n := by simp [args]
  have hm : (((segEnv imps gs).imps[s1.f.value.val]?).map Prod.snd).getD 0 = s1.m := by
    simp [segEnv, List.getElem?_eq_getElem hf, himp]
  have hm' : (((spEnv imps gs).imps[s1.f.value.val]?).map Prod.snd).getD 0 = s1.m := by
    simp [spEnv, List.getElem?_eq_getElem hf, himp]
  have hs : step (segEnv imps gs) c = .ask s1.f.value.val args
      ⟨⟨fid, ls, ops.drop s1.n, c1 ++ flatCalls r, g.nres⟩ :: sw, c.globals, c.mem⟩ :=
    step_imp_args hcs rfl hops hf himp hargs
  have hsrc : srcStep (segEnv imps gs) H (c, s) = .next (⟨⟨fid, ls,
      (fit s1.m ans.2).reverse ++ ops.drop s1.n, c1 ++ flatCalls r, g.nres⟩ :: sw, c.globals,
      c.mem⟩, ans.1) := by
    simp only [srcStep, hs, hm, pushTop]
    rfl
  have e1 := steps_spillPre (imps := imps) (gs := gs) (fid := fid) (K := .call s1.f :: K) (tw := tw)
    (yg := yc.globals) (ym := yc.mem) hl hex hd hn (by unfold FnSeg.ntmp; omega) hB
  have e2 : step (spEnv imps gs) ⟨⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), ops.take s1.n, .call s1.f :: K, g.nres⟩ :: tw,
      yc.globals, yc.mem⟩ = .ask s1.f.value.val args
        ⟨⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), [], K, g.nres⟩ :: tw, yc.globals, yc.mem⟩ :=
    step_imp_args (E := spEnv imps gs) (fr := ⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), ops.take s1.n, .call s1.f :: K, g.nres⟩)
      (args := args) (low := []) rfl rfl (by simp [args]) hf himp hargs
  have htgt : runN (srcStep (spEnv imps gs) H) ((spillPre g.nloc s1).length + 1) (yc, ys) =
      .next (⟨⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), (fit s1.m ans.2).reverse, K, g.nres⟩ :: tw, yc.globals, yc.mem⟩,
        ans.1) := by
    rw [cfg_eta hct, runN_add_next (e1.src ys)]
    simp only [runN, srcStep, e2, hm', pushTop, hys, List.append_nil]
    rfl
  have hex1 : (ops.reverse ++ ex.drop s1.d).length = g.ntmp := by simp; omega
  have htop := TopS.after (vs := (fit s1.m ans.2).reverse) hg hl hex1 hsuf (by simp [fit])
    (live_of_spill hd hn) hn hc1
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  exact ⟨_, _, htgt, ⟨rfl, hR.globals, hR.mem, ⟨_, _, sw, tw, rfl, rfl, htop, hch⟩⟩, by omega⟩

/-- The source and spilled entry frames of a call. -/
theorem TopS.ofEntry (hok : SegOk imps gs) {f : Nat} {g : FnSeg} (hg : segAt imps gs f = some g)
    {args : List W} (hargs : args.length = g.nparams) :
    TopS imps gs (entry f g.toDef args) (entry f g.spDef args) := by
  have h := TopS.seg (ls := args ++ List.replicate g.nlocals 0) (ex := List.replicate g.ntmp 0)
    (ops := []) (q := g.c0) (r := g.calls) hg (by simp [FnSeg.nloc, hargs]) (by simp) ⟨[], rfl⟩
    (hok.chain (segAt_mem hg).1)
  have hloc : args ++ List.replicate (g.nlocals + g.ntmp) (0 : W) =
      (args ++ List.replicate g.nlocals 0) ++ List.replicate g.ntmp 0 := by
    rw [List.replicate_add, List.append_assoc]
  show TopS imps gs ⟨f, args ++ List.replicate g.nlocals 0, [], g.c0 ++ flatCalls g.calls, g.nres⟩
    ⟨f, args ++ List.replicate (g.nlocals + g.ntmp) 0, [], g.c0 ++ spCalls g.nloc g.maxD g.calls,
      g.nres⟩
  rw [hloc]
  exact h

/-- A call site to a defined function: both push the callee's entry frame. -/
theorem simS_call_def {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid : Nat}
    {g : FnSeg} {ls ex ops : List W} {s1 : Site} {c1 : List Instr} {r : List (Site × List Instr)}
    (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨fid, ls, ops, .call s1.f :: (c1 ++ flatCalls r), g.nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, ops, spillPre g.nloc s1 ++ .call s1.f ::
      (spillPost g.nloc g.maxD s1 ++ c1 ++ spCalls g.nloc g.maxD r), g.nres⟩ :: tw)
    (hch : SChain imps gs fid sw tw) (hg : segAt imps gs fid = some g) (hl : ls.length = g.nloc)
    (hex : ex.length = g.ntmp) (hsuf : SufOf g ((s1, c1) :: r)) (hok : SegOk imps gs)
    (hc : chainOk (segEnv imps gs).sig g.nloc g.nres ops.length [] ((s1, c1) :: r) = true)
    (hf : ¬ s1.f.value.val < imps.length) : SimS imps gs H (c, s) (yc, ys) := by
  obtain ⟨hd, hsig, hn, hc1⟩ := chainOk_site hc
  obtain ⟨g', hg', hnp, -⟩ := sig_def hsig hf
  have hB : g.nloc + g.ntmp < 2 ^ 32 := hok.bound (segAt_mem hg).1
  have hD : s1.d ≤ g.maxD ∧ s1.m ≤ g.maxM := hsuf.bounds
  let args := (ops.take s1.n).reverse
  let K := spillPost g.nloc g.maxD s1 ++ c1 ++ spCalls g.nloc g.maxD r
  have hT : g.ntmp = g.maxD + g.maxM := rfl
  have hargs : args.length = s1.n := by simp [args]; omega
  have hops : ops = args.reverse ++ ops.drop s1.n := by simp [args]
  have hs : step (segEnv imps gs) c = .next ⟨entry s1.f.value.val g'.toDef args ::
      ⟨fid, ls, ops.drop s1.n, c1 ++ flatCalls r, g.nres⟩ :: sw, c.globals, c.mem⟩ :=
    step_call_args hcs rfl hops (by simpa [segEnv] using hf) (segAt_src hg')
      (by simp [FnSeg.toDef, hnp, hargs])
  have hsrc : srcStep (segEnv imps gs) H (c, s) = .next (⟨entry s1.f.value.val g'.toDef args ::
      ⟨fid, ls, ops.drop s1.n, c1 ++ flatCalls r, g.nres⟩ :: sw, c.globals, c.mem⟩, s) := by
    simp only [srcStep, hs]
  have e1 := steps_spillPre (imps := imps) (gs := gs) (fid := fid) (K := .call s1.f :: K) (tw := tw)
    (yg := yc.globals) (ym := yc.mem) hl hex hd hn (by unfold FnSeg.ntmp; omega) hB
  have e2 : step (spEnv imps gs) ⟨⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), ops.take s1.n, .call s1.f :: K, g.nres⟩ :: tw,
      yc.globals, yc.mem⟩ = .next ⟨entry s1.f.value.val g'.spDef args ::
        ⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), [], K, g.nres⟩ :: tw, yc.globals, yc.mem⟩ :=
    step_call_args (E := spEnv imps gs)
      (fr := ⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), ops.take s1.n, .call s1.f :: K, g.nres⟩) (args := args) (low := [])
      rfl rfl (by simp [args]) (by simpa [spEnv] using hf) (segAt_tgt hg')
      (by simp [FnSeg.spDef, hnp, hargs])
  have htgt : runN (srcStep (spEnv imps gs) H) ((spillPre g.nloc s1).length + 1) (yc, ys) =
      .next (⟨entry s1.f.value.val g'.spDef args :: ⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), [], K, g.nres⟩ :: tw,
        yc.globals, yc.mem⟩, ys) := by
    rw [cfg_eta hct, runN_add_next (e1.src ys)]
    simp only [runN, srcStep, e2]
  have hex1 : (ops.reverse ++ ex.drop s1.d).length = g.ntmp := by simp; omega
  have hw : WaitS imps gs s1.f.value.val ⟨fid, ls, ops.drop s1.n, c1 ++ flatCalls r, g.nres⟩
      ⟨fid, ls ++ (ops.reverse ++ ex.drop s1.d), [], K, g.nres⟩ :=
    .mk hg hl hex1 hsuf (live_of_spill hd hn) hn hsig hc1
  have htop := TopS.ofEntry hok hg' (show args.length = g'.nparams by omega)
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  exact ⟨_, _, htgt, ⟨hR.host, hR.globals, hR.mem, ⟨_, _, _, _, rfl, rfl, htop, .cons hw hch⟩⟩,
    by omega⟩

end Silmaril.Wasm.FX.Asyncify.Tool
