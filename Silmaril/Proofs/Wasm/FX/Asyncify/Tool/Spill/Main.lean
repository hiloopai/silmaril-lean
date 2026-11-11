module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.Call

/-!
# The spill simulation: all cases, and the equality of behaviours
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type} {imps : List (Nat × Nat)} {gs : List FnSeg}

/-- A top frame inside a segment. -/
theorem simS_seg {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid : Nat}
    {g : FnSeg} {ls ex ops : List W} {q : List Instr} {r : List (Site × List Instr)}
    (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨fid, ls, ops, q ++ flatCalls r, g.nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, ops, q ++ spCalls g.nloc g.maxD r, g.nres⟩ :: tw)
    (hch : SChain imps gs fid sw tw) (hg : segAt imps gs fid = some g) (hl : ls.length = g.nloc)
    (hex : ex.length = g.ntmp) (hsuf : SufOf g r) (hok : SegOk imps gs)
    (hc : chainOk (segEnv imps gs).sig g.nloc g.nres ops.length q r = true) :
    SimS imps gs H (c, s) (yc, ys) := by
  cases q with
  | cons i q => exact simS_pure hR hcs hct hch hg hl hex hsuf hc
  | nil =>
    cases r with
    | nil => exact simS_ret hR hcs hct hch hg (chainOk_end hc)
    | cons x r =>
      obtain ⟨s1, c1⟩ := x
      by_cases hf : s1.f.value.val < imps.length
      · exact simS_call_imp hR hcs hct hch hg hl hex hsuf hok hc hf
      · exact simS_call_def hR hcs hct hch hg hl hex hsuf hok hc hf

/-- A top frame just after a call: the target reloads, then the segment continues. -/
theorem simS_after {H : Host σ} {c yc : Cfg} {s ys : σ} {sw tw : List Frame} {fid : Nat}
    {g : FnSeg} {ls ex vs live : List W} {s1 : Site} {c1 : List Instr}
    {r : List (Site × List Instr)} (hR : SRel imps gs (c, s) (yc, ys))
    (hcs : c.frames = ⟨fid, ls, vs ++ live, c1 ++ flatCalls r, g.nres⟩ :: sw)
    (hct : yc.frames = ⟨fid, ls ++ ex, vs, spillPost g.nloc g.maxD s1 ++ c1 ++
      spCalls g.nloc g.maxD r, g.nres⟩ :: tw)
    (hch : SChain imps gs fid sw tw) (hg : segAt imps gs fid = some g) (hl : ls.length = g.nloc)
    (hex : ex.length = g.ntmp) (hsuf : SufOf g ((s1, c1) :: r)) (hvs : vs.length = s1.m)
    (hlive : (ex.take (s1.d - s1.n)).reverse = live) (hn : s1.n ≤ s1.d)
    (hc : chainOk (segEnv imps gs).sig g.nloc g.nres (s1.d - s1.n + s1.m) c1 r = true)
    (hok : SegOk imps gs) : SimS imps gs H (c, s) (yc, ys) := by
  have hB : g.nloc + g.ntmp < 2 ^ 32 := hok.bound (segAt_mem hg).1
  have hD : s1.d ≤ g.maxD ∧ s1.m ≤ g.maxM := hsuf.bounds
  have hT : g.ntmp = g.maxD + g.maxM := rfl
  have hrun := spillPost_run (B := g.nloc) (D := g.maxD) (s := s1) (ops := []) (gs := yc.globals)
    (mem := yc.mem) (ex := ex) hl hvs (by omega) (by omega) (by omega)
  let ex2 := ovw ex g.maxD vs.reverse
  have e : Steps (spEnv imps gs) (spillPost g.nloc g.maxD s1).length
      ⟨⟨fid, ls ++ ex, vs, spillPost g.nloc g.maxD s1 ++ c1 ++ spCalls g.nloc g.maxD r, g.nres⟩ ::
        tw, yc.globals, yc.mem⟩
      ⟨⟨fid, ls ++ ex2, vs ++ live, c1 ++ spCalls g.nloc g.maxD r, g.nres⟩ :: tw, yc.globals,
        yc.mem⟩ := by
    have e0 := steps_seg (E := spEnv imps gs) (fr := ⟨fid, ls ++ ex, vs, [], g.nres⟩) (rest := tw)
      (code := c1 ++ spCalls g.nloc g.maxD r) (by simpa using hrun)
    simpa [hlive, ex2, List.append_assoc] using e0
  have hex2 : ex2.length = g.ntmp := by rw [ovw_length (by simp; omega)]; exact hex
  have hlen : (vs ++ live).length = s1.d - s1.n + s1.m := by
    rw [List.length_append, hvs, ← hlive, List.length_reverse, List.length_take]; omega
  have hc' : chainOk (segEnv imps gs).sig g.nloc g.nres (vs ++ live).length c1 r = true := by
    rw [hlen]; exact hc
  have hR' : SRel imps gs (c, s) (⟨⟨fid, ls ++ ex2, vs ++ live, c1 ++ spCalls g.nloc g.maxD r,
      g.nres⟩ :: tw, yc.globals, yc.mem⟩, ys) :=
    ⟨hR.host, hR.globals, hR.mem, ⟨_, _, sw, tw, hcs, rfl, .seg hg hl hex2 hsuf.tail hc', hch⟩⟩
  exact SimS.pre (by rw [cfg_eta hct]; exact e.src ys)
    (simS_seg hR' hcs rfl hch hg hl hex2 hsuf.tail hok hc')

/-- Every related pair satisfies the one-step obligation. -/
theorem simS_of_rel (hok : SegOk imps gs) {H : Host σ} {x y : Cfg × σ} (hR : SRel imps gs x y) :
    SimS imps gs H x y := by
  obtain ⟨c, s⟩ := x
  obtain ⟨yc, ys⟩ := y
  obtain ⟨s0, t0, sw, tw, hcs, hct, htop, hch⟩ := hR.frames
  cases htop with
  | seg hg hl hex hsuf hc => exact simS_seg hR hcs hct hch hg hl hex hsuf hok hc
  | after hg hl hex hsuf hvs hlive hn hc =>
    exact simS_after hR hcs hct hch hg hl hex hsuf hvs hlive hn hc hok

theorem isSimS (hok : SegOk imps gs) (H : Host σ) :
    IsSim (srcStep (segEnv imps gs) H) (srcStep (spEnv imps gs) H) (SRel imps gs) fun _ => 0 where
  stop := fun _ _ o hR h => (simS_of_rel hok hR).1 o h
  next := fun _ _ x' hR h => by
    obtain ⟨n, y', h1, h2, h3⟩ := (simS_of_rel hok hR).2 x' h
    exact ⟨n, y', h1, h2, Or.inl h3⟩

theorem srcInit_segEnv {e : Nat} {g : FnSeg} (hg : segAt imps gs e = some g) (args : List W) :
    srcInit (segEnv imps gs) e args = some ⟨[entry e g.toDef args], [], fun _ => 0⟩ := by
  have hge := (segAt_mem hg).2
  simp only [srcInit, show (segEnv imps gs).imps.length ≤ e from hge, ↓reduceIte, segAt_src hg,
    Option.map_some]

theorem srcInit_spEnv {e : Nat} {g : FnSeg} (hg : segAt imps gs e = some g) (args : List W) :
    srcInit (spEnv imps gs) e args = some ⟨[entry e g.spDef args], [], fun _ => 0⟩ := by
  have hge := (segAt_mem hg).2
  simp only [srcInit, show (spEnv imps gs).imps.length ≤ e from hge, ↓reduceIte, segAt_tgt hg,
    Option.map_some]

/-- **The spill is correct**: a call of a defined function of the segmented program and the same
call of the spilled program have the same behaviours (results with the final host state, traps,
divergence), for every deterministic host. -/
theorem spill_beh (hok : SegOk imps gs) (H : Host σ) {e : Nat} {g : FnSeg}
    (hg : segAt imps gs e = some g) (args : List W) (hargs : args.length = g.nparams) (s : σ) :
    beh (srcStep (segEnv imps gs) H) (⟨[entry e g.toDef args], [], fun _ => 0⟩, s) =
      beh (srcStep (spEnv imps gs) H) (⟨[entry e g.spDef args], [], fun _ => 0⟩, s) :=
  beh_eq_of_sim (isSimS hok H)
    ⟨rfl, rfl, rfl, ⟨_, _, [], [], rfl, rfl, TopS.ofEntry hok hg hargs, .nil _⟩⟩

end Silmaril.Wasm.FX.Asyncify.Tool
