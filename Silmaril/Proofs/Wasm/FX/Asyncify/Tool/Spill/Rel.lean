module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.Code

/-!
# The simulation relation of the spill

The source is the segmented program `segEnv imps gs`, the target the spilled `spEnv imps gs`,
both on the frame machine. A top frame (`TopS`) is inside pure code (`seg`: same code prefix,
same operands, the target's temporaries arbitrary) or just after a call (`after`: the source has
the results on top of the live operands, the target only the results, the live operands being in
its temporaries). A frame below (`WaitS`) waits on a call site with its live operands in its
temporaries.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- The segmented function at function index `fid`. -/
def segAt (imps : List (Nat × Nat)) (gs : List FnSeg) (fid : Nat) : Option FnSeg :=
  if imps.length ≤ fid then gs[fid - imps.length]? else none

/-- `r` is what is left of the call sites of `g`. -/
def SufOf (g : FnSeg) (r : List (Site × List Instr)) : Prop := ∃ pre, g.calls = pre ++ r

/-- The depth `chainOk` asks for at the end of the pure code before the sites `r`. -/
def nextD (nres : Nat) : List (Site × List Instr) → Nat
  | [] => nres
  | (s, _) :: _ => s.d

/-- The checks of the sites `r` themselves. -/
def sitesOk (sig : Nat → Option (Nat × Nat)) (B nres : Nat) : List (Site × List Instr) → Bool
  | [] => true
  | (s, c) :: r => sig s.f.value.val == some (s.n, s.m) && decide (s.n ≤ s.d) &&
      chainOk sig B nres (s.d - s.n + s.m) c r

theorem chainOk_eq (sig : Nat → Option (Nat × Nat)) (B nres d : Nat) (q : List Instr) :
    ∀ r, chainOk sig B nres d q r =
      (q.all (pureIns B) && depthAfter q d == some (nextD nres r) && sitesOk sig B nres r)
  | [] => by simp [chainOk, nextD, sitesOk]
  | (s, c) :: r => by simp [chainOk, nextD, sitesOk, Bool.and_assoc]

/-- The facts of `chainOk` before a site. -/
theorem chainOk_site {sig : Nat → Option (Nat × Nat)} {B nres d : Nat} {s : Site}
    {c : List Instr} {r : List (Site × List Instr)}
    (h : chainOk sig B nres d [] ((s, c) :: r) = true) :
    d = s.d ∧ sig s.f.value.val = some (s.n, s.m) ∧ s.n ≤ s.d ∧
      chainOk sig B nres (s.d - s.n + s.m) c r = true := by
  simp only [chainOk, List.all_nil, depthAfter, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
    Option.some.injEq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem chainOk_end {sig : Nat → Option (Nat × Nat)} {B nres d : Nat}
    (h : chainOk sig B nres d [] [] = true) : d = nres := by
  simpa [chainOk, depthAfter] using h

/-- A pure step keeps `chainOk`. -/
theorem chainOk_cons {sig : Nat → Option (Nat × Nat)} {B nres : Nat} {i : Instr}
    {q : List Instr} {r : List (Site × List Instr)} {ls ops ls' ops' : List W}
    (h : chainOk sig B nres ops.length (i :: q) r = true) :
    PureShape B i ∧ (pexec i ls ops = some (ls', ops') →
      chainOk sig B nres ops'.length q r = true) := by
  rw [chainOk_eq] at h
  simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
  have hi : PureShape B i := pureShape h.1.1.1
  refine ⟨hi, fun he => ?_⟩
  rw [chainOk_eq]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨h.1.1.2, depthAfter_cons hi h.1.2 he⟩, h.2⟩

theorem segAt_mem {imps : List (Nat × Nat)} {gs : List FnSeg} {fid : Nat} {g : FnSeg}
    (h : segAt imps gs fid = some g) : g ∈ gs ∧ imps.length ≤ fid := by
  unfold segAt at h
  split at h
  · exact ⟨List.mem_of_getElem? h, by assumption⟩
  · cases h

theorem segAt_src {imps : List (Nat × Nat)} {gs : List FnSeg} {fid : Nat} {g : FnSeg}
    (h : segAt imps gs fid = some g) :
    (segEnv imps gs).fns[fid - (segEnv imps gs).imps.length]? = some g.toDef := by
  unfold segAt at h
  split at h
  · simp [segEnv, h]
  · cases h

theorem segAt_tgt {imps : List (Nat × Nat)} {gs : List FnSeg} {fid : Nat} {g : FnSeg}
    (h : segAt imps gs fid = some g) :
    (spEnv imps gs).fns[fid - (spEnv imps gs).imps.length]? = some g.spDef := by
  unfold segAt at h
  split at h
  · simp [spEnv, h]
  · cases h

theorem sig_segAt {imps : List (Nat × Nat)} {gs : List FnSeg} {fid : Nat} {g : FnSeg}
    (h : segAt imps gs fid = some g) : (segEnv imps gs).sig fid = some (g.nparams, g.nres) := by
  have hge := (segAt_mem h).2
  have hs := segAt_src h
  unfold Env.sig
  rw [dite_eq_right (by simp only [segEnv]; omega), hs]
  rfl

theorem sig_def {imps : List (Nat × Nat)} {gs : List FnSeg} {f n m : Nat}
    (h : (segEnv imps gs).sig f = some (n, m)) (hf : ¬ f < imps.length) :
    ∃ g, segAt imps gs f = some g ∧ g.nparams = n ∧ g.nres = m := by
  unfold Env.sig at h
  rw [dite_eq_right (by simp only [segEnv]; omega)] at h
  cases hg : gs[f - imps.length]? with
  | none => simp [segEnv, hg] at h
  | some g =>
    simp only [segEnv, List.getElem?_map, hg, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    exact ⟨g, by simp [segAt, show imps.length ≤ f by omega, hg], h.1, h.2⟩

theorem sig_imp {imps : List (Nat × Nat)} {gs : List FnSeg} {f n m : Nat}
    (h : (segEnv imps gs).sig f = some (n, m)) (hf : f < imps.length) : imps[f] = (n, m) := by
  unfold Env.sig at h
  rw [dite_eq_left (by simp only [segEnv]; omega)] at h
  simpa [segEnv] using h

theorem SufOf.tail {g : FnSeg} {x : Site × List Instr} {r : List (Site × List Instr)}
    (h : SufOf g (x :: r)) : SufOf g r := by
  obtain ⟨pre, hp⟩ := h
  exact ⟨pre ++ [x], by rw [hp]; simp⟩

theorem SufOf.bounds {g : FnSeg} {s : Site} {c : List Instr} {r : List (Site × List Instr)}
    (h : SufOf g ((s, c) :: r)) : s.d ≤ g.maxD ∧ s.m ≤ g.maxM := by
  obtain ⟨pre, hp⟩ := h
  have hm : (s, c) ∈ g.calls := by rw [hp]; simp
  exact ⟨foldr_max_ge (List.mem_map_of_mem (f := fun x => x.1.d) hm),
    foldr_max_ge (List.mem_map_of_mem (f := fun x => x.1.m) hm)⟩

/-- The checks of every segmented function. -/
def SegOk (imps : List (Nat × Nat)) (gs : List FnSeg) : Prop :=
  ∀ g ∈ gs, g.ok (segEnv imps gs).sig = true

theorem SegOk.chain {imps : List (Nat × Nat)} {gs : List FnSeg} (hok : SegOk imps gs) {g : FnSeg}
    (hg : g ∈ gs) : chainOk (segEnv imps gs).sig g.nloc g.nres 0 g.c0 g.calls = true := by
  have h := hok g hg
  simp only [FnSeg.ok, Bool.and_eq_true] at h
  exact h.1

theorem SegOk.bound {imps : List (Nat × Nat)} {gs : List FnSeg} (hok : SegOk imps gs) {g : FnSeg}
    (hg : g ∈ gs) : g.nloc + g.ntmp < 2 ^ 32 := by
  have h := hok g hg
  simp only [FnSeg.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ## The relation -/

/-- Top frames. -/
inductive TopS (imps : List (Nat × Nat)) (gs : List FnSeg) : Frame → Frame → Prop
  | seg {fid : Nat} {g : FnSeg} {ls ex ops : List W} {q : List Instr}
      {r : List (Site × List Instr)} :
      segAt imps gs fid = some g → ls.length = g.nloc → ex.length = g.ntmp → SufOf g r →
      chainOk (segEnv imps gs).sig g.nloc g.nres ops.length q r = true →
      TopS imps gs ⟨fid, ls, ops, q ++ flatCalls r, g.nres⟩
        ⟨fid, ls ++ ex, ops, q ++ spCalls g.nloc g.maxD r, g.nres⟩
  | after {fid : Nat} {g : FnSeg} {ls ex vs live : List W} {s : Site} {c : List Instr}
      {r : List (Site × List Instr)} :
      segAt imps gs fid = some g → ls.length = g.nloc → ex.length = g.ntmp →
      SufOf g ((s, c) :: r) → vs.length = s.m → (ex.take (s.d - s.n)).reverse = live →
      s.n ≤ s.d → chainOk (segEnv imps gs).sig g.nloc g.nres (s.d - s.n + s.m) c r = true →
      TopS imps gs ⟨fid, ls, vs ++ live, c ++ flatCalls r, g.nres⟩
        ⟨fid, ls ++ ex, vs, spillPost g.nloc g.maxD s ++ c ++ spCalls g.nloc g.maxD r, g.nres⟩

/-- A frame waiting on call site `s` (to function `s.f`). -/
inductive WaitS (imps : List (Nat × Nat)) (gs : List FnSeg) : Nat → Frame → Frame → Prop
  | mk {fid : Nat} {g : FnSeg} {ls ex live : List W} {s : Site} {c : List Instr}
      {r : List (Site × List Instr)} :
      segAt imps gs fid = some g → ls.length = g.nloc → ex.length = g.ntmp →
      SufOf g ((s, c) :: r) → (ex.take (s.d - s.n)).reverse = live → s.n ≤ s.d →
      (segEnv imps gs).sig s.f.value.val = some (s.n, s.m) →
      chainOk (segEnv imps gs).sig g.nloc g.nres (s.d - s.n + s.m) c r = true →
      WaitS imps gs s.f.value.val ⟨fid, ls, live, c ++ flatCalls r, g.nres⟩
        ⟨fid, ls ++ ex, [], spillPost g.nloc g.maxD s ++ c ++ spCalls g.nloc g.maxD r, g.nres⟩

/-- The frames below the top, each waiting on a call of the frame above it. -/
inductive SChain (imps : List (Nat × Nat)) (gs : List FnSeg) : Nat → List Frame → List Frame → Prop
  | nil (a : Nat) : SChain imps gs a [] []
  | cons {a : Nat} {fs ft : Frame} {ss ts : List Frame} :
      WaitS imps gs a fs ft → SChain imps gs fs.fid ss ts → SChain imps gs a (fs :: ss) (ft :: ts)

/-- The simulation relation of the closed systems. -/
structure SRel {σ : Type} (imps : List (Nat × Nat)) (gs : List FnSeg) (x y : Cfg × σ) : Prop where
  host : y.2 = x.2
  globals : y.1.globals = x.1.globals
  mem : y.1.mem = x.1.mem
  frames : ∃ s0 t0 sw tw, x.1.frames = s0 :: sw ∧ y.1.frames = t0 :: tw ∧ TopS imps gs s0 t0 ∧
    SChain imps gs s0.fid sw tw

/-- The one-step obligation. -/
def SimS {σ : Type} (imps : List (Nat × Nat)) (gs : List FnSeg) (H : Host σ) (x y : Cfg × σ) :
    Prop :=
  (∀ o, srcStep (segEnv imps gs) H x = .stop o →
    ∃ n, runN (srcStep (spEnv imps gs) H) n y = .stop o) ∧
  (∀ x', srcStep (segEnv imps gs) H x = .next x' →
    ∃ n y', runN (srcStep (spEnv imps gs) H) n y = .next y' ∧ SRel imps gs x' y' ∧ 0 < n)

theorem SimS.pre {σ : Type} {imps : List (Nat × Nat)} {gs : List FnSeg} {H : Host σ}
    {x y y' : Cfg × σ} {k : Nat} (h : runN (srcStep (spEnv imps gs) H) k y = .next y')
    (hok : SimS imps gs H x y') : SimS imps gs H x y := by
  refine ⟨fun o ho => ?_, fun x' hx => ?_⟩
  · obtain ⟨n, hn⟩ := hok.1 o ho
    exact ⟨k + n, by rw [runN_add_next h]; exact hn⟩
  · obtain ⟨n, y'', hn, hR, hpos⟩ := hok.2 x' hx
    exact ⟨k + n, y'', by rw [runN_add_next h]; exact hn, hR, by omega⟩

end Silmaril.Wasm.FX.Asyncify.Tool
