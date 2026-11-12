module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.Main
public import Silmaril.Wasm.FX.Asyncify.Tool.Elide.Thms

/-!
# The tool on the wider fragment: reading the segmented form, the output module, end to end
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem segmentEnv_sound {E : Env} {gs : List FnSeg} (h : segmentEnv E = some gs) :
    E = segEnv E.imps gs ∧ SegOk E.imps gs := by
  unfold segmentEnv at h
  cases hm : E.fns.mapM (segFn E.sig) with
  | none => simp [hm] at h
  | some gs' =>
    have h' : (fnDefsEqb (gs'.map FnSeg.toDef) E.fns = true ∧ ∀ x ∈ gs', x.ok E.sig = true) ∧
        gs' = gs := by simpa [hm] using h
    have hE : E = segEnv E.imps gs := by
      cases E; simp [segEnv, ← h'.2, fnDefsEqb_sound h'.1.1]
    refine ⟨hE, fun g hg => ?_⟩
    rw [← hE]
    exact h'.1.2 g (h'.2 ▸ hg)

/-- A function of the module, read as a machine function, read back after the pass. -/
theorem fnDefOf_async {m : Module} {P : Prog} {pages : Nat} {f : Func} {d : FnDef} {fn : FnSrc}
    (h : fnDefOf m f = some d) (hp : d.nparams = fn.nparams) (hr : d.nres = fn.nres) :
    fnDefOf (asyncifyModule m P pages)
      ⟨f.type, List.replicate (P.frameWords - fn.nparams) .i32, P.tBody fn⟩ =
      some ⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ := by
  unfold fnDefOf at h ⊢
  rw [i32Sig_async]
  cases hs : i32Sig m f.type with
  | none => rw [hs] at h; cases h
  | some nr =>
    rw [hs] at h
    simp only at h
    split at h
    · have hd := (Option.some.inj h).symm
      rw [hd] at hp hr
      simp [← hp, ← hr]
    · cases h

theorem fns_async_of {m : Module} {P : Prog} {pages : Nat} :
    ∀ {fs : List Func} {ds : List FnDef} {fns : List FnSrc},
      List.Forall₂ (fun f d => fnDefOf m f = some d) fs ds →
      List.Forall₂ (fun d fn => d.nparams = fn.nparams ∧ d.nres = fn.nres) ds fns →
      List.Forall₂ (fun f d => fnDefOf (asyncifyModule m P pages) f = some d)
        ((fs.zip fns).map fun (f, fn) => (⟨f.type, List.replicate (P.frameWords - fn.nparams) .i32,
          P.tBody fn⟩ : Func))
        (fns.map fun fn => (⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ : FnDef))
  | [], [], [], _, _ => by simp
  | f :: fs, d :: ds, fn :: fns, .cons h1 h2, .cons k1 k2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.forall₂_cons]
    exact ⟨fnDefOf_async h1 k1.1 k1.2, fns_async_of h2 k2⟩
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | _, [], _ :: _, _, h => by cases h
  | _, _ :: _, [], _, h => by cases h

/-- The output module read back, for a program `P` with the module's signatures. -/
theorem envOfLax_asyncifyModule_of {m : Module} {E : Env} {P : Prog} (h : envOf m = some E)
    (himps : E.imps = P.imps)
    (hfns : List.Forall₂ (fun d fn => d.nparams = fn.nparams ∧ d.nres = fn.nres) E.fns P.fns)
    (pages : Nat) : envOfLax (asyncifyModule m P pages) = some (asyncifyProg P) := by
  obtain ⟨-, hi, hf⟩ := envOf_parts h
  have hfil := filter_funcs_of_mapM hi
  have hfns' : ((m.funcs.zip P.fns).map fun (f, fn) => (⟨f.type, List.replicate (P.frameWords -
      fn.nparams) .i32, P.tBody fn⟩ : Func)).mapM (fnDefOf (asyncifyModule m P pages)) =
      some (P.fns.map fun fn => (⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ :
        FnDef)) :=
    (List.mapM_eq_some_iff_forall₂).2 (fns_async_of ((List.mapM_eq_some_iff_forall₂).1 hf) hfns)
  have hi' : m.imports.mapM (impSig (asyncifyModule m P pages)) = some P.imps := by
    rw [← himps]; exact hi
  have hI : (asyncifyModule m P pages).imports = m.imports := rfl
  have hF : (asyncifyModule m P pages).funcs = (m.funcs.zip P.fns).map fun (f, fn) =>
      (⟨f.type, List.replicate (P.frameWords - fn.nparams) .i32, P.tBody fn⟩ : Func) := rfl
  unfold envOfLax
  rw [hI, hfil, hi', hF, hfns']
  rfl

theorem forall₂_sig_self (P : Prog) :
    List.Forall₂ (fun d fn => d.nparams = fn.nparams ∧ d.nres = fn.nres) P.env.fns P.fns := by
  simp only [Prog.env]
  induction P.fns with
  | nil => exact .nil
  | cons fn fns ih => exact .cons ⟨rfl, rfl⟩ ih

/-! ## The pass on the segmented form -/

/-- The last checks of `asyncifyS`, once the module is read and segmented. -/
theorem asyncifyS_ok {m m' : Module} {pages : Nat} {E : Env} {gs : List FnSeg}
    (hE : envOf m = some E) (hgs : segmentEnv E = some gs) (h : asyncifyS m pages = .ok m') :
    (envEqb (progOf (spEnv E.imps gs)).env (spEnv E.imps gs) && (progOf (spEnv E.imps gs)).wf) =
      true ∧ m' = asyncifyModule m (progOf (spEnv E.imps gs)).elide pages := by
  unfold asyncifyS at h
  simp only [hE, hgs] at h
  by_cases hc : (envEqb (progOf (spEnv E.imps gs)).env (spEnv E.imps gs) &&
    (progOf (spEnv E.imps gs)).wf) = true
  · refine ⟨hc, ?_⟩
    simp only [hc, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · exact (Except.ok.inj h).symm
      · cases h
  · simp [hc] at h

theorem asyncifyS_eq {m m' : Module} {pages : Nat} (h : asyncifyS m pages = .ok m') :
    ∃ E gs, envOf m = some E ∧ segmentEnv E = some gs ∧
      (progOf (spEnv E.imps gs)).env = spEnv E.imps gs ∧ (progOf (spEnv E.imps gs)).WF ∧
      m' = asyncifyModule m (progOf (spEnv E.imps gs)).elide pages := by
  cases hE : envOf m with
  | none => simp [asyncifyS, hE] at h
  | some E =>
    cases hgs : segmentEnv E with
    | none => simp [asyncifyS, hE, hgs] at h
    | some gs =>
      obtain ⟨hc, hm'⟩ := asyncifyS_ok hE hgs h
      simp only [Bool.and_eq_true] at hc
      exact ⟨E, gs, rfl, hgs, envEqb_sound hc.1, hc.2, hm'⟩

/-- The spilled statement-form program has the signatures of the segmented one. -/
theorem forall₂_sig_spill {imps : List (Nat × Nat)} {gs : List FnSeg} {P : Prog}
    (hP : P.env = spEnv imps gs) :
    List.Forall₂ (fun d fn => d.nparams = fn.nparams ∧ d.nres = fn.nres) (segEnv imps gs).fns
      P.fns := by
  have h := forall₂_sig_self P
  rw [hP] at h
  have h' : List.Forall₂ (fun g fn => g.spDef.nparams = fn.nparams ∧ g.spDef.nres = fn.nres)
      gs P.fns := List.forall₂_map_left_iff.1 h
  show List.Forall₂ _ (gs.map FnSeg.toDef) P.fns
  exact List.forall₂_map_left_iff.2 (h'.imp fun _ _ hx => hx)

theorem fnAt_spill {imps : List (Nat × Nat)} {gs : List FnSeg} {P : Prog}
    (hP : P.env = spEnv imps gs) {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn) :
    ∃ g, segAt imps gs e = some g ∧ g.spDef = ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ := by
  have h1 := Prog.env_fn hfn
  have hge := Prog.fnAt_ge hfn
  have himps : P.imps = imps := by
    have := congrArg Env.imps hP; simpa [Prog.env, spEnv] using this
  have hge' : imps.length ≤ e := himps ▸ hge
  rw [hP] at h1
  simp only [spEnv, List.getElem?_map] at h1
  cases hg : gs[e - imps.length]? with
  | none => rw [hg] at h1; cases h1
  | some g =>
    rw [hg] at h1
    exact ⟨g, by simp [segAt, hge', hg], Option.some.inj h1⟩

/-- **The pass on the segmented form is correct**: for the module's machine program `E` and the
spilled statement-form program `P`, every call has the same behaviours in `E` (suspending) and
in the asyncified `P.elide` (asyncify protocol), when the shadow stack of `P`'s runs fits in
32 bits. -/
theorem asyncifyS_beh {E : Env} {gs : List FnSeg}
    (hgs : segmentEnv E = some gs) {P : Prog} (hP : P.env = spEnv E.imps gs) (hwf : P.WF)
    {σ : Type} (H : Host σ) {e : Nat} {fn : FnSrc} (args : List W) (s : σ)
    (hfn : P.fnAt e = some fn) (hargs : args.length = fn.nparams)
    (hb : DepthBound P H (srcCfg e fn args, s)) :
    ∃ c, srcInit E e args = some c ∧
      beh (srcStep E H) (c, s) = beh (tgtStep (asyncifyProg P.elide) H) (tgtSt P.elide e fn.elide args s) := by
  obtain ⟨hEq, hok⟩ := segmentEnv_sound hgs
  obtain ⟨g, hg, hgd⟩ := fnAt_spill hP hfn
  have hnp : g.nparams = fn.nparams := congrArg FnDef.nparams hgd
  have hsrc : srcCfg e fn args = ⟨[entry e g.spDef args], [], fun _ => 0⟩ := by
    rw [hgd]; rfl
  have h1 := spill_beh hok H hg args (by omega) s
  have h2 := asyncify_elide_beh P hwf H hfn args hargs s hb
  rw [hP, hsrc] at h2
  refine ⟨_, by rw [hEq]; exact srcInit_segEnv hg args, ?_⟩
  rw [hEq]
  exact h1.trans h2

end Silmaril.Wasm.FX.Asyncify.Tool
