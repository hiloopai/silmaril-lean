module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.SuspendSim

/-!
# The simulation, all cases, and the correctness of the pass

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/Main.lean` and restyled: the case split
of `simOk_of_rel` is `sim_top_run`, `sim_stmt` and `sim_open_pure`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- A call statement, while or after its arguments are read. -/
theorem sim_pre {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} {j : Nat} (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ((as.take j).map (lv sl)).reverse,
      (getsCode as).drop j ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest) (hj : j ≤ as.length) :
    SimOk P H (c, s) t := by
  rcases Nat.lt_or_ge j as.length with hlt | hge
  · exact sim_get hR hcs hct hch hfn hloc hst hlt
  · have hj' : j = as.length := by omega
    subst hj'
    have hd : (getsCode as).drop as.length = [] := List.drop_eq_nil_of_le (by simp [getsCode])
    rw [hd, List.take_length] at hcs
    have hcs' : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
        .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw := by
      rw [hcs]; simp
    by_cases hf : f.value.val < P.imps.length
    · exact sim_imp hR hcs' hct hch hfn hloc hst hf
    · exact sim_call hR hcs' hct hch hfn hloc hst (by omega)

/-- A pure statement opens: the target passes its guard (normal mode), then both run it. -/
theorem sim_open_pure {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre r : List Stmt} {i : Instr} {is : List Instr}
    (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, [], [] ++ flatS (Stmt.pure (i :: is) :: r) ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (Stmt.pure (i :: is) :: r) ++
      fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.pure (i :: is) :: r) :
    SimOk P H (c, s) t := by
  obtain ⟨-, hpure, hdep⟩ :=
    Stmt.wf_pure ((Prog.fnOk hR.wf hfn).stmts (Stmt.pure (i :: is)) (by rw [hst]; simp))
  let pre' := pre ++ [Stmt.pure (i :: is)]
  let K := (i :: is) ++ trS (P.ctx fn) pre'.length r ++ fn.tail
  have e : Steps (asyncifyProg P) (3 + 1) ⟨⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length
      (Stmt.pure (i :: is) :: r) ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩
      ⟨⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by
    have e1 := steps_ite (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩) (rest := tw)
      (t := i :: is) (e := []) (K := trS (P.ctx fn) (pre.length + 1) r ++ fn.tail)
      (seg_guard_ne P tl [] t.cfg.mem)
    simpa [trS, trStmt, ifThen, K, pre', List.append_assoc] using e1
  have hcfg : t.cfg = ⟨⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (Stmt.pure (i :: is) :: r) ++
      fn.tail, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by rw [← hct, ← hR.globals]
  have hcs' : c.frames = ⟨fid, sl, [], (i :: is) ++ flatS r ++ fn.tail, fn.nres⟩ :: sw := by
    rw [hcs]; simp [flatS, Stmt.code]
  have hst' : fn.stmts = pre' ++ r := by rw [hst]; simp [pre']
  have hd : depthAfter (i :: is) ([] : List W).length = some 0 := by simpa using hdep
  have hR' : Rel P H (c, s) { t with cfg := ⟨⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals,
      t.cfg.mem⟩ } :=
    ⟨hR.wf, hR.host, ⟨_, _, sw, tw, ks, hcs', rfl, TopR.mk hR.wf hfn hloc hst' hpure hd, hch⟩, rfl,
      hR.entry, hR.bound⟩
  exact SimOk.pre (e.tgt_of hcfg) (sim_run hR' hcs' rfl hch hfn hloc hst' hpure hd)

/-- A top frame at the start of a statement (no pure code pending). -/
theorem sim_stmt {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre r : List Stmt} {st : Stmt}
    (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, [], [] ++ flatS (st :: r) ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (st :: r) ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ st :: r) : SimOk P H (c, s) t := by
  cases st with
  | pure is =>
    cases is with
    | nil =>
      exact absurd rfl (Stmt.wf_pure ((Prog.fnOk hR.wf hfn).stmts (Stmt.pure [])
        (by rw [hst]; simp))).1
    | cons i is => exact sim_open_pure hR hcs hct hch hfn hloc hst
  | call f as rs =>
    exact sim_pre (j := 0) hR (by rw [hcs]; simp [flatS, Stmt.code, getsCode])
      (by rw [hct]; simp [trS]) hch hfn hloc hst (Nat.zero_le _)

/-- A top frame inside a pure statement or at the start of one. -/
theorem sim_top_run {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {p : List Instr} {pre rest : List Stmt}
    (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, p ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, p ++ trS (P.ctx fn) pre.length rest ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ rest) (hrest : rest ≠ [])
    (hp : ∀ i ∈ p, pureIns fn.nloc i = true) (hd : depthAfter p ops.length = some 0) :
    SimOk P H (c, s) t := by
  cases p with
  | cons i p => exact sim_run hR hcs hct hch hfn hloc hst hp hd
  | nil =>
    have hops : ops = [] := List.eq_nil_of_length_eq_zero (by simpa [depthAfter] using hd)
    cases rest with
    | nil => exact absurd rfl hrest
    | cons st r => exact sim_stmt hR (by rw [hcs, hops]) (by rw [hct, hops]) hch hfn hloc hst

/-- Every related pair satisfies the one-step obligation. -/
theorem simOk_of_rel {P : Prog} {H : Host σ} {x : Cfg × σ} {t : TSt σ} (hR : Rel P H x t) :
    SimOk P H x t := by
  obtain ⟨c, s⟩ := x
  obtain ⟨s0, t0, sw, tw, ks, hcs, hct, htop, hch⟩ := hR.frames
  cases htop with
  | run hfn hloc hst hrest hp hd => exact sim_top_run hR hcs hct hch hfn hloc hst hrest hp hd
  | @fin _ _ _ _ _ q hfn hloc hq hd =>
    cases q with
    | nil => exact sim_ret hR hcs hct hch hfn hd
    | cons i q => exact sim_fin hR hcs hct hch hfn hloc hq hd
  | pre hfn hloc hst hj => exact sim_pre hR hcs hct hch hfn hloc hst hj

theorem isSim (P : Prog) (H : Host σ) :
    IsSim (srcStep P.env H) (tgtStep (asyncifyProg P) H) (Rel P H) mu where
  stop := fun _ _ o hR h => (simOk_of_rel hR).1 o h
  next := fun _ _ x' hR h => (simOk_of_rel hR).2 x' h

/-- The source configuration of a call. -/
def srcCfg (e : Nat) (fn : FnSrc) (args : List W) : Cfg :=
  ⟨[entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ args], [], fun _ => 0⟩

/-- The target state of the same call. -/
def tgtSt (P : Prog) (e : Nat) (fn : FnSrc) (args : List W) (s : σ) : TSt σ :=
  ⟨⟨[entry e (tdef P fn) args], P.tGlobals, fun _ => 0⟩, s, e, args⟩

theorem srcInit_eq {P : Prog} {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) :
    srcInit P.env e args = some (srcCfg e fn args) := by
  have hge := Prog.fnAt_ge hfn
  have := Prog.env_fn hfn
  simp only [srcInit, show P.env.imps.length ≤ e from hge, ↓reduceIte, this, Option.map_some]
  rfl

theorem tgtInit_eq {P : Prog} {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W)
    (s : σ) : tgtInit P e args s = some (tgtSt P e fn args s) := by
  have hge := Prog.fnAt_ge hfn
  have := Prog.tgt_fn hfn
  simp only [tgtInit, srcInit, show (asyncifyProg P).imps.length ≤ e from hge, ↓reduceIte, this,
    Option.map_some]
  rfl

/-- **Correctness of the asyncify pass** (first strategy). For a well-formed source program, a
call of a defined function with arguments of the right number, every deterministic host, and a
source run whose stack depth keeps the shadow stack inside the 32-bit address space: the source
system (suspending import calls, answered by the host) and the target system (the asyncified
program, which never calls an import, run under the host protocol of `tgtStep`) have the same
behaviours: the same results with the same final host state, the same traps, divergence. -/
theorem asyncify_beh (P : Prog) (hP : P.WF) (H : Host σ) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (s : σ)
    (hbound : DepthBound P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStep (asyncifyProg P) H) (tgtSt P e fn args s) := by
  have e1 : Steps (asyncifyProg P) (3 + 1) ⟨[entry e (tdef P fn) args], P.tGlobals, fun _ => 0⟩
      ⟨[⟨e, args ++ List.replicate (P.frameWords - fn.nparams) 0, [],
        trS (P.ctx fn) 0 fn.stmts ++ fn.tail, fn.nres⟩], P.tGlobals, fun _ => 0⟩ := by
    have h := steps_ite (E := asyncifyProg P) (fr := ⟨e, args ++
      List.replicate (P.frameWords - fn.nparams) 0, [], [], fn.nres⟩) (rest := [])
      (t := restoreCode P.frameWords) (e := []) (K := trS (P.ctx fn) 0 fn.stmts ++ fn.tail)
      (seg_prologue_normal P _ (fun _ => 0))
    simpa [entry, tdef, Prog.tBody, prologue, ifThen, List.append_assoc] using h
  rw [beh_shift (e1.tgt_of (H := H) (t := tgtSt P e fn args s) rfl)]
  exact beh_eq_of_sim (isSim P H) ⟨hP, rfl, ⟨_, _, [], [], [], rfl, rfl,
    TopR.ofEntry hP hfn rfl hargs, .nil e⟩, rfl, ⟨fn, hfn, hargs⟩, hbound⟩

end Silmaril.Wasm.FX.Asyncify.Tool
