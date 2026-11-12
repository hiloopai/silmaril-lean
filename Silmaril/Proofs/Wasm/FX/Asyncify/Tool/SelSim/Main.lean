module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.SelSim.Calm

/-!
# The selective simulation: opening statements, all cases, correctness under `SelOk`

* `sim_lf_start`: a pure statement opens (the target passes its guard `state ≠ 2`) and its code
  runs in lockstep; used for calm frames (`sim_lf_open`) and for a pure statement that holds a
  calm call (`sim_stmt_q`, from the `Rel` shape into a calm segment);
* `simOkQ`, `simOkC`: every related pair of either shape satisfies the obligation;
* **`asyncify_beh_selOk`**: `asyncify_beh` for every program with `SelOk Q C`.

New proofs (`sim_pre_q`, `sim_open_pure_q` and `sim_top_run_q` are copies of the lemmas of
`Silmaril/Proofs/Wasm/FX/Asyncify/Tool/Main.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type} {C : Nat → Prop}

/-! ## The code of a calm call statement -/

theorem depthC_append {Q : Prog} : ∀ (p q : List Instr) (d : Nat),
    depthC Q (p ++ q) d = (depthC Q p d).bind (depthC Q q)
  | [], q, d => by simp [depthC]
  | i :: p, q, d => by
    simp only [List.cons_append, depthC]
    split
    · exact depthC_append p q _
    · rfl

theorem depthAfter_gets : ∀ (as : List LocalIdx) (d : Nat),
    depthAfter (getsCode as) d = some (d + as.length)
  | [], d => by simp [getsCode, depthAfter]
  | a :: as, d => by
    have h := depthAfter_gets as (d + 1)
    simp only [getsCode, List.map_cons, depthAfter, eff, Nat.zero_le, ite_true, Nat.sub_zero] at h ⊢
    rw [h]; simp only [List.length_cons]; congr 1; omega

/-- The code of a well-formed call statement to a calm function runs in lockstep and returns to
depth 0. -/
theorem callCode_ok {Q : Prog} {S : Nat} {g : FuncIdx} {as rs : List LocalIdx}
    (hw : (Stmt.call g as rs).wf Q S = true) (hg : C g.value.val) :
    (∀ j ∈ (Stmt.call g as rs).code, cIns C S j) ∧ depthC Q (Stmt.call g as rs).code 0 = some 0 := by
  obtain ⟨hsig, has, hrs⟩ := Stmt.wf_call hw
  have hgets : ∀ j ∈ getsCode as, pureIns S j = true := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ as, .localGet a = j := by simpa [getsCode] using hj
    simp [pureIns, has a ha]
  refine ⟨fun j hj => ?_, ?_⟩
  · have hj' : (j ∈ getsCode as ∨ j = .call g) ∨ j ∈ setsCode rs := by
      simpa only [Stmt.code, List.mem_append, List.mem_singleton] using hj
    rcases hj' with (h | h) | h
    · exact Or.inl (hgets j h)
    · exact Or.inr ⟨g, h, hg⟩
    · exact Or.inl (setsCode_pure hrs j h)
  · simp only [Stmt.code]
    rw [depthC_append, depthC_append, depthC_of_pure hgets, depthAfter_gets, Option.bind_some]
    simp only [depthC, effC_call hsig, Nat.zero_add, Nat.le_refl, ite_true, Nat.sub_self,
      Option.bind_some]
    rw [depthC_of_pure (setsCode_pure hrs)]
    simpa using depthAfter_sets rs 0

/-- The code of a pure statement under `StmtOk`. -/
theorem StmtOk.pure_start {Q : Prog} {S : Nat} {is : List Instr} (h : StmtOk Q C S (.pure is)) :
    (∀ j ∈ is, cIns C S j) ∧ depthC Q is 0 = some 0 ∧ is ≠ [] := by
  simp only [StmtOk] at h
  rcases h with h | ⟨g, as, rs, rfl, hg, hw⟩
  · obtain ⟨hne, hp, hd⟩ := Stmt.wf_pure h
    exact ⟨fun j hj => Or.inl (hp j hj), by rw [depthC_of_pure hp]; exact hd, hne⟩
  · obtain ⟨h1, h2⟩ := callCode_ok hw hg
    exact ⟨h1, h2, by simp [Stmt.code]⟩

/-! ## Opening a pure statement into lockstep code -/

/-- A pure statement opens: the target passes its guard, then both run its code in lockstep.
`hmk` builds the segment with the frame pair after the guard. -/
theorem sim_lf_start {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} {fid : Nat} {fn : FnSrc}
    {sl tl : List W} {is : List Instr} {pre r : List Stmt}
    (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, [], is ++ flatS r ++ fn.tail, fn.nres⟩ :: (xs ++ sw))
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (Q.ctx fn) pre.length (.pure is) ++
      (trS (Q.ctx fn) (pre.length + 1) r ++ fn.tail), fn.nres⟩ :: (ts ++ tw))
    (hmk : ∀ ft, LF Q C 0 ⟨fid, sl, [], is ++ flatS r ++ fn.tail, fn.nres⟩ ft →
      Seg Q C 0 (⟨fid, sl, [], is ++ flatS r ++ fn.tail, fn.nres⟩ :: xs) (ft :: ts) b)
    (hch : Chain Q b t.fid ks sw tw) (hfn : Q.fnAt fid = some fn) (hloc : LocR Q fn sl tl)
    (hst : fn.stmts = pre ++ Stmt.pure is :: r) (hp : ∀ j ∈ is, cIns C fn.nloc j)
    (hd : depthC Q is 0 = some 0) (hne : is ≠ []) : SimOkS Q C H (c, s) t := by
  let K := is ++ trS (Q.ctx fn) (pre ++ [Stmt.pure is]).length r ++ fn.tail
  have e : Steps (asyncifyProg Q) (3 + 1) ⟨⟨fid, tl, [], trStmt (Q.ctx fn) pre.length (.pure is) ++
      (trS (Q.ctx fn) (pre.length + 1) r ++ fn.tail), fn.nres⟩ :: (ts ++ tw), Q.tGlobals, t.cfg.mem⟩
      ⟨⟨fid, tl, [], K, fn.nres⟩ :: (ts ++ tw), Q.tGlobals, t.cfg.mem⟩ := by
    have e1 := steps_ite (E := asyncifyProg Q) (fr := ⟨fid, tl, [], [], fn.nres⟩) (rest := ts ++ tw)
      (t := is) (e := []) (K := trS (Q.ctx fn) (pre.length + 1) r ++ fn.tail)
      (seg_guard_ne Q tl [] t.cfg.mem)
    simpa [trStmt, ifThen, K, List.append_assoc] using e1
  have hcfg : t.cfg = ⟨⟨fid, tl, [], trStmt (Q.ctx fn) pre.length (.pure is) ++
      (trS (Q.ctx fn) (pre.length + 1) r ++ fn.tail), fn.nres⟩ :: (ts ++ tw), Q.tGlobals,
      t.cfg.mem⟩ := by rw [← hct, ← hR.globals]
  have hst' : fn.stmts = (pre ++ [Stmt.pure is]) ++ r := by rw [hst]; simp
  obtain ⟨i, p, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hd' : depthC Q (i :: p) (([] : List W).length + 0) = some 0 := by simpa using hd
  have hlf : LF Q C 0 ⟨fid, sl, [], (i :: p) ++ flatS r ++ fn.tail, fn.nres⟩
      ⟨fid, tl, [], K, fn.nres⟩ := LF.run hfn hloc hst' hp hd'
  have hR' : RelS Q C H (c, s) { t with cfg := ⟨⟨fid, tl, [], K, fn.nres⟩ :: (ts ++ tw),
      Q.tGlobals, t.cfg.mem⟩ } :=
    ⟨hR.ok, hR.host, .inr ⟨_ :: xs, _ :: ts, sw, tw, b, ks, hcs, rfl, hmk _ hlf, hch⟩, rfl,
      hR.entry, hR.bound⟩
  exact SimOkS.pre (e.tgt_of hcfg) (sim_lf_run hR' hcs rfl (hmk _ hlf) hch hfn hloc hst' hp hd')

/-- A calm frame opens its next statement. -/
theorem sim_lf_open {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} {fid : Nat} {fn : FnSrc}
    {sl tl ops : List W} {pre r : List Stmt} {st : Stmt} (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, [] ++ flatS (st :: r) ++ fn.tail, fn.nres⟩ :: (xs ++ sw))
    (hct : t.cfg.frames =
      ⟨fid, tl, ops, [] ++ trS (Q.ctx fn) pre.length (st :: r) ++ fn.tail, fn.nres⟩ :: (ts ++ tw))
    (hseg : Seg Q C 0 (⟨fid, sl, ops, [] ++ flatS (st :: r) ++ fn.tail, fn.nres⟩ :: xs)
      (⟨fid, tl, ops, [] ++ trS (Q.ctx fn) pre.length (st :: r) ++ fn.tail, fn.nres⟩ :: ts) b)
    (hch : Chain Q b t.fid ks sw tw) (hfn : Q.fnAt fid = some fn) (hloc : LocR Q fn sl tl)
    (hst : fn.stmts = pre ++ st :: r) (hd : depthC Q [] (ops.length + 0) = some 0)
    (hcalm : C fid) : SimOkS Q C H (c, s) t := by
  have hops : ops = [] := List.eq_nil_of_length_eq_zero (by simpa [depthC] using hd)
  subst hops
  obtain ⟨is, rfl⟩ := hR.ok.calmPure hcalm hfn st (by rw [hst]; simp)
  obtain ⟨hp, hd', hne⟩ := StmtOk.pure_start ((hR.ok.fn hfn).stmts (Stmt.pure is) (by rw [hst]; simp))
  exact sim_lf_start (pre := pre) (is := is) (r := r) hR (by simpa [flatS, Stmt.code] using hcs) (by simpa [trS] using hct)
    (fun _ h => hseg.replace h rfl rfl) hch hfn hloc hst hp hd' hne

/-- A calm frame in its tail. -/
theorem sim_lf_fin {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} {fid : Nat} {fn : FnSrc}
    {sl tl ops : List W} {q : List Instr} (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, q, fn.nres⟩ :: (xs ++ sw))
    (hct : t.cfg.frames = ⟨fid, tl, ops, q, fn.nres⟩ :: (ts ++ tw)) (hc : C fid)
    (hseg' : Seg Q C fn.nres xs ts b) (hch : Chain Q b t.fid ks sw tw) (hfn : Q.fnAt fid = some fn)
    (hloc : LocR Q fn sl tl) (hq : ∀ i ∈ q, pureIns fn.nloc i = true)
    (hd : depthAfter q (ops.length + 0) = some fn.nres) : SimOkS Q C H (c, s) t := by
  cases q with
  | cons i q =>
    have hi := pureShape (hq i (by simp))
    obtain ⟨hl, ex, rfl, hex⟩ := hloc
    refine sim_lf_pure hR hcs hct (.cons hc (.fin hfn ⟨hl, ex, rfl, hex⟩ hq hd) hseg') hch hl hi ?_
    intro sl' ops' he hl'
    exact .fin hfn ⟨hl', ex, rfl, hex⟩ (fun j hj => hq j (by simp [hj]))
      (by simpa using depthAfter_cons hi (by simpa using hd) he)
  | nil =>
    have hlen : ops.length = fn.nres := by simpa [depthAfter] using hd
    cases hseg' with
    | one hl2 =>
      exact sim_lf_ret (xs := []) (ts := []) (fs := ⟨fid, sl, ops, [], fn.nres⟩)
        (ft := ⟨fid, tl, ops, [], fn.nres⟩) hR hcs hct rfl rfl rfl hlen (.one hl2) hch
    | cons hc2 hl2 hs2 =>
      exact sim_lf_ret (fs := ⟨fid, sl, ops, [], fn.nres⟩) (ft := ⟨fid, tl, ops, [], fn.nres⟩) hR
        hcs hct rfl rfl rfl hlen (.cons hc2 hl2 hs2) hch

/-! ## The cases of the `Rel` shape -/

/-- A call statement, while or after its arguments are read. -/
theorem sim_pre_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} {j : Nat} (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ((as.take j).map (lv sl)).reverse,
      (getsCode as).drop j ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest) (hj : j ≤ as.length) :
    SimOkS P C H (c, s) t := by
  rcases Nat.lt_or_ge j as.length with hlt | hge
  · exact sim_get_q hR hcs hct hch hfn hloc hst hlt
  · have hj' : j = as.length := by omega
    subst hj'
    have hd : (getsCode as).drop as.length = [] := List.drop_eq_nil_of_le (by simp [getsCode])
    rw [hd, List.take_length] at hcs
    have hcs' : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
        .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw := by
      rw [hcs]; simp
    by_cases hf : f.value.val < P.imps.length
    · exact sim_imp_q hR hcs' hct hch hfn hloc hst hf
    · exact sim_call_q hR hcs' hct hch hfn hloc hst (by omega)

/-- A pure statement opens: the target passes its guard (normal mode), then both run it. -/
theorem sim_open_pure_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre r : List Stmt} {i : Instr} {is : List Instr}
    (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, [], [] ++ flatS (Stmt.pure (i :: is) :: r) ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (Stmt.pure (i :: is) :: r) ++
      fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.pure (i :: is) :: r)
    (hpure : ∀ j ∈ i :: is, pureIns fn.nloc j = true) (hdep : depthAfter (i :: is) 0 = some 0) :
    SimOkS P C H (c, s) t := by
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
  have hR' : RelS P C H (c, s) { t with cfg := ⟨⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals,
      t.cfg.mem⟩ } :=
    ⟨hR.ok, hR.host, .inl ⟨_, _, sw, tw, ks, hcs', rfl, TopR.mkS hR.ok hfn hloc hst' hpure hd, hch⟩, rfl,
      hR.entry, hR.bound⟩
  exact SimOkS.pre (e.tgt_of hcfg) (sim_run_q hR' hcs' rfl hch hfn hloc hst' hpure hd)


/-- A top frame at the start of a statement (no pure code pending). -/
theorem sim_stmt_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre r : List Stmt} {st : Stmt}
    (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, [], [] ++ flatS (st :: r) ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (st :: r) ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ st :: r) : SimOkS P C H (c, s) t := by
  cases st with
  | pure is =>
    have hso := (hR.ok.fn hfn).stmts (Stmt.pure is) (by rw [hst]; simp)
    have hso' := hso
    simp only [StmtOk] at hso'
    rcases hso' with h | -
    · obtain ⟨hne, hp, hd⟩ := Stmt.wf_pure h
      cases is with
      | nil => exact absurd rfl hne
      | cons i is => exact sim_open_pure_q hR hcs hct hch hfn hloc hst hp hd
    · obtain ⟨hp, hd, hne⟩ := StmtOk.pure_start hso
      exact sim_lf_start (xs := []) (ts := []) (pre := pre) (is := is) (r := r) hR (by simpa [flatS, Stmt.code] using hcs)
        (by simpa [trS] using hct) (fun _ h => Seg.one h) hch hfn hloc hst hp hd hne
  | call f as rs =>
    exact sim_pre_q (j := 0) hR (by rw [hcs]; simp [flatS, Stmt.code, getsCode])
      (by rw [hct]; simp [trS]) hch hfn hloc hst (Nat.zero_le _)

/-- A top frame inside a pure statement or at the start of one. -/
theorem sim_top_run_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {p : List Instr} {pre rest : List Stmt}
    (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, p ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, p ++ trS (P.ctx fn) pre.length rest ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ rest) (hrest : rest ≠ [])
    (hp : ∀ i ∈ p, pureIns fn.nloc i = true) (hd : depthAfter p ops.length = some 0) :
    SimOkS P C H (c, s) t := by
  cases p with
  | cons i p => exact sim_run_q hR hcs hct hch hfn hloc hst hp hd
  | nil =>
    have hops : ops = [] := List.eq_nil_of_length_eq_zero (by simpa [depthAfter] using hd)
    cases rest with
    | nil => exact absurd rfl hrest
    | cons st r => exact sim_stmt_q hR (by rw [hcs, hops]) (by rw [hct, hops]) hch hfn hloc hst



/-! ## All cases -/

/-- Every pair related in the `Rel` shape satisfies the obligation. -/
theorem simOkQ {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} (hR : RelS Q C H (c, s) t)
    (hF : FramesQ Q t.fid c.frames t.cfg.frames) : SimOkS Q C H (c, s) t := by
  obtain ⟨s0, t0, sw, tw, ks, hcs, hct, htop, hch⟩ := hF
  cases htop with
  | run hfn hloc hst hrest hp hd => exact sim_top_run_q hR hcs hct hch hfn hloc hst hrest hp hd
  | @fin _ _ _ _ _ q hfn hloc hq hd =>
    cases q with
    | nil => exact sim_ret_q hR hcs hct hch hfn hd
    | cons i q => exact sim_fin_q hR hcs hct hch hfn hloc hq hd
  | pre hfn hloc hst hj => exact sim_pre_q hR hcs hct hch hfn hloc hst hj

/-- The bottom frame of a segment alone: in the `Rel` shape when its code is pure, else a
lockstep step. -/
theorem simOkC_bottom {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {s0 t0 : Frame}
    {sw tw : List Frame} {ks : List Nat} (hR : RelS Q C H (c, s) t) (hcs : c.frames = s0 :: sw)
    (hct : t.cfg.frames = t0 :: tw) (hlf : LF Q C 0 s0 t0) (hch : Chain Q s0.fid t.fid ks sw tw) :
    SimOkS Q C H (c, s) t := by
  cases hlf with
  | @run fid fn sl tl ops p pre rest hfn hloc hst hp hd =>
    show SimOkS Q C H (c, s) t
    by_cases hpure : ∀ i ∈ p, pureIns fn.nloc i = true
    · have hd' : depthAfter p ops.length = some 0 := by
        rw [← depthC_of_pure (Q := Q) hpure]; simpa using hd
      exact simOkQ hR ⟨_, _, sw, tw, ks, hcs, hct, TopR.mkS hR.ok hfn hloc hst hpure hd', hch⟩
    · cases p with
      | nil => exact absurd (fun i hi => by simp at hi) hpure
      | cons i p =>
        exact sim_lf_run (xs := []) (ts := []) hR hcs hct (.one (.run hfn hloc hst hp hd)) hch hfn
          hloc hst hp hd
  | fin hfn hloc hq hd =>
    exact simOkQ hR ⟨_, _, sw, tw, ks, hcs, hct, .fin hfn hloc hq (by simpa using hd), hch⟩

/-- A calm frame at the end of its statements runs its tail. -/
theorem sim_lf_tail {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} {fid : Nat} {fn : FnSrc}
    {sl tl ops : List W} {pre : List Stmt} (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, [] ++ flatS [] ++ fn.tail, fn.nres⟩ :: (xs ++ sw))
    (hct : t.cfg.frames =
      ⟨fid, tl, ops, [] ++ trS (Q.ctx fn) pre.length [] ++ fn.tail, fn.nres⟩ :: (ts ++ tw))
    (hc : C fid) (hseg' : Seg Q C fn.nres xs ts b) (hch : Chain Q b t.fid ks sw tw)
    (hfn : Q.fnAt fid = some fn) (hloc : LocR Q fn sl tl) (hd : depthC Q [] (ops.length + 0) = some 0) :
    SimOkS Q C H (c, s) t := by
  have hops : ops = [] := List.eq_nil_of_length_eq_zero (by simpa [depthC] using hd)
  have hcs' : c.frames = ⟨fid, sl, [], fn.tail, fn.nres⟩ :: (xs ++ sw) := by
    simpa [flatS, hops] using hcs
  have hct' : t.cfg.frames = ⟨fid, tl, [], fn.tail, fn.nres⟩ :: (ts ++ tw) := by
    simpa [trS, hops] using hct
  have hd' : depthAfter fn.tail (([] : List W).length + 0) = some fn.nres := by
    simpa using (hR.ok.fn hfn).tailDepth
  exact sim_lf_fin hR hcs' hct' hc hseg' hch hfn hloc (hR.ok.fn hfn).tailPure hd'

/-- A calm frame on top of a segment. -/
theorem simOkC_calm {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {fs ft : Frame}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = fs :: (xs ++ sw)) (hct : t.cfg.frames = ft :: (ts ++ tw)) (hc : C fs.fid)
    (hlf : LF Q C 0 fs ft) (hseg' : Seg Q C fs.nres xs ts b) (hch : Chain Q b t.fid ks sw tw) :
    SimOkS Q C H (c, s) t := by
  cases hlf with
  | @run fid fn sl tl ops p pre rest hfn hloc hst hp hd =>
    show SimOkS Q C H (c, s) t
    cases p with
    | cons i p =>
      exact sim_lf_run hR hcs hct (.cons hc (.run hfn hloc hst hp hd) hseg') hch hfn hloc hst hp hd
    | nil =>
      cases rest with
      | cons st r =>
        exact sim_lf_open hR hcs hct (.cons hc (.run hfn hloc hst hp hd) hseg') hch hfn hloc hst
          hd hc
      | nil => exact sim_lf_tail hR hcs hct hc hseg' hch hfn hloc hd
  | fin hfn hloc hq hd => exact sim_lf_fin hR hcs hct hc hseg' hch hfn hloc hq hd

/-- Every pair related in the shape of a calm call in progress satisfies the obligation. -/
theorem simOkC {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} (hR : RelS Q C H (c, s) t)
    (hF : FramesC Q C t.fid c.frames t.cfg.frames) : SimOkS Q C H (c, s) t := by
  obtain ⟨ss, tt, sw, tw, b, ks, hcs, hct, hseg, hch⟩ := hF
  cases hseg with
  | one hlf => exact simOkC_bottom hR hcs hct hlf hch
  | cons hc hlf hseg' => exact simOkC_calm hR hcs hct hc hlf hseg' hch

/-- **Every related pair satisfies the one-step obligation.** -/
theorem simOkS_of_rel {Q : Prog} {H : Host σ} {x : Cfg × σ} {t : TSt σ} (hR : RelS Q C H x t) :
    SimOkS Q C H x t := by
  obtain ⟨c, s⟩ := x
  rcases hR.frames with hF | hF
  · exact simOkQ hR hF
  · exact simOkC hR hF

theorem isSimSel (Q : Prog) (C : Nat → Prop) (H : Host σ) :
    IsSim (srcStep Q.env H) (tgtStep (asyncifyProg Q) H) (RelS Q C H) mu where
  stop := fun _ _ o hR h => (simOkS_of_rel hR).1 o h
  next := fun _ _ x' hR h => (simOkS_of_rel hR).2 x' h

/-- **Correctness of the pass under `SelOk`**: `asyncify_beh` for every program that is well
formed up to pure statements holding calls of calm functions. -/
theorem asyncify_beh_selOk (Q : Prog) (C : Nat → Prop) (hQ : SelOk Q C) (H : Host σ) {e : Nat}
    {fn : FnSrc} (hfn : Q.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams)
    (s : σ) (hbound : DepthBound Q H (srcCfg e fn args, s)) :
    beh (srcStep Q.env H) (srcCfg e fn args, s) =
      beh (tgtStep (asyncifyProg Q) H) (tgtSt Q e fn args s) := by
  have e1 : Steps (asyncifyProg Q) (3 + 1) ⟨[entry e (tdef Q fn) args], Q.tGlobals, fun _ => 0⟩
      ⟨[⟨e, args ++ List.replicate (Q.frameWords - fn.nparams) 0, [],
        trS (Q.ctx fn) 0 fn.stmts ++ fn.tail, fn.nres⟩], Q.tGlobals, fun _ => 0⟩ := by
    have h := steps_ite (E := asyncifyProg Q) (fr := ⟨e, args ++
      List.replicate (Q.frameWords - fn.nparams) 0, [], [], fn.nres⟩) (rest := [])
      (t := restoreCode Q.frameWords) (e := []) (K := trS (Q.ctx fn) 0 fn.stmts ++ fn.tail)
      (seg_prologue_normal Q _ (fun _ => 0))
    simpa [entry, tdef, Prog.tBody, prologue, ifThen, List.append_assoc] using h
  rw [beh_shift (e1.tgt_of (H := H) (t := tgtSt Q e fn args s) rfl)]
  exact beh_eq_of_sim (isSimSel Q C H) ⟨hQ, rfl, .inl ⟨_, _, [], [], [], rfl, rfl,
    TopR.ofEntryS hQ hfn rfl hargs, .nil e⟩, rfl, ⟨fn, hfn, hargs⟩, hbound⟩

end Silmaril.Wasm.FX.Asyncify.Tool
