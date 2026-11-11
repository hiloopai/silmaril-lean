module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Pure

/-!
# The simulation relation between the source and the asyncified program

In normal mode (`state = 0`, `sp = SB`) the target has one frame per source frame:

* the top frame (`TopR`) is inside a pure statement or the tail (`run`, `fin`: same code prefix,
  same operands), or reading the arguments of a call statement (`pre`: the source pushes them one
  by one while the target waits at the statement);
* the frames below (`WaitR`, chained by `Chain`) wait on a call statement to a defined function:
  the target code is the call-site check `chk` followed by the translation of the rest.

Locals agree up to the extra target locals (`LocR`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-! ## Lookups and well-formedness facts -/

/-- The source function at function index `fid`. -/
def Prog.fnAt (P : Prog) (fid : Nat) : Option FnSrc :=
  if P.imps.length ≤ fid then P.fns[fid - P.imps.length]? else none

theorem Prog.fnAt_mem {P : Prog} {fid : Nat} {fn : FnSrc} (h : P.fnAt fid = some fn) :
    fn ∈ P.fns := by
  unfold Prog.fnAt at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

theorem Prog.fnAt_ge {P : Prog} {fid : Nat} {fn : FnSrc} (h : P.fnAt fid = some fn) :
    P.imps.length ≤ fid := by
  unfold Prog.fnAt at h
  split at h
  · assumption
  · cases h

theorem Prog.env_fn {P : Prog} {fid : Nat} {fn : FnSrc} (h : P.fnAt fid = some fn) :
    P.env.fns[fid - P.env.imps.length]? = some ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ := by
  unfold Prog.fnAt at h
  split at h
  · simp [Prog.env, h]
  · cases h

theorem Prog.tgt_fn {P : Prog} {fid : Nat} {fn : FnSrc} (h : P.fnAt fid = some fn) :
    (asyncifyProg P).fns[fid - (asyncifyProg P).imps.length]? =
      some ⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ := by
  unfold Prog.fnAt at h
  split at h
  · simp [asyncifyProg, h]
  · cases h

theorem Prog.wf_fns {P : Prog} (hP : P.WF) {fn : FnSrc} (h : fn ∈ P.fns) : fn.wf P = true := by
  simp only [Prog.WF, Prog.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hP
  exact hP.1.1 fn h

theorem Prog.wf_bounds {P : Prog} (hP : P.WF) :
    P.imps.length + P.fns.length < 2 ^ 31 ∧ 4 * P.frameWords + 4 * P.reqWords < 2 ^ 24 := by
  simp only [Prog.WF, Prog.wf, Bool.and_eq_true, decide_eq_true_eq] at hP
  exact ⟨hP.1.2, hP.2⟩

theorem foldr_max_ge {l : List Nat} {a d : Nat} (h : a ∈ l) : a ≤ l.foldr max d := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem foldr_max_ge_init (l : List Nat) (d : Nat) : d ≤ l.foldr max d := by
  induction l with
  | nil => simp
  | cons b l ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem Prog.nloc_lt {P : Prog} {fn : FnSrc} (h : fn ∈ P.fns) : fn.nloc + 1 ≤ P.frameWords := by
  unfold Prog.frameWords
  have := foldr_max_ge (d := 0) (List.mem_map_of_mem (f := FnSrc.nloc) h)
  omega

theorem Prog.imp_le {P : Prog} {n m : Nat} (h : (n, m) ∈ P.imps) :
    n + 1 ≤ P.reqWords ∧ m ≤ P.reqWords := by
  unfold Prog.reqWords
  have h1 : max (n + 1) m ∈ P.imps.map (fun x : Nat × Nat => max (x.1 + 1) x.2) :=
    List.mem_map.2 ⟨(n, m), h, rfl⟩
  have := foldr_max_ge (d := 1) h1
  omega

theorem Prog.reqWords_pos (P : Prog) : 1 ≤ P.reqWords := foldr_max_ge_init _ _

/-- The facts of a well-formed function that the proofs use. -/
structure FnOk (P : Prog) (fn : FnSrc) : Prop where
  stmts : ∀ s ∈ fn.stmts, s.wf P fn.nloc = true
  tailPure : ∀ i ∈ fn.tail, pureIns fn.nloc i = true
  tailDepth : depthAfter fn.tail 0 = some fn.nres
  nstmts : fn.stmts.length < 2 ^ 31
  nloc : fn.nloc + 1 ≤ P.frameWords

theorem Prog.fnOk {P : Prog} (hP : P.WF) {fid : Nat} {fn : FnSrc} (h : P.fnAt fid = some fn) :
    FnOk P fn := by
  have hm := Prog.fnAt_mem h
  have := Prog.wf_fns hP hm
  simp only [FnSrc.wf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2, Prog.nloc_lt hm⟩

/-- Facts of a well-formed call statement. -/
theorem Stmt.wf_call {P : Prog} {S : Nat} {f : FuncIdx} {as rs : List LocalIdx}
    (h : (Stmt.call f as rs).wf P S = true) :
    P.sig f.value.val = some (as.length, rs.length) ∧ (∀ a ∈ as, a.value.val < S) ∧
      (∀ r ∈ rs, r.value.val < S) := by
  simp only [Stmt.wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem Stmt.wf_pure {P : Prog} {S : Nat} {is : List Instr} (h : (Stmt.pure is).wf P S = true) :
    is ≠ [] ∧ (∀ i ∈ is, pureIns S i = true) ∧ depthAfter is 0 = some 0 := by
  simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## The relation -/

/-- Source and target locals agree, up to the extra target locals. -/
def LocR (P : Prog) (fn : FnSrc) (sl tl : List W) : Prop :=
  sl.length = fn.nloc ∧ ∃ ex, tl = sl ++ ex ∧ ex.length = P.frameWords - fn.nloc

/-- The top frames. -/
inductive TopR (P : Prog) : Frame → Frame → Prop
  | run {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {p : List Instr} {pre rest : List Stmt} :
      P.fnAt fid = some fn → LocR P fn sl tl → fn.stmts = pre ++ rest → rest ≠ [] →
      (∀ i ∈ p, pureIns fn.nloc i = true) → depthAfter p ops.length = some 0 →
      TopR P ⟨fid, sl, ops, p ++ flatS rest ++ fn.tail, fn.nres⟩
        ⟨fid, tl, ops, p ++ trS (P.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩
  | fin {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {q : List Instr} :
      P.fnAt fid = some fn → LocR P fn sl tl → (∀ i ∈ q, pureIns fn.nloc i = true) →
      depthAfter q ops.length = some fn.nres →
      TopR P ⟨fid, sl, ops, q, fn.nres⟩ ⟨fid, tl, ops, q, fn.nres⟩
  | pre {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
      {as rs : List LocalIdx} {j : Nat} :
      P.fnAt fid = some fn → LocR P fn sl tl → fn.stmts = pre ++ Stmt.call f as rs :: rest →
      j ≤ as.length →
      TopR P ⟨fid, sl, ((as.take j).map (lv sl)).reverse,
          (getsCode as).drop j ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩
        ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
          trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩

/-- A frame waiting on call statement `k` to the defined function `callee`. -/
inductive WaitR (P : Prog) : Nat → Nat → Frame → Frame → Prop
  | mk {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
      {as rs : List LocalIdx} :
      P.fnAt fid = some fn → LocR P fn sl tl → fn.stmts = pre ++ Stmt.call f as rs :: rest →
      P.imps.length ≤ f.value.val →
      WaitR P f.value.val pre.length ⟨fid, sl, [], setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩
        ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++
          trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩

/-- The frames below the top: each waits on a call to the function of the frame above; the
bottom frame is function `e`. -/
inductive Chain (P : Prog) : Nat → Nat → List Nat → List Frame → List Frame → Prop
  | nil (e : Nat) : Chain P e e [] [] []
  | cons {above e k : Nat} {ks : List Nat} {fs ft : Frame} {ss ts : List Frame} :
      WaitR P above k fs ft → Chain P fs.fid e ks ss ts →
      Chain P above e (k :: ks) (fs :: ss) (ft :: ts)

/-- The simulation relation of the closed systems. -/
structure Rel {σ : Type} (P : Prog) (H : Host σ) (x : Cfg × σ) (t : TSt σ) : Prop where
  wf : P.WF
  host : t.host = x.2
  frames : ∃ s0 t0 sw tw ks, x.1.frames = s0 :: sw ∧ t.cfg.frames = t0 :: tw ∧ TopR P s0 t0 ∧
    Chain P s0.fid t.fid ks sw tw
  globals : t.cfg.globals = P.tGlobals
  entry : ∃ fn, P.fnAt t.fid = some fn ∧ t.args.length = fn.nparams
  bound : DepthBound P H x

/-- The measure of stuttering steps: the code length of the source top frame. -/
def mu {σ : Type} (x : Cfg × σ) : Nat :=
  match x.1.frames with
  | [] => 0
  | fr :: _ => fr.code.length

end Silmaril.Wasm.FX.Asyncify.Tool
