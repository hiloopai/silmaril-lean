module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Main

/-!
# The simulation of the selective mode: the relation

The selective program `Q = selProg P` is not `WF`: a call statement to a calm function became a
pure statement whose code is the call. The simulation of `asyncify_beh` is redone here for any
program `Q` that is well formed in a weaker sense, `SelOk Q C`, for a set `C` of *calm*
functions:

* every statement is well formed, except that a pure statement may also be the code of a call
  statement to a calm function (`StmtOk`);
* every calm function is a defined function whose statements are all pure.

The relation `RelS` has two shapes:

* `.inl`: the shape of `Rel` (`TopR` on top, `Chain` below), for `Q`;
* `.inr`: a calm call in progress (`FramesC`). The frames above the bottom frame `s0` of the
  segment run calm functions, and source and target run the same instructions in lockstep
  (`LF`): pure instructions and calls of calm functions (`cIns`), with the stack depth tracked
  through calls (`depthC`). Below `s0` the frames wait in a `Chain` as in `Rel`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-! ## Weak well-formedness -/

/-- A statement of a function with `S` locals: well formed, or a pure statement holding the code
of a well-formed call statement to a calm function. -/
def StmtOk (Q : Prog) (C : Nat → Prop) (S : Nat) : Stmt → Prop
  | .call f as rs => (Stmt.call f as rs).wf Q S = true
  | .pure is => (Stmt.pure is).wf Q S = true ∨
      ∃ g as rs, is = (Stmt.call g as rs).code ∧ C g.value.val ∧ (Stmt.call g as rs).wf Q S = true

/-- The facts of a function that the simulation uses (`FnOk`, with `StmtOk`). -/
structure FnOkS (Q : Prog) (C : Nat → Prop) (fn : FnSrc) : Prop where
  stmts : ∀ s ∈ fn.stmts, StmtOk Q C fn.nloc s
  tailPure : ∀ i ∈ fn.tail, pureIns fn.nloc i = true
  tailDepth : depthAfter fn.tail 0 = some fn.nres
  nstmts : fn.stmts.length < 2 ^ 31
  nloc : fn.nloc + 1 ≤ Q.frameWords

/-- **Weak well-formedness** with calm functions `C`. -/
structure SelOk (Q : Prog) (C : Nat → Prop) : Prop where
  bounds : Q.imps.length + Q.fns.length < 2 ^ 31 ∧ 4 * Q.frameWords + 4 * Q.reqWords < 2 ^ 24
  fn : ∀ {fid : Nat} {fn : FnSrc}, Q.fnAt fid = some fn → FnOkS Q C fn
  calmFn : ∀ {g : Nat}, C g → ∃ fn, Q.fnAt g = some fn
  calmPure : ∀ {g : Nat} {fn : FnSrc}, C g → Q.fnAt g = some fn → ∀ s ∈ fn.stmts, ∃ is, s = .pure is

theorem FnOkS.call {Q : Prog} {C : Nat → Prop} {fn : FnSrc} (hok : FnOkS Q C fn) {f : FuncIdx}
    {as rs : List LocalIdx} (h : Stmt.call f as rs ∈ fn.stmts) :
    (Stmt.call f as rs).wf Q fn.nloc = true := hok.stmts _ h

theorem FnOkS.pre_lt {Q : Prog} {C : Nat → Prop} {fn : FnSrc} (hok : FnOkS Q C fn)
    {pre rest : List Stmt} {s : Stmt} (hst : fn.stmts = pre ++ s :: rest) : pre.length < 2 ^ 31 := by
  have hlen : fn.stmts.length = pre.length + (rest.length + 1) := by rw [hst]; simp
  have := hok.nstmts
  omega

/-! ## Lockstep code: pure instructions and calm calls -/

/-- An instruction both machines run in lockstep: pure, or a call of a calm function. -/
def cIns (C : Nat → Prop) (S : Nat) (i : Instr) : Prop :=
  pureIns S i = true ∨ ∃ g, i = .call g ∧ C g.value.val

/-- Operands popped and pushed, calls included. -/
def effC (Q : Prog) : Instr → Nat × Nat
  | .call g => (Q.sig g.value.val).getD (0, 0)
  | i => eff i

/-- The stack depth after lockstep code. -/
def depthC (Q : Prog) : List Instr → Nat → Option Nat
  | [], d => some d
  | i :: is, d => if (effC Q i).1 ≤ d then depthC Q is (d - (effC Q i).1 + (effC Q i).2) else none

/-- A frame pair running in lockstep; `m` results of a callee above are still to come. -/
inductive LF (Q : Prog) (C : Nat → Prop) (m : Nat) : Frame → Frame → Prop
  | run {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {p : List Instr} {pre rest : List Stmt} :
      Q.fnAt fid = some fn → LocR Q fn sl tl → fn.stmts = pre ++ rest →
      (∀ i ∈ p, cIns C fn.nloc i) → depthC Q p (ops.length + m) = some 0 →
      LF Q C m ⟨fid, sl, ops, p ++ flatS rest ++ fn.tail, fn.nres⟩
        ⟨fid, tl, ops, p ++ trS (Q.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩
  | fin {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {q : List Instr} :
      Q.fnAt fid = some fn → LocR Q fn sl tl → (∀ i ∈ q, pureIns fn.nloc i = true) →
      depthAfter q (ops.length + m) = some fn.nres →
      LF Q C m ⟨fid, sl, ops, q, fn.nres⟩ ⟨fid, tl, ops, q, fn.nres⟩

/-- A calm call in progress, top first: every frame above the last runs a calm function and
waits for the results of the frame above it; `b` is the function of the last frame. -/
inductive Seg (Q : Prog) (C : Nat → Prop) : Nat → List Frame → List Frame → Nat → Prop
  | one {m : Nat} {s0 t0 : Frame} : LF Q C m s0 t0 → Seg Q C m [s0] [t0] s0.fid
  | cons {m b : Nat} {fs ft : Frame} {xs ts : List Frame} : C fs.fid → LF Q C m fs ft →
      Seg Q C fs.nres xs ts b → Seg Q C m (fs :: xs) (ft :: ts) b

/-- Frames in the shape of `Rel`. -/
def FramesQ (Q : Prog) (e : Nat) (xs ts : List Frame) : Prop :=
  ∃ s0 t0 sw tw ks, xs = s0 :: sw ∧ ts = t0 :: tw ∧ TopR Q s0 t0 ∧ Chain Q s0.fid e ks sw tw

/-- Frames of a calm call in progress, above a chain. -/
def FramesC (Q : Prog) (C : Nat → Prop) (e : Nat) (xs ts : List Frame) : Prop :=
  ∃ ss tt sw tw b ks, xs = ss ++ sw ∧ ts = tt ++ tw ∧ Seg Q C 0 ss tt b ∧ Chain Q b e ks sw tw

/-- **The simulation relation of the selective mode.** -/
structure RelS (Q : Prog) (C : Nat → Prop) (H : Host σ) (x : Cfg × σ) (t : TSt σ) : Prop where
  ok : SelOk Q C
  host : t.host = x.2
  frames : FramesQ Q t.fid x.1.frames t.cfg.frames ∨ FramesC Q C t.fid x.1.frames t.cfg.frames
  globals : t.cfg.globals = Q.tGlobals
  entry : ∃ fn, Q.fnAt t.fid = some fn ∧ t.args.length = fn.nparams
  bound : DepthBound Q H x

/-- The simulation obligation at one pair of states. -/
def SimOkS (Q : Prog) (C : Nat → Prop) (H : Host σ) (x : Cfg × σ) (t : TSt σ) : Prop :=
  (∀ o, srcStep Q.env H x = .stop o → ∃ n, runN (tgtStep (asyncifyProg Q) H) n t = .stop o) ∧
  (∀ x', srcStep Q.env H x = .next x' → ∃ n t', runN (tgtStep (asyncifyProg Q) H) n t = .next t' ∧
    RelS Q C H x' t' ∧ (0 < n ∨ mu x' < mu x))

/-- Target steps before an obligation. -/
theorem SimOkS.pre {Q : Prog} {C : Nat → Prop} {H : Host σ} {x : Cfg × σ} {t t' : TSt σ} {k : Nat}
    (h : runN (tgtStep (asyncifyProg Q) H) k t = .next t') (hok : SimOkS Q C H x t') :
    SimOkS Q C H x t := by
  refine ⟨fun o ho => ?_, fun x' hx => ?_⟩
  · obtain ⟨n, hn⟩ := hok.1 o ho
    exact ⟨k + n, by rw [runN_add_next h]; exact hn⟩
  · obtain ⟨n, t'', hn, hR, hd⟩ := hok.2 x' hx
    refine ⟨k + n, t'', by rw [runN_add_next h]; exact hn, hR, ?_⟩
    rcases hd with hd | hd
    · exact Or.inl (by omega)
    · exact Or.inr hd

/-! ## Facts for the `Rel` shape -/

/-- A top frame inside the code of statements `rest` (`TopR.mk` under `SelOk`). -/
theorem TopR.mkS {Q : Prog} {C : Nat → Prop} {fid : Nat} {fn : FnSrc} {sl tl ops : List W}
    {p : List Instr} {pre rest : List Stmt} (hQ : SelOk Q C) (hfn : Q.fnAt fid = some fn)
    (hloc : LocR Q fn sl tl) (hst : fn.stmts = pre ++ rest) (hp : ∀ i ∈ p, pureIns fn.nloc i = true)
    (hd : depthAfter p ops.length = some 0) :
    TopR Q ⟨fid, sl, ops, p ++ flatS rest ++ fn.tail, fn.nres⟩
      ⟨fid, tl, ops, p ++ trS (Q.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩ := by
  by_cases hr : rest = []
  · subst hr
    have hok := hQ.fn hfn
    simp only [flatS, trS, List.append_nil]
    refine .fin hfn hloc ?_ ?_
    · intro i hi
      rcases List.mem_append.1 hi with h | h
      · exact hp i h
      · exact hok.tailPure i h
    · rw [depthAfter_append, hd]; exact hok.tailDepth
  · exact .run hfn hloc hst hr hp hd

/-- The entry frame of a call, after the target's prologue (`TopR.ofEntry` under `SelOk`). -/
theorem TopR.ofEntryS {Q : Prog} {C : Nat → Prop} (hQ : SelOk Q C) {e : Nat} {fn : FnSrc}
    (hfn : Q.fnAt e = some fn) {sargs targs : List W} (heq : targs = sargs)
    (hlen : sargs.length = fn.nparams) :
    TopR Q (Tool.entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ sargs)
      ⟨e, targs ++ List.replicate (Q.frameWords - fn.nparams) 0, [],
        trS (Q.ctx fn) 0 fn.stmts ++ fn.tail, fn.nres⟩ := by
  have hloc := LocR.ofEntry (P := Q) (hQ.fn hfn).nloc heq hlen
  have h := TopR.mkS (ops := []) (p := []) (pre := []) (rest := fn.stmts) hQ hfn hloc (by simp)
    (by simp) (by simp [depthAfter])
  simpa [Tool.entry, FnSrc.body] using h

theorem Chain.lenS {Q : Prog} {C : Nat → Prop} (hQ : SelOk Q C) {above e : Nat} {ks : List Nat}
    {sw tw : List Frame} (h : Chain Q above e ks sw tw) :
    sw.length = tw.length ∧ ∀ w ∈ tw, w.locals.length = Q.frameWords := by
  induction h with
  | nil e => simp
  | cons hw _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro w hw'
    simp only [List.mem_cons] at hw'
    rcases hw' with rfl | hw'
    · cases hw with
      | mk hfn hloc _ _ => exact hloc.len (hQ.fn hfn).nloc
    · exact ih.2 w hw'

/-! ## Facts for lockstep code -/

theorem effC_pure {Q : Prog} {S : Nat} {i : Instr} (hi : PureShape S i) : effC Q i = eff i := by
  cases hi <;> rfl

theorem depthC_cons_pure {Q : Prog} {S : Nat} {i : Instr} (hi : PureShape S i) {p : List Instr}
    {d : Nat} : depthC Q (i :: p) d =
      if (eff i).1 ≤ d then depthC Q p (d - (eff i).1 + (eff i).2) else none := by
  simp only [depthC, effC_pure hi]

theorem depthC_of_pure {Q : Prog} {S : Nat} :
    ∀ {p : List Instr}, (∀ i ∈ p, pureIns S i = true) → ∀ d, depthC Q p d = depthAfter p d
  | [], _, d => rfl
  | i :: p, hp, d => by
    have hi := pureShape (hp i (by simp))
    rw [depthC_cons_pure hi, depthAfter]
    split
    · exact depthC_of_pure (fun j hj => hp j (by simp [hj])) _
    · rfl

/-- After a pure instruction, the depth of the rest. -/
theorem depthC_cons {Q : Prog} {S : Nat} {i : Instr} (hi : PureShape S i) {p : List Instr}
    {ls ops ls' ops' : List W} {m : Nat} (hd : depthC Q (i :: p) (ops.length + m) = some 0)
    (he : pexec i ls ops = some (ls', ops')) : depthC Q p (ops'.length + m) = some 0 := by
  rw [depthC_cons_pure hi] at hd
  obtain ⟨h1, h2⟩ := pexec_depth hi he
  simp only [show (eff i).1 ≤ ops.length + m by omega, ite_true] at hd
  rwa [show ops.length + m - (eff i).1 + (eff i).2 = ops'.length + m by omega] at hd

end Silmaril.Wasm.FX.Asyncify.Tool
