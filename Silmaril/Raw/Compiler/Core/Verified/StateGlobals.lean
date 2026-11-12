module

public import Silmaril.Compiler.Core.Verified.State.Defs
public import Silmaril.Compiler.Core.Verified.GlobalsState.Defs
public import Silmaril.Compiler.Core.Verified.RmwValue.Defs
public import Silmaril.Cerberus.Core.LoopReach.Defs
public import Silmaril.Compiler.Core.Verified.PtrStmt.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # `main` as a block of `int` statements over `int` globals and locals

`State.recognize` with file-scope `int` globals: the file's global definitions are `int`s
initialised by literals with distinct symbols (`Globals.inits`, as for `GlobalExpr`), and
`main`'s block reads and assigns them like its locals. The globals are slots of the `int`
state from the start of `main` (`GlobalsState.initial_reaches_state`), each defined by its
literal (`GlobalsState.defs`); the block's locals are created after them.

Only the block's locals are killed before the return: the statements take the slots `ys`
(globals, then locals: the keys a temporary must avoid and an assignment may target) apart from
the locals `xs` (`retStmt`, whose `kill`s must be those of `xs` in order). With no global
definitions this is `State.recognize`'s fragment, and more.

The statements run as a machine over a stack of pending statements (`run`, `Pending`): a sequence
`s; rest` (a declaration group, a nested block without locals) runs `s` with `rest` pending,
`pure(unit)` (an empty statement, the end of a block) goes on with the next pending statement, an
expression statement `e;` (`exprStmt`) evaluates `e` and drops its value, and `if (c) A else B`
(`ifParts`, with or without `else`, arms of any statements) runs each arm followed by the pending
statements and selects between the two results at run time (`StmtIf.choose`). A statement budget
(`budget`) and a size bound keep the copies of the rest of the block in check. The block may fall off
its end (its locals killed, `killsEnd`): `main` then returns its return label's default `0`
(`zeroDefault`, `main_falls`).

A local may also be a struct wrapping one `int` (`WrapObj`: created, declared and killed like an
`int` local; its member designators read and assign the local's slot, `IntWrap.desig`).

`T` is again one closed `IntExpr.Term`: a read of a global that was not assigned yet is its
initialiser's literal, an assignment replaces the global's definition like a local's. The Lir
code computes `T` at run time (`IntExpr.exprOps 0 T`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateGlobals

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Mem.Concrete (LiveInt nextIntAddress)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open ConvInt (isConvLoadedInt)
open StateExpr (Key Term term termP PtsTo values close)
open StateMem (Local Inv Fresh Defined defsOf update ptr PEnv)
open StateStmt (isLocal isFresh killsRun assignStmt initStmt uninitStmt Keys Overflows
  killsRun_halts killsRunZ_halts KLive killOf bound_pop fails_overflows boolSource_touched seqFocus_touched
  pure_unit_reaches)
open PtrStmt (updateP)
open State (Stmt closeSize maxSize)
open IntExpr (spec)
open LoadTask (Touched)
open LocalExpr (Shows)

/-! ## Statements over globals and locals -/

/-- A bound expression used as a return value, including a post-increment/decrement. -/
def returnValue (file : File Codec.wireModel Unit Unit) (e : Eff)
    (pts : Key → Option PtsTo := fun _ => none) : Option Term :=
  match e with
  | .mk _ (.bound body) =>
    match termP file pts body with
    | some t => some t
    | none => (Rmw.boundRmw file e).map fun (x, op) => Rmw.oldTerm x op
  | _ => none

/-- Return-value evaluation may update slots before returning its value. -/
theorem returnValue_runs {file : Program} {labels : Labels} {e : Eff} {t : Term}
    {pts : Key → Option PtsTo} (h : returnValue file e pts = some t) {env : Env} {m : Mem.Concrete.State}
    {ls : List Local} {ds : Key → Option IntExpr.Term} {ps : List Local} (inv : Inv env m ls ds ps pts)
    (hd : Defined ds t = true) (k : List Frame) (penv : PEnv env ps := by intro l hl; cases hl) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    t.Ok (values (defsOf ds)) ∧ ∃ m' ds', m'.stdout = m.stdout ∧ Inv env m' ls ds' ps pts ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (spec (t.val (values (defsOf ds)))), k, m'⟩ := by
  unfold returnValue at h
  split at h
  next ann body =>
    split at h
    next t' ht =>
      cases h
      have pre := ReturnLit.bound_reaches (file := file) (labels := labels) ann body env k m
      by_cases ok : t.Ok (values (defsOf ds))
      · right
        obtain ⟨xs', m', fr, hfr, -, tch, run⟩ := StateExpr.termP_runs (file := file) (labels := labels)
          t ht ok (.bound :: k) m (inv.locsP penv hd)
        exact ⟨ok, m', ds, tch.stdout, inv.touched tch,
          pre.trans ((Interleave.reaches_of_local file labels run).trans (bound_pop hfr _ k m'))⟩
      · exact .inl (StateStmt.Overflows.pre pre (fails_overflows
          (StateExpr.termP_fails (file := file) (labels := labels) t ht ok (.bound :: k) m
            (inv.locsP penv hd))))
    next =>
      cases hr : Rmw.boundRmw file (.mk ann (.bound body)) with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨x, op⟩ := pair
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst t
        have hd' : (ds x.key).isSome := by
          simpa [Defined, Rmw.oldTerm, StateExpr.Term.vars] using hd
        rcases Rmw.boundRmw_runs hr inv hd' k with ub | ⟨ok, m', out, inv', reach⟩
        · exact .inl ub
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, hop, -⟩ := Rmw.boundRmw_inv hr
          obtain ⟨ok', val⟩ := Rmw.oldTerm_ok_val x hop ok
          rw [← val] at reach
          exact .inr ⟨ok', m', _, out, inv', reach⟩
  next => cases h

/-- `return e;` in a block with the slots `ys` and the locals `xs`. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : List Sym) (e : Eff)
    (zs : List Sym := []) (pts : Key → Option PtsTo := fun _ => none) : Option Term :=
  match e with
  | .mk _ (.sseq (.mk _ (.base (some u, _))) b@(.mk _ (.bound _)) kr) =>
      if isFresh ys u = true ∧ isFresh zs u = true ∧ killsRun file ret u xs kr zs = true then
        returnValue file b pts
      else none
  | _ => none

/-- `if (c) A else B` (no `else`: `B` is `pure(unit)`): the test `c == 0` as a loaded integer,
`let strong c = bound(e) in let strong b = <c as a Core boolean> in if b then A else B`. The test's
term and the two arms. -/
def ifParts (file : File Codec.wireModel Unit Unit) (ys : List Sym) (e : Eff) (zs : List Sym := [])
    (pts : Key → Option PtsTo := fun _ => none) : Option (Term × Eff × Eff) :=
  match e with
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb (.mk _ (.if_ (.mk _ () (.sym b')) ea eb))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh ys c = true ∧ isFresh ys b = true ∧
          isFresh zs c = true ∧ isFresh zs b = true then
        (termP file pts ec).map fun tc => (tc, ea, eb)
      else none
  | _ => none

theorem ifParts_inv {f : File Codec.wireModel Unit Unit} {ys : List Sym} {e ea eb : Eff} {tc : Term}
    {zs : List Sym} {pts : Key → Option PtsTo} (h : ifParts f ys e zs pts = some (tc, ea, eb)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : Eff) (a3 a4 : List Annot)
      (b : Sym) (bty : BaseType) (cb : Eff) (a5 a6 : List Annot) (b' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb (.mk a5 (.if_ (.mk a6 () (.sym b')) ea eb))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh ys c = true ∧ isFresh ys b = true ∧
      isFresh zs c = true ∧ isFresh zs b = true ∧ termP f pts ec = some tc := by
  unfold ifParts at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨tc', htc, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
        hc.2.2.2.2.1, hc.2.2.2.2.2, htc⟩
    · cases h
  · cases h

theorem ifParts_size {f : File Codec.wireModel Unit Unit} {ys : List Sym} {e ea eb : Eff} {tc : Term}
    {zs : List Sym} {pts : Key → Option PtsTo}
    (h : ifParts f ys e zs pts = some (tc, ea, eb)) : sizeOf ea < sizeOf e ∧ sizeOf eb < sizeOf e := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, -⟩ := ifParts_inv h
  constructor <;> simp <;> omega

variable {file : Program} {labels : Labels}

/-- The kills of the locals `lk` (keys `xs`, the pointer locals `zs` among them) need their objects
live and their ids distinct. -/
theorem kills_facts {env : Env} {m : Mem.Concrete.State} {ls lk ps : List Local}
    {ds : Key → Option IntExpr.Term} {pts : Key → Option PtsTo} {zs : List Sym}
    (inv : Inv env m ls ds ps pts) (penv : PEnv env ps)
    (sub : ∀ l ∈ lk, (isLocal zs l.sym = true ∧ l ∈ ps) ∨ (isLocal zs l.sym = false ∧ l ∈ ls)) :
    (∀ l ∈ lk, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) ∧
    (∀ l ∈ lk, KLive zs m l) ∧
    (∀ a ∈ lk, ∀ b ∈ lk, a.sym.key ≠ b.sym.key → a.id ≠ b.id) := by
  refine ⟨fun l hl => (sub l hl).elim (fun h => penv l h.2) (fun h => inv.env l h.2), fun l hl => ?_,
    fun a ha b hb ne => ?_⟩
  · unfold KLive
    rcases sub l hl with ⟨hz, h⟩ | ⟨hz, h⟩
    · simp only [hz, ↓reduceIte]; exact inv.ptrs.live l h
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]; exact inv.live l h
  · rcases sub a ha with ⟨-, ha⟩ | ⟨-, ha⟩ <;> rcases sub b hb with ⟨-, hb⟩ | ⟨-, hb⟩
    · exact (inv.ptrs.apart a ha b hb ne).1
    · exact (inv.ptrs.sep a ha b hb).2.1
    · exact fun e => (inv.ptrs.sep b hb a ha).2.1 e.symm
    · exact (inv.apart a ha b hb ne).1

/-- `StateStmt.ret_halts` with globals and pointer locals: the slots `ls` (keys `ys`), the pointer
locals `ps` (keys `zs`), the locals `lk` (keys `xs`, `int` slots and pointer locals) killed before
the return. -/
theorem ret_haltsP {ret : Sym} (hret : ReturnLabel labels ret) {ys xs zs : List Sym} {e : Eff}
    {t : Term} {pts : Key → Option PtsTo} (h : retStmt file ret ys xs e zs pts = some t) {env : Env}
    {m : Mem.Concrete.State} {ls lk ps : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds ps pts) (penv : PEnv env ps) (hls : Keys ls ys) (hps : Keys ps zs)
    (hlk : Keys lk xs)
    (sub : ∀ l ∈ lk, (isLocal zs l.sym = true ∧ l ∈ ps) ∨ (isLocal zs l.sym = false ∧ l ∈ ls))
    (nodup : (xs.map (·.key)).Nodup)
    (hd : Defined ds t = true) {k : List Frame} (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0
      (close (defsOf ds) t) m.stdout := by
  unfold retStmt at h
  split at h
  next ann pann u ty bann e' kr =>
    split at h
    next cond =>
      obtain ⟨hfresh, hzfresh, hkr⟩ := cond
      let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
      have pre := ReturnConst.sequence_reaches file labels ann (.mk pann (.base (some u, ty)))
        (.mk bann (.bound e')) kr env k m
      rcases returnValue_runs h inv hd K penv with ub | ⟨ok, m₁, ds₁, out, inv₁, run⟩
      · exact Shows.pre pre (.inr ub)
      · left
        refine ⟨StateExpr.close_ok _ t (inv.defs_ok hd) ok, ?_⟩
        let v := spec (t.val (values (defsOf ds)))
        have inv₂ := inv₁.extend (x := u) (v := v) (hls.fresh hfresh)
        have penv₂ : PEnv (extendEnv [(u, v)] env) ps := fun l hl y hy => by
          rw [ConvInt.lookup_one_other (by rw [hy]; exact hps.fresh hzfresh l hl)]
          exact penv l hl y hy
        obtain ⟨henv, hlive, hids⟩ := kills_facts inv₂ penv₂ sub
        obtain ⟨m', out', reach⟩ := killsRunZ_halts hret zs xs lk hlk nodup hkr (extendEnv [(u, v)] env)
          hk m₁ henv hlive hids (StateExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
        refine ⟨m', out'.trans out, ?_⟩
        rw [StateExpr.close_val]
        exact pre.trans (run.trans ((ReturnLit.bind_reaches pann u ty v kr env k m₁).trans reach))
    next => cases h
  next => cases h

theorem ret_halts {ret : Sym} (hret : ReturnLabel labels ret) {ys xs : List Sym} {e : Eff}
    {t : Term} (h : retStmt file ret ys xs e = some t) {env : Env} {m : Mem.Concrete.State}
    {ls lk : List Local} {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls ys)
    (hlk : Keys lk xs) (sub : ∀ l ∈ lk, l ∈ ls) (nodup : (xs.map (·.key)).Nodup)
    (hd : Defined ds t = true) {k : List Frame} (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0
      (close (defsOf ds) t) m.stdout :=
  ret_haltsP hret h inv (fun _ h => by cases h) hls rfl hlk (fun l hl => .inr ⟨rfl, sub l hl⟩) nodup hd hk

/-- **An `if` statement** reaches undefined behaviour in its test, or one of its arms with the
slots unchanged: `B` when the test `c == 0` is `1`, `A` otherwise. -/
theorem if_runs {ys zs : List Sym} {e ea eb : Eff} {tc : Term} {pts : Key → Option PtsTo}
    (h : ifParts file ys e zs pts = some (tc, ea, eb))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} (inv : Inv env m ls ds ps pts) (penv : PEnv env ps) (hls : Keys ls ys)
    (hps : Keys ps zs) (hdc : Defined ds tc = true) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    (tc.Ok (values (defsOf ds)) ∧ ∃ env' m', m'.stdout = m.stdout ∧ Inv env' m' ls ds ps pts ∧
      PEnv env' ps ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr (if tc.val (values (defsOf ds)) = 1 then eb else ea) env', k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, hb', hcb, hfc, hfb, hzc, hzb, htc⟩ :=
    ifParts_inv h
  let σ := values (defsOf ds)
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea eb)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.termP_runs (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locsP penv hdc)
    let cv := tc.val σ
    let env₁ := extendEnv [(c, spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    let m₃ := SeqReach.focusMemory a5 m₂
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then ea else eb) env₂, k, m₃⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have tch₃ : Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₂ : Inv env₂ m₃ ls ds ps pts :=
      ((inv.touched tch₃).extend (hls.fresh hfc)).extend (hls.fresh hfb)
    have penv₂ : PEnv env₂ ps := fun l hl y hy => by
      rw [ConvInt.lookup_one_other (by rw [hy]; exact hps.fresh hzb l hl),
        ConvInt.lookup_one_other (by rw [hy]; exact hps.fresh hzc l hl)]
      exact penv l hl y hy
    refine ⟨okc, env₂, m₃, tch₃.stdout, inv₂, penv₂, pre.trans ?_⟩
    have hsel : (if flag then ea else eb) = (if tc.val σ = 1 then eb else ea) := by
      by_cases h1 : tc.val σ = 1 <;> simp [flag, cv, h1]
    rw [← hsel]
    exact enter
  · left
    exact StateStmt.Overflows.pre pre (fails_overflows (StateExpr.termP_fails (file := file)
      (labels := labels) tc htc okc (.bound :: K) m (inv.locsP penv hdc)))

/-- `e;`, an expression statement whose value is discarded: `bound(e)`. -/
def exprStmt (file : File Codec.wireModel Unit Unit) (e : Eff)
    (pts : Key → Option PtsTo := fun _ => none) : Option Term :=
  match e with
  | .mk _ (.bound e) => termP file pts e
  | _ => none

/-- **An expression statement** reaches undefined behaviour or its value, with the slots
unchanged. -/
theorem expr_runs {e : Eff} {t : Term} {pts : Key → Option PtsTo} (h : exprStmt file e pts = some t)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} (inv : Inv env m ls ds ps pts)
    (hd : Defined ds t = true) (k : List Frame) (penv : PEnv env ps := by intro l hl; cases hl) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    ∃ v m', m'.stdout = m.stdout ∧ Inv env m' ls ds ps pts ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value v, k, m'⟩ := by
  unfold exprStmt at h
  split at h
  · rename_i ann e'
    have pre := ReturnLit.bound_reaches (file := file) (labels := labels) ann e' env k m
    by_cases ok : t.Ok (values (defsOf ds))
    · right
      obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.termP_runs (file := file) (labels := labels)
        t h ok (.bound :: k) m (inv.locsP penv hd)
      exact ⟨_, m₁, tch.stdout, inv.touched tch,
        pre.trans ((Interleave.reaches_of_local file labels run).trans (bound_pop hfr _ k m₁))⟩
    · left
      exact StateStmt.Overflows.pre pre (fails_overflows (StateExpr.termP_fails (file := file)
        (labels := labels) t h ok (.bound :: k) m (inv.locsP penv hd)))
  · cases h

/-! ## Falling off the end of `main` -/

/-- `kill(int, x₁); …; kill(int, xₙ); pure(unit)`: the end of a block with the locals `xs`. -/
def killsEnd (file : File Codec.wireModel Unit Unit) (xs : List Sym) (e : Eff)
    (zs : List Sym := []) : Bool :=
  match xs with
  | [] => match e with
    | .mk _ (.pure (.mk _ () (.val .unit))) => true
    | _ => false
  | x :: xs => match e with
    | .mk _ (.sseq (.mk _ (.base (none, _))) kl rest) =>
        killOf file zs x kl && killsEnd file xs rest zs
    | _ => false

theorem killsEnd_nil {file : File Codec.wireModel Unit Unit} {e : Eff} {zs : List Sym}
    (h : killsEnd file [] e zs = true) :
    ∃ ann pann, e = .mk ann (.pure (.mk pann () (.val .unit))) := by
  simp only [killsEnd] at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

theorem killsEnd_cons {file : File Codec.wireModel Unit Unit} {x : Sym} {xs : List Sym} {e : Eff}
    {zs : List Sym} (h : killsEnd file (x :: xs) e zs = true) :
    ∃ ann pann ty kl rest, e = .mk ann (.sseq (.mk pann (.base (none, ty))) kl rest) ∧
      killOf file zs x kl = true ∧ killsEnd file xs rest zs = true := by
  simp only [killsEnd] at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, rfl, h.1, h.2⟩
  · cases h

/-- **The end of a block** kills its locals and reaches `unit`, keeping stdout. -/
theorem killsEnd_reaches (zs : List Sym) : (xs : List Sym) → (ls : List Local) → Keys ls xs →
    (xs.map (·.key)).Nodup →
    {e : Eff} → killsEnd file xs e zs = true → (env : Env) → (k : List Frame) → (m : Mem.Concrete.State) →
    (∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ ls, KLive zs m l) →
    (∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩
  | [], _, _, _, e, h, env, k, m, _, _, _ => by
    obtain ⟨ann, pann, rfl⟩ := killsEnd_nil h
    exact ⟨_, by simp, pure_unit_reaches ann pann env k m⟩
  | x :: xs, ls, hls, nodup, e, h, env, k, m, henv, hlive, hids => by
    cases ls with
    | nil => cases hls
    | cons l ls =>
      simp only [Keys, List.map_cons, List.cons.injEq] at hls
      obtain ⟨hxl, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsEnd_cons h
      have hzx : isLocal zs x = isLocal zs l.sym := by simp [isLocal, hxl]
      have kill : ∃ kann, Reaches file labels ⟨.effectExpr kl env,
          .strongBind (.mk pann (.base (none, ty))) rest env :: k, m⟩
          ⟨.value .unit, .strongBind (.mk pann (.base (none, ty))) rest env :: k,
            Locals.killed (focusMemory kann m) l.id⟩ := by
        have hl := hlive l (by simp)
        unfold killOf at hkl
        unfold KLive at hl
        rw [hzx] at hkl
        split at hkl
        · rename_i hz
          simp only [hz, ↓reduceIte] at hl
          exact StateStmt.killPtr_reaches hkl env _ m (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) hl
        · rename_i hz
          simp only [hz] at hl
          exact WrapObj.killAny_reaches (file := file) (labels := labels) hkl env _ m
            (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) hl
      obtain ⟨kann, kill⟩ := kill
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have ne : ∀ l' ∈ ls, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls, e, hxl] at hm
        exact hm
      obtain ⟨m', out, reach⟩ := killsEnd_reaches zs xs ls hls nodup hrest env k m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => ((hlive l' (by simp [hl'])).focus kann).killed l.id (ne l' hl'))
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb]))
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], ?_⟩
      exact (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans (kill.trans
        ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m₁).trans reach))

/-- From the frames `k`, the `unit` of the block's end, over at most one annotation frame, ends
`main` returning `0`. -/
def Falls (k : List Frame) : Prop :=
  ∀ (fr : Option (List Access)) (m : Mem.Concrete.State), ∃ m', m'.stdout = m.stdout ∧
    Reaches file labels ⟨.value .unit, (fr.map .annotations).toList ++ k, m⟩
      ⟨.halt (.defined (spec 0)), [], m'⟩

/-- `Specified(0)`: the default of `main`'s return label, what falling off its end returns. -/
def zeroDefault : PE → Bool
  | .mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer z)))]) => z == 0
  | _ => false

theorem zeroDefault_eval {p : PE} (h : zeroDefault p = true) (env : Env) :
    SeqReach.PureEval file labels p env (spec 0) := by
  unfold zeroDefault at h
  split at h
  · rename_i a a' z
    have hz : z = 0 := by simpa using h
    subst hz
    intro k m
    exact (PureEval.Eval.sound file _ (PureEval.Eval.ctor (PureEval.Eval.cons PureEval.Eval.val
      PureEval.Eval.nil) (by simp [primitive, runtimeValue, runtimeObject]; rfl))) labels _ _ rfl
  · cases h

/-- **`main`'s frames fall to `0`**: past its block, the return label's save binds its default
`0` and returns it. -/
theorem main_falls {pann sann bann pann' : List Annot} {bt0 bt : BaseType} {ret r r' : Sym}
    {info : BaseType × Option (Ctype × PassBy)} {p : PE} (hr : r'.key = r.key)
    (hz : zeroDefault p = true) (env : Env) (xs : List Access) :
    Falls (file := file) (labels := labels) [.strongBind (.mk pann (.base (none, bt0)))
      (.mk sann (.save (ret, bt) [(r, (info, p))] (.mk bann (.pure (.mk pann' () (.sym r')))))) env,
      .annotations xs] := by
  let SAVE : EE := .mk sann (.save (ret, bt) [(r, (info, p))] (.mk bann (.pure (.mk pann' () (.sym r')))))
  have body : ∀ (K : List Frame) (m : Mem.Concrete.State), Reaches file labels
      ⟨.effectExpr SAVE env, K, m⟩
      ⟨.value (spec 0), K, SeqReach.focusMemory bann (SeqReach.focusMemory sann m)⟩ := by
    intro K m
    refine (LoopReach.save_reaches sann (ret, bt) [(r, (info, p))] _ env [spec 0]
      (.cons (zeroDefault_eval hz env) .nil) K m).trans ?_
    exact SeqReach.effect_pure_reaches bann
      (SeqReach.pure_symbol pann' r' _ _ (ConvInt.lookup_one hr)) K _
  intro fr m
  cases fr with
  | none =>
    refine ⟨_, ?_, (ReturnConst.wildcard_sequence_reaches file labels pann bt0 .unit SAVE env _ m).trans
      ((body _ m).trans (ReturnConst.value_halts_annotations file labels _ xs _))⟩
    simp
  | some a =>
    refine ⟨_, ?_, (Locals.annotations_bind_reaches a pann bt0 .unit SAVE env _ m).trans
      ((body _ m).trans ((Locals.annotations_merge_reaches a xs _ _ _).trans
        (ReturnConst.value_halts_annotations file labels _ _ _)))⟩
    simp

/-! ## The block -/

/-- Assignments and discarded increment/decrement statements have the same slot update. -/
def assignOrRmw (file : File Codec.wireModel Unit Unit) (e : Eff)
    (pts : Key → Option PtsTo := fun _ => none) : Option (Sym × Term) :=
  match assignStmt file e pts with
  | some p => some p
  | none => (Rmw.rmwStmt file e).map fun (x, op) => (x, .bin op (.var x.key) (.lit 1))

/-- The shared assignment interface, including the read-modify-write footprint and overflow. -/
theorem assignOrRmw_runs {e : Eff} {x : Sym} {t : Term} {pts : Key → Option PtsTo}
    (h : assignOrRmw file e pts = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} (inv : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) (penv : PEnv env ps := by intro l hl; cases hl) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ps pts ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold assignOrRmw at h
  split at h
  next pair ha =>
    cases h
    exact StateStmt.assign_runs ha inv hl hx hd k penv
  next =>
    cases hr : Rmw.rmwStmt file e with
    | none => simp [hr] at h
    | some pair =>
      obtain ⟨y, op⟩ := pair
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd' : (ds y.key).isSome := by
        simpa [Defined, StateExpr.Term.vars] using hd
      simpa only [hx] using Rmw.rmw_runs hr inv hd' k

/-- Which statement `s` is (an `if` is `ifParts`). -/
def classify (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : List Sym) (s : Eff)
    (zs : List Sym := []) (pts : Key → Option PtsTo := fun _ => none) : Option Stmt :=
  match retStmt file ret ys xs s zs pts with
  | some t => some (.ret t)
  | none => match assignOrRmw file s pts with
    | some (x, t) => some (.assign x t)
    | none => match initStmt file s pts with
      | some (x, t) => some (.init x t)
      | none => (StateStmt.uninitAny file s).map .uninit

/-- What the classification of `s` says about `s`. -/
def Shape (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : List Sym) (s : Eff)
    (zs : List Sym) (pts : Key → Option PtsTo) : Stmt → Prop
  | .ret t => retStmt file ret ys xs s zs pts = some t
  | .ifRet _ _ => False
  | .assign x t => assignOrRmw file s pts = some (x, t)
  | .init x t => initStmt file s pts = some (x, t)
  | .uninit x => StateStmt.uninitAny file s = some x

theorem classify_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {ys xs zs : List Sym}
    {pts : Key → Option PtsTo} {s : Eff} {st : Stmt} (h : classify file ret ys xs s zs pts = some st) :
    Shape file ret ys xs s zs pts st := by
  unfold classify at h
  split at h
  next t ht => cases h; exact ht
  next =>
    split at h
    next x t hx => cases h; exact hx
    next =>
      split at h
      next x t hx => cases h; exact hx
      next =>
        cases hu : StateStmt.uninitAny file s with
        | none => simp [hu] at h
        | some x =>
          simp only [hu, Option.map_some, Option.some.injEq] at h
          subst h
          exact hu

/-- A statement about a pointer local `r` (one of `zs`): `r = &x;` or `int *r = &x;` for an `int`
slot `x` (one of `ys`), the unspecified store of `int *r;`, or `int *r = NULL;`, with `r`'s new
target. -/
def ptrStmt (ys zs : List Sym) (e : Eff) : Option (Sym × Option PtsTo) :=
  match PtrStmt.ptrAssignStmt e with
  | some (r, x) => if isLocal zs r = true ∧ isLocal ys x = true then some (r, some (.addr x)) else none
  | none => match PtrStmt.ptrInitStmt e with
    | some (r, x) => if isLocal zs r = true ∧ isLocal ys x = true then some (r, some (.addr x)) else none
    | none => match PtrStmt.ptrUninitStmt e with
      | some r => if isLocal zs r = true then some (r, none) else none
      | none => match PtrStmt.ptrNullInitStmt e with
        | some r => if isLocal zs r = true then some (r, some .null) else none
        | none => none

/-- **A pointer statement** updates the pointer local's target. -/
theorem ptrStmt_runs {ys zs : List Sym} {e : Eff} {r : Sym} {t : Option PtsTo}
    (h : ptrStmt ys zs e = some (r, t)) {env : Env} {m : Mem.Concrete.State} {ls ps : List Local}
    {ds : Key → Option IntExpr.Term} {pts : Key → Option PtsTo} (inv : Inv env m ls ds ps pts)
    (penv : PEnv env ps) (hls : Keys ls ys) (hps : Keys ps zs) (k : List Frame) :
    ∃ fr : Option (List Access), ∃ m', m'.stdout = m.stdout ∧ Inv env m' ls ds ps (updateP pts r.key t) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, (fr.map .annotations).toList ++ k, m'⟩ := by
  unfold ptrStmt at h
  split at h
  · rename_i r' x ha
    split at h
    · rename_i hc
      cases h
      obtain ⟨l, hl, hk⟩ := State.Keys.mem_of_local hps hc.1
      obtain ⟨lq, hlq, hq⟩ := State.Keys.mem_of_local hls hc.2
      obtain ⟨m', out, inv', reach⟩ := PtrStmt.ptrAssign_runs ha inv hl hk hlq hq k penv
      rw [← hk] at inv'
      exact ⟨none, m', out, inv', by simpa using reach⟩
    · cases h
  · split at h
    · rename_i r' x hi
      split at h
      · rename_i hc
        cases h
        obtain ⟨l, hl, hk⟩ := State.Keys.mem_of_local hps hc.1
        obtain ⟨lq, hlq, hq⟩ := State.Keys.mem_of_local hls hc.2
        obtain ⟨m', xs, out, inv', reach⟩ := PtrStmt.ptrInit_runs hi inv hl hk hlq hq k penv
        rw [← hk] at inv'
        exact ⟨some xs, m', out, inv', by simpa using reach⟩
      · cases h
    · split at h
      · rename_i r' hu
        split at h
        · rename_i hc
          cases h
          obtain ⟨l, hl, hk⟩ := State.Keys.mem_of_local hps hc
          obtain ⟨m', xs, out, inv', reach⟩ := PtrStmt.ptrUninit_runs hu inv hl hk k penv
          rw [← hk] at inv'
          exact ⟨some xs, m', out, inv', by simpa using reach⟩
        · cases h
      · split at h
        · rename_i r' hn
          split at h
          · rename_i hc
            cases h
            obtain ⟨l, hl, hk⟩ := State.Keys.mem_of_local hps hc
            obtain ⟨m', xs, out, inv', reach⟩ := PtrStmt.ptrNullInit_runs hn inv hl hk k penv
            rw [← hk] at inv'
            exact ⟨some xs, m', out, inv', by simpa using reach⟩
          · cases h
        · cases h

/-- `s; rest`: a wildcard strong sequence, its two parts. -/
def seqParts : Eff → Option (Eff × Eff)
  | .mk _ (.sseq (.mk _ (.base (none, _))) s rest) => some (s, rest)
  | _ => none

theorem seqParts_inv {e s rest : Eff} (h : seqParts e = some (s, rest)) :
    ∃ ann pann ty, e = .mk ann (.sseq (.mk pann (.base (none, ty))) s rest) := by
  unfold seqParts at h
  split at h
  · cases h; exact ⟨_, _, _, rfl⟩
  · cases h

theorem seqParts_size {e s rest : Eff} (h : seqParts e = some (s, rest)) :
    sizeOf s + sizeOf rest < sizeOf e := by
  obtain ⟨ann, pann, ty, rfl⟩ := seqParts_inv h
  simp
  omega

/-- `pure(unit)`. -/
def isUnit : Eff → Bool
  | .mk _ (.pure (.mk _ () (.val .unit))) => true
  | _ => false

theorem isUnit_inv {e : Eff} (h : isUnit e = true) :
    ∃ ann pann, e = .mk ann (.pure (.mk pann () (.val .unit))) := by
  unfold isUnit at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

/-- The number of nodes of a closed expression. -/
def termSize : IntExpr.Term → Nat
  | .lit _ => 1
  | .var => 1
  | .bin _ a b => 1 + termSize a + termSize b
  | .cmp _ _ _ a b => 1 + termSize a + termSize b
  | .cond c a b => 1 + termSize c + termSize a + termSize b
  | .bit _ a b => 1 + termSize a + termSize b
  | .divpos _ _ a => 1 + termSize a

/-- How many statements a block may visit: an `if` runs the rest of the block after each arm. -/
def budget : Nat := 65536

/-- The statements of a block with the slots `ys` and the locals `xs`, the definitions `ds` (sizes
`sz`): the statement `e`, then the pending statements `todo` in order. A sequence `s; rest` runs
`s` with `rest` pending, `pure(unit)` (an empty statement, the end of a nested block) goes on with the
next pending statement, `if (c) A else B` runs each arm before the pending statements and selects
at run time (`StmtIf.choose`). `n` bounds the statements visited; the result is the closed
expression and what is left of `n`. -/
def run (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs zs : List Sym) (fall : Bool) :
    (Key → Option PtsTo) → (Key → Option IntExpr.Term) → (Key → Nat) → Nat → Eff → List Eff →
      Option (IntExpr.Term × Nat)
  | _, _, _, 0, _, _ => none
  | pts, ds, sz, n + 1, e, todo =>
    match _hi : ifParts file ys e zs pts with
    | some (tc, ea, eb) =>
      if Defined ds tc = true ∧ closeSize sz tc ≤ maxSize then
        match run file ret ys xs zs fall pts ds sz n ea todo with
        | some (ta, n₁) =>
          match run file ret ys xs zs fall pts ds sz n₁ eb todo with
          | some (tb, n₂) =>
            if termSize (StmtIf.choose (close (defsOf ds) tc) ta tb) ≤ maxSize then
              some (StmtIf.choose (close (defsOf ds) tc) ta tb, n₂)
            else none
          | none => none
        | none => none
      else none
    | none =>
      match classify file ret ys xs e zs pts with
      | some (.ret t) =>
        if Defined ds t = true ∧ closeSize sz t ≤ maxSize then some (close (defsOf ds) t, n)
        else none
      | some (.assign x t) =>
        if isLocal ys x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
          match todo with
          | [] => none
          | r :: todo =>
            run file ret ys xs zs fall pts (update ds x.key (some (close (defsOf ds) t)))
              (fun q => if q = x.key then closeSize sz t else sz q) n r todo
        else none
      | some (.init x t) =>
        if isLocal ys x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
          match todo with
          | [] => none
          | r :: todo =>
            run file ret ys xs zs fall pts (update ds x.key (some (close (defsOf ds) t)))
              (fun q => if q = x.key then closeSize sz t else sz q) n r todo
        else none
      | some (.uninit x) =>
        if isLocal ys x = true then
          match todo with
          | [] => none
          | r :: todo => run file ret ys xs zs fall pts (update ds x.key none) sz n r todo
        else none
      | _ =>
        match ptrStmt ys zs e with
        | some (r, t) =>
          match todo with
          | [] => none
          | r' :: todo => run file ret ys xs zs fall (updateP pts r.key t) ds sz n r' todo
        | none =>
        match exprStmt file e pts with
        | some t =>
          if Defined ds t = true ∧ closeSize sz t ≤ maxSize then
            match todo with
            | [] => none
            | r :: todo => run file ret ys xs zs fall pts ds sz n r todo
          else none
        | none =>
          match _hs : seqParts e with
          | some (s, rest) =>
            if fall = true ∧ todo.isEmpty = true ∧ killsEnd file xs e zs = true then some (.lit 0, n)
            else run file ret ys xs zs fall pts ds sz n s (rest :: todo)
          | none =>
            if isUnit e = true then
              match todo with
              | [] => if fall = true ∧ xs.isEmpty = true then some (.lit 0, n) else none
              | r :: todo => run file ret ys xs zs fall pts ds sz n r todo
            else none
termination_by _ _ _ _ e todo => sizeOf e + (todo.map sizeOf).sum
decreasing_by
  all_goals first
    | (have := (ifParts_size _hi).1; omega)
    | (have := (ifParts_size _hi).2; omega)
    | (have := seqParts_size _hs; simp; omega)
    | (cases e; simp)

/-! ## The pending statements -/

/-- `env` maps the slots' symbols to their pointers (the environment part of `Inv`). -/
def EnvOk (env : Env) (ls : List Local) : Prop :=
  ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)

theorem inv_withEnv {env env' : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (h : EnvOk env' ls) :
    Inv env' m ls ds :=
  ⟨h, inv.live, inv.apart, inv.defs⟩

theorem envOk_of {env : Env} {m : Mem.Concrete.State} {ls ps : List Local}
    {ds : Key → Option IntExpr.Term} {pts : Key → Option PtsTo} (inv : Inv env m ls ds ps pts)
    (penv : PEnv env ps) : EnvOk env (ls ++ ps) :=
  fun l hl => (List.mem_append.mp hl).elim (inv.env l) (penv l)

theorem inv_withEnvP {env env' : Env} {m : Mem.Concrete.State} {ls ps : List Local}
    {ds : Key → Option IntExpr.Term} {pts : Key → Option PtsTo} (inv : Inv env m ls ds ps pts)
    (h : EnvOk env' (ls ++ ps)) : Inv env' m ls ds ps pts :=
  haveI := inv.ptrs
  ⟨fun l hl => h l (List.mem_append_left _ hl), inv.live, inv.apart, inv.defs⟩

theorem penv_of {env' : Env} {ls ps : List Local} (h : EnvOk env' (ls ++ ps)) : PEnv env' ps :=
  fun l hl => h l (List.mem_append_right _ hl)

/-- The frames `k` hold the pending statements `todo`: each a wildcard strong sequence over an
environment of the slots, among access annotation frames, above a continuation without boundary
from which, when `fall`, the end of the block returns `0` (`Falls`). -/
inductive Pending (ls : List Local) (fall : Bool) : List Eff → List Frame → Prop
  | base {k : List Frame} : NoBoundary k → (fall = true → Falls (file := file) (labels := labels) k) →
      Pending ls fall [] k
  | ann {todo : List Eff} {k : List Frame} (xs : List Access) :
      Pending ls fall todo k → Pending ls fall todo (.annotations xs :: k)
  | bind {todo : List Eff} {k : List Frame} {env : Env} (pann : List Annot) (ty : BaseType)
      (rest : Eff) : EnvOk env ls → Pending ls fall todo k →
      Pending ls fall (rest :: todo) (.strongBind (.mk pann (.base (none, ty))) rest env :: k)

theorem Pending.noBoundary {ls : List Local} {fall : Bool} {todo : List Eff} {k : List Frame}
    (p : Pending (file := file) (labels := labels) ls fall todo k) : NoBoundary k := by
  induction p with
  | base hk _ => exact hk
  | ann _ _ ih => exact noBoundary_cons ih trivial
  | bind _ _ _ _ _ ih => exact noBoundary_cons ih trivial

/-- The value of a finished statement, over at most one annotation frame, reaches the next pending
statement. -/
theorem Pending.resume {ls : List Local} {fall : Bool} {todo : List Eff} {k : List Frame}
    (p : Pending (file := file) (labels := labels) ls fall todo k) (v : Val) :
    ∀ (fr : Option (List Access)) (m : Mem.Concrete.State) (rest : Eff) (todo' : List Eff),
      todo = rest :: todo' → ∃ env k', EnvOk env ls ∧
        Pending (file := file) (labels := labels) ls fall todo' k' ∧
        Reaches file labels ⟨.value v, (fr.map .annotations).toList ++ k, m⟩
          ⟨.effectExpr rest env, k', m⟩ := by
  induction p with
  | base _ _ => intro _ _ _ _ h; cases h
  | ann xs p ih =>
    intro fr m rest todo' h
    cases fr with
    | none => exact ih (some xs) m rest todo' h
    | some a =>
      obtain ⟨env, k', he, p', r⟩ := ih (some (a ++ xs)) m rest todo' h
      exact ⟨env, k', he, p', (Locals.annotations_merge_reaches a xs v _ m).trans r⟩
  | bind pann ty rest₀ he p _ =>
    intro fr m rest todo' h
    cases h
    cases fr with
    | none =>
      exact ⟨_, _, he, p, ReturnConst.wildcard_sequence_reaches file labels pann ty v rest₀ _ _ m⟩
    | some a =>
      exact ⟨_, _, he, .ann a p, Locals.annotations_bind_reaches a pann ty v rest₀ _ _ m⟩

/-- With no statement pending, the end of the block returns `0`. -/
theorem Pending.falls {ls : List Local} {fall : Bool} {todo : List Eff} {k : List Frame}
    (p : Pending (file := file) (labels := labels) ls fall todo k) (hf : fall = true) :
    todo = [] → Falls (file := file) (labels := labels) k := by
  induction p with
  | base _ f => intro _; exact f hf
  | ann xs p ih =>
    intro h fr m
    cases fr with
    | none => exact ih h (some xs) m
    | some a =>
      obtain ⟨m', out, r⟩ := ih h (some (a ++ xs)) m
      exact ⟨m', out, (Locals.annotations_merge_reaches a xs .unit _ m).trans r⟩
  | bind _ _ _ _ _ _ => intro h; cases h

/-- `run_halts` for a statement and pending statements of size below `N`. -/
theorem run_halts_lt {ret : Sym} (hret : ReturnLabel labels ret) {ys xs zs : List Sym} {fall : Bool}
    (nodup : (xs.map (·.key)).Nodup) {ls lk ps : List Local} (hls : Keys ls ys) (hlk : Keys lk xs)
    (hps : Keys ps zs)
    (sub : ∀ l ∈ lk, (isLocal zs l.sym = true ∧ l ∈ ps) ∨ (isLocal zs l.sym = false ∧ l ∈ ls))
    (N : Nat) :
    ∀ (pts : Key → Option PtsTo) (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (n : Nat) (e : Eff)
      (todo : List Eff) {T : IntExpr.Term} {n' : Nat}, sizeOf e + (todo.map sizeOf).sum < N →
      run file ret ys xs zs fall pts ds sz n e todo = some (T, n') → ∀ (env : Env) (m : Mem.Concrete.State),
      Inv env m ls ds ps pts → PEnv env ps → ∀ (k : List Frame),
      Pending (file := file) (labels := labels) (ls ++ ps) fall todo k →
      Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 T m.stdout := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ hN; omega
  | succ N ih =>
  intro pts ds sz n e todo T n' hN h env m inv penv k p
  have he1 : 0 < sizeOf e := by cases e; simp
  unfold run at h
  split at h
  next => cases h
  next n =>
    split at h
    next tc ea eb hi =>
      split at h
      next hd =>
        split at h
        next ta n₁ hA =>
          split at h
          next tb n₂ hB =>
            split at h
            next =>
              cases h
              rcases if_runs hi inv penv hls hps hd.1 k with ub | ⟨okc, env', m', out, inv', penv', reach⟩
              · exact .inr ub
              · have okC := StateExpr.close_ok (defsOf ds) tc (inv.defs_ok hd.1) okc
                by_cases h1 : tc.val (values (defsOf ds)) = 1
                · simp only [h1, ↓reduceIte] at reach
                  have o := ih pts ds sz n₁ eb todo (by have := (ifParts_size hi).2; omega) hB env' m' inv'
                    penv' k p
                  rw [out] at o
                  exact State.shows_choose_right okC (by rw [StateExpr.close_val]; exact h1)
                    (Shows.pre reach o)
                · simp only [h1, ↓reduceIte] at reach
                  have o := ih pts ds sz n ea todo (by have := (ifParts_size hi).1; omega) hA env' m' inv'
                    penv' k p
                  rw [out] at o
                  exact State.shows_choose_left okC (by rw [StateExpr.close_val]; exact h1)
                    (Shows.pre reach o)
            next => cases h
          next => cases h
        next => cases h
      next => cases h
    next hi =>
      split at h
      next t hc =>
        split at h
        next hd =>
          cases h
          exact ret_haltsP hret (classify_spec hc) inv penv hls hps hlk sub nodup hd.1 p.noBoundary
        next => cases h
      next x t hc =>
        split at h
        next hd =>
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
            rw [State.update_key hx] at h
            rcases assignOrRmw_runs (classify_spec hc) inv hl hx hd.2.1 k penv with
              ub | ⟨-, m', out, inv', reach⟩
            · exact .inr ub
            · obtain ⟨env', k', he, p', r'⟩ := p.resume .unit none m' r todo' rfl
              have o := ih _ _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
                (inv_withEnvP inv' he) (penv_of he) k' p'
              rw [out] at o
              exact Shows.pre (reach.trans r') o
        next => cases h
      next x t hc =>
        split at h
        next hd =>
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
            rw [State.update_key hx] at h
            rcases StateStmt.init_runs (classify_spec hc) inv hl hx hd.2.1 k penv with
              ub | ⟨-, m', ys', out, inv', reach⟩
            · exact .inr ub
            · obtain ⟨env', k', he, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
              have o := ih _ _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
                (inv_withEnvP inv' he) (penv_of he) k' p'
              rw [out] at o
              exact Shows.pre (reach.trans r') o
        next => cases h
      next x hc =>
        split at h
        next hd =>
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd
            rw [State.update_key hx] at h
            obtain ⟨m', ys', out, inv', reach⟩ := StateStmt.uninitAny_runs (classify_spec hc) inv hl hx k
            obtain ⟨env', k', he, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
            have o := ih _ _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
              (inv_withEnvP inv' he) (penv_of he) k' p'
            rw [out] at o
            exact Shows.pre (reach.trans r') o
        next => cases h
      next =>
        split at h
        next r t hpt =>
          split at h
          next => cases h
          next r' todo' =>
            obtain ⟨fr, m', out, inv', reach⟩ := ptrStmt_runs hpt inv penv hls hps k
            obtain ⟨env', k', he, p', r''⟩ := p.resume .unit fr m' r' todo' rfl
            have o := ih _ _ _ n r' todo' (by simp at hN ⊢; omega) h env' m'
              (inv_withEnvP inv' he) (penv_of he) k' p'
            rw [out] at o
            exact Shows.pre (reach.trans r'') o
        next hpt =>
        split at h
        next t hx =>
          split at h
          next hd =>
            split at h
            next => cases h
            next r todo' =>
              rcases expr_runs hx inv hd.1 k penv with ub | ⟨v, m', out, inv', reach⟩
              · exact .inr ub
              · obtain ⟨env', k', he, p', r'⟩ := p.resume v none m' r todo' rfl
                have o := ih pts ds sz n r todo' (by simp at hN ⊢; omega) h env' m'
                  (inv_withEnvP inv' he) (penv_of he) k' p'
                rw [out] at o
                exact Shows.pre (reach.trans r') o
          next => cases h
        next hx =>
          split at h
          next s rest hs =>
            obtain ⟨ann, pann, ty, rfl⟩ := seqParts_inv hs
            split at h
            next hk =>
              cases h
              obtain ⟨hf, hnil, hke⟩ := hk
              have hnil' : todo = [] := List.isEmpty_iff.mp hnil
              obtain ⟨henv, hlive, hids⟩ := kills_facts inv penv sub
              obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) zs xs lk hlk
                nodup hke env k m henv hlive hids
              obtain ⟨m'', out', fin⟩ := p.falls hf hnil' none m'
              exact .inl ⟨show ConvInt.IsInt 0 by constructor <;> omega, m'', out'.trans out,
                reach.trans fin⟩
            next =>
              exact Shows.pre (ReturnConst.sequence_reaches file labels ann _ s rest env k m)
                (ih pts ds sz n s (rest :: todo) (by simp at hN ⊢; omega) h env m inv penv _
                  (.bind pann ty rest (envOk_of inv penv) p))
          next hs =>
            split at h
            next hu =>
              obtain ⟨ann, pann, rfl⟩ := isUnit_inv hu
              split at h
              next =>
                split at h
                next hk =>
                  cases h
                  obtain ⟨hf, hxs⟩ := hk
                  have hxs' : xs = [] := List.isEmpty_iff.mp hxs
                  obtain ⟨henv, hlive, hids⟩ := kills_facts inv penv sub
                  obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) zs xs lk
                    hlk nodup (e := .mk ann (.pure (.mk pann () (.val .unit)))) (by rw [hxs']; rfl)
                    env k m henv hlive hids
                  obtain ⟨m'', out', fin⟩ := p.falls hf rfl none m'
                  exact .inl ⟨show ConvInt.IsInt 0 by constructor <;> omega, m'', out'.trans out,
                    reach.trans fin⟩
                next => cases h
              next r todo' =>
                obtain ⟨env', k', he, p', reach⟩ :=
                  p.resume .unit none (focusMemory ann m) r todo' rfl
                have o := ih pts ds sz n r todo' (by simp at hN ⊢; omega) h env' (focusMemory ann m)
                  (inv_withEnvP (inv.focus ann) he) (penv_of he) k' p'
                rw [ReturnConst.focusMemory_stdout] at o
                exact Shows.pre ((pure_unit_reaches ann pann env k m).trans reach) o
            next => cases h

/-- **The statements** show the value of the closed expression, or undefined behaviour. -/
theorem run_halts {ret : Sym} (hret : ReturnLabel labels ret) {ys xs zs : List Sym} {fall : Bool}
    (nodup : (xs.map (·.key)).Nodup) {ls lk ps : List Local} (hls : Keys ls ys) (hlk : Keys lk xs)
    (hps : Keys ps zs)
    (sub : ∀ l ∈ lk, (isLocal zs l.sym = true ∧ l ∈ ps) ∨ (isLocal zs l.sym = false ∧ l ∈ ls))
    (pts : Key → Option PtsTo) (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (n : Nat) (e : Eff)
    (todo : List Eff) {T : IntExpr.Term} {n' : Nat}
    (h : run file ret ys xs zs fall pts ds sz n e todo = some (T, n')) (env : Env) (m : Mem.Concrete.State)
    (inv : Inv env m ls ds ps pts) (penv : PEnv env ps) (k : List Frame)
    (p : Pending (file := file) (labels := labels) (ls ++ ps) fall todo k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 T m.stdout :=
  run_halts_lt hret nodup hls hlk hps sub _ pts ds sz n e todo (Nat.lt_succ_self _) h env m inv penv k p

/-- The startup memory with the `int` locals `ls` and then the pointer locals `ps` created:
nothing died, ids below the next one, every local at or above the last address, which is at most
`16` bytes per local below `errno`. -/
structure FreshP (m : Mem.Concrete.State) (ls ps : List Local) : Prop where
  dead : m.dead = []
  ids : ∀ l ∈ ls ++ ps, l.id < m.nextId
  addrs : ∀ l ∈ ls ++ ps, m.lastAddress ≤ l.addr
  room : StartupReach.errnoAddr - 16 * (ls.length + ps.length) ≤ m.lastAddress

/-- The pointer locals of a block after its `int` locals `ws` (a block without globals):
`int *p;` creations, then the statements. -/
def blockP (file : File Codec.wireModel Unit Unit) (ret : Sym) (fall : Bool)
    (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (ws : List Sym) : List Sym → Eff → Option IntExpr.Term
  | zs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    if PtrStmt.createPtrOf cr = true ∧ isFresh (ws ++ zs) x = true ∧ (ws ++ zs).length < 1024 then
      blockP file ret fall ds sz ws (zs ++ [x]) rest
    else none
  | zs, e =>
    if ((ws ++ zs).map (·.key)).Nodup then
      (run file ret ws (ws ++ zs) zs fall (fun _ => none) ds sz budget e []).map (·.1)
    else none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- **The pointer locals of a block**: creating them keeps `Inv`, then its statements show. -/
theorem blockP_halts {ret : Sym} (hret : ReturnLabel labels ret) {fall : Bool}
    {ds : Key → Option IntExpr.Term} {sz : Key → Nat} (ws : List Sym) (zs : List Sym) (e : Eff)
    {T : IntExpr.Term} (h : blockP file ret fall ds sz ws zs e = some T) (env : Env)
    (m : Mem.Concrete.State) (ls ps : List Local) (inv : Inv env m ls ds ps (fun _ => none))
    (penv : PEnv env ps) (hls : Keys ls ws) (hps : Keys ps zs)
    (good : ∀ l ∈ ls, 0 < l.addr ∧ l.addr < 18446744073709551616 ∧ l.addr % 4 = 0)
    (fresh : FreshP m ls ps) (k : List Frame)
    (hk : NoBoundary k) (falls : fall = true → Falls (file := file) (labels := labels) k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 T m.stdout := by
  have hlen : ls.length + ps.length = (ws ++ zs).length := by
    have h1 := congrArg List.length hls
    have h2 := congrArg List.length hps
    simp only [List.length_map] at h1 h2
    simp [h1, h2]
  unfold blockP at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      have hb := StrMem.ptrAddr_bounds m
      have hpos : 0 < StrMem.ptrAddr m := by
        have := fresh.room
        simp only [StartupReach.errnoAddr] at this
        omega
      let REST := rest
      let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      obtain ⟨ann, pref, t, create⟩ := PtrStmt.createPtrOf_reaches (file := file) (labels := labels) hcr
        env K m hpos
      let m₁ := StrMem.createdPtr pref t (ReturnConst.focusMemory ann m)
      let nl : Local := ⟨x, m.nextId, StrMem.ptrAddr m⟩
      let env₁ := extendEnv [(x, ptr nl)] env
      have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
      have hfx' : isFresh ws x = true ∧ isFresh zs x = true := by
        simpa [isFresh, List.all_append] using hfx
      have fxl : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx'.1
      have fxp : ∀ l ∈ ps, l.sym.key ≠ x.key := hps.fresh hfx'.2
      have hfm : ReturnConst.focusMemory ann m = SeqReach.focusMemory ann m := PrintfStmt.focus_same ann m
      have keeps : StrMem.Keeps m m₁ := by
        have := PrintfStd.keeps_focus ann m
        rw [← hfm] at this
        exact this.trans (StrMem.createdPtr_keeps pref t _)
      obtain ⟨fl, fn, fd, fo, -⟩ := StrMem.createdPtr_facts pref t (ReturnConst.focusMemory ann m)
      have fnext : (ReturnConst.focusMemory ann m).nextId = m.nextId := by
        rw [hfm]; exact PrintfStd.focus_nextId ann m
      have flast : (ReturnConst.focusMemory ann m).lastAddress = m.lastAddress := by
        rw [hfm]; exact PrintfStd.focus_lastAddress ann m
      have fdead : (ReturnConst.focusMemory ann m).dead = m.dead := by
        obtain ⟨loc, hf⟩ := Locals.focusMemory_eq ann m
        rw [hf]
      have fpa : StrMem.ptrAddr (ReturnConst.focusMemory ann m) = StrMem.ptrAddr m := by
        unfold StrMem.ptrAddr; rw [flast]
      have ids : ∀ l ∈ ls ++ ps, l.id < m.nextId := fresh.ids
      have addrs : ∀ l ∈ ls ++ ps, m.lastAddress ≤ l.addr := fresh.addrs
      have newslot : StrMem.PtrSlot m₁ nl.id nl.addr := by
        have := StrMem.createdPtr_slot pref t (ReturnConst.focusMemory ann m)
          (by rw [fdead, fresh.dead, fnext]; simp)
        rwa [fnext, fpa] at this
      have P := inv.ptrs
      have pinv : StateMem.PInv m₁ ls (ps ++ [nl]) (fun _ => none) := by
        refine ⟨?_, ?_, ?_, ?_, fun _ _ h => by simp at h⟩
        · intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · exact (P.live l hl).keeps keeps
          · obtain rfl := List.mem_singleton.mp hl; exact newslot
        · intro a ha b hb ne
          rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
          · exact P.apart a ha b hb ne
          · obtain rfl := List.mem_singleton.mp hb
            have := addrs a (List.mem_append_right _ ha)
            exact ⟨Int.ne_of_lt (ids a (List.mem_append_right _ ha)),
              by show a.addr + 8 ≤ StrMem.ptrAddr m ∨ StrMem.ptrAddr m + 8 ≤ a.addr; omega⟩
          · obtain rfl := List.mem_singleton.mp ha
            have := addrs b (List.mem_append_right _ hb)
            exact ⟨Int.ne_of_gt (ids b (List.mem_append_right _ hb)),
              by show StrMem.ptrAddr m + 8 ≤ b.addr ∨ b.addr + 8 ≤ StrMem.ptrAddr m; omega⟩
          · obtain rfl := List.mem_singleton.mp ha
            obtain rfl := List.mem_singleton.mp hb
            exact absurd rfl ne
        · intro a ha b hb
          rcases List.mem_append.mp ha with ha | ha
          · exact P.sep a ha b hb
          · obtain rfl := List.mem_singleton.mp ha
            have := addrs b (List.mem_append_left _ hb)
            exact ⟨fun e => fxl b hb e.symm, Int.ne_of_gt (ids b (List.mem_append_left _ hb)),
              by show StrMem.ptrAddr m + 8 ≤ b.addr ∨ b.addr + 4 ≤ StrMem.ptrAddr m; omega⟩
        · exact fun _ => good
      have inv₁ : Inv env₁ m₁ ls ds (ps ++ [nl]) (fun _ => none) := by
        refine @StateMem.Inv.mk _ _ _ _ _ _ pinv ?_ ?_ inv.apart ?_
        · intro l hl y hy
          rw [ConvInt.lookup_one_other (by rw [hy]; exact fxl l hl)]
          exact inv.env l hl y hy
        · intro l hl
          exact PtrStmt.liveInt_keeps (inv.live l hl) keeps (ids l (List.mem_append_left _ hl))
        · intro q d hd
          obtain ⟨ok, l, hl, hk, slot⟩ := inv.defs q d hd
          exact ⟨ok, l, hl, hk, PtrStmt.slot_keeps slot keeps (ids l (List.mem_append_left _ hl))
            (addrs l (List.mem_append_left _ hl))⟩
      have penv₁ : PEnv env₁ (ps ++ [nl]) := by
        intro l hl y hy
        rcases List.mem_append.mp hl with hl | hl
        · rw [ConvInt.lookup_one_other (by rw [hy]; exact fxp l hl)]
          exact penv l hl y hy
        · obtain rfl := List.mem_singleton.mp hl
          exact ConvInt.lookup_one hy
      have hps₁ : Keys (ps ++ [nl]) (zs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hps ⊢
        rw [hps]
      have fresh₁ : FreshP m₁ ls (ps ++ [nl]) := by
        refine ⟨by rw [fd, fdead, fresh.dead], ?_, ?_, ?_⟩
        · intro l hl
          rw [fn, fnext]
          rcases List.mem_append.mp hl with hl | hl
          · have := ids l (List.mem_append_left _ hl); omega
          · rcases List.mem_append.mp hl with hl | hl
            · have := ids l (List.mem_append_right _ hl); omega
            · obtain rfl := List.mem_singleton.mp hl; show m.nextId < m.nextId + 1; omega
        · intro l hl
          rw [fl, fpa]
          rcases List.mem_append.mp hl with hl | hl
          · have := addrs l (List.mem_append_left _ hl); omega
          · rcases List.mem_append.mp hl with hl | hl
            · have := addrs l (List.mem_append_right _ hl); omega
            · obtain rfl := List.mem_singleton.mp hl; exact le_refl _
        · rw [fl, fpa, List.length_append, List.length_singleton]
          have := fresh.room
          push_cast
          omega
      have o := blockP_halts hret ws (zs ++ [x]) rest h env₁ m₁ ls (ps ++ [nl]) inv₁ penv₁ hls hps₁ good
        fresh₁ k hk falls
      have out : m₁.stdout = m.stdout := by
        rw [fo]; exact PtrStmt.focus_stdout ann m
      rw [out] at o
      exact Shows.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans bind)) o
    next => cases h
  next =>
    split at h
    next nodup =>
      cases hr : run file ret ws (ws ++ zs) zs fall (fun _ => none) ds sz budget e [] with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨T', n'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        have hlk : Keys (ls ++ ps) (ws ++ zs) := by
          simp only [Keys, List.map_append] at hls hps ⊢
          rw [hls, hps]
        have hzl : ∀ l ∈ ls, isLocal zs l.sym = false := by
          intro l hl
          have hw : l.sym.key ∈ ws.map (·.key) := by rw [← hls]; exact List.mem_map_of_mem hl
          rw [List.map_append] at nodup
          have disj := (List.nodup_append.mp nodup).2.2
          simp only [isLocal, List.any_eq_false, beq_iff_eq]
          intro y hy e
          exact disj _ hw _ (List.mem_map_of_mem hy) e.symm
        have hzp : ∀ l ∈ ps, isLocal zs l.sym = true := by
          intro l hl
          have hz : l.sym.key ∈ zs.map (·.key) := by rw [← hps]; exact List.mem_map_of_mem hl
          obtain ⟨y, hy, hyk⟩ := List.mem_map.mp hz
          exact List.any_eq_true.mpr ⟨y, hy, by simp [hyk]⟩
        exact run_halts (fall := fall) hret nodup hls hlk hps
          (fun l hl => (List.mem_append.mp hl).elim (fun h => .inr ⟨hzl l h, h⟩) (fun h => .inl ⟨hzp l h, h⟩))
          (fun _ => none) ds sz budget e [] hr env m inv penv k (.base hk falls)
    next => cases h
termination_by sizeOf e

/-- The block after the globals `gs` (definitions `ds`, sizes `sz`): the creations of its locals,
then its statements. -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) (gs : List Sym) (fall : Bool)
    (ds : Key → Option IntExpr.Term) (sz : Key → Nat) : List Sym → Eff → Option IntExpr.Term
  | xs, .mk an (.sseq (.mk pn (.base (some x, ty))) cr rest) =>
    if WrapObj.createAny file cr = true ∧ isFresh (gs ++ xs) x = true ∧ (gs ++ xs).length < 1024 then
      block file ret gs fall ds sz (xs ++ [x]) rest
    else if gs.isEmpty = true ∧ PtrStmt.createPtrOf cr = true then
      blockP file ret fall ds sz xs [] (.mk an (.sseq (.mk pn (.base (some x, ty))) cr rest))
    else none
  | xs, e =>
    if (xs.map (·.key)).Nodup then (run file ret (gs ++ xs) xs [] fall (fun _ => none) ds sz budget e []).map (·.1)
    else none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- **The block**: creating its locals after the globals keeps `Fresh` and `Inv`, then its
statements show. -/
theorem block_halts {ret : Sym} (hret : ReturnLabel labels ret) {gs : List Sym} {fall : Bool}
    {ds : Key → Option IntExpr.Term} {sz : Key → Nat} (xs : List Sym) (e : Eff)
    {T : IntExpr.Term} (h : block file ret gs fall ds sz xs e = some T) (env : Env)
    (m : Mem.Concrete.State) (ls lk : List Local) (inv : Inv env m ls ds) (hls : Keys ls (gs ++ xs))
    (hlk : Keys lk xs) (sub : ∀ l ∈ lk, l ∈ ls) (fresh : Fresh m ls)
    (good : gs = [] → ∀ l ∈ ls, 0 < l.addr ∧ l.addr < 18446744073709551616 ∧ l.addr % 4 = 0)
    (k : List Frame)
    (hk : NoBoundary k) (falls : fall = true → Falls (file := file) (labels := labels) k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 T m.stdout := by
  have hlen : ls.length = (gs ++ xs).length := by
    have := congrArg List.length hls; simpa using this
  unfold block at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      have hnext : nextIntAddress m = m.lastAddress - 4 := fresh.nextIntAddress
      have hpos : 0 < nextIntAddress m := by
        rw [hnext, fresh.last, hlen]
        simp only [StartupReach.errnoAddr]
        omega
      let REST := rest
      let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      obtain ⟨ann, m₁, hC, create⟩ := WrapObj.createAny_reaches (file := file) (labels := labels) hcr
        env K m hpos
      rw [State.focus_nextId] at create
      let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
      let env₁ := extendEnv [(x, ptr nl)] env
      have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
      have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
      have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
      have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
      have inv₁ : Inv env₁ m₁ (ls ++ [nl]) ds := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro l hl y hy
          rcases List.mem_append.mp hl with hl | hl
          · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
            exact inv.env l hl y hy
          · obtain rfl := List.mem_singleton.mp hl
            exact ConvInt.lookup_one hy
        · intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · refine hC.live (Locals.liveInt_focus ann (inv.live l hl)) ?_
            rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)
          · obtain rfl := List.mem_singleton.mp hl
            have := hC.fresh (by rw [State.focus_dead, fresh.dead, State.focus_nextId]; simp)
            rwa [Locals.nextIntAddress_focus, State.focus_nextId] at this
        · intro a ha b hb ne
          rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
          · exact inv.apart a ha b hb ne
          · obtain rfl := List.mem_singleton.mp hb
            refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
            have := addrs a ha
            show a.addr + 4 ≤ nextIntAddress m ∨ nextIntAddress m + 4 ≤ a.addr
            omega
          · obtain rfl := List.mem_singleton.mp ha
            refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
            have := addrs b hb
            show nextIntAddress m + 4 ≤ b.addr ∨ b.addr + 4 ≤ nextIntAddress m
            omega
          · obtain rfl := List.mem_singleton.mp ha
            obtain rfl := List.mem_singleton.mp hb
            exact absurd rfl ne
        · intro q d hd
          obtain ⟨ok, l, hl, hk, slot⟩ := inv.defs q d hd
          refine ⟨ok, l, List.mem_append_left _ hl, hk, ?_⟩
          have held : Globals.Held m l.id l.addr (d.val 0) := ⟨slot, ids l hl, addrs l hl⟩
          exact (hC.held (Globals.held_focus ann held)).slot
      have hls₁ : Keys (ls ++ [nl]) (gs ++ (xs ++ [x])) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
        rw [hls, List.append_assoc]
      have hlk₁ : Keys (lk ++ [nl]) (xs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hlk ⊢
        rw [hlk]
      have sub₁ : ∀ l ∈ lk ++ [nl], l ∈ ls ++ [nl] := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact List.mem_append_left _ (sub l hl)
        · exact List.mem_append_right _ hl
      have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
        rw [hC.last, Locals.nextIntAddress_focus, hnext]
      have fresh₁ : Fresh m₁ (ls ++ [nl]) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hC.dead, State.focus_dead, fresh.dead]
        · intro l hl
          rw [hC.next, State.focus_nextId]
          rcases List.mem_append.mp hl with hl | hl
          · have := ids l hl; omega
          · obtain rfl := List.mem_singleton.mp hl
            show m.nextId < m.nextId + 1
            omega
        · intro l hl
          rw [last₁]
          rcases List.mem_append.mp hl with hl | hl
          · have := addrs l hl; omega
          · obtain rfl := List.mem_singleton.mp hl
            show m.lastAddress - 4 ≤ nextIntAddress m
            omega
        · rw [last₁, fresh.last, List.length_append, List.length_singleton]
          push_cast
          ring
      have good₁ : gs = [] → ∀ l ∈ ls ++ [nl], 0 < l.addr ∧ l.addr < 18446744073709551616 ∧
          l.addr % 4 = 0 := by
        intro hg l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact good hg l hl
        · obtain rfl := List.mem_singleton.mp hl
          have hl4 := fresh.last
          simp only [StartupReach.errnoAddr] at hl4
          refine ⟨hpos, ?_, ?_⟩
          · show nextIntAddress m < 18446744073709551616
            have : (ls.length : Int) ≥ 0 := by omega
            omega
          · show nextIntAddress m % 4 = 0
            unfold Mem.Concrete.nextIntAddress
            omega
      have o := block_halts hret (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) (lk ++ [nl]) inv₁ hls₁ hlk₁
        sub₁ fresh₁ good₁ k hk falls
      have out : m₁.stdout = m.stdout := by
        rw [hC.stdout]
        obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
        rw [hl]
      rw [out] at o
      exact Shows.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans bind)) o
    next =>
      split at h
      next hc2 =>
        obtain ⟨hg, -⟩ := hc2
        have hgs : gs = [] := List.isEmpty_iff.mp hg
        have hls0 : Keys ls xs := by simpa [hgs] using hls
        have hlen0 : ls.length = xs.length := by simpa [hgs] using hlen
        refine blockP_halts hret xs [] _ h env m ls [] inv (fun _ h => by cases h) hls0 rfl (good hgs)
          ⟨fresh.dead, by simpa using fresh.ids, by simpa using fresh.addrs, ?_⟩ k hk falls
        rw [fresh.last]
        simp only [List.length_nil, Nat.cast_zero, add_zero]
        omega
      next => cases h
  next =>
    split at h
    next nodup =>
      cases hr : run file ret (gs ++ xs) xs [] fall (fun _ => none) ds sz budget e [] with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨T', n'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact run_halts (fall := fall) hret nodup hls hlk (ps := []) (zs := []) rfl
          (fun l hl => .inr ⟨rfl, sub l hl⟩)
          (fun _ => none) ds sz budget e [] hr env m inv (fun _ h => by cases h) k (.base hk falls)
    next => cases h
termination_by sizeOf e

/-- The body of `main` over the globals `gs`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (gs : List (Sym × Int)) :
    Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, (_, p))] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then
        block file ret (gs.map (·.1)) (zeroDefault p) (GlobalsState.defs gs) (fun _ => 1) [] a
      else none
  | _ => none

/-- The globals are `int`s initialised by literals, with distinct symbols, and `main` is a block
of `int` statements over them and its locals. -/
def recognize (doc : Codec.Document) : Option IntExpr.Term := do
  let ds := Globals.definitions doc.file
  let gs ← Globals.inits doc.file ds
  if (ds.map fun d => d.1.key).Nodup ∧ ds.length < 1024 then do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file gs body
  else none

/-! ## Core side -/

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (t : IntExpr.Term) (h : recognize doc = some t)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s 0 t "" := by
  unfold recognize at h
  cases hgs : Globals.inits doc.file (Globals.definitions doc.file) with
  | none => simp [hgs] at h
  | some gs =>
    simp only [hgs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i cond
      obtain ⟨nd, room⟩ := cond
      cases main : doc.file.main with
      | none => simp [main] at h
      | some sym =>
        cases decl : doc.file.funs.lookup sym with
        | none => simp [main, decl] at h
        | some entry =>
          cases entry <;> try { simp [main, decl] at h }
          case procedure loc marker ty ps body =>
            cases ps with
            | cons p ps => simp [main, decl] at h
            | nil =>
              have hbody : recognizeBody doc.file gs body = some t := by simpa [main, decl] using h
              obtain ⟨s, m, env, xs, lg, hinit, hout, hkeys, inv, fresh, hentry⟩ :=
                GlobalsState.initial_reaches_state doc.file enums args hgs nd (by omega) main decl
              obtain ⟨labels, hlabels⟩ : ∃ labels : Labels, labels = Map.ofList (saves body).reverse :=
                ⟨_, rfl⟩
              rw [← hlabels] at hinit hentry
              unfold recognizeBody at hbody
              split at hbody
              · rename_i ann pann bt0 a sann ret bt r info p0 bann pann' r'
                split at hbody
                · rename_i cond
                  obtain ⟨hr, hfree⟩ := cond
                  have hret : ReturnLabel labels ret := by
                    rw [hlabels]
                    refine ⟨r, bann, pann', r', hr, ?_⟩
                    simp [saves, StmtIf.labelFree_saves a hfree, Map.ofList]
                  let SAVE : EE :=
                    .mk sann (.save (ret, bt) [(r, (info, p0))] (.mk bann (.pure (.mk pann' () (.sym r')))))
                  have hls : Keys lg (gs.map (·.1) ++ []) := by
                    rw [List.append_nil]
                    unfold Keys
                    have := congrArg (List.map Sym.key) hkeys
                    simp only [List.map_map] at this
                    rw [List.map_map]
                    exact this
                  have o := block_halts hret [] a hbody env m lg [] inv hls rfl (by simp) fresh
                    (fun hg l hl => by
                      have hm := List.mem_map_of_mem (f := (·.sym)) hl
                      rw [hkeys, hg] at hm
                      simp at hm)
                    [.strongBind (.mk pann (.base (none, bt0))) SAVE env, .annotations xs]
                    (by simp [NoBoundary, hasBoundary]) (fun hz => main_falls hr hz env xs)
                  rw [hout] at o
                  exact ⟨s, _, hinit, LocalExpr.Shows.pre
                    (hentry.trans (ReturnConst.sequence_reaches doc.file _ ann _ a SAVE env _ m)) o⟩
                · cases hbody
              · cases hbody
    · cases h

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with
`t.val 0 mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (t : IntExpr.Term) (h : recognize doc = some t)
    (args : List String) :
    Spec.CoreUB doc args ∨ t.Ok 0 ∧ Spec.CoreBeh doc args (.exit (t.val 0 % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc t h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (t.val 0 % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.StateGlobals
