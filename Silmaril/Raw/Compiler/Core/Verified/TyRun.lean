module

public import Silmaril.Compiler.Core.Verified.TyState.Defs
public import Silmaril.Compiler.Core.Verified.StateGlobals.Defs
public import Silmaril.Compiler.Core.Verified.TyGlobals.Defs
public import Silmaril.Compiler.Core.Verified.StateExitResult.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # `main` as a statement machine over typed integer globals and locals

`TyState` with the statement machine of `StateGlobals.run`: globals of every supported integer
type (`TyActions.supported`) initialised by constant expressions (`TyGlobals`), and locals of those
types created at the start of `main`'s block; the slots are the globals then the locals, and a
`return` kills only the locals (`retStmt`). The statements run over a stack
of pending statements (`run`, `Pending`). A sequence `s; rest` (declaration groups, nested blocks
without locals) runs `s` with `rest` pending, `pure(unit)` goes on with the next pending
statement, an expression statement `e;` (`exprStmt`) evaluates `e` and drops it, and
`if (c) A else B` (`ifParts`, with or without `else`, arms of any statements) runs each arm
followed by the pending statements; the two results are selected at run time (`Out.ite`). The
other statements are `TyStmt`'s: `T x;`, `T x = e;`, `x = e;`, `return e;`. The block may fall off
its end (its locals killed at their types, `killsEnd`): `main` then returns its return label's
default `0` (`StateGlobals.zeroDefault`, `StateGlobals.main_falls`).

The result is closed (`Out`); its Lir code (`Out.ops`) computes it at run time on 64-bit words
(`TyLir`). A statement budget and size bounds keep the copies of the pending statements in check.

`recognize_sound`: Core reaches undefined behaviour or exits with `R.val mod 256` and no output,
for every argument list.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyRun

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open Mem.Concrete (LiveSz nextAddress)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open TyActions (supported width)
open TyExpr (Key Term term zero values close)
open TyMem (Local Inv Fresh Defined defsOf update ptr)
open TyStmt (Vars isLocal isFresh typedIn assignStmt initStmt uninitStmt Keys Shows convT)
open TyState (Stmt closeSize maxSize createTy)
open StateStmt (Overflows fails_overflows bound_pop boolSource_touched seqFocus_touched
  pure_unit_reaches)
open StateGlobals (Falls seqParts seqParts_inv seqParts_size isUnit isUnit_inv budget)
open IntExpr (spec)
open LoadTask (Touched)

/-! ## Results -/

/-- A closed result: a returned term, `abort()`, or the run-time selection `ite c a b` (`b` when
`c = 1`, `a` otherwise). -/
inductive Out where
  | ret (t : Term)
  | abort
  | ite (c : Term) (a b : Out)

/-- The returned value (`0` for `abort()`). -/
def Out.val : Out → Int
  | .ret t => t.val zero
  | .abort => 0
  | .ite c a b => if c.val zero = 1 then b.val else a.val

/-- The termination flag: `1` for a return (or `exit`), `0` for `abort()`. -/
def Out.test : Out → Out
  | .ret _ => .ret (.lit 1)
  | .abort => .ret (.lit 0)
  | .ite c a b => .ite c a.test b.test

/-- How the program ends: with the returned value when the flag is `1`, by `abort()` otherwise. -/
def Out.outcome (R : Out) : Outcome :=
  if R.test.val = 1 then .defined (spec R.val) else .aborted

/-- The guards are those of the recogniser and the tests are comparisons (checked). -/
def Out.wf : Out → Bool
  | .ret t => TyState.Term.wf t
  | .abort => true
  | .ite c a b => TyState.Term.wf c && TyState.Term.bool01 c && Out.wf a && Out.wf b

/-- The number of nodes. -/
def Out.size : Out → Nat
  | .ret t => closeSize (fun _ => 1) t
  | .abort => 1
  | .ite c a b => 1 + closeSize (fun _ => 1) c + Out.size a + Out.size b

theorem Out.wf_test : (R : Out) → Out.wf R = true → Out.wf R.test = true
  | .ret _, _ => rfl
  | .abort, _ => rfl
  | .ite c a b, h => by
    simp only [Out.wf, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hb⟩, ha⟩, hr⟩ := h
    simp [Out.test, Out.wf, hc, hb, Out.wf_test a ha, Out.wf_test b hr]

theorem Out.test_val : (R : Out) → R.test.val = 0 ∨ R.test.val = 1
  | .ret _ => by simp [Out.test, Out.val, Term.val]
  | .abort => by simp [Out.test, Out.val, Term.val]
  | .ite c a b => by
    by_cases h : c.val zero = 1 <;> simp [Out.test, Out.val, h, Out.test_val a, Out.test_val b]

theorem Out.outcome_ret (t : Term) : (Out.ret t).outcome = .defined (spec (t.val zero)) := by
  simp [Out.outcome, Out.test, Out.val, Term.val]

theorem Out.outcome_abort : Out.abort.outcome = .aborted := by
  simp [Out.outcome, Out.test, Out.val, Term.val]

theorem Out.outcome_ite_right {c : Term} {a b : Out} (h : c.val zero = 1) :
    (Out.ite c a b).outcome = b.outcome := by
  simp [Out.outcome, Out.test, Out.val, h]

theorem Out.outcome_ite_left {c : Term} {a b : Out} (h : c.val zero ≠ 1) :
    (Out.ite c a b).outcome = a.outcome := by
  simp [Out.outcome, Out.test, Out.val, h]

/-- The code of `R` into register `d`, the temporaries above. -/
def Out.ops (d : Mir.Reg) : Out → List (Lir.Op Mir.Reg)
  | .ret t => t.ops d
  | .abort => [.const d (BitVec.ofInt 64 0)]
  | .ite c a b => c.ops d ++ Out.ops (d + 1) a ++ Out.ops (d + 2) b ++
      [.const (d + 3) (BitVec.ofInt 64 1), .binary (.cmp .eq) d d (d + 3),
        .binary .sub (d + 2) (d + 2) (d + 1), .binary .mul d d (d + 2), .binary .add d d (d + 1)]

theorem Out.ops_exec : (R : Out) → Out.wf R = true → (d : Nat) → (fr : Lir.Frame Mir.Reg) →
    (mem : Lir.Memory) → ∃ fr', Lir.execOps (R.ops d) fr mem = some (fr', mem) ∧
      fr'.get d = some (BitVec.ofInt 64 R.val) ∧ ∀ r : Nat, r < d → fr'.get r = fr.get r
  | .ret t, h, d, fr, mem => TyLir.ops_exec t (TyState.Term.wf_spec t h) d fr mem
  | .abort, _, d, fr, mem => by
    exact ⟨fr.set d (BitVec.ofInt 64 0), by simp [Out.ops, Lir.execOps, Lir.Op.exec], by simp [Out.val],
      fun r hr => IntExpr.get_below hr _⟩
  | .ite c a b, h, d, fr, mem => by
    simp only [Out.wf, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hb⟩, ha⟩, hr⟩ := h
    obtain ⟨fr₁, x₁, g₁, p₁⟩ := TyLir.ops_exec c (TyState.Term.wf_spec c hc) d fr mem
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := Out.ops_exec a ha (d + 1) fr₁ mem
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := Out.ops_exec b hr (d + 2) fr₂ mem
    have gc : fr₃.get d = some (BitVec.ofInt 64 (c.val zero)) := by
      rw [p₃ d (by omega), p₂ d (by omega)]; exact g₁
    have ga : fr₃.get (d + 1) = some (BitVec.ofInt 64 a.val) := by
      rw [p₃ (d + 1) (by omega)]; exact g₂
    let f := Lir.ofBool (BitVec.ofInt 64 (c.val zero) == BitVec.ofInt 64 1)
    let wa := BitVec.ofInt 64 a.val
    let wr := BitVec.ofInt 64 b.val
    refine ⟨(((((fr₃.set (d + 3) (BitVec.ofInt 64 1)).set d f).set (d + 2) (wr - wa)).set d
      (f * (wr - wa))).set d (f * (wr - wa) + wa)), ?_, ?_, fun x hx => ?_⟩
    · simp only [Out.ops, Lir.execOps_append, x₁, Option.bind_some, x₂, x₃]
      simp [Lir.execOps, Lir.Op.exec, gc, ga, g₃, Lir.Binop.eval, Lir.Cond.eval, f, wa, wr]
    · simp only [Lir.Frame.get_set, ↓reduceIte, f, IntExpr.select_cond, TyState.ofInt_eq_one
        (TyState.Term.bool01_val hb zero), Out.val]
      by_cases h1 : c.val zero = 1 <;> simp [h1, wa, wr]
    · rw [IntExpr.get_below hx, IntExpr.get_below hx, IntExpr.get_below (show x < d + 2 by omega),
        IntExpr.get_below hx, IntExpr.get_below (show x < d + 3 by omega), p₃ x (by omega),
        p₂ x (by omega), p₁ x hx]

variable {file : Program} {labels : Labels}

/-- What a run from a statement shows: the outcome of `R` (its value returned, or `abort()`), or
undefined behaviour. -/
def Ends (s : State) (R : Out) (stdout : String) : Prop :=
  (∃ m', m'.stdout = stdout ∧ Reaches file labels s ⟨.halt R.outcome, [], m'⟩) ∨
  ∃ s', Reaches file labels s s' ∧ s'.control = .halt IntExpr.overflow

theorem Ends.pre {s s' : State} {R : Out} {out : String}
    (h : Reaches file labels s s') (o : Ends (file := file) (labels := labels) s' R out) :
    Ends (file := file) (labels := labels) s R out := by
  rcases o with ⟨m', hout, r⟩ | ⟨s'', r, hs⟩
  · exact .inl ⟨m', hout, h.trans r⟩
  · exact .inr ⟨s'', h.trans r, hs⟩

theorem Ends.of_ret {s : State} {t : Term} {out : String}
    (o : Shows (file := file) (labels := labels) s (t.val zero) out) :
    Ends (file := file) (labels := labels) s (.ret t) out := by
  rw [Ends, Out.outcome_ret]
  exact o

theorem ends_ite_left {s : State} {C : Term} {A B : Out} {out : String}
    (h1 : C.val zero ≠ 1) (o : Ends (file := file) (labels := labels) s A out) :
    Ends (file := file) (labels := labels) s (Out.ite C A B) out := by
  rw [Ends, Out.outcome_ite_left h1]
  exact o

theorem ends_ite_right {s : State} {C : Term} {A B : Out} {out : String}
    (h1 : C.val zero = 1) (o : Ends (file := file) (labels := labels) s B out) :
    Ends (file := file) (labels := labels) s (Out.ite C A B) out := by
  rw [Ends, Out.outcome_ite_right h1]
  exact o

/-! ## `if` statements and expression statements -/

/-- `if (c) A else B` (no `else`: `B` is `pure(unit)`), as `StateGlobals.ifParts` over typed
locals: the test's term and the two arms. -/
def ifParts (file : File Codec.wireModel Unit Unit) (xs : Vars) : Eff → Option (Term × Eff × Eff)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb (.mk _ (.if_ (.mk _ () (.sym b')) ea eb))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧ isFresh xs b = true then
        (term file ec).map fun tc => (tc, ea, eb)
      else none
  | _ => none

theorem ifParts_inv {f : File Codec.wireModel Unit Unit} {xs : Vars} {e ea eb : Eff} {tc : Term}
    (h : ifParts f xs e = some (tc, ea, eb)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : Eff) (a3 a4 : List Annot)
      (b : Sym) (bty : BaseType) (cb : Eff) (a5 a6 : List Annot) (b' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb (.mk a5 (.if_ (.mk a6 () (.sym b')) ea eb))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧ isFresh xs b = true ∧
      term f ec = some tc := by
  unfold ifParts at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨tc', htc, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, htc⟩
    · cases h
  · cases h

theorem ifParts_size {f : File Codec.wireModel Unit Unit} {xs : Vars} {e ea eb : Eff} {tc : Term}
    (h : ifParts f xs e = some (tc, ea, eb)) : sizeOf ea < sizeOf e ∧ sizeOf eb < sizeOf e := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, -⟩ := ifParts_inv h
  constructor <;> simp <;> omega

/-- **An `if` statement** reaches undefined behaviour in its test, or one of its arms with the
locals unchanged: `B` when the test is `1`, `A` otherwise. -/
theorem if_runs {xs : Vars} {e ea eb : Eff} {tc : Term} (h : ifParts file xs e = some (tc, ea, eb))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) (hls : Keys ls xs) (hdc : Defined ds tc = true)
    (htc : typedIn xs tc = true) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    ∃ env' m', m'.stdout = m.stdout ∧ TyStmt.SameAlloc m m' ∧ Inv env' m' ls ds ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr (if tc.val (values (defsOf ds)) = 1 then eb else ea) env', k, m'⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, hb', hcb, hfc, hfb, htc'⟩ :=
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
  have locs := inv.locs hdc (hls.typed htc)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := TyExpr.term_runs (file := file) (labels := labels)
      tc htc' okc (.bound :: K) m locs
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
    have inv₂ : Inv env₂ m₃ ls ds := ((inv.touched tch₃).extend (hls.fresh hfc)).extend (hls.fresh hfb)
    refine ⟨env₂, m₃, tch₃.stdout, TyStmt.sameAlloc_touched tch₃, inv₂, pre.trans ?_⟩
    have hsel : (if flag then ea else eb) = (if tc.val σ = 1 then eb else ea) := by
      by_cases h1 : tc.val σ = 1 <;> simp [flag, cv, h1]
    rw [← hsel]
    exact enter
  · left
    exact StateStmt.Overflows.pre pre (fails_overflows (TyExpr.term_fails (file := file)
      (labels := labels) tc htc' okc (.bound :: K) m locs))

/-- `e;`, an expression statement whose value is discarded: `bound(e)`. -/
def exprStmt (file : File Codec.wireModel Unit Unit) : Eff → Option Term
  | .mk _ (.bound e) => term file e
  | _ => none

/-- **An expression statement** reaches undefined behaviour or a value, with the locals
unchanged. -/
theorem expr_runs {e : Eff} {t : Term} (h : exprStmt file e = some t) {xs : Vars} {env : Env}
    {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term} (inv : Inv env m ls ds)
    (hls : Keys ls xs) (hd : Defined ds t = true) (ht : typedIn xs t = true) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    ∃ v m', m'.stdout = m.stdout ∧ TyStmt.SameAlloc m m' ∧ Inv env m' ls ds ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value v, k, m'⟩ := by
  unfold exprStmt at h
  split at h
  · rename_i ann e'
    have pre := ReturnLit.bound_reaches (file := file) (labels := labels) ann e' env k m
    have locs := inv.locs hd (hls.typed ht)
    by_cases ok : t.Ok (values (defsOf ds))
    · right
      obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := TyExpr.term_runs (file := file) (labels := labels)
        t h ok (.bound :: k) m locs
      exact ⟨_, m₁, tch.stdout, TyStmt.sameAlloc_touched tch, inv.touched tch,
        pre.trans ((Interleave.reaches_of_local file labels run).trans (bound_pop hfr _ k m₁))⟩
    · left
      exact StateStmt.Overflows.pre pre (fails_overflows (TyExpr.term_fails (file := file)
        (labels := labels) t h ok (.bound :: k) m locs))
  · cases h

/-! ## Falling off the end of `main` -/

/-- `kill(T₁, x₁); …; kill(Tₙ, xₙ); pure(unit)`: the end of a block with the locals `xs`. -/
def killsEnd : Vars → Eff → Bool
  | [], e => isUnit e
  | x :: xs, e => match e with
    | .mk _ (.sseq (.mk _ (.base (none, _))) kl rest) => TyStmt.killTy x.1 x.2 kl && killsEnd xs rest
    | _ => false

theorem killsEnd_cons {x : Sym × IntegerType} {xs : Vars} {e : Eff} (h : killsEnd (x :: xs) e = true) :
    ∃ ann pann ty kl rest, e = .mk ann (.sseq (.mk pann (.base (none, ty))) kl rest) ∧
      TyStmt.killTy x.1 x.2 kl = true ∧ killsEnd xs rest = true := by
  simp only [killsEnd] at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, rfl, h.1, h.2⟩
  · cases h

/-- **The end of a block** kills its locals and reaches `unit`, keeping stdout. -/
theorem killsEnd_reaches : (xs : Vars) → (ls : List Local) → Keys ls xs → (xs.map (·.1.key)).Nodup →
    {e : Eff} → killsEnd xs e = true → (env : Env) → (k : List Frame) → (m : Mem.Concrete.State) →
    (∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ ls, supported l.ity = true ∧ LiveSz m l.id l.addr (width l.ity)) →
    (∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩
  | [], _, _, _, e, h, env, k, m, _, _, _ => by
    obtain ⟨ann, pann, rfl⟩ := isUnit_inv (show isUnit e = true from h)
    exact ⟨_, by simp, pure_unit_reaches ann pann env k m⟩
  | x :: xs, ls, hls, nodup, e, h, env, k, m, henv, hlive, hids => by
    cases ls with
    | nil => cases hls
    | cons l ls =>
      simp only [Keys, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hls
      obtain ⟨⟨hxl, hxt⟩, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsEnd_cons h
      obtain ⟨kann, loc, uu, c1, a2, x', rfl, hx'k⟩ := TyStmt.killTy_inv hkl
      have hx' : env.lookup x' = some (ptr l) :=
        henv l (by simp) x' (hx'k.trans hxl.symm)
      obtain ⟨hsl, livel⟩ := hlive l (by simp)
      rw [← hxt]
      have kill := TyActions.kill_reaches (file := file) (labels := labels) kann a2 c1 loc uu x' hsl env
        (.strongBind (.mk pann (.base (none, ty))) rest env :: k) m hx' livel
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have hls' : Keys ls xs := hls
      have ne : ∀ l' ∈ ls, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls'.keys, e, hxl] at hm
        exact hm
      obtain ⟨m', out, reach⟩ := killsEnd_reaches xs ls hls' nodup hrest env k m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => ⟨(hlive l' (by simp [hl'])).1, TyActions.live_killed
          (TyActions.liveSz_focus kann (hlive l' (by simp [hl'])).2) l.id (ne l' hl')⟩)
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb]))
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], ?_⟩
      exact (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans (kill.trans
        ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m₁).trans reach))

/-! ## Returns over globals and locals -/

/-- `return e;` with the slots `ys` (globals, then locals: what the temporary must avoid) and the
locals `xs`, which it kills (`TyStmt.retStmt` with globals). -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : Vars) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e)) kr) =>
      if isFresh ys u = true then
        match TyStmt.killsRun file ret u xs kr, term file e with
        | some r, some t => some (convT r t)
        | _, _ => none
      else none
  | _ => none

theorem retStmt_inv {f : File Codec.wireModel Unit Unit} {ret : Sym} {ys xs : Vars} {e : Eff}
    {t : Term} (h : retStmt f ret ys xs e = some t) :
    ∃ (ann pann : List Annot) (u : Sym) (ty : BaseType) (bann : List Annot) (e' kr : Eff)
      (r : IntegerType) (te : Term),
      e = .mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr) ∧
      isFresh ys u = true ∧ TyStmt.killsRun f ret u xs kr = some r ∧ term f e' = some te ∧
      t = convT r te := by
  unfold retStmt at h
  split at h
  · split at h
    · rename_i hf
      split at h
      · rename_i r te hk he
        cases h
        exact ⟨_, _, _, _, _, _, _, _, _, rfl, hf, hk, he, rfl⟩
      · cases h
    · cases h
  · cases h

/-- **`return e;`** over globals and locals: the slots `ls` (keys `ys`), the locals `lk ⊆ ls`
(keys `xs`) killed before the return. -/
theorem ret_halts {ret : Sym} (hret : ReturnLabel labels ret) {ys xs : Vars} {e : Eff} {t : Term}
    (h : retStmt file ret ys xs e = some t) {env : Env} {m : Mem.Concrete.State}
    {ls lk : List Local} {ds : Key → Option Term} (inv : Inv env m ls ds) (hls : Keys ls ys)
    (hlk : Keys lk xs) (sub : ∀ l ∈ lk, l ∈ ls) (nodup : (xs.map (·.1.key)).Nodup)
    (hd : Defined ds t = true) (ht : typedIn ys t = true) {k : List Frame} (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩
      ((close (defsOf ds) t).val zero) m.stdout := by
  obtain ⟨ann, pann, u, ty, bann, e', kr, r, te, rfl, hfresh, hkr, he, rfl⟩ := retStmt_inv h
  have hr := TyStmt.killsRun_supported xs hkr
  let σ := values (defsOf ds)
  let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr)) env,
        k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
      (ReturnLit.bound_reaches bann _ env _ m)
  refine Shows.pre pre ?_
  have hd' : Defined ds te = true := by
    simpa [Defined, convT, Term.vars] using hd
  have ht' : typedIn ys te = true := by
    simpa [typedIn, convT, Term.vars] using ht
  have locs := inv.locs hd' (hls.typed ht')
  by_cases ok : te.Ok σ
  · left
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := TyExpr.term_runs (file := file) (labels := labels)
      te he ok (.bound :: K) m locs
    let v := spec (te.val σ)
    have inv₁ := (inv.touched tch).extend (x := u) (v := v) (hls.fresh hfresh)
    obtain ⟨m', out, reach⟩ := TyStmt.killsRun_halts hret xs lk hlk nodup hkr (extendEnv [(u, v)] env)
      hk m₁ (fun l hl => inv₁.env l (sub l hl)) (fun l hl => inv₁.live l (sub l hl))
      (fun a ha b hb ne => (inv₁.apart a (sub a ha) b (sub b hb) ne).1) (ConvInt.lookup_one rfl)
    refine ⟨m', by rw [out, tch.stdout], ?_⟩
    rw [TyStmt.close_convT, TyStmt.convT_val hr, TyExpr.close_val]
    exact (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr v K m₁).trans
      ((ReturnLit.bind_reaches pann u ty v kr env k m₁).trans reach))
  · right
    exact fails_overflows (TyExpr.term_fails (file := file) (labels := labels) te he ok
      (.bound :: K) m locs)

/-! ## The pending statements -/

/-- `env` maps the locals' symbols to their pointers (the environment part of `Inv`). -/
def EnvOk (env : Env) (ls : List Local) : Prop :=
  ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)

theorem inv_withEnv {env env' : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option Term} (inv : Inv env m ls ds) (h : EnvOk env' ls) : Inv env' m ls ds :=
  ⟨h, inv.live, inv.uniq, inv.apart, inv.defs⟩

/-- `StateGlobals.Pending` over typed locals: the frames `k` hold the pending statements `todo`,
each a wildcard strong sequence over an environment of the locals, among access annotation
frames, above a continuation without boundary from which, when `fall`, the end of the block
returns `0`. -/
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

/-- The allocation budget of a later `exit` argument survives the statements. -/
theorem budget_same {m m' : Mem.Concrete.State} (b : ExitCall.Budget m) (h : TyStmt.SameAlloc m m') :
    ExitCall.Budget m' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_⟩
  · unfold Mem.Concrete.nextIntAddress
    rw [h1]
    exact b.room
  · rw [h2, h3]
    exact b.fresh

/-- The memory after the creation of at most `1024` slots leaves room for an `exit` argument. -/
theorem budget_of_fresh {m : Mem.Concrete.State} {ls : List Local} (fresh : Fresh m ls)
    (h : ls.length ≤ 1024) : ExitCall.Budget m := by
  refine ⟨?_, by rw [fresh.dead]; simp⟩
  have hl := fresh.last
  have he := TyState.errno_large
  have : (ls.length : Int) ≤ 1024 := by exact_mod_cast h
  unfold Mem.Concrete.nextIntAddress
  omega

/-! ## The machine -/

/-- Which statement `s` is (an `if` is `ifParts`). -/
def classify (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : Vars) (s : Eff) :
    Option Stmt :=
  match retStmt file ret ys xs s with
  | some t => some (.ret t)
  | none => match assignStmt file s with
    | some (x, ity, t) => some (.assign x ity t)
    | none => match initStmt file s with
      | some (x, ity, t) => some (.init x ity t)
      | none => (uninitStmt s).map fun (x, ity) => .uninit x ity

/-- What the classification of `s` says about `s`. -/
def Shape (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : Vars) (s : Eff) : Stmt → Prop
  | .ret t => retStmt file ret ys xs s = some t
  | .ifRet _ _ => False
  | .assign x ity t => assignStmt file s = some (x, ity, t)
  | .init x ity t => initStmt file s = some (x, ity, t)
  | .uninit x ity => uninitStmt s = some (x, ity)

theorem classify_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {ys xs : Vars} {s : Eff}
    {st : Stmt} (h : classify file ret ys xs s = some st) : Shape file ret ys xs s st := by
  unfold classify at h
  split at h
  next t ht => cases h; exact ht
  next =>
    split at h
    next x ity t hx => cases h; exact hx
    next =>
      split at h
      next x ity t hx => cases h; exact hx
      next =>
        cases hu : uninitStmt s with
        | none => simp [hu] at h
        | some p =>
          obtain ⟨x, ity⟩ := p
          simp only [hu, Option.map_some, Option.some.injEq] at h
          subst h
          exact hu

/-- A term the statements may use: defined, read at the locals' types, not too large. -/
def usable (xs : Vars) (ds : Key → Option Term) (sz : Key → Nat) (t : Term) : Bool :=
  Defined ds t && typedIn xs t && decide (closeSize sz t ≤ maxSize)

theorem usable_spec {xs : Vars} {ds : Key → Option Term} {sz : Key → Nat} {t : Term}
    (h : usable xs ds sz t = true) : Defined ds t = true ∧ typedIn xs t = true := by
  simp only [usable, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

/-- The statements of a block with the locals `xs`, the definitions `ds` (sizes `sz`): the
statement `e`, then the pending statements `todo` in order (`StateGlobals.run` over typed
locals). `n` bounds the statements visited; the result is the closed result and what is left of
`n`. -/
def run (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : Vars) (fall : Bool) :
    (Key → Option Term) → (Key → Nat) → Nat → Eff → List Eff → Option (Out × Nat)
  | _, _, 0, _, _ => none
  | ds, sz, n + 1, e, todo =>
    if AbortCall.abortStmt file e = true then some (.abort, n) else
    match ExitCall.recognizeBody file e with
    | some v => some (.ret (.lit v), n)
    | none =>
    match _hi : ifParts file ys e with
    | some (tc, ea, eb) =>
      if usable ys ds sz tc = true then
        match run file ret ys xs fall ds sz n ea todo with
        | some (ta, n₁) =>
          match run file ret ys xs fall ds sz n₁ eb todo with
          | some (tb, n₂) =>
            if (Out.ite (close (defsOf ds) tc) ta tb).size ≤ maxSize then
              some (Out.ite (close (defsOf ds) tc) ta tb, n₂)
            else none
          | none => none
        | none => none
      else none
    | none =>
      match classify file ret ys xs e with
      | some (.ret t) =>
        if usable ys ds sz t = true then some (.ret (close (defsOf ds) t), n) else none
      | some (.assign x ity t) =>
        if isLocal ys x ity = true ∧ usable ys ds sz t = true then
          match todo with
          | [] => none
          | r :: todo =>
            run file ret ys xs fall (update ds x.key (some (close (defsOf ds) (convT ity t))))
              (fun q => if q = x.key then closeSize sz t + 2 else sz q) n r todo
        else none
      | some (.init x ity t) =>
        if isLocal ys x ity = true ∧ usable ys ds sz t = true then
          match todo with
          | [] => none
          | r :: todo =>
            run file ret ys xs fall (update ds x.key (some (close (defsOf ds) (convT ity t))))
              (fun q => if q = x.key then closeSize sz t + 2 else sz q) n r todo
        else none
      | some (.uninit x ity) =>
        if isLocal ys x ity = true then
          match todo with
          | [] => none
          | r :: todo => run file ret ys xs fall (update ds x.key none) sz n r todo
        else none
      | _ =>
        match exprStmt file e with
        | some t =>
          if usable ys ds sz t = true then
            match todo with
            | [] => none
            | r :: todo => run file ret ys xs fall ds sz n r todo
          else none
        | none =>
          match _hs : seqParts e with
          | some (s, rest) =>
            if fall = true ∧ todo.isEmpty = true ∧ killsEnd xs e = true then some (.ret (.lit 0), n)
            else run file ret ys xs fall ds sz n s (rest :: todo)
          | none =>
            if isUnit e = true then
              match todo with
              | [] => if fall = true ∧ xs.isEmpty = true then some (.ret (.lit 0), n) else none
              | r :: todo => run file ret ys xs fall ds sz n r todo
            else none
termination_by _ _ _ e todo => sizeOf e + (todo.map sizeOf).sum
decreasing_by
  all_goals first
    | (have := (ifParts_size _hi).1; omega)
    | (have := (ifParts_size _hi).2; omega)
    | (have := seqParts_size _hs; simp; omega)
    | (cases e; simp)

theorem lit_zero_val : (Out.ret (.lit 0)).val = 0 := by simp [Out.val, Term.val]

/-- `run_halts` for a statement and pending statements of size below `N`. -/
theorem run_halts_lt {ret : Sym} (hret : ReturnLabel labels ret) {ys xs : Vars} {fall : Bool}
    (nodup : (xs.map (·.1.key)).Nodup) {ls lk : List Local} (hls : Keys ls ys) (hlk : Keys lk xs)
    (sub : ∀ l ∈ lk, l ∈ ls) (N : Nat) :
    ∀ (ds : Key → Option Term) (sz : Key → Nat) (n : Nat) (e : Eff) (todo : List Eff)
      {R : Out} {n' : Nat}, sizeOf e + (todo.map sizeOf).sum < N →
      run file ret ys xs fall ds sz n e todo = some (R, n') → ∀ (env : Env) (m : Mem.Concrete.State),
      Inv env m ls ds → ExitCall.Budget m → ∀ (k : List Frame),
      Pending (file := file) (labels := labels) ls fall todo k →
      Ends (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ R m.stdout := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ hN; omega
  | succ N ih =>
  intro ds sz n e todo R n' hN h env m inv hb k p
  have he1 : 0 < sizeOf e := by cases e; simp
  unfold run at h
  split at h
  next => cases h
  next n =>
    split at h
    · cases h
      obtain ⟨m', reach, out⟩ := AbortCall.abortStmt_reaches (labels := labels) (by assumption) env k m
      exact .inl ⟨m', out, by rw [Out.outcome_abort]; exact reach⟩
    split at h
    · rename_i v hv
      cases h
      obtain ⟨m', reach, out⟩ := StateExit.exit_reaches (labels := labels) e hv env k m hb
      exact Ends.of_ret (.inl ⟨m', out, reach⟩)
    split at h
    next tc ea eb hi =>
      split at h
      next hd =>
        obtain ⟨hdc, htc⟩ := usable_spec hd
        split at h
        next ta n₁ hA =>
          split at h
          next tb n₂ hB =>
            split at h
            next =>
              cases h
              rcases if_runs hi inv hls hdc htc k with ub | ⟨env', m', out, sa, inv', reach⟩
              · exact .inr ub
              · by_cases h1 : tc.val (values (defsOf ds)) = 1
                · simp only [h1, ↓reduceIte] at reach
                  have o := ih ds sz n₁ eb todo (by have := (ifParts_size hi).2; omega) hB env' m' inv'
                    (budget_same hb sa) k p
                  rw [out] at o
                  exact ends_ite_right (by rw [TyExpr.close_val]; exact h1) (Ends.pre reach o)
                · simp only [h1, ↓reduceIte] at reach
                  have o := ih ds sz n ea todo (by have := (ifParts_size hi).1; omega) hA env' m' inv'
                    (budget_same hb sa) k p
                  rw [out] at o
                  exact ends_ite_left (by rw [TyExpr.close_val]; exact h1) (Ends.pre reach o)
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
          obtain ⟨hdt, htt⟩ := usable_spec hd
          exact Ends.of_ret (ret_halts hret (classify_spec hc) inv hls hlk sub nodup hdt htt p.noBoundary)
        next => cases h
      next x ity t hc =>
        split at h
        next hd =>
          obtain ⟨hdt, htt⟩ := usable_spec hd.2
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx, hty⟩ := hls.mem_of_local hd.1
            rw [TyState.update_key hx] at h
            rcases TyStmt.assign_runs (classify_spec hc) inv hl hx hty hdt (hls.typed htt) k with
              ub | ⟨m', out, sa, inv', reach⟩
            · exact .inr ub
            · obtain ⟨env', k', he, p', r'⟩ := p.resume .unit none m' r todo' rfl
              have o := ih _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
                (inv_withEnv inv' he) (budget_same hb sa) k' p'
              rw [out] at o
              exact Ends.pre (reach.trans r') o
        next => cases h
      next x ity t hc =>
        split at h
        next hd =>
          obtain ⟨hdt, htt⟩ := usable_spec hd.2
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx, hty⟩ := hls.mem_of_local hd.1
            rw [TyState.update_key hx] at h
            rcases TyStmt.init_runs (classify_spec hc) inv hl hx hty hdt (hls.typed htt) k with
              ub | ⟨m', ys', out, sa, inv', reach⟩
            · exact .inr ub
            · obtain ⟨env', k', he, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
              have o := ih _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
                (inv_withEnv inv' he) (budget_same hb sa) k' p'
              rw [out] at o
              exact Ends.pre (reach.trans r') o
        next => cases h
      next x ity hc =>
        split at h
        next hd =>
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx, hty⟩ := hls.mem_of_local hd
            rw [TyState.update_key hx] at h
            obtain ⟨m', ys', out, sa, inv', reach⟩ := TyStmt.uninit_runs (classify_spec hc) inv hl hx hty k
            obtain ⟨env', k', he, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
            have o := ih _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
              (inv_withEnv inv' he) (budget_same hb sa) k' p'
            rw [out] at o
            exact Ends.pre (reach.trans r') o
        next => cases h
      next =>
        split at h
        next t hx =>
          split at h
          next hd =>
            obtain ⟨hdt, htt⟩ := usable_spec hd
            split at h
            next => cases h
            next r todo' =>
              rcases expr_runs hx inv hls hdt htt k with ub | ⟨v, m', out, sa, inv', reach⟩
              · exact .inr ub
              · obtain ⟨env', k', he, p', r'⟩ := p.resume v none m' r todo' rfl
                have o := ih ds sz n r todo' (by simp at hN ⊢; omega) h env' m'
                  (inv_withEnv inv' he) (budget_same hb sa) k' p'
                rw [out] at o
                exact Ends.pre (reach.trans r') o
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
              obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) xs lk hlk
                nodup hke env k m (fun l hl => inv.env l (sub l hl)) (fun l hl => inv.live l (sub l hl))
                (fun a ha b hb ne => (inv.apart a (sub a ha) b (sub b hb) ne).1)
              obtain ⟨m'', out', fin⟩ := p.falls hf hnil' none m'
              exact Ends.of_ret (.inl ⟨m'', out'.trans out, reach.trans fin⟩)
            next =>
              exact Ends.pre (ReturnConst.sequence_reaches file labels ann _ s rest env k m)
                (ih ds sz n s (rest :: todo) (by simp at hN ⊢; omega) h env m inv hb _
                  (.bind pann ty rest inv.env p))
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
                  obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) xs lk
                    hlk nodup (e := .mk ann (.pure (.mk pann () (.val .unit)))) (by rw [hxs']; rfl)
                    env k m (fun l hl => inv.env l (sub l hl)) (fun l hl => inv.live l (sub l hl))
                    (fun a ha b hb ne => (inv.apart a (sub a ha) b (sub b hb) ne).1)
                  obtain ⟨m'', out', fin⟩ := p.falls hf rfl none m'
                  exact Ends.of_ret (.inl ⟨m'', out'.trans out, reach.trans fin⟩)
                next => cases h
              next r todo' =>
                obtain ⟨env', k', he, p', reach⟩ :=
                  p.resume .unit none (focusMemory ann m) r todo' rfl
                have o := ih ds sz n r todo' (by simp at hN ⊢; omega) h env' (focusMemory ann m)
                  (inv_withEnv (inv.focus ann) he) (hb.focus ann) k' p'
                rw [ReturnConst.focusMemory_stdout] at o
                exact Ends.pre ((pure_unit_reaches ann pann env k m).trans reach) o
            next => cases h

/-- **The statements** show the value of the closed result, or undefined behaviour. -/
theorem run_halts {ret : Sym} (hret : ReturnLabel labels ret) {ys xs : Vars} {fall : Bool}
    (nodup : (xs.map (·.1.key)).Nodup) {ls lk : List Local} (hls : Keys ls ys) (hlk : Keys lk xs)
    (sub : ∀ l ∈ lk, l ∈ ls)
    (ds : Key → Option Term) (sz : Key → Nat) (n : Nat) (e : Eff) (todo : List Eff) {R : Out}
    {n' : Nat} (h : run file ret ys xs fall ds sz n e todo = some (R, n')) (env : Env)
    (m : Mem.Concrete.State) (inv : Inv env m ls ds) (hb : ExitCall.Budget m) (k : List Frame)
    (p : Pending (file := file) (labels := labels) ls fall todo k) :
    Ends (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ R m.stdout :=
  run_halts_lt hret nodup hls hlk sub _ ds sz n e todo (Nat.lt_succ_self _) h env m inv hb k p

/-! ## The block -/

/-- The block after the globals `gs` (definitions `ds`, sizes `sz`): the creations of its
locals, then its statements. -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) (gs : Vars) (fall : Bool)
    (ds : Key → Option Term) (sz : Key → Nat) : Vars → Eff → Option Out
  | xs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    match createTy cr with
    | some ity =>
      if isFresh (gs ++ xs) x = true ∧ (gs ++ xs).length < 1024 then
        block file ret gs fall ds sz (xs ++ [(x, ity)]) rest
      else none
    | none => none
  | xs, e =>
    if (xs.map (·.1.key)).Nodup ∧ (gs ++ xs).length ≤ 1024 then
      (run file ret (gs ++ xs) xs fall ds sz budget e []).map (·.1)
    else none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- **The block**: creating its locals keeps `Fresh` and `Inv`, then its statements show. -/
theorem block_halts {ret : Sym} (hret : ReturnLabel labels ret) {gs : Vars} {fall : Bool}
    {ds : Key → Option Term} {sz : Key → Nat} (xs : Vars) (e : Eff)
    {R : Out} (h : block file ret gs fall ds sz xs e = some R) (env : Env) (m : Mem.Concrete.State)
    (ls lk : List Local) (inv : Inv env m ls ds) (hls : Keys ls (gs ++ xs)) (hlk : Keys lk xs)
    (sub : ∀ l ∈ lk, l ∈ ls) (fresh : Fresh m ls)
    (k : List Frame) (hk : NoBoundary k) (falls : fall = true → Falls (file := file) (labels := labels) k) :
    Ends (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ R m.stdout := by
  have hlen : ls.length = (gs ++ xs).length := by
    have := congrArg List.length hls; simpa using this
  unfold block at h
  split at h
  next a p x ty cr rest =>
    split at h
    next ity hcr =>
      split at h
      next hc =>
        obtain ⟨hfx, hlt⟩ := hc
        obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl, hs⟩ := TyState.createTy_inv hcr
        have hw := TyActions.width_pos hs
        have hw8 := TyActions.width_le hs
        have hge := TyActions.nextAddress_ge m hw
        have hle := TyActions.nextAddress_le m hw
        have hlast := fresh.last
        have herr := TyState.errno_large
        have hpos : 0 < nextAddress m (width ity) := by
          rw [hlen] at hlast
          have : ((gs ++ xs).length : Int) < 1024 := by exact_mod_cast hlt
          omega
        let REST := rest
        let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
        have create := TyActions.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
          pref hs env K m hpos
        let nl : Local := ⟨x, m.nextId, nextAddress m (width ity), ity⟩
        let m₁ := TyActions.created pref c2 ity (focusMemory ann m)
        let env₁ := extendEnv [(x, ptr nl)] env
        have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
        have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
        have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
        have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
        have nfocus : (focusMemory ann m).nextId = m.nextId := TyActions.focus_nextId ann m
        have afocus : nextAddress (focusMemory ann m) (width ity) = nextAddress m (width ity) :=
          TyActions.nextAddress_focus ann m _
        have inv₁ : Inv env₁ m₁ (ls ++ [nl]) ds := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro l hl y hy
            rcases List.mem_append.mp hl with hl | hl
            · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
              exact inv.env l hl y hy
            · obtain rfl := List.mem_singleton.mp hl
              exact ConvInt.lookup_one hy
          · intro l hl
            rcases List.mem_append.mp hl with hl | hl
            · refine ⟨(inv.live l hl).1, TyActions.live_created
                (TyActions.liveSz_focus ann (inv.live l hl).2) pref c2 ity ?_⟩
              rw [nfocus]; exact Int.ne_of_lt (ids l hl)
            · obtain rfl := List.mem_singleton.mp hl
              refine ⟨hs, ?_⟩
              have := TyActions.created_live pref c2 ity (focusMemory ann m)
                (by rw [TyActions.focus_dead, fresh.dead, nfocus]; simp)
              rwa [afocus, nfocus] at this
          · intro a ha b hb e
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact inv.uniq a ha b hb e
            · obtain rfl := List.mem_singleton.mp hb
              exact absurd e (fx a ha)
            · obtain rfl := List.mem_singleton.mp ha
              exact absurd e.symm (fx b hb)
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              rfl
          · intro a ha b hb ne
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact inv.apart a ha b hb ne
            · obtain rfl := List.mem_singleton.mp hb
              refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
              have := addrs a ha
              show a.addr + width a.ity ≤ nextAddress m (width ity) ∨
                nextAddress m (width ity) + width ity ≤ a.addr
              omega
            · obtain rfl := List.mem_singleton.mp ha
              refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
              have := addrs b hb
              show nextAddress m (width ity) + width ity ≤ b.addr ∨
                b.addr + width b.ity ≤ nextAddress m (width ity)
              omega
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              exact absurd rfl ne
          · intro q d hd
            obtain ⟨ok, l, hl, hkq, hf, slot⟩ := inv.defs q d hd
            refine ⟨ok, l, List.mem_append_left _ hl, hkq, hf, ?_⟩
            have := addrs l hl
            exact TyActions.slot_created (TyActions.slot_focus ann slot) pref c2 ity
              (by rw [nfocus]; exact Int.ne_of_lt (ids l hl)) (.inl (by rw [afocus]; omega))
        have hls₁ : Keys (ls ++ [nl]) (gs ++ (xs ++ [(x, ity)])) := by
          simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
          rw [hls, List.append_assoc]
        have hlk₁ : Keys (lk ++ [nl]) (xs ++ [(x, ity)]) := by
          simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hlk ⊢
          rw [hlk]
        have sub₁ : ∀ l ∈ lk ++ [nl], l ∈ ls ++ [nl] := by
          intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · exact List.mem_append_left _ (sub l hl)
          · exact List.mem_append_right _ hl
        have last₁ : m₁.lastAddress = nextAddress m (width ity) := by
          rw [TyActions.created_lastAddress, afocus]
        have fresh₁ : Fresh m₁ (ls ++ [nl]) := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [TyActions.created_dead, TyActions.focus_dead, fresh.dead]
          · intro l hl
            rw [TyActions.created_nextId, nfocus]
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
              exact le_refl _
          · rw [last₁, List.length_append, List.length_singleton]
            push_cast
            omega
        have o := block_halts hret (xs ++ [(x, ity)]) rest h env₁ m₁ (ls ++ [nl]) (lk ++ [nl]) inv₁ hls₁
          hlk₁ sub₁ fresh₁ k hk falls
        have out : m₁.stdout = m.stdout := by
          simp [m₁, TyActions.created_stdout]
        rw [out] at o
        exact Ends.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
          (create.trans bind)) o
      next => cases h
    next => cases h
  next =>
    split at h
    next nd =>
      obtain ⟨nodup, room⟩ := nd
      cases hr : run file ret (gs ++ xs) xs fall ds sz budget e [] with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨R', n'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact run_halts hret nodup hls hlk sub _ _ budget e [] hr env m inv
          (budget_of_fresh fresh (by rw [hlen]; exact room)) k (.base hk falls)
    next => cases h
termination_by sizeOf e

/-! ## The document -/

/-- The body of `main` over the globals `gs` (definitions `ds`): the block, then the return
label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (gs : Vars) (ds : Key → Option Term) :
    Eff → Option Out
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, (_, p))] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then
        block file ret gs (StateGlobals.zeroDefault p) ds (fun _ => 1) [] a
      else none
  | _ => none

/-- The globals are integers of supported types initialised by literals, with distinct symbols
(`TyGlobals.inits`), and `main` is a block of typed integer statements over them and its
locals. -/
def recognizeRes (doc : Codec.Document) : Option Out := do
  let ds := Globals.definitions doc.file
  let gs ← TyGlobals.inits doc.file ds
  if (ds.map fun d => d.1.key).Nodup ∧ ds.length < 1024 then do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file (gs.map fun g => (g.1, g.2.1)) (TyGlobals.defs gs) body
  else none

/-- `recognizeRes`, with the guards and tests the Lir code needs (checked). -/
def recognize (doc : Codec.Document) : Option Out :=
  match recognizeRes doc with
  | some R => if Out.wf R = true then some R else none
  | none => none

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (R : Out) (h : recognizeRes doc = some R)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Ends (file := doc.file) (labels := labels) s R "" := by
  unfold recognizeRes at h
  cases hgs : TyGlobals.inits doc.file (Globals.definitions doc.file) with
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
              have hbody : recognizeBody doc.file (gs.map fun g => (g.1, g.2.1)) (TyGlobals.defs gs)
                  body = some R := by simpa [main, decl] using h
              obtain ⟨s, m, env, xs, lg, hinit, hout, hkeys, inv, fresh, hentry⟩ :=
                TyGlobals.initial_reaches_state doc.file enums args hgs nd room main decl
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
                  have hls : Keys lg ((gs.map fun g => (g.1, g.2.1)) ++ []) := by
                    rw [List.append_nil]
                    unfold Keys
                    have := congrArg (List.map fun p : Sym × IntegerType => (p.1.key, p.2)) hkeys
                    simpa [List.map_map, Function.comp_def] using this
                  have o := block_halts hret [] a hbody env m lg [] inv hls rfl (by simp) fresh
                    [.strongBind (.mk pann (.base (none, bt0))) SAVE env, .annotations xs]
                    (by simp [NoBoundary, hasBoundary]) (fun hz => StateGlobals.main_falls hr hz env xs)
                  rw [hout] at o
                  exact ⟨s, _, hinit, Ends.pre
                    (hentry.trans (ReturnConst.sequence_reaches doc.file _ ann _ a SAVE env _ m)) o⟩
                · cases hbody
              · cases hbody
    · cases h

theorem recognizeRes_of {doc : Codec.Document} {R : Out} (h : recognize doc = some R) :
    recognizeRes doc = some R ∧ Out.wf R = true := by
  unfold recognize at h
  split at h
  · rename_i R' hR
    split at h
    · cases h; exact ⟨hR, by assumption⟩
    · cases h
  · cases h

/-- The observation selected by the termination flag. -/
def Out.obs (R : Out) : Spec.Obs :=
  if R.test.val = 1 then .exit (R.val % 256).toNat [] else .abort []

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with
`R.val mod 256` and no output when the flag is `1`, or aborts with no output. -/
theorem recognize_sound (doc : Codec.Document) (R : Out) (h : recognize doc = some R)
    (args : List String) :
    Spec.CoreUB doc args ∨ Spec.CoreBeh doc args R.obs := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc R (recognizeRes_of h).1 (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    by_cases flag : R.test.val = 1
    · have beh := Spec.CoreBeh.exit (v := spec R.val) (k := (R.val % 256).toNat)
        ⟨s, labels, hinit, reach⟩ (by simp [Out.outcome, flag]) rfl
      simpa [Out.obs, flag, Spec.coreBytes, out] using beh
    · have beh := Spec.CoreBeh.abort ⟨s, labels, hinit, reach⟩ (by simp [Out.outcome, flag])
      simpa [Out.obs, flag, Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.TyRun
