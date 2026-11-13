module

public import Silmaril.Compiler.Core.Verified.ParamCallTail.Defs
public import Silmaril.Compiler.Core.Verified.ParamCallReserve.Defs
public import Silmaril.Compiler.Core.Verified.ParamManyBool.Defs
/-! # Sequences of parameter-call conditions

`if (f(a) != c) abort();`, `if (f(a)) abort();` or `if (g(a₁, …, aₖ) != c) abort();` any number of times, then `exit(n)`, `abort()` or `return n;`. The
recognizer builds a tree whose inner nodes are parameter-call conditions
(`ParamCallBool.condition`) and whose leaves terminate. Both successors of a condition continue
with the CFG's pending strong sequences, so a condition without `else` falls through to the next
statement. Each call allocates its argument objects and its callee's locals, at most `ParamMany.cost`
objects: `k` bounds the allocations on a path, and `CallParamAlloc.Reserve k` keeps room for them
and for an exit argument.

The tree is a `StateExit.Result`: the target computes its termination flag and exit value, with
each call's parameter body inlined (`ParamCallCompare.Plan.inst`), at run time.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamCallChain

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open ReturnLit (Eff ReturnLabel)
open StateExit (Result Shows)
open CallParamAlloc (Reserve)

/-- The test of a condition: a parameter-call comparison under Cerberus's zero test
(`if (f(a) != c)`, two operand arenas) or compared with zero directly (`if (f(a))`, one arena),
or a comparison of a call with several arguments, under the zero test or not
(`ParamManyBool.condition`, `ParamMany.condition`). The successors remain syntax. -/
def test (file : File Codec.wireModel Unit Unit) (e : EE) : Option (IntExpr.Term × EE × EE) :=
  match ParamCallBool.condition file e with
  | some (t, y, n) => some (t.result, y, n)
  | none => match ParamCallReserve.condition file e with
    | some (t, y, n) => some (t.result, y, n)
    | none => match ParamManyBool.condition file e with
      | some (t, y, n) => some (t.result, y, n)
      | none => (ParamMany.condition file e).map fun (t, y, n) => (t.result, y, n)

theorem test_runs {file : Program} {labels : Labels} {r : Nat} {e y n : EE} {c : IntExpr.Term}
    (h : test file e = some (c, y, n)) (env : Env) (m : Mem.Concrete.State) (k : List Frame)
    (hb : Reserve (r + ParamMany.cost) m) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      c.Ok 0 ∧ ∃ env' m', m'.stdout = m.stdout ∧ Reserve r m' ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if c.val 0 = 1 then n else y) env', k, m'⟩ := by
  have hb' : Reserve (r + ParamRun.maxLocals + 1) m :=
    ParamMany.reserve_mono hb (by unfold ParamMany.cost CallMany.maxArgs; omega)
  unfold test at h
  split at h
  · rename_i t y' n' hc
    cases h
    exact ParamCallBool.condition_runs (labels := labels) hc env m k hb'
  · split at h
    · rename_i t y' n' hc
      cases h
      exact ParamCallReserve.condition_runs (labels := labels) hc env m k hb'
    · split at h
      · rename_i t y' n' hc
        cases h
        exact ParamManyBool.condition_runs (labels := labels) hc env m k hb
      · obtain ⟨⟨t, y', n'⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact ParamMany.condition_runs (labels := labels) hc env m k hb

/-- Terminal leaves and parameter-call conditions through strong sequencing glue. -/
def tree (file : File Codec.wireModel Unit Unit) (ret : Sym) :
    Nat → Nat → EE → List EE → Option Result
  | 0, _, _, _ => none
  | f + 1, k, e, P =>
    if AbortCall.abortStmt file e then some .aborting else
    match ExitCall.recognizeBody file e with
    | some n => if -2147483648 ≤ n ∧ n ≤ 2147483647 then some (.returning (.lit n)) else none
    | none => match ReturnLit.retLit file ret e with
      | some n => if -2147483648 ≤ n ∧ n ≤ 2147483647 then some (.returning (.lit n)) else none
      | none => match test file e with
        | some (c, y, n) =>
          if ParamMany.cost ≤ k then
            match tree file ret f (k - ParamMany.cost) y P, tree file ret f (k - ParamMany.cost) n P with
            | some a, some b =>
              if StateGlobals.termSize (Result.choose c a b).test +
                  StateGlobals.termSize (Result.choose c a b).ret ≤ State.maxSize then
                some (Result.choose c a b)
              else none
            | _, _ => none
          else none
        | none => match e with
          | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => tree file ret f k a (b :: P)
          | .mk _ (.pure (.mk _ () (.val .unit))) => match P with
            | b :: P' => tree file ret f k b P'
            | [] => none
          | _ => none

variable {file : Program} {labels : Labels}

theorem tree_runs {ret : Sym} (hret : ReturnLabel labels ret) :
    (fuel k : Nat) → {e : EE} → {P : List EE} → {r : Result} →
    tree file ret fuel k e P = some r → ∀ (env : Env) (m : Mem.Concrete.State)
      (F : List Frame), Cfg.Pends [] P F → Reserve k m →
      Shows (file := file) (labels := labels) ⟨.effectExpr e env, F, m⟩ r m.stdout
  | 0, _, _, _, _, h => by simp [tree] at h
  | f + 1, k, e, P, r, h => by
    unfold tree at h
    split at h
    · rename_i hab
      cases h
      intro env m F _ _
      obtain ⟨m', reach, out⟩ := AbortCall.abortStmt_reaches (labels := labels) hab env F m
      exact .inl ⟨by simp [StateExit.Result.Ok, Result.aborting, IntExpr.Term.Ok, IntExpr.Term.val,
          ConvInt.IsInt],
        m', out, by simpa [StateExit.Result.outcome, Result.aborting, IntExpr.Term.val] using reach⟩
    split at h
    · rename_i n hn
      split at h
      · rename_i hi
        cases h
        intro env m F _ hb
        obtain ⟨m', reach, out⟩ := StateExit.exit_reaches (file := file) (labels := labels) e hn env F m
          hb.budget
        exact .inl ⟨by simpa [StateExit.Result.Ok, Result.returning, IntExpr.Term.Ok, IntExpr.Term.val,
            ConvInt.IsInt] using hi,
          m', out, by simpa [StateExit.Result.outcome, Result.returning, IntExpr.Term.val] using reach⟩
      · cases h
    split at h
    · rename_i n hn
      split at h
      · rename_i hi
        cases h
        intro env m F hp _
        obtain ⟨m', out, reach⟩ := ReturnLit.retLit_halts (file := file) hret e n hn env hp.noBoundary m
        exact .inl ⟨by simpa [StateExit.Result.Ok, Result.returning, IntExpr.Term.Ok, IntExpr.Term.val,
            ConvInt.IsInt] using hi,
          m', out, by simpa [StateExit.Result.outcome, Result.returning, IntExpr.Term.val] using reach⟩
      · cases h
    split at h
    · rename_i c y n hc
      split at h
      · rename_i hk
        split at h
        · rename_i a b ha hb'
          split at h
          · cases h
            intro env m F hp hb
            rcases test_runs (r := k - ParamMany.cost) (labels := labels) hc env m F
                (by rwa [show k - ParamMany.cost + ParamMany.cost = k by omega]) with
              ub | ⟨ok, env', m', out, reserve, run⟩
            · exact .inr ub
            · by_cases flag : c.val 0 = 1
              · rw [ite_eq_left flag] at run
                have sh := tree_runs hret f (k - ParamMany.cost) hb' env' m' F hp reserve
                rw [out] at sh
                exact StateExit.Shows.pre run (StateExit.shows_choose_right ok flag sh)
              · rw [ite_eq_right flag] at run
                have sh := tree_runs hret f (k - ParamMany.cost) ha env' m' F hp reserve
                rw [out] at sh
                exact StateExit.Shows.pre run (StateExit.shows_choose_left ok flag sh)
          · cases h
        · cases h
      · cases h
    · split at h
      · rename_i ann pann ty a b _ _ _ _
        intro env m F hp hb
        exact StateExit.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env F m)
          (tree_runs hret f k h env m _ (.bind pann ty b env (by simp [LoopMain.EnvOk]) hp) hb)
      · rename_i ann pann _ _ _ _
        split at h
        · rename_i b P'
          intro env m F hp hb
          obtain ⟨env', F', _, hp', reach⟩ := Cfg.Pends.pop (file := file) (labels := labels) F hp
            (ReturnConst.focusMemory ann m)
          have sh := tree_runs hret f k h env' (ReturnConst.focusMemory ann m) F' hp' (hb.focus ann)
          simpa using StateExit.Shows.pre ((StateStmt.pure_unit_reaches ann pann env F m).trans reach) sh
        · cases h
      · cases h

/-- Allocations a recognized `main` may make: each call takes its argument objects and room for
`ParamRun.maxLocals` callee locals. -/
def calls : Nat := 1024 * ParamMany.cost

def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Result
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then tree file ret 1024 calls a [] else none
  | _ => none

def recognize (doc : Codec.Document) : Option Result := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-- `StartupMem.initial_reaches_body_mem`, naming the labels of `main`'s body. -/
theorem initial_reaches_body (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s m xs, initial file enums args = .ok (s, Map.ofList (saves body).reverse) ∧ m.stdout = "" ∧
      m.lastAddress = StartupReach.errnoAddr ∧ m.dead = [] ∧
      Reaches file (Map.ofList (saves body).reverse) s ⟨.effectExpr body ∅, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  obtain ⟨m', xs, out, hlast, hdead, reach⟩ := StartupMem.startup_errno_mem file labels
    (.effectExpr body ∅) ({enumTypes := enums} : Mem.Concrete.State) rfl rfl
  refine ⟨_, m', xs, ?_, by simpa using out, hlast, hdead,
    (StartupReach.enter_main_reaches file labels args ∅ _ main decl).trans reach⟩
  simp only [initial]
  rw [List.filterMap_eq_nil_iff.mpr]
  · simp [main, decl]
  · rintro ⟨_, _ | _⟩ hx
    · exact absurd rfl (nodefs _ hx _ _)
    · rfl

theorem recognize_reaches (doc : Codec.Document) (p : Result) (h : recognize doc = some p)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s p "" := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
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
          have hbody : recognizeBody doc.file body = some p := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, m, xs, hinit, hout, hlast, hdead, hentry⟩ := initial_reaches_body
            doc.file enums args hdefs main decl
          obtain ⟨labels, hlabels⟩ : ∃ labels : Labels, labels = Map.ofList (saves body).reverse :=
            ⟨_, rfl⟩
          rw [← hlabels] at hinit hentry
          unfold recognizeBody at hbody
          split at hbody
          · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]
                refine ⟨r, bann, pann', r', hr, ?_⟩
                simp [saves, StmtIf.labelFree_saves a hfree, Map.ofList]
              let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)]
                (.mk bann (.pure (.mk pann' () (.sym r')))))
              let k : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
              have hp : Cfg.Pends [] [] k := .base (by simp [k, ReturnLit.NoBoundary, hasBoundary])
              have hb : Reserve calls m :=
                ⟨by simp [hdead], by rw [hlast]; decide, by rw [hlast]; decide⟩
              have sh := tree_runs (labels := labels) hret 1024 calls hbody ∅ m k hp hb
              rw [hout] at sh
              exact ⟨s, labels, hinit, StateExit.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) sh⟩
            · cases hbody
          · cases hbody

theorem recognize_sound (doc : Codec.Document) (p : Result) (h : recognize doc = some p)
    (args : List String) : Spec.CoreUB doc args ∨ p.Ok ∧ Spec.CoreBeh doc args p.obs := by
  obtain ⟨s, labels, hinit, sh⟩ := recognize_reaches doc p h (Map.ofList (doc.enumBindings.getD [])) args
  rcases sh with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    by_cases flag : p.test.val 0 = 1
    · have beh := Spec.CoreBeh.exit (v := IntExpr.spec (p.ret.val 0)) (k := (p.ret.val 0 % 256).toNat)
        ⟨s, labels, hinit, reach⟩ (by simp [StateExit.Result.outcome, flag]) rfl
      simpa [StateExit.Result.obs, flag, Spec.coreBytes, out] using beh
    · have beh := Spec.CoreBeh.abort ⟨s, labels, hinit, reach⟩
        (by simp [StateExit.Result.outcome, flag])
      simpa [StateExit.Result.obs, flag, Spec.coreBytes, out] using beh
  · exact .inl (.inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩)

end Silmaril.Compile.Core.Verified.ParamCallChain
