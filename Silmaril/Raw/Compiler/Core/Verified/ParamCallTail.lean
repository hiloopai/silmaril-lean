module

public import Silmaril.Compiler.Core.Verified.ParamCallBool.Defs
public import Silmaril.Compiler.Core.Verified.CfgSound.Defs
public import Silmaril.Compiler.Core.Verified.StateExit.Defs
/-! # A parameter-call condition whose two successors terminate

The call is executed in its operand arena. Only after its result is obtained is
the selected abort/exit successor entered. The pending-statement relation is the
CFG machine's; no caller-slot preservation is needed after a terminal branch.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamCallTail

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open ReturnLit (Eff)
open StateExit (Result Shows)
open CallParamAlloc (Reserve)

inductive Stop where
  | abort
  | exit (n : Int)

def Stop.result : Stop → Result
  | .abort => .aborting
  | .exit n => .returning (.lit n)

/-- A terminal branch, with the CFG's pending strong sequences. -/
def stop (file : File Codec.wireModel Unit Unit) : Nat → EE → List EE → Option Stop
  | 0, _, _ => none
  | f + 1, e, P =>
    if AbortCall.abortStmt file e then some .abort else
    match ExitCall.recognizeBody file e with
    | some n => if -2147483648 ≤ n ∧ n ≤ 2147483647 then some (.exit n) else none
    | none => match e with
      | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => stop file f a (b :: P)
      | .mk _ (.pure (.mk _ () (.val .unit))) => match P with
        | b :: P' => stop file f b P'
        | [] => none
      | _ => none

structure Plan where
  test : ParamCallBool.Plan
  yes : Stop
  no : Stop

def Plan.result (p : Plan) : Result := .choose p.test.result p.yes.result p.no.result

/-- Recognize one terminal call test through strong sequencing glue. -/
def calls (file : File Codec.wireModel Unit Unit) : Nat → EE → List EE → Option Plan
  | 0, _, _ => none
  | f + 1, e, P =>
    match ParamCallBool.condition file e with
    | some (t, y, n) => do
      let a ← stop file 1024 y P
      let b ← stop file 1024 n P
      pure ⟨t, a, b⟩
    | none => match e with
      | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => calls file f a (b :: P)
      | .mk _ (.pure (.mk _ () (.val .unit))) => match P with
        | b :: P' => calls file f b P'
        | [] => none
      | _ => none

variable {file : Program} {labels : Labels}

theorem stop_runs : (fuel : Nat) → {e : EE} → {P : List EE} → {s : Stop} →
    stop file fuel e P = some s → ∀ (env : Env) (m : Mem.Concrete.State)
      (F : List Frame), Cfg.Pends [] P F → Reserve 0 m →
      Shows (file := file) (labels := labels) ⟨.effectExpr e env, F, m⟩ s.result m.stdout
  | 0, _, _, _, h => by simp [stop] at h
  | f + 1, e, P, s, h => by
    unfold stop at h
    split at h
    · rename_i hab
      cases h
      intro env m F _ _
      obtain ⟨m', r, out⟩ := AbortCall.abortStmt_reaches (labels := labels) hab env F m
      exact .inl ⟨by simp [Result.Ok, Stop.result, Result.aborting, IntExpr.Term.Ok, IntExpr.Term.val, ConvInt.IsInt],
        m', out, by simpa [Result.outcome, Stop.result, Result.aborting, IntExpr.Term.val] using r⟩
    · split at h
      · rename_i n hn
        split at h
        · rename_i hi
          cases h
          intro env m F _ hb
          obtain ⟨m', r, out⟩ := StateExit.exit_reaches (file := file) (labels := labels) e hn env F m hb.budget
          exact .inl ⟨by simpa [Result.Ok, Stop.result, Result.returning, IntExpr.Term.Ok, IntExpr.Term.val, ConvInt.IsInt] using hi,
            m', out, by simpa [Result.outcome, Stop.result, Result.returning, IntExpr.Term.val] using r⟩
        · cases h
      · split at h
        · rename_i ann pann ty a b _ _
          intro env m F hp hb
          exact StateExit.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env F m)
            (stop_runs f h env m _ (.bind pann ty b env (by simp [LoopMain.EnvOk]) hp) hb)
        · rename_i ann pann _ _
          split at h
          · rename_i b P'
            intro env m F hp hb
            obtain ⟨env', F', _, hp', r⟩ := Cfg.Pends.pop (file := file) (labels := labels) F hp (ReturnConst.focusMemory ann m)
            have sh := stop_runs f h env' (ReturnConst.focusMemory ann m) F' hp' (hb.focus ann)
            simpa using StateExit.Shows.pre ((StateStmt.pure_unit_reaches ann pann env F m).trans r) sh
          · cases h
        · cases h

theorem calls_runs : (fuel : Nat) → {e : EE} → {P : List EE} → {p : Plan} →
    calls file fuel e P = some p → ∀ (env : Env) (m : Mem.Concrete.State)
      (F : List Frame), Cfg.Pends [] P F → Reserve (ParamRun.maxLocals + 1) m →
      Shows (file := file) (labels := labels) ⟨.effectExpr e env, F, m⟩ p.result m.stdout
  | 0, _, _, _, h => by simp [calls] at h
  | f + 1, e, P, p, h => by
    unfold calls at h
    split at h
    · rename_i t y n ht
      cases hy : stop file 1024 y P with
      | none => simp [hy] at h
      | some a =>
        cases hn : stop file 1024 n P with
        | none => simp [hy, hn] at h
        | some b =>
          simp only [hy, hn, bind, Option.bind, pure, Option.some.injEq] at h
          subst p
          intro env m F hp hb
          rcases ParamCallBool.condition_runs (r := 0) (labels := labels) ht env m F (by simpa using hb) with
            ub | ⟨ok, env', m', out, reserve, run⟩
          · exact .inr ub
          · by_cases flag : t.result.val 0 = 1
            · rw [ite_eq_left flag] at run
              have sh := stop_runs (labels := labels) 1024 hn env' m' F hp reserve
              rw [out] at sh
              exact StateExit.Shows.pre run (StateExit.shows_choose_right ok flag sh)
            · rw [ite_eq_right flag] at run
              have sh := stop_runs (labels := labels) 1024 hy env' m' F hp reserve
              rw [out] at sh
              exact StateExit.Shows.pre run (StateExit.shows_choose_left ok flag sh)
    · split at h
      · rename_i ann pann ty a b _
        intro env m F hp hb
        exact StateExit.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env F m)
          (calls_runs f h env m _ (.bind pann ty b env (by simp [LoopMain.EnvOk]) hp) hb)
      · rename_i ann pann _
        split at h
        · rename_i b P'
          intro env m F hp hb
          obtain ⟨env', F', _, hp', r⟩ := Cfg.Pends.pop (file := file) (labels := labels) F hp (ReturnConst.focusMemory ann m)
          have sh := calls_runs f h env' (ReturnConst.focusMemory ann m) F' hp' (hb.focus ann)
          simpa using StateExit.Shows.pre ((StateStmt.pure_unit_reaches ann pann env F m).trans r) sh
        · cases h
      · cases h

def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Plan
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (_, _) [(_, _)] (.mk _ (.pure (.mk _ () (.sym _))))))) => calls file 1024 a []
  | _ => none

def recognize (doc : Codec.Document) : Option Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

theorem recognize_reaches (doc : Codec.Document) (p : Plan) (h : recognize doc = some p)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s p.result "" := by
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
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ := StartupMem.initial_reaches_body_mem
            doc.file enums args hdefs main decl
          unfold recognizeBody at hbody
          split at hbody
          · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
            let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
            let k : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
            have hp : Cfg.Pends [] [] k := .base (by simp [k, ReturnLit.NoBoundary, hasBoundary])
            have hb : Reserve (ParamRun.maxLocals + 1) m := ⟨by simp [hdead], by rw [hlast]; decide, by rw [hlast]; decide⟩
            have sh := calls_runs (labels := labels) 1024 hbody ∅ m k hp hb
            rw [hout] at sh
            exact ⟨s, labels, hinit, StateExit.Shows.pre
              (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) sh⟩
          · cases hbody

theorem recognize_sound (doc : Codec.Document) (p : Plan) (h : recognize doc = some p)
    (args : List String) : Spec.CoreUB doc args ∨ p.result.Ok ∧
      Spec.CoreBeh doc args p.result.obs := by
  obtain ⟨s, labels, hinit, sh⟩ := recognize_reaches doc p h (Map.ofList (doc.enumBindings.getD [])) args
  rcases sh with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    by_cases flag : p.result.test.val 0 = 1
    · have beh := Spec.CoreBeh.exit (v := IntExpr.spec (p.result.ret.val 0)) (k := (p.result.ret.val 0 % 256).toNat)
        ⟨s, labels, hinit, reach⟩ (by simp [Result.outcome, flag]) rfl
      simpa [Result.obs, flag, Spec.coreBytes, out] using beh
    · have beh := Spec.CoreBeh.abort ⟨s, labels, hinit, reach⟩
        (by simp [Result.outcome, flag])
      simpa [Result.obs, flag, Spec.coreBytes, out] using beh
  · exact .inl (.inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩)

end Silmaril.Compile.Core.Verified.ParamCallTail
