module

public import Silmaril.Compiler.Core.Verified.Call.Defs
public import Silmaril.Cerberus.Core.ArenaRun.Defs

/-! # Successful arithmetic callees as local operand runs

Unlike a top-level reachability witness, a local witness can be passed directly to
`Interleave.drive_task`: that theorem handles early collection of values. Calls
are scheduled separately; these bodies contain no further calls.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CallLocal

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open LoadTask (plain_effectExpr plain_pureExpr plain_value)

variable {file : Program} {labels : Labels}

/-- Exact focused memory, rather than an existential diagnostic location. -/
theorem focus {wc : Bool} {c c' : Control} {k k' : List Frame}
    (ann : List Annot) (m : Mem.Concrete.State) (hp : Plain c')
    (hr : requestAux file labels m c k wc =
      if (focusMemory ann m).currentLocation == m.currentLocation then .next c' k'
      else .next (.setLocation (focusMemory ann m).currentLocation c') k') :
    LocalReaches file labels wc ⟨c, k, m⟩ ⟨c', k', focusMemory ann m⟩ := by
  have shape : focusMemory ann m = {m with currentLocation := (focusMemory ann m).currentLocation} :=
    SeqReach.focusMemory_shape ann m
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation
  · have heq : (focusMemory ann m).currentLocation = m.currentLocation := by simpa using eq
    have hm : focusMemory ann m = m := by rw [shape, heq]
    rw [hm]
    exact .single (.next (by simpa [eq] using hr) hp)
  · refine .head (.next (by simpa [eq] using hr) (LoadTask.plain_setLocation _ _)) ?_
    rw [shape]
    exact .single (.update (requestAux_setLocation file labels m _ c' k' wc))

theorem sequence (ann : List Annot) (p : Pattern Sym) (a b : EE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.sseq p a b)) env, k, m⟩
      ⟨.effectExpr a env, .strongBind p b env :: k, m⟩ := by
  exact .single (.next (by simp [requestAux, awaitsScheduling]) (plain_effectExpr _ _))

theorem bound (ann : List Annot) (e : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
      ⟨.effectExpr e env, .bound :: k, m⟩ := by
  exact .single (.next (by simp [requestAux, awaitsScheduling]) (plain_effectExpr _ _))

theorem bind (ann : List Annot) (s : Sym) (ty : BaseType) (v : Val) (b : EE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false
      ⟨.value v, .strongBind (.mk ann (.base (some s, ty))) b env :: k, m⟩
      ⟨.effectExpr b (extendEnv [(s, v)] env), k, m⟩ := by
  exact .single (.next (by simp [requestAux, awaitsScheduling, matchPattern]) (plain_effectExpr _ _))

theorem pure {wc : Bool} (ann : List Annot) {p : PE} {env : Env} {v : Val}
    (hp : ∀ tags, Eval file tags env (.inl p) (.inl v))
    (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels wc ⟨.effectExpr (.mk ann (.pure p)) env, k, m⟩
      ⟨.value v, k, focusMemory ann m⟩ := by
  refine (focus (c' := .pureExpr p env) (k' := .diagnosticLocation m.currentLocation :: k)
    ann m (plain_pureExpr p env) ?_).trans ?_
  · simp [requestAux, awaitsScheduling, focusMemory]; rfl
  · exact (PureLocal.eval_local file _ (hp _) _ _ rfl).tail
      (.next (requestAux_value_diagnostic file labels _ v _ k wc) (plain_value v))

/-- A callee-local return resolves its own labels before an arena sees it. -/
theorem jump_return {ret l : Sym} {L : Labels} (hl : l.key = ret.key)
    (hret : ReturnLabel L ret) (v : Val) (env : Env) {loc : List Frame}
    (hk : NoBoundary loc) (caller : List Frame) (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ LocalReaches file labels false
      ⟨.value v, .runLabel l [] [] env :: (loc ++ .procedureReturn L :: caller), m⟩
      ⟨.value v, .procedureReturn L :: caller, m'⟩ := by
  obtain ⟨r, bann, pann, r', hr, hlook⟩ := hret
  have hlook' : L.lookup l = some ([r], .mk bann (.pure (.mk pann () (.sym r')))) := by
    rw [ReturnLit.lookup_key hl]; exact hlook
  have hb : hasBoundary (loc ++ .procedureReturn L :: caller) = true := by
    simp [hasBoundary, List.any_append]
  refine ⟨focusMemory bann m, by simp, ?_⟩
  refine .head (.next (c' := .effectExpr (.mk bann (.pure (.mk pann () (.sym r'))))
      (extendEnv [(r, v)] env)) (k' := .procedureReturn L :: caller)
    ?_ (plain_effectExpr _ _)) ?_
  · rw [requestAux.eq_def]
    simp [awaitsScheduling, requestJump, hb, jump, jumpDestination,
      Call.context_local hk L caller, hlook']
  · exact pure bann (fun _ => .sym (ConvInt.lookup_one hr)) _ _

/-- A linear return statement, with the same expression recognizer as `Call`.
The restriction to the first return avoids silently claiming State completeness. -/
def retTerm (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ ConvInt.isConvLoadedInt file s = true then
        match IntExpr.term file u e with
        | some t => if t.reads = false then some t else none
        | none => none
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retTerm file ret a
  | _ => none

/-- A successful recognised arithmetic return has a local trace, under arbitrary
caller frames. No per-step boundary/unfinished/Plain assumptions are supplied. -/
theorem retTerm_returns {ret : Sym} {L : Labels} (hret : ReturnLabel L ret)
    (e : EE) (t : IntExpr.Term) (h : retTerm file ret e = some t) (ok : t.Ok 0)
    (env : Env) {loc : List Frame} (hk : NoBoundary loc)
    (caller : List Frame) (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ LocalReaches file labels false
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      ⟨.value (IntExpr.spec (t.val 0)), .procedureReturn L :: caller, m'⟩ := by
  unfold retTerm at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i t' ht
        split at h
        · rename_i hr
          have he := Option.some.inj h
          subst t
          have none₁ : ∀ {P : Prop}, t'.reads = true → P := fun r => by rw [hr] at r; cases r
          let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
          let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env ::
            (loc ++ .procedureReturn L :: caller)
          obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
            (labels := labels) (env := env) (id := 0) (addr := 0) t' ht none₁
            ReturnExpr.isInt_zero ok (.bound :: kR) m none₁
          let v : Val := IntExpr.spec (t'.val 0)
          have popped : LocalReaches file labels false ⟨.value v, fr ++ .bound :: kR, m₁⟩
              ⟨.value v, kR, m₁⟩ := by
            rcases hfr with ⟨rfl, -⟩ | rfl
            all_goals exact .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value v))
          let env₁ := extendEnv [(u, v)] env
          have heval : ∀ tags, Eval file tags env₁
              (.inl (.mk cann () (.call (.sym s)
                [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                  .mk a3 () (.sym u')]))) (.inl v) := fun _ =>
            ConvInt.convLoadedInt_eval (ann := tyann) hs
              (IntExpr.Term.ok_int ReturnExpr.isInt_zero t' ok)
              (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
          obtain ⟨m', out, back⟩ := jump_return (file := file) (labels := labels) hl hret v env₁ hk
            caller (focusMemory rann m₁)
          refine ⟨m', by simp [out, tch.stdout], ?_⟩
          refine (sequence ann _ _ _ env _ m).trans ((bound bann _ env kR m).trans ?_)
          refine run.trans (popped.trans ((bind pann u ty v R env _ m₁).trans ?_))
          refine (focus (c' := .pureExpr (.mk cann () (.call (.sym s)
              [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                .mk a3 () (.sym u')])) env₁)
            (k' := .runLabel l [] [] env₁ :: (loc ++ .procedureReturn L :: caller))
            rann m₁ (plain_pureExpr _ _) ?_).trans ?_
          · simp [R, requestAux, awaitsScheduling, focusMemory]; rfl
          · exact (PureLocal.eval_local file _ (heval _) _ _ rfl).trans back
        · cases h
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    obtain ⟨m', out, run⟩ := retTerm_returns hret a t h ok env
      (loc := .strongBind (.mk pann (.base (none, ty))) b env :: loc)
      (ReturnLit.noBoundary_cons hk trivial) caller m
    exact ⟨m', out, (sequence ann _ _ _ env _ m).trans run⟩
  · cases h
termination_by sizeOf e

/-- A complete callee body with one arithmetic return. -/
def bodyTerm (file : File Codec.wireModel Unit Unit) : Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ ReturnLit.saveFree a = true then retTerm file ret a else none
  | _ => none

theorem body_returns {body : EE} {t : IntExpr.Term} (h : bodyTerm file body = some t)
    (ok : t.Ok 0) (env : Env) (caller : List Frame) (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ LocalReaches file labels false
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: caller, m⟩
      ⟨.value (IntExpr.spec (t.val 0)), caller, m'⟩ := by
  unfold bodyTerm at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      have hret : ReturnLabel (CallReach.bodyLabels
          (.mk ann (.sseq (.mk pann (.base (none, bt0))) a
            (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r'))))))))) ret := by
        refine ⟨r, bann, pann', r', hr, ?_⟩
        simp [CallReach.bodyLabels, saves, ReturnLit.saves_saveFree a hfree, Map.ofList]
      obtain ⟨m', out, run⟩ := retTerm_returns hret a t h ok env
        (loc := [.strongBind (.mk pann (.base (none, bt0))) _ env])
        (by simp [NoBoundary, hasBoundary]) caller m
      refine ⟨m', out, (sequence ann _ _ _ env _ m).trans (run.tail ?_)⟩
      exact .next (by simp [requestAux, awaitsScheduling]) (plain_value _)
    · cases h
  · cases h

/-- The actual arithmetic-callee trace is a successful operand trace. The arena
collects it using the established early-finish rule, without an invariant supplied
by the caller of this theorem. -/
theorem body_in_arena {body : EE} {t : IntExpr.Term} (h : bodyTerm file body = some t)
    (ok : t.Ok 0) (env : Env) (m : Mem.Concrete.State)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    ∃ m', m'.stdout = m.stdout ∧ CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr body env,
        [.procedureReturn (CallReach.bodyLabels body)])], k, m⟩
      ⟨.interleave ((i, IntExpr.spec (t.val 0), []) :: done) [], k, m'⟩ := by
  obtain ⟨m', out, run⟩ := body_returns (labels := labels) h ok env [] m
  refine ⟨m', out, reaches_of_local file labels ?_⟩
  have pending : Pending [] i := ⟨by simp, by simp⟩
  apply drive_task file labels pending
  exact ⟨[], by simpa [taskFlag] using run, rfl⟩

end Silmaril.Compile.Core.Verified.CallLocal
