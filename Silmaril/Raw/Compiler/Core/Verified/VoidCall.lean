module

public import Silmaril.Compiler.Core.Verified.StateParam.Defs

/-! # Effect-free void calls as CFG statements

An ordinary, known, no-parameter void procedure whose body contains only unit
statements and void returns can be inlined as an empty sequence of operations.
The proof retains all memory except diagnostic location changes. These calls
allocate nothing, so they remain safe on arbitrary CFG back edges.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.VoidCall

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel saveFree noBoundary_cons)
open ReturnConst (focusMemory)
open Call (callSite callee retKind voidRet voidBody context_local
  lookup_ext2_first lookup_ext2_second lookup_ext2_other
  cfunction_reaches length_eval pureEval_of compatible_reaches)
open LoadTask (Touched)

variable {file : Program} {labels : Labels}

open ReturnConst

theorem skip_touched (file : Program) (labels : Labels) (e : EE)
    (h : ReturnConst.skip e = true) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧
      PureEval.Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold ReturnConst.skip at h
  split at h
  · rename_i ann pann u
    refine ⟨focusMemory ann m, LoadTask.focusMemory_touched ann m, ?_⟩
    exact (effect_pure_reaches file labels ann _ env k m).trans
      ((pure_value_reaches file labels pann .unit env _ _).trans
        (diagnostic_reaches file labels m.currentLocation .unit k _))
  · rename_i ann patann ty a b
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨m₁, out₁, ra⟩ := skip_touched file labels a ha env
      (.strongBind (.mk patann (.base (none, ty))) b env :: k) m
    obtain ⟨m₂, out₂, rb⟩ := skip_touched file labels b hb env k m₁
    refine ⟨m₂, out₁.trans out₂, ?_⟩
    exact (sequence_reaches file labels ann _ a b env k m).trans
      (ra.trans ((wildcard_sequence_reaches file labels patann ty .unit b env k m₁).trans rb))
  · cases h
termination_by sizeOf e

theorem voidRet_touched {ret : Sym} {L : Labels} (hret : ReturnLabel L ret) (e : EE)
    (h : voidRet ret e = true) (env : Env) {loc : List Frame} (hk : NoBoundary loc)
    (caller : List Frame) (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ PureEval.Reaches file labels
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      ⟨.value .unit, .procedureReturn L :: caller, m'⟩ := by
  unfold voidRet at h
  split at h
  · rename_i ann l pann
    obtain ⟨m', out, back⟩ := StateParam.jump_return (file := file) (labels := labels)
      (of_decide_eq_true h) hret .unit env hk caller (ReturnConst.focusMemory ann m)
    refine ⟨m', (LoadTask.focusMemory_touched ann m).trans out, ?_⟩
    refine (Straight.focus_reaches Straight.request_run).trans ?_
    exact (ReturnConst.pure_value_reaches file labels pann .unit env _ _).trans (reaches_of_local file labels back)
  · rename_i ann pann ty a b
    rcases Bool.or_eq_true_iff.mp h with ha | hab
    · obtain ⟨m', out, r⟩ := voidRet_touched hret a ha env
        (loc := .strongBind (.mk pann (.base (none, ty))) b env :: loc) (noBoundary_cons hk trivial)
        caller m
      exact ⟨m', out, (ReturnConst.sequence_reaches file labels ann _ a b env _ m).trans r⟩
    · obtain ⟨hs, hb⟩ := Bool.and_eq_true_iff.mp hab
      obtain ⟨m₁, out₁, ra⟩ := skip_touched file labels a hs env
        (.strongBind (.mk pann (.base (none, ty))) b env :: (loc ++ .procedureReturn L :: caller)) m
      obtain ⟨m₂, out₂, rb⟩ := voidRet_touched hret b hb env hk caller m₁
      exact ⟨m₂, out₁.trans out₂, (ReturnConst.sequence_reaches file labels ann _ a b env _ m).trans
        (ra.trans ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env _ m₁).trans rb))⟩
  · cases h
termination_by sizeOf e

/-- The body of a `void` callee returns `unit` to the caller. -/
theorem voidBody_touched {body : EE} (h : voidBody body = true) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ PureEval.Reaches file labels
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: caller, m⟩
      ⟨.value .unit, .procedureReturn (CallReach.bodyLabels body) :: caller, m'⟩ := by
  unfold voidBody at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r pinfo dann bann pann' r'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hfree⟩, hskip | hret⟩ := h
    · let SAVE : EE := .mk sann (.save (ret, bt) [(r, (pinfo, .mk dann () (.val .unit)))]
        (.mk bann (.pure (.mk pann' () (.sym r')))))
      let k := Frame.procedureReturn (CallReach.bodyLabels
        (.mk ann (.sseq (.mk pann (.base (none, bt0))) a SAVE))) :: caller
      obtain ⟨m₁, out₁, ra⟩ := skip_touched file labels a hskip env
        (.strongBind (.mk pann (.base (none, bt0))) SAVE env :: k) m
      let m₂ := ReturnConst.focusMemory sann m₁
      refine ⟨ReturnConst.focusMemory bann m₂, out₁.trans
        ((LoadTask.focusMemory_touched sann m₁).trans (LoadTask.focusMemory_touched bann m₂)), ?_⟩
      refine (ReturnConst.sequence_reaches file labels ann _ a SAVE env _ m).trans
        (ra.trans ((ReturnConst.wildcard_sequence_reaches file labels pann bt0 .unit SAVE env _ m₁).trans ?_))
      refine (ReturnConst.save_reaches file labels sann _ r pinfo _ _ env k m₁).trans ?_
      refine (ReturnConst.pure_value_reaches file labels dann .unit env _ _).trans ?_
      refine (ReturnConst.saveArgument_reaches file labels r .unit _ env k m₂).trans ?_
      refine (ReturnConst.effect_pure_reaches file labels bann _ (env.insert r .unit) k m₂).trans ?_
      exact (ReturnConst.pure_sym_reaches file labels pann' r r' hr.symm .unit env _ _).trans
        (ReturnConst.diagnostic_reaches file labels m₂.currentLocation .unit k _)
    · obtain ⟨m', out, back⟩ := voidRet_touched (file := file) (labels := labels)
        (ReturnLit.returnLabel_body (pat := .mk pann (.base (none, bt0))) (ann := ann) (sann := sann)
          (bann := bann) (pann' := pann') (bt := bt) (info := (pinfo, .mk dann () (.val .unit))) hr hfree)
        a hret env (loc := [.strongBind (.mk pann (.base (none, bt0))) _ env])
        (by simp [NoBoundary, hasBoundary]) caller m
      exact ⟨m', out, (ReturnConst.sequence_reaches file labels ann _ a _ env _ m).trans back⟩
  · cases h

theorem body_touched {body : EE} (h : voidBody body = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ PureEval.Reaches file labels
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: k, m⟩
      ⟨.value .unit, k, m'⟩ := by
  obtain ⟨m', touch, run⟩ := voidBody_touched (labels := labels) h env k m
  exact ⟨m', touch, run.trans (CallReach.return_reaches .unit _ k m')⟩

theorem call_touched {e : EE} {g : Sym}
    (hs : callSite file e = some (g, false)) (hc : callee file g false = some none)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ PureEval.Reaches file labels
      ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨loc, attrs, fty, variadic, proto, dloc, marker, bt, body, hstd, hinfo, hdecl, hfk, hbody⟩ :=
    Call.callee_spec hc
  unfold callSite at hs
  split at hs
  · rename_i ann pann p pbt fann vann g' lann tann fa fty' fbt pa pty pbt' w1a w1 w2a w2 cann cpann
      p₁ iann oann lenann len lnann pty₁ zann z iann' cpa cva rty cfa fty₁ ccann mt pann₂ p₂ no1 no2
    split at hs
    · rename_i cond
      obtain ⟨hp₁, hp₂, hpty, hfty, hne, hpf, hpp, rfl, hlen⟩ := cond
      have hrk : retKind rty = some false ∧ g' = g := by
        cases h : retKind rty with
        | none => simp [h] at hs
        | some b =>
          simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          exact ⟨by rw [hs.2], hs.1⟩
      obtain ⟨hrk, rfl⟩ := hrk
      let fp : Val := .loaded (.specified (.pointer (.function g')))
      let env₁ := extendEnv [(p, fp)] env
      let env₂ := extendEnv [(fty', (.ctype fty : Val)), (pty, .list .ctype [])] env₁
      have l1 : env₁.lookup p₁ = some fp := ConvInt.lookup_one hp₁
      have l2 : env₂.lookup pty₁ = some (.list .ctype []) :=
        lookup_ext2_second hpty (fun h => hne h.symm)
      have l3 : env₂.lookup fty₁ = some (.ctype fty) := lookup_ext2_first hfty
      have l4 : env₂.lookup p₂ = some fp := by
        rw [lookup_ext2_other (by rw [hp₂]; exact hpf) (by rw [hp₂]; exact hpp)]
        exact ConvInt.lookup_one hp₂
      have hmatch : matchPattern (.mk tann (.ctor .tuple [.mk fa (.base (some fty', fbt)),
          .mk pa (.base (some pty, pbt')), .mk w1a (.base (none, w1)), .mk w2a (.base (none, w2))]))
          (.tuple [.ctype fty, .list .ctype (([] : List (Option Sym × Ctype)).map fun q => .ctype q.2),
            boolean variadic, boolean proto]) =
          some [(fty', .ctype fty), (pty, .list .ctype [])] := rfl
      let m₁ := SeqReach.focusMemory fann m
      let m₂ := SeqReach.focusMemory lann m₁
      let m₃ := SeqReach.focusMemory iann m₂
      let m₄ := SeqReach.focusMemory iann' m₃
      obtain ⟨m', touch, run⟩ := body_touched (labels := labels) hbody env₂ k (SeqReach.focusMemory ccann m₄)
      refine ⟨m', (LoadTask.focusMemory_touched fann m).trans
        ((LoadTask.focusMemory_touched lann m₁).trans
          ((LoadTask.focusMemory_touched iann m₂).trans
            ((LoadTask.focusMemory_touched iann' m₃).trans
              ((LoadTask.focusMemory_touched ccann m₄).trans touch)))), ?_⟩
      apply Relation.ReflTransGen.trans (b :=
        ⟨.effectExpr body env₂, .procedureReturn (CallReach.bodyLabels body) :: k,
          SeqReach.focusMemory ccann m₄⟩) _ run
      refine (SeqReach.sseq_pure_reaches ann fann (pat := .mk pann (.base (some p, pbt))) (xs := [(p, fp)])
        (SeqReach.pure_value vann (.loaded (.specified (.pointer (.function g')))) env) rfl k m).trans ?_
      refine (SeqReach.effect_let_reaches lann (cfunction_reaches l1 hinfo) hmatch k m₁).trans ?_
      refine (SeqReach.effect_if_reaches iann true (pureEval_of (length_eval hlen l2)) k m₂).trans ?_
      refine (SeqReach.effect_if_reaches iann' true (compatible_reaches hrk hfk l3) k m₃).trans ?_
      exact CallReach.ccall_reaches ccann mt (SeqReach.pure_symbol pann₂ p₂ env₂ fp l4) .nil
        (CallReach.procedure_not_builtin hdecl) (CallReach.procedure_body hstd hdecl rfl) k m₄
    · cases hs
  · cases hs

/-- A call of a proved effect-free no-parameter void procedure. -/
def direct (file : File Codec.wireModel Unit Unit) (e : EE) : Bool :=
  match callSite file e with
  | some (g, false) => match callee file g false with
    | some none => true
    | _ => false
  | _ => false

theorem direct_runs {e : EE} (h : direct file e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ PureEval.Reaches file labels
      ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold direct at h
  split at h
  · rename_i g hs
    split at h
    · rename_i hc
      exact call_touched hs hc env k m
    · cases h
  · cases h

/-- A plain call, or its discarded-value bound wrapper, is a CFG statement. -/
def recognize (file : File Codec.wireModel Unit Unit) : EE → Bool
  | .mk _ (.bound a) => direct file a
  | e => direct file e

theorem recognize_runs {e : EE} (h : recognize file e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ PureEval.Reaches file labels
      ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold recognize at h
  split at h
  · rename_i ann a
    obtain ⟨m', touch, run⟩ := direct_runs (labels := labels) h env (.bound :: k) m
    exact ⟨m', touch, (ReturnLit.bound_reaches ann a env k m).trans
      (run.trans (LocalExpr.value_bound_reaches .unit k m'))⟩
  · exact direct_runs h env k m

end Silmaril.Compile.Core.Verified.VoidCall
