module

public import Silmaril.Compiler.Core.Verified.StateProcLocal.Defs
public import Silmaril.Compiler.Core.Verified.CallState.Defs
/-! # Complete State-bodied procedure calls in operand arenas -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CallStateArena

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnConst (focusMemory)
open CallArena (sseq_pure effect_let function_info effect_if of_eval compatible ccall_start)

variable {file : Program} {labels : Labels}

theorem reserve_touched {base : Int} {m m' : Mem.Concrete.State} {ls : List StateMem.Local}
    (h : StateProc.Reserve base m ls) (t : LoadTask.Touched m m') :
    StateProc.Reserve base m' ls := by
  obtain ⟨l, u, rfl⟩ := t
  exact ⟨h.dead, h.ids, h.addrs, h.last, h.aligned, h.room⟩

theorem call_prefix {e : EE} {g : Sym} {t : IntExpr.Term}
    (hs : Call.callSite file e = some (g, true)) (hc : CallState.callee file g = some t)
    (env : Env) (m : Mem.Concrete.State) :
    ∃ body env' m', State.recognizeBody file body = some t ∧ m'.stdout = m.stdout ∧ LoadTask.Touched m m' ∧
      libraryCall file g = none ∧ procedureBody file g [] = .ok (body, []) ∧
      LocalReaches file labels false ⟨.effectExpr e env, [], m⟩
        ⟨.apply (.procedure env') [.loaded (.specified (.pointer (.function g)))], [], m'⟩ := by
  obtain ⟨loc, attrs, fty, variadic, proto, dloc, marker, bt, body, hstd, hinfo, hdecl, hfk, hbody⟩ :=
    CallState.callee_spec hc
  unfold Call.callSite at hs
  split at hs
  · rename_i ann pann p pbt fann vann g' lann tann fa fty' fbt pa pty pbt' w1a w1 w2a w2 cann cpann
      p₁ iann oann lenann len lnann pty₁ zann z iann' cpa cva rty cfa fty₁ ccann mt pann₂ p₂ no1 no2
    split at hs
    · rename_i cond
      obtain ⟨hp₁, hp₂, hpty, hfty, hne, hpf, hpp, rfl, hlen⟩ := cond
      have hrk : Call.retKind rty = some true ∧ g' = g := by
        cases h : Call.retKind rty with
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
        Call.lookup_ext2_second hpty (fun h => hne h.symm)
      have l3 : env₂.lookup fty₁ = some (.ctype fty) := Call.lookup_ext2_first hfty
      have l4 : env₂.lookup p₂ = some fp := by
        rw [Call.lookup_ext2_other (by rw [hp₂]; exact hpf) (by rw [hp₂]; exact hpp)]
        exact ConvInt.lookup_one hp₂
      have hmatch : matchPattern (.mk tann (.ctor .tuple [.mk fa (.base (some fty', fbt)),
          .mk pa (.base (some pty, pbt')), .mk w1a (.base (none, w1)), .mk w2a (.base (none, w2))]))
          (.tuple [.ctype fty, .list .ctype (([] : List (Option Sym × Ctype)).map fun q => .ctype q.2),
            boolean variadic, boolean proto]) =
          some [(fty', .ctype fty), (pty, .list .ctype [])] := rfl
      let m₁ := focusMemory fann m
      let m₂ := focusMemory lann m₁
      let m₃ := focusMemory iann m₂
      let m₄ := focusMemory iann' m₃
      refine ⟨body, env₂, focusMemory ccann m₄, hbody, by simp [m₄, m₃, m₂, m₁],
        (LoadTask.focusMemory_touched fann m).trans
          ((LoadTask.focusMemory_touched lann m₁).trans
            ((LoadTask.focusMemory_touched iann m₂).trans
              ((LoadTask.focusMemory_touched iann' m₃).trans
                (LoadTask.focusMemory_touched ccann m₄)))),
        CallReach.procedure_not_builtin hdecl, CallReach.procedure_body hstd hdecl rfl, ?_⟩
      refine (sseq_pure ann fann (pat := .mk pann (.base (some p, pbt))) (xs := [(p, fp)])
        (fun _ => .val) rfl [] m).trans ?_
      refine (effect_let lann (function_info l1 hinfo) hmatch [] m₁).trans ?_
      refine (effect_if iann true (of_eval (Call.length_eval hlen l2)) [] m₂).trans ?_
      refine (effect_if iann' true (compatible hrk hfk l3) [] m₃).trans ?_
      exact ccall_start ccann mt (fun _ => .sym l4) [] m₄
    · cases hs
  · cases hs

/-- All State statements, including UB, execute inside the call's operand task.
The allocation reserve is the only memory precondition beyond the body invariant. -/
theorem call_in_arena {base : Int} {e : EE} {g : Sym} {t : IntExpr.Term}
    (hs : Call.callSite file e = some (g, true)) (hc : CallState.callee file g = some t)
    (env : Env) (m : Mem.Concrete.State) (fresh : StateProc.Reserve base m [])
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩ ∨
    t.Ok 0 ∧ ∃ m', m'.stdout = m.stdout ∧ CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave ((i, IntExpr.spec (t.val 0), []) :: done) [], k, m'⟩ := by
  obtain ⟨body, env', m₁, hbody, out₁, touched, ordinary, resolved, run⟩ :=
    call_prefix (labels := labels) hs hc env m
  have pending : Pending [] i := ⟨by simp, by simp⟩
  have preRun : CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave done [(i, .apply (.procedure env')
        [.loaded (.specified (.pointer (.function g)))], [])], k, m₁⟩ := by
    apply reaches_of_local file labels
    have localRun : LocalReaches file labels (taskFlag false k [])
        ⟨.effectExpr e env, [], m⟩
        ⟨.apply (.procedure env') [.loaded (.specified (.pointer (.function g)))], [], m₁⟩ := by
      simpa [taskFlag] using run
    exact ArenaFail.drive_run file labels pending (done := done) (k := k) (wc := false)
      localRun (fun v h => by cases h)
  have entry := ArenaCall.procedure_enter file labels m₁ done i g [] env' body [] [] k ordinary resolved
  have enter : CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave done [(i, .effectExpr body env', [.procedureReturn (CallReach.bodyLabels body)])], k, m₁⟩ := by
    exact preRun.trans (by simpa [extendEnv, CallReach.bodyLabels] using entry)
  rcases StateProcLocal.body_in_arena (labels := labels) hbody env' m₁
      (reserve_touched fresh touched) done i k with ⟨ok, m', out, bodyrun⟩ | fail
  · exact .inr ⟨ok, m', out.trans out₁, enter.trans bodyrun⟩
  · exact .inl (StateStmt.Overflows.pre enter (ArenaFail.fail_reaches file labels fail))

end Silmaril.Compile.Core.Verified.CallStateArena
