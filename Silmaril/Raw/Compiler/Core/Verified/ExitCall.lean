module

public import Silmaril.Compiler.Core.Verified.Locals.Defs
public import Silmaril.Compiler.Core.Verified.ReturnSound.Defs
public import Silmaril.Cerberus.Core.Interleave.Defs
public import Silmaril.Compiler.Core.Source.StartupMem.Defs

/-! # `main` calling `exit(n)`

Cerberus elaborates the statement `exit(e);` (with `exit` declared `void exit(int)`, no body) to

```
let strong ((f, (r, ps, va, pr)), a) =
  unseq(let strong f' = pure(<exit>) in pure((f', cfunction(f'))), pure(e)) in
if not(params_length(ps) = 1) then undef(UB038) else
if va || not(are_compatible(void, r)) then undef(UB041) else
let strong p =
  { let t = params_nth(ps, 0) in
    if not(are_compatible(int, t)) then undef(UB041) else
    let weak x = create(Ivalignof(int), int) in
    let weak _ = store(int, x, conv_loaded_int(int, a)) in pure(x) } in
let strong _ = ccall(ty, f, [p]) in …
```

`recognize doc = some n` when `main`'s body starts, through sequencing glue (`sseq`, `wseq`, `bound`
on their first operand), with this call, `e` folds to an `int` (`Fold.eval`), and the call's
checks fold to `false` (`params_length`, `params_nth` and `are_compatible` on the callee's static
type, `Fold.eval` with the callee's `cfunction` metadata). This is constant folding of the type
checks and of the argument, not an execution of the program.

The Core side (`recognize_reaches`): the unsequenced pair runs last task first
(`Interleave.unseq_runs`), the checks fold to `false`, the argument object is created and holds
`n` (`Locals.create_reaches`, `Locals.store_reaches`), the call of the C library `exit`
(`Dynamics.libraryCall`) loads it (`Actions.load_apply`) and the builtin `exit` halts with
`Specified n` and unchanged stdout: `CoreBeh doc args (exit (n mod 256) [])`. The code after the
call never runs. `exitCall_reaches` holds in any environment the folder's environment describes,
under any continuation, from any memory with room for one `int` object, so a later fragment can
use it for an `exit` that is not the first statement of `main`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ExitCall

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches)
open ReturnConst (focusMemory focusMemory_stdout)
open Mem.Concrete (LiveInt PlainAt IntRange nextIntAddress)
open Interleave (LocalStep LocalReaches TaskRuns TasksRun Plain)

local notation "rv" => runtimeValue

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-! ## The recogniser -/

/-- `exit` or `_Exit` declared without a body: the C library call the dynamics implements
(`Dynamics.libraryCall`). -/
def isExit (file : Doc) (s : Sym) : Bool :=
  match file.funs.lookup s, s.description with
  | some (.procedureDecl ..), .id "exit" | some (.procedureDecl ..), .id "_Exit" => true
  | _, _ => false

/-- The metadata `cfunction` gives a declared function: return type, parameter types, variadic
and prototype flags. -/
def info (file : Doc) (s : Sym) : Option WVal :=
  match file.funInfo.lookup s with
  | some (_, _, ret, params, variadic, proto) =>
      some (.tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2), boolean variadic,
        boolean proto])
  | none => none

/-- The callee task `let strong f = pure(<exit>) in pure((f, cfunction(f)))`: its value. -/
def calleeTask (file : Doc) : EExp → Option WVal
  | .mk _ (.sseq (.mk _ (.base (some f, _))) (.mk _ (.pure (.mk _ _ (.val w))))
      (.mk _ (.pure (.mk _ _ (.ctor .tuple
        [.mk _ _ (.sym f1), .mk _ _ (.cfunction (.mk _ _ (.sym f2)))]))))) =>
      match w with
      | .loaded (.specified (.pointer (.function x))) =>
          if MapKey.key f1 = MapKey.key f ∧ MapKey.key f2 = MapKey.key f then
            (info file x).map fun i => .tuple [w, i]
          else none
      | _ => none
  | _ => none

mutual
/-- The value of an operator task folding in `env`: `pure(e)`, or
`let weak pat = unseq(t₁, …, tₖ) in pure(e)` over operator tasks `tᵢ` (Cerberus's elaboration of
an operator applied to its operands). -/
def opValue (file : Doc) (env : WEnv) : EExp → Option WVal
  | .mk _ (.pure p) => eval file Return.fuel env p
  | .mk _ (.wseq pat (.mk _ (.unseq es)) (.mk _ (.pure p))) =>
      match opValues file env es with
      | none => none
      | some ws => match matchP pat (.tuple ws) with
        | none => none
        | some xs => eval file Return.fuel (extend xs env) p
  | _ => none

def opValues (file : Doc) (env : WEnv) : List EExp → Option (List WVal)
  | [] => some []
  | e :: es => match opValue file env e, opValues file env es with
    | some w, some ws => some (w :: ws)
    | _, _ => none
end

/-- An integer. -/
def intOf : Option WVal → Option Int
  | some (.loaded (.specified (.integer n))) => some n
  | _ => none

/-- The argument task: an operator task folding to an integer in `env`. -/
def argTask (file : Doc) (env : WEnv) (t : EExp) : Option Int := intOf (opValue file env t)

/-- `c` folds to `false` in `env`. -/
def foldsFalse (file : Doc) (env : WEnv) (c : PExp) : Bool :=
  match eval file Return.fuel env c with
  | some .false => true
  | _ => false

/-- `create(Ivalignof(int), int)`. -/
def isIntCreate : EExp → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.create (.mk _ _ (.ctor .ivAlignof
      [.mk _ _ (.val (.ctype (.mk _ (.basic (.integer (.signed .int))))))]))
      (.mk _ _ (.val (.ctype (.mk _ (.basic (.integer (.signed .int))))))) _)))) => true
  | _ => false

/-- `store(int, x, conv_loaded_int(int, t))`: the object and the value symbols. -/
def intStore (file : Doc) : EExp → Option (Sym × Sym)
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false
      (.mk _ _ (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
      (.mk _ _ (.sym x))
      (.mk _ _ (.call (.sym s) [.mk _ _ (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
        .mk _ _ (.sym t)])) .na)))) =>
      if ConvInt.isConvLoadedInt file s then some (x, t) else none
  | _ => none

/-- The argument object `let t = params_nth(…) in if c then undef else let weak x = create(int) in
let weak _ = store(int, x, conv_loaded_int(int, a)) in pure(x)`: the stored `int`. -/
def argObject (file : Doc) (env : WEnv) : EExp → Option Int
  | .mk _ (.let_ pt nth (.mk _ (.if_ c _ (.mk _ (.wseq (.mk _ (.base (some x, _))) cr
      (.mk _ (.wseq (.mk _ (.base (none, _))) st (.mk _ (.pure (.mk _ _ (.sym x'))))))))))) =>
      match eval file Return.fuel env nth with
      | none => none
      | some w => match matchP pt w with
        | none => none
        | some ys =>
          if foldsFalse file (extend ys env) c ∧ isIntCreate cr ∧ MapKey.key x' = MapKey.key x then
            match intStore file st with
            | none => none
            | some (x3, t) =>
              if MapKey.key x3 = MapKey.key x ∧ MapKey.key t ≠ MapKey.key x then
                match (extend ys env).lookup t with
                | some (.loaded (.specified (.integer n))) =>
                    if -2147483648 ≤ n ∧ n ≤ 2147483647 then some n else none
                | _ => none
              else none
          else none
  | _ => none

/-- `let strong _ = ccall(ty, g, [q]) in _`. -/
def callExit : EExp → Option (Sym × Sym)
  | .mk _ (.sseq _ (.mk _ (.ccall _ _ (.mk _ _ (.sym g)) [.mk _ _ (.sym q)])) _) => some (g, q)
  | _ => none

/-- The call `exit(e)`, run in `env`: the `int` it exits with. -/
def exitCall (file : Doc) (env : WEnv) : EExp → Option Int
  | .mk _ (.sseq pat (.mk _ (.unseq [t0, t1])) (.mk _ (.if_ c1 _ (.mk _ (.if_ c2 _
      (.mk _ (.sseq (.mk _ (.base (some p, _))) args rest))))))) =>
      match calleeTask file t0, argTask file env t1 with
      | some w0, some n =>
        match matchP pat (.tuple [w0, .loaded (.specified (.integer n))]) with
        | none => none
        | some xs =>
          if foldsFalse file (extend xs env) c1 ∧ foldsFalse file (extend xs env) c2 then
            match argObject file (extend xs env) args, callExit rest with
            | some stored, some (g, q) =>
              if MapKey.key q = MapKey.key p ∧ MapKey.key g ≠ MapKey.key p then
                match (extend xs env).lookup g with
                | some (.loaded (.specified (.pointer (.function y)))) =>
                    if isExit file y then some stored else none
                | _ => none
              else none
            | _, _ => none
          else none
      | _, _ => none
  | _ => none

/-- A body whose first effect, through sequencing glue, is `exit(e)`. -/
def recognizeBody (file : Doc) (e : EExp) : Option Int :=
  match exitCall file ∅ e with
  | some n => some n
  | none => match e with
    | .mk _ (.sseq _ a _) => recognizeBody file a
    | .mk _ (.wseq _ a _) => recognizeBody file a
    | .mk _ (.bound a) => recognizeBody file a
    | _ => none

/-- No global definitions, `main` a procedure without parameters whose body is recognised. -/
def recognize (doc : Codec.Document) : Option Int := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-! ## Steps of the dynamics -/

section Steps
variable (file : Program) (labels : Labels)

theorem plain_pureExpr (p : PE) (env : Env) : Plain (.pureExpr p env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_effectExpr (e : EE) (env : Env) : Plain (.effectExpr e env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_value (v : Val) : Plain (.value v) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_apply (op : Prim) (vs : List Val) : Plain (.apply op vs) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- A deterministic step read off `requestAux` at the top level is a step of the Core LTS. -/
theorem lift {c c' : Control} {k k' : List Frame} {m : Mem.Concrete.State}
    (h : requestAux file labels m c k = .next c' k') (hc : Plain c') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m⟩ :=
  Interleave.reaches_of_local file labels (.single (.next h hc))

theorem local_next {wc : Bool} {c c' : Control} {k k' : List Frame} {m : Mem.Concrete.State}
    (h : requestAux file labels m c k wc = .next c' k') (hc : Plain c') :
    LocalReaches file labels wc ⟨c, k, m⟩ ⟨c', k', m⟩ :=
  .single (.next h hc)

variable {wc : Bool} {m : Mem.Concrete.State} {k : List Frame} {env : Env}

theorem ra_sseq (ann : List Annot) (pat : Pattern Sym) (a b : EE) :
    requestAux file labels m (.effectExpr (.mk ann (.sseq pat a b)) env) k wc =
      .next (.effectExpr a env) (.strongBind pat b env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_wseq (ann : List Annot) (pat : Pattern Sym) (a b : EE) :
    requestAux file labels m (.effectExpr (.mk ann (.wseq pat a b)) env) k wc =
      .next (.effectExpr a env) (.effectBind pat b env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_bound (ann : List Annot) (a : EE) :
    requestAux file labels m (.effectExpr (.mk ann (.bound a)) env) k wc =
      .next (.effectExpr a env) (.bound :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_val (ann : List Annot) (u : Unit) (w : Value Codec.wireModel) :
    requestAux file labels m (.pureExpr (.mk ann u (.val w)) env) k wc = .next (.value (rv w)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_sym (ann : List Annot) (u : Unit) {s : Sym} {v : Val} (h : env.lookup s = some v) :
    requestAux file labels m (.pureExpr (.mk ann u (.sym s)) env) k wc = .next (.value v) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, h]

theorem ra_ctor (ann : List Annot) (u : Unit) (c : Ctor) (p : PE) (ps : List PE) :
    requestAux file labels m (.pureExpr (.mk ann u (.ctor c (p :: ps))) env) k wc =
      .next (.pureExpr p env) (.arguments (.ctor c) [] ps env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, arguments]

theorem ra_cfunction (ann : List Annot) (u : Unit) (p : PE) :
    requestAux file labels m (.pureExpr (.mk ann u (.cfunction p)) env) k wc =
      .next (.pureExpr p env) (.arguments .functionInfo [] [] env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, arguments]

theorem ra_args_cons (v : Val) (op : Prim) (vs : List Val) (p : PE) (ps : List PE) :
    requestAux file labels m (.value v) (.arguments op vs (p :: ps) env :: k) wc =
      .next (.pureExpr p env) (.arguments op (vs ++ [v]) ps env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_args_nil (v : Val) (op : Prim) (vs : List Val) :
    requestAux file labels m (.value v) (.arguments op vs [] env :: k) wc =
      .next (.apply op (vs ++ [v])) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_functionInfo {s : Sym} {l : Loc} {at_ : Attributes} {ret : Ctype}
    {params : List (Option Sym × Ctype)} {va pr : Bool}
    (h : file.funInfo.lookup s = some (l, at_, ret, params, va, pr)) :
    requestAux file labels m (.apply .functionInfo [.loaded (.specified (.pointer (.function s)))]) k wc =
      .next (.value (.tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2),
        Dynamics.boolean va, Dynamics.boolean pr])) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, h]

theorem ra_tuple (vs : List Val) :
    requestAux file labels m (.apply (.ctor .tuple) vs) k wc = .next (.value (.tuple vs)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, primitive]; rfl

theorem ra_strongBind {v : Val} {pat : Pattern Sym} {xs : Bindings} (h : matchPattern pat v = some xs)
    (b : EE) (benv : Env) :
    requestAux file labels m (.value v) (.strongBind pat b benv :: k) wc =
      .next (.effectExpr b (extendEnv xs benv)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, h]

theorem ra_effectBind {v : Val} {pat : Pattern Sym} {xs : Bindings} (h : matchPattern pat v = some xs)
    (b : EE) (benv : Env) :
    requestAux file labels m (.value v) (.effectBind pat b benv :: k) wc =
      .next (.effectExpr b (extendEnv xs benv)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, h]

theorem ra_if_false (yes no : EE) (benv : Env) :
    requestAux file labels m (.value .false) (.effectIf yes no benv :: k) wc =
      .next (.effectExpr no benv) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_diagnostic (v : Val) (l : Loc) :
    requestAux file labels m (.value v) (.diagnosticLocation l :: k) wc = .next (.value v) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- A value over an annotation frame continues as below it, keeping the frame. -/
theorem ra_annotations {v : Val} {xs : List Access} {f : Frame} {c' : Control} {k' : List Frame}
    (hf : ∀ ys, f ≠ .annotations ys) (hb : f ≠ .bound)
    (h : ∀ wc', requestAux file labels m (.value v) (f :: k) wc' = .next c' k') :
    requestAux file labels m (.value v) (.annotations xs :: f :: k) wc =
      .next c' (.annotations xs :: k') := by
  rw [requestAux.eq_def]
  cases f
  case annotations ys => exact absurd rfl (hf ys)
  case bound => exact absurd rfl hb
  all_goals simp [awaitsScheduling, h]

theorem ra_exit {outer : Env} {y : Sym} (hy : libraryCall file y = some .exit) (p : Val) :
    requestAux file labels m (.apply (.procedure outer) [.loaded (.specified (.pointer (.function y))), p]) k =
      .scheduled [(.apply (.memory .load) [.ctype (Ctype.mk [] (.basic (.integer (.signed .int)))), p],
        .arguments (.builtin "exit") [] [] ∅ :: k)] := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, hy, scheduledRequest]

theorem ra_builtin_exit (v : Val) :
    requestAux file labels m (.apply (.builtin "exit") [v]) k =
      .scheduled [(.raise (.defined v), [])] := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, scheduledRequest]

theorem ra_raise (o : Outcome) : requestAux file labels m (.raise o) k = .end_ o := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- A step the dynamics schedules (a call or a builtin), with a single choice. -/
theorem scheduled_reaches {c c' : Control} {k' : List Frame}
    (h : requestAux file labels m c k = .scheduled [(c', k')]) (live : ∀ o, c ≠ .halt o) :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.tau, Step.respond live ?_⟩
  have : request file labels ⟨c, k, m⟩ = .scheduled [(c', k')] := by
    unfold request; simp only [h]
  rw [this]
  exact Respond.scheduled (by simp)

theorem end_reaches {c : Control} {o : Outcome} (h : requestAux file labels m c k = .end_ o)
    (live : ∀ o, c ≠ .halt o) : Reaches file labels ⟨c, k, m⟩ ⟨.halt o, [], m⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.terminal o, Step.respond live ?_⟩
  have : request file labels ⟨c, k, m⟩ = .end_ o := by
    unfold request; simp only [h]
  rw [this]
  exact Respond.end_

theorem request_if {ann : List Annot} {p : PE} {yes no : EE} :
    request file labels ⟨.effectExpr (.mk ann (.if_ p yes no)) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.effectIf yes no env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectIf yes no env :: k) := by
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.effectIf yes no env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectIf yes no env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem request_let {ann : List Annot} {pat : Pattern Sym} {p : PE} {b : EE} :
    request file labels ⟨.effectExpr (.mk ann (.let_ pat p b)) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.effectBind pat b env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectBind pat b env :: k) := by
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.effectBind pat b env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectBind pat b env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem request_ccall {ann : List Annot} {u : Unit} {ty p : PE} {ps : List PE} :
    request file labels ⟨.effectExpr (.mk ann (.ccall u ty p ps)) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.arguments (.procedure env) [] ps env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.arguments (.procedure env) [] ps env :: k) := by
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.arguments (.procedure env) [] ps env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.arguments (.procedure env) [] ps env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

/-- `pure(p)` over any frames: the focus, then `p` above a diagnostic frame. -/
theorem pure_local (annots : List Annot) (p : PE) :
    ∃ l, LocalReaches file labels wc ⟨.effectExpr (.mk annots (.pure p)) env, k, m⟩
      ⟨.pureExpr p env, .diagnosticLocation m.currentLocation :: k, {m with currentLocation := l}⟩ := by
  have hr : ∃ l, requestAux file labels m (.effectExpr (.mk annots (.pure p)) env) k wc =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.diagnosticLocation m.currentLocation :: k)
      else .next (.setLocation l (.pureExpr p env)) (.diagnosticLocation m.currentLocation :: k) := by
    rw [requestAux.eq_def]
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true]
    split
    · split
      · exact ⟨m.currentLocation, by simp⟩
      · exact ⟨_, rfl⟩
    · exact ⟨m.currentLocation, by simp⟩
  obtain ⟨l, hr⟩ := hr
  by_cases hl : (({m with currentLocation := l} : Mem.Concrete.State).currentLocation ==
      m.currentLocation) = true
  · simp only [hl, ↓reduceIte] at hr
    exact ⟨m.currentLocation, .single (.next hr (plain_pureExpr p env))⟩
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr
    exact ⟨l, .head (.next hr ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
      (.single (.update (Interleave.requestAux_setLocation file labels m l _ _ wc)))⟩

end Steps

/-! ## Inversions of the recogniser -/

section Inversions
variable {file : Program}

theorem calleeTask_inv {t : EExp} {w : WVal} (h : calleeTask file t = some w) :
    ∃ a0 pa f bt a1 a2 u2 x a3 a4 u4 a5 u5 f1 a6 u6 a7 u7 f2 i,
      t = .mk a0 (.sseq (.mk pa (.base (some f, bt)))
        (.mk a1 (.pure (.mk a2 u2 (.val (.loaded (.specified (.pointer (.function x))))))))
        (.mk a3 (.pure (.mk a4 u4 (.ctor .tuple
          [.mk a5 u5 (.sym f1), .mk a6 u6 (.cfunction (.mk a7 u7 (.sym f2)))]))))) ∧
      MapKey.key f1 = MapKey.key f ∧ MapKey.key f2 = MapKey.key f ∧ info file x = some i ∧
      w = .tuple [.loaded (.specified (.pointer (.function x))), i] := by
  unfold calleeTask at h
  split at h
  · split at h
    · split at h
      · rename_i hk
        obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hk.1, hk.2, hi, rfl⟩
      · cases h
    · cases h
  · cases h

theorem info_inv {x : Sym} {i : WVal} (h : info file x = some i) :
    ∃ l at_ ret params va pr, file.funInfo.lookup x = some (l, at_, ret, params, va, pr) ∧
      i = .tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2), boolean va,
        boolean pr] := by
  unfold info at h
  split at h
  · rename_i hl
    cases h
    exact ⟨_, _, _, _, _, _, hl, rfl⟩
  · cases h

theorem opValue_inv {env : WEnv} {e : EExp} {w : WVal} (h : opValue file env e = some w) :
    (∃ a p, e = .mk a (.pure p) ∧ eval file Return.fuel env p = some w) ∨
    (∃ a pat a1 es a2 p ws xs, e = .mk a (.wseq pat (.mk a1 (.unseq es)) (.mk a2 (.pure p))) ∧
      opValues file env es = some ws ∧ matchP pat (.tuple ws) = some xs ∧
      eval file Return.fuel (extend xs env) p = some w) := by
  unfold opValue at h
  split at h
  · exact .inl ⟨_, _, rfl, h⟩
  · split at h
    · cases h
    · rename_i ws hws
      split at h
      · cases h
      · rename_i xs hxs
        exact .inr ⟨_, _, _, _, _, _, _, _, rfl, hws, hxs, h⟩
  · cases h

theorem opValues_cons {env : WEnv} {e : EExp} {es : List EExp} {ws : List WVal}
    (h : opValues file env (e :: es) = some ws) :
    ∃ w ws', opValue file env e = some w ∧ opValues file env es = some ws' ∧ ws = w :: ws' := by
  unfold opValues at h
  split at h
  · rename_i w ws' hw hws
    cases h
    exact ⟨w, ws', hw, hws, rfl⟩
  · cases h

theorem opValues_mem {env : WEnv} : ∀ {es : List EExp} {ws : List WVal},
    opValues file env es = some ws → ∀ e ∈ es, ∃ w, opValue file env e = some w
  | [], _, _, e, he => by cases he
  | e :: es, ws, h, e', he' => by
    obtain ⟨w, ws', hw, hes, rfl⟩ := opValues_cons h
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨w, hw⟩
    · exact opValues_mem hes e' he'

theorem argTask_eq {env : WEnv} {t : EExp} {n : Int} (h : argTask file env t = some n) :
    opValue file env t = some (.loaded (.specified (.integer n))) := by
  unfold argTask intOf at h
  split at h
  · cases h; assumption
  · cases h

theorem foldsFalse_eval {env : WEnv} {c : PExp} (h : foldsFalse file env c = true) :
    eval file Return.fuel env c = some .false := by
  unfold foldsFalse at h
  split at h
  · assumption
  · cases h

theorem isIntCreate_inv {e : EExp} (h : isIntCreate e = true) :
    ∃ ann l u a1 a2 c1 a3 c2 pref,
      e = .mk ann (.action (.mk .pos (.mk l u (.create (.mk a1 () (.ctor .ivAlignof
        [Locals.intVal a2 c1])) (Locals.intVal a3 c2) pref)))) := by
  unfold isIntCreate at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem intStore_inv {e : EExp} {x t : Sym} (h : intStore file e = some (x, t)) :
    ∃ ann l u a1 c1 a2 a3 s a4 c3 a5,
      e = .mk ann (.action (.mk .pos (.mk l u (.store false (Locals.intVal a1 c1) (.mk a2 () (.sym x))
        (.mk a3 () (.call (.sym s) [Locals.intVal a4 c3, .mk a5 () (.sym t)])) .na)))) ∧
      ConvInt.isConvLoadedInt file s = true := by
  unfold intStore at h
  split at h
  · split at h
    · rename_i hs
      cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, hs⟩
    · cases h
  · cases h

theorem callExit_inv {e : EExp} {g q : Sym} (h : callExit e = some (g, q)) :
    ∃ a0 pat a1 u ty a2 u2 a3 u3 after,
      e = .mk a0 (.sseq pat (.mk a1 (.ccall u ty (.mk a2 u2 (.sym g)) [.mk a3 u3 (.sym q)])) after) := by
  unfold callExit at h
  split at h
  · cases h
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem argObject_inv {env : WEnv} {e : EExp} {n : Int} (h : argObject file env e = some n) :
    ∃ a0 pt nth a1 c u a2 px x bx cr a3 pn bn st a4 a5 u5 x' w ys x3 t,
      e = .mk a0 (.let_ pt nth (.mk a1 (.if_ c u (.mk a2 (.wseq (.mk px (.base (some x, bx))) cr
        (.mk a3 (.wseq (.mk pn (.base (none, bn))) st
          (.mk a4 (.pure (.mk a5 u5 (.sym x'))))))))))) ∧
      eval file Return.fuel env nth = some w ∧ matchP pt w = some ys ∧
      foldsFalse file (extend ys env) c = true ∧ isIntCreate cr = true ∧
      MapKey.key x' = MapKey.key x ∧ intStore file st = some (x3, t) ∧
      MapKey.key x3 = MapKey.key x ∧ MapKey.key t ≠ MapKey.key x ∧
      (extend ys env).lookup t = some (.loaded (.specified (.integer n))) ∧ IntRange n := by
  unfold argObject at h
  split at h
  · split at h
    · cases h
    · rename_i w hw
      split at h
      · cases h
      · rename_i ys hys
        split at h
        · rename_i hc
          split at h
          · cases h
          · rename_i x3 t hst
            split at h
            · rename_i hk
              split at h
              · rename_i n' hl
                split at h
                · rename_i hr
                  cases h
                  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
                    hw, hys, hc.1, hc.2.1, hc.2.2, hst, hk.1, hk.2, hl, hr⟩
                · cases h
              · cases h
            · cases h
        · cases h
  · cases h

theorem exitCall_inv {env : WEnv} {e : EExp} {n : Int} (h : exitCall file env e = some n) :
    ∃ a0 pat a1 t0 t1 a2 c1 u1 a3 c2 u2 a4 pp p bp args rest w0 na xs g q y,
      e = .mk a0 (.sseq pat (.mk a1 (.unseq [t0, t1])) (.mk a2 (.if_ c1 u1 (.mk a3 (.if_ c2 u2
        (.mk a4 (.sseq (.mk pp (.base (some p, bp))) args rest))))))) ∧
      calleeTask file t0 = some w0 ∧ argTask file env t1 = some na ∧
      matchP pat (.tuple [w0, .loaded (.specified (.integer na))]) = some xs ∧
      foldsFalse file (extend xs env) c1 = true ∧ foldsFalse file (extend xs env) c2 = true ∧
      argObject file (extend xs env) args = some n ∧ callExit rest = some (g, q) ∧
      MapKey.key q = MapKey.key p ∧ MapKey.key g ≠ MapKey.key p ∧
      (extend xs env).lookup g = some (.loaded (.specified (.pointer (.function y)))) ∧
      isExit file y = true := by
  unfold exitCall at h
  split at h
  · split at h
    · rename_i w0 na h0 h1
      split at h
      · cases h
      · rename_i xs hxs
        split at h
        · rename_i hc
          split at h
          · rename_i stored g q ho hce
            split at h
            · rename_i hk
              split at h
              · rename_i y hl
                split at h
                · rename_i hy
                  cases h
                  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
                    h0, h1, hxs, hc.1, hc.2, ho, hce, hk.1, hk.2, hl, hy⟩
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
    · cases h
  · cases h

theorem libraryCall_of_isExit {s : Sym} (h : isExit file s = true) : libraryCall file s = some .exit := by
  unfold isExit at h
  unfold libraryCall
  split at h <;> simp_all

end Inversions

/-! ## The unsequenced callee and argument -/

section Tasks
variable (file : Program) (labels : Labels)

theorem rv_info (ret : Ctype) (params : List (Option Sym × Ctype)) (va pr : Bool) :
    rv (.tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2), Fold.boolean va,
      Fold.boolean pr]) =
      .tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2), Dynamics.boolean va,
        Dynamics.boolean pr] := by
  have hl : runtimeValues (params.map fun p => (Value.ctype p.2 : WVal)) =
      params.map fun p => .ctype p.2 := by
    induction params with
    | nil => rfl
    | cons q qs ih => simp [runtimeValues, runtimeValue, ih]
  cases va <;> cases pr <;> simp [runtimeValue, runtimeValues, hl, Fold.boolean, Dynamics.boolean]

theorem lookup_bind {α : Type} {m : Map Sym α} {a b : Sym} (v : α) (h : MapKey.key a = MapKey.key b) :
    (m.insert b v).lookup a = some v := by
  rw [ReturnLit.lookup_key h]; exact Map.lookup_insert b v m

/-- **The callee task runs** to the callee and its `cfunction` metadata, reading nothing. -/
theorem calleeTask_runs {t : EExp} {w : WVal} (h : calleeTask file t = some w) (env : Env)
    (m : Mem.Concrete.State) :
    ∃ l, TaskRuns file labels false ⟨.effectExpr t env, [], m⟩ (rv w) [] {m with currentLocation := l} := by
  obtain ⟨a0, pa, f, bt, a1, a2, u2, x, a3, a4, u4, a5, u5, f1, a6, u6, a7, u7, f2, i, rfl, h1, h2,
    hi, rfl⟩ := calleeTask_inv h
  obtain ⟨l0, at0, ret, params, va, pr, hlook, rfl⟩ := info_inv hi
  let fv : Val := .loaded (.specified (.pointer (.function x)))
  let env1 : Env := env.insert f fv
  have hf1 : env1.lookup f1 = some fv := lookup_bind fv h1
  have hf2 : env1.lookup f2 = some fv := lookup_bind fv h2
  let tup : PE := .mk a4 u4 (.ctor .tuple [.mk a5 u5 (.sym f1), .mk a6 u6 (.cfunction (.mk a7 u7 (.sym f2)))])
  obtain ⟨l1, r2⟩ := pure_local file labels (wc := false) (env := env)
    (k := [.strongBind (.mk pa (.base (some f, bt))) (.mk a3 (.pure tup)) env]) (m := m) a1
    (.mk a2 u2 (.val (.loaded (.specified (.pointer (.function x))))))
  obtain ⟨l2, r6⟩ := pure_local file labels (wc := false) (env := env1) (k := [])
    (m := {m with currentLocation := l1}) a3 tup
  refine ⟨l2, [], ?_, rfl⟩
  refine .head (.next (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)) ?_
  refine r2.trans ?_
  refine .head (.next (ra_val file labels _ _ _) (plain_value _)) ?_
  refine .head (.next (ra_diagnostic file labels _ _) (plain_value _)) ?_
  refine .head (.next (ra_strongBind file labels (xs := [(f, fv)]) (by simp [matchPattern]; rfl) _ _)
    (plain_effectExpr _ _)) ?_
  refine r6.trans ?_
  refine .head (.next (ra_ctor file labels _ _ _ _ _) (plain_pureExpr _ _)) ?_
  refine .head (.next (ra_sym file labels _ _ hf1) (plain_value _)) ?_
  refine .head (.next (ra_args_cons file labels _ _ _ _ _) (plain_pureExpr _ _)) ?_
  refine .head (.next (ra_cfunction file labels _ _ _) (plain_pureExpr _ _)) ?_
  refine .head (.next (ra_sym file labels _ _ hf2) (plain_value _)) ?_
  refine .head (.next (ra_args_nil file labels _ _ _) (plain_apply _ _)) ?_
  refine .head (.next (ra_functionInfo file labels hlook) (plain_value _)) ?_
  refine .head (.next (ra_args_nil file labels _ _ _) (plain_apply _ _)) ?_
  refine .head (.next (ra_tuple file labels _) (plain_value _)) ?_
  refine .head (.next (ra_diagnostic file labels _ _) (plain_value _)) ?_
  rw [show rv (.tuple [.loaded (.specified (.pointer (.function x))),
      .tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2), Fold.boolean va,
        Fold.boolean pr]]) =
    .tuple [fv, rv (.tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2), Fold.boolean va,
      Fold.boolean pr])] from rfl, rv_info]
  exact .refl

/-- From a value above a diagnostic and an annotation frame, the Core LTS only drops the frames
and halts. -/
theorem diagnostic2_reaches {v : Val} {l : Loc} {xs : List Access} {m : Mem.Concrete.State}
    {t : State}
    (h : Interleave.CoreReaches file labels ⟨.value v, [.diagnosticLocation l, .annotations xs], m⟩ t) :
    t = ⟨.value v, [.diagnosticLocation l, .annotations xs], m⟩ ∨
      t.stack ≠ [.diagnosticLocation l, .annotations xs] := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl rfl
  | head step rest =>
    rw [Interleave.lts_of_next file labels
      (Interleave.requestAux_value_diagnostic file labels m v l _ false)
      (fun _ _ _ h => nomatch h) step.choose_spec] at rest
    cases rest using Relation.ReflTransGen.head_induction_on with
    | refl => exact .inr (by simp)
    | head step' rest' =>
      rw [Interleave.lts_of_end file labels
        (Interleave.requestAux_value_annotations file labels m v xs false) step'.choose_spec] at rest'
      rw [Interleave.halt_reaches file labels rest']
      exact .inr (by simp)

/-- `Interleave.pure_bridge` above a diagnostic and an annotation frame: a run of the Core LTS from
a pure state to a value there is a run of local steps. -/
theorem pure_bridge2 {c : Control} {k : List Frame} {l : Loc} {xs : List Access}
    {m m' : Mem.Concrete.State} {v : Val} (hc : Interleave.PureControl c = true)
    (hk : Interleave.PureAbove [.diagnosticLocation l, .annotations xs] k)
    (h : Interleave.CoreReaches file labels ⟨c, k, m⟩
      ⟨.value v, [.diagnosticLocation l, .annotations xs], m'⟩) :
    LocalReaches file labels false ⟨c, k, m⟩
      ⟨.value v, [.diagnosticLocation l, .annotations xs], m'⟩ := by
  suffices ∀ s, Interleave.CoreReaches file labels s
      ⟨.value v, [.diagnosticLocation l, .annotations xs], m'⟩ →
      Interleave.PureControl s.control = true →
      Interleave.PureAbove [.diagnosticLocation l, .annotations xs] s.stack →
      LocalReaches file labels false s ⟨.value v, [.diagnosticLocation l, .annotations xs], m'⟩ from
    this _ h hc hk
  intro s hs
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ _; exact .refl
  | head step rest ih =>
    rename_i s s'
    intro hc hk
    obtain ⟨cs, ks, ms⟩ := s
    simp only at hc hk
    by_cases hend : ∃ v0, cs = .value v0 ∧ ks = [.diagnosticLocation l, .annotations xs]
    · obtain ⟨v0, rfl, rfl⟩ := hend
      rcases diagnostic2_reaches file labels (.head step rest) with heq | hne
      · rw [heq]
      · exact absurd rfl hne
    · have hne : ∀ v0, cs = .value v0 → ks ≠ [.diagnosticLocation l, .annotations xs] :=
        fun v0 hv hks => hend ⟨v0, hv, hks⟩
      have hres := Interleave.pure_result file labels hc hk hne ms false
      revert hres
      cases hr : requestAux file labels ms cs ks false <;>
        simp only [Interleave.PureResult, IsEmpty.forall_iff]
      case next c' k' =>
        rintro ⟨hc', hk'⟩
        have hj : ∀ s vs env, c' ≠ .jumping s vs env := by
          rintro s vs env rfl; simp [Interleave.PureControl] at hc'
        have hs' := Interleave.lts_of_next file labels hr hj step.choose_spec
        subst hs'
        exact .head (.next hr ⟨fun o h => by subst h; simp [Interleave.PureControl] at hc', hj⟩)
          (ih hc' hk')
      case end_ o =>
        intro _
        have hs' := Interleave.lts_of_end file labels hr step.choose_spec
        subst hs'
        have := Interleave.halt_reaches file labels rest
        cases this

/-- Tasks that each run to a fixed value, changing only the current location, run in an arena
under flag `false`. -/
theorem tasksRun_reloc {k : List Frame} {env : Env} (val : EE → Val) (es : List EE)
    (h : ∀ e ∈ es, ∀ m : Mem.Concrete.State, ∃ l,
      TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ (val e) [] {m with currentLocation := l})
    (calls : ∀ e ∈ es, hasCCall e = false) (m : Mem.Concrete.State) :
    ∃ l, TasksRun file labels false k (Interleave.unseqTasks es env) m
      (Interleave.pureResults val es) {m with currentLocation := l} := by
  induction es using List.reverseRecOn generalizing m with
  | nil => exact ⟨m.currentLocation, .nil⟩
  | append_singleton es e ih =>
    obtain ⟨l1, run⟩ := h e (by simp) m
    obtain ⟨l2, rest⟩ := ih (fun e' he' => h e' (by simp [he']))
      (fun e' he' => calls e' (by simp [he'])) {m with currentLocation := l1}
    refine ⟨l2, ?_⟩
    rw [Interleave.unseqTasks_snoc, show Interleave.pureResults val (es ++ [e]) =
      Interleave.pureResults val es ++ [(es.length, val e, [])] by
        simp [Interleave.pureResults, List.zipIdx_append]]
    have hflag := Interleave.taskFlag_unseq (k := k) (env := env) (es := es ++ [e]) calls
      (List.prefix_append es [e])
    exact .snoc (by rw [hflag]; exact run) rest

/-- The value of an operator task, as a function of the task. -/
def opVal (file : Program) (env : WEnv) (e : EE) : Val := ((opValue file env e).map rv).getD .unit

theorem opValues_values {fenv : WEnv} : ∀ {es : List EExp} {ws : List WVal},
    opValues file fenv es = some ws → es.map (opVal file fenv) = ws.map rv
  | [], ws, h => by cases h; rfl
  | e :: es, ws, h => by
    obtain ⟨w, ws', hw, hes, rfl⟩ := opValues_cons h
    simp [opVal, hw, opValues_values hes]

/-- An unsequenced expression of tasks that each run to a fixed value, changing only the current
location and holding no call, reaches the tuple of their values by local steps. -/
theorem unseq_tasks_local {env : Env} {es : List EExp} (val : EE → Val)
    (h : ∀ e ∈ es, ∀ m : Mem.Concrete.State, ∃ l,
      TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ (val e) [] {m with currentLocation := l})
    (calls : ∀ e ∈ es, hasCCall e = false) (annots : List Annot) (k : List Frame)
    (m : Mem.Concrete.State) :
    ∃ l, LocalReaches file labels false ⟨.effectExpr (.mk annots (.unseq es)) env, k, m⟩
      ⟨.value (.tuple (es.map val)), .annotations [] :: k, {m with currentLocation := l}⟩ := by
  obtain ⟨l, run⟩ := tasksRun_reloc file labels (k := k) (env := env) val es h calls m
  have reads : ∀ x ∈ Interleave.pureResults val es, ∀ a ∈ x.2.2, a.write = false := by
    intro x hx a ha
    simp only [Interleave.pureResults, List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    cases ha
  have hv : (Interleave.pureResults val es).map (·.2.1) = es.map val := by
    simp only [Interleave.pureResults, List.map_map]
    rw [show ((·.2.1) ∘ fun p : EE × Nat => (p.2, val p.1, ([] : List Access))) = val ∘ Prod.fst
      from rfl, ← List.map_map, List.zipIdx_map_fst]
  have ha : (Interleave.pureResults val es).flatMap (·.2.2) = [] := by
    simp [Interleave.pureResults]
  refine ⟨l, ?_⟩
  simpa [hv, ha] using Interleave.unseq_runs file labels (annots := annots) run reads

/-- Operator tasks hold no call. -/
theorem opValue_noCall {fenv : WEnv} : (e : EExp) → ∀ {w : WVal}, opValue file fenv e = some w →
    hasCCall e = false
  | e, w, h => by
    rcases opValue_inv h with ⟨a, p, rfl, -⟩ | ⟨a, pat, a1, es, a2, p, ws, xs, he, hws, -⟩
    · simp [hasCCall]
    · have hall : ∀ e' ∈ es, hasCCall e' = false := fun e' he' => by
        have hlt : sizeOf e' < sizeOf e := by
          have := List.sizeOf_lt_of_mem he'
          rw [he]; simp only [Expr.mk.sizeOf_spec, ExprNode.wseq.sizeOf_spec, ExprNode.unseq.sizeOf_spec]; omega
        obtain ⟨w', hw'⟩ := opValues_mem hws e' he'
        exact opValue_noCall e' hw'
      rw [he]
      simp only [hasCCall, Bool.or_false, List.any_eq_false]
      intro e' he'
      simpa using hall e'.1 e'.2
termination_by e => sizeOf e
decreasing_by omega

/-- **An operator task runs** to its folded value, changing only the current location. -/
theorem opValue_runs {fenv : WEnv} {env : Env} (hr : EnvRel fenv env) : (e : EExp) → ∀ {w : WVal},
    opValue file fenv e = some w → ∀ m : Mem.Concrete.State,
    ∃ l, TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ (rv w) [] {m with currentLocation := l}
  | e, w, h, m => by
    rcases opValue_inv h with ⟨a, p, rfl, hp⟩ | ⟨a, pat, a1, es, a2, p, ws, xs, he, hws, hxs, hp⟩
    · exact Interleave.pure_task_of_reaches file labels
        (fun k m' => eval_reaches file labels Return.fuel fenv p _ hp env hr k m')
    have hrun : ∀ e' ∈ es, ∀ m : Mem.Concrete.State, ∃ l, TaskRuns file labels false
        ⟨.effectExpr e' env, [], m⟩ (opVal file fenv e') [] {m with currentLocation := l} := by
      intro e' he' m
      have hlt : sizeOf e' < sizeOf e := by
        have := List.sizeOf_lt_of_mem he'
        rw [he]; simp only [Expr.mk.sizeOf_spec, ExprNode.wseq.sizeOf_spec, ExprNode.unseq.sizeOf_spec]; omega
      obtain ⟨w', hw'⟩ := opValues_mem hws e' he'
      obtain ⟨l, r⟩ := opValue_runs hr e' hw' m
      exact ⟨l, by simpa [opVal, hw'] using r⟩
    rw [he]
    obtain ⟨l1, ru⟩ := unseq_tasks_local file labels (opVal file fenv) hrun
      (fun e' he' => by
        obtain ⟨w', hw'⟩ := opValues_mem hws e' he'; exact opValue_noCall file e' hw')
      a1 [.effectBind pat (.mk a2 (.pure p)) env] m
    rw [opValues_values file hws] at ru
    have hm : matchPattern pat (.tuple (ws.map rv)) = some (bmap xs) := by
      rw [← runtimeValues_eq, show (Value.tuple (runtimeValues ws) : Val) = rv (.tuple ws) from rfl,
        matchP_rv, hxs]; rfl
    have hr' : EnvRel (extend xs fenv) (extendEnv (bmap xs) env) := hr.extend xs
    obtain ⟨l2, rp⟩ := pure_local file labels (wc := false) (env := extendEnv (bmap xs) env)
      (k := [.annotations []]) (m := {m with currentLocation := l1}) a2 p
    refine ⟨l2, [.annotations []], ?_, rfl⟩
    refine .head (.next (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)) ?_
    refine ru.trans ?_
    refine .head (.next (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
      (fun _ => ra_effectBind file labels hm _ _)) (plain_effectExpr _ _)) ?_
    refine rp.trans ?_
    refine (pure_bridge2 file labels rfl .base
      (eval_reaches file labels Return.fuel _ p _ hp _ hr' _ _)).trans ?_
    exact .single (.next (ra_diagnostic file labels _ _) (plain_value _))
termination_by e => sizeOf e
decreasing_by omega

/-- **The argument task runs** to its folded value. -/
theorem argTask_runs {fenv : WEnv} {env : Env} (hr : EnvRel fenv env) {t : EExp} {n : Int}
    (h : argTask file fenv t = some n) (m : Mem.Concrete.State) :
    ∃ l, TaskRuns file labels false ⟨.effectExpr t env, [], m⟩ (.loaded (.specified (.integer n))) []
      {m with currentLocation := l} :=
  opValue_runs file labels hr t (argTask_eq h) m

theorem calleeTask_noCall {t : EExp} {w : WVal} (h : calleeTask file t = some w) :
    hasCCall t = false := by
  obtain ⟨a0, pa, f, bt, a1, a2, u2, x, a3, a4, u4, a5, u5, f1, a6, u6, a7, u7, f2, i, rfl, -⟩ :=
    calleeTask_inv h
  simp [hasCCall]

/-- **The unsequenced callee and argument** reach the tuple of their values, callee first. -/
theorem call_unseq {fenv : WEnv} {env : Env} (hr : EnvRel fenv env) {t0 t1 : EExp} {w0 : WVal}
    {n : Int} (h0 : calleeTask file t0 = some w0) (h1 : argTask file fenv t1 = some n) (a : List Annot)
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l, Reaches file labels ⟨.effectExpr (.mk a (.unseq [t0, t1])) env, k, m⟩
      ⟨.value (.tuple [rv w0, .loaded (.specified (.integer n))]), .annotations [] :: k,
        {m with currentLocation := l}⟩ := by
  obtain ⟨l1, r1⟩ := argTask_runs file labels hr h1 m
  obtain ⟨l0, r0⟩ := calleeTask_runs file labels h0 env {m with currentLocation := l1}
  have flag1 : Interleave.taskFlag false k ([] ++ [(0, .effectExpr t0 env, [])]) = false := by
    simp [Interleave.taskFlag, Interleave.controlHasCCall_effectExpr, calleeTask_noCall file h0]
  have flag0 : Interleave.taskFlag false k [] = false := by simp [Interleave.taskFlag]
  have run : TasksRun file labels false k (([] ++ [(0, .effectExpr t0 env, [])]) ++ [(1, .effectExpr t1 env, [])])
      m (([] ++ [(0, rv w0, [])]) ++ [(1, .loaded (.specified (.integer n)), [])])
      {m with currentLocation := l0} :=
    .snoc (flag1 ▸ r1) (.snoc (flag0 ▸ r0) .nil)
  have hl := Interleave.unseq_runs file labels (annots := a) (es := [t0, t1]) (env := env) run
    (by intro x hx b hb; simp at hx; rcases hx with rfl | rfl <;> simp at hb)
  exact ⟨l0, Interleave.reaches_of_local file labels (by simpa using hl)⟩

end Tasks

/-! ## The call -/

section Call
variable (file : Program) (labels : Labels)

/-- What the `create` of the argument object needs: room below the last allocation and a fresh
identifier. -/
structure Budget (m : Mem.Concrete.State) : Prop where
  room : 0 < nextIntAddress m
  fresh : m.nextId ∉ m.dead

theorem Budget.reloc {m : Mem.Concrete.State} (h : Budget m) (l : Loc) :
    Budget {m with currentLocation := l} := ⟨h.room, h.fresh⟩

theorem Budget.focus {m : Mem.Concrete.State} (h : Budget m) (ann : List Annot) :
    Budget (focusMemory ann m) := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]; exact h.reloc l

/-- An effectful `if` whose condition folds to `false` runs its `else` branch. -/
theorem if_false_reaches {fenv : WEnv} {env : Env} (hr : EnvRel fenv env) {ann : List Annot}
    {c : PExp} {yes no : EE} (hc : foldsFalse file fenv c = true) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.if_ c yes no)) env, k, m⟩
      ⟨.effectExpr no env, k, focusMemory ann m⟩ :=
  (Straight.focus_reaches (request_if file labels)).trans
    ((eval_reaches file labels Return.fuel fenv c _ (foldsFalse_eval hc) env hr _ _).trans
      (lift file labels (ra_if_false file labels _ _ _) (plain_effectExpr _ _)))

/-- **The argument object** of `exit` is created and holds the stored `int`. -/
theorem argObject_reaches {fenv : WEnv} {env : Env} (hr : EnvRel fenv env) {e : EExp} {n : Int}
    (h : argObject file fenv e = some n) (k : List Frame) (m : Mem.Concrete.State) (hb : Budget m) :
    ∃ id addr xs m', Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated id addr))), .annotations xs :: k, m'⟩ ∧
      Locals.Slot m' id addr n ∧ IntRange n ∧ m'.stdout = m.stdout := by
  obtain ⟨a0, pt, nth, a1, c, u, a2, px, x, bx, cr, a3, pn, bn, st, a4, a5, u5, x', w, ys, x3, t,
    rfl, hw, hys, hc, hcr, hx', hst, hx3, hlt, hlook, hrange⟩ := argObject_inv h
  obtain ⟨ann, l, uu, b1, b2, cc1, b3, cc2, pref, rfl⟩ := isIntCreate_inv hcr
  obtain ⟨sann, sl, su, s1, sc1, s2, s3, s, s4, sc3, s5, rfl, hs⟩ := intStore_inv hst
  let env2 : Env := extendEnv (bmap ys) env
  have hr2 : EnvRel (extend ys fenv) env2 := hr.extend ys
  have hm : matchPattern pt (rv w) = some (bmap ys) := by rw [matchP_rv, hys]; rfl
  let m2 := focusMemory a1 (focusMemory a0 m)
  have hb2 : Budget m2 := (hb.focus a0).focus a1
  let mc := focusMemory ann m2
  let ptr : Val := .object (.pointer (.allocated mc.nextId (nextIntAddress m2)))
  let m3 := Actions.created pref cc2 mc
  let env3 : Env := env2.insert x ptr
  have hlive : LiveInt m3 mc.nextId (nextIntAddress m2) := by
    have := Locals.created_live pref cc2 mc (hb2.focus ann).fresh
    rwa [Locals.nextIntAddress_focus] at this
  have hxl : env3.lookup x3 = some ptr := lookup_bind ptr hx3
  have htl : env3.lookup t = some (.loaded (.specified (.integer n))) := by
    rw [Map.lookup_insert_of_key_ne _ _ hlt, hr2 t, hlook]; rfl
  obtain ⟨xs, rst⟩ := Locals.store_reaches (file := file) (labels := labels) sann s1 s2 s3 s4 s5 sc1
    sc3 sl su x3 s t hs env3
    (.effectBind (.mk pn (.base (none, bn))) (.mk a4 (.pure (.mk a5 u5 (.sym x')))) env3 :: k) m3
    hxl htl hrange hlive
  let m4 := Locals.stored (focusMemory sann m3) mc.nextId (nextIntAddress m2) n
  have hslot : Locals.Slot m4 mc.nextId (nextIntAddress m2) n :=
    Locals.stored_slot (Locals.liveInt_focus sann hlive) n
  refine ⟨mc.nextId, nextIntAddress m2, xs, focusMemory a4 m4, ?_, Locals.slot_focus a4 hslot, hrange,
    by simp [m4, m3, mc, m2, Locals.stored_stdout, Actions.created_stdout]⟩
  refine (Straight.focus_reaches (request_let file labels)).trans ?_
  refine (eval_reaches file labels Return.fuel fenv nth w hw env hr _ _).trans ?_
  refine (lift file labels (ra_effectBind file labels hm _ _) (plain_effectExpr _ _)).trans ?_
  refine (if_false_reaches file labels hr2 hc _ _).trans ?_
  refine (lift file labels (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine (Locals.create_reaches ann b1 b2 b3 cc1 cc2 l uu pref env2 _ m2 hb2.room).trans ?_
  refine (lift file labels (ra_effectBind file labels (xs := [(x, ptr)]) rfl _ _)
    (plain_effectExpr _ _)).trans ?_
  refine (lift file labels (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine rst.trans ?_
  refine (lift file labels (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => ra_effectBind file labels (xs := []) rfl _ _)) (plain_effectExpr _ _)).trans ?_
  refine (ReturnConst.effect_pure_reaches file labels a4 _ _ _ _).trans ?_
  refine (lift file labels (ra_sym file labels _ _ (lookup_bind ptr hx')) (plain_value _)).trans ?_
  exact lift file labels (ra_diagnostic file labels _ _) (plain_value _)

/-- **The call of the C library `exit`** on the argument object holding `n` halts with `n`. -/
theorem call_reaches {e : EExp} {g q : Sym} (h : callExit e = some (g, q)) {env : Env} {y : Sym}
    (hg : env.lookup g = some (.loaded (.specified (.pointer (.function y)))))
    (hy : isExit file y = true) {id addr n : Int}
    (hq : env.lookup q = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (k : List Frame) (m : Mem.Concrete.State) (slot : Locals.Slot m id addr n) :
    ∃ m', Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ ∧ m'.stdout = m.stdout := by
  obtain ⟨a0, pat, a1, u, ty, a2, u2, a3, u3, after, rfl⟩ := callExit_inv h
  obtain ⟨live, plain, bytes⟩ := Locals.slot_focus a1 slot
  obtain ⟨xs, rload⟩ := Actions.load_apply (file := file) (labels := labels) []
    (.arguments (.builtin "exit") [] [] ∅ :: .strongBind pat after env :: k) live plain hn bytes
  refine ⟨{focusMemory a1 m with lastUsed := some id}, ?_, by simp⟩
  refine (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine (Straight.focus_reaches (request_ccall file labels)).trans ?_
  refine (lift file labels (ra_sym file labels _ _ hg) (plain_value _)).trans ?_
  refine (lift file labels (ra_args_cons file labels _ _ _ _ _) (plain_pureExpr _ _)).trans ?_
  refine (lift file labels (ra_sym file labels _ _ hq) (plain_value _)).trans ?_
  refine (lift file labels (ra_args_nil file labels _ _ _) (plain_apply _ _)).trans ?_
  refine (scheduled_reaches file labels (ra_exit file labels (libraryCall_of_isExit hy) _)
    (fun _ h => nomatch h)).trans ?_
  refine rload.trans ?_
  refine (lift file labels (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => ra_args_nil file labels _ _ _)) (plain_apply _ _)).trans ?_
  refine (scheduled_reaches file labels (ra_builtin_exit file labels _) (fun _ h => nomatch h)).trans ?_
  exact end_reaches file labels (ra_raise file labels _) (fun _ h => nomatch h)

/-- **`exit(e)`** halts with the stored argument, in any environment the folder's environment
describes, under any continuation, from any memory with room for the argument object. -/
theorem exitCall_reaches {fenv : WEnv} {env : Env} (hr0 : EnvRel fenv env) {e : EExp} {n : Int}
    (h : exitCall file fenv e = some n) (k : List Frame) (m : Mem.Concrete.State) (hb : Budget m) :
    ∃ m', Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ ∧ m'.stdout = m.stdout := by
  obtain ⟨a0, pat, a1, t0, t1, a2, c1, u1, a3, c2, u2, a4, pp, p, bp, args, rest, w0, na, xs, g, q, y,
    rfl, h0, h1, hxs, hc1, hc2, ho, hce, hq, hg, hgl, hy⟩ := exitCall_inv h
  let env' : Env := extendEnv (bmap xs) env
  have hr : EnvRel (extend xs fenv) env' := hr0.extend xs
  have hm : matchPattern pat (.tuple [rv w0, .loaded (.specified (.integer na))]) = some (bmap xs) := by
    rw [show (Value.tuple [rv w0, .loaded (.specified (.integer na))] : Val) =
      rv (.tuple [w0, .loaded (.specified (.integer na))]) from rfl, matchP_rv, hxs]; rfl
  obtain ⟨l1, ru⟩ := call_unseq file labels hr0 h0 h1 a1 (.strongBind pat _ env :: k) m
  let m2 := focusMemory a3 (focusMemory a2 {m with currentLocation := l1})
  obtain ⟨id, addr, ys, m3, ra, slot, hn, out3⟩ := argObject_reaches file labels hr ho
    (.strongBind (.mk pp (.base (some p, bp))) rest env' :: .annotations [] :: k) m2
    (((hb.reloc l1).focus a2).focus a3)
  let pv : Val := .object (.pointer (.allocated id addr))
  have hgl' : (env'.insert p pv).lookup g = some (.loaded (.specified (.pointer (.function y)))) := by
    rw [Map.lookup_insert_of_key_ne _ _ hg, hr g, hgl]; rfl
  obtain ⟨m4, rc, out4⟩ := call_reaches file labels hce hgl' hy (lookup_bind pv hq) hn
    (.annotations ys :: .annotations [] :: k) m3 slot
  refine ⟨m4, ?_, by rw [out4, out3]; simp [m2]⟩
  refine (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine ru.trans ?_
  refine (lift file labels (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => ra_strongBind file labels hm _ _)) (plain_effectExpr _ _)).trans ?_
  refine (if_false_reaches file labels hr hc1 _ _).trans ?_
  refine (if_false_reaches file labels hr hc2 _ _).trans ?_
  refine (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine ra.trans ?_
  refine (lift file labels (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => ra_strongBind file labels (xs := [(p, pv)]) rfl _ _)) (plain_effectExpr _ _)).trans ?_
  exact rc

/-- The body runs its sequencing glue down to `exit(e)`. -/
theorem recognizeBody_reaches {n : Int} : (e : EExp) → recognizeBody file e = some n →
    ∀ (k : List Frame) (m : Mem.Concrete.State), Budget m →
    ∃ m', Reaches file labels ⟨.effectExpr e ∅, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ ∧ m'.stdout = m.stdout
  | e, h, k, m, hb => by
    rw [recognizeBody.eq_def] at h
    split at h
    · rename_i n' he
      cases h
      exact exitCall_reaches file labels EnvRel.empty he k m hb
    · split at h
      · rename_i pat a b _
        obtain ⟨m', r, o⟩ := recognizeBody_reaches a h (.strongBind pat b ∅ :: k) m hb
        exact ⟨m', (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans r, o⟩
      · rename_i pat a b _
        obtain ⟨m', r, o⟩ := recognizeBody_reaches a h (.effectBind pat b ∅ :: k) m hb
        exact ⟨m', (lift file labels (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)).trans r, o⟩
      · rename_i a _
        obtain ⟨m', r, o⟩ := recognizeBody_reaches a h (.bound :: k) m hb
        exact ⟨m', (lift file labels (ra_bound file labels _ _) (plain_effectExpr _ _)).trans r, o⟩
      · cases h

end Call

/-! ## The whole document -/

/-- The whole-document run: from the initial state (any arguments, any enum registrations), the
dynamics halts with `Specified n` and empty stdout. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (h : recognize doc = some n)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels t, initial doc.file enums args = .ok (s, labels) ∧ Reaches doc.file labels s t ∧
      t.control = .halt (.defined (.loaded (.specified (.integer n)))) ∧ t.memory.stdout = "" := by
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
          have hbody : recognizeBody doc.file body = some n := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ :=
            StartupMem.initial_reaches_body_mem doc.file enums args hdefs main decl
          have hb : Budget m :=
            ⟨by simp [nextIntAddress, hlast, StartupReach.errnoAddr], by simp [hdead]⟩
          obtain ⟨m', hrun, hout'⟩ := recognizeBody_reaches doc.file labels body hbody _ m hb
          exact ⟨s, labels, _, hinit, hentry.trans hrun, rfl, hout'.trans hout⟩

/-- **Core side.** A recognised document exits with `n mod 256` and no output, for every
argument list. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (h : recognize doc = some n)
    (args : List String) : Spec.CoreBeh doc args (.exit (n % 256).toNat []) := by
  obtain ⟨s, labels, t, hinit, reach, halt, out⟩ :=
    recognize_reaches doc n h (Map.ofList (doc.enumBindings.getD [])) args
  have beh := Spec.CoreBeh.exit (k := (n % 256).toNat) ⟨s, labels, hinit, reach⟩ halt rfl
  simpa [Spec.coreBytes, out] using beh

end Silmaril.Compile.Core.Verified.ExitCall
