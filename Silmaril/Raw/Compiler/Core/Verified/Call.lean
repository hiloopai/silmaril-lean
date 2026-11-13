module

public import Silmaril.Compiler.Core.Verified.ReturnExpr.Defs
public import Silmaril.Cerberus.Core.CallReach.Defs

/-! # Calls of known procedures without parameters

Cerberus elaborates a call `g()` of a function designator to

```
let strong p = pure(<function pointer g>) in
let (f, ps, _, _) = cfunction(p) in
if params_length(ps) = 0 then
  if are_compatible(<return type at the call>, f) then ccall(<type>, p, []) else undef
else undef
```

`callSite` recognises that shape, `callee` the procedure `g` it calls: a procedure of the file
(not of std.core) without parameters, whose body is `return e;` for an `int` expression `e` of
`IntExpr.term` that reads no local (as `ReturnExpr.recognizeBody`), or a `void` body that
returns (`return;`) or falls off its end without effects (`voidBody`). `recognize` accepts a
`main` whose body is `return g();` (`Plan.ret`) or `g(); return e;` (`Plan.stmt`).

`recognize_sound`: Core reaches undefined behaviour (an operator of a returned expression
leaves `int`) or exits with the value of the returned expression mod 256 and no output, for
every argument list. Nothing is evaluated at compile time: the Lir translation
(`Verified/CallLink.lean`) calls a Lir function for `g` that computes `e` at run time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Call

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel saveFree noBoundary_cons)
open ConvInt (isConvLoadedInt IsInt lookupFun)
open IntExpr (Term)
open LocalExpr (Shows)

/-! ## Recognisers -/

/-- The return types of the fragment: `int` (`true`) and `void` (`false`). -/
def retKind : Ctype → Option Bool
  | .mk _ (.basic (.integer (.signed .int))) => some true
  | .mk _ .void => some false
  | _ => none

/-- std.core's `params_length_aux(acc, cs) = case cs of [] => acc | …`. -/
def isLengthAux : ConvInt.Fun → Bool
  | .function _ [(acc, _), (cs, _)]
      (.mk _ () (.case_ (.mk _ () (.sym cs₁))
        ((.mk _ (.ctor (.nil _) []), .mk _ () (.sym acc₁)) :: _))) =>
      decide (acc.key ≠ cs.key ∧ cs₁.key = cs.key ∧ acc₁.key = acc.key)
  | _ => false

/-- std.core's `params_length(cs) = params_length_aux(0, cs)`. -/
def isLength (file : File Codec.wireModel Unit Unit) : ConvInt.Fun → Bool
  | .function _ [(cs, _)]
      (.mk _ () (.call (.sym aux) [.mk _ () (.val (.object (.integer z))), .mk _ () (.sym cs₁)])) =>
      decide (z = 0 ∧ cs₁.key = cs.key) &&
      (match lookupFun file aux with
       | some d => isLengthAux d
       | none => false)
  | _ => false

/-- The symbol `s` names std.core's `params_length`. -/
def isParamsLength (file : File Codec.wireModel Unit Unit) (s : Sym) : Bool :=
  match lookupFun file s with
  | some d => isLength file d
  | none => false

/-- The elaboration of a call `g()`: the procedure `g` and the return kind at the call. -/
def callSite (file : File Codec.wireModel Unit Unit) : Eff → Option (Sym × Bool)
  | .mk _ (.sseq (.mk _ (.base (some p, _)))
      (.mk _ (.pure (.mk _ () (.val (.loaded (.specified (.pointer (.function g))))))))
      (.mk _ (.let_ (.mk _ (.ctor .tuple [.mk _ (.base (some fty, _)), .mk _ (.base (some pty, _)),
          .mk _ (.base (none, _)), .mk _ (.base (none, _))]))
        (.mk _ () (.cfunction (.mk _ () (.sym p₁))))
        (.mk _ (.if_ (.mk _ () (.op .eq (.mk _ () (.call (.sym len) [.mk _ () (.sym pty₁)]))
            (.mk _ () (.val (.object (.integer z))))))
          (.mk _ (.if_ (.mk _ () (.areCompatible (.mk _ () (.val (.ctype rty))) (.mk _ () (.sym fty₁))))
            (.mk _ (.ccall () _ (.mk _ () (.sym p₂)) []))
            _))
          _))))) =>
      if p₁.key = p.key ∧ p₂.key = p.key ∧ pty₁.key = pty.key ∧ fty₁.key = fty.key ∧
          fty.key ≠ pty.key ∧ p.key ≠ fty.key ∧ p.key ≠ pty.key ∧ z = 0 ∧
          isParamsLength file len = true then
        (retKind rty).map (g, ·)
      else none
  | _ => none

/-- A `void` statement sequence that executes `return;` (a transfer of `unit` to `ret`),
after statements without effect. -/
def voidRet (ret : Sym) : Eff → Bool
  | .mk _ (.run () l [.mk _ () (.val .unit)]) => decide (l.key = ret.key)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a b) =>
      voidRet ret a || (ReturnConst.skip a && voidRet ret b)
  | _ => false

/-- The body of a `void` procedure: statements that return or fall off the end without
effects, then the return label `ret(r := unit) = pure(r)`. -/
def voidBody : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, (_, .mk _ () (.val .unit)))] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      decide (r'.key = r.key) && saveFree a && (ReturnConst.skip a || voidRet ret a)
  | _ => false

/-- The procedure `g` of the file, without parameters, of return kind `isInt`: `some t` for a
body `return e;` (`e` recognised as `t`), `none` for a `void` body. -/
def callee (file : File Codec.wireModel Unit Unit) (g : Sym) (isInt : Bool) :
    Option (Option Term) :=
  if (file.stdlib.lookup g).isSome then none else
  match file.funInfo.lookup g with
  | some (_, _, rty, [], _, _) =>
    match file.funs.lookup g with
    | some (.procedure _ _ _ [] body) =>
      if retKind rty = some isInt then
        if isInt then (ReturnExpr.recognizeBody file body).map some
        else if voidBody body then some none else none
      else none
    | _ => none
  | _ => none

/-- A statement sequence that starts with `return g();`. -/
def retCall (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option (Sym × Term)
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ isConvLoadedInt file s = true then
        match callSite file e with
        | some (g, true) =>
          match callee file g true with
          | some (some t) => some (g, t)
          | _ => none
        | _ => none
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retCall file ret a
  | _ => none

/-- A statement sequence `g(); return e;`. -/
def stmtCall (file : File Codec.wireModel Unit Unit) (ret : Sym) :
    Eff → Option (Sym × Option Term × Term)
  | .mk _ (.sseq (.mk _ (.base (none, _)))
      (.mk _ (.sseq (.mk _ (.base (none, _))) (.mk _ (.bound e)) u)) rest) =>
      if ReturnConst.skip u = true then
        match callSite file e with
        | some (g, isInt) =>
          match callee file g isInt, ReturnExpr.retTerm file ret rest with
          | some c, some t => some (g, c, t)
          | _, _ => none
        | none => none
      else none
  | _ => none

/-- A statement sequence that starts with `return g(), e;` (the comma operator). -/
def retComma (file : File Codec.wireModel Unit Unit) (ret : Sym) :
    Eff → Option (Sym × Option Term × Term)
  | .mk _ (.sseq (.mk _ (.base (some u, _)))
      (.mk _ (.bound (.mk _ (.sseq (.mk _ (.base (none, _))) e e₂))))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ isConvLoadedInt file s = true then
        match callSite file e with
        | some (g, isInt) =>
          match callee file g isInt, IntExpr.term file u e₂ with
          | some c, some t => if t.reads = false then some (g, c, t) else none
          | _, _ => none
        | none => none
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retComma file ret a
  | _ => none

/-- What a recognised `main` does. -/
inductive Plan where
  /-- `return g();`, `g` returning `t`. -/
  | ret (g : Sym) (t : Term)
  /-- `g(); return t;`, `g` returning `c` (`none`: `void`). -/
  | stmt (g : Sym) (c : Option Term) (t : Term)
  /-- `return g(), t;`, with the call result discarded. -/
  | comma (g : Sym) (c : Option Term) (t : Term)

/-- The expression whose value `main` returns. -/
def Plan.result : Plan → Term
  | .ret _ t => t
  | .stmt _ _ t | .comma _ _ t => t

/-- The body of `main`: a statement sequence of the fragment, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Plan
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then
        match retCall file ret a with
        | some (g, t) => some (.ret g t)
        | none =>
          match stmtCall file ret a with
          | some (g, c, t) => some (.stmt g c t)
          | none => (retComma file ret a).map fun (g, c, t) => .comma g c t
      else none
  | _ => none

/-- `main` calls a known procedure without parameters. -/
def recognize (doc : Codec.Document) : Option Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-! ## Core side -/

variable {file : Program} {labels : Labels}

theorem retKind_eq {c : Ctype} {isInt : Bool} (h : retKind c = some isInt) :
    ∃ ann, c = .mk ann (if isInt then .basic (.integer (.signed .int)) else .void) := by
  unfold retKind at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> exact ⟨_, rfl⟩

/-- Return types of the same kind are compatible. -/
theorem compatible_retKind {a b : Ctype} {isInt : Bool} (ha : retKind a = some isInt)
    (hb : retKind b = some isInt) (enums : Map Sym IntegerType) :
    compatibleWith enums 256 noQualifiers a noQualifiers b = .ok true := by
  obtain ⟨an, rfl⟩ := retKind_eq ha
  obtain ⟨bn, rfl⟩ := retKind_eq hb
  cases isInt <;> rfl

/-- `are_compatible(rty, f)` for return types of the same kind. -/
theorem compatible_reaches {ann aann bann : List Annot} {rty fty : Ctype} {f : Sym} {env : Env}
    {isInt : Bool} (hr : retKind rty = some isInt) (hf : retKind fty = some isInt)
    (hl : env.lookup f = some (.ctype fty)) :
    SeqReach.PureEval file labels
      (.mk ann () (.areCompatible (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))) env
      .true := by
  intro k m
  refine (SeqReach.next_reaches (c' := .pureExpr (.mk aann () (.val (.ctype rty))) env)
    (k' := .arguments .compatible [] [.mk bann () (.sym f)] env :: k) (by intro o h; cases h)
    (by simp [request, requestAux, awaitsScheduling, arguments])).trans ?_
  refine (SeqReach.pure_value aann (.ctype rty) env _ _).trans ?_
  refine (CallReach.arguments_reaches (.cons (SeqReach.pure_symbol bann f env _ hl) .nil)
    .compatible [] _ k m).trans ?_
  apply SeqReach.next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, primitive, runtimeValue,
    compatible_retKind hr hf, boolean, pure, Except.pure]

/-- `cfunction(p)` gives the metadata of the procedure `p` points to. -/
theorem cfunction_reaches {ann pann : List Annot} {p g : Sym} {env : Env}
    {loc : Loc} {attrs : Attributes} {rty : Ctype} {params : List (Option Sym × Ctype)}
    {variadic proto : Bool}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hg : file.funInfo.lookup g = some (loc, attrs, rty, params, variadic, proto)) :
    SeqReach.PureEval file labels (.mk ann () (.cfunction (.mk pann () (.sym p)))) env
      (.tuple [.ctype rty, .list .ctype (params.map fun q => .ctype q.2),
        boolean variadic, boolean proto]) := by
  intro k m
  refine (SeqReach.next_reaches (c' := .pureExpr (.mk pann () (.sym p)) env)
    (k' := .arguments .functionInfo [] [] env :: k) (by intro o h; cases h)
    (by simp [request, requestAux, awaitsScheduling, arguments])).trans ?_
  refine (SeqReach.pure_symbol pann p env _ hp _ _).trans ?_
  refine (CallReach.arguments_reaches .nil .functionInfo [] _ k m).trans ?_
  apply SeqReach.next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, hg]

/-- `params_length(ps) = 0` for the empty parameter list. -/
theorem length_eval {len pty : Sym} {env : Env} {ann a1 a2 a3 : List Annot}
    (hl : isParamsLength file len = true) (hp : env.lookup pty = some (.list .ctype []))
    (tags : Mem.Concrete.Tags) :
    Eval file tags env (.inl (.mk ann () (.op .eq
      (.mk a1 () (.call (.sym len) [.mk a2 () (.sym pty)])) (.mk a3 () (.val (.object (.integer 0)))))))
      (.inl .true) := by
  unfold isParamsLength at hl
  split at hl
  · rename_i d hd
    unfold isLength at hl
    split at hl
    · rename_i bt cs cbt pann cann aux vann z wann cs₁
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨⟨rfl, hcs⟩, hl⟩ := hl
      split at hl
      · rename_i d' hd'
        unfold isLengthAux at hl
        split at hl
        · rename_i bt' acc abt cs' cbt' pann' cann' cs'₁ nbt nann sann acc₁ rest
          obtain ⟨hne, hcs', hacc⟩ := of_decide_eq_true hl
          refine .op (vs := [.object (.integer 0), .object (.integer 0)])
            (.cons (.call (v := .object (.integer 0)) (.cons (.sym hp) .nil)
              (ConvInt.functionBody_eq hd rfl) ?_) (.cons .val .nil)) ?_
          · refine .call (v := .object (.integer 0))
              (.cons .val (.cons (.sym (ConvInt.lookup_one hcs)) .nil))
              (ConvInt.functionBody_eq hd' rfl) ?_
            refine .case_ (xs := []) (body := .mk sann () (.sym acc₁))
              (.sym (ConvInt.lookup_two_second hcs' (fun h => hne h.symm))) ?_ (.sym ?_)
            · simp [selectCase, matchPattern]
            · exact ConvInt.lookup_two_first (x := .object (.integer 0)) (y := .list .ctype []) hacc
          · simp [primitive, integerBin, boolean, pure, Except.pure]
        · cases hl
      · cases hl
    · cases hl
  · cases hl

/-- A pure expression that evaluates under every tag environment. -/
theorem pureEval_of {p : PE} {env : Env} {v : Val}
    (h : ∀ tags, Eval file tags env (.inl p) (.inl v)) : SeqReach.PureEval file labels p env v :=
  fun k m => Eval.sound file _ (h (tagsOf file m)) labels k m rfl

/-- What a call reaches: for an `int` callee `some t`, the value of `t`, or undefined behaviour
when an operator leaves `int`; for a `void` callee (`none`), `unit`. -/
def Gives (s : State) (k : List Frame) (out : String) : Option Term → Prop
  | none => ∃ m', m'.stdout = out ∧ Reaches file labels s ⟨.value .unit, k, m'⟩
  | some t => (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧
      Reaches file labels s ⟨.value (IntExpr.spec (t.val 0)), k, m'⟩) ∨
    ∃ s', Reaches file labels s s' ∧ s'.control = .halt IntExpr.overflow

theorem Gives.pre {s s' : State} {k : List Frame} {out : String} {c : Option Term}
    (h : Reaches file labels s s') (o : Gives (file := file) (labels := labels) s' k out c) :
    Gives (file := file) (labels := labels) s k out c := by
  cases c with
  | none =>
    obtain ⟨m', hout, r⟩ := o
    exact ⟨m', hout, h.trans r⟩
  | some t =>
    rcases o with ⟨ok, m', hout, r⟩ | ⟨s'', r, hs⟩
    · exact .inl ⟨ok, m', hout, h.trans r⟩
    · exact .inr ⟨s'', h.trans r, hs⟩

/-- Below the frames of the callee's body, the nearest boundary is the procedure's. -/
theorem context_local {loc : List Frame} (h : NoBoundary loc) (L : Labels) (caller : List Frame) :
    procedureContext labels (loc ++ .procedureReturn L :: caller) =
      (L, .procedureReturn L :: caller) := by
  induction loc with
  | nil => rfl
  | cons f loc ih =>
    unfold NoBoundary hasBoundary at h
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have ih' := ih h.2
    cases f <;> simp_all [procedureContext]

/-- `run ret(v)` in a procedure returns `v` to its caller. -/
theorem jump_returns {ret l : Sym} {L : Labels} (hl : l.key = ret.key) (hret : ReturnLabel L ret)
    (v : Val) (env : Env) {loc : List Frame} (hk : NoBoundary loc) (caller : List Frame)
    (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels
      ⟨.value v, .runLabel l [] [] env :: (loc ++ .procedureReturn L :: caller), m⟩
      ⟨.value v, .procedureReturn L :: caller, m'⟩ := by
  obtain ⟨r, bann, pann, r', hr, hlook⟩ := hret
  have hlook' : L.lookup l = some ([r], .mk bann (.pure (.mk pann () (.sym r')))) := by
    rw [ReturnLit.lookup_key hl]; exact hlook
  refine ⟨SeqReach.focusMemory bann m, by simp, ?_⟩
  exact (LoopReach.run_arguments_reaches .nil [] v _ _ m L [r] _ (context_local hk L caller)
    hlook' rfl).trans
    (SeqReach.effect_pure_reaches bann (SeqReach.pure_symbol pann r' _ v (ConvInt.lookup_one hr)) _ m)

/-- **`return e;` in a procedure** returns the value of `e` to the caller, or reaches
undefined behaviour. -/
theorem retTerm_returns {ret : Sym} {L : Labels} (hret : ReturnLabel L ret) (e : EE) (t : Term)
    (h : ReturnExpr.retTerm file ret e = some t) (env : Env) {loc : List Frame}
    (hk : NoBoundary loc) (caller : List Frame) (m : Mem.Concrete.State) :
    Gives (file := file) (labels := labels)
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      (.procedureReturn L :: caller) m.stdout (some t) := by
  unfold ReturnExpr.retTerm at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i t' hτ
        split at h
        · rename_i hr
          have e := Option.some.inj h
          subst e
          have none₁ : ∀ {P : Prop}, t'.reads = true → P := fun r => by rw [hr] at r; cases r
          let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
          let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env ::
            (loc ++ .procedureReturn L :: caller)
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
                loc ++ .procedureReturn L :: caller, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env _ m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine Gives.pre pre ?_
          by_cases ok : t'.Ok 0
          · left
            refine ⟨ok, ?_⟩
            obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
              (labels := labels) (env := env) (id := 0) (addr := 0) t' hτ none₁
              ReturnExpr.isInt_zero ok (.bound :: kR) m none₁
            let v : Val := IntExpr.spec (t'.val 0)
            have popped : Reaches file labels ⟨.value v, fr ++ .bound :: kR, m₁⟩
                ⟨.value v, kR, m₁⟩ := by
              rcases hfr with ⟨rfl, -⟩ | rfl
              · exact LocalExpr.value_bound_reaches v kR m₁
              · exact Locals.annotations_bound_reaches xs v kR m₁
            let env₁ := extendEnv [(u, v)] env
            have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₁)) env₁
                (.inl (.mk cann () (.call (.sym s)
                  [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                    .mk a3 () (.sym u')])))
                (.inl v) :=
              ConvInt.convLoadedInt_eval (ann := tyann) hs
                (IntExpr.Term.ok_int ReturnExpr.isInt_zero t' ok)
                (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
            obtain ⟨m', out, back⟩ := jump_returns (file := file) (labels := labels) hl hret v env₁ hk
              caller (ReturnConst.focusMemory rann m₁)
            refine ⟨m', by simp [out, tch.stdout], ?_⟩
            refine (Interleave.reaches_of_local file labels run).trans (popped.trans ?_)
            refine (ReturnLit.bind_reaches pann u ty v R env _ m₁).trans ?_
            refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
            exact ((Eval.sound file _ heval) labels _ _ rfl).trans back
          · right
            exact ArenaFail.fail_reaches file labels
              (IntExpr.term_fails (file := file) (labels := labels) (env := env) (id := 0) (addr := 0)
                t' hτ none₁ ReturnExpr.isInt_zero ok (.bound :: kR) m none₁)
        · cases h
      · cases h
    · cases h
  · rename_i _ ann pc c cty bann ec sann pb b bty cb iann bp b' ea eb
    split at h
    · rename_i cond
      obtain ⟨hb', hcb⟩ := cond
      split at h
      · rename_i tc ta tb htc hta htb
        split at h
        · rename_i hreads
          cases h
          have noread : ∀ {P : Prop}, tc.reads = true → P := fun r => by
            rw [hreads] at r; cases r
          let k := loc ++ .procedureReturn L :: caller
          let IF : EE := .mk iann (.if_ (.mk bp () (.sym b')) ea eb)
          let REST : EE := .mk sann (.sseq (.mk pb (.base (some b, bty))) cb IF)
          let K := Frame.strongBind (.mk pc (.base (some c, cty))) REST env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pc (.base (some c, cty)))
                (.mk bann (.bound ec)) REST)) env, k, m⟩
              ⟨.effectExpr ec env, .bound :: K, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine Gives.pre pre ?_
          by_cases okc : tc.Ok 0
          · obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
              (labels := labels) (env := env) (id := 0) (addr := 0) tc htc noread
              ReturnExpr.isInt_zero okc (.bound :: K) m noread
            have popped : Reaches file labels
                ⟨.value (IntExpr.spec (tc.val 0)), fr ++ .bound :: K, m₁⟩
                ⟨.value (IntExpr.spec (tc.val 0)), K, m₁⟩ := by
              rcases hfr with ⟨rfl, -⟩ | rfl
              · exact LocalExpr.value_bound_reaches _ K m₁
              · exact Locals.annotations_bound_reaches xs _ K m₁
            let env₁ := extendEnv [(c, IntExpr.spec (tc.val 0))] env
            let KB := Frame.strongBind (.mk pb (.base (some b, bty))) IF env₁ :: k
            obtain ⟨m₂, out₂, conv⟩ := StmtIf.boolSource_reaches (file := file) (labels := labels)
              hcb env₁ KB m₁ (tc.val 0) (ConvInt.lookup_one rfl)
            let flag := decide (tc.val 0 ≠ 1)
            let env₂ := extendEnv [(b, boolean flag)] env₁
            have hp : SeqReach.PureEval file labels (.mk bp () (.sym b')) env₂ (boolean flag) :=
              SeqReach.pure_symbol bp b' env₂ _ (ConvInt.lookup_one hb')
            have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
                ⟨.effectExpr (if flag then ea else eb) env₂, k, SeqReach.focusMemory iann m₂⟩ :=
              (Interleave.reaches_of_local file labels run).trans (popped.trans
                ((ReturnLit.bind_reaches pc c cty _ REST env k m₁).trans
                  ((ReturnConst.sequence_reaches file labels sann _ cb IF env₁ k m₁).trans
                    (conv.trans ((ReturnLit.bind_reaches pb b bty _ IF env₁ k m₂).trans
                      (SeqReach.effect_if_reaches iann flag hp k m₂))))))
            have outm : (SeqReach.focusMemory iann m₂).stdout = m.stdout := by
              simp [out₂, tch.stdout]
            by_cases hc : tc.val 0 = 1
            · have o := retTerm_returns hret eb tb htb env₂ hk caller (SeqReach.focusMemory iann m₂)
              rw [outm] at o
              have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
                  ⟨.effectExpr eb env₂, k, SeqReach.focusMemory iann m₂⟩ := by
                simpa [flag, hc] using enter
              have o := Gives.pre enter' o
              rcases o with ⟨okb, m', hout, reach⟩ | ub
              · exact .inl ⟨by simpa [hc] using And.intro okc okb, m', hout,
                  by simpa [hc] using reach⟩
              · exact .inr ub
            · have o := retTerm_returns hret ea ta hta env₂ hk caller (SeqReach.focusMemory iann m₂)
              rw [outm] at o
              have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
                  ⟨.effectExpr ea env₂, k, SeqReach.focusMemory iann m₂⟩ := by
                simpa [flag, hc] using enter
              have o := Gives.pre enter' o
              rcases o with ⟨oka, m', hout, reach⟩ | ub
              · exact .inl ⟨by simpa [hc] using And.intro okc oka, m', hout,
                  by simpa [hc] using reach⟩
              · exact .inr ub
          · right
            exact ArenaFail.fail_reaches file labels
              (IntExpr.term_fails (file := file) (labels := labels) (env := env) (id := 0) (addr := 0)
                tc htc noread ReturnExpr.isInt_zero okc (.bound :: K) m noread)
        · cases h
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    exact Gives.pre (ReturnConst.sequence_reaches file labels ann _ a b env _ m)
      (retTerm_returns hret a t h env (loc := .strongBind (.mk pann (.base (none, ty))) b env :: loc)
        (noBoundary_cons hk trivial) caller m)
  · cases h
termination_by sizeOf e

/-- The body of an `int` callee returns its value, or reaches undefined behaviour. -/
theorem intBody_returns {body : EE} {t : Term} (h : ReturnExpr.recognizeBody file body = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) :
    Gives (file := file) (labels := labels)
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: caller, m⟩
      (.procedureReturn (CallReach.bodyLabels body) :: caller) m.stdout (some t) := by
  unfold ReturnExpr.recognizeBody at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      exact Gives.pre (ReturnConst.sequence_reaches file labels ann _ a _ env _ m)
        (retTerm_returns (by
            refine ⟨r, bann, pann', r', hr, ?_⟩
            simp [CallReach.bodyLabels, saves, StmtIf.labelFree_saves a hfree, Map.ofList])
          a t h env
          (loc := [.strongBind (.mk pann (.base (none, bt0))) _ env])
          (by simp [NoBoundary, hasBoundary]) caller m)
    · cases h
  · cases h

/-- `return;` in a `void` procedure returns `unit` to the caller. -/
theorem voidRet_returns {ret : Sym} {L : Labels} (hret : ReturnLabel L ret) (e : EE)
    (h : voidRet ret e = true) (env : Env) {loc : List Frame} (hk : NoBoundary loc)
    (caller : List Frame) (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      ⟨.value .unit, .procedureReturn L :: caller, m'⟩ := by
  unfold voidRet at h
  split at h
  · rename_i ann l pann
    obtain ⟨m', out, back⟩ := jump_returns (file := file) (labels := labels)
      (of_decide_eq_true h) hret .unit env hk caller (ReturnConst.focusMemory ann m)
    refine ⟨m', by simp [out], ?_⟩
    refine (Straight.focus_reaches Straight.request_run).trans ?_
    exact (ReturnConst.pure_value_reaches file labels pann .unit env _ _).trans back
  · rename_i ann pann ty a b
    rcases Bool.or_eq_true_iff.mp h with ha | hab
    · obtain ⟨m', out, r⟩ := voidRet_returns hret a ha env
        (loc := .strongBind (.mk pann (.base (none, ty))) b env :: loc) (noBoundary_cons hk trivial)
        caller m
      exact ⟨m', out, (ReturnConst.sequence_reaches file labels ann _ a b env _ m).trans r⟩
    · obtain ⟨hs, hb⟩ := Bool.and_eq_true_iff.mp hab
      obtain ⟨m₁, out₁, ra⟩ := ReturnConst.skip_reaches file labels a hs env
        (.strongBind (.mk pann (.base (none, ty))) b env :: (loc ++ .procedureReturn L :: caller)) m
      obtain ⟨m₂, out₂, rb⟩ := voidRet_returns hret b hb env hk caller m₁
      exact ⟨m₂, out₂.trans out₁, (ReturnConst.sequence_reaches file labels ann _ a b env _ m).trans
        (ra.trans ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env _ m₁).trans rb))⟩
  · cases h
termination_by sizeOf e

/-- The body of a `void` callee returns `unit` to the caller. -/
theorem voidBody_returns {body : EE} (h : voidBody body = true) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels
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
      obtain ⟨m₁, out₁, ra⟩ := ReturnConst.skip_reaches file labels a hskip env
        (.strongBind (.mk pann (.base (none, bt0))) SAVE env :: k) m
      let m₂ := ReturnConst.focusMemory sann m₁
      refine ⟨ReturnConst.focusMemory bann m₂, by simp [m₂, out₁], ?_⟩
      refine (ReturnConst.sequence_reaches file labels ann _ a SAVE env _ m).trans
        (ra.trans ((ReturnConst.wildcard_sequence_reaches file labels pann bt0 .unit SAVE env _ m₁).trans ?_))
      refine (ReturnConst.save_reaches file labels sann _ r pinfo _ _ env k m₁).trans ?_
      refine (ReturnConst.pure_value_reaches file labels dann .unit env _ _).trans ?_
      refine (ReturnConst.saveArgument_reaches file labels r .unit _ env k m₂).trans ?_
      refine (ReturnConst.effect_pure_reaches file labels bann _ (env.insert r .unit) k m₂).trans ?_
      exact (ReturnConst.pure_sym_reaches file labels pann' r r' hr.symm .unit env _ _).trans
        (ReturnConst.diagnostic_reaches file labels m₂.currentLocation .unit k _)
    · obtain ⟨m', out, back⟩ := voidRet_returns (file := file) (labels := labels)
        (ReturnLit.returnLabel_body (pat := .mk pann (.base (none, bt0))) (ann := ann) (sann := sann)
          (bann := bann) (pann' := pann') (bt := bt) (info := (pinfo, .mk dann () (.val .unit))) hr hfree)
        a hret env (loc := [.strongBind (.mk pann (.base (none, bt0))) _ env])
        (by simp [NoBoundary, hasBoundary]) caller m
      exact ⟨m', out, (ReturnConst.sequence_reaches file labels ann _ a _ env _ m).trans back⟩
  · cases h

/-- What `callee` checked of the body of `g`. -/
def BodyOf (file : Program) (body : EE) : Option Term → Prop
  | some t => ReturnExpr.recognizeBody file body = some t
  | none => voidBody body = true

/-- The facts `callee` checks. -/
theorem callee_spec {g : Sym} {isInt : Bool} {c : Option Term}
    (hc : callee file g isInt = some c) :
    ∃ loc attrs rty variadic proto dloc marker bt body,
      file.stdlib.lookup g = none ∧
      file.funInfo.lookup g = some (loc, attrs, rty, [], variadic, proto) ∧
      file.funs.lookup g = some (.procedure dloc marker bt [] body) ∧ retKind rty = some isInt ∧
      BodyOf file body c := by
  unfold callee at hc
  split at hc
  · cases hc
  rename_i hstd
  split at hc
  · rename_i loc attrs rty variadic proto hinfo
    split at hc
    · rename_i dloc marker bt body hdecl
      split at hc
      · rename_i hk
        refine ⟨loc, attrs, rty, variadic, proto, dloc, marker, bt, body, ?_, hinfo, hdecl, hk, ?_⟩
        · simpa using hstd
        split at hc
        · obtain ⟨t, ht, rfl⟩ : ∃ t, ReturnExpr.recognizeBody file body = some t ∧ c = some t := by
            cases h : ReturnExpr.recognizeBody file body with
            | none => simp [h] at hc
            | some t =>
              simp [h] at hc
              exact ⟨t, rfl, by subst hc; rfl⟩
          exact ht
        · split at hc
          · cases hc
            assumption
          · cases hc
      · cases hc
    · cases hc
  · cases hc

theorem lookup_ext2_first {a b s : Sym} {x y : Val} {env : Env} (h : s.key = a.key) :
    (extendEnv [(a, x), (b, y)] env).lookup s = some x := by
  have : MapKey.key s = MapKey.key a := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [this, Finmap.lookup_insert]

theorem lookup_ext2_second {a b s : Sym} {x y : Val} {env : Env} (h : s.key = b.key)
    (ne : b.key ≠ a.key) : (extendEnv [(a, x), (b, y)] env).lookup s = some y := by
  have hs : MapKey.key s ≠ MapKey.key a := by
    change s.key ≠ a.key
    rw [h]; exact ne
  have : MapKey.key s = MapKey.key b := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [Finmap.lookup_insert_of_ne _ hs, this, Finmap.lookup_insert]

theorem lookup_ext2_other {a b s : Sym} {x y : Val} {env : Env} (ha : s.key ≠ a.key)
    (hb : s.key ≠ b.key) : (extendEnv [(a, x), (b, y)] env).lookup s = env.lookup s := by
  have ha' : MapKey.key s ≠ MapKey.key a := ha
  have hb' : MapKey.key s ≠ MapKey.key b := hb
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [Finmap.lookup_insert_of_ne _ ha', Finmap.lookup_insert_of_ne _ hb']

/-- The body of a recognised callee, entered with its return frame, returns to the caller. -/
theorem body_gives {body : EE} {c : Option Term} (hbody : BodyOf file body c)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Gives (file := file) (labels := labels)
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: k, m⟩ k m.stdout c := by
  cases c with
  | none =>
    obtain ⟨m', out, r⟩ := voidBody_returns (file := file) (labels := labels) hbody env k m
    exact ⟨m', out, r.trans (CallReach.return_reaches .unit _ k m')⟩
  | some t =>
    rcases intBody_returns (file := file) (labels := labels) hbody env k m with
      ⟨ok, m', out, r⟩ | ub
    · exact .inl ⟨ok, m', out, r.trans (CallReach.return_reaches _ _ k m')⟩
    · exact .inr ub

/-- **A call `g()`** reaches what `g` returns. -/
theorem call_gives {e : EE} {g : Sym} {isInt : Bool} {c : Option Term}
    (hs : callSite file e = some (g, isInt)) (hc : callee file g isInt = some c)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Gives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout c := by
  obtain ⟨loc, attrs, fty, variadic, proto, dloc, marker, bt, body, hstd, hinfo, hdecl, hfk, hbody⟩ :=
    callee_spec hc
  unfold callSite at hs
  split at hs
  · rename_i ann pann p pbt fann vann g' lann tann fa fty' fbt pa pty pbt' w1a w1 w2a w2 cann cpann
      p₁ iann oann lenann len lnann pty₁ zann z iann' cpa cva rty cfa fty₁ ccann mt pann₂ p₂ no1 no2
    split at hs
    · rename_i cond
      obtain ⟨hp₁, hp₂, hpty, hfty, hne, hpf, hpp, rfl, hlen⟩ := cond
      have hrk : retKind rty = some isInt ∧ g' = g := by
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
      have o := body_gives (file := file) (labels := labels) hbody env₂ k (SeqReach.focusMemory ccann m₄)
      have hst : (SeqReach.focusMemory ccann m₄).stdout = m.stdout := by simp [m₄, m₃, m₂, m₁]
      rw [hst] at o
      refine Gives.pre ?_ o
      refine (SeqReach.sseq_pure_reaches ann fann (pat := .mk pann (.base (some p, pbt))) (xs := [(p, fp)])
        (SeqReach.pure_value vann (.loaded (.specified (.pointer (.function g')))) env) rfl k m).trans ?_
      refine (SeqReach.effect_let_reaches lann (cfunction_reaches l1 hinfo) hmatch k m₁).trans ?_
      refine (SeqReach.effect_if_reaches iann true (pureEval_of (length_eval hlen l2)) k m₂).trans ?_
      refine (SeqReach.effect_if_reaches iann' true (compatible_reaches hrk hfk l3) k m₃).trans ?_
      exact CallReach.ccall_reaches ccann mt (SeqReach.pure_symbol pann₂ p₂ env₂ fp l4) .nil
        (CallReach.procedure_not_builtin hdecl) (CallReach.procedure_body hstd hdecl rfl) k m₄
    · cases hs
  · cases hs

/-! ## `main` -/

/-- **`return g();`** halts with what `g` returns, or reaches undefined behaviour. -/
theorem retCall_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) {g : Sym} {t : Term}
    (h : retCall file ret e = some (g, t)) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold retCall at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i g' hsite
        split at h
        · rename_i t' hcallee
          cases h
          let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
          let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
                k, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine LocalExpr.Shows.pre pre ?_
          rcases call_gives (labels := labels) hsite hcallee env (.bound :: kR) m with
            ⟨ok, m₁, out₁, r⟩ | ⟨s', r, hs'⟩
          · left
            refine ⟨ok, ?_⟩
            let v : Val := IntExpr.spec (t.val 0)
            let env₁ := extendEnv [(u, v)] env
            have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₁)) env₁
                (.inl (.mk cann () (.call (.sym s)
                  [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                    .mk a3 () (.sym u')])))
                (.inl v) :=
              ConvInt.convLoadedInt_eval (ann := tyann) hs
                (IntExpr.Term.ok_int ReturnExpr.isInt_zero t ok)
                (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
            obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk
              (ReturnConst.focusMemory rann m₁)
            refine ⟨m', by simp [out, out₁], ?_⟩
            refine r.trans ((LocalExpr.value_bound_reaches v kR m₁).trans ?_)
            refine (ReturnLit.bind_reaches pann u ty v R env k m₁).trans ?_
            refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
            exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
          · exact .inr ⟨s', r, hs'⟩
        · cases h
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retCall_halts hret a h env (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m)
  · cases h
termination_by sizeOf e

/-- **`g(); return e;`** halts with the value of `e`, or reaches undefined behaviour. -/
theorem stmtCall_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) {g : Sym}
    {c : Option Term} {t : Term} (h : stmtCall file ret e = some (g, c, t)) (env : Env)
    {k : List Frame} (hk : NoBoundary k) (m : Mem.Concrete.State) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold stmtCall at h
  split at h
  · rename_i _ ann pann ty sann pann' ty' bann e' u rest
    split at h
    · rename_i hu
      split at h
      · rename_i g' isInt hsite
        cases hcallee : callee file g' isInt with
        | none => simp [hcallee] at h
        | some c' =>
          cases hterm : ReturnExpr.retTerm file ret rest with
          | none => simp [hcallee, hterm] at h
          | some t' =>
              simp only [hcallee, hterm, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hg, hc, ht⟩ := h
              rw [hg] at hsite
              rw [hg, hc] at hcallee
              rw [ht] at hterm
              let k1 := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
              let k2 := Frame.strongBind (.mk pann' (.base (none, ty'))) u env :: k1
              have pre : Reaches file labels ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (none, ty)))
                  (.mk sann (.sseq (.mk pann' (.base (none, ty'))) (.mk bann (.bound e')) u)) rest)) env, k, m⟩
                  ⟨.effectExpr e' env, .bound :: k2, m⟩ :=
                (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans
                  ((ReturnConst.sequence_reaches file labels sann _ _ u env k1 m).trans
                    (ReturnLit.bound_reaches bann e' env k2 m))
              refine LocalExpr.Shows.pre pre ?_
              have after : ∀ (w : Val) (m₁ : Mem.Concrete.State), m₁.stdout = m.stdout →
                  Shows (file := file) (labels := labels) ⟨.value w, .bound :: k2, m₁⟩ 0 t m.stdout := by
                intro w m₁ out₁
                obtain ⟨m₂, out₂, ru⟩ := ReturnConst.skip_reaches file labels u hu env k1 m₁
                have o := ReturnExpr.retTerm_halts (file := file) hret rest t hterm env hk m₂
                rw [out₂, out₁] at o
                exact LocalExpr.Shows.pre ((LocalExpr.value_bound_reaches w k2 m₁).trans
                  ((ReturnConst.wildcard_sequence_reaches file labels pann' ty' w u env k1 m₁).trans
                    (ru.trans (ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m₂))))
                  o
              cases c with
              | none =>
                obtain ⟨m₁, out₁, r⟩ := call_gives (labels := labels) hsite hcallee env (.bound :: k2) m
                exact LocalExpr.Shows.pre r (after _ m₁ out₁)
              | some tc =>
                rcases call_gives (labels := labels) hsite hcallee env (.bound :: k2) m with
                  ⟨-, m₁, out₁, r⟩ | ⟨s', r, hs'⟩
                · exact LocalExpr.Shows.pre r (after _ m₁ out₁)
                · exact .inr ⟨s', r, hs'⟩
      · cases h
    · cases h
  · cases h

/-- **`return g(), e;`** halts with the value of `e`, or reaches undefined behaviour. -/
theorem retComma_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) {g : Sym}
    {c : Option Term} {t : Term} (h : retComma file ret e = some (g, c, t)) (env : Env)
    {k : List Frame} (hk : NoBoundary k) (m : Mem.Concrete.State) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold retComma at h
  split at h
  · rename_i _ ann pann u ty bann sann wann wty e' e₂ rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i g' isInt hsite
        cases hcallee : callee file g' isInt with
        | none => simp [hcallee] at h
        | some c' =>
          cases hτ : IntExpr.term file u e₂ with
          | none => simp [hcallee, hτ] at h
          | some t' =>
            by_cases hr : t'.reads = false
            · simp only [hcallee, hτ, hr, ite_true, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hg, hc, ht⟩ := h
              rw [hg] at hsite
              rw [hg, hc] at hcallee
              rw [ht] at hτ hr
              have none₁ : ∀ {P : Prop}, t.reads = true → P := fun r => by rw [hr] at r; cases r
              let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
                [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
              let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
              let k₂ := Frame.strongBind (.mk wann (.base (none, wty))) e₂ env :: .bound :: kR
              have pre : Reaches file labels
                  ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty)))
                    (.mk bann (.bound (.mk sann (.sseq (.mk wann (.base (none, wty))) e' e₂)))) R)) env,
                    k, m⟩ ⟨.effectExpr e' env, k₂, m⟩ :=
                (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
                  ((ReturnLit.bound_reaches bann _ env _ m).trans
                    (ReturnConst.sequence_reaches file labels sann _ e' e₂ env _ m))
              refine LocalExpr.Shows.pre pre ?_
              have after : ∀ (w : Val) (m₁ : Mem.Concrete.State), m₁.stdout = m.stdout →
                  Shows (file := file) (labels := labels) ⟨.value w, k₂, m₁⟩ 0 t m.stdout := by
                intro w m₁ out₁
                refine LocalExpr.Shows.pre
                  (ReturnConst.wildcard_sequence_reaches file labels wann wty w e₂ env _ m₁) ?_
                by_cases ok : t.Ok 0
                · left
                  refine ⟨ok, ?_⟩
                  obtain ⟨xs, m₂, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
                    (labels := labels) (env := env) (id := 0) (addr := 0) t hτ none₁
                    ReturnExpr.isInt_zero ok (.bound :: kR) m₁ none₁
                  let v : Val := IntExpr.spec (t.val 0)
                  have popped : Reaches file labels ⟨.value v, fr ++ .bound :: kR, m₂⟩
                      ⟨.value v, kR, m₂⟩ := by
                    rcases hfr with ⟨rfl, -⟩ | rfl
                    · exact LocalExpr.value_bound_reaches v kR m₂
                    · exact Locals.annotations_bound_reaches xs v kR m₂
                  let env₁ := extendEnv [(u, v)] env
                  have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₂)) env₁
                      (.inl (.mk cann () (.call (.sym s)
                        [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                          .mk a3 () (.sym u')])))
                      (.inl v) :=
                    ConvInt.convLoadedInt_eval (ann := tyann) hs
                      (IntExpr.Term.ok_int ReturnExpr.isInt_zero t ok)
                      (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
                  obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk
                    (ReturnConst.focusMemory rann m₂)
                  refine ⟨m', by simp [out, tch.stdout, out₁], ?_⟩
                  refine (Interleave.reaches_of_local file labels run).trans (popped.trans ?_)
                  refine (ReturnLit.bind_reaches pann u ty v R env k m₂).trans ?_
                  refine (Straight.focus_reaches (m := m₂) Straight.request_run).trans ?_
                  exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
                · right
                  exact ArenaFail.fail_reaches file labels
                    (IntExpr.term_fails (file := file) (labels := labels) (env := env) (id := 0)
                      (addr := 0) t hτ none₁ ReturnExpr.isInt_zero ok (.bound :: kR) m₁ none₁)
              cases c with
              | none =>
                obtain ⟨m₁, out₁, r⟩ := call_gives (labels := labels) hsite hcallee env k₂ m
                exact LocalExpr.Shows.pre r (after _ m₁ out₁)
              | some tc =>
                rcases call_gives (labels := labels) hsite hcallee env k₂ m with
                  ⟨-, m₁, out₁, r⟩ | ⟨s', r, hs'⟩
                · exact LocalExpr.Shows.pre r (after _ m₁ out₁)
                · exact .inr ⟨s', r, hs'⟩
            · simp [hcallee, hτ, hr] at h
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retComma_halts hret a h env (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m)
  · cases h
termination_by sizeOf e

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (pl : Plan) (h : recognize doc = some pl)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s 0 pl.result "" := by
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
          have hbody : recognizeBody doc.file body = some pl := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hentry⟩ := StartupReach.initial_reaches_body
            doc.file enums args hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]; exact ReturnLit.returnLabel_body hr hfree
              let SAVE : EE :=
                .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
              let k : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
              have hk : NoBoundary k := by simp [k, NoBoundary, hasBoundary]
              have o : Shows (file := doc.file) (labels := labels) ⟨.effectExpr a ∅, k, m⟩ 0
                  pl.result m.stdout := by
                split at hbody
                · rename_i g t hrc
                  cases hbody
                  exact retCall_halts hret a hrc ∅ hk m
                · cases hsc : stmtCall doc.file ret a with
                  | some x =>
                    obtain ⟨g, c, t⟩ := x
                    simp [hsc] at hbody
                    subst hbody
                    exact stmtCall_halts hret a hsc ∅ hk m
                  | none =>
                    cases hcm : retComma doc.file ret a with
                    | none => simp [hsc, hcm] at hbody
                    | some x =>
                      obtain ⟨g, c, t⟩ := x
                      simp [hsc, hcm] at hbody
                      subst hbody
                      exact retComma_halts hret a hcm ∅ hk m
              rw [hout] at o
              exact ⟨s, labels, hinit, LocalExpr.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with the value
of the returned expression mod 256 and no output. -/
theorem recognize_sound (doc : Codec.Document) (pl : Plan) (h : recognize doc = some pl)
    (args : List String) :
    Spec.CoreUB doc args ∨ pl.result.Ok 0 ∧
      Spec.CoreBeh doc args (.exit (pl.result.val 0 % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc pl h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (pl.result.val 0 % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.Call
