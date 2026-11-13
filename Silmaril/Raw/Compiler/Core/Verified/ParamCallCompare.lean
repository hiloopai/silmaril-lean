module

public import Silmaril.Compiler.Core.Verified.CallParamLocal.Defs
public import Silmaril.Compiler.Core.Verified.CallArgLink.Defs
public import Silmaril.Compiler.Core.Verified.ClosedEffAny.Defs
/-! # A mutable-parameter call as the left operand of an integer comparison -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ParamCallCompare

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons saveFree)
open ConvInt (IsInt isConvLoadedInt)
open IntExpr (Term spec)
open LocalExpr (Shows)

/-- One State-bodied callee, compared with a closed integer operand (`ClosedEff.flatLit`). -/
structure Plan where
  callee : Sym
  parameter : Sym
  argument : Int
  term : Term
  literal : Int
  rel : BinOp
  yes : Int
  no : Int

/-- Specialize the symbolic input, retaining all arithmetic operations. -/
def Plan.inst (p : Plan) : Term := StateSubst.subst (.lit p.argument) p.term

def Plan.result (p : Plan) : Term := .cmp p.rel p.yes p.no p.inst (.lit p.literal)
def Plan.caller (p : Plan) : Term := .cmp p.rel p.yes p.no .var (.lit p.literal)

/-- The operand recognizer reads syntax only; `J` bounds the callee's own locals. -/
def expr (file : File Codec.wireModel Unit Unit) (e : Eff) (J : Nat := 0) : Option Plan :=
  match e with
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [ec, rhs])) (.mk _ (.pure guard))) => do
      let n ← ClosedEff.flatLit file rhs
      if -2147483648 ≤ n ∧ n ≤ 2147483647 then
        let (g, input) ← CallArg.argSite file ec
        let (x, t) ← CallParam.calleeArg file g J
        let (r, y, z) ← StateExpr.cmpGuard' file a b guard
        pure ⟨g, x, input, t, n, r, y, z⟩
      else none
  | _ => none

variable {file : Program} {labels : Labels}

/-- The pure right operand finishes first; the full State callee then runs
inside the sole remaining operand, with overflow propagated out of the arena. -/
theorem operands {ec : EE} {g x : Sym} {t : Term} {n c : Int}
    (hs : CallArg.argSite file ec = some (g, n))
    (hc : CallParam.calleeArg file g = some (x, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < Mem.Concrete.nextIntAddress m) (hdead : m.nextId ∉ m.dead)
    {rhs : EE} (hrhs : ClosedEff.flatLit file rhs = some c) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr rhs env, [])], k, m⟩ ∨
    t.Ok n ∧ ∃ m' xs, m'.stdout = m.stdout ∧ CoreReaches file labels
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr rhs env, [])], k, m⟩
      ⟨.interleave [(0, spec (t.val n), xs), (1, spec c, [])] [], k, m'⟩ := by
  have pending : Pending [(0, .effectExpr ec env, [])] 1 :=
    ⟨by simp, by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact activeCall_effectExpr ec env⟩
  obtain ⟨l, literal⟩ := ClosedEff.flatLit_task file labels (taskFlag false k [(0, .effectExpr ec env, [])]) hrhs env m
  have first := reaches_of_local file labels
    (drive_task file labels pending (done := []) (k := k) (wc := false) literal)
  rcases CallParamLocal.call_in_arena (labels := labels) hs hc env
      {m with currentLocation := l} (by simpa [Mem.Concrete.nextIntAddress] using hpos)
      hdead [(1, spec c, [])] 0 k with ub | ⟨ok, m', xs, out, call⟩
  · exact .inl (StateStmt.Overflows.pre first ub)
  · exact .inr ⟨ok, m', xs, out, first.trans call⟩

theorem expr_parts {e : EE} {p : Plan} {J : Nat} (h : expr file e J = some p) :
    ∃ an pp p1 p2 au ag a b ta tb ec rhs guard,
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)),
        .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [ec, rhs])) (.mk ag (.pure guard))) ∧
      ClosedEff.flatLit file rhs = some p.literal ∧
      CallArg.argSite file ec = some (p.callee, p.argument) ∧
      CallParam.calleeArg file p.callee J = some (p.parameter, p.term) ∧ IsInt p.literal ∧
      StateExpr.cmpGuard' file a b guard = some (p.rel, p.yes, p.no) := by
  unfold expr at h
  split at h
  · rename_i an pp p1 a ta p2 b tb au ec rhs ag guard
    cases hr : ClosedEff.flatLit file rhs with
    | none => simp [hr, bind, Option.bind] at h
    | some n =>
      simp only [hr, bind, Option.bind] at h
      split at h
      · rename_i hn
        cases hs : CallArg.argSite file ec with
        | none => simp [hs] at h
        | some pair =>
          obtain ⟨g, input⟩ := pair
          cases hc : CallParam.calleeArg file g J with
          | none => simp [hs, hc] at h
          | some xt =>
            obtain ⟨x, t⟩ := xt
            cases hg : StateExpr.cmpGuard' file a b guard with
            | none => simp [hs, hc, hg] at h
            | some triple =>
              obtain ⟨r, y, z⟩ := triple
              simp [hs, hc, hg, pure] at h
              subst p
              exact ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, ec, rhs, guard,
                rfl, hr, hs, hc, hn, hg⟩
      · cases h
  · cases h

/-- A comparison consumes the real result of its operand call. -/
theorem expr_runs {e : EE} {p : Plan} (h : expr file e = some p)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < Mem.Concrete.nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    p.result.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reaches file labels
      ⟨.effectExpr e env, k, m⟩
      ⟨.value (spec (p.result.val 0)), .annotations xs :: k, m'⟩ := by
  obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, ec, rhs, guard,
    rfl, hrhs, hs, hc, hlit, hg⟩ := expr_parts h
  let pat : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
  let K := Frame.effectBind pat (.mk ag (.pure guard)) env :: k
  have start : Reaches file labels
      ⟨.effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec,
        rhs]))
          (.mk ag (.pure guard)))) env, k, m⟩
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr (rhs) env, [])], K, m⟩ := by
    apply reaches_of_local file labels
    refine .head (.next (LoadTask.requestAux_wseq m an pat _ _ env k false)
      (LoadTask.plain_effectExpr _ _)) ?_
    exact .single (.next (requestAux_unseq file labels m au _ env K false)
      (plain_interleave _ _))
  rcases operands (labels := labels) hs hc env K m hpos hdead hrhs with ub | ⟨okt, m₁, xs, out₁, run⟩
  · exact .inl (StateStmt.Overflows.pre start ub)
  right
  have harg := CallArg.argSite_range hs
  have okt' : p.inst.Ok 0 := (StateSubst.subst_ok (.lit p.argument) p.term 0 harg).mpr okt
  have value : p.inst.val 0 = p.term.val p.argument := StateSubst.subst_val _ _ _
  have hn := IntExpr.Term.ok_int harg p.term okt
  have hok : p.result.Ok 0 := ⟨okt', hlit, StateExpr.cmpGuard'_int hg⟩
  refine ⟨hok, ?_⟩
  have finish : Reaches file labels
      ⟨.interleave [(0, spec (p.term.val p.argument), xs), (1, spec p.literal, [])] [], K, m₁⟩
      ⟨.value (.tuple [spec (p.term.val p.argument), spec p.literal]), .annotations xs :: K, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (by
      simpa using requestAux_end file labels m₁
        [(0, spec (p.term.val p.argument), xs), (1, spec p.literal, [])] K false (by simp [NoRace])
        (by simp))
      (LoadTask.plain_value _))
  have bind : Reaches file labels
      ⟨.value (.tuple [spec (p.term.val p.argument), spec p.literal]), .annotations xs :: K, m₁⟩
      ⟨.effectExpr (.mk ag (.pure guard)) (Guard.operands a b (p.term.val p.argument) p.literal env),
        .annotations xs :: k, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
      (LoadTask.plain_effectExpr _ _))
  refine ⟨ReturnConst.focusMemory ag m₁, xs, by simp [out₁], ?_⟩
  have final := start.trans (run.trans (finish.trans (bind.trans (reaches_of_local file labels
    (CallLocal.pure ag (fun _ => StateExpr.cmpGuard'_eval hg env hn hlit) _ _)))))
  simpa [Plan.result, IntExpr.Term.val, value] using final

def retCall (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option Plan
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ isConvLoadedInt file s = true then expr file e else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retCall file ret a
  | _ => none

theorem retCall_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) {p : Plan}
    (h : retCall file ret e = some p) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) (hpos : 0 < Mem.Concrete.nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 p.result m.stdout := by
  unfold retCall at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
        [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
      let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
      have pre : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
            k, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
          (ReturnLit.bound_reaches bann _ env _ m)
      rcases expr_runs (labels := labels) h env (.bound :: kR) m hpos hdead with ub | ⟨ok, m₁, xs, out₁, r⟩
      · exact .inr (StateStmt.Overflows.pre pre ub)
      left
      refine ⟨ok, ?_⟩
      let v : Val := spec (p.result.val 0)
      let env₁ := extendEnv [(u, v)] env
      have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₁)) env₁
          (.inl (.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
              .mk a3 () (.sym u')]))) (.inl v) :=
        ConvInt.convLoadedInt_eval (ann := tyann) hs
          (IntExpr.Term.ok_int ReturnExpr.isInt_zero p.result ok)
          (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
      obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk
        (ReturnConst.focusMemory rann m₁)
      refine ⟨m', by simp [out, out₁], ?_⟩
      refine pre.trans (r.trans ((Locals.annotations_bound_reaches xs v kR m₁).trans ?_))
      refine (ReturnLit.bind_reaches pann u ty v R env k m₁).trans ?_
      refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
      exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retCall_halts hret a h env
        (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m hpos hdead)
  · cases h
termination_by sizeOf e

/-- The call-site recognizer checks the literal argument's range even when the
callee's result is independent of that argument. -/
theorem retCall_range (ret : Sym) (e : EE) {p : Plan}
    (h : retCall file ret e = some p) : IsInt p.argument := by
  unfold retCall at h
  split at h
  · split at h
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := expr_parts h
      exact CallArg.argSite_range hs
    · cases h
  · exact retCall_range ret _ h
  · cases h
termination_by sizeOf e

def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Plan
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then retCall file ret a else none
  | _ => none

def recognize (doc : Codec.Document) : Option Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

theorem recognize_range (doc : Codec.Document) {p : Plan} (h : recognize doc = some p) :
    IsInt p.argument := by
  unfold recognize at h
  split at h
  · cases h
  cases hm : doc.file.main with
  | none => simp [hm] at h
  | some main =>
    cases hd : doc.file.funs.lookup main with
    | none => simp [hm, hd] at h
    | some decl =>
      cases decl <;> try { simp [hm, hd] at h }
      case procedure loc marker bt ps body =>
        cases ps with
        | cons _ _ => simp [hm, hd] at h
        | nil =>
          have hb : recognizeBody doc.file body = some p := by simpa [hm, hd] using h
          unfold recognizeBody at hb
          split at hb
          · split at hb
            · exact retCall_range _ _ hb
            · cases hb
          · cases hb

theorem recognize_reaches (doc : Codec.Document) (p : Plan) (h : recognize doc = some p)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s 0 p.result "" := by
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
              have o := retCall_halts hret a hbody ∅ hk m
                (Locals.errno_nextIntAddress hlast) (by simp [hdead])
              rw [hout] at o
              exact ⟨s, labels, hinit, LocalExpr.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

theorem recognize_sound (doc : Codec.Document) (p : Plan) (h : recognize doc = some p)
    (args : List String) :
    Spec.CoreUB doc args ∨ p.result.Ok 0 ∧
      Spec.CoreBeh doc args (.exit (p.result.val 0 % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc p h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (p.result.val 0 % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · exact .inl (.inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩)

/-- Fuse the pure comparison into the called function, retaining the runtime
parameter input and every operation of the callee's symbolic term. -/
def Plan.applied (p : Plan) : Term := .cmp p.rel p.yes p.no p.term (.lit p.literal)

def planLink (p : Plan) : Mir.Linked := CallArgLink.link p.argument p.applied

theorem planLink_sound (p : Plan) (harg : IsInt p.argument) (ok : p.result.Ok 0) {a : Spec.Artifact}
    (h : Backend.artifactOf (planLink p) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Spec.Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Spec.Obs}
    (hb : Spec.MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit ((BitVec.ofInt 64 (p.result.val 0)).toNat % 256) [] := by
  have ht : p.term.Ok p.argument :=
    (StateSubst.subst_ok (.lit p.argument) p.term 0 harg).mp ok.1
  have ho : p.applied.Ok p.argument := ⟨ht, ok.2⟩
  have value : p.applied.val p.argument = p.result.val 0 := by
    simp [Plan.applied, Plan.result, Plan.inst, Term.val, StateSubst.subst_val]
  simpa only [value] using CallArgLink.link_sound ho h hl hb

end Silmaril.Compile.Core.Verified.ParamCallCompare
