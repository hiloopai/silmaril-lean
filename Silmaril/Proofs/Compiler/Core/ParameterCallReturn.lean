module

public import Silmaril.Compiler.Core.ParameterCallReturn.Defs
public import Silmaril.Compiler.Core.CalleeReturn.Thms

@[expose] public section
namespace Silmaril.Compiler.Core.ParameterCallReturn
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Elaboration
open Construction Example
attribute [local cbv_eval] Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil

theorem source_elaborates : elaborated.1.toOption.isSome = true := by cbv

def bindings : Codec.FileBindings := elaborated.1.toOption.get source_elaborates
def file : Program := bindings.toFile


open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open CallArg
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ConvInt (IsInt)
open Mem.Concrete (IntRange nextIntAddress LiveInt)
open Locals (Slot)
open IntExpr (Term)
open LoadTask (Touched ReadTask)
open Call (retKind)

section SuccessfulReturn
variable {file : Program} {labels : Labels}

/-- Unlike the imported success-or-UB contract, an explicitly defined integer
term has an actual successful return path. It reads the actual supplied Slot. -/
theorem retTermArg_returns_of_ok {ret x : Sym} {L : Labels} (hret : ReturnLabel L ret)
    (e : EE) (t : Term) (recognized : retTermArg file ret x e = some t)
    (env : Env) {localFrames : List Frame} (boundary : NoBoundary localFrames)
    (caller : List Frame) (memory : Mem.Concrete.State) {id addr n : Int}
    (parameter : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (bounds : IntRange n) (slot : Slot memory id addr n) (ok : t.Ok n) :
    ∃ finish, Touched memory finish ∧ Reaches file labels
      ⟨.effectExpr e env, localFrames ++ .procedureReturn L :: caller, memory⟩
      ⟨.value (IntExpr.spec (t.val n)), .procedureReturn L :: caller, finish⟩ := by
  unfold retTermArg at recognized
  split at recognized
  next _ ann pann u ty bann child rann label cann conversion a2 tyann a3 occurrence =>
    show ∃ finish, Touched memory finish ∧ Reaches file labels
      ⟨.effectExpr _ env, localFrames ++ .procedureReturn L :: caller, memory⟩
      ⟨.value (IntExpr.spec (t.val n)), .procedureReturn L :: caller, finish⟩
    split at recognized
    next accepted =>
      show ∃ finish, Touched memory finish ∧ Reaches file labels
        ⟨.effectExpr _ env, localFrames ++ .procedureReturn L :: caller, memory⟩
        ⟨.value (IntExpr.spec (t.val n)), .procedureReturn L :: caller, finish⟩
      obtain ⟨sameLabel, sameTemporary, runtime⟩ := accepted
      let ending : EE := .mk rann (.run () label [.mk cann () (.call (.sym conversion)
        [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
         .mk a3 () (.sym occurrence)])])
      let continuation := Frame.strongBind (.mk pann (.base (some u, ty))) ending env ::
        (localFrames ++ .procedureReturn L :: caller)
      obtain ⟨annotations, middle, extraFrames, shape, -, touched, evaluated⟩ :=
        IntExpr.term_runs (file := file) (labels := labels) t recognized (fun _ => parameter)
          bounds ok (.bound :: continuation) memory (fun _ => slot)
      let value := IntExpr.spec (t.val n)
      have popped : Reaches file labels ⟨.value value, extraFrames ++ .bound :: continuation, middle⟩
          ⟨.value value, continuation, middle⟩ := by
        rcases shape with ⟨rfl, -⟩ | rfl
        · exact LocalExpr.value_bound_reaches value continuation middle
        · exact Locals.annotations_bound_reaches annotations value continuation middle
      let extended := extendEnv [(u, value)] env
      have conversionEval : Eval file (tagsOf file (ReturnConst.focusMemory rann middle)) extended
          (.inl (.mk cann () (.call (.sym conversion)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
             .mk a3 () (.sym occurrence)]))) (.inl value) :=
        ConvInt.convLoadedInt_eval (ann := tyann) runtime (IntExpr.Term.ok_int bounds t ok)
          (.cons .val (.cons (.sym (ConvInt.lookup_one sameTemporary)) .nil))
      obtain ⟨finish, lastTouched, returned⟩ := jump_returns' (file := file) (labels := labels)
        sameLabel hret value extended boundary caller (ReturnConst.focusMemory rann middle)
      have entered : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty)))
            (.mk bann (.bound child)) ending)) env,
            localFrames ++ .procedureReturn L :: caller, memory⟩
          ⟨.effectExpr child env, .bound :: continuation, memory⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env _ memory).trans
          (ReturnLit.bound_reaches bann child env _ memory)
      have computed : Reaches file labels ⟨.effectExpr child env, .bound :: continuation, memory⟩
          ⟨.value value, continuation, middle⟩ :=
        (Interleave.reaches_of_local file labels evaluated).trans popped
      refine ⟨finish, touched.trans ((LoadTask.focusMemory_touched rann middle).trans lastTouched), ?_⟩
      refine entered.trans (computed.trans ?_)
      refine (ReturnLit.bind_reaches pann u ty value ending env _ middle).trans ?_
      refine (Straight.focus_reaches (m := middle) Straight.request_run).trans ?_
      exact ((Eval.sound file _ conversionEval) labels _ _ rfl).trans returned
    next rejected => cases recognized
  next _ ann pann ty first rest =>
    obtain ⟨finish, touched, returned⟩ := retTermArg_returns_of_ok hret first t recognized env
      (localFrames := .strongBind (.mk pann (.base (none, ty))) rest env :: localFrames)
      (noBoundary_cons boundary trivial) caller memory parameter bounds slot ok
    exact ⟨finish, touched,
      (ReturnConst.sequence_reaches file labels ann _ first rest env _ memory).trans returned⟩
  next => cases recognized
termination_by sizeOf e

/-- A recognized one-parameter callee with a defined term returns successfully
through its actual procedure boundary, preserving arbitrary caller frames. -/
theorem argBody_returns_of_ok {x : Sym} {body : EE} {t : Term}
    (recognized : argBody file x body = some t) (env : Env) (caller : List Frame)
    (memory : Mem.Concrete.State) {id addr n : Int}
    (parameter : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (bounds : IntRange n) (slot : Slot memory id addr n) (ok : t.Ok n) :
    ∃ finish, Touched memory finish ∧ Reaches file labels
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: caller, memory⟩
      ⟨.value (IntExpr.spec (t.val n)), caller, finish⟩ := by
  unfold argBody at recognized
  split at recognized
  next ann pann bt first sann ret rbt r info bann pann' occurrence =>
    split at recognized
    next accepted =>
      obtain ⟨same, saveFree⟩ := accepted
      obtain ⟨finish, touched, returned⟩ := retTermArg_returns_of_ok (file := file) (labels := labels)
        (ReturnLit.returnLabel_body same saveFree) first t recognized env
        (localFrames := [.strongBind (.mk pann (.base (none, bt))) _ env])
        (by simp [NoBoundary, hasBoundary]) caller memory parameter bounds slot ok
      exact ⟨finish, touched,
        (ReturnConst.sequence_reaches file labels ann _ first _ env _ memory).trans
          (returned.trans (CallReach.return_reaches _ _ caller finish))⟩
    next rejected => cases recognized
  next => cases recognized
end SuccessfulReturn

section SuccessfulCall
variable {file : Program} {labels : Labels}

/-- The actual static integer kill records the allocation ID as dead. -/
theorem killInt_records_dead {x : Sym} {expression : EE}
    (recognized : Locals.killInt x expression = true) (environment : Env) (frames : List Frame)
    (memory : Mem.Concrete.State) {id addr : Int}
    (pointer : environment.lookup x = some (.object (.pointer (.allocated id addr))))
    (live : LiveInt memory id addr) :
    ∃ finish, finish.stdout = memory.stdout ∧ id ∈ finish.dead ∧ Reaches file labels
      ⟨.effectExpr expression environment, frames, memory⟩ ⟨.value .unit, frames, finish⟩ := by
  unfold Locals.killInt at recognized
  split at recognized
  next _ annotations location payload typeAnnotations pointerAnnotations occurrence =>
    have lookup : environment.lookup occurrence = some (.object (.pointer (.allocated id addr))) := by
      rw [ReturnLit.lookup_key (of_decide_eq_true recognized)]; exact pointer
    refine ⟨Locals.killed (ReturnConst.focusMemory annotations memory) id, ?_, ?_,
      Locals.kill_reaches annotations pointerAnnotations typeAnnotations location payload occurrence
        environment frames memory lookup live⟩
    · simp [Locals.killed]
    · simp [Locals.killed]
  next => cases recognized

/-- The emitted caller cleanup kills the same object whose pointer it holds. -/
theorem killTail_records_dead {x r : Sym} {expression : EE}
    (recognized : killTail x r expression = true) (environment : Env) (frames : List Frame)
    (memory : Mem.Concrete.State) {id addr : Int} {value : Val}
    (pointer : environment.lookup x = some (.object (.pointer (.allocated id addr))))
    (result : environment.lookup r = some value) (live : LiveInt memory id addr) :
    ∃ finish, finish.stdout = memory.stdout ∧ id ∈ finish.dead ∧ Reaches file labels
      ⟨.effectExpr expression environment, frames, memory⟩ ⟨.value value, frames, finish⟩ := by
  unfold killTail at recognized
  split at recognized
  next _ annotations patternAnnotations type kill pureAnnotations symbolAnnotations occurrence =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at recognized
    obtain ⟨recognizedKill, same⟩ := recognized
    obtain ⟨middle, stdout, dead, killed⟩ := killInt_records_dead (file := file) (labels := labels)
      recognizedKill environment (.strongBind (.mk patternAnnotations (.base (none, type)))
        (.mk pureAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence)))) environment :: frames)
      memory pointer live
    refine ⟨SeqReach.focusMemory pureAnnotations middle, by simp [stdout], ?_, ?_⟩
    · rw [touched_dead (touched_seq pureAnnotations middle)]; exact dead
    refine (ReturnConst.sequence_reaches file labels annotations _ kill _ environment frames memory).trans
      (killed.trans ?_)
    refine (ReturnConst.wildcard_sequence_reaches file labels patternAnnotations type .unit _
      environment frames middle).trans ?_
    exact SeqReach.effect_pure_reaches pureAnnotations
      (SeqReach.pure_symbol symbolAnnotations occurrence environment value
        (by rw [ReturnLit.lookup_key same]; exact result)) frames middle
  next => cases recognized

/-- Actual call dispatch, successful callee load/return and emitted cleanup. -/
theorem callTail_returns_of_ok {p x : Sym} {e : EE} (h : callTail p x e = true) {g x0 : Sym} {t : Term}
    (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) (ok : t.Ok n) :
    ∃ m', m'.stdout = m.stdout ∧ id ∈ m'.dead ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value (IntExpr.spec (t.val n)), k, m'⟩ := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, -, -,
    hbody⟩ := calleeArg_spec hc
  unfold callTail at h
  split at h
  next _ ann rann r rt cann mt pann p₁ xann x₁ kt =>
    show ∃ finish, finish.stdout = m.stdout ∧ id ∈ finish.dead ∧
      Reaches file labels ⟨.effectExpr _ env, k, m⟩
        ⟨.value (IntExpr.spec (t.val n)), k, finish⟩
    have accepted : (p₁.key = p.key ∧ x₁.key = x.key ∧ x.key ≠ r.key) ∧
        killTail x r kt = true := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    obtain ⟨⟨hp₁, hx₁, hxr⟩, hkt⟩ := accepted
    let ptr : Val := .object (.pointer (.allocated id addr))
    let K := Frame.strongBind (.mk rann (.base (some r, rt))) kt env :: k
    have enter : Reaches file labels
        ⟨.effectExpr (.mk ann (.sseq (.mk rann (.base (some r, rt)))
          (.mk cann (.ccall () mt (.mk pann () (.sym p₁)) [.mk xann () (.sym x₁)])) kt)) env, k, m⟩
        ⟨.effectExpr body (extendEnv [(x0, ptr)] env),
          .procedureReturn (CallReach.bodyLabels body) :: K, SeqReach.focusMemory cann m⟩ :=
      (ReturnConst.sequence_reaches file labels ann _ _ kt env k m).trans
      (CallReach.ccall_reaches (file := file) (labels := labels) (args := [ptr]) cann mt
        (SeqReach.pure_symbol pann p₁ env _ (by rw [ReturnLit.lookup_key hp₁]; exact hp))
        (.cons (SeqReach.pure_symbol xann x₁ env _ (by rw [ReturnLit.lookup_key hx₁]; exact hx)) .nil)
        (CallReach.procedure_not_builtin hdecl)
        (CallReach.procedure_body (values := [ptr]) hstd hdecl rfl) K m)
    obtain ⟨m₁, tch, r₁⟩ := argBody_returns_of_ok (file := file) (labels := labels) hbody
      (extendEnv [(x0, ptr)] env) K (SeqReach.focusMemory cann m) (ConvInt.lookup_one rfl)
      hn ((touched_seq cann m).slot slot) ok
    let v := IntExpr.spec (t.val n)
    let env₁ := extendEnv [(r, v)] env
    have hx' : env₁.lookup x = some ptr := by
      rw [ConvInt.lookup_one_other hxr]; exact hx
    obtain ⟨m₂, out₂, dead, rk⟩ := killTail_records_dead (file := file) (labels := labels) hkt env₁ k m₁ hx'
      (ConvInt.lookup_one rfl) (touched_live tch (touched_live (touched_seq cann m) slot.live))
    refine ⟨m₂, by rw [out₂, tch.stdout]; simp, dead, ?_⟩
    exact enter.trans (r₁.trans ((SeqReach.strong_bind_reaches rfl k m₁).trans rk))
  next => cases h

theorem restArg_returns_of_ok {pty a p : Sym} {e : EE} (h : restArg file pty a p e = true) {g x0 : Sym}
    {t : Term} (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {c : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : retKind c = some true)
    (ha : env.lookup a = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) (ok : t.Ok n) :
    ∃ m' zs, m'.stdout = m.stdout ∧ m.nextId ∈ m'.dead ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (IntExpr.spec (t.val n)), .annotations zs :: k, m'⟩ := by
  unfold restArg at h
  split at h
  · rename_i _ ann xann x xbt la ct
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpx, hla⟩, hct⟩ := h
    obtain ⟨m₁, ys, out₁, slot₁, r₁⟩ := letArg_reaches (file := file) (labels := labels) hla env
      (.strongBind (.mk xann (.base (some x, xbt))) ct env :: k) m hpty hcint ha hn hpos hdead
    let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
    let env₁ := extendEnv [(x, ptr)] env
    have pre := (ReturnConst.sequence_reaches file labels ann _ la ct env k m).trans
      (r₁.trans (annotations_sbind_reaches ys (bs := [(x, ptr)]) rfl ct env k m₁))
    obtain ⟨m₂, out₂, dead, r₂⟩ := callTail_returns_of_ok (file := file) (labels := labels) hct hc env₁
      (.annotations ys :: k) m₁ (by rw [ConvInt.lookup_one_other hpx]; exact hp)
      (ConvInt.lookup_one rfl) hn slot₁ ok
    exact ⟨m₂, ys, by rw [out₂, out₁], dead, pre.trans r₂⟩
  · cases h

theorem guards_return_of_ok {fty pty vs a p : Sym} {e : EE} (h : guards file fty pty vs a p e = true)
    {g x0 : Sym} {t : Term} (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {c frt : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : retKind c = some true)
    (hvs : env.lookup vs = some .false) (hfty : env.lookup fty = some (.ctype frt))
    (hfrt : retKind frt = some true)
    (ha : env.lookup a = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) (ok : t.Ok n) :
    ∃ m' zs, m'.stdout = m.stdout ∧ m.nextId ∈ m'.dead ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (IntExpr.spec (t.val n)), .annotations zs :: k, m'⟩ := by
  unfold guards at h
  split at h
  · rename_i _ i1ann c1a c1b c1c len c1d pty₁ c1e one u1 i2ann c2a c2b vs₁ c2c c2d c2e rty c2f fty₁
      u2 rest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty₁, hvs₁, hfty₁, rfl⟩, hlen⟩, hrty⟩, hrest⟩ := h
    let m₁ := SeqReach.focusMemory i1ann m
    let m₂ := SeqReach.focusMemory i2ann m₁
    have T : Touched m m₂ := (touched_seq i1ann m).trans (touched_seq i2ann m₁)
    obtain ⟨finish, annotations, stdout, dead, returned⟩ := restArg_returns_of_ok (file := file) (labels := labels) hrest hc env k m₂ hp hpty hcint ha hn
      (by rw [touched_nextIntAddress T]; exact hpos) (by rw [touched_nextId T, touched_dead T]; exact hdead) ok
    refine ⟨finish, annotations, stdout.trans T.stdout, ?_, ?_⟩
    · rw [← touched_nextId T]; exact dead
    refine Relation.ReflTransGen.trans ?_ returned
    refine (SeqReach.effect_if_reaches i1ann false
      (Call.pureEval_of (length_one_eval hlen ((ReturnLit.lookup_key hpty₁).trans hpty))) k m).trans ?_
    exact SeqReach.effect_if_reaches i2ann false (variadicCheck_reaches hrty hfrt
      ((ReturnLit.lookup_key hvs₁).trans hvs) ((ReturnLit.lookup_key hfty₁).trans hfty)) k m₁
  · cases h

theorem argCall_returns_of_ok {e : EE} {g x0 : Sym} {n : Int} {t : Term}
    (hs : argSite file e = some (g, n)) (hc : calleeArg file g = some (x0, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m)
    (hdead : m.nextId ∉ m.dead) (ok : t.Ok n) :
    ∃ m' zs, m'.stdout = m.stdout ∧ m.nextId ∈ m'.dead ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (IntExpr.spec (t.val n)), .annotations zs :: k, m'⟩ := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, hfr, hfp,
    hbody⟩ := calleeArg_spec hc
  unfold argSite at hs
  split at hs
  next _ eA pA pA1 pA2 p pT pA3 fA fty fT psA pty psT vA vs vT prA pr prT aA a aT uA t1 T2 gd =>
    show ∃ finish annotations, finish.stdout = m.stdout ∧ m.nextId ∈ finish.dead ∧
      Reaches file labels ⟨.effectExpr _ env, k, m⟩
        ⟨.value (IntExpr.spec (t.val n)), .annotations annotations :: k, finish⟩
    split at hs
    next g' hfn =>
      show ∃ finish annotations, finish.stdout = m.stdout ∧ m.nextId ∈ finish.dead ∧
        Reaches file labels ⟨.effectExpr _ env, k, m⟩
          ⟨.value (IntExpr.spec (t.val n)), .annotations annotations :: k, finish⟩
      split at hs
      next n' hlit =>
        show ∃ finish annotations, finish.stdout = m.stdout ∧ m.nextId ∈ finish.dead ∧
          Reaches file labels ⟨.effectExpr _ env, k, m⟩
            ⟨.value (IntExpr.spec (t.val n)), .annotations annotations :: k, finish⟩
        split at hs
        next cond =>
          show ∃ finish annotations, finish.stdout = m.stdout ∧ m.nextId ∈ finish.dead ∧
            Reaches file labels ⟨.effectExpr _ env, k, m⟩
              ⟨.value (IntExpr.spec (t.val n)), .annotations annotations :: k, finish⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
          obtain ⟨⟨⟨⟨nfp, npp, npf, nvp, nvf, nvpt⟩, nap, naf, napt, nav, napr⟩, lo, hi⟩, hgd⟩ := cond
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨hg, hnn⟩ := hs
          subst hg hnn
          have hn : IntRange n' := ⟨lo, hi⟩
          let fp : Val := .loaded (.specified (.pointer (.function g')))
          let lit : Val := .loaded (.specified (.integer n'))
          let info := fnInfo g' frt [(po, fpt)] false proto
          let val : EE → Val := fun e => if isPure e then lit else info
          obtain ⟨hpure, hread⟩ := fnTask_spec (file := file) (labels := labels) hfn (fun _ => True) hinfo env
          obtain ⟨hpure₂, -, hread₂⟩ := argLit_spec (file := file) (labels := labels) hlit (fun _ => True) env
          have tasks : ∀ e ∈ [t1, T2], ReadTask (file := file) (labels := labels) (fun _ => True) env e
              (val e) := by
            intro e he
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl
            · simpa [val, hpure] using hread
            · simpa [val, hpure₂] using hread₂
          have hvals : [t1, T2].map val = [info, lit] := by
            show [val t1, val T2] = [info, lit]
            simp only [val, hpure, hpure₂, Bool.false_eq_true, ↓reduceIte]
          let PAT : Pattern Sym := .mk pA (.ctor .tuple [.mk pA1 (.ctor .tuple [.mk pA2 (.base (some p, pT)),
            .mk pA3 (.ctor .tuple [.mk fA (.base (some fty, fT)), .mk psA (.base (some pty, psT)),
              .mk vA (.base (some vs, vT)), .mk prA (.base (some pr, prT))])]), .mk aA (.base (some a, aT))])
          obtain ⟨xs, m₁, -, tch₁, run⟩ := LoadTask.unseq_reads (file := file) (labels := labels)
            (k := .strongBind PAT gd env :: k) (annots := uA) (fun _ => True) (fun _ _ _ _ => trivial) val
            tasks m trivial
          rw [hvals] at run
          let bs : Bindings := [(p, fp), (fty, .ctype frt), (pty, .list .ctype [.ctype fpt]),
            (vs, boolean false), (pr, boolean proto), (a, lit)]
          let env₁ := extendEnv bs env
          have pre : Reaches file labels ⟨.effectExpr (.mk eA (.sseq PAT (.mk uA (.unseq [t1, T2])) gd)) env, k, m⟩
              ⟨.effectExpr gd env₁, .annotations xs :: k, m₁⟩ :=
            (ReturnConst.sequence_reaches file labels eA PAT _ gd env k m).trans
              ((Interleave.reaches_of_local file labels run).trans
                (annotations_sbind_reaches xs (bs := bs) rfl gd env k m₁))
          have lp : env₁.lookup p = some fp := lookup_cons_eq rfl
          have lfty : env₁.lookup fty = some (.ctype frt) := by
            rw [lookup_cons_ne nfp]; exact lookup_cons_eq rfl
          have lpty : env₁.lookup pty = some (.list .ctype [.ctype fpt]) := by
            rw [lookup_cons_ne npp, lookup_cons_ne npf]; exact lookup_cons_eq rfl
          have lvs : env₁.lookup vs = some .false := by
            rw [lookup_cons_ne nvp, lookup_cons_ne nvf, lookup_cons_ne nvpt]; exact lookup_cons_eq rfl
          have la : env₁.lookup a = some lit := by
            rw [lookup_cons_ne nap, lookup_cons_ne naf, lookup_cons_ne napt, lookup_cons_ne nav,
              lookup_cons_ne napr]
            exact lookup_cons_eq rfl
          obtain ⟨m', zs, out, dead, returned⟩ := guards_return_of_ok (file := file) (labels := labels) hgd hc env₁ (.annotations xs :: k) m₁ lp lpty
            hfp lvs lfty hfr la hn (by rw [touched_nextIntAddress tch₁]; exact hpos)
            (by rw [touched_nextId tch₁, touched_dead tch₁]; exact hdead) ok
          exact ⟨m', zs ++ xs, out.trans tch₁.stdout,
            by rw [← touched_nextId tch₁]; exact dead, pre.trans (returned.trans (Locals.annotations_merge_reaches zs xs _ k m'))⟩
        next => cases hs
      next => cases hs
    next => cases hs
  next => cases hs

end SuccessfulCall


/-- Extract only the call subexpression from the actual successful elaboration. -/
def emittedCall : Option EE := do
  let .procedure _ _ _ []
    (.mk _ (.sseq _ (.mk _ (.sseq _ (.mk _ (.sseq _ (.mk _ (.bound expression)) _)) _)) _))
    ← file.funs.lookup mainSymbol | none
  pure expression

theorem source_call_exists : emittedCall.isSome = true := by cbv

def actualCall : EE := emittedCall.get source_call_exists

theorem source_call_recognized : CallArg.argSite file actualCall = some (fSymbol, 42) := by cbv

theorem source_callee_recognized :
    CallArg.calleeArg file fSymbol = some (parameterSymbol, .var) := by cbv

theorem runtime_length : CallArg.isParamsLength file length = true := by cbv
theorem runtime_nth : CallArg.isParamsNth file nth = true := by cbv
theorem runtime_conversion : ConvInt.isConvLoadedInt file conversion = true := by cbv

/-- Actual successful execution of the source-generated nonempty call. The
argument is evaluated, a real object is created/stored, dispatch binds its
pointer, the callee loads it, returns, and the caller executes cleanup. This
asserts an existential Core schedule; the extra annotations are actual accesses. -/
theorem source_call_returns (labels : Labels) (environment : Env) (frames : List Frame)
    (memory : Mem.Concrete.State) (positive : 0 < nextIntAddress memory)
    (fresh : memory.nextId ∉ memory.dead) :
    ∃ finish annotations, finish.stdout = memory.stdout ∧ memory.nextId ∈ finish.dead ∧
      Silmaril.Cerberus.Core.PureEval.Reaches file labels
        ⟨.effectExpr actualCall environment, frames, memory⟩
        ⟨.value (.loaded (.specified (.integer 42))), .annotations annotations :: frames, finish⟩ := by
  simpa [IntExpr.Term.val] using argCall_returns_of_ok source_call_recognized
    source_callee_recognized environment frames memory positive fresh (by trivial)

theorem source_freshness_actual : elaborated.2.freshness.next = 119 := by cbv

/-- The actual generated source site exposes the dynamic parameter-list and
loaded-argument names together with its actual preparation expression. -/
def emittedPreparation : Option (Sym × Sym × EE) := do
  let .mk _ (.sseq
    (.mk _ (.ctor .tuple [
      .mk _ (.ctor .tuple [_, .mk _ (.ctor .tuple [_,
        .mk _ (.base (some parameters, _)), _, _])]),
      .mk _ (.base (some loaded, _))])) _
    (.mk _ (.if_ _ _ (.mk _ (.if_ _ _
      (.mk _ (.sseq _ preparation _))))))) := actualCall | none
  pure (parameters, loaded, preparation)

theorem source_preparation_exists : emittedPreparation.isSome = true := by cbv

def actualPreparation : Sym × Sym × EE := emittedPreparation.get source_preparation_exists

theorem source_preparation_recognized :
    CallArg.letArg file actualPreparation.1 actualPreparation.2.1 actualPreparation.2.2 = true := by cbv

/-- The real source-generated preparation creates an actual integer Slot
and stores 42 in it. The following callee theorem consumes precisely that Slot. -/
theorem source_preparation_stores (labels : Labels) (environment : Env) (frames : List Frame)
    (memory : Mem.Concrete.State)
    (parameters : environment.lookup actualPreparation.1 = some (.list .ctype [.ctype intType]))
    (argument : environment.lookup actualPreparation.2.1 = some (.loaded (.specified (.integer 42))))
    (positive : 0 < nextIntAddress memory) (fresh : memory.nextId ∉ memory.dead) :
    ∃ prepared annotations, prepared.stdout = memory.stdout ∧
      Locals.Slot prepared memory.nextId (nextIntAddress memory) 42 ∧
      Reaches file labels
        ⟨.effectExpr actualPreparation.2.2 environment, frames, memory⟩
        ⟨.value (.object (.pointer (.allocated memory.nextId (nextIntAddress memory)))),
          .annotations annotations :: frames, prepared⟩ := by
  exact CallArg.letArg_reaches source_preparation_recognized environment frames memory parameters
    (by cbv) argument (by constructor <;> decide) positive fresh
end Silmaril.Compiler.Core.ParameterCallReturn
