module

public import Silmaril.Compiler.Core.Verified.CallParam.Defs
public import Silmaril.Compiler.Core.Verified.StateActionsLocal.Defs
/-! # Parameter call-site setup and cleanup inside operand arenas

The caller allocates the argument object, retains its annotations and cleanup
continuation across scheduled procedure entry, and kills it after the mutable
parameter body returns. These are local traces, usable in an enclosing operand.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.CallParamLocal

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnConst (focusMemory)
open ReturnLit (Eff)
open ConvInt (IsInt)
open Mem.Concrete (LiveInt IntRange nextIntAddress)
open LoadTask (Touched ReadTask plain_effectExpr plain_value plain_pureExpr)
open CallArg

variable {file : Program} {labels : Labels}

theorem annotations_sbind (xs : List Access) {pat : Pattern Sym} {v : Val} {bs : Bindings}
    (hm : matchPattern pat v = some bs) (b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.value v, .annotations xs :: .strongBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv bs env), .annotations xs :: k, m⟩ :=
  .single (.next (by simp [requestAux, awaitsScheduling, hm]) (plain_effectExpr _ _))

theorem annotations_wbind (xs : List Access) {pat : Pattern Sym} {v : Val} {bs : Bindings}
    (hm : matchPattern pat v = some bs) (b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.value v, .annotations xs :: .effectBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv bs env), .annotations xs :: k, m⟩ :=
  .single (.next (by simp [requestAux, awaitsScheduling, hm]) (plain_effectExpr _ _))

theorem not_compatible {an ann aann bann : List Annot} {rty fty : Ctype} {f : Sym}
    {env : Env} {isInt : Bool} (hr : Call.retKind rty = some isInt)
    (hf : Call.retKind fty = some isInt) (hl : env.lookup f = some (.ctype fty)) :
    CallArena.LPure (file := file) (labels := labels) (.mk an () (.not
      (.mk ann () (.areCompatible (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))))) env
      .false := by
  intro k m
  refine .head (.next (c' := .pureExpr (.mk ann () (.areCompatible
      (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))) env)
    (k' := .arguments .notBool [] [] env :: k)
    (by simp [requestAux, awaitsScheduling, arguments]) (plain_pureExpr _ _)) ?_
  refine (CallArena.compatible hr hf hl _ m).trans ?_
  refine .head (.next (c' := .apply .notBool [.true]) (k' := k)
    (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_apply _ _)) ?_
  exact .single (.next (by simp [requestAux, awaitsScheduling, primitive, pure, Except.pure])
    (plain_value _))

theorem variadic_check {an a1 a2 ann aann bann : List Annot} {rty fty : Ctype} {b f : Sym}
    {env : Env} {isInt : Bool} (hr : Call.retKind rty = some isInt)
    (hf : Call.retKind fty = some isInt) (hb : env.lookup b = some .false)
    (hl : env.lookup f = some (.ctype fty)) :
    CallArena.LPure (file := file) (labels := labels) (.mk an () (.op .or (.mk a1 () (.sym b))
      (.mk a2 () (.not (.mk ann () (.areCompatible
        (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))))))) env .false := by
  intro k m
  refine .head (.next (c' := .pureExpr (.mk a1 () (.sym b)) env)
    (k' := .arguments (.bin .or) [] [.mk a2 () (.not (.mk ann () (.areCompatible
      (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))))] env :: k)
    (by simp [requestAux, awaitsScheduling, arguments]) (plain_pureExpr _ _)) ?_
  refine (PureLocal.eval_local file _ (Eval.sym hb) _ _ rfl).trans ?_
  refine .head (.next (c' := .pureExpr (.mk a2 () (.not (.mk ann () (.areCompatible
      (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))))) env)
    (k' := .arguments (.bin .or) [.false] [] env :: k)
    (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
  refine (not_compatible hr hf hl _ m).trans ?_
  refine .head (.next (c' := .apply (.bin .or) [.false, .false]) (k' := k)
    (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_apply _ _)) ?_
  exact .single (.next (by simp [requestAux, awaitsScheduling, primitive, pure, Except.pure])
    (plain_value _))

/-- Local allocation, initialization and pointer return for the caller's argument. -/
theorem mkArg_local {a : Sym} {e : EE} (h : mkArg file a e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {n : Int} (ha : env.lookup a = some (IntExpr.spec n))
    (hn : IntRange n) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' ys, m'.stdout = m.stdout ∧ Locals.Slot m' m.nextId (nextIntAddress m) n ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations ys :: k, m'⟩ := by
  unfold mkArg at h
  split at h
  · rename_i _ ann oann o ot cr wann w2ann w2t stann stl stu a1 c1 a2 o₁ a3 cv a4 c3 a5 a₁ pann bann o₂
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hcr, ho₁, ho₂, ha₁, hao⟩, hcv⟩ := h
    unfold Locals.createInt at hcr
    split at hcr
    · rename_i crann crloc cru ca1 ca2 cc1 ca3 cc2 pref
      let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
      let PURE : EE := .mk pann (.pure (.mk bann () (.sym o₂)))
      let ST : EE := .mk stann (.action (.mk .pos (.mk stl stu (.store false
        (Locals.intVal a1 c1) (.mk a2 () (.sym o₁))
        (.mk a3 () (.call (.sym cv) [Locals.intVal a4 c3, .mk a5 () (.sym a₁)])) .na))))
      let W2 : EE := .mk wann (.wseq (.mk w2ann (.base (none, w2t))) ST PURE)
      let m₁ := Actions.created pref cc2 (focusMemory crann m)
      have rc := StateActionsLocal.create (file := file) (labels := labels) crann ca1 ca2 ca3 cc1 cc2
        crloc cru pref env (.effectBind (.mk oann (.base (some o, ot))) W2 env :: k) m hpos
      rw [touched_nextId (LoadTask.focusMemory_touched crann m)] at rc
      have live₁ : LiveInt m₁ m.nextId (nextIntAddress m) := by
        simpa [m₁, Locals.nextIntAddress_focus, touched_nextId (LoadTask.focusMemory_touched crann m)] using
          (Locals.created_live pref cc2 (focusMemory crann m) (by rw [touched_nextId (LoadTask.focusMemory_touched crann m), touched_dead (LoadTask.focusMemory_touched crann m)]; exact hdead))
      let env₁ := extendEnv [(o, ptr)] env
      have hx₁ : env₁.lookup o₁ = some ptr := ConvInt.lookup_one ho₁
      have ht₁ : env₁.lookup a₁ = some (IntExpr.spec n) := by
        rw [ConvInt.lookup_one_other (by rw [ha₁]; exact hao), ReturnLit.lookup_key ha₁]; exact ha
      obtain ⟨ys, rst⟩ := StateActionsLocal.store (file := file) (labels := labels)
        stann a1 a2 a3 a4 a5 c1 c3 stl stu o₁ cv a₁ hcv env₁
        (.effectBind (.mk w2ann (.base (none, w2t))) PURE env₁ :: k) m₁ hx₁ ht₁ hn live₁
      let m₂ := Locals.stored (focusMemory stann m₁) m.nextId (nextIntAddress m) n
      refine ⟨focusMemory pann m₂, ys, ?_, ?_, ?_⟩
      · simp [m₂, m₁, Locals.stored_stdout, Actions.created_stdout]
      · exact (LoadTask.focusMemory_touched pann m₂).slot
          (Locals.stored_slot (Locals.liveInt_focus stann live₁) n)
      refine (StateActionsLocal.wseq ann _ _ W2 env k m).trans (rc.trans ?_)
      have bind : LocalReaches file labels false
          ⟨.value ptr, .effectBind (.mk oann (.base (some o, ot))) W2 env :: k, m₁⟩
          ⟨.effectExpr W2 env₁, k, m₁⟩ :=
        .single (.next (by simp [requestAux, awaitsScheduling, matchPattern, env₁]) (plain_effectExpr _ _))
      refine bind.trans ?_
      refine (StateActionsLocal.wseq wann _ ST PURE env₁ k m₁).trans (rst.trans ?_)
      refine (annotations_wbind ys (bs := []) rfl PURE env₁ k m₂).trans ?_
      exact CallLocal.pure pann (fun _ => .sym (by
        rw [lookup_nil]; exact ConvInt.lookup_one ho₂)) (.annotations ys :: k) m₂
    · cases hcr
  · cases h

/-- The argument type guard is also local; no top-level reachability conversion is used. -/
theorem letArg_local {pty a : Sym} {e : EE} (h : letArg file pty a e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {c : Ctype} {n : Int}
    (hp : env.lookup pty = some (.list .ctype [.ctype c])) (hc : Call.retKind c = some true)
    (ha : env.lookup a = some (IntExpr.spec n)) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' ys, m'.stdout = m.stdout ∧ Locals.Slot m' m.nextId (nextIntAddress m) n ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations ys :: k, m'⟩ := by
  unfold letArg at h
  split at h
  · rename_i _ lann tann tt tbt nann nth a1 pty₂ a2 zero iann cann bann cvann ity cfann tt₁ u mk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty, htt, rfl, hat⟩, hnth⟩, hity⟩, hmk⟩ := h
    let env₁ := extendEnv [(tt, .ctype c)] env
    let m₁ := focusMemory lann m
    let m₂ := focusMemory iann m₁
    have T : Touched m m₂ := (touched_seq lann m).trans (touched_seq iann m₁)
    have ha₁ : env₁.lookup a = some (IntExpr.spec n) := by
      rw [ConvInt.lookup_one_other hat]; exact ha
    obtain ⟨m', ys, out, slot, r⟩ := mkArg_local (file := file) (labels := labels) hmk env₁ k m₂ ha₁ hn
      (by rw [touched_nextIntAddress T]; exact hpos) (by rw [touched_nextId T, touched_dead T]; exact hdead)
    rw [touched_nextId T, touched_nextIntAddress T] at slot r
    refine ⟨m', ys, out.trans T.stdout, slot, ?_⟩
    refine (CallArena.effect_let lann (xs := [(tt, .ctype c)])
      (CallArena.of_eval (nth_zero_eval hnth ((ReturnLit.lookup_key hpty).trans hp))) rfl k m).trans ?_
    exact (CallArena.effect_if iann false
      (not_compatible hity hc (ConvInt.lookup_one htt)) k m₁).trans r
  · cases h


/-- Caller frames finish the call by killing its live argument object. -/
def Cleanup (fr : List Frame) (id addr : Int) (k : List Frame) : Prop :=
  ∀ (v : Val) (m : Mem.Concrete.State), LiveInt m id addr →
    ∃ m' fs xs, m'.stdout = m.stdout ∧ Cond.OneAnn fs xs ∧ LocalReaches file labels false
      ⟨.value v, fr, m⟩ ⟨.value v, fs ++ k, m'⟩

/-- The caller's kill and value return have a local trace under arbitrary outer frames. -/
theorem killTail_local {x r : Sym} {e : EE} (h : killTail x r e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {id addr : Int} {v : Val}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hr : env.lookup r = some v) (live : LiveInt m id addr) :
    ∃ m', m'.stdout = m.stdout ∧ LocalReaches file labels false
      ⟨.effectExpr e env, k, m⟩ ⟨.value v, k, m'⟩ := by
  unfold killTail at h
  split at h
  · rename_i _ ann kann kt kl pann bann r₁
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hkl, hr₁⟩ := h
    unfold Locals.killInt at hkl
    split at hkl
    · rename_i _ klann klloc klu kc1 ka2 x₁
      simp only [decide_eq_true_eq] at hkl
      let K := Frame.strongBind (.mk kann (.base (none, kt)))
        (.mk pann (.pure (.mk bann () (.sym r₁)))) env :: k
      let m₁ := Locals.killed (focusMemory klann m) id
      refine ⟨focusMemory pann m₁, by simp [m₁, Locals.killed], ?_⟩
      refine (CallLocal.sequence ann _ _ _ env k m).trans ?_
      refine (StateReturnLocal.kill (file := file) (labels := labels) klann ka2 kc1 klloc klu x₁
        env K m (by rw [ReturnLit.lookup_key hkl]; exact hx) live).trans ?_
      refine (StateReturnLocal.wildcard kann kt .unit _ env k m₁).trans ?_
      exact CallLocal.pure pann (fun _ => .sym (by rw [ReturnLit.lookup_key hr₁]; exact hr)) k m₁
    · cases hkl
  · cases h

/-- Setup stops exactly at the scheduler, retaining the caller's cleanup frames. -/
def Prepared (g x : Sym) (body : EE) (n : Int) (s : State) (k : List Frame) (out : String) : Prop :=
  ∃ env m fr id addr, m.stdout = out ∧ Locals.Slot m id addr n ∧
    libraryCall file g = none ∧
    procedureBody file g [.object (.pointer (.allocated id addr))] =
      .ok (body, [(x, .object (.pointer (.allocated id addr)))]) ∧
    LocalReaches file labels false s
      ⟨.apply (.procedure env) [.loaded (.specified (.pointer (.function g))),
        .object (.pointer (.allocated id addr))], fr, m⟩ ∧
    Cleanup (file := file) (labels := labels) fr id addr k

theorem Prepared.pre {g x : Sym} {body : EE} {n : Int} {s s' : State}
    {k : List Frame} {out : String} (r : LocalReaches file labels false s s')
    (h : Prepared (file := file) (labels := labels) g x body n s' k out) :
    Prepared (file := file) (labels := labels) g x body n s k out := by
  obtain ⟨env, m, fr, id, addr, out, slot, ordinary, resolved, run, cleanup⟩ := h
  exact ⟨env, m, fr, id, addr, out, slot, ordinary, resolved, r.trans run, cleanup⟩

/-- The final call syntax supplies its own cleanup continuation. -/
theorem callTail_prepared {p x : Sym} {e : EE} (h : callTail p x e = true)
    {g x0 : Sym} {t : IntExpr.Term} (hc : CallParam.calleeArg file g = some (x0, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (slot : Locals.Slot m id addr n) :
    ∃ body, ParamRun.body file x0 body = some t ∧
      Prepared (file := file) (labels := labels) g x0 body n ⟨.effectExpr e env, k, m⟩ k m.stdout := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, -, -,
    hbody⟩ := CallParam.calleeArg_spec hc
  unfold callTail at h
  split at h
  · rename_i _ ann rann r rt cann mt pann p₁ xann x₁ kt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp₁, hx₁, hxr⟩, hkt⟩ := h
    let ptr : Val := .object (.pointer (.allocated id addr))
    let K := Frame.strongBind (.mk rann (.base (some r, rt))) kt env :: k
    refine ⟨body, hbody, env, focusMemory cann m, K, id, addr, by simp,
      (LoadTask.focusMemory_touched cann m).slot slot,
      CallReach.procedure_not_builtin hdecl,
      CallReach.procedure_body (values := [ptr]) hstd hdecl rfl, ?_, ?_⟩
    · refine (CallLocal.sequence ann _ _ _ env k m).trans ?_
      refine (CallLocal.focus (c' := .pureExpr (.mk pann () (.sym p₁)) env)
        (k' := .arguments (.procedure env) [] [.mk xann () (.sym x₁)] env :: K)
        cann m (plain_pureExpr _ _) ?_).trans ?_
      · simp [requestAux, awaitsScheduling, arguments, focusMemory]; rfl
      · simpa [PureEval.argState] using PureLocal.args_local file _
          (Eval.cons (Eval.sym (by rw [ReturnLit.lookup_key hp₁]; exact hp))
            (Eval.cons (Eval.sym (by rw [ReturnLit.lookup_key hx₁]; exact hx)) Eval.nil))
          (.procedure env) [] K (focusMemory cann m) rfl
    · intro v m' live
      obtain ⟨m'', out, cleanup⟩ := killTail_local (file := file) (labels := labels) hkt
        (extendEnv [(r, v)] env) k m'
        (by rw [ConvInt.lookup_one_other hxr]; exact hx) (ConvInt.lookup_one rfl) live
      exact ⟨m'', [], [], out, .inl ⟨rfl, rfl⟩,
        (CallLocal.bind rann r rt v kt env k m').trans cleanup⟩
  · cases h


/-- Allocation and operand annotations remain in the task until collection. -/
theorem Prepared.annotations {g x : Sym} {body : EE} {n : Int} {s : State}
    {k : List Frame} {out : String} (ys : List Access)
    (h : Prepared (file := file) (labels := labels) g x body n s (.annotations ys :: k) out) :
    Prepared (file := file) (labels := labels) g x body n s k out := by
  obtain ⟨env, m, fr, id, addr, out, slot, ordinary, resolved, run, cleanup⟩ := h
  refine ⟨env, m, fr, id, addr, out, slot, ordinary, resolved, run, ?_⟩
  intro v m' live
  obtain ⟨m'', fs, xs, hout, hfs, r⟩ := cleanup v m' live
  rcases hfs with ⟨rfl, rfl⟩ | rfl
  · exact ⟨m'', [.annotations ys], ys, hout, .inr rfl, r⟩
  · refine ⟨m'', [.annotations (xs ++ ys)], xs ++ ys, hout, .inr rfl, ?_⟩
    exact r.tail (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))

theorem restArg_prepared {pty a p : Sym} {e : EE} (h : restArg file pty a p e = true)
    {g x0 : Sym} {t : IntExpr.Term} (hc : CallParam.calleeArg file g = some (x0, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {c : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : Call.retKind c = some true)
    (ha : env.lookup a = some (IntExpr.spec n)) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ body, ParamRun.body file x0 body = some t ∧
      Prepared (file := file) (labels := labels) g x0 body n ⟨.effectExpr e env, k, m⟩ k m.stdout := by
  unfold restArg at h
  split at h
  · rename_i _ ann xann x xbt la ct
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpx, hla⟩, hct⟩ := h
    obtain ⟨m₁, ys, out₁, slot₁, r₁⟩ := letArg_local (file := file) (labels := labels) hla env
      (.strongBind (.mk xann (.base (some x, xbt))) ct env :: k) m hpty hcint ha hn hpos hdead
    let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
    let env₁ := extendEnv [(x, ptr)] env
    have pre := (CallLocal.sequence ann _ la ct env k m).trans
      (r₁.trans (annotations_sbind ys (bs := [(x, ptr)]) rfl ct env k m₁))
    obtain ⟨body, hb, r⟩ := callTail_prepared (file := file) (labels := labels) hct hc
      env₁ (.annotations ys :: k) m₁
      (by rw [ConvInt.lookup_one_other hpx]; exact hp) (ConvInt.lookup_one rfl) slot₁
    rw [out₁] at r
    exact ⟨body, hb, (r.annotations ys).pre pre⟩
  · cases h

theorem guards_prepared {fty pty vs a p : Sym} {e : EE} (h : guards file fty pty vs a p e = true)
    {g x0 : Sym} {t : IntExpr.Term} (hc : CallParam.calleeArg file g = some (x0, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {c frt : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : Call.retKind c = some true)
    (hvs : env.lookup vs = some .false) (hfty : env.lookup fty = some (.ctype frt))
    (hfrt : Call.retKind frt = some true)
    (ha : env.lookup a = some (IntExpr.spec n)) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ body, ParamRun.body file x0 body = some t ∧
      Prepared (file := file) (labels := labels) g x0 body n ⟨.effectExpr e env, k, m⟩ k m.stdout := by
  unfold guards at h
  split at h
  · rename_i _ i1ann c1a c1b c1c len c1d pty₁ c1e one u1 i2ann c2a c2b vs₁ c2c c2d c2e rty c2f fty₁
      u2 rest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty₁, hvs₁, hfty₁, rfl⟩, hlen⟩, hrty⟩, hrest⟩ := h
    let m₁ := focusMemory i1ann m
    let m₂ := focusMemory i2ann m₁
    have T : Touched m m₂ := (touched_seq i1ann m).trans (touched_seq i2ann m₁)
    obtain ⟨body, hb, o⟩ := restArg_prepared (file := file) (labels := labels) hrest hc env k m₂ hp hpty
      hcint ha hn (by rw [touched_nextIntAddress T]; exact hpos)
      (by rw [touched_nextId T, touched_dead T]; exact hdead)
    rw [T.stdout] at o
    refine ⟨body, hb, o.pre ?_⟩
    exact (CallArena.effect_if i1ann false
      (CallArena.of_eval (length_one_eval hlen ((ReturnLit.lookup_key hpty₁).trans hpty))) k m).trans
      (CallArena.effect_if i2ann false (variadic_check hrty hfrt
        ((ReturnLit.lookup_key hvs₁).trans hvs) ((ReturnLit.lookup_key hfty₁).trans hfty)) k m₁)
  · cases h


/-- The complete metadata/argument prefix of a parameter call is a local trace. -/
theorem argSite_prepared {e : EE} {g x0 : Sym} {n : Int} {t : IntExpr.Term}
    (hs : argSite file e = some (g, n)) (hc : CallParam.calleeArg file g = some (x0, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m)
    (hdead : m.nextId ∉ m.dead) :
    ∃ body, ParamRun.body file x0 body = some t ∧
      Prepared (file := file) (labels := labels) g x0 body n ⟨.effectExpr e env, k, m⟩ k m.stdout := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, hfr, hfp,
    hbody⟩ := CallParam.calleeArg_spec hc
  unfold argSite at hs
  split at hs
  · rename_i _ eA pA pA1 pA2 p pT pA3 fA fty fT psA pty psT vA vs vT prA pr prT aA a aT uA t1 T2 gd
    split at hs
    · rename_i g' hfn
      split at hs
      · rename_i n' hlit
        split at hs
        · rename_i cond
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
          obtain ⟨hpure₂, -, hread₂⟩ := CallArg.argLit_spec (file := file) (labels := labels) hlit (fun _ => True) env
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
          have pre : LocalReaches file labels false ⟨.effectExpr (.mk eA (.sseq PAT (.mk uA (.unseq [t1, T2])) gd)) env, k, m⟩
              ⟨.effectExpr gd env₁, .annotations xs :: k, m₁⟩ :=
            (CallLocal.sequence eA PAT _ gd env k m).trans
              (run.trans (annotations_sbind xs (bs := bs) rfl gd env k m₁))
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
          obtain ⟨body', hb, o⟩ := guards_prepared (file := file) (labels := labels) hgd hc env₁
            (.annotations xs :: k) m₁ lp lpty hfp lvs lfty hfr la hn
            (by rw [touched_nextIntAddress tch₁]; exact hpos)
            (by rw [touched_nextId tch₁, touched_dead tch₁]; exact hdead)
          rw [tch₁.stdout] at o
          exact ⟨body', hb, (o.annotations xs).pre pre⟩
        · cases hs
      · cases hs
    · cases hs
  · cases hs

/-- A full parameter call, including its caller-owned allocation and kill, executes
as the sole remaining operand. Completed siblings and outer frames stay intact. -/
theorem call_in_arena {e : EE} {g x : Sym} {n : Int} {t : IntExpr.Term}
    (hs : argSite file e = some (g, n)) (hc : CallParam.calleeArg file g = some (x, t))
    (env : Env) (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩ ∨
    t.Ok n ∧ ∃ m' xs, m'.stdout = m.stdout ∧ CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave ((i, IntExpr.spec (t.val n), xs) :: done) [], k, m'⟩ := by
  obtain ⟨body, hb, env', m₁, fr, id, addr, out₁, slot, ordinary, resolved, pre, cleanup⟩ :=
    argSite_prepared (labels := labels) hs hc env [] m hpos hdead
  have pending : Pending [] i := ⟨by simp, by simp⟩
  have preRun : CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave done [(i, .apply (.procedure env')
        [.loaded (.specified (.pointer (.function g))), .object (.pointer (.allocated id addr))], fr)],
        k, m₁⟩ := by
    apply reaches_of_local file labels
    have localPre : LocalReaches file labels (taskFlag false k [])
        ⟨.effectExpr e env, [], m⟩
        ⟨.apply (.procedure env') [.loaded (.specified (.pointer (.function g))),
          .object (.pointer (.allocated id addr))], fr, m₁⟩ := by simpa [taskFlag] using pre
    exact ArenaFail.drive_run file labels pending (done := done) (k := k) (wc := false)
      localPre (fun v h => by cases h)
  have enter := ArenaCall.procedure_enter file labels m₁ done i g
    [.object (.pointer (.allocated id addr))] env' body [(x, .object (.pointer (.allocated id addr)))]
    fr k ordinary resolved
  have entry := preRun.trans (by simpa [CallReach.bodyLabels] using enter)
  rcases ParamRun.body_returns' (labels := labels) hb
      (extendEnv [(x, .object (.pointer (.allocated id addr)))] env') fr m₁
      (ConvInt.lookup_one rfl) (argSite_range hs) slot with ⟨ok, m₂, out₂, live, run⟩ | fail
  · right
    let v := IntExpr.spec (t.val n)
    obtain ⟨m₃, fs, xs, out₃, hfs, finish⟩ := cleanup v m₂ live
    have pop : LocalReaches file labels false
        ⟨.value v, .procedureReturn (CallReach.bodyLabels body) :: fr, m₂⟩ ⟨.value v, fr, m₂⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))
    have complete := run.trans (pop.trans finish)
    refine ⟨ok, m₃, xs, out₃.trans (out₂.trans out₁), entry.trans ?_⟩
    apply reaches_of_local file labels
    apply drive_task file labels pending
    refine ⟨fs, ?_, ?_⟩
    · simpa [taskFlag, CallReach.bodyLabels, v] using complete
    · rcases hfs with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
  · left
    refine StateStmt.Overflows.pre entry ?_
    exact ArenaFail.fail_reaches file labels
      (ArenaFail.fail_task file labels pending (done := done) (k := k) (wc := false)
        (by simpa [taskFlag, CallReach.bodyLabels] using fail))

end Silmaril.Compile.Core.Verified.CallParamLocal
