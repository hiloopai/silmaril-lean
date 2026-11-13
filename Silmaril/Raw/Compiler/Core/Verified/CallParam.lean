module

public import Silmaril.Compiler.Core.Verified.ParamRun.Defs
public import Silmaril.Compiler.Core.Verified.CallArgLink.Defs
/-! # Calls with a mutable State parameter

The argument object is allocated and killed by the caller. The callee's symbolic
State term is computed from the actual parameter register by `CallArgLink`.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.CallParam

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ConvInt (IsInt)
open Mem.Concrete (LiveInt IntRange nextIntAddress)
open Locals (Slot)
open IntExpr (Term)
open LoadTask (Touched ReadTask)
open Call (retKind)
open CallArg

variable {file : Program} {labels : Labels}

/-- A known callee with one `int` parameter; `J` bounds its own `int` locals. -/
def calleeArg (file : File Codec.wireModel Unit Unit) (g : Sym) (J : Nat := 0) : Option (Sym × Term) :=
  if (file.stdlib.lookup g).isSome then none else
  match file.funInfo.lookup g with
  | some (_, _, rty, [(_, pty)], false, _) =>
    match file.funs.lookup g with
    | some (.procedure _ _ _ [(x, _)] body) =>
      if retKind rty = some true ∧ retKind pty = some true then
        (ParamRun.body file x body J).map fun t => (x, t)
      else none
    | _ => none
  | _ => none

theorem calleeArg_spec {g x : Sym} {t : Term} {J : Nat} (hc : calleeArg file g J = some (x, t)) :
    ∃ loc attrs rty po pty proto dloc marker bt xbt body,
      file.stdlib.lookup g = none ∧
      file.funInfo.lookup g = some (loc, attrs, rty, [(po, pty)], false, proto) ∧
      file.funs.lookup g = some (.procedure dloc marker bt [(x, xbt)] body) ∧
      retKind rty = some true ∧ retKind pty = some true ∧ ParamRun.body file x body J = some t := by
  unfold calleeArg at hc
  split at hc
  · cases hc
  rename_i hstd
  split at hc
  · rename_i loc attrs rty po pty proto hinfo
    split at hc
    · rename_i dloc marker bt x' xbt body hdecl
      split at hc
      · rename_i hk
        cases hb : ParamRun.body file x' body J with
        | none => simp [hb] at hc
        | some t' =>
          simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact ⟨loc, attrs, rty, po, pty, proto, dloc, marker, bt, xbt, body, by simpa using hstd,
            hinfo, hdecl, hk.1, hk.2, hb⟩
      · cases hc
    · cases hc
  · cases hc

/-- Once caller-side metadata and argument allocation have prepared the call,
the scheduled call runs the mutable parameter body inside its operand arena. -/
theorem prepared_in_arena {e : EE} {x g : Sym} {t : Term}
    (hbody : ParamRun.body file x e = some t) (env : Env) (m : Mem.Concrete.State)
    {id addr n : Int} (hn : IntRange n) (slot : Slot m id addr n)
    (ordinary : libraryCall file g = none)
    (resolved : procedureBody file g [.object (.pointer (.allocated id addr))] =
      .ok (e, [(x, .object (.pointer (.allocated id addr)))]))
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave done [(i, .apply (.procedure env)
        [.loaded (.specified (.pointer (.function g))),
         .object (.pointer (.allocated id addr))], [])], k, m⟩ ∨
    t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ LiveInt m' id addr ∧ CoreReaches file labels
      ⟨.interleave done [(i, .apply (.procedure env)
        [.loaded (.specified (.pointer (.function g))),
         .object (.pointer (.allocated id addr))], [])], k, m⟩
      ⟨.interleave ((i, IntExpr.spec (t.val n), []) :: done) [], k, m'⟩ := by
  have entry := ArenaCall.procedure_enter file labels m done i g
    [.object (.pointer (.allocated id addr))] env e
    [(x, .object (.pointer (.allocated id addr)))] [] k ordinary resolved
  rcases ParamRun.body_in_arena (labels := labels) hbody
      (extendEnv [(x, .object (.pointer (.allocated id addr)))] env) m
      (ConvInt.lookup_one rfl) hn slot done i k with ⟨ok, m', out, live, run⟩ | fail
  · exact .inr ⟨ok, m', out, live, entry.trans (by simpa [CallReach.bodyLabels] using run)⟩
  · obtain ⟨s', run, halt⟩ := ArenaFail.fail_reaches file labels fail
    exact .inl ⟨s', entry.trans (by simpa only [CallReach.bodyLabels] using run), halt⟩

theorem callTail_returns {p x : Sym} {e : EE} (h : callTail p x e = true) {g x0 : Sym} {t : Term}
    (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value (IntExpr.spec (t.val n)), k, m'⟩) ∨
    ∃ s', Reaches file labels ⟨.effectExpr e env, k, m⟩ s' ∧ s'.control = .halt IntExpr.overflow := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, -, -,
    hbody⟩ := calleeArg_spec hc
  unfold callTail at h
  split at h
  · rename_i _ ann rann r rt cann mt pann p₁ xann x₁ kt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp₁, hx₁, hxr⟩, hkt⟩ := h
    let ptr : Val := .object (.pointer (.allocated id addr))
    let K := Frame.strongBind (.mk rann (.base (some r, rt))) kt env :: k
    have enter := (ReturnConst.sequence_reaches file labels ann _ _ kt env k m).trans
      (CallReach.ccall_reaches (file := file) (labels := labels) (args := [ptr]) cann mt
        (SeqReach.pure_symbol pann p₁ env _ (by rw [ReturnLit.lookup_key hp₁]; exact hp))
        (.cons (SeqReach.pure_symbol xann x₁ env _ (by rw [ReturnLit.lookup_key hx₁]; exact hx)) .nil)
        (CallReach.procedure_not_builtin hdecl)
        (CallReach.procedure_body (values := [ptr]) hstd hdecl rfl) K m)
    rcases ParamRun.body_returns' (file := file) (labels := labels) hbody
        (extendEnv [(x0, ptr)] env) K (SeqReach.focusMemory cann m)
        (ConvInt.lookup_one rfl) hn ((touched_seq cann m).slot slot) with
      ⟨ok, m₁, out₁, live, r₁⟩ | fail
    · left
      refine ⟨ok, ?_⟩
      let v := IntExpr.spec (t.val n)
      let env₁ := extendEnv [(r, v)] env
      have hx' : env₁.lookup x = some ptr := by
        rw [ConvInt.lookup_one_other hxr]; exact hx
      obtain ⟨m₂, out₂, rk⟩ := killTail_reaches (file := file) (labels := labels) hkt env₁ k m₁ hx'
        (ConvInt.lookup_one rfl) live
      refine ⟨m₂, by rw [out₂, out₁]; simp, ?_⟩
      exact enter.trans ((Interleave.reaches_of_local file labels r₁).trans
        ((CallReach.return_reaches _ _ K m₁).trans
          ((SeqReach.strong_bind_reaches rfl k m₁).trans rk)))
    · obtain ⟨s', r₁, hs'⟩ := ArenaFail.fail_reaches file labels fail
      exact .inr ⟨s', enter.trans r₁, hs'⟩
  · cases h

theorem restArg_gives {pty a p : Sym} {e : EE} (h : restArg file pty a p e = true) {g x0 : Sym}
    {t : Term} (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {c : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : retKind c = some true)
    (ha : env.lookup a = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ArgGives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout n t := by
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
    rcases callTail_returns (file := file) (labels := labels) hct hc env₁ (.annotations ys :: k) m₁
        (by rw [ConvInt.lookup_one_other hpx]; exact hp) (ConvInt.lookup_one rfl) hn slot₁ with
      ⟨ok, m₂, out₂, r₂⟩ | ⟨s', r₂, hs'⟩
    · exact .inl ⟨ok, m₂, ys, by rw [out₂, out₁], pre.trans r₂⟩
    · exact .inr ⟨s', pre.trans r₂, hs'⟩
  · cases h

theorem guards_gives {fty pty vs a p : Sym} {e : EE} (h : guards file fty pty vs a p e = true)
    {g x0 : Sym} {t : Term} (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {c frt : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : retKind c = some true)
    (hvs : env.lookup vs = some .false) (hfty : env.lookup fty = some (.ctype frt))
    (hfrt : retKind frt = some true)
    (ha : env.lookup a = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ArgGives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout n t := by
  unfold guards at h
  split at h
  · rename_i _ i1ann c1a c1b c1c len c1d pty₁ c1e one u1 i2ann c2a c2b vs₁ c2c c2d c2e rty c2f fty₁
      u2 rest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty₁, hvs₁, hfty₁, rfl⟩, hlen⟩, hrty⟩, hrest⟩ := h
    let m₁ := SeqReach.focusMemory i1ann m
    let m₂ := SeqReach.focusMemory i2ann m₁
    have T : Touched m m₂ := (touched_seq i1ann m).trans (touched_seq i2ann m₁)
    have o := restArg_gives (file := file) (labels := labels) hrest hc env k m₂ hp hpty hcint ha hn
      (by rw [touched_nextIntAddress T]; exact hpos) (by rw [touched_nextId T, touched_dead T]; exact hdead)
    rw [T.stdout] at o
    refine ArgGives.pre ?_ o
    refine (SeqReach.effect_if_reaches i1ann false
      (Call.pureEval_of (length_one_eval hlen ((ReturnLit.lookup_key hpty₁).trans hpty))) k m).trans ?_
    exact SeqReach.effect_if_reaches i2ann false (variadicCheck_reaches hrty hfrt
      ((ReturnLit.lookup_key hvs₁).trans hvs) ((ReturnLit.lookup_key hfty₁).trans hfty)) k m₁
  · cases h

theorem argCall_gives {e : EE} {g x0 : Sym} {n : Int} {t : Term}
    (hs : argSite file e = some (g, n)) (hc : calleeArg file g = some (x0, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m)
    (hdead : m.nextId ∉ m.dead) :
    ArgGives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout n t := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, hfr, hfp,
    hbody⟩ := calleeArg_spec hc
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
          have o := guards_gives (file := file) (labels := labels) hgd hc env₁ (.annotations xs :: k) m₁ lp lpty
            hfp lvs lfty hfr la hn (by rw [touched_nextIntAddress tch₁]; exact hpos)
            (by rw [touched_nextId tch₁, touched_dead tch₁]; exact hdead)
          rw [tch₁.stdout] at o
          rcases o with ⟨ok, m', zs, out, r⟩ | ⟨s', r, hs'⟩
          · exact .inl ⟨ok, m', zs ++ xs, out,
              pre.trans (r.trans (Locals.annotations_merge_reaches zs xs _ k m'))⟩
          · exact .inr ⟨s', pre.trans r, hs'⟩
        · cases hs
      · cases hs
    · cases hs
  · cases hs

open LocalExpr (Shows)

/-- A statement sequence that starts with `return g(n);`: `n` and what `g` returns. -/
def retArg (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option (Int × Term)
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ ConvInt.isConvLoadedInt file s = true then
        match argSite file e with
        | some (g, n) => (calleeArg file g).map fun (_, t) => (n, t)
        | none => none
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retArg file ret a
  | _ => none

/-- **`return g(n);`** halts with what `g` returns for `n`, or reaches undefined behaviour. -/
theorem retArg_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) {n : Int} {t : Term}
    (h : retArg file ret e = some (n, t)) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ n t m.stdout := by
  unfold retArg at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i g n' hsite
        cases hca : calleeArg file g with
        | none => simp [hca] at h
        | some xt =>
          obtain ⟨x0, t'⟩ := xt
          simp only [hca, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hn', ht'⟩ := h
          subst hn' ht'
          have hn : IntRange n' := argSite_range hsite
          let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
          let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
                k, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine LocalExpr.Shows.pre pre ?_
          rcases argCall_gives (labels := labels) hsite hca env (.bound :: kR) m hpos hdead with
            ⟨ok, m₁, zs, out₁, r⟩ | ⟨s', r, hs'⟩
          · left
            refine ⟨ok, ?_⟩
            let v : Val := IntExpr.spec (t'.val n')
            let env₁ := extendEnv [(u, v)] env
            have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₁)) env₁
                (.inl (.mk cann () (.call (.sym s)
                  [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                    .mk a3 () (.sym u')])))
                (.inl v) :=
              ConvInt.convLoadedInt_eval (ann := tyann) hs (IntExpr.Term.ok_int hn t' ok)
                (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
            obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk
              (ReturnConst.focusMemory rann m₁)
            refine ⟨m', by simp [out, out₁], ?_⟩
            refine r.trans ((Locals.annotations_bound_reaches zs v kR m₁).trans ?_)
            refine (ReturnLit.bind_reaches pann u ty v R env k m₁).trans ?_
            refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
            exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
          · exact .inr ⟨s', r, hs'⟩
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retArg_halts hret a h env (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m hpos hdead)
  · cases h
termination_by sizeOf e

/-- The body of `main`: a statement sequence that returns `g(n)`, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option (Int × Term)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ ReturnLit.saveFree a = true then retArg file ret a else none
  | _ => none

/-- `main` returns `g(n)` for a procedure `g` of the file with one `int` parameter. -/
def recognize (doc : Codec.Document) : Option (Int × Term) := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (t : Term)
    (h : recognize doc = some (n, t)) (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s n t "" := by
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
          have hbody : recognizeBody doc.file body = some (n, t) := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ :=
            StartupMem.initial_reaches_body_mem doc.file enums args hdefs main decl
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
              have o := retArg_halts hret a hbody ∅
                (k := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs])
                (by simp [NoBoundary, hasBoundary]) m (Locals.errno_nextIntAddress hlast)
                (by simp [hdead])
              rw [hout] at o
              exact ⟨s, labels, hinit, LocalExpr.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with the value
the callee returns for `n`, mod 256, and no output. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (t : Term) (h : recognize doc = some (n, t))
    (args : List String) :
    Spec.CoreUB doc args ∨ t.Ok n ∧ Spec.CoreBeh doc args (.exit (t.val n % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc n t h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (t.val n % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.CallParam
