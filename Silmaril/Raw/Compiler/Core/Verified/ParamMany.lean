module

public import Silmaril.Compiler.Core.Verified.CallMany.Defs
public import Silmaril.Compiler.Core.Verified.ParamCallReserve.Defs
/-! # Calls with several `int` arguments: the callee and the comparison

The callee is a `ParamRun` block over its parameters, which start as the literals of the
call's arguments (`paramDefs`): its term is closed, and the target computes the callee's
arithmetic and tests on those values at run time, as `ParamCallCompare.Plan.inst` does for one
argument. `condition` is `ParamCallReserve.condition` for such a call:
`if (g(n₁, …, nₖ) != c) …`.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamMany

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ConvInt (IsInt)
open Mem.Concrete (LiveInt IntRange nextIntAddress)
open IntExpr (Term spec)
open StateExpr (Key)
open StateMem (Local Inv)
open StateStmt (Keys Overflows boolSource_touched seqFocus_touched)
open CallParamAlloc (Reserve)
open CallMany (ArgsMem ptrOf fp forall₂_mem_left)
open Call (retKind)

/-- The parameters `ps` start as the literals `ns`. -/
def paramDefs (ps : List Sym) (ns : List Int) : Key → Option IntExpr.Term := fun q =>
  ((ps.zip ns).find? fun xn => decide (xn.1.key = q)).map fun xn => .lit xn.2

/-- A callee body over the parameters `ps` holding `ns`, with at most `J` locals. -/
def body (file : File Codec.wireModel Unit Unit) (ps : List Sym) (ns : List Int) (e : Eff)
    (J : Nat) : Option IntExpr.Term :=
  match e with
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then
        ParamRun.block file ret ps J [] (paramDefs ps ns) a else none
  | _ => none

/-- A known procedure with `int` parameters and result, called on the arguments `ns`. -/
def callee (file : File Codec.wireModel Unit Unit) (g : Sym) (ns : List Int) : Option IntExpr.Term :=
  if (file.stdlib.lookup g).isSome then none else
  match file.funInfo.lookup g with
  | some (_, _, rty, pts, false, _) =>
    match file.funs.lookup g with
    | some (.procedure _ _ _ params e) =>
      if retKind rty = some true ∧ pts.all (fun q => retKind q.2 = some true) = true ∧
          pts.length = ns.length ∧ params.length = ns.length ∧ (params.map (·.1.key)).Nodup then
        body file (params.map (·.1)) ns e ParamRun.maxLocals
      else none
    | _ => none
  | _ => none

variable {file : Program} {labels : Labels}

theorem callee_spec {g : Sym} {ns : List Int} {t : Term} (hc : callee file g ns = some t) :
    ∃ loc attrs rty pts proto dloc marker bt params e,
      file.stdlib.lookup g = none ∧
      file.funInfo.lookup g = some (loc, attrs, rty, pts, false, proto) ∧
      file.funs.lookup g = some (.procedure dloc marker bt params e) ∧
      retKind rty = some true ∧ (∀ q ∈ pts, retKind q.2 = some true) ∧ pts.length = ns.length ∧
      params.length = ns.length ∧ (params.map (·.1.key)).Nodup ∧
      body file (params.map (·.1)) ns e ParamRun.maxLocals = some t := by
  unfold callee at hc
  split at hc
  · cases hc
  rename_i hstd
  split at hc
  · rename_i loc attrs rty pts proto hinfo
    split at hc
    · rename_i dloc marker bt params e hdecl
      split at hc
      · rename_i hk
        obtain ⟨hr, hpts, hl1, hl2, hnd⟩ := hk
        exact ⟨loc, attrs, rty, pts, proto, dloc, marker, bt, params, e, by simpa using hstd, hinfo,
          hdecl, hr, by simpa using hpts, hl1, hl2, hnd, hc⟩
      · cases hc
    · cases hc
  · cases hc

/-! ## The callee's invariant -/

theorem mem_zip_idx {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) :
    ∃ i, ∃ (h1 : i < l₁.length) (h2 : i < l₂.length), l₁[i] = a ∧ l₂[i] = b := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  simp only [List.length_zip] at hi
  simp only [List.getElem_zip, Prod.mk.injEq] at he
  exact ⟨i, by omega, by omega, he.1, he.2⟩

theorem idx_mem_zip {α β : Type} {l₁ : List α} {l₂ : List β} {i : Nat} (h1 : i < l₁.length)
    (h2 : i < l₂.length) : (l₁[i], l₂[i]) ∈ l₁.zip l₂ :=
  List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

/-- The parameters as `StateMem` locals. -/
def locals (ps : List Sym) (objs : List (Int × Int)) : List Local :=
  (ps.zip objs).map fun xo => ⟨xo.1, xo.2.1, xo.2.2⟩

theorem keys_locals : ∀ {ps : List Sym} {objs : List (Int × Int)}, ps.length = objs.length →
    Keys (locals ps objs) ps
  | [], [], _ => rfl
  | p :: ps, o :: objs, h => by
    have ih := keys_locals (ps := ps) (objs := objs) (by simpa using h)
    simp only [Keys, locals, List.zip_cons_cons, List.map_cons] at ih ⊢
    rw [ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The argument objects, seen from the callee's environment, satisfy `StateMem.Inv` for the
parameters with their literal definitions. -/
theorem inv_params {ps : List Sym} {ns : List Int} {objs : List (Int × Int)} {env : Env}
    {m : Mem.Concrete.State} (hnd : (ps.map (·.key)).Nodup) (hlen : ps.length = objs.length)
    (mem : ArgsMem m objs ns) (hns : ∀ n ∈ ns, IsInt n) :
    Inv (extendEnv (ps.zip (objs.map ptrOf)) env) m (locals ps objs) (paramDefs ps ns) := by
  have hlen' : objs.length = ns.length := mem.slots.length_eq
  have keysz : ((ps.zip (objs.map ptrOf)).map (·.1.key)).Nodup := by
    rw [show (ps.zip (objs.map ptrOf)).map (·.1.key) = ((ps.zip (objs.map ptrOf)).map Prod.fst).map
      (·.key) by simp, List.map_fst_zip (by simp [hlen])]
    exact hnd
  have objnd : objs.Nodup := by
    have := mem.apart
    exact this.imp fun h e => h.1 (by rw [e])
  refine { env := ?_, live := ?_, apart := ?_, defs := ?_ }
  · intro l hl y hy
    obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp hl
    refine CallMany.lookup_extend_mem keysz ?_ hy
    rw [List.zip_map_right]
    exact List.mem_map_of_mem (f := Prod.map id ptrOf) hxo
  · intro l hl
    obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp hl
    obtain ⟨n, -, s⟩ := forall₂_mem_left mem.slots (List.of_mem_zip hxo).2
    exact s.live
  · intro a ha b hb hne
    obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp ha
    obtain ⟨yo, hyo, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi1, hi2, hx, ho⟩ := mem_zip_idx (a := xo.1) (b := xo.2) (by simpa using hxo)
    obtain ⟨j, hj1, hj2, hy, ho'⟩ := mem_zip_idx (a := yo.1) (b := yo.2) (by simpa using hyo)
    have hij : i ≠ j := by
      rintro rfl; apply hne; show xo.1.key = yo.1.key; rw [← hx, ← hy]
    have pw := List.pairwise_iff_getElem.mp mem.apart
    show xo.2.1 ≠ yo.2.1 ∧ Slots.Apart xo.2.2 4 yo.2.2 4
    rw [← ho, ← ho']
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact pw i j hi2 hj2 h
    · obtain ⟨n1, n2⟩ := pw j i hj2 hi2 h
      exact ⟨Ne.symm n1, n2.symm⟩
  · intro q d hd
    unfold paramDefs at hd
    obtain ⟨xn, hfind, rfl⟩ := Option.map_eq_some_iff.mp hd
    have hq := List.find?_some hfind
    simp only [decide_eq_true_eq] at hq
    obtain ⟨i, hi1, hi2, hx, hn⟩ := mem_zip_idx (a := xn.1) (b := xn.2)
      (by simpa using List.mem_of_find?_eq_some hfind)
    have hi3 : i < objs.length := by omega
    have slot := mem.slots.get hi3 (by omega)
    simp only [List.get_eq_getElem] at slot
    refine ⟨by simpa [IntExpr.Term.Ok, ← hn] using hns _ (List.getElem_mem hi2), ⟨ps[i], objs[i].1, objs[i].2⟩,
      List.mem_map_of_mem (f := fun xo : Sym × (Int × Int) => (⟨xo.1, xo.2.1, xo.2.2⟩ : Local))
        (idx_mem_zip hi1 hi3), by simp [hx, hq], ?_⟩
    simpa [IntExpr.Term.val, ← hn] using slot

/-- The whole callee body, entered with its parameters bound to the argument objects. -/
theorem body_returns {ps : List Sym} {ns : List Int} {e : EE} {t : IntExpr.Term} {J : Nat}
    (h : body file ps ns e J = some t) (env : Env) (caller : List Frame) (m : Mem.Concrete.State)
    {objs : List (Int × Int)} (hnd : (ps.map (·.key)).Nodup) (hlen : ps.length = objs.length)
    (mem : ArgsMem m objs ns) (hns : ∀ n ∈ ns, IsInt n)
    (aligned : m.lastAddress % 4 = 0) (room : 4 * ((J : Int) + 1) < m.lastAddress)
    (dead : ∀ d ∈ m.dead, d < m.nextId) :
    (t.Ok 0 ∧ ∃ m', m'.stdout = m.stdout ∧ ParamRun.Uses J m m' ∧ (∀ o ∈ objs, LiveInt m' o.1 o.2) ∧
      LocalReaches file labels false
        ⟨.effectExpr e (extendEnv (ps.zip (objs.map ptrOf)) env),
          .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩
        ⟨.value (spec (t.val 0)), .procedureReturn (CallReach.bodyLabels e) :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.effectExpr e (extendEnv (ps.zip (objs.map ptrOf)) env),
        .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩ IntExpr.overflow := by
  unfold body at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      let B : EE := .mk ann (.sseq (.mk pann (.base (none, bt0))) a
        (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))))
      have hret : ReturnLabel (CallReach.bodyLabels B) ret := by
        refine ⟨r, bann, pann', r', hr, ?_⟩
        simp [B, CallReach.bodyLabels, saves, StmtIf.labelFree_saves a hfree, Map.ofList]
      let env₁ := extendEnv (ps.zip (objs.map ptrOf)) env
      let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
      let K := Frame.strongBind (.mk pann (.base (none, bt0))) SAVE env₁ ::
        .procedureReturn (CallReach.bodyLabels B) :: caller
      have hK : StateProc.Context (labels := labels) (CallReach.bodyLabels B) caller K := rfl
      have inv : Inv env₁ m (locals ps objs ++ []) (paramDefs ps ns) := by
        simpa using inv_params (env := env) hnd hlen mem hns
      have inLocals : ∀ l ∈ locals ps objs ++ [], ∃ o ∈ objs, l.id = o.1 ∧ l.addr = o.2 := by
        intro l hl
        simp only [List.append_nil] at hl
        obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp hl
        exact ⟨xo.2, (List.of_mem_zip hxo).2, rfl, rfl⟩
      have result := ParamRun.block_returns (labels := labels) hret (ps := ps) (pl := locals ps objs)
        (keys_locals hlen) J [] [] _ a h env₁ m inv rfl
        (by intro l hl; obtain ⟨o, ho, e1, -⟩ := inLocals l hl; rw [e1]; exact mem.below o ho)
        (by intro l hl; obtain ⟨o, ho, -, e2⟩ := inLocals l hl; rw [e2]; exact mem.above o ho)
        aligned room dead K hK
      have pre := CallLocal.sequence (file := file) (labels := labels) ann (.mk pann (.base (none, bt0)))
        a SAVE env₁ (.procedureReturn (CallReach.bodyLabels B) :: caller) m
      rcases ParamRun.Returns.pre pre (fun _ h => h) result with ⟨ok, m', out, uses, live, run⟩ | fail
      · refine .inl ⟨ok, m', out, uses, fun o ho => ?_, run⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
        have hi1 : i < ps.length := by omega
        exact live ⟨ps[i], objs[i].1, objs[i].2⟩ (List.mem_map_of_mem
          (f := fun xo : Sym × (Int × Int) => (⟨xo.1, xo.2.1, xo.2.2⟩ : Local)) (idx_mem_zip hi1 hi))
      · exact .inr fail
    · cases h
  · cases h

/-! ## The call in an operand arena -/

theorem reserve_mono {n n' : Nat} {m : Mem.Concrete.State} (h : Reserve n m) (le : n' ≤ n) :
    Reserve n' m :=
  ⟨h.dead, h.aligned, by have := h.room; omega⟩

/-- **A full call `g(n₁, …, nₖ)`**, including its caller-owned allocations and kills, executes
as the sole remaining operand of an arena. -/
theorem call_in_arena {fuel : Nat} {e : EE} {g : Sym} {ns : List Int} {t : IntExpr.Term}
    (hs : CallMany.argSite file e = some (g, ns)) (hc : callee file g ns = some t)
    (env : Env) (m : Mem.Concrete.State)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame)
    (hb : Reserve (fuel + ParamRun.maxLocals + ns.length) m) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩ ∨
    t.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve fuel m' ∧ CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave ((i, IntExpr.spec (t.val 0), xs) :: done) [], k, m'⟩ := by
  obtain ⟨loc, attrs, rty, pts, proto, dloc, marker, bt, params, body', hstd, hinfo, hdecl, hr, hpts,
    hlp, hlq, hnd, hbody⟩ := callee_spec hc
  obtain ⟨env', m₁, fr, objs, out₁, mem, reserve₁, pre, cleanup⟩ :=
    CallMany.argSite_prepared (fuel := fuel + ParamRun.maxLocals) (file := file) (labels := labels)
      hs hinfo hr hpts hlp env [] m hb
  have hlen : objs.length = ns.length := mem.slots.length_eq
  have hns : ∀ n ∈ ns, IsInt n := CallMany.argSite_range hs
  have pending : Pending [] i := ⟨by simp, by simp⟩
  have preRun : CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave done [(i, .apply (.procedure env') (fp g :: objs.map ptrOf), fr)], k, m₁⟩ := by
    apply reaches_of_local file labels
    have localPre : LocalReaches file labels (taskFlag false k [])
        ⟨.effectExpr e env, [], m⟩ ⟨.apply (.procedure env') (fp g :: objs.map ptrOf), fr, m₁⟩ := by
      simpa [taskFlag] using pre
    exact ArenaFail.drive_run file labels pending (done := done) (k := k) (wc := false)
      localPre (fun v h => by cases h)
  have resolved := CallReach.procedure_body (file := file) (values := objs.map ptrOf) hstd hdecl
    (by simp [hlq, hlen])
  have enter := ArenaCall.procedure_enter file labels m₁ done i g (objs.map ptrOf) env' body'
    ((params.map Prod.fst).zip (objs.map ptrOf)) fr k (CallReach.procedure_not_builtin hdecl) resolved
  have entry := preRun.trans (by simpa [CallReach.bodyLabels] using enter)
  rcases body_returns (labels := labels) hbody env' fr m₁ (by rw [List.map_map]; exact hnd) (by simp [hlq, hlen])
      mem hns reserve₁.aligned (by have := reserve₁.room; push_cast at this ⊢; omega) reserve₁.dead with
    ⟨ok, m₂, out₂, uses, live, run⟩ | fail
  · right
    let v := IntExpr.spec (t.val 0)
    obtain ⟨m₃, fs, xs, out₃, reserve₃, hfs, finish⟩ := cleanup fuel v m₂ live (reserve₁.uses uses)
      (fun o ho => by have := mem.below o ho; have := uses.next; omega)
    have pop : LocalReaches file labels false
        ⟨.value v, .procedureReturn (CallReach.bodyLabels body') :: fr, m₂⟩ ⟨.value v, fr, m₂⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_value _))
    have complete := run.trans (pop.trans finish)
    refine ⟨ok, m₃, xs, out₃.trans (out₂.trans out₁), reserve₃, entry.trans ?_⟩
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

/-! ## The call as the left operand of a comparison -/

/-- One call `g(n₁, …, nₖ)` with its closed callee term, compared with a closed operand. -/
structure Plan where
  callee : Sym
  arguments : List Int
  term : Term
  literal : Int
  rel : BinOp
  yes : Int
  no : Int

def Plan.result (p : Plan) : Term := .cmp p.rel p.yes p.no p.term (.lit p.literal)

/-- The operand recognizer reads syntax only. -/
def expr (file : File Codec.wireModel Unit Unit) (e : Eff) : Option Plan :=
  match e with
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [ec, rhs])) (.mk _ (.pure guard))) => do
      let n ← ClosedEff.flatLit file rhs
      if -2147483648 ≤ n ∧ n ≤ 2147483647 then
        let (g, ns) ← CallMany.argSite file ec
        let t ← callee file g ns
        let (r, y, z) ← StateExpr.cmpGuard' file a b guard
        pure ⟨g, ns, t, n, r, y, z⟩
      else none
  | _ => none

theorem expr_parts {e : EE} {p : Plan} (h : expr file e = some p) :
    ∃ an pp p1 p2 au ag a b ta tb ec rhs guard,
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)),
        .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [ec, rhs])) (.mk ag (.pure guard))) ∧
      ClosedEff.flatLit file rhs = some p.literal ∧
      CallMany.argSite file ec = some (p.callee, p.arguments) ∧
      callee file p.callee p.arguments = some p.term ∧ IsInt p.literal ∧
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
        cases hs : CallMany.argSite file ec with
        | none => simp [hs] at h
        | some pair =>
          obtain ⟨g, ns⟩ := pair
          cases hc : callee file g ns with
          | none => simp [hs, hc] at h
          | some t =>
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

variable {r : Nat}

/-- The cost of one call in allocations: its argument objects and the callee's locals. -/
def cost : Nat := ParamRun.maxLocals + CallMany.maxArgs

/-- The pure right operand finishes first; the call then runs inside the sole remaining
operand, with overflow propagated out of the arena. -/
theorem operands {ec : EE} {g : Sym} {ns : List Int} {t : Term} {c : Int}
    (hs : CallMany.argSite file ec = some (g, ns)) (hc : callee file g ns = some t)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {rhs : EE} (hrhs : ClosedEff.flatLit file rhs = some c) (hb : Reserve (r + cost) m) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave [] [(0, .effectExpr ec env, []), (1, .effectExpr rhs env, [])], k, m⟩ ∨
    t.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ CoreReaches file labels
      ⟨.interleave [] [(0, .effectExpr ec env, []), (1, .effectExpr rhs env, [])], k, m⟩
      ⟨.interleave [(0, spec (t.val 0), xs), (1, spec c, [])] [], k, m'⟩ := by
  have pending : Pending [(0, .effectExpr ec env, [])] 1 :=
    ⟨by simp, by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact activeCall_effectExpr ec env⟩
  obtain ⟨l, literal⟩ := ClosedEff.flatLit_task file labels (taskFlag false k [(0, .effectExpr ec env, [])])
    hrhs env m
  have first := reaches_of_local file labels
    (drive_task file labels pending (done := []) (k := k) (wc := false) literal)
  have hlen := (CallMany.argSite_len hs)
  rcases call_in_arena (fuel := r) (labels := labels) hs hc env {m with currentLocation := l}
      [(1, spec c, [])] 0 k (reserve_mono (hb.same ⟨rfl, rfl, rfl⟩) (by unfold cost; omega)) with
    ub | ⟨ok, m', xs, out, reserve, call⟩
  · exact .inl (StateStmt.Overflows.pre first ub)
  · exact .inr ⟨ok, m', xs, out, reserve, first.trans call⟩

/-- A comparison consumes the real result of its operand call. -/
theorem expr_runs {e : EE} {p : Plan} (h : expr file e = some p)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hb : Reserve (r + cost) m) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    p.result.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ Reaches file labels
      ⟨.effectExpr e env, k, m⟩
      ⟨.value (spec (p.result.val 0)), .annotations xs :: k, m'⟩ := by
  obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, ec, rhs, guard,
    rfl, hrhs, hs, hc, hlit, hg⟩ := expr_parts h
  let pat : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
  let K := Frame.effectBind pat (.mk ag (.pure guard)) env :: k
  have start : Reaches file labels
      ⟨.effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec, rhs])) (.mk ag (.pure guard)))) env, k, m⟩
      ⟨.interleave [] [(0, .effectExpr ec env, []), (1, .effectExpr rhs env, [])], K, m⟩ := by
    apply reaches_of_local file labels
    refine .head (.next (LoadTask.requestAux_wseq m an pat _ _ env k false)
      (LoadTask.plain_effectExpr _ _)) ?_
    exact .single (.next (requestAux_unseq file labels m au _ env K false) (plain_interleave _ _))
  rcases operands (labels := labels) hs hc env K m hrhs hb with ub | ⟨okt, m₁, xs, out₁, reserve₁, run⟩
  · exact .inl (StateStmt.Overflows.pre start ub)
  right
  have hn := IntExpr.Term.ok_int (n := 0) (by unfold IsInt; decide) p.term okt
  have hok : p.result.Ok 0 := ⟨okt, hlit, StateExpr.cmpGuard'_int hg⟩
  refine ⟨hok, ?_⟩
  have finish : Reaches file labels
      ⟨.interleave [(0, spec (p.term.val 0), xs), (1, spec p.literal, [])] [], K, m₁⟩
      ⟨.value (.tuple [spec (p.term.val 0), spec p.literal]), .annotations xs :: K, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (by
      simpa using requestAux_end file labels m₁
        [(0, spec (p.term.val 0), xs), (1, spec p.literal, [])] K false (by simp [NoRace])
        (by simp))
      (LoadTask.plain_value _))
  have bind : Reaches file labels
      ⟨.value (.tuple [spec (p.term.val 0), spec p.literal]), .annotations xs :: K, m₁⟩
      ⟨.effectExpr (.mk ag (.pure guard)) (Guard.operands a b (p.term.val 0) p.literal env),
        .annotations xs :: k, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
      (LoadTask.plain_effectExpr _ _))
  refine ⟨ReturnConst.focusMemory ag m₁, xs, by simp [out₁], reserve₁.focus ag, ?_⟩
  have final := start.trans (run.trans (finish.trans (bind.trans (reaches_of_local file labels
    (CallLocal.pure ag (fun _ => StateExpr.cmpGuard'_eval hg env hn hlit) _ _)))))
  simpa [Plan.result, IntExpr.Term.val] using final

/-- `if (g(n₁, …, nₖ) != c)`: both successors remain syntax. -/
def condition (file : File Codec.wireModel Unit Unit) : EE → Option (Plan × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) yes no))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true then
        (expr file ec).map fun t => (t, yes, no)
      else none
  | _ => none

theorem condition_inv {e yes no : EE} {t : Plan} (h : condition file e = some (t, yes, no)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : EE)
      (a3 a4 : List Annot) (b : Sym) (bty : BaseType) (cb : EE)
      (a5 a6 : List Annot) (b' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb
          (.mk a5 (.if_ (.mk a6 () (.sym b')) yes no))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ expr file ec = some t := by
  unfold condition at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨t', ht, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2, ht⟩
    · cases h
  · cases h

/-- Enter the selected branch, preserving stdout and the rest of the allocation reserve. -/
theorem condition_runs {e yes no : EE} {t : Plan} (shape : condition file e = some (t, yes, no))
    (env : Env) (m : Mem.Concrete.State) (k : List Frame) (hb : Reserve (r + cost) m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.result.Ok 0 ∧ ∃ env' m', m'.stdout = m.stdout ∧ Reserve r m' ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.result.val 0 = 1 then no else yes) env', k, m'⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, hb', hcb, htc⟩ :=
    condition_inv shape
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) yes no)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  rcases expr_runs (labels := labels) htc env (.bound :: K) m hb with
    ub | ⟨ok, m₁, xs', out₁, reserve₁, run⟩
  · exact .inl (Overflows.pre pre ub)
  · right
    let cv := t.result.val 0
    let env₁ := extendEnv [(c, IntExpr.spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then yes else no) env₂, k, SeqReach.focusMemory a5 m₂⟩ :=
      run.trans ((Locals.annotations_bound_reaches xs' _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have reserve := (reserve₁.touched tch₂).touched (seqFocus_touched a5 m₂)
    refine ⟨ok, env₂, _, (seqFocus_touched a5 m₂).stdout.trans (tch₂.stdout.trans out₁), reserve, ?_⟩
    have select : (if flag then yes else no) = (if t.result.val 0 = 1 then no else yes) := by
      change (if flag then yes else no) = (if cv = 1 then no else yes)
      by_cases h : cv = 1 <;> simp [flag, h]
    rw [select] at enter
    exact pre.trans enter

end Silmaril.Compile.Core.Verified.ParamMany
