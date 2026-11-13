module

public import Silmaril.Compiler.Core.Verified.Rmw.Defs
public import Silmaril.Compiler.Core.Verified.StateStmt.Defs
public import Silmaril.Compiler.Core.Verified.StoreTask.Defs

/-! # `x++;` and `x--;` as statements: the proof

The dynamics runs a `seq_rmw` in one memory step: it loads the object, computes the update with
its own bounded pure evaluator (`Dynamics.evalUpdate`, depth 256), stores the result, and then
lifts the write's footprint out of the enclosing `bound` (`rmwFinish`, `rmwMarker`).

`update_ok`/`update_ub`: on an `int` slot holding `n`, the recognised update evaluates to
`n ± 1` when it is an `int`, and fails with Cerberus's exceptional condition otherwise; the
evaluation needs depth 12 (`upd_*`, each stated for every larger depth). `rmw_runs`: the
statement either reaches that undefined behaviour or stores `n ± 1` in the local and continues.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Rmw

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ConvInt (Pure Fun IsInt intTy lookupFun lookup_two_first lookup_two_second lookup_one
  functionBody_eq bounds_int bounds_bool)

variable {file : Program} {enums : Map Sym IntegerType}

/-! ## The update evaluator -/

theorem upd_val (f : Nat) (a : List Annot) (v : Value Codec.wireModel) (env : Env) :
    evalUpdate enums (f + 1) file (.mk a () (.val v)) env = .ok (runtimeValue v) := by
  simp [evalUpdate]; rfl

theorem upd_sym (f : Nat) (a : List Annot) {s : Sym} {v : Val} {env : Env}
    (h : env.lookup s = some v) :
    evalUpdate enums (f + 1) file (.mk a () (.sym s)) env = .ok v := by
  simp [evalUpdate, h]; rfl

theorem upd_op (f : Nat) (a : List Annot) (b : BinOp) {p q : PE} {env : Env} {x y v : Val}
    (hp : evalUpdate enums f file p env = .ok x) (hq : evalUpdate enums f file q env = .ok y)
    (hv : primitive (.bin b) [x, y] ⟨file.tagDefs, enums⟩ = .ok v) :
    evalUpdate enums (f + 1) file (.mk a () (.op b p q)) env = .ok v := by
  simp [evalUpdate, hp, hq, hv, bind, Except.bind, pure, Except.pure]

theorem upd_ctor1 (f : Nat) (a : List Annot) (c : Ctor) {p : PE} {env : Env} {x v : Val}
    (hp : evalUpdate enums f file p env = .ok x)
    (hv : primitive (.ctor c) [x] ⟨file.tagDefs, enums⟩ = .ok v) :
    evalUpdate enums (f + 1) file (.mk a () (.ctor c [p])) env = .ok v := by
  simp [evalUpdate, hp, hv, bind, Except.bind, pure, Except.pure]

theorem upd_convInt (f : Nat) (a : List Annot) (ty : IntegerType) {p : PE} {env : Env} {x v : Val}
    (hp : evalUpdate enums f file p env = .ok x)
    (hv : primitive (.conv ty) [x] ⟨file.tagDefs, enums⟩ = .ok v) :
    evalUpdate enums (f + 1) file (.mk a () (.convInt ty p)) env = .ok v := by
  simp [evalUpdate, hp, hv, bind, Except.bind, pure, Except.pure]

theorem upd_catch (f : Nat) (a : List Annot) (ty : IntegerType) (op : IntOp) {p q : PE} {env : Env}
    {x y : Val} {r : Except Outcome Val}
    (hp : evalUpdate enums f file p env = .ok x) (hq : evalUpdate enums f file q env = .ok y)
    (hv : primitive (.catchInt ty op) [x, y] ⟨file.tagDefs, enums⟩ = r) :
    evalUpdate enums (f + 1) file (.mk a () (.catchExceptionalCondition ty op p q)) env = r := by
  simp [evalUpdate, hp, hq, hv, bind, Except.bind, pure, Except.pure]

theorem upd_call2 (f : Nat) (a : List Annot) (name : Name Sym) {p q body : PE} {env env' : Env}
    {x y : Val} {r : Except Outcome Val}
    (hp : evalUpdate enums f file p env = .ok x) (hq : evalUpdate enums f file q env = .ok y)
    (hb : functionBody file name [x, y] = .ok (body, env'))
    (hv : evalUpdate enums f file body env' = r) :
    evalUpdate enums (f + 1) file (.mk a () (.call name [p, q])) env = r := by
  simp [evalUpdate, hp, hq, hb, hv, bind, Except.bind, pure, Except.pure]

theorem upd_if (f : Nat) (a : List Annot) {p yes no : PE} {env : Env} {b : Bool} {r : Except Outcome Val}
    (hp : evalUpdate enums f file p env = .ok (boolean b))
    (hv : evalUpdate enums f file (if b then yes else no) env = r) :
    evalUpdate enums (f + 1) file (.mk a () (.if_ p yes no)) env = r := by
  cases b <;> simp_all [evalUpdate, boolean, bind, Except.bind]

theorem upd_case (f : Nat) (a : List Annot) {p : PE} {bs : List (Pattern Sym × PE)} {env : Env}
    {x : Val} {xs : Bindings} {body : PE} {r : Except Outcome Val}
    (hp : evalUpdate enums f file p env = .ok x) (hs : selectCase x bs = some (xs, body))
    (hv : evalUpdate enums f file body (extendEnv xs env) = r) :
    evalUpdate enums (f + 1) file (.mk a () (.case_ p bs)) env = r := by
  simp [evalUpdate, hp, hs, hv, bind, Except.bind]

theorem upd_call2_err (f : Nat) (a : List Annot) (name : Name Sym) {p q : PE} {env : Env}
    {x : Val} {o : Outcome}
    (hp : evalUpdate enums f file p env = .ok x) (hq : evalUpdate enums f file q env = .error o) :
    evalUpdate enums (f + 1) file (.mk a () (.call name [p, q])) env = .error o := by
  simp [evalUpdate, hp, hq, bind, Except.bind]

theorem upd_ctor1_err (f : Nat) (a : List Annot) (c : Ctor) {p : PE} {env : Env} {o : Outcome}
    (hp : evalUpdate enums f file p env = .error o) :
    evalUpdate enums (f + 1) file (.mk a () (.ctor c [p])) env = .error o := by
  simp [evalUpdate, hp, bind, Except.bind]

variable (enums) in
/-- std.core's `is_representable_integer(n, int)` is `true` for an `int` `n`. -/
theorem upd_representable {r : Sym} {d : Fun} (hl : lookupFun file r = some d)
    (hd : ConvInt.isRepresentable d = true) {n : Int} (hn : IsInt n) {ann : List Annot} (g : Nat)
    {env : Env} {a : List Annot} {p q : PE}
    (hp : evalUpdate enums (g + 4) file p env = .ok (.object (.integer n)))
    (hq : evalUpdate enums (g + 4) file q env = .ok (.ctype (intTy ann))) :
    evalUpdate enums (g + 5) file (.mk a () (.call (.sym r) [p, q])) env = .ok .true := by
  unfold ConvInt.isRepresentable at hd
  split at hd
  · rename_i _ _ nn _ ty _ _ _ _ _ ty₁ _ n₁ _ _ n₂ _ _ ty₂
    simp only [decide_eq_true_eq] at hd
    obtain ⟨ne, e1, e2, e3, e4⟩ := hd
    refine upd_call2 _ _ _ hp hq (functionBody_eq hl rfl) ?_
    have lty : ∀ {s : Sym}, s.key = ty.key → (extendEnv [(nn, Value.object (.integer n)),
        (ty, .ctype (intTy ann))] ∅ : Env).lookup s = some (.ctype (intTy ann)) :=
      fun h => lookup_two_second h (Ne.symm ne)
    have ln : ∀ {s : Sym}, s.key = nn.key → (extendEnv [(nn, Value.object (.integer n)),
        (ty, .ctype (intTy ann))] ∅ : Env).lookup s = some (.object (.integer n)) :=
      fun h => lookup_two_first h
    obtain ⟨lo, hi⟩ := hn
    refine upd_op (x := .true) (y := .true) _ _ _ ?_ ?_ (by simp [primitive]; rfl)
    · refine upd_op (x := .object (.integer (-2147483648))) (y := .object (.integer n)) _ _ _ ?_
        (upd_sym _ _ (ln e3)) (by simp [primitive, Dynamics.integerBin, boolean, lo]; rfl)
      exact upd_ctor1 (x := .ctype (intTy ann)) _ _ _ (upd_sym _ _ (lty e1))
        (by simp [primitive, intTy, Dynamics.intType, bounds_int, integer]; rfl)
    · refine upd_op (x := .object (.integer n)) (y := .object (.integer 2147483647)) _ _ _
        (upd_sym _ _ (ln e4)) ?_ (by simp [primitive, Dynamics.integerBin, boolean, hi]; rfl)
      exact upd_ctor1 (x := .ctype (intTy ann)) _ _ _ (upd_sym _ _ (lty e2))
        (by simp [primitive, intTy, Dynamics.intType, bounds_int, integer]; rfl)
  · cases hd

variable (enums) in
/-- std.core's `conv_int(int, n)` is `n` for an `int` `n`. -/
theorem upd_convIntFun {c : Sym} {d : Fun} (hl : lookupFun file c = some d)
    (hd : ConvInt.convInt file d = true) {n : Int} (hn : IsInt n) {ann : List Annot} (g : Nat)
    {env : Env} {a : List Annot} {p q : PE}
    (hp : evalUpdate enums (g + 7) file p env = .ok (.ctype (intTy ann)))
    (hq : evalUpdate enums (g + 7) file q env = .ok (.object (.integer n))) :
    evalUpdate enums (g + 8) file (.mk a () (.call (.sym c) [p, q])) env = .ok (.object (.integer n)) := by
  unfold ConvInt.convInt at hd
  split at hd
  · rename_i _ _ ty _ nn _ _ _ _ ty₁ _ _ _ _ _ r _ n₁ _ ty₂ _ n₂ _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨ne, e1, e2, e3, e4⟩, hr⟩ := hd
    split at hr
    · rename_i d' hlr
      refine upd_call2 _ _ _ hp hq (functionBody_eq hl rfl) ?_
      have lty : ∀ {s : Sym}, s.key = ty.key → (extendEnv [(ty, Value.ctype (intTy ann)),
          (nn, .object (.integer n))] ∅ : Env).lookup s = some (.ctype (intTy ann)) :=
        fun h => lookup_two_first h
      have ln : ∀ {s : Sym}, s.key = nn.key → (extendEnv [(ty, Value.ctype (intTy ann)),
          (nn, .object (.integer n))] ∅ : Env).lookup s = some (.object (.integer n)) :=
        fun h => lookup_two_second h ne
      refine upd_if (b := false) _ _ ?_ ?_
      · exact upd_op (x := .ctype (intTy ann)) _ _ _ (upd_sym _ _ (lty e1)) (upd_val _ _ _ _)
          (by simp [primitive, intTy, Dynamics.intType, bounds_int, bounds_bool, boolean, runtimeValue]; rfl)
      refine upd_if (b := true) _ _ ?_ (upd_sym _ _ (ln e4))
      exact upd_representable enums hlr hr hn (ann := ann) g (upd_sym _ _ (ln e3))
        (upd_sym _ _ (lty e2))
    · cases hr
  · cases hd

variable (enums) in
/-- Cerberus's operand conversion `conv_int(int, z)` (a call or the primitive). -/
theorem upd_convOf {z : Sym} {q : PE} (h : Guard.convOf file z q = true) {n : Int} (hn : IsInt n)
    (g : Nat) {env : Env} (hz : env.lookup z = some (.object (.integer n))) :
    evalUpdate enums (g + 9) file q env = .ok (.object (.integer n)) := by
  unfold Guard.convOf at h
  split at h
  · rename_i _ c _ ann _ s'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs, hc⟩ := h
    split at hc
    · rename_i d hl
      have hs' : env.lookup s' = some (.object (.integer n)) := by
        rw [ReturnLit.lookup_key hs]; exact hz
      exact upd_convIntFun enums hl hc hn (ann := ann) (g + 1) (upd_val _ _ _ _) (upd_sym _ _ hs')
    · cases hc
  · rename_i _ _ s'
    have hs' : env.lookup s' = some (.object (.integer n)) := by
      rw [ReturnLit.lookup_key (of_decide_eq_true h)]; exact hz
    obtain ⟨lo, hi⟩ := hn
    exact upd_convInt _ _ _ (upd_sym _ _ hs')
      (by simp [primitive, bounds_int, lo, hi, integer]; rfl)
  · cases h

/-! ## The recognised statement -/

/-- The update `case v of Specified(z) => Specified(conv_int(int, catch(op, conv_int(int, z), 1)))
| …` of a recognised statement. -/
abbrev upd (A11 A12 : List Annot) (v' : Sym) (A13 A14 : List Annot) (z : Sym) (T2 : BaseType)
    (A15 A16 : List Annot) (c : Sym) (A17 A18 A19 : List Annot) (op : IntOp) (q : PE) (A20 : List Annot)
    (rest : List (Pattern Sym × PE)) : PE :=
  .mk A11 () (.case_ (.mk A12 () (.sym v'))
    ((.mk A13 (.ctor .specified [.mk A14 (.base (some z, T2))]),
      .mk A15 () (.ctor .specified [.mk A16 () (.call (.sym c)
        [.mk A17 () (.val (.ctype (.mk A18 (.basic (.integer (.signed .int)))))),
         .mk A19 () (.catchExceptionalCondition (.signed .int) op q
           (.mk A20 () (.val (.object (.integer 1)))))])])) :: rest))

theorem rmwStmt_inv {e : EE} {x : Sym} {op : IntOp} (h : rmwStmt file e = some (x, op)) :
    ∃ (A0 A1 : List Annot) (T0 : BaseType) (A2 A3 A4 : List Annot) (p : Sym) (T1 : BaseType)
      (A5 A6 A7 : List Annot) (L : Loc) (U : Unit) (A8 A9 A10 : List Annot) (p' v : Sym)
      (A11 A12 : List Annot) (v' : Sym) (A13 A14 : List Annot) (z : Sym) (T2 : BaseType)
      (A15 A16 : List Annot) (c : Sym) (A17 A18 A19 : List Annot) (q : PE) (A20 : List Annot)
      (rest : List (Pattern Sym × PE)) (A21 A22 : List Annot),
      e = .mk A0 (.sseq (.mk A1 (.base (none, T0)))
        (.mk A2 (.bound (.mk A3 (.wseq (.mk A4 (.base (some p, T1))) (.mk A5 (.pure (.mk A6 () (.sym x))))
          (.mk A7 (.action (.mk .pos (.mk L U (.seqRmw false
            (.mk A8 () (.val (.ctype (.mk A9 (.basic (.integer (.signed .int)))))))
            (.mk A10 () (.sym p')) v
            (upd A11 A12 v' A13 A14 z T2 A15 A16 c A17 A18 A19 op q A20 rest))))))))))
        (.mk A21 (.pure (.mk A22 () (.val .unit))))) ∧
      p'.key = p.key ∧ v'.key = v.key ∧ (op = .add ∨ op = .sub) ∧ Guard.convOf file z q = true ∧
      ∃ d, lookupFun file c = some d ∧ ConvInt.convInt file d = true := by
  unfold rmwStmt at h
  split at h
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hp, hv, rfl, hop⟩, hq⟩, hc⟩ := hc
      unfold convFun at hc
      split at hc
      · rename_i d hl
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, rfl, hp, hv, hop, hq, d, hl, hc⟩
      · cases hc
    · cases h
  · cases h

theorem arith_of {op : IntOp} (h : op = .add ∨ op = .sub) : Guard.arith op = true := by
  rcases h with rfl | rfl <;> rfl

variable (enums) in
/-- **The update** of `x++`/`x--` on `n` is `n ± 1` when it is an `int`. -/
theorem update_ok {A11 A12 : List Annot} {v v' : Sym} {A13 A14 : List Annot} {z : Sym}
    {T2 : BaseType} {A15 A16 : List Annot} {c : Sym} {A17 A18 A19 : List Annot} {op : IntOp}
    {q : PE} {A20 : List Annot} {rest : List (Pattern Sym × PE)} (hv : v'.key = v.key)
    (hop : op = .add ∨ op = .sub) (hq : Guard.convOf file z q = true) {d : Fun}
    (hl : lookupFun file c = some d) (hd : ConvInt.convInt file d = true) {n : Int} (hn : IsInt n)
    (hr : IsInt (Guard.apply op n 1)) (env : Env) (g : Nat) :
    evalUpdate enums (g + 13) file (upd A11 A12 v' A13 A14 z T2 A15 A16 c A17 A18 A19 op q A20 rest)
      (env.insert v (.loaded (.specified (.integer n)))) =
      .ok (.loaded (.specified (.integer (Guard.apply op n 1)))) := by
  have look : (env.insert v (.loaded (.specified (.integer n)))).lookup v' =
      some (.loaded (.specified (.integer n))) := by
    rw [ReturnLit.lookup_key hv]
    exact Map.lookup_insert v _ env
  refine upd_case _ _ (upd_sym _ _ look) (xs := [(z, .object (.integer n))]) rfl ?_
  have hz : (extendEnv [(z, Value.object (.integer n))]
      (env.insert v (.loaded (.specified (.integer n))))).lookup z = some (.object (.integer n)) :=
    lookup_one rfl
  refine upd_ctor1 _ _ _ (x := .object (.integer (Guard.apply op n 1))) ?_ (by simp [primitive]; rfl)
  refine upd_convIntFun enums hl hd hr (ann := A18) (g + 3) (upd_val _ _ _ _) ?_
  exact upd_catch _ _ _ _ (upd_convOf enums hq hn g hz) (upd_val _ _ _ _)
    (Guard.catchInt_ok (arith_of hop) hr _)

variable (enums) in
/-- **The update** of `x++`/`x--` on `n` fails with Cerberus's exceptional condition when
`n ± 1` is not an `int`. -/
theorem update_ub {A11 A12 : List Annot} {v v' : Sym} {A13 A14 : List Annot} {z : Sym}
    {T2 : BaseType} {A15 A16 : List Annot} {c : Sym} {A17 A18 A19 : List Annot} {op : IntOp}
    {q : PE} {A20 : List Annot} {rest : List (Pattern Sym × PE)} (hv : v'.key = v.key)
    (hop : op = .add ∨ op = .sub) (hq : Guard.convOf file z q = true) {n : Int} (hn : IsInt n)
    (hr : ¬ IsInt (Guard.apply op n 1)) (env : Env) (g : Nat) :
    evalUpdate enums (g + 13) file (upd A11 A12 v' A13 A14 z T2 A15 A16 c A17 A18 A19 op q A20 rest)
      (env.insert v (.loaded (.specified (.integer n)))) = .error IntExpr.overflow := by
  have look : (env.insert v (.loaded (.specified (.integer n)))).lookup v' =
      some (.loaded (.specified (.integer n))) := by
    rw [ReturnLit.lookup_key hv]
    exact Map.lookup_insert v _ env
  refine upd_case _ _ (upd_sym _ _ look) (xs := [(z, .object (.integer n))]) rfl ?_
  have hz : (extendEnv [(z, Value.object (.integer n))]
      (env.insert v (.loaded (.specified (.integer n))))).lookup z = some (.object (.integer n)) :=
    lookup_one rfl
  refine upd_ctor1_err _ _ _ ?_
  exact upd_call2_err _ _ _ (upd_val _ _ _ _)
    (upd_catch _ _ _ _ (upd_convOf enums hq hn g hz) (upd_val _ _ _ _)
      (Guard.catchInt_ub (arith_of hop) hr _))

/-! ## The run of the statement -/

open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches LocalStep TaskRuns TasksRun interleave_runs
  requestAux_end NoRace taskFlag)
open StateExpr (Key Term values close)
open StateMem (Local Inv defsOf update ptr)
open StateStmt (Overflows)
open Locals (Slot stored)

section run

variable {labels : Labels}

theorem fromMemory_int (ty : IntegerType) (n : Int) :
    fromMemory (.integer ty n) = .specified (.integer n) := rfl

/-- The read-modify-write of an `int` slot holding `n`, storing `n'`: one memory step. -/
theorem requestAux_rmw (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State}
    {id addr n n' : Int} (slot : Slot m id addr n) (hn : IsInt n) (hn' : IsInt n') (v : Sym) (u : PE)
    (env : Env)
    (hupd : evalUpdate m.enumTypes 256 file u (env.insert v (.loaded (.specified (.integer n)))) =
      .ok (.loaded (.specified (.integer n')))) :
    requestAux file labels m (.apply (.seqRMW false v u env)
      [.ctype (Mem.Concrete.intType ann), .object (.pointer (.allocated id addr))]) k false =
      .memory "SeqRMW" (stored {m with lastUsed := some id} id addr n')
        (.rmwFinish (.loaded (.specified (.integer n))) addr 4) k := by
  have live' : Mem.Concrete.LiveInt {m with lastUsed := some id} id addr :=
    Locals.liveInt_with slot.live rfl rfl
  have hupd' : evalUpdate m.enumTypes 256 file u
      (env.insert v (.loaded (fromMemory (.integer (.signed .int) n)))) =
      .ok (.loaded (.specified (.integer n'))) := hupd
  have hun : Mem.Concrete.unatomic (Mem.Concrete.intType ann) = Mem.Concrete.intType ann := rfl
  have hint : Dynamics.intType (Mem.Concrete.intType ann) = some (.signed .int) := rfl
  rw [requestAux.eq_def]
  simp [awaitsScheduling, Mem.Concrete.load_int _ ann slot.live slot.plain hn slot.bytes, hupd',
    toMemory, objectMemory, hun, hint, Mem.Concrete.store_int _ ann live' hn', stored, bind,
    Except.bind, pure, Except.pure, Except.mapError]
  exact fromMemory_int _ _

/-- The update fails: the read-modify-write ends with the failure. -/
theorem requestAux_rmw_ub (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State}
    {id addr n : Int} (slot : Slot m id addr n) (hn : IsInt n) (v : Sym) (u : PE) (env : Env)
    {o : Outcome}
    (hupd : evalUpdate m.enumTypes 256 file u (env.insert v (.loaded (.specified (.integer n)))) =
      .error o) :
    requestAux file labels m (.apply (.seqRMW false v u env)
      [.ctype (Mem.Concrete.intType ann), .object (.pointer (.allocated id addr))]) k false =
      .end_ o := by
  have hupd' : evalUpdate m.enumTypes 256 file u
      (env.insert v (.loaded (fromMemory (.integer (.signed .int) n)))) = .error o := hupd
  rw [requestAux.eq_def]
  simp [awaitsScheduling, Mem.Concrete.load_int _ ann slot.live slot.plain hn slot.bytes, hupd',
    bind, Except.bind, Except.mapError]

/-- The finished write is lifted out of the enclosing `bound` with its footprint. -/
theorem requestAux_finish (w : Val) (addr : Int) (k : List Frame) (m : Mem.Concrete.State) :
    requestAux file labels m (.rmwFinish w addr 4) (.bound :: k) false =
      .update {m with nextExcluded := m.nextExcluded + 1}
        (.interleave [] [(0, .rmwMarker addr 4, [.excluded m.nextExcluded]), (1, .value w, [])])
        (.liftedResult :: .bound :: k) := by
  rw [requestAux.eq_def]
  simp [awaitsScheduling, liftAction, excludePath, excludeFrames]

/-- The marker task records the write. -/
theorem marker_runs (addr : Int) (n : Nat) (m : Mem.Concrete.State) (wc : Bool) :
    TaskRuns file labels wc ⟨.rmwMarker addr 4, [.excluded n], m⟩ .unit
      [⟨some n, [], true, addr, 4⟩] m := by
  refine ⟨[.annotations [⟨some n, [], true, addr, 4⟩]], ?_, rfl⟩
  refine .tail (.single (.next (k' := [.annotations [⟨some n, [], true, addr, 4⟩], .excluded n]) ?_
    (LoadTask.plain_value .unit))) (.next ?_ (LoadTask.plain_value .unit))
  · rw [requestAux.eq_def]; simp [awaitsScheduling]
  · rw [requestAux.eq_def]; simp [awaitsScheduling, requestAux]

/-- The allocation state is unchanged: the next identifier, the dead objects and the last
address. -/
def Same (m m' : Mem.Concrete.State) : Prop :=
  m'.nextId = m.nextId ∧ m'.dead = m.dead ∧ m'.lastAddress = m.lastAddress

theorem Same.trans {m₁ m₂ m₃ : Mem.Concrete.State} (a : Same m₁ m₂) (b : Same m₂ m₃) : Same m₁ m₃ :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.trans a.2.2⟩

theorem same_focus (ann : List Annot) (m : Mem.Concrete.State) :
    Same m (ReturnConst.focusMemory ann m) := by
  obtain ⟨l, h⟩ := Locals.focusMemory_eq ann m
  rw [h]; exact ⟨rfl, rfl, rfl⟩

theorem same_stored (m : Mem.Concrete.State) (id addr n : Int) : Same m (stored m id addr n) := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m
  simp only [stored, hw]; exact ⟨rfl, rfl, rfl⟩

/-- `P` holds after the memory changes of the read-modify-write of a slot of `ls`: touching the
location, a fresh exclusion identifier, and a store at a slot. -/
def StmtClosed (P : Mem.Concrete.State → Prop) (ls : List Local) : Prop :=
  (∀ m m', P m → LoadTask.Touched m m' → P m') ∧
    (∀ (m : Mem.Concrete.State) (n : Nat), P m → P {m with nextExcluded := n}) ∧
    ∀ (m : Mem.Concrete.State) (v : Int), ∀ l ∈ ls, P m → P (stored m l.id l.addr v)

/-- What `x++;` does to memory: location updates, a store into one slot of `ls` and an
exclusion counter. Every property closed under these changes holds after it. -/
def Closes (ls : List Local) (m m' : Mem.Concrete.State) : Prop :=
  ∀ P : Mem.Concrete.State → Prop, (∀ {m₁ m₂}, P m₁ → LoadTask.Touched m₁ m₂ → P m₂) →
    (∀ {m₁} (n : Nat), P m₁ → P {m₁ with nextExcluded := n}) →
    (∀ {m₁} (l : Local) (v : Int), l ∈ ls → P m₁ → P (stored m₁ l.id l.addr v)) → P m → P m'

/-- A property closed under the read-modify-write changes holds after any `Closes` change. -/
theorem StmtClosed.closes {P : Mem.Concrete.State → Prop} {ls : List Local} (h : StmtClosed P ls)
    {m m' : Mem.Concrete.State} (c : Closes ls m m') (p : P m) : P m' :=
  c P (fun p t => h.1 _ _ p t) (fun n p => h.2.1 _ n p) (fun l v hl p => h.2.2 _ v l hl p) p

/-- **`x++;` / `x--;`** on a defined local: undefined behaviour, or `x` holds `x ± 1`, with the
allocation state unchanged and the memory changed only as `Closes` allows. -/
theorem rmw_runs_closed {e : EE} {x : Sym} {op : IntOp} (h : rmwStmt file e = some (x, op))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option StateExpr.PtsTo}
    (inv : Inv env m ls ds ps pts) (hd : (ds x.key).isSome) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      (Term.bin op (.var x.key) (.lit 1)).Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Same m m' ∧ Closes ls m m' ∧
        Inv env m' ls (update ds x.key (some (close (defsOf ds) (.bin op (.var x.key) (.lit 1))))) ps pts ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨A0, A1, T0, A2, A3, A4, p, T1, A5, A6, A7, L, U, A8, A9, A10, p', v, A11, A12, v', A13, A14,
    z, T2, A15, A16, c, A17, A18, A19, q, A20, rest, A21, A22, rfl, hp', hv, hop, hq, d, hl, hc⟩ :=
    rmwStmt_inv h
  obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨okx, l, hlm, hk, slot⟩ := inv.defs x.key dx hdx
  let σ := values (defsOf ds)
  let n := dx.val 0
  have hσ : σ x.key = n := by simp [σ, n, values, defsOf, hdx]
  have hn : IsInt n := IntExpr.Term.int_of_ok dx okx
  let t : Term := .bin op (.var x.key) (.lit 1)
  let UPD := upd A11 A12 v' A13 A14 z T2 A15 A16 c A17 A18 A19 op q A20 rest
  let PU : EE := .mk A21 (.pure (.mk A22 () (.val .unit)))
  let ACT : EE := .mk A7 (.action (.mk .pos (.mk L U (.seqRmw false
    (.mk A8 () (.val (.ctype (.mk A9 (.basic (.integer (.signed .int))))))) (.mk A10 () (.sym p')) v UPD))))
  let BODY : EE := .mk A3 (.wseq (.mk A4 (.base (some p, T1))) (.mk A5 (.pure (.mk A6 () (.sym x)))) ACT)
  let K := Frame.strongBind (.mk A1 (.base (none, T0))) PU env :: k
  let m₁ := ReturnConst.focusMemory A5 m
  let env₁ := extendEnv [(p, ptr l)] env
  have hx : env.lookup x = some (ptr l) := inv.lookup hlm hk.symm
  -- Up to the action: the sequence, the bound, the weak sequence and the read of `x`'s pointer.
  have pre : Reaches file labels ⟨.effectExpr (.mk A0 (.sseq (.mk A1 (.base (none, T0)))
      (.mk A2 (.bound BODY)) PU)) env, k, m⟩ ⟨.effectExpr ACT env₁, .bound :: K, m₁⟩ :=
    (ReturnConst.sequence_reaches file labels A0 _ _ PU env k m).trans
      ((ReturnLit.bound_reaches A2 BODY env K m).trans
        ((Locals.wseq_reaches A3 _ _ ACT env (.bound :: K) m).trans
          ((ReturnConst.effect_pure_reaches file labels A5 _ env _ m).trans
            (((SeqReach.pure_symbol A6 x env _ hx) _ _).trans
              ((ReturnConst.diagnostic_reaches file labels m.currentLocation (ptr l) _ m₁).trans
                (Locals.wbind_reaches A4 p T1 (ptr l) ACT env (.bound :: K) m₁))))))
  -- The action: its location, then its operands.
  let m₂ := ReturnConst.focusMemory A7 m₁
  let OP : Prim := .seqRMW false v UPD env₁
  let tyArg : PE := .mk A8 () (.val (.ctype (.mk A9 (.basic (.integer (.signed .int))))))
  let pArg : PE := .mk A10 () (.sym p')
  have hp'l : env₁.lookup p' = some (ptr l) := by
    rw [ReturnLit.lookup_key hp']; exact lookup_one rfl
  have req : requestAux file labels m₁ (.effectExpr ACT env₁) (.bound :: K) false =
      if (ReturnConst.focusMemory A7 m₁).currentLocation == m₁.currentLocation then
        .next (.pureExpr tyArg env₁) (.arguments OP [] [pArg] env₁ :: .bound :: K)
      else .next (.setLocation (ReturnConst.focusMemory A7 m₁).currentLocation (.pureExpr tyArg env₁))
        (.arguments OP [] [pArg] env₁ :: .bound :: K) := by
    simp only [ACT, requestAux, awaitsScheduling, arguments]
    rfl
  have hf : LocalReaches file labels false ⟨.effectExpr ACT env₁, .bound :: K, m₁⟩
      ⟨.pureExpr tyArg env₁, .arguments OP [] [pArg] env₁ :: .bound :: K, m₂⟩ := by
    obtain ⟨loc, hfocus⟩ := Locals.focusMemory_eq A7 m₁
    simp only [m₂]
    rw [hfocus] at req ⊢
    by_cases same : loc == m₁.currentLocation
    · have eq : loc = m₁.currentLocation := by simpa using same
      subst loc
      simpa using Relation.ReflTransGen.single (Interleave.LocalStep.next
        (by simpa using req) (LoadTask.plain_pureExpr tyArg env₁))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (Interleave.requestAux_setLocation file labels m₁ loc _ _ false)))
  have eval : Eval file (tagsOf file m₁) env₁ (.inr [tyArg, pArg])
      (.inr [.ctype (Mem.Concrete.intType A9), ptr l]) := .cons .val (.cons (.sym hp'l) .nil)
  have args := PureLocal.args_local file (tagsOf file m₁) (labels := labels) (wc := false) eval OP []
    (.bound :: K) m₂ (Locals.tagsOf_focus A7 m₁)
  simp only [argState, List.nil_append] at args
  have toApply := hf.trans args
  have slot₂ : Slot m₂ l.id l.addr n := Locals.slot_focus A7 (Locals.slot_focus A5 slot)
  have inv₂ : Inv env m₂ ls ds ps pts := (inv.focus A5).focus A7
  have tdef : StateMem.Defined ds (Term.bin op (.var x.key) (.lit 1)) = true := by
    simp [StateMem.Defined, Term.vars, hd]
  by_cases hr : IsInt (Guard.apply op n 1)
  · -- The update is in range: store it, lift the write, return `unit`.
    right
    let n' := Guard.apply op n 1
    have hupd : evalUpdate m₂.enumTypes 256 file UPD (env₁.insert v (.loaded (.specified (.integer n)))) =
        .ok (.loaded (.specified (.integer n'))) :=
      update_ok m₂.enumTypes hv hop hq hl hc hn hr env₁ 243
    let w : Val := .loaded (.specified (.integer n))
    let m₃ := stored {m₂ with lastUsed := some l.id} l.id l.addr n'
    have memStep : LocalStep file labels false ⟨.apply OP [.ctype (Mem.Concrete.intType A9), ptr l], .bound :: K, m₂⟩
        ⟨.rmwFinish w l.addr 4, .bound :: K, m₃⟩ :=
      .memory (requestAux_rmw A9 (.bound :: K) slot₂ hn hr v UPD env₁ hupd)
    let m₄ : Mem.Concrete.State := {m₃ with nextExcluded := m₃.nextExcluded + 1}
    let a : Access := ⟨some m₃.nextExcluded, [], true, l.addr, 4⟩
    let tasks : List (Nat × (Control × List Frame)) :=
      [(0, .rmwMarker l.addr 4, [.excluded m₃.nextExcluded]), (1, .value w, [])]
    let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, w, [])]
    let K' := Frame.liftedResult :: .bound :: K
    have finStep : LocalStep file labels false ⟨.rmwFinish w l.addr 4, .bound :: K, m₃⟩
        ⟨.interleave [] tasks, K', m₄⟩ :=
      .update (requestAux_finish w l.addr K m₃)
    have run : TasksRun file labels false K' tasks m₄ results m₄ := by
      have r0 : TasksRun file labels false K' [(0, .rmwMarker l.addr 4, [.excluded m₃.nextExcluded])]
          m₄ [(0, .unit, [a])] m₄ :=
        .snoc (marker_runs l.addr m₃.nextExcluded m₄ _) .nil
      exact .snoc ⟨[], .refl, rfl⟩ r0
    have arena := interleave_runs file labels run (by simp [tasks]) (by
      intro t ht
      simp only [tasks, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp [activeCall]) []
    have norace : NoRace results := by
      intro x hx y hy ne aa haa bb hbb
      simp only [results, List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
    have sorted : results.Pairwise fun a b => a.1 ≤ b.1 := by simp [results]
    have endStep := Interleave.LocalStep.next (requestAux_end file labels m₄ results K' false
      norace sorted) (LoadTask.plain_value _)
    rw [List.append_nil] at arena
    have local₁ := toApply.trans (Relation.ReflTransGen.single memStep |>.tail finStep |>.trans
      (arena.tail endStep))
    have selected : Reaches file labels
        ⟨.value (.tuple [.unit, w]), .annotations [a] :: K', m₄⟩
        ⟨.value w, .annotations [a] :: .bound :: K, m₄⟩ :=
      next_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling, K'])
    have tail := selected.trans ((Locals.annotations_bound_reaches [a] w K m₄).trans
      ((ReturnConst.wildcard_sequence_reaches file labels A1 T0 w PU env k m₄).trans
        (StateStmt.pure_unit_reaches A21 A22 env k m₄)))
    have middle := Interleave.reaches_of_local file labels local₁
    simp only [results, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at middle
    have hval : (close (defsOf ds) (Term.bin op (.var x.key) (.lit 1))).val 0 = n' := by
      rw [StateExpr.close_val]
      simp only [Term.val]
      rw [show values (defsOf ds) x.key = n from hσ]
    have tok : (Term.bin op (.var x.key) (.lit 1)).Ok σ := by
      refine ⟨?_, ?_, ?_⟩
      · change IsInt (σ x.key); rw [hσ]; exact hn
      · change IsInt 1; constructor <;> decide
      · change IsInt (Guard.apply op (σ x.key) 1); rw [hσ]; exact hr
    have okc := StateExpr.close_ok _ _ (inv.defs_ok tdef) tok
    have inv₃ := (inv₂.touched ⟨m₂.currentLocation, some l.id, rfl⟩).store hlm okc
    rw [hval, hk] at inv₃
    refine ⟨tok, ReturnConst.focusMemory A21 m₄, ?_, ?_, ?_, (inv₃.nextExcluded _).focus A21, ?_⟩
    · simp [m₄, m₃, m₂, m₁, Locals.stored_stdout]
    · have s₂ : Same m m₂ := (same_focus A5 m).trans (same_focus A7 m₁)
      have s₃ : Same m m₃ := s₂.trans (Same.trans (m₂ := {m₂ with lastUsed := some l.id})
        ⟨rfl, rfl, rfl⟩ (same_stored _ l.id l.addr n'))
      exact s₃.trans (Same.trans (m₂ := m₄) ⟨rfl, rfl, rfl⟩ (same_focus A21 m₄))
    · intro P touched excluded store p0
      have p2 : P m₂ := touched (touched p0 (LoadTask.focusMemory_touched A5 m))
        (LoadTask.focusMemory_touched A7 m₁)
      have p3 : P m₃ := store l n' hlm (touched p2 ⟨m₂.currentLocation, some l.id, rfl⟩)
      exact touched (excluded _ p3) (LoadTask.focusMemory_touched A21 m₄)
    · exact pre.trans (middle.trans tail)
  · -- The update leaves `int`: Cerberus's exceptional condition.
    left
    have hupd : evalUpdate m₂.enumTypes 256 file UPD (env₁.insert v (.loaded (.specified (.integer n)))) =
        .error IntExpr.overflow :=
      update_ub m₂.enumTypes hv hop hq hn hr env₁ 243
    have hreq : request file labels ⟨.apply OP [.ctype (Mem.Concrete.intType A9), ptr l], .bound :: K, m₂⟩ =
        .end_ IntExpr.overflow := by
      simp only [request]
      rw [requestAux_rmw_ub A9 (.bound :: K) slot₂ hn v UPD env₁ hupd]
    refine ⟨⟨.halt IntExpr.overflow, [], m₂⟩, pre.trans ((Interleave.reaches_of_local file labels toApply).trans
      (.single ⟨_, Step.respond (by intro o h; cases h) (hreq ▸ Respond.end_)⟩)), rfl⟩

/-- **`x++;` / `x--;`** on a defined local: undefined behaviour, or `x` holds `x ± 1`, with the
allocation state unchanged. -/
theorem rmw_runs_same {e : EE} {x : Sym} {op : IntOp} (h : rmwStmt file e = some (x, op))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option StateExpr.PtsTo}
    (inv : Inv env m ls ds ps pts) (hd : (ds x.key).isSome) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      (Term.bin op (.var x.key) (.lit 1)).Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Same m m' ∧
        Inv env m' ls (update ds x.key (some (close (defsOf ds) (.bin op (.var x.key) (.lit 1))))) ps pts ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  rcases rmw_runs_closed h inv hd k with ub | ⟨ok, m', out, same, -, inv', r⟩
  · exact .inl ub
  · exact .inr ⟨ok, m', out, same, inv', r⟩

/-- **`x++;` / `x--;`** on a defined local: undefined behaviour, or `x` holds `x ± 1`. -/
theorem rmw_runs {e : EE} {x : Sym} {op : IntOp} (h : rmwStmt file e = some (x, op))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option StateExpr.PtsTo}
    (inv : Inv env m ls ds ps pts) (hd : (ds x.key).isSome) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      (Term.bin op (.var x.key) (.lit 1)).Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds x.key (some (close (defsOf ds) (.bin op (.var x.key) (.lit 1))))) ps pts ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  rcases rmw_runs_same h inv hd k with ub | ⟨ok, m', out, -, inv', r⟩
  · exact .inl ub
  · exact .inr ⟨ok, m', out, inv', r⟩

end run

end Silmaril.Compile.Core.Verified.Rmw
