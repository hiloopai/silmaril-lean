module

public import Silmaril.Compiler.Core.Verified.DoCondition.Defs

/-! # The dispatch of a `switch` statement

Cerberus elaborates `switch (e) { case k₁: … case kₙ: … default: … }` to a test of the
controlling expression, its integer promotion, then one jump per case label:

```
let strong c = bound(e) in
case c of
| Specified(z) =>
    let strong y: integer = pure(conv_int('signed int', z)) in
    if y = k₁ then run case₁() else pure(Unit) ; … ;
    if y = kₙ then run caseₙ() else pure(Unit) ;
    run default() ; …           -- `pure(Unit) ; run break()` without a `default`
| Unspecified(_) => undef(UB036)
end
```

The case bodies are saved labels of the `switch` (`case₁`, …, `default`, `break`), so the
control-flow graph of `Cfg` already holds them. `recognize` reads the controlling expression
as a `Term`, the case constants as `int` literals and the labels in order; nothing is
evaluated. `runs` evaluates the head (the controlling expression in the Core machine, its
promotion, which is the identity on an `int`) and `chain_runs` the tests, which reach the
`run` of the first label whose constant equals the value, or of the last label.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Switch

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open StateExpr (Key Term term values)
open StateMem (Local Inv Defined defsOf)
open StateStmt
open PureEval (Reaches Eval)
open ReturnLit (NoBoundary noBoundary_cons)

/-- A jump `run l(a₁, …, aₙ)`: the label and its arguments. -/
abbrev Jump := Sym × List PE

/-- The test `if y = k then run l(…) else pure(Unit)` of one case label, with an `int`
constant `k`. -/
def caseTest (y : Sym) : EE → Option (Int × Jump)
  | .mk _ (.if_ (.mk _ () (.op .eq (.mk _ () (.sym y')) (.mk _ () (.val (.object (.integer k))))))
      (.mk _ (.run () l args)) (.mk _ (.pure (.mk _ () (.val .unit))))) =>
    if y'.key = y.key ∧ -2147483648 ≤ k ∧ k ≤ 2147483647 then some (k, l, args) else none
  | _ => none

/-- The tests in order, then the final jump (to `default`, or to `break`). -/
def chain (y : Sym) : EE → Option (List (Int × Jump) × Jump)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a b) =>
    match caseTest y a with
    | some c => (chain y b).map fun r => (c :: r.1, r.2)
    | none => match a with
      | .mk _ (.pure (.mk _ () (.val .unit))) => chain y b
      | .mk _ (.run () l args) => some ([], l, args)
      | _ => none
  | .mk _ (.run () l args) => some ([], l, args)
  | _ => none

/-- The head of the `switch`: its controlling expression, the promoted value's symbol and the
tests. The temporaries must be fresh for every local object pointer. -/
def head (file : File Codec.wireModel Unit Unit) (xs : List Sym) :
    EE → Option (Term × Sym × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.case_ (.mk _ () (.sym c'))
        [(.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
          .mk _ (.sseq (.mk _ (.base (some y, _))) (.mk _ (.pure p)) body)),
         (.mk _ (.ctor .unspecified [_]), _)]))) =>
    if c'.key = c.key ∧ isFresh xs c = true ∧ isFresh xs z = true ∧ isFresh xs y = true ∧
        Guard.convOf file z p = true then
      (term file ec).map fun t => (t, y, body)
    else none
  | _ => none

/-- The three temporaries the head of a `switch` binds. -/
def binders : EE → List Sym
  | .mk _ (.sseq (.mk _ (.base (some c, _))) _
      (.mk _ (.case_ _
        [(.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
          .mk _ (.sseq (.mk _ (.base (some y, _))) _ _)),
         (.mk _ (.ctor .unspecified [_]), _)]))) => [c, z, y]
  | _ => []

/-- A `switch` statement: the controlling expression, the cases and the final jump. -/
def recognize (file : File Codec.wireModel Unit Unit) (xs : List Sym) (e : EE) :
    Option (Term × List (Int × Jump) × Jump) := do
  let (t, y, body) ← head file xs e
  let (cs, d) ← chain y body
  return (t, cs, d)

/-- The jump the dispatch takes for the value `v`. -/
def select (v : Int) : List (Int × Jump) → Jump → Jump
  | [], d => d
  | (k, j) :: cs, d => if v = k then j else select v cs d

theorem select_mem (v : Int) : (cs : List (Int × Jump)) → (d : Jump) →
    select v cs d = d ∨ select v cs d ∈ cs.map (·.2)
  | [], _ => .inl rfl
  | (k, l) :: cs, d => by
    unfold select
    split
    · exact .inr (List.mem_cons_self ..)
    · rcases select_mem v cs d with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem caseTest_inv {y : Sym} {e : EE} {k : Int} {l : Sym} {args : List PE}
    (h : caseTest y e = some (k, l, args)) :
    ∃ (a0 a1 a2 a3 a4 a5 a6 : List Annot) (y' : Sym),
      e = .mk a0 (.if_ (.mk a1 () (.op .eq (.mk a2 () (.sym y'))
        (.mk a3 () (.val (.object (.integer k)))))) (.mk a4 (.run () l args))
        (.mk a5 (.pure (.mk a6 () (.val .unit))))) ∧ y'.key = y.key := by
  unfold caseTest at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, rfl, hc.1⟩
    · cases h
  · cases h

theorem caseTest_int {y : Sym} {e : EE} {k : Int} {j : Jump} (h : caseTest y e = some (k, j)) :
    ConvInt.IsInt k := by
  unfold caseTest at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc.2
    · cases h
  · cases h

theorem chain_int {y : Sym} {e : EE} {cs : List (Int × Jump)} {d : Jump}
    (h : chain y e = some (cs, d)) : ∀ c ∈ cs, ConvInt.IsInt c.1 := by
  revert h
  fun_induction chain y e generalizing cs d with
  | case1 _ _ _ _ _ c hc ih =>
    intro h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨cs', d'⟩, h', rfl, rfl⟩ := h
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · obtain ⟨k, l⟩ := c'
      exact caseTest_int hc
    · exact ih h' c' hc'
  | case2 _ _ _ _ _ _ _ ih => exact ih
  | case3 | case5 =>
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | case4 | case6 => intro h; cases h

theorem recognize_int {file : File Codec.wireModel Unit Unit} {xs : List Sym} {e : EE}
    {t : Term} {cs : List (Int × Jump)} {d : Jump} (h : recognize file xs e = some (t, cs, d)) :
    ∀ c ∈ cs, ConvInt.IsInt c.1 := by
  simp only [recognize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨⟨t', y, body⟩, -, ⟨cs', d'⟩, hc, eq⟩ := h
  simp only [Prod.mk.injEq] at eq
  obtain ⟨-, rfl, rfl⟩ := eq
  exact chain_int hc

variable {file : Program} {labels : Labels}

/-- **The tests**: from the dispatch, with `y` bound to `v`, Core reaches the `run` of the
selected label, under frames without a procedure boundary. -/
theorem chain_runs {y : Sym} {e : EE} {cs : List (Int × Jump)} {d : Jump}
    (h : chain y e = some (cs, d)) (env : Env) (v : Int)
    (hy : env.lookup y = some (.object (.integer v))) (k : List Frame) (hk : NoBoundary k)
    (m : Mem.Concrete.State) :
    ∃ ann k' m', NoBoundary k' ∧ LoadTask.Touched m m' ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr (.mk ann (.run () (select v cs d).1 (select v cs d).2)) env, k', m'⟩ := by
  revert h
  fun_induction chain y e generalizing cs d k m with
  | case1 ann pann ty a b c hc ih =>
    intro h
    have push := ReturnConst.sequence_reaches file labels ann (.mk pann (.base (none, ty))) a b env k m
    let K := Frame.strongBind (.mk pann (.base (none, ty))) b env :: k
    have hK : NoBoundary K := noBoundary_cons hk trivial
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨cs', d'⟩, h', rfl, rfl⟩ := h
    obtain ⟨kc, l, args⟩ := c
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, y', rfl, hy'⟩ := caseTest_inv hc
    have hp : SeqReach.PureEval file labels (.mk a1 () (.op .eq (.mk a2 () (.sym y'))
        (.mk a3 () (.val (.object (.integer kc)))))) env (boolean (v == kc)) := by
      intro k' m'
      have eq : Eval file (PureEval.tagsOf file m') env
          (.inl (.mk a1 () (.op .eq (.mk a2 () (.sym y'))
            (.mk a3 () (.val (.object (.integer kc)))))))
          (.inl (boolean (v == kc))) :=
        .op (.cons (.sym (by rw [ReturnLit.lookup_key hy']; exact hy)) (.cons .val .nil))
          (by simp [primitive, integerBin, runtimeValue, runtimeObject]; rfl)
      exact (Eval.sound file _ eq) labels k' m' rfl
    have test := SeqReach.effect_if_reaches (file := file) (labels := labels) a0
      (yes := .mk a4 (.run () l args)) (no := .mk a5 (.pure (.mk a6 () (.val .unit)))) (v == kc) hp K m
    by_cases hv : v = kc
    · subst hv
      refine ⟨a4, K, _, hK, seqFocus_touched a0 m, ?_⟩
      have sel : select v ((v, l, args) :: cs') d' = (l, args) := by simp [select]
      rw [sel]
      simpa using push.trans test
    · have sel : select v ((kc, l, args) :: cs') d' = select v cs' d' := by simp [select, hv]
      rw [sel]
      have hb : (v == kc) = false := by simp [hv]
      rw [hb] at test
      have skip := (StateStmt.pure_unit_reaches (file := file) (labels := labels) a5 a6 env K
        (SeqReach.focusMemory a0 m)).trans
        (ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env k _)
      obtain ⟨ann', k', m', hk', tch, rest⟩ := ih k hk _ h'
      exact ⟨ann', k', m', hk', (seqFocus_touched a0 m).trans
        ((seqFocus_touched a5 _).trans tch), push.trans (test.trans (skip.trans rest))⟩
  | case2 ann pann ty b pa ppa _ ih =>
    intro h
    have push := ReturnConst.sequence_reaches file labels ann (.mk pann (.base (none, ty)))
      (.mk pa (.pure (.mk ppa () (.val .unit)))) b env k m
    let K := Frame.strongBind (.mk pann (.base (none, ty))) b env :: k
    obtain ⟨ann', k', m', hk', tch, rest⟩ := ih k hk _ h
    refine ⟨ann', k', m', hk', (seqFocus_touched pa m).trans tch, push.trans ?_⟩
    exact (StateStmt.pure_unit_reaches pa ppa env K m).trans
      ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env k _).trans rest)
  | case3 ann pann ty b ra l args _ =>
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ra, _, m, noBoundary_cons hk trivial, LoadTask.Touched.refl m,
      ReturnConst.sequence_reaches file labels ann _ _ b env k m⟩
  | case5 ann l args =>
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ann, k, m, hk, LoadTask.Touched.refl m, .refl⟩
  | case4 | case6 => intro h; cases h

/-- **The head**: the controlling expression runs in the Core machine (or overflows), its
promotion binds `y` to its value, and the locals keep their objects and values. -/
theorem head_runs {xs : List Sym} {e : EE} {t : Term} {y : Sym} {body : EE}
    (shape : head file xs e = some (t, y, body))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ env' m',
        LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧
        env'.lookup y = some (.object (.integer (t.val (values (defsOf ds))))) ∧
        (∀ w : Sym, (∀ z ∈ binders e, z.key ≠ w.key) → env'.lookup w = env.lookup w) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr body env', k, m'⟩ := by
  unfold head at shape
  split at shape
  · rename_i ann pann c cty bann ec cann pa c' sa spa z zty yann ypann y' yty pann' p body' ua up un
    split at shape
    · rename_i checks
      obtain ⟨hcc, fc, fz, fy, hconv⟩ := checks
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at shape
      obtain ⟨t', ht, rfl, rfl, rfl⟩ := shape
      let CASE : EE := .mk cann (.case_ (.mk pa () (.sym c'))
        [(.mk sa (.ctor .specified [.mk spa (.base (some z, zty))]),
          .mk yann (.sseq (.mk ypann (.base (some y', yty))) (.mk pann' (.pure p)) body')),
         (.mk ua (.ctor .unspecified [up]), un)])
      let K := Frame.strongBind (.mk pann (.base (some c, cty))) CASE env :: k
      have pre := (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
        (ReturnLit.bound_reaches bann ec env K m)
      by_cases ok : t'.Ok (values (defsOf ds))
      · right
        let v := t'.val (values (defsOf ds))
        obtain ⟨as, m₁, fr, hfr, _, touch, run⟩ := StateExpr.term_runs
          (file := file) (labels := labels) t' ht ok (.bound :: K) m (inv.locs defined)
        have toCase := (Interleave.reaches_of_local file labels run).trans
          ((bound_pop hfr _ K m₁).trans (ReturnLit.bind_reaches pann c cty _ CASE env k m₁))
        let env₁ := extendEnv [(c, IntExpr.spec v)] env
        have hs : SeqReach.PureEval file labels (.mk pa () (.sym c')) env₁ (IntExpr.spec v) :=
          SeqReach.pure_symbol pa c' env₁ _ (ConvInt.lookup_one hcc)
        have enter := SeqReach.specified_case_reaches (file := file) (labels := labels)
          cann sa ua (.mk spa (.base (some z, zty))) up
          (yes := .mk yann (.sseq (.mk ypann (.base (some y', yty))) (.mk pann' (.pure p)) body'))
          (no := un) hs
          (show matchPattern (.mk spa (.base (some z, zty))) (.object (.integer v)) =
            some [(z, .object (.integer v))] from rfl) k m₁
        let env₂ := extendEnv [(z, (.object (.integer v) : Val))] env₁
        let K₂ := Frame.strongBind (.mk ypann (.base (some y', yty))) body' env₂ :: k
        have hint : ConvInt.IsInt v := StateExpr.Term.int_of_ok t' ok
        have hp : SeqReach.PureEval file labels p env₂ (.object (.integer v)) := by
          intro k' m'
          exact (Eval.sound file _ (Guard.convOf_eval hconv hint (ConvInt.lookup_one rfl)))
            labels k' m' rfl
        have promote := (ReturnConst.sequence_reaches file labels yann _ _ _ env₂ k
            (SeqReach.focusMemory cann m₁)).trans
          ((SeqReach.effect_pure_reaches pann' hp K₂ _).trans
            (ReturnLit.bind_reaches ypann y' yty _ body' env₂ k _))
        have touched := touch.trans ((seqFocus_touched cann m₁).trans (seqFocus_touched pann' _))
        refine ⟨ok, _, _, touched,
          (((inv.touched touched).extend (keys.fresh fc)).extend (keys.fresh fz)).extend
            (keys.fresh fy), ConvInt.lookup_one rfl, fun w hw => ?_,
          pre.trans (toCase.trans (enter.trans promote))⟩
        have h1 : w.key ≠ c.key := fun h => hw c (by simp [binders]) h.symm
        have h2 : w.key ≠ z.key := fun h => hw z (by simp [binders]) h.symm
        have h3 : w.key ≠ y'.key := fun h => hw y' (by simp [binders]) h.symm
        rw [ConvInt.lookup_one_other h3, ConvInt.lookup_one_other h2, ConvInt.lookup_one_other h1]
      · left
        exact Overflows.pre pre (fails_overflows (StateExpr.term_fails
          (file := file) (labels := labels) t' ht ok (.bound :: K) m (inv.locs defined)))
    · cases shape
  · cases shape

/-- **A `switch`**: Core evaluates the controlling expression `t` (or overflows) and reaches the
`run` of the label `select` picks for its value. -/
theorem runs {xs : List Sym} {e : EE} {t : Term} {cs : List (Int × Jump)} {d : Jump}
    (shape : recognize file xs e = some (t, cs, d))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) (hk : NoBoundary k) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ env' m' ann k',
        LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧ NoBoundary k' ∧
        (∀ w : Sym, (∀ z ∈ binders e, z.key ≠ w.key) → env'.lookup w = env.lookup w) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (.mk ann (.run () (select (t.val (values (defsOf ds))) cs d).1
            (select (t.val (values (defsOf ds))) cs d).2)) env', k', m'⟩ := by
  simp only [recognize, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at shape
  obtain ⟨⟨t', y, body⟩, hh, ⟨cs', d'⟩, hc, eq⟩ := shape
  simp only [Prod.mk.injEq] at eq
  obtain ⟨rfl, rfl, rfl⟩ := eq
  rcases head_runs (labels := labels) hh inv keys defined k with
    ub | ⟨ok, env', m', tch, inv', hy, look, src⟩
  · exact .inl ub
  · obtain ⟨ann, k', m'', hk', tch', rest⟩ := chain_runs (file := file) (labels := labels) hc env' _ hy k hk m'
    refine .inr ⟨ok, env', m'', ann, k', tch.trans tch', inv'.touched tch', hk', fun w hw => look w ?_,
      src.trans rest⟩
    intro z hz
    unfold head at hh
    split at hh
    · exact hw z (by simpa [binders] using hz)
    · cases hh

end Silmaril.Compile.Core.Verified.Switch
