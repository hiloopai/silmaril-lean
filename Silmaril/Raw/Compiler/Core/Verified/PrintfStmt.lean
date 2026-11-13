module

public import Silmaril.Compiler.Core.Verified.StrLit.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # The statement `printf("…")`

Cerberus elaborates `printf(s)`, `s` a string literal without conversions and no further
argument, to (inside the statement's `bound`)

```
let strong ((f, (r, ps, va, pr)), a) =
  unseq(let strong f' = pure(<printf_proxy>) in pure((f', cfunction(f'))),
        let weak t₁ = pure(lit) in let weak t₂ = memop(PtrArrayShift, t₁, char, 0) in pure(Specified(t₂))) in
if not(params_length(ps) <= 1) then undef(UB038) else
if not(va) || not(are_compatible(int, r)) then undef(UB041) else
let strong p =
  { let t = params_nth(ps, 0) in
    if not(are_compatible(const char*, t)) then undef(UB041) else
    let weak x = create(Ivalignof(const char*), const char*) in
    let weak _ = store(const char*, x, a) in pure(x) } in
let strong ret = ccall(ty, f, [p, []]) in
let strong _ = kill(static const char*, p) in pure(ret)
```

`printfLit file ls fenv e = some cs` when `e` has this shape, `lit` is a string literal of `ls`
with the characters `cs` and no conversion (`PrintfStd.PlainFormat`), the callee is
`printf_proxy` with std.core's bodies (`PrintfStd.stdOf`), and the type checks fold to `false`
(`Fold.eval`, `ExitCall.foldsFalse`; the pointer compatibility check by `ptrCompat`). This is
syntax and constant folding of the checks, not an execution of the program.

`printfLit_reaches`: the statement prints the literal's characters and returns their number,
in any environment that holds the literals and the folder's bindings, under any continuation,
from any memory with room for the argument object; it keeps every earlier object.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfStmt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold (WVal WEnv PExp Doc eval matchP extend EnvSub)
open StrMem PrintfStd StrLit

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-! ## The recogniser

Piece by piece, each piece one small pattern (as `PrintfStd`). -/

/-- `let weak x = a in b`: `x`, `a`, `b`. -/
def wseqOf : EExp → Option (Sym × EExp × EExp)
  | .mk _ (.wseq (.mk _ (.base (some x, _))) a b) => some (x, a, b)
  | _ => none

/-- `let weak _ = a in b`: `a`, `b`. -/
def wseqNone : EExp → Option (EExp × EExp)
  | .mk _ (.wseq (.mk _ (.base (none, _))) a b) => some (a, b)
  | _ => none

/-- `let strong _ = a in b`: `a`, `b`. -/
def sseqNone : EExp → Option (EExp × EExp)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => some (a, b)
  | _ => none

/-- `pure(Specified(x))`. -/
def pureSpecified : EExp → Option Sym
  | .mk _ (.pure (.mk _ _ (.ctor .specified [.mk _ _ (.sym x)]))) => some x
  | _ => none

/-- The format task `let weak t₁ = pure(lit) in let weak t₂ = memop(PtrArrayShift, t₁, char, 0) in
pure(Specified(t₂))`: the literal it decays. -/
def fmtTask (e : EExp) : Option Sym := do
  let (t1, e1, r1) ← wseqOf e
  let lit ← pureSym e1
  let (t2, e2, r2) ← wseqOf r1
  let (t1', n) ← shiftOf e2
  let t2' ← pureSpecified r2
  if n = 0 ∧ t1'.key = t1.key ∧ t2'.key = t2.key ∧ t1.key ≠ lit.key then some lit else none

/-- `let strong (pf, a) = unseq(t₀, t₁) in if c₁ then _ else if c₂ then _ else
let strong p = argobj in rest`. -/
def stmtShape : EExp → Option (Pattern Sym × Sym × EExp × EExp × PExp × PExp × Sym × EExp × EExp)
  | .mk _ (.sseq (.mk _ (.ctor .tuple [pf, .mk _ (.base (some a, _))])) (.mk _ (.unseq [t0, t1]))
      (.mk _ (.if_ c1 _ (.mk _ (.if_ c2 _ (.mk _ (.sseq (.mk _ (.base (some p, _))) argobj rest))))))) =>
      some (pf, a, t0, t1, c1, c2, p, argobj, rest)
  | _ => none

/-- `let pt = nth in b`. -/
def letOf : EExp → Option (Pattern Sym × PExp × EExp)
  | .mk _ (.let_ pt nth b) => some (pt, nth, b)
  | _ => none

/-- `if not(are_compatible(T, t)) then _ else no`: `T`, `t`, `no`. -/
def ifNotCompat : EExp → Option (Ctype × Sym × EExp)
  | .mk _ (.if_ (.mk _ _ (.not (.mk _ _ (.areCompatible (.mk _ _ (.val (.ctype ct))) (.mk _ _ (.sym t))))))
      _ no) => some (ct, t, no)
  | _ => none

/-- `create(Ivalignof(T₁), T₂)`. -/
def createOf : EExp → Option (Ctype × Ctype)
  | .mk _ (.action (.mk .pos (.mk _ _ (.create (.mk _ _ (.ctor .ivAlignof [.mk _ _ (.val (.ctype ct1))]))
      (.mk _ _ (.val (.ctype ct2))) _)))) => some (ct1, ct2)
  | _ => none

/-- `store(T, x, a)` (not locking, non-atomic). -/
def storeOf : EExp → Option (Ctype × Sym × Sym)
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false (.mk _ _ (.val (.ctype ct))) (.mk _ _ (.sym x))
      (.mk _ _ (.sym a)) .na)))) => some (ct, x, a)
  | _ => none

/-- `ccall(_, g, [q, []])`. -/
def ccallNil : EExp → Option (Sym × Sym)
  | .mk _ (.ccall _ _ (.mk _ _ (.sym g)) [.mk _ _ (.sym q), .mk _ _ (.ctor (.nil _) [])]) => some (g, q)
  | _ => none

/-- `kill(static T, q)`. -/
def killOf : EExp → Option (Ctype × Sym)
  | .mk _ (.action (.mk .pos (.mk _ _ (.kill (.static kt) (.mk _ _ (.sym q)))))) => some (kt, q)
  | _ => none

/-- `are_compatible` of two pointer-to-integer types: same qualifiers, same integer type (no
enums), as the dynamics' `Core.compatibleWith` decides it. -/
def ptrCompat : Ctype → Ctype → Bool
  | .mk _ (.pointer q (.mk _ (.basic (.integer a)))), .mk _ (.pointer q' (.mk _ (.basic (.integer b)))) =>
      match Fold.nonEnum a, Fold.nonEnum b with
      | some a, some b => q == q' && Core.normalizeInteger a == Core.normalizeInteger b &&
          (Core.normalizeInteger a).isSome
      | _, _ => false
  | _, _ => false

/-- The pointer argument object `let t = params_nth(…) in if not(are_compatible(T, t)) then undef
else let weak x = create(Ivalignof(T), T) in let weak _ = store(T, x, a) in pure(x)`, `T` a
`char` pointer type: `T`. -/
def ptrArg (file : Doc) (fenv : WEnv) (a : Sym) (e : EExp) : Option Ctype := do
  let (pt, nth, b) ← letOf e
  let w ← eval file Return.fuel fenv nth
  let ys ← matchP pt w
  let (ct, t, no) ← ifNotCompat b
  let (x, cr, r1) ← wseqOf no
  let (ct1, ct2) ← createOf cr
  let (st, r2) ← wseqNone r1
  let (ct3, x', a') ← storeOf st
  let x'' ← pureSym r2
  match (extend ys fenv).lookup t with
  | some (.ctype ct') =>
      if isCharPtr ct ∧ ptrCompat ct ct' ∧ ct1 = ct ∧ ct2 = ct ∧ ct3 = ct ∧ x'.key = x.key ∧
          x''.key = x.key ∧ a'.key = a.key ∧ x.key ≠ a.key ∧ (∀ y ∈ ys, y.1.key ≠ a.key)
      then some ct else none
  | _ => none

/-- `let strong ret = ccall(ty, g, [q, []]) in let strong _ = kill(static T, q') in pure(ret)`:
the callee and the argument symbols. -/
def callPrintf (rest : EExp) : Option (Sym × Sym) := do
  let (ret, cl, r1) ← sseqOf rest
  let (g, q) ← ccallNil cl
  let (kl, r2) ← sseqNone r1
  let (kt, q') ← killOf kl
  let ret' ← pureSym r2
  if isCharPtr kt ∧ q'.key = q.key ∧ ret'.key = ret.key ∧ ret.key ≠ q.key then some (g, q) else none

/-- The literal `lit` of `ls`. -/
def litOf (ls : List (Sym × List Int)) (lit : Sym) : Option (List Int) :=
  (ls.find? fun y => y.1.key == lit.key).map Prod.snd

/-- **The statement** `printf(s)`: the characters of `s`. -/
def printfLit (file : Doc) (ls : List (Sym × List Int)) (fenv : WEnv) (e : EExp) :
    Option (List Int) := do
  let (pf, a, t0, t1, c1, c2, p, argobj, rest) ← stmtShape e
  let w0 ← ExitCall.calleeTask file t0
  let lit ← fmtTask t1
  let cs ← litOf ls lit
  let xs ← matchP pf w0
  let _ ← ptrArg file (extend xs fenv) a argobj
  let (g, q) ← callPrintf rest
  match (extend xs fenv).lookup g with
  | some (.loaded (.specified (.pointer (.function y)))) =>
      if PlainFormat cs ∧ (∀ y ∈ xs, y.1.key ≠ a.key) ∧ fenv.lookup a = none ∧
          ExitCall.foldsFalse file (extend xs fenv) c1 ∧ ExitCall.foldsFalse file (extend xs fenv) c2 ∧
          q.key = p.key ∧ g.key ≠ p.key ∧ (stdOf file y).isSome
      then some cs else none
  | _ => none

/-- A recognised statement prints a plain format. -/
theorem printfLit_plain {file : Doc} {ls : List (Sym × List Int)} {fenv : WEnv} {e : EExp}
    {cs : List Int} (h : printfLit file ls fenv e = some cs) : PlainFormat cs := by
  unfold printfLit at h
  obtain ⟨_, -, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨_, -, h⟩ := PrintfStd.bind_some h
  obtain ⟨_, -, h⟩ := PrintfStd.bind_some h
  obtain ⟨_, -, h⟩ := PrintfStd.bind_some h
  obtain ⟨_, -, h⟩ := PrintfStd.bind_some h
  obtain ⟨_, -, h⟩ := PrintfStd.bind_some h
  obtain ⟨_, -, h⟩ := PrintfStd.bind_some h
  split at h
  · split at h
    · rename_i hc; cases h; exact hc.1
    · cases h
  · cases h

/-! ## Inversions of the pieces -/

theorem wseqOf_inv {e : EExp} {x : Sym} {a b : EExp} (h : wseqOf e = some (x, a, b)) :
    ∃ ann pa bt, e = .mk ann (.wseq (.mk pa (.base (some x, bt))) a b) := by
  unfold wseqOf at h; split at h
  · cases h; exact ⟨_, _, _, rfl⟩
  · cases h

theorem wseqNone_inv {e : EExp} {a b : EExp} (h : wseqNone e = some (a, b)) :
    ∃ ann pa bt, e = .mk ann (.wseq (.mk pa (.base (none, bt))) a b) := by
  unfold wseqNone at h; split at h
  · cases h; exact ⟨_, _, _, rfl⟩
  · cases h

theorem sseqNone_inv {e : EExp} {a b : EExp} (h : sseqNone e = some (a, b)) :
    ∃ ann pa bt, e = .mk ann (.sseq (.mk pa (.base (none, bt))) a b) := by
  unfold sseqNone at h; split at h
  · cases h; exact ⟨_, _, _, rfl⟩
  · cases h

theorem pureSpecified_inv {e : EExp} {x : Sym} (h : pureSpecified e = some x) :
    ∃ ann a u a1 u1, e = .mk ann (.pure (.mk a u (.ctor .specified [.mk a1 u1 (.sym x)]))) := by
  unfold pureSpecified at h; split at h
  · cases h; exact ⟨_, _, _, _, _, rfl⟩
  · cases h

theorem stmtShape_inv {e : EExp} {pf : Pattern Sym} {a : Sym} {t0 t1 : EExp} {c1 c2 : PExp} {p : Sym}
    {argobj rest : EExp} (h : stmtShape e = some (pf, a, t0, t1, c1, c2, p, argobj, rest)) :
    ∃ a0 a1 pa ba a2 a3 u3 a4 u4 a5 pp bp, e = .mk a0 (.sseq (.mk a1 (.ctor .tuple [pf, .mk pa (.base (some a, ba))]))
      (.mk a2 (.unseq [t0, t1])) (.mk a3 (.if_ c1 u3 (.mk a4 (.if_ c2 u4
        (.mk a5 (.sseq (.mk pp (.base (some p, bp))) argobj rest))))))) := by
  unfold stmtShape at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem letOf_inv {e : EExp} {pt : Pattern Sym} {nth : PExp} {b : EExp} (h : letOf e = some (pt, nth, b)) :
    ∃ ann, e = .mk ann (.let_ pt nth b) := by
  unfold letOf at h; split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

theorem ifNotCompat_inv {e : EExp} {ct : Ctype} {t : Sym} {no : EExp} (h : ifNotCompat e = some (ct, t, no)) :
    ∃ ann a u a1 u1 a2 u2 a3 u3 yes, e = .mk ann (.if_ (.mk a u (.not (.mk a1 u1 (.areCompatible
      (.mk a2 u2 (.val (.ctype ct))) (.mk a3 u3 (.sym t)))))) yes no) := by
  unfold ifNotCompat at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem createOf_inv {e : EExp} {ct1 ct2 : Ctype} (h : createOf e = some (ct1, ct2)) :
    ∃ ann l u a1 u1 a2 u2 a3 u3 pref, e = .mk ann (.action (.mk .pos (.mk l u (.create
      (.mk a1 u1 (.ctor .ivAlignof [.mk a2 u2 (.val (.ctype ct1))])) (.mk a3 u3 (.val (.ctype ct2))) pref)))) := by
  unfold createOf at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem storeOf_inv {e : EExp} {ct : Ctype} {x a : Sym} (h : storeOf e = some (ct, x, a)) :
    ∃ ann l u a1 u1 a2 u2 a3 u3, e = .mk ann (.action (.mk .pos (.mk l u (.store false
      (.mk a1 u1 (.val (.ctype ct))) (.mk a2 u2 (.sym x)) (.mk a3 u3 (.sym a)) .na)))) := by
  unfold storeOf at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem ccallNil_inv {e : EExp} {g q : Sym} (h : ccallNil e = some (g, q)) :
    ∃ ann u ty a1 u1 a2 u2 a3 u3 bt, e = .mk ann (.ccall u ty (.mk a1 u1 (.sym g))
      [.mk a2 u2 (.sym q), .mk a3 u3 (.ctor (.nil bt) [])]) := by
  unfold ccallNil at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem killOf_inv {e : EExp} {kt : Ctype} {q : Sym} (h : killOf e = some (kt, q)) :
    ∃ ann l u a1 u1, e = .mk ann (.action (.mk .pos (.mk l u (.kill (.static kt) (.mk a1 u1 (.sym q)))))) := by
  unfold killOf at h; split at h
  · cases h; exact ⟨_, _, _, _, _, rfl⟩
  · cases h

/-! ## Steps -/

section Steps
variable (file : Program) (labels : Labels)

local notation "rv" => runtimeValue

open ExitCall (lift plain_effectExpr plain_value plain_pureExpr plain_apply ra_sseq ra_wseq ra_sym ra_val
  ra_args_cons ra_args_nil ra_effectBind ra_strongBind ra_diagnostic ra_ctor ra_annotations)
open Interleave (TaskRuns LocalReaches LocalStep)

/-- A located `memop(op, p :: ps)` over any frames: the focus, then its first operand. -/
theorem memop_local {wc : Bool} {env : Env} {k : List Frame} {m : Mem.Concrete.State}
    (annots : List Annot) (p : PE) (ps : List PE) :
    ∃ l, LocalReaches file labels wc ⟨.effectExpr (.mk annots (.memop .ptrArrayShift (p :: ps))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.memop .ptrArrayShift) [] ps env :: k, {m with currentLocation := l}⟩ := by
  have hr : ∃ l, requestAux file labels m (.effectExpr (.mk annots (.memop .ptrArrayShift (p :: ps))) env) k wc =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.arguments (.memop .ptrArrayShift) [] ps env :: k)
      else .next (.setLocation l (.pureExpr p env)) (.arguments (.memop .ptrArrayShift) [] ps env :: k) := by
    rw [requestAux.eq_def]
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true, arguments]
    split
    · split
      · exact ⟨m.currentLocation, by simp⟩
      · exact ⟨_, rfl⟩
    · exact ⟨m.currentLocation, by simp⟩
  obtain ⟨l, hr⟩ := hr
  by_cases hl : (({m with currentLocation := l} : Mem.Concrete.State).currentLocation ==
      m.currentLocation) = true
  · simp only [hl, ↓reduceIte] at hr
    exact ⟨m.currentLocation, .single (.next hr (plain_pureExpr _ _))⟩
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr
    exact ⟨l, .head (.next hr ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
      (.single (.update (Interleave.requestAux_setLocation file labels m l _ _ wc)))⟩

theorem ra_shift0 {k : List Frame} {m : Mem.Concrete.State} {sid saddr : Int}
    {cs : List Int} (hs : StrObj m sid saddr cs) {t : Ctype} (ht : isChar t = true) :
    requestAux file labels m (.apply (.memop .ptrArrayShift)
      [.object (.pointer (.allocated sid saddr)), .ctype t, .object (.integer 0)]) k false =
      .next (.value (.object (.pointer (.allocated sid saddr)))) k := by
  obtain ⟨tann, rfl⟩ := PrintfStd.isChar_inv ht
  have := shift_char ⟨file.tagDefs, m.enumTypes⟩ tann hs 0 0 (by omega) (by omega)
  simp only [add_zero] at this
  rw [requestAux.eq_def]
  simp [awaitsScheduling, this, pure, Except.pure, bind, Except.bind]

theorem ra_specified {wc : Bool} {k : List Frame} {m : Mem.Concrete.State}
    (o : ObjectValue Mem.Concrete.model) :
    requestAux file labels m (.apply (.ctor .specified) [.object o]) k wc =
      .next (.value (.loaded (.specified o))) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, primitive, pure, Except.pure]

/-- **The format task runs** to the pointer to the literal's first character, reading nothing. -/
theorem fmtTask_runs {t : EExp} {lit : Sym} (h : fmtTask t = some lit) {env : Env} {sid saddr : Int}
    (hl : env.lookup lit = some (.object (.pointer (.allocated sid saddr)))) {cs : List Int}
    (m : Mem.Concrete.State) (hs : StrObj m sid saddr cs) :
    ∃ l, TaskRuns file labels false ⟨.effectExpr t env, [], m⟩
      (.loaded (.specified (.pointer (.allocated sid saddr)))) [] {m with currentLocation := l} := by
  unfold fmtTask at h
  obtain ⟨⟨t1, e1, r1⟩, q1, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨lit', q2, h⟩ := PrintfStd.bind_some h
  obtain ⟨⟨t2, e2, r2⟩, q3, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨t1', n⟩, q4, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨t2', q5, h⟩ := PrintfStd.bind_some h
  split at h
  case isFalse => cases h
  rename_i hc
  cases h
  obtain ⟨rfl, k1, k2, n12⟩ := hc
  obtain ⟨A0, P0, b0, rfl⟩ := wseqOf_inv q1
  obtain ⟨A1, a1, u1, rfl⟩ := pureSym_inv q2
  obtain ⟨A2, P2, b2, rfl⟩ := wseqOf_inv q3
  obtain ⟨A3, a4, u4, a5, u5, ct, a6, u6, rfl, hct⟩ := shiftOf_inv q4
  obtain ⟨A7, a8, u8, a9, u9, rfl⟩ := pureSpecified_inv q5
  let P : Val := .object (.pointer (.allocated sid saddr))
  let env1 := extendEnv [(t1, P)] env
  let env2 := extendEnv [(t2, P)] env1
  obtain ⟨l1, rp1⟩ := ExitCall.pure_local file labels (wc := false) (env := env)
    (k := [.effectBind (.mk P0 (.base (some t1, b0))) (.mk A2 (.wseq (.mk P2 (.base (some t2, b2)))
      (.mk A3 (.memop .ptrArrayShift [.mk a4 u4 (.sym t1'), .mk a5 u5 (.val (.ctype ct)),
        .mk a6 u6 (.val (.object (.integer 0)))]))
      (.mk A7 (.pure (.mk a8 u8 (.ctor .specified [.mk a9 u9 (.sym t2')])))))) env]) (m := m) A1
    (.mk a1 u1 (.sym lit))
  let m1 : Mem.Concrete.State := {m with currentLocation := l1}
  obtain ⟨l2, rm⟩ := memop_local file labels (wc := false) (env := env1)
    (k := [.effectBind (.mk P2 (.base (some t2, b2)))
      (.mk A7 (.pure (.mk a8 u8 (.ctor .specified [.mk a9 u9 (.sym t2')])))) env1]) (m := m1) A3
    (.mk a4 u4 (.sym t1')) [.mk a5 u5 (.val (.ctype ct)), .mk a6 u6 (.val (.object (.integer 0)))]
  let m2 : Mem.Concrete.State := {m1 with currentLocation := l2}
  have hs2 : StrObj m2 sid saddr cs := hs.keeps (((Keeps.refl m).location l1).location l2)
  obtain ⟨l3, rp3⟩ := ExitCall.pure_local file labels (wc := false) (env := env2) (k := []) (m := m2) A7
    (.mk a8 u8 (.ctor .specified [.mk a9 u9 (.sym t2')]))
  refine ⟨l3, [], ?_, rfl⟩
  refine .head (.next (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)) ?_
  refine rp1.trans ?_
  refine .head (.next (ra_sym file labels _ _ hl) (plain_value _)) ?_
  refine .head (.next (ra_diagnostic file labels _ _) (plain_value _)) ?_
  refine .head (.next (ra_effectBind file labels (xs := [(t1, P)]) rfl _ _) (plain_effectExpr _ _)) ?_
  refine .head (.next (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)) ?_
  refine rm.trans ?_
  refine .head (.next (ra_sym file labels _ _ (PrintfStd.lk_same k1 _ _)) (plain_value _)) ?_
  refine .head (.next (ra_args_cons file labels _ _ _ _ _) (plain_pureExpr _ _)) ?_
  refine .head (.next (ra_val file labels _ _ _) (plain_value _)) ?_
  refine .head (.next (ra_args_cons file labels _ _ _ _ _) (plain_pureExpr _ _)) ?_
  refine .head (.next (ra_val file labels _ _ _) (plain_value _)) ?_
  refine .head (.next (ra_args_nil file labels _ _ _) (plain_apply _ _)) ?_
  refine .head (.next (ra_shift0 file labels hs2 hct) (plain_value _)) ?_
  refine .head (.next (ra_effectBind file labels (xs := [(t2, P)]) rfl _ _) (plain_effectExpr _ _)) ?_
  refine rp3.trans ?_
  refine .head (.next (ra_ctor file labels _ _ _ _ _) (plain_pureExpr _ _)) ?_
  refine .head (.next (ra_sym file labels _ _ (PrintfStd.lk_same k2 _ _)) (plain_value _)) ?_
  refine .head (.next (ra_args_nil file labels _ _ _) (plain_apply _ _)) ?_
  refine .head (.next (ra_specified file labels _) (plain_value _)) ?_
  exact .single (.next (ra_diagnostic file labels _ _) (plain_value _))

/-- **The unsequenced callee and format** reach the tuple of their values, callee first. -/
theorem printf_unseq {t0 t1 : EExp} {w0 : WVal} (h0 : ExitCall.calleeTask file t0 = some w0) {lit : Sym}
    (h1 : fmtTask t1 = some lit) {env : Env} {sid saddr : Int}
    (hl : env.lookup lit = some (.object (.pointer (.allocated sid saddr)))) {cs : List Int}
    (a : List Annot) (k : List Frame) (m : Mem.Concrete.State) (hs : StrObj m sid saddr cs) :
    ∃ l, ReturnConst.Reaches file labels ⟨.effectExpr (.mk a (.unseq [t0, t1])) env, k, m⟩
      ⟨.value (.tuple [rv w0, .loaded (.specified (.pointer (.allocated sid saddr)))]), .annotations [] :: k,
        {m with currentLocation := l}⟩ := by
  obtain ⟨l1, r1⟩ := fmtTask_runs file labels h1 hl m hs
  obtain ⟨l0, r0⟩ := ExitCall.calleeTask_runs file labels h0 env {m with currentLocation := l1}
  have flag1 : Interleave.taskFlag false k ([] ++ [(0, .effectExpr t0 env, [])]) = false := by
    simp [Interleave.taskFlag, Interleave.controlHasCCall_effectExpr, ExitCall.calleeTask_noCall file h0]
  have flag0 : Interleave.taskFlag false k [] = false := by simp [Interleave.taskFlag]
  have run : Interleave.TasksRun file labels false k
      (([] ++ [(0, .effectExpr t0 env, [])]) ++ [(1, .effectExpr t1 env, [])])
      m (([] ++ [(0, rv w0, [])]) ++ [(1, .loaded (.specified (.pointer (.allocated sid saddr))), [])])
      {m with currentLocation := l0} :=
    .snoc (flag1 ▸ r1) (.snoc (flag0 ▸ r0) .nil)
  have hl' := Interleave.unseq_runs file labels (annots := a) (es := [t0, t1]) (env := env) run
    (by intro x hx b hb; simp at hx; rcases hx with rfl | rfl <;> simp at hb)
  exact ⟨l0, Interleave.reaches_of_local file labels (by simpa using hl')⟩

theorem ptrCompat_ok {ct ct' : Ctype} (h : ptrCompat ct ct' = true) (enums : Map Sym IntegerType) :
    Core.compatibleWith enums 256 Core.noQualifiers ct Core.noQualifiers ct' = .ok true := by
  unfold ptrCompat at h
  split at h
  · rename_i ann q ann2 a ann' q' ann2' b
    split at h
    · rename_i a' b' ha hb
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
      obtain ⟨⟨hq, hn⟩, n, hsome⟩ := h
      have hea : Core.normalizeInteger a enums = Core.normalizeInteger a := by
        cases a <;> simp_all [Fold.nonEnum, Core.normalizeInteger]
      have heb : Core.normalizeInteger b enums = Core.normalizeInteger b := by
        cases b <;> simp_all [Fold.nonEnum, Core.normalizeInteger]
      have ha' : a' = a := by cases a <;> simp_all [Fold.nonEnum]
      have hb' : b' = b := by cases b <;> simp_all [Fold.nonEnum]
      subst ha' hb' hq
      simp [Core.compatibleWith, Core.compatibleBasicWith, hea, heb, ← hn, hsome, pure, Except.pure]
    · cases h
  · cases h

/-- `not(are_compatible(T, t))` is false when `t` is a compatible pointer type. -/
theorem notCompat_eval {env : Env} {ct ct' : Ctype} {t : Sym} (hl : env.lookup t = some (.ctype ct'))
    (hc : ptrCompat ct ct' = true) (a a1 a2 a3 : List Annot) (u u1 u2 u3 : Unit) :
    SeqReach.PureEval file labels (.mk a u (.not (.mk a1 u1 (.areCompatible (.mk a2 u2 (.val (.ctype ct)))
      (.mk a3 u3 (.sym t)))))) env (Dynamics.boolean false) := by
  intro k m
  cases u; cases u1; cases u2; cases u3
  have hok := ptrCompat_ok hc m.enumTypes
  refine Relation.ReflTransGen.trans (b := ⟨.pureExpr (.mk a1 () (.areCompatible
      (.mk a2 () (.val (.ctype ct))) (.mk a3 () (.sym t)))) env, .arguments .notBool [] [] env :: k, m⟩)
    (SeqReach.next_reaches (by intro o; simp) (by simp [request, requestAux, awaitsScheduling, arguments])) ?_
  refine Relation.ReflTransGen.trans (b := ⟨.pureExpr (.mk a2 () (.val (.ctype ct))) env,
      .arguments .compatible [] [.mk a3 () (.sym t)] env :: .arguments .notBool [] [] env :: k, m⟩)
    (SeqReach.next_reaches (by intro o; simp) (by simp [request, requestAux, awaitsScheduling, arguments])) ?_
  refine (SeqReach.pure_value a2 _ env _ _).trans ?_
  refine (CallReach.arguments_reaches (.cons (SeqReach.pure_symbol a3 t env _ hl) .nil) .compatible [] _ _ _).trans ?_
  refine Relation.ReflTransGen.trans (b := ⟨.value .true, .arguments .notBool [] [] env :: k, m⟩)
    (SeqReach.next_reaches (by intro o; simp) (by
      simp [request, requestAux, awaitsScheduling, primitive, runtimeValue, hok, Dynamics.boolean, pure,
        Except.pure])) ?_
  refine Relation.ReflTransGen.trans (b := ⟨.apply .notBool [.true], k, m⟩)
    (SeqReach.next_reaches (by intro o; simp) (by simp [request, requestAux, awaitsScheduling])) ?_
  exact SeqReach.next_reaches (by intro o; simp) (by
    simp [request, requestAux, awaitsScheduling, primitive, Dynamics.boolean, pure, Except.pure])

/-- An effectful `if` whose condition folds to `false`, in a run-time environment the folder's
describes in part. -/
theorem if_false_sub {fenv : WEnv} {env : Env} (hr : EnvSub fenv env) {ann : List Annot}
    {c : PExp} {yes no : EE} (hc : ExitCall.foldsFalse file fenv c = true) (k : List Frame)
    (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.if_ c yes no)) env, k, m⟩
      ⟨.effectExpr no env, k, SeqReach.focusMemory ann m⟩ :=
  SeqReach.effect_if_reaches ann false
    (fun k m => Fold.eval_reaches_sub file labels _ fenv c _ (ExitCall.foldsFalse_eval hc) env hr k m) k m

theorem focus_same (ann : List Annot) (m : Mem.Concrete.State) :
    ReturnConst.focusMemory ann m = SeqReach.focusMemory ann m := rfl

theorem alignof_ptr (tags : Mem.Concrete.Tags) (ann : List Annot) (q : Qualifiers) (ref : Ctype) :
    primitive (.ctor .ivAlignof) [.ctype (.mk ann (.pointer q ref))] tags = .ok (.object (.integer 8)) := by
  simp [primitive, Mem.Concrete.alignment, Mem.Concrete.typeLayout, integer, bind, Except.bind, pure,
    Except.pure]

/-- **Creating the pointer argument object.** -/
theorem createPtr_reaches (ann a1 a2 a3 : List Annot) (l : Loc) (u u1 u2 u3 : Unit) (pref : Prefix)
    (tann : List Annot) (q : Qualifiers) (ref : Ctype) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr : Int} (hid : m.nextId = id) (haddr : ptrAddr m = addr) (hpos : 0 < addr) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.create (.mk a1 u1 (.ctor .ivAlignof
        [.mk a2 u2 (.val (.ctype (.mk tann (.pointer q ref))))])) (.mk a3 u3 (.val (.ctype (.mk tann (.pointer q ref)))))
        pref))))) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated id addr))), k,
        createdPtr pref (.mk tann (.pointer q ref)) (SeqReach.focusMemory ann m)⟩ := by
  subst hid haddr
  cases u1; cases u2; cases u3
  have hev : PureEval.Eval file (PureEval.tagsOf file m) env
      (.inr [.mk a1 () (.ctor .ivAlignof [.mk a2 () (.val (.ctype (.mk tann (.pointer q ref))))]),
        .mk a3 () (.val (.ctype (.mk tann (.pointer q ref))))])
      (.inr [.object (.integer 8), .ctype (.mk tann (.pointer q ref))]) :=
    .cons (.ctor (.cons .val .nil) (alignof_ptr _ tann q ref)) (.cons .val .nil)
  refine (Locals.action_reaches Locals.request_create hev).trans ?_
  have hpos' : 0 < ptrAddr (SeqReach.focusMemory ann m) := by
    unfold ptrAddr; simp only [PrintfStd.focus_lastAddress]; exact hpos
  have ha := allocate_ptr ⟨file.tagDefs, (SeqReach.focusMemory ann m).enumTypes⟩
    (SeqReach.focusMemory ann m) tann q ref hpos'
  have hid : (SeqReach.focusMemory ann m).nextId = m.nextId := PrintfStd.focus_nextId ann m
  have hpa : ptrAddr (SeqReach.focusMemory ann m) = ptrAddr m := by
    unfold ptrAddr; simp only [PrintfStd.focus_lastAddress]
  rw [focus_same, ← hid, ← hpa]
  exact Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest, ha, createdPtr, bind, Except.bind,
      pure, Except.pure])

/-- The access annotation of an 8-byte store at `addr` under `k`. -/
def storeAnn (k : List Frame) (addr : Int) : List Access :=
  [⟨k.findSome? (fun f => match f with | .excluded n => some n | _ => none), [], true, addr, 8⟩]

/-- The memory after storing the pointer `allocated pid paddr` into the object at `addr`. -/
def storedPtr (m : Mem.Concrete.State) (id addr pid paddr : Int) : Mem.Concrete.State :=
  {Mem.Concrete.writeRepresentation addr (ptrBytes pid paddr) m with lastUsed := some id}

/-- **Storing the format pointer** into the argument object. -/
theorem storePtr_reaches (ann a1 a2 a3 : List Annot) (l : Loc) (u u1 u2 u3 : Unit) (tann : List Annot)
    (q : Qualifiers) (ref : Ctype) {x a : Sym} {env : Env} {id addr pid paddr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (ha : env.lookup a = some (.loaded (.specified (.pointer (.allocated pid paddr)))))
    {m : Mem.Concrete.State} (hslot : PtrSlot m id addr) (range : 0 < paddr ∧ paddr < 18446744073709551616)
    (k : List Frame) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false (.mk a1 u1 (.val (.ctype (.mk tann (.pointer q ref)))))
        (.mk a2 u2 (.sym x)) (.mk a3 u3 (.sym a)) .na))))) env, k, m⟩
      ⟨.value .unit, .annotations (storeAnn k addr) :: k,
        storedPtr (SeqReach.focusMemory ann m) id addr pid paddr⟩ := by
  cases u1; cases u2; cases u3
  have hev : PureEval.Eval file (PureEval.tagsOf file m) env
      (.inr [.mk a1 () (.val (.ctype (.mk tann (.pointer q ref)))), .mk a2 () (.sym x), .mk a3 () (.sym a)])
      (.inr [.ctype (.mk tann (.pointer q ref)), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.pointer (.allocated pid paddr)))]) :=
    .cons .val (.cons (.sym hx) (.cons (.sym ha) .nil))
  refine (Locals.action_reaches Locals.request_store hev).trans ?_
  rw [focus_same]
  have hs' : PtrSlot (SeqReach.focusMemory ann m) id addr := hslot.keeps (PrintfStd.keeps_focus ann m)
  let tags : Mem.Concrete.Tags := ⟨file.tagDefs, (SeqReach.focusMemory ann m).enumTypes⟩
  obtain ⟨hst, -⟩ := store_ptr tags tann q ref hs' range
  have hacc := access_ptr tags tann q ref hs'
  obtain ⟨r, hr⟩ : ∃ r, request file labels
      ⟨.apply (.memory .store) [.ctype (.mk tann (.pointer q ref)), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.pointer (.allocated pid paddr)))], k, SeqReach.focusMemory ann m⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory,
    Mem.Concrete.unatomic, bind, Except.bind, pure, Except.pure] at hr'
  erw [hst, hacc] at hr'
  simp only at hr'
  exact Actions.memory_reaches (by intro o h; cases h) (hr.trans hr'.symm)

/-- A value over an annotation frame binds weakly as below it. -/
theorem v_effectBind (xs : List Access) {v : Val} {pat : Pattern Sym} {b : EE} {env : Env}
    {ys : Bindings} (hm : matchPattern pat v = some ys) (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.value v, .annotations xs :: .effectBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv ys env), .annotations xs :: k, m⟩ :=
  lift file labels (ra_annotations file labels (by intro _ h; cases h)
    (by intro h; cases h) (fun _ => ra_effectBind file labels hm _ _)) (plain_effectExpr _ _)

theorem lookup_extend_other {xs : Bindings} {env : Env} {a : Sym} (h : ∀ y ∈ xs, y.1.key ≠ a.key) :
    (extendEnv xs env).lookup a = env.lookup a := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨s, v⟩ := y
    simp only [extendEnv, List.foldr] at ih ⊢
    rw [Map.lookup_insert_of_key_ne _ _ (Ne.symm (h (s, v) List.mem_cons_self))]
    exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem isCharPtr_inv {t : Ctype} (h : isCharPtr t = true) :
    ∃ tann q cann, t = .mk tann (.pointer q (charTy cann)) := by
  unfold isCharPtr at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · cases h

/-- **The pointer argument object** is created and holds the format pointer. -/
theorem ptrArg_reaches {fenv : WEnv} {env : Env} (hr : EnvSub fenv env) {a : Sym} {e : EExp}
    {ct : Ctype} (h : ptrArg file fenv a e = some ct) {sid saddr : Int}
    (ha : env.lookup a = some (.loaded (.specified (.pointer (.allocated sid saddr)))))
    (range : 0 < saddr ∧ saddr < 18446744073709551616) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < ptrAddr m) (hfresh : m.nextId ∉ m.dead) :
    ∃ xs m', ReturnConst.Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (ptrAddr m)))), .annotations xs :: k, m'⟩ ∧
      PtrObj m' m.nextId (ptrAddr m) sid saddr ∧ Keeps m m' ∧ m'.stdout = m.stdout ∧
      m'.nextId = m.nextId + 1 ∧ m'.lastAddress = ptrAddr m ∧ m'.dead = m.dead := by
  unfold ptrArg at h
  obtain ⟨⟨pt, nth, b⟩, q1, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨w, q2, h⟩ := PrintfStd.bind_some h
  obtain ⟨ys, q3, h⟩ := PrintfStd.bind_some h
  obtain ⟨⟨ct0, t, no⟩, q4, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨x, cr, r1⟩, q5, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨ct1, ct2⟩, q6, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨st, r2⟩, q7, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨ct3, x', a'⟩, q8, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨x'', q9, h⟩ := PrintfStd.bind_some h
  split at h
  case h_2 => cases h
  rename_i ct' hlt
  split at h
  case isFalse => cases h
  rename_i hc
  cases h
  obtain ⟨hcp, hcompat, rfl, rfl, rfl, k1, k2, k3, nxa, hys⟩ := hc
  obtain ⟨tann, q, cann, rfl⟩ := isCharPtr_inv hcp
  obtain ⟨A0, rfl⟩ := letOf_inv q1
  obtain ⟨B, ba, bu, ba1, bu1, ba2, bu2, ba3, bu3, yes, rfl⟩ := ifNotCompat_inv q4
  obtain ⟨A2, P2, b2, rfl⟩ := wseqOf_inv q5
  obtain ⟨A3, l3, u3, c1, cu1, c2, cu2, c3, cu3, pref, rfl⟩ := createOf_inv q6
  obtain ⟨A4, P4, b4, rfl⟩ := wseqNone_inv q7
  obtain ⟨A5, l5, u5, s1, su1, s2, su2, s3, su3, rfl⟩ := storeOf_inv q8
  obtain ⟨A6, a6, u6, rfl⟩ := pureSym_inv q9
  have hm : matchPattern pt (runtimeValue w) = some (Fold.bmap ys) := by rw [Fold.matchP_rv, q3]; rfl
  have hr1 : EnvSub (extend ys fenv) (extendEnv (Fold.bmap ys) env) := hr.extend ys
  have hys' : ∀ y ∈ Fold.bmap ys, y.1.key ≠ a.key := by
    intro y hy
    simp only [Fold.bmap, List.mem_map] at hy
    obtain ⟨⟨s, w'⟩, hs, rfl⟩ := hy
    exact hys _ hs
  have ha1 : (extendEnv (Fold.bmap ys) env).lookup a =
      some (.loaded (.specified (.pointer (.allocated sid saddr)))) := by
    rw [lookup_extend_other hys']; exact ha
  have chain := (SeqReach.effect_let_reaches (labels := labels) A0 (body := .mk B (.if_ _ yes _))
      (fun k m => Fold.eval_reaches_sub file labels _ fenv nth w q2 env hr k m) hm k m).trans
    ((SeqReach.effect_if_reaches B false (notCompat_eval file labels (hr1 t _ hlt) hcompat
      ba ba1 ba2 ba3 bu bu1 bu2 bu3) k _).trans
    ((SeqReach.wseq_reaches A2 (pat := .mk P2 (.base (some x, b2))) (createPtr_reaches file labels A3 c1 c2 c3 l3 u3 cu1 cu2 cu3 pref tann q
      (charTy cann) _ _ _ (id := m.nextId) (addr := ptrAddr m) (by simp) (by unfold ptrAddr; simp) hpos)
      (by rfl)).trans
    ((lift file labels (ra_wseq file labels A4 _ _ _) (plain_effectExpr _ _)).trans
    ((storePtr_reaches file labels A5 s1 s2 s3 l5 u5 su1 su2 su3 tann q (charTy cann)
      (PrintfStd.lk_same k1 _ _)
      (by rw [ReturnLit.lookup_key k3, PrintfStd.lk_other (Ne.symm nxa)]; exact ha1)
      (by
        have := createdPtr_slot pref (.mk tann (.pointer q (charTy cann)))
          (SeqReach.focusMemory A3 (SeqReach.focusMemory B (SeqReach.focusMemory A0 m))) (by simpa using hfresh)
        simpa [ptrAddr] using this) range _).trans
    ((v_effectBind file labels _ (pat := .mk P4 (.base (none, b4))) rfl _ _).trans
    (SeqReach.effect_pure_reaches A6 (SeqReach.pure_symbol a6 x'' _ _ (PrintfStd.lk_same k2 _ _)) _ _))))))
  let M3 := createdPtr pref (.mk tann (.pointer q (charTy cann)))
    (SeqReach.focusMemory A3 (SeqReach.focusMemory B (SeqReach.focusMemory A0 m)))
  have hslot : PtrSlot (SeqReach.focusMemory A5 M3) m.nextId (ptrAddr m) := by
    have := createdPtr_slot pref (.mk tann (.pointer q (charTy cann)))
      (SeqReach.focusMemory A3 (SeqReach.focusMemory B (SeqReach.focusMemory A0 m))) (by simpa using hfresh)
    exact (by simpa [ptrAddr] using this : PtrSlot M3 m.nextId (ptrAddr m)).keeps (PrintfStd.keeps_focus A5 M3)
  have hobj := (store_ptr ⟨file.tagDefs, (SeqReach.focusMemory A5 M3).enumTypes⟩ s1 q (charTy cann) hslot (pid := sid)
    range).2
  have k3m : Keeps m (SeqReach.focusMemory A5 M3) :=
    ((((PrintfStd.keeps_focus A0 m).trans (PrintfStd.keeps_focus B _)).trans (PrintfStd.keeps_focus A3 _)).trans
      (createdPtr_keeps _ _ _)).trans (PrintfStd.keeps_focus A5 M3)
  have hfacts := createdPtr_facts pref (.mk tann (.pointer q (charTy cann)))
    (SeqReach.focusMemory A3 (SeqReach.focusMemory B (SeqReach.focusMemory A0 m)))
  have hb := ptrAddr_bounds m
  refine ⟨_, _, chain, hobj.keeps (PrintfStd.keeps_focus A6 _),
    (store_ptr_keeps k3m (by omega) _ _ _).trans (PrintfStd.keeps_focus A6 _), ?_, ?_, ?_, ?_⟩
  · simp [storedPtr, StrMem.wr_stdout, hfacts.2.2.2.1]
  · simp [storedPtr, StrMem.wr_nextId, hfacts.2.1]
  · simp [storedPtr, StrMem.wr_lastAddress, hfacts.1, ptrAddr]
  · simp [storedPtr, (Mem.Concrete.writeRepresentation_allocations _ _ _).2.1, hfacts.2.2.1]

/-- **Killing the argument object.** -/
theorem killPtr_reaches (ann a1 : List Annot) (l : Loc) (u u1 : Unit) (tann : List Annot) (q : Qualifiers)
    (ref : Ctype) {x : Sym} {env : Env} {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) {m : Mem.Concrete.State}
    (hslot : PtrSlot m id addr) (k : List Frame) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.kill (.static (.mk tann (.pointer q ref)))
        (.mk a1 u1 (.sym x))))))) env, k, m⟩
      ⟨.value .unit, k, killed (SeqReach.focusMemory ann m) id⟩ := by
  cases u1
  have hev : PureEval.Eval file (PureEval.tagsOf file m) env (.inr [.mk a1 () (.sym x)])
      (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym hx) .nil
  refine (Locals.action_reaches Locals.request_kill hev).trans ?_
  rw [focus_same]
  have hs' : PtrSlot (SeqReach.focusMemory ann m) id addr := hslot.keeps (PrintfStd.keeps_focus ann m)
  have hk := kill_ptr ⟨file.tagDefs, (SeqReach.focusMemory ann m).enumTypes⟩ tann q ref hs'
  exact Actions.memory_reaches (name := "Kill") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest, hk, bind, Except.bind, pure, Except.pure])

/-- Continue a run that reaches an indirect call with the call's own run. -/
theorem bridgeP {S : State} {E : Env} {k : List Frame} {m : Mem.Concrete.State} {args : List Val}
    {v : Val} {Q : Mem.Concrete.State → Prop}
    (c : ReturnConst.Reaches file labels S ⟨.apply (.procedure E) args, k, m⟩)
    (h : ∃ m' zs, ReturnConst.Reaches file labels ⟨.apply (.procedure E) args, k, m⟩
      ⟨.value v, .annotations zs :: k, m'⟩ ∧ Q m') :
    ∃ m' zs, ReturnConst.Reaches file labels S ⟨.value v, .annotations zs :: k, m'⟩ ∧ Q m' :=
  let ⟨m', zs, r, q⟩ := h
  ⟨m', zs, c.trans r, q⟩

/-- **The call of `printf_proxy` and the kill of its argument object**: the literal is printed,
the call returns its length, and only the argument object dies. -/
theorem callPrintf_reaches {rest : EExp} {g q : Sym} (h : callPrintf rest = some (g, q)) {env : Env}
    {y : Sym} {s : Std} (hs : stdOf file y = some s)
    (hg : env.lookup g = some (.loaded (.specified (.pointer (.function y))))) {fid faddr sid saddr : Int}
    (hq : env.lookup q = some (.object (.pointer (.allocated fid faddr)))) {cs : List Int}
    (hcs : PlainFormat cs) {m : Mem.Concrete.State} (hp : PtrObj m fid faddr sid saddr)
    (hstr : StrObj m sid saddr cs) (k : List Frame) :
    ∃ m'' m' zs, ReturnConst.Reaches file labels ⟨.effectExpr rest env, k, m⟩
      ⟨.value (.loaded (.specified (.integer (plainText cs).length))), .annotations zs :: k, m'⟩ ∧
      m''.stdout = m.stdout ++ plainText cs ∧ Keeps m m'' ∧ PrintfStd.SameAlloc m m'' ∧
      m'.stdout = m''.stdout ∧ m'.lastAddress = m''.lastAddress ∧ m'.nextId = m''.nextId ∧
      m'.dead = fid :: m''.dead ∧ (∀ m₀, Keeps m₀ m'' → m₀.nextId ≤ fid → Keeps m₀ m') := by
  unfold callPrintf at h
  obtain ⟨⟨ret, cl, r1⟩, q1, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨g', q'⟩, q2, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨kl, r2⟩, q3, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨⟨kt, q''⟩, q4, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨ret', q5, h⟩ := PrintfStd.bind_some h
  split at h
  case isFalse => cases h
  rename_i hc
  cases h
  obtain ⟨hkt, k1, k2, nrq⟩ := hc
  obtain ⟨tann, kq, cann, rfl⟩ := isCharPtr_inv hkt
  obtain ⟨B0, P0, b0, rfl⟩ := sseqOf_inv q1
  obtain ⟨C0, U, ty, a1, u1, a2, u2, a3, u3, bt, rfl⟩ := ccallNil_inv q2
  cases U; cases u1; cases u3
  have hp' := hp.keeps (PrintfStd.keeps_focus C0 m)
  have hstr' := hstr.keeps (PrintfStd.keeps_focus C0 m)
  have c1 := (lift file labels (ra_sseq file labels (k := k) (env := env) (m := m) B0
      (.mk P0 (.base (some ret, b0))) _ r1) (plain_effectExpr _ _)).trans
    ((CallReach.ccall_enter C0 ty (.mk a1 () (.sym g)) [.mk a2 u2 (.sym q), .mk a3 () (.ctor (.nil bt) [])]
      env (.strongBind (.mk P0 (.base (some ret, b0))) r1 env :: k) m).trans
    ((SeqReach.pure_symbol a1 g env _ hg _ _).trans
    (CallReach.arguments_reaches (.cons (SeqReach.pure_symbol a2 q env _ hq)
      (.cons (PrintfStd.pe_of_eval fun tags => .ctor (c := .nil bt) .nil rfl) .nil)) (.procedure env) [] _ _ _)))
  obtain ⟨m'', zs, r2, o2, kp2, s2⟩ := bridgeP file labels c1 (PrintfStd.proxy_reaches hs hcs hp' hstr' env _ bt)
  obtain ⟨B1, P1, b1, rfl⟩ := sseqNone_inv q3
  obtain ⟨K0, l4, u4, a4, u4', rfl⟩ := killOf_inv q4
  obtain ⟨B2, a5, u5, rfl⟩ := pureSym_inv q5
  have kc := (PrintfStd.keeps_focus C0 m).trans kp2
  have hslot : PtrSlot m'' fid faddr := hp.slot.keeps kc
  have r3 := r2.trans ((PrintfStd.v_strongBind zs rfl _ _).trans
    ((lift file labels (ra_sseq file labels B1 _ _ _) (plain_effectExpr _ _)).trans
    ((killPtr_reaches file labels K0 a4 l4 u4 u4' tann kq (charTy cann)
      (by rw [ReturnLit.lookup_key k1, PrintfStd.lk_other (Ne.symm nrq)]; exact hq) hslot _).trans
    ((SeqReach.strong_bind_reaches (by rfl) _ _).trans
    (SeqReach.effect_pure_reaches B2 (SeqReach.pure_symbol a5 ret' _ _ (by exact PrintfStd.lk_same k2 _ _))
      _ _)))))
  obtain ⟨sl, sn, sd⟩ := s2
  refine ⟨m'', _, _, r3, by simpa using o2, kc, ⟨by simpa using sl, by simpa using sn, by simpa using sd⟩,
    by simp [killed], by simp [killed], by simp [killed], by simp [killed], ?_⟩
  intro m₀ h₀ hj
  exact (((h₀.trans (PrintfStd.keeps_focus K0 m'')).killed (by simpa using hj))).trans
    (PrintfStd.keeps_focus B2 _)

end Steps

/-! ## The run -/

/-- Dead allocations are all below the next identifier. -/
def DeadBelow (m : Mem.Concrete.State) : Prop := ∀ j ∈ m.dead, j < m.nextId

theorem litOf_mem {ls : List (Sym × List Int)} {lit : Sym} {cs : List Int} (h : litOf ls lit = some cs) :
    ∃ x, (x, cs) ∈ ls ∧ x.key = lit.key := by
  unfold litOf at h
  obtain ⟨⟨x, cs'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  simp only [beq_iff_eq] at hp
  exact ⟨x, hm, hp⟩

theorem extendEnv_append (l1 l2 : Bindings) (env : Env) :
    extendEnv (l1 ++ l2) env = extendEnv l1 (extendEnv l2 env) := List.foldr_append

theorem v_bound {file : Program} {labels : Labels} (xs : List Access) (v : Val) (k : List Frame)
    (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.value v, .annotations xs :: .bound :: k, m⟩ ⟨.value v, k, m⟩ :=
  SeqReach.next_reaches (by intro o; simp) (by simp [request, requestAux, awaitsScheduling])

/-- **The statement `printf(s)` runs**: it prints `s` and returns its length, keeping every
earlier object, killing only its own argument object, using at most 16 bytes below the last
allocation. -/
theorem printfLit_reaches {file : Program} {labels : Labels} {ls : List (Sym × List Int)}
    {fenv : WEnv} {e : EExp} {cs : List Int} (h : printfLit file ls fenv e = some cs)
    {env : Env} (hr : EnvSub fenv env) {m : Mem.Concrete.State} (hlit : LitEnv ls env m)
    (hdead : DeadBelow m) (hroom : 64 ≤ m.lastAddress) (ann : List Annot) (k : List Frame) :
    ∃ m', ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer (plainText cs).length))), k, m'⟩ ∧
      m'.stdout = m.stdout ++ plainText cs ∧ Keeps m m' ∧ DeadBelow m' ∧
      m.lastAddress - 16 ≤ m'.lastAddress := by
  unfold printfLit at h
  obtain ⟨⟨pf, a, t0, t1, c1, c2, p, argobj, rest⟩, q1, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  obtain ⟨w0, q2, h⟩ := PrintfStd.bind_some h
  obtain ⟨lit, q3, h⟩ := PrintfStd.bind_some h
  obtain ⟨cs', q4, h⟩ := PrintfStd.bind_some h
  obtain ⟨xs, q5, h⟩ := PrintfStd.bind_some h
  obtain ⟨ct, q6, h⟩ := PrintfStd.bind_some h
  obtain ⟨⟨g, q⟩, q7, h⟩ := PrintfStd.bind_some h; try dsimp only at h
  split at h
  case h_2 => cases h
  rename_i y hgl
  split at h
  case isFalse => cases h
  rename_i hc
  cases h
  obtain ⟨hcs, hxa, hfa, hc1, hc2, hqp, hgp, hsy⟩ := hc
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsy
  obtain ⟨a0, a1, pa, ba, a2, a3, u3, a4, u4, a5, pp, bp, rfl⟩ := stmtShape_inv q1
  obtain ⟨lx, hmem, hlk⟩ := litOf_mem q4
  obtain ⟨sid, saddr, hlx, hstr, hpos0, hlt0⟩ := hlit lx cs hmem
  have hl : env.lookup lit = some (.object (.pointer (.allocated sid saddr))) := by
    rw [← ReturnLit.lookup_key hlk]; exact hlx
  let V : Val := .loaded (.specified (.pointer (.allocated sid saddr)))
  let K1 : List Frame := .strongBind (.mk a1 (.ctor .tuple [pf, .mk pa (.base (some a, ba))]))
    (.mk a3 (.if_ c1 u3 (.mk a4 (.if_ c2 u4 (.mk a5 (.sseq (.mk pp (.base (some p, bp))) argobj rest)))))) env ::
    .bound :: k
  obtain ⟨l, ru⟩ := printf_unseq file labels q2 q3 hl a2 K1 m hstr
  have hm : matchPattern (.mk a1 (.ctor .tuple [pf, .mk pa (.base (some a, ba))])) (.tuple [runtimeValue w0, V]) =
      some (Fold.bmap xs ++ [(a, V)]) := by
    simp [matchPattern, matchPatterns, Fold.matchP_rv, q5, bind, Option.bind]
  let E1 : Env := extendEnv (Fold.bmap xs ++ [(a, V)]) env
  have hr1 : EnvSub (extend xs fenv) E1 := by
    rw [show E1 = extendEnv (Fold.bmap xs) (env.insert a V) from extendEnv_append _ _ _]
    exact (hr.insert_right hfa V).extend xs
  have hxa' : ∀ y ∈ Fold.bmap xs, y.1.key ≠ a.key := by
    intro y hy
    simp only [Fold.bmap, List.mem_map] at hy
    obtain ⟨⟨s', w'⟩, hs', rfl⟩ := hy
    exact hxa _ hs'
  have haE : E1.lookup a = some V := by
    rw [show E1 = extendEnv (Fold.bmap xs) (env.insert a V) from extendEnv_append _ _ _,
      lookup_extend_other hxa']
    exact Map.lookup_insert _ _ _
  let M : Mem.Concrete.State :=
    SeqReach.focusMemory a4 (SeqReach.focusMemory a3 {m with currentLocation := l})
  have kM : Keeps m M := (((Keeps.refl m).location l).trans (PrintfStd.keeps_focus a3 _)).trans
    (PrintfStd.keeps_focus a4 _)
  have hMl : M.lastAddress = m.lastAddress := by simp [M]
  have hMn : M.nextId = m.nextId := by simp [M]
  have hMd : M.dead = m.dead := by simp [M]
  have hb := ptrAddr_bounds M
  obtain ⟨xs2, M2, r8, hobj, k8, o8, n8, l8, d8⟩ := ptrArg_reaches file labels hr1 q6 haE
    ⟨hpos0, by omega⟩ (.strongBind (.mk pp (.base (some p, bp))) rest E1 :: .annotations [] :: .bound :: k) M
    (by omega) (by rw [hMn, hMd]; intro hmem'; exact absurd (hdead _ hmem') (lt_irrefl _))
  let PV : Val := .object (.pointer (.allocated M.nextId (ptrAddr M)))
  let E2 : Env := extendEnv [(p, PV)] E1
  have hg2 : E2.lookup g = some (.loaded (.specified (.pointer (.function y)))) := by
    rw [PrintfStd.lk_other hgp]; exact hr1 g _ hgl
  have hq2 : E2.lookup q = some PV := PrintfStd.lk_same hqp _ _
  have hstr2 : StrObj M2 sid saddr cs := hstr.keeps (kM.trans k8)
  obtain ⟨m'', m', zs, r10, o10, k10, s10, o10', l10, n10, d10, kk10⟩ :=
    callPrintf_reaches file labels q7 hs hg2 hq2 hcs hobj hstr2
      (.annotations xs2 :: .annotations [] :: .bound :: k)
  have chain := (ExitCall.lift file labels (ExitCall.ra_bound file labels ann _) (ExitCall.plain_effectExpr _ _)).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels a0 _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (ru.trans
    ((ExitCall.lift file labels (ExitCall.ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
      (fun _ => ExitCall.ra_strongBind file labels hm _ _)) (ExitCall.plain_effectExpr _ _)).trans
    ((if_false_sub file labels hr1 hc1 _ _).trans
    ((if_false_sub file labels hr1 hc2 _ _).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels a5 _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (r8.trans
    ((PrintfStd.v_strongBind xs2 rfl _ _).trans
    (r10.trans
    ((PrintfStd.v_merge _ _ _ _ _).trans
    ((PrintfStd.v_merge _ _ _ _ _).trans
    (v_bound _ _ k _))))))))))))
  obtain ⟨sl, sn, sd⟩ := s10
  refine ⟨m', chain, by rw [o10', o10, o8]; simp [M], kk10 m (kM.trans (k8.trans k10)) (by rw [hMn]), ?_, ?_⟩
  · intro j hj
    rw [d10, sd, d8, hMd] at hj
    rw [n10, sn, n8, hMn]
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [hMn]; omega
    · have := hdead j hj; omega
  · rw [l10, sl, l8]; omega

end Silmaril.Compile.Core.Verified.PrintfStmt
