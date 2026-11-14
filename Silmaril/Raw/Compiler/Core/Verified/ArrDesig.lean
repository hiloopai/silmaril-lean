module

public import Silmaril.Compiler.Core.Verified.PtrDeref.Defs
/-! # Elements of `int` arrays

Cerberus elaborates `a[i]` for an array object `int a[N]` to the designator
`CHECK(SHIFT(DECAY(a), int, i))`: `DECAY(a)` is the array-to-pointer conversion
`let weak s = pure(a) in let weak t = PtrArrayShift(s, int, 0) in pure(Specified(t))`
(`decayOf`), `SHIFT` the pointer addition by the index (`ArgvChar.shiftOf`, here with a literal
index) and `CHECK` `PtrValidForDeref` (`ArgvChar.checkOf`). `elemOf` recognises the designator
with a constant index and returns `(a, i)`.

- `decay_runs`: `DECAY(a)` runs to the pointer to the start of `a`'s object.
- `shiftN_runs`: `SHIFT(X, int, n)` runs to the pointer `4 * n` bytes further, when that address
  is within the allocation (Cerberus's bound, otherwise `UB046`): the generalisation of
  `PtrDeref.shift0_runs` to any index.
- `elem_runs`: `a[n]` for `0 ≤ n < N` runs to the pointer to element `n`, with read accesses only
  and the memory `Touched`.
- `readSub_runs`: the read `let weak p = d in load(int, p)` through any such designator of a
  defined `int` subobject (`IntSubobject.Slot`), the subobject version of `PtrDeref.read_runs`.

These are the source-side facts an array fragment of the statement machine needs: the index is
a constant proved in bounds, so no execution reaches `UB046` or an unsupported access.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrDesig

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ReturnLit (Eff)
open LoadTask (Touched ReadTask)
open Cond (OneAnn)
open ArgvChar (shiftOf shiftOf_inv checkOf checkOf_inv wseq_enter value_effectBind
  plain_effectExpr plain_pureExpr plain_value plain_apply)
open PtrDeref (Runs isInt isInt_inv shiftOf_noCall check_runs)

/-- `DECAY(r)`: `let weak s = pure(r) in let weak t = PtrArrayShift(s, int, 0) in
pure(Specified(t))`. -/
def decayOf : Eff → Option Sym
  | .mk _ (.wseq (.mk _ (.base (some s, _))) (.mk _ (.pure (.mk _ () (.sym r))))
      (.mk _ (.wseq (.mk _ (.base (some t, _)))
        (.mk _ (.memop .ptrArrayShift [.mk _ () (.sym s'), .mk _ () (.val (.ctype ty)),
          .mk _ () (.val (.object (.integer 0)))]))
        (.mk _ (.pure (.mk _ () (.ctor .specified [.mk _ () (.sym t')]))))))) =>
      if s'.key = s.key ∧ t'.key = t.key ∧ isInt ty = true then some r else none
  | _ => none

theorem decayOf_inv {e : Eff} {r : Sym} (h : decayOf e = some r) :
    ∃ (a0 p0 : List Annot) (s : Sym) (ts : BaseType) (a1 a2 a3 p1 : List Annot) (t : Sym)
      (tt : BaseType) (a4 a5 : List Annot) (s' : Sym) (a6 : List Annot) (ty : Ctype)
      (a7 a8 a9 a10 : List Annot) (t' : Sym),
      e = .mk a0 (.wseq (.mk p0 (.base (some s, ts))) (.mk a1 (.pure (.mk a2 () (.sym r))))
        (.mk a3 (.wseq (.mk p1 (.base (some t, tt)))
          (.mk a4 (.memop .ptrArrayShift [.mk a5 () (.sym s'), .mk a6 () (.val (.ctype ty)),
            .mk a7 () (.val (.object (.integer 0)))]))
          (.mk a8 (.pure (.mk a9 () (.ctor .specified [.mk a10 () (.sym t')]))))))) ∧
      s'.key = s.key ∧ t'.key = t.key ∧ isInt ty = true := by
  unfold decayOf at h
  split at h
  · split at h
    · rename_i hc; cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

/-- The designator `r[n]` of an `int` array object `r` with a literal index `n`. -/
def elemOf (e : Eff) : Option (Sym × Int) :=
  match checkOf e with
  | some (S, ty) =>
    if isInt ty then
      match shiftOf S with
      | some (X, ty', n) => if isInt ty' then (decayOf X).map (·, n) else none
      | none => none
    else none
  | none => none

theorem elemOf_inv {e : Eff} {r : Sym} {n : Int} (h : elemOf e = some (r, n)) :
    ∃ S ty X ty', checkOf e = some (S, ty) ∧ isInt ty = true ∧ shiftOf S = some (X, ty', n) ∧
      isInt ty' = true ∧ decayOf X = some r := by
  unfold elemOf at h
  split at h
  · rename_i S ty hc
    split at h
    · rename_i hi
      split at h
      · rename_i X ty' n' hs
        split at h
        · rename_i hi'
          cases hd : decayOf X with
          | none => simp [hd] at h
          | some r' =>
            simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨S, ty, X, ty', hc, hi, hs, hi', hd⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem decayOf_noCall {e : Eff} {r : Sym} (h : decayOf e = some r) : hasCCall e = false := by
  obtain ⟨a0, p0, s, ts, a1, a2, a3, p1, t, tt, a4, a5, s', a6, ty, a7, a8, a9, a10, t', rfl, -⟩ :=
    decayOf_inv h
  simp [hasCCall]

theorem elemOf_noCall {e : Eff} {r : Sym} {n : Int} (h : elemOf e = some (r, n)) :
    hasCCall e = false := by
  obtain ⟨S, ty, X, ty', hc, -, hs, -, hd⟩ := elemOf_inv h
  exact ArgvChar.checkOf_calls hc (shiftOf_noCall hs (decayOf_noCall hd))

variable {file : Program} {labels : Labels}

/-- **`DECAY(r)`** of the array object `r` runs to the pointer to its start. -/
theorem decay_runs {e : Eff} {r : Sym} (h : decayOf e = some r) (I : Mem.Concrete.State → Prop)
    {env : Env} {id addr : Int}
    (hr : env.lookup r = some (.object (.pointer (.allocated id addr))))
    (inb : ∀ m, I m → ∃ al, m.allocations.lookup id = some al ∧ al.base ≤ addr ∧
      addr ≤ al.base + al.size) :
    Runs (file := file) (labels := labels) I env e
      (.loaded (.specified (.pointer (.allocated id addr)))) := by
  refine ⟨decayOf_noCall h, fun k m hm => ?_⟩
  obtain ⟨a0, p0, s, ts, a1, a2, a3, p1, t, tt, a4, a5, s', a6, ty, a7, a8, a9, a10, t', rfl, hs, ht,
    hty⟩ := decayOf_inv h
  obtain ⟨tann, rfl⟩ := isInt_inv hty
  let ptr : Mem.Concrete.Pointer := .allocated id addr
  let INT : Ctype := .mk tann (.basic (.integer (.signed .int)))
  let MEMOP : EE := .mk a4 (.memop .ptrArrayShift [.mk a5 () (.sym s'), .mk a6 () (.val (.ctype INT)),
    .mk a7 () (.val (.object (.integer 0)))])
  let PURE : EE := .mk a8 (.pure (.mk a9 () (.ctor .specified [.mk a10 () (.sym t')])))
  let REST : EE := .mk a3 (.wseq (.mk p1 (.base (some t, tt))) MEMOP PURE)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk p0 (.base (some s, ts)))
    (.mk a1 (.pure (.mk a2 () (.sym r)))) REST env k m
  obtain ⟨l₁, s₁⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) a1 a2 r
    env hr (.effectBind (.mk p0 (.base (some s, ts))) REST env :: k) m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  let env₁ := extendEnv [(s, .object (.pointer ptr))] env
  have s₂ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
    (pat := .mk p0 (.base (some s, ts))) (v := .object (.pointer ptr)) rfl REST env k m₁
  let K' : List Frame := .effectBind (.mk p1 (.base (some t, tt))) PURE env₁ :: k
  have s₃ := wseq_enter (file := file) (labels := labels) a3 (.mk p1 (.base (some t, tt))) MEMOP PURE
    env₁ k m₁
  obtain ⟨l₂, s₄⟩ := ArgvChar.shift_enter (file := file) (labels := labels) (env := env₁) (k := K')
    (m := m₁) a4 (.mk a5 () (.sym s')) [.mk a6 () (.val (.ctype INT)), .mk a7 () (.val (.object (.integer 0)))]
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₂}
  have s₅ : LocalReaches file labels false
      ⟨.pureExpr (.mk a5 () (.sym s')) env₁, .arguments (.memop .ptrArrayShift) []
        [.mk a6 () (.val (.ctype INT)), .mk a7 () (.val (.object (.integer 0)))] env₁ :: K', m₂⟩
      ⟨.apply (.memop .ptrArrayShift) [.object (.pointer ptr), .ctype INT, .object (.integer 0)], K', m₂⟩ :=
    .head (.next (LoadTask.requestAux_sym m₂ a5 s' env₁ (ConvInt.lookup_one hs) _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₂ _ [] _ _ _ env₁ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_val m₂ a6 _ env₁ _ false) (plain_value _))
          (.head (.next (LoadTask.requestAux_argument m₂ _ _ _ _ [] env₁ _ false) (plain_pureExpr _ _))
            (.head (.next (LoadTask.requestAux_val m₂ a7 _ env₁ _ false) (plain_value _))
              (.single (.next (LoadTask.requestAux_last_argument m₂ _ _ _ env₁ _ false)
                (plain_apply _ _)))))))
  have hshift : Mem.Concrete.shiftPointer (PureEval.tagsOf file m₂) m₂ ptr INT 0 = .ok ptr := by
    obtain ⟨al0, look, lo, hi⟩ := inb m hm
    rw [show INT = Mem.Concrete.intType tann from rfl]
    simp [Mem.Concrete.shiftPointer, ptr, m₂, m₁, look, lo, hi, Mem.Concrete.layout_intType, bind,
      Except.bind, pure, Except.pure]
  let env₂ := extendEnv [(t, .object (.pointer ptr))] env₁
  have s₆ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
    (pat := .mk p1 (.base (some t, tt))) (v := .object (.pointer ptr)) rfl PURE env₁ k m₂
  obtain ⟨l₃, s₇⟩ := ExitCall.pure_local file labels (wc := false) (env := env₂) (k := k) (m := m₂) a8
    (.mk a9 () (.ctor .specified [.mk a10 () (.sym t')]))
  let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₃}
  have heval : PureEval.Eval file (PureEval.tagsOf file m₃) env₂
      (.inl (.mk a9 () (.ctor .specified [.mk a10 () (.sym t')])))
      (.inl (.loaded (.specified (.pointer ptr)))) :=
    .ctor (.cons (.sym (ConvInt.lookup_one ht)) .nil) (by simp [primitive, pure, Except.pure])
  have s₈ := PureLocal.eval_local file (PureEval.tagsOf file m₃) (wc := false) (labels := labels) heval
    (.diagnosticLocation m₂.currentLocation :: k) m₃ rfl
  refine ⟨[], m₃, [], .inl ⟨rfl, rfl⟩, by simp, ⟨l₃, m.lastUsed, by simp [m₃, m₂, m₁]⟩,
    s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans
      ((Relation.ReflTransGen.single (.next (ArgvChar.requestAux_shift_ok hshift K') (plain_value _))).trans
        (s₆.trans (s₇.trans (s₈.tail
          (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
            (plain_value _)))))))))))⟩

theorem shiftN_runs {e X : Eff} {ty : Ctype} {n : Int} (h : shiftOf e = some (X, ty, n)) (hty : isInt ty = true)
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int}
    (hX : Runs (file := file) (labels := labels) I env X (.loaded (.specified (.pointer (.allocated id addr)))))
    (inb : ∀ m, I m → ∃ al, m.allocations.lookup id = some al ∧ al.base ≤ addr + 4 * n ∧
      addr + 4 * n ≤ al.base + al.size) (hXne : ∀ an p, X ≠ .mk an (.pure p)) :
    Runs (file := file) (labels := labels) I env e
      (.loaded (.specified (.pointer (.allocated id (addr + 4 * n))))) := by
  refine ⟨shiftOf_noCall h hX.1, fun k m hm => ?_⟩
  obtain ⟨tann, rfl⟩ := isInt_inv hty
  obtain ⟨a0, pp, p1, a, ta, p2, c, tc, au, al, al', ac, as, as1, a', as2, c', q0, q1, q2, x, tx, q3, q4,
    y, ty', w0, w1, z, tz, w2, w3, x', w4, w5, y', w6, w7, w8, z', rest, rfl, ha, hc, hx, hy, hz, hca,
    hyx, -⟩ := shiftOf_inv h
  let ptr : Mem.Concrete.Pointer := .allocated id addr
  let ptr' : Mem.Concrete.Pointer := .allocated id (addr + 4 * n)
  let LIT : EE := .mk al (.pure (.mk al' () (.val (.loaded (.specified (.integer n))))))
  let TP : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some c, tc))])
  let INT : Ctype := .mk tann (.basic (.integer (.signed .int)))
  let MEMOP : EE := .mk w2 (.memop .ptrArrayShift [.mk w3 () (.sym x'), .mk w4 () (.val (.ctype INT)),
    .mk w5 () (.sym y')])
  let PURE : EE := .mk w6 (.pure (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))
  let ARM : EE := .mk w0 (.wseq (.mk w1 (.base (some z, tz))) MEMOP PURE)
  let SCRUT : PE := .mk as () (.ctor .tuple [.mk as1 () (.sym a'), .mk as2 () (.sym c')])
  let BS : List (Pattern Sym × EE) := (.mk q0 (.ctor .tuple [.mk q1 (.ctor .specified
    [.mk q2 (.base (some x, tx))]), .mk q3 (.ctor .specified [.mk q4 (.base (some y, ty'))])]), ARM) :: rest
  let CASE : EE := .mk ac (.case_ SCRUT BS)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 TP (.mk au (.unseq [X, LIT])) CASE env k m
  have hneq : X ≠ LIT := hXne al _
  obtain ⟨xs, m₁, rd, g₁, s₁⟩ := IntExpr.unseq_pair (file := file) (labels := labels)
    (k := .effectBind TP CASE env :: k) (annots := au) I hI hX.task
    (LoadTask.literal_readTask I env al al' (.loaded (.specified (.integer n))))
    (fun eq => absurd eq hneq) m hm
  let v₁ : Val := .loaded (.specified (.pointer ptr))
  let v₂ : Val := .loaded (.specified (.integer n))
  let env₁ := extendEnv [(a, v₁), (c, v₂)] env
  let K : List Frame := .annotations xs :: k
  have s₂ : LocalReaches file labels false
      ⟨.value (.tuple [v₁, runtimeValue (.loaded (.specified (.integer n)))]),
        .annotations xs :: .effectBind TP CASE env :: k, m₁⟩
      ⟨.effectExpr CASE env₁, K, m₁⟩ :=
    .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a c ta tc v₁ v₂ CASE env k)
      (plain_effectExpr _ _))
  obtain ⟨l, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ ac SCRUT BS env₁ K false
  obtain ⟨l₁, s₃⟩ := LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
  have heval : PureEval.Eval file (PureEval.tagsOf file m₂) env₁ (.inl SCRUT) (.inl (.tuple [v₁, v₂])) :=
    .ctor (.cons (.sym (ArgvChar.lookup2_first ha)) (.cons (.sym (ArgvChar.lookup2_second hc hca)) .nil))
      (by simp [primitive, pure, Except.pure])
  have s₄ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels) heval
    (.effectCase BS env₁ :: K) m₂ rfl
  let env₂ := extendEnv [(x, .object (.pointer ptr)), (y, .object (.integer n))] env₁
  have s₅ : LocalReaches file labels false ⟨.value (.tuple [v₁, v₂]), .effectCase BS env₁ :: K, m₂⟩
      ⟨.effectExpr ARM env₂, K, m₂⟩ :=
    .single (.next (Cond.requestAux_effectCase m₂ _ BS env₁ K false
      (by simp [BS, selectCase, matchPattern, matchPatterns, v₁, v₂, pure])) (plain_effectExpr _ _))
  let K' : List Frame := .effectBind (.mk w1 (.base (some z, tz))) PURE env₂ :: K
  have s₆ := wseq_enter (file := file) (labels := labels) w0 (.mk w1 (.base (some z, tz))) MEMOP PURE env₂ K m₂
  obtain ⟨l₂, s₇⟩ := ArgvChar.shift_enter (file := file) (labels := labels) (env := env₂) (k := K') (m := m₂) w2
    (.mk w3 () (.sym x')) [.mk w4 () (.val (.ctype INT)), .mk w5 () (.sym y')]
  let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
  have s₈ : LocalReaches file labels false
      ⟨.pureExpr (.mk w3 () (.sym x')) env₂, .arguments (.memop .ptrArrayShift) []
        [.mk w4 () (.val (.ctype INT)), .mk w5 () (.sym y')] env₂ :: K', m₃⟩
      ⟨.apply (.memop .ptrArrayShift) [.object (.pointer ptr), .ctype INT, .object (.integer n)], K', m₃⟩ :=
    .head (.next (LoadTask.requestAux_sym m₃ w3 x' env₂ (ArgvChar.lookup2_first hx) _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ _ env₂ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_val m₃ w4 _ env₂ _ false) (plain_value _))
          (.head (.next (LoadTask.requestAux_argument m₃ _ _ _ _ [] env₂ _ false) (plain_pureExpr _ _))
            (.head (.next (LoadTask.requestAux_sym m₃ w5 y' env₂ (ArgvChar.lookup2_second hy hyx) _ false)
              (plain_value _))
              (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false)
                (plain_apply _ _)))))))
  have g₃ : Touched m m₃ := g₁.trans ⟨l₂, m₁.lastUsed, by simp [m₃, m₂]⟩
  have hshift : Mem.Concrete.shiftPointer (PureEval.tagsOf file m₃) m₃ ptr INT n = .ok ptr' := by
    obtain ⟨al0, look, lo, hi⟩ := inb m₃ (hI m m₃ hm g₃)
    rw [show INT = Mem.Concrete.intType tann from rfl]
    simp [Mem.Concrete.shiftPointer, ptr, ptr', look, lo, hi, Mem.Concrete.layout_intType, bind,
      Except.bind, pure, Except.pure]
  let env₃ := extendEnv [(z, .object (.pointer ptr'))] env₂
  have s₉ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
    (pat := .mk w1 (.base (some z, tz))) (v := .object (.pointer ptr')) rfl PURE env₂ K m₃
  obtain ⟨l₃, s₁₀⟩ := ExitCall.pure_local file labels (wc := false) (env := env₃) (k := K) (m := m₃) w6
    (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')]))
  let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l₃}
  have heval' : PureEval.Eval file (PureEval.tagsOf file m₄) env₃
      (.inl (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))
      (.inl (.loaded (.specified (.pointer ptr')))) :=
    .ctor (.cons (.sym (ConvInt.lookup_one hz)) .nil) (by simp [primitive, pure, Except.pure])
  have s₁₁ := PureLocal.eval_local file (PureEval.tagsOf file m₄) (wc := false) (labels := labels) heval'
    (.diagnosticLocation m₃.currentLocation :: K) m₄ rfl
  refine ⟨xs, m₄, [.annotations xs], .inr rfl, rd, g₃.trans ⟨l₃, m₃.lastUsed, rfl⟩,
    s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans (s₈.trans
      ((Relation.ReflTransGen.single (.next (ArgvChar.requestAux_shift_ok hshift K') (plain_value _))).trans
        (s₉.trans (s₁₀.trans (s₁₁.tail
          (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _))))))))))))))⟩


/-- **The element `r[n]`** of an `int` array object `r` (a live allocation at `addr` holding at
least `n + 1` ints) runs to the pointer to element `n`. -/
theorem elem_runs {e : Eff} {r : Sym} {n : Int} (h : elemOf e = some (r, n))
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int} (hr : env.lookup r = some (.object (.pointer (.allocated id addr))))
    (inb : ∀ m, I m → id ∉ m.dead ∧ ∃ al, m.allocations.lookup id = some al ∧ al.base = addr ∧
      0 ≤ n ∧ 4 * n + 4 ≤ al.size)
    (aligned : addr % 4 = 0) :
    Runs (file := file) (labels := labels) I env e (.object (.pointer (.allocated id (addr + 4 * n)))) := by
  obtain ⟨S, ty, X, ty', hc, hty, hs, hty', hd⟩ := elemOf_inv h
  refine check_runs hc hty I hI ?_ (fun m hm => (inb m hm).1) (by omega)
  refine shiftN_runs hs hty' I hI (decay_runs hd I hr fun m hm => ?_) (fun m hm => ?_) ?_
  · obtain ⟨-, al, look, base, h0, hs⟩ := inb m hm
    exact ⟨al, look, by omega, by omega⟩
  · obtain ⟨-, al, look, base, h0, hs⟩ := inb m hm
    exact ⟨al, look, by omega, by omega⟩
  · obtain ⟨a0, p0, s, ts, a1, a2, a3, p1, t, tt, a4, a5, s', a6, ty, a7, a8, a9, a10, t', rfl, -⟩ :=
      decayOf_inv hd
    intro an q eq
    cases eq

/-- **The read through a designator** that runs to the pointer of an `int` subobject (an array
element or a member, `IntSubobject.Slot`):
`let weak p = d in load(int, p')`. -/
theorem readSub_runs (a0 pa la a3 c1 a4 : List Annot) (pt : BaseType) (p p' : Sym) (d : Eff)
    (l : Loc) (u : Unit) (hp' : p'.key = p.key) (I : Mem.Concrete.State → Prop) {env : Env}
    {id addr n : Int} (hd : Runs (file := file) (labels := labels) I env d
      (.object (.pointer (.allocated id addr))))
    (hn : Mem.Concrete.IntRange n) (slot : ∀ m, I m → IntSubobject.Slot m id addr n)
    (k : List Frame) (m : Mem.Concrete.State) (hm : I m) :
    ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
      LocalReaches file labels false
        ⟨.effectExpr (.mk a0 (.wseq (.mk pa (.base (some p, pt))) d
          (.mk la (.action (.mk .pos (.mk l u (.load (Locals.intVal a3 c1) (.mk a4 () (.sym p'))
            .na))))))) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer n))), fr ++ k, m'⟩ := by
  let ptr : Val := .object (.pointer (.allocated id addr))
  let LOAD : EE := .mk la (.action (.mk .pos (.mk l u
    (.load (Locals.intVal a3 c1) (.mk a4 () (.sym p')) .na))))
  have s₁ := wseq_enter (file := file) (labels := labels) a0 (.mk pa (.base (some p, pt))) d LOAD env k m
  obtain ⟨xs, m₁, fr, hfr, rd, t₁, s₂⟩ := hd.2 (.effectBind (.mk pa (.base (some p, pt))) LOAD env :: k) m hm
  have s₃ := value_effectBind (file := file) (labels := labels) hfr (pat := .mk pa (.base (some p, pt)))
    (v := ptr) rfl LOAD env k m₁
  let env₁ := extendEnv [(p, ptr)] env
  have slot₁ : IntSubobject.Slot m₁ id addr n := (slot m hm).touched t₁
  obtain ⟨a, ha, s₄⟩ := SubobjectTask.load_local (file := file) (labels := labels) la l u
    (Locals.intVal a3 c1) (.mk a4 () (.sym p')) env₁ (fr ++ k) m₁ c1 slot₁ hn
    (.cons (Locals.eval_intVal _ env₁ a3 c1) (.cons (.sym (ConvInt.lookup_one hp')) .nil))
  obtain ⟨zs, fr', hfr', hzs, s₅⟩ := Cond.merge (file := file) (labels := labels) hfr (.inr rfl)
    (.loaded (.specified (.integer n))) k {ReturnConst.focusMemory la m₁ with lastUsed := some id}
  refine ⟨zs, _, fr', hfr', fun b hb => (hzs b hb).elim (fun hb' => ?_) (rd b), t₁.trans ?_,
    s₁.trans (s₂.trans (s₃.trans (s₄.trans s₅)))⟩
  · obtain rfl := List.mem_singleton.mp hb'; exact ha
  · exact (LoadTask.focusMemory_touched la m₁).trans
      ⟨(ReturnConst.focusMemory la m₁).currentLocation, some id, rfl⟩

/-! ## Array objects -/

/-- A live, writable, non-atomic allocation `id` of `N` ints at `addr`: the object of a local
`int a[N]`. -/
structure Arr (m : Mem.Concrete.State) (id addr : Int) (N : Nat) : Prop where
  alive : id ∉ m.dead
  found : ∃ al, m.allocations.lookup id = some al ∧ al.base = addr ∧ al.size = 4 * N ∧
    al.atomic = false ∧ al.readonly = none

theorem Arr.touched {m m' : Mem.Concrete.State} {id addr : Int} {N : Nat} (h : Arr m id addr N)
    (t : Touched m m') : Arr m' id addr N := by
  obtain ⟨l, u, rfl⟩ := t
  exact ⟨h.alive, h.found⟩

/-- Every element of an array object is an `int` subobject. -/
theorem Arr.live {m : Mem.Concrete.State} {id addr : Int} {N : Nat} (h : Arr m id addr N) {n : Int}
    (h0 : 0 ≤ n) (hn : n < N) : IntSubobject.Live m id (addr + 4 * n) := by
  obtain ⟨alive, al, look, base, size, hat, ro⟩ := h
  exact ⟨alive, al, look, by omega, by omega, hat, ro⟩

/-- **The element `r[n]`** of the array object `r` with `0 ≤ n < N`. -/
theorem elem_runs_arr {e : Eff} {r : Sym} {n : Int} (h : elemOf e = some (r, n))
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int} {N : Nat} (hr : env.lookup r = some (.object (.pointer (.allocated id addr))))
    (arr : ∀ m, I m → Arr m id addr N) (h0 : 0 ≤ n) (hn : n < N) (aligned : addr % 4 = 0) :
    Runs (file := file) (labels := labels) I env e (.object (.pointer (.allocated id (addr + 4 * n)))) := by
  refine elem_runs h I hI hr (fun m hm => ?_) aligned
  obtain ⟨alive, al, look, base, size, -, -⟩ := arr m hm
  exact ⟨alive, al, look, base, h0, by omega⟩

/-- **Reading `r[n]`**: `let weak p = r[n] in load(int, p')` runs to the element's value. -/
theorem readElem_runs (a0 pa la a3 c1 a4 : List Annot) (pt : BaseType) (p p' : Sym) {d : Eff}
    {r : Sym} {n : Int} (hd : elemOf d = some (r, n)) (l : Loc) (u : Unit) (hp' : p'.key = p.key)
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr v : Int} {N : Nat} (hr : env.lookup r = some (.object (.pointer (.allocated id addr))))
    (arr : ∀ m, I m → Arr m id addr N) (h0 : 0 ≤ n) (hn : n < N) (aligned : addr % 4 = 0)
    (hv : Mem.Concrete.IntRange v) (slot : ∀ m, I m → IntSubobject.Slot m id (addr + 4 * n) v)
    (k : List Frame) (m : Mem.Concrete.State) (hm : I m) :
    ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
      LocalReaches file labels false
        ⟨.effectExpr (.mk a0 (.wseq (.mk pa (.base (some p, pt))) d
          (.mk la (.action (.mk .pos (.mk l u (.load (Locals.intVal a3 c1) (.mk a4 () (.sym p'))
            .na))))))) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer v))), fr ++ k, m'⟩ :=
  readSub_runs a0 pa la a3 c1 a4 pt p p' d l u hp' I
    (elem_runs_arr hd I hI hr arr h0 hn aligned) hv slot k m hm

/-! ## Creating an array object

`int a[N];` elaborates to `create(alignof(int[N]), int[N])` followed by the store of the
unspecified aggregate (`AggregateUninit`). The object is allocated like any other: `4 * N` bytes
below the last allocation, aligned to `4` (`arrAddr`), with unspecified bytes (`createdArr`). -/

/-- `int[N]`. -/
abbrev intArr (ann annE : List Annot) (n : Int) : Ctype :=
  .mk ann (.array (Mem.Concrete.intType annE) (some n))

theorem layout_intArr (tags : Mem.Concrete.Tags) (ann annE : List Annot) (n : Nat) :
    Mem.Concrete.typeLayout 64 tags (intArr ann annE n) = .ok ⟨(n : Int) * 4, 4, []⟩ := by
  simp [Mem.Concrete.typeLayout, Mem.Concrete.intType, Mem.Concrete.registeredIntegerLayout,
    Mem.Concrete.registeredInteger, Mem.Concrete.integerLayout, Mem.Concrete.baseWidth]
  rfl

theorem alignof_intArr (tags : Mem.Concrete.Tags) (ann annE : List Annot) (n : Nat) :
    primitive (.ctor .ivAlignof) [.ctype (intArr ann annE n)] tags = .ok (.object (.integer 4)) := by
  simp [primitive, Mem.Concrete.alignment, layout_intArr, integer, bind, Except.bind, pure, Except.pure]

/-- The address of a fresh `int[N]` object. -/
def arrAddr (m : Mem.Concrete.State) (N : Nat) : Int :=
  (m.lastAddress - (N : Int) * 4) - (m.lastAddress - (N : Int) * 4) % 4

/-- The memory after allocating an `int[N]` object (`allocateTyped`). -/
def createdArr (ann annE : List Annot) (N : Nat) (m : Mem.Concrete.State) : Mem.Concrete.State :=
  { Mem.Concrete.writeRepresentation (arrAddr m N)
      (Mem.Concrete.plainBytes (List.replicate (N * 4) none)) m with
    nextId := m.nextId + 1
    lastAddress := arrAddr m N
    allocations := m.allocations.insert m.nextId
      ({base := arrAddr m N, size := (N : Int) * 4, objectType := some (intArr ann annE N)} :
        Mem.Concrete.Allocation)
    lastUsed := some m.nextId }

/-- A fresh `int[N]` object is allocated below every earlier one. -/
theorem allocate_arr (tags : Mem.Concrete.Tags) (m : Mem.Concrete.State) (ann annE : List Annot)
    (N : Nat) (hpos : 0 < arrAddr m N) :
    Mem.Concrete.allocateTyped tags m 4 (intArr ann annE N) =
      .ok (.allocated m.nextId (arrAddr m N), createdArr ann annE N m) := by
  unfold arrAddr at hpos
  have hn : ¬ (m.lastAddress - (N : Int) * 4 - (m.lastAddress - (N : Int) * 4) % 4 ≤ 0) := by omega
  simp only [Mem.Concrete.allocateTyped, layout_intArr, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right_of_eq_false _ _ (by simp), ite_eq_right_of_eq_false _ _ (by simpa using hn)]
  rw [show ((N : Int) * 4).toNat = N * 4 by omega]
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape
    (m.lastAddress - (N : Int) * 4 - (m.lastAddress - (N : Int) * 4) % 4)
    (Mem.Concrete.plainBytes (List.replicate (N * 4) none)) m
  simp only [createdArr, arrAddr, h]

/-- The fresh object is an array object of `N` ints. -/
theorem createdArr_arr (ann annE : List Annot) (N : Nat) (m : Mem.Concrete.State)
    (fresh : m.nextId ∉ m.dead) :
    Arr (createdArr ann annE N m) m.nextId (arrAddr m N) N := by
  refine ⟨?_, _, Map.lookup_insert _ _ _, rfl, by simp; omega, rfl, rfl⟩
  simpa [createdArr, (Mem.Concrete.writeRepresentation_allocations _ _ m).2.1] using fresh

end Silmaril.Compile.Core.Verified.ArrDesig
