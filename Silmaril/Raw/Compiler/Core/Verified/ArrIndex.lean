module

public import Silmaril.Compiler.Core.Verified.ArrRead.Defs
/-! # Runtime indices into integer arrays

Unlike `ArrDesig`, `shiftOf` retains the index expression as syntax. `shift_runs`
evaluates it as a read-only task and proves the resulting address computation
when that runtime index is in bounds. Bounds must be supplied by the caller's
invariant; no source computation is executed at compile time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrIndex

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ReturnLit (Eff)
open LoadTask (Touched ReadTask)
open ArgvChar (checkOf pureArms wseq_enter value_effectBind plain_effectExpr plain_pureExpr plain_value plain_apply)
open PtrDeref (Runs isInt isInt_inv)

variable {file : Program} {labels : Labels}

def shiftOf : Eff → Option (Eff × Ctype × Eff)
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some c, _))]))
      (.mk _ (.unseq [X, Y]))
      (.mk _ (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym c')]))
        ((.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
            .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]),
          .mk _ (.wseq (.mk _ (.base (some z, _)))
            (.mk _ (.memop .ptrArrayShift [.mk _ () (.sym x'), .mk _ () (.val (.ctype ty)),
              .mk _ () (.sym y')]))
            (.mk _ (.pure (.mk _ () (.ctor .specified [.mk _ () (.sym z')])))))) :: rest)))) =>
      if a'.key = a.key ∧ c'.key = c.key ∧ x'.key = x.key ∧ y'.key = y.key ∧ z'.key = z.key ∧
          c.key ≠ a.key ∧ y.key ≠ x.key ∧ pureArms rest = true then some (X, ty, Y)
      else none
  | _ => none

theorem shiftOf_inv {e X Y : Eff} {ty : Ctype} (h : shiftOf e = some (X, ty, Y)) :
    ∃ (a0 pp p1 : List Annot) (a : Sym) (ta : BaseType) (p2 : List Annot) (c : Sym) (tc : BaseType)
      (au ac as as1 : List Annot) (a' : Sym) (as2 : List Annot) (c' : Sym)
      (q0 q1 q2 : List Annot) (x : Sym) (tx : BaseType) (q3 q4 : List Annot) (y : Sym) (ty' : BaseType)
      (w0 w1 : List Annot) (z : Sym) (tz : BaseType) (w2 w3 : List Annot) (x' : Sym) (w4 w5 : List Annot)
      (y' : Sym) (w6 w7 w8 : List Annot) (z' : Sym) (rest : List (Pattern Sym × EE)),
      e = .mk a0 (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some c, tc))]))
        (.mk au (.unseq [X, Y]))
        (.mk ac (.case_ (.mk as () (.ctor .tuple [.mk as1 () (.sym a'), .mk as2 () (.sym c')]))
          ((.mk q0 (.ctor .tuple [.mk q1 (.ctor .specified [.mk q2 (.base (some x, tx))]),
              .mk q3 (.ctor .specified [.mk q4 (.base (some y, ty'))])]),
            .mk w0 (.wseq (.mk w1 (.base (some z, tz)))
              (.mk w2 (.memop .ptrArrayShift [.mk w3 () (.sym x'), .mk w4 () (.val (.ctype ty)),
                .mk w5 () (.sym y')]))
              (.mk w6 (.pure (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))))) :: rest)))) ∧
      a'.key = a.key ∧ c'.key = c.key ∧ x'.key = x.key ∧ y'.key = y.key ∧ z'.key = z.key ∧
      c.key ≠ a.key ∧ y.key ≠ x.key ∧ pureArms rest = true := by
  unfold shiftOf at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

theorem shiftOf_noCall {e X Y : Eff} {ty : Ctype} (h : shiftOf e = some (X, ty, Y))
    (hX : hasCCall X = false) (hY : hasCCall Y = false) : hasCCall e = false := by
  obtain ⟨a0, pp, p1, a, ta, p2, c, tc, au, ac, as, as1, a', as2, c', q0, q1, q2, x, tx, q3, q4,
    y, ty', w0, w1, z, tz, w2, w3, x', w4, w5, y', w6, w7, w8, z', rest, rfl, _, _, _, _, _, _, _, hp⟩ :=
    shiftOf_inv h
  simp [hasCCall, hX, hY]
  exact fun a b hab => ArgvChar.pureArms_calls hp a b hab

theorem shift_runs {e X Y : Eff} {ty : Ctype} {n : Int} (h : shiftOf e = some (X, ty, Y)) (hty : isInt ty = true)
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int}
    (hX : Runs (file := file) (labels := labels) I env X (.loaded (.specified (.pointer (.allocated id addr)))))
    (hY : ReadTask (file := file) (labels := labels) I env Y (IntExpr.spec n))
    (ne : X ≠ Y)
    (inb : ∀ m, I m → ∃ al, m.allocations.lookup id = some al ∧ al.base ≤ addr + 4 * n ∧
      addr + 4 * n ≤ al.base + al.size) :
    Runs (file := file) (labels := labels) I env e
      (.loaded (.specified (.pointer (.allocated id (addr + 4 * n))))) := by
  refine ⟨shiftOf_noCall h hX.1 hY.1, fun k m hm => ?_⟩
  obtain ⟨tann, rfl⟩ := isInt_inv hty
  obtain ⟨a0, pp, p1, a, ta, p2, c, tc, au, ac, as, as1, a', as2, c', q0, q1, q2, x, tx, q3, q4,
    y, ty', w0, w1, z, tz, w2, w3, x', w4, w5, y', w6, w7, w8, z', rest, rfl, ha, hc, hx, hy, hz, hca,
    hyx, -⟩ := shiftOf_inv h
  let ptr : Mem.Concrete.Pointer := .allocated id addr
  let ptr' : Mem.Concrete.Pointer := .allocated id (addr + 4 * n)
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
  have s₀ := wseq_enter (file := file) (labels := labels) a0 TP (.mk au (.unseq [X, Y])) CASE env k m
  obtain ⟨xs, m₁, rd, g₁, s₁⟩ := IntExpr.unseq_pair (file := file) (labels := labels)
    (k := .effectBind TP CASE env :: k) (annots := au) I hI hX.task
    hY
    (fun eq => absurd eq ne) m hm
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



def elemOf (e : Eff) : Option (Sym × Eff) :=
  match checkOf e with
  | some (S, ty) =>
    if isInt ty then
      match shiftOf S with
      | some (X, ty', Y) => if isInt ty' then (ArrDesig.decayOf X).map (·, Y) else none
      | none => none
    else none
  | none => none

theorem elemOf_inv {e Y : Eff} {r : Sym} (h : elemOf e = some (r, Y)) :
    ∃ S ty X ty', checkOf e = some (S, ty) ∧ isInt ty = true ∧ shiftOf S = some (X, ty', Y) ∧
      isInt ty' = true ∧ ArrDesig.decayOf X = some r := by
  unfold elemOf at h
  split at h
  · rename_i S ty hc
    split at h
    · rename_i hi
      split at h
      · rename_i X ty' Y' hs
        split at h
        · rename_i hi'
          cases hd : ArrDesig.decayOf X with
          | none => simp [hd] at h
          | some r' =>
            simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨S, ty, X, ty', hc, hi, hs, hi', hd⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- The index task is executed at runtime; bounds belong to the current loop state. -/
theorem elem_runs {e Y : Eff} {r : Sym} {n : Int} (h : elemOf e = some (r, Y))
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int} {N : Nat}
    (hr : env.lookup r = some (.object (.pointer (.allocated id addr))))
    (arr : ∀ m, I m → ArrDesig.Arr m id addr N)
    (index : ReadTask (file := file) (labels := labels) I env Y (IntExpr.spec n))
    (notDecay : ArrDesig.decayOf Y = none) (h0 : 0 ≤ n) (hn : n < N) (aligned : addr % 4 = 0) :
    Runs (file := file) (labels := labels) I env e
      (.object (.pointer (.allocated id (addr + 4 * n)))) := by
  obtain ⟨S, ty, X, ty', hc, ht, hs, ht', hd⟩ := elemOf_inv h
  refine PtrDeref.check_runs hc ht I hI ?_ (fun m hm => (arr m hm).alive) (by omega)
  refine shift_runs hs ht' I hI (ArrDesig.decay_runs hd I hr fun m hm => ?_) index ?_
    (fun m hm => ?_)
  · obtain ⟨_, al, look, base, size, _, _⟩ := arr m hm
    exact ⟨al, look, by omega, by omega⟩
  · intro eq
    rw [eq, notDecay] at hd
    cases hd
  · obtain ⟨_, al, look, base, size, _, _⟩ := arr m hm
    exact ⟨al, look, by omega, by omega⟩

end Silmaril.Compile.Core.Verified.ArrIndex
