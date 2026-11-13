module

public import Silmaril.Compiler.Core.Verified.ArgvChar.Defs
/-! # `argv[i][x]`: a character of an argument at the index an `int` local holds

`ArgvChar` reads `argv[i][j]` with literal indices. In a loop such as
`while (argv[1][n]) n++;` the second index is the `int` local `n`, which Cerberus elaborates to a
read `let weak p = pure(n) in load(int, p)` in place of the literal of `SHIFT` (`shiftYOf`: the
same shape with any second operand). `charVarOf argv e = some (i, x)` recognises
`argv[i][x]` with `i` a literal and `x` a local.

`charVar_ev`: from memories that hold the argument objects (`ArgvMem.Objs`) and the slot of `x`
holding `v` (an invariant `I` that reads keep), `argv[i][x]` for `i ≤ argc` and `0 ≤ v` at most
the length of `args[i]` is `Ev` of byte `v` of `args[i]` (its terminator at the length), and
of every value when `i = argc` (the null slot, where it always reaches undefined behaviour). The caller proves the bound
on `v`: past the terminator Cerberus's shift is still defined (one past the end) but the load is
an unsupported out-of-bounds access, not undefined behaviour.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvVar

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns TasksRun Plain unseqTasks
  taskFlag)
open ReturnLit (Eff)
open ArgvMem (Reads)
open ArgvChar

variable {file : Program} {labels : Labels}

/-! ## Shifts by an expression -/

/-- `SHIFT(X, ty, Y)`: the operand, the element type and the offset expression. -/
def shiftYOf : Eff → Option (Eff × Ctype × Eff)
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

theorem shiftYOf_inv {e X Y : Eff} {ty : Ctype} (h : shiftYOf e = some (X, ty, Y)) :
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
  unfold shiftYOf at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

theorem shiftYOf_calls {e X Y : Eff} {ty : Ctype} (h : shiftYOf e = some (X, ty, Y))
    (hX : hasCCall X = false) (hY : hasCCall Y = false) : hasCCall e = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, rfl, -, -, -, -, -, -, -, hrest⟩ := shiftYOf_inv h
  simp [hasCCall, hX, hY]
  exact fun a b hab => pureArms_calls hrest a b hab

/-- The run of `SHIFT(X, ty, Y)` up to the shift itself (`ArgvChar.shift_prefix` with the offset
computed by `Y`). -/
theorem shiftY_prefix {I : Mem.Concrete.State → Prop} (hI : Stable I) {e X Y : Eff} {ty : Ctype}
    (h : shiftYOf e = some (X, ty, Y)) {env : Env} {ptr : Mem.Concrete.Pointer} {n : Int}
    (hX : Ev (file := file) (labels := labels) I env X (.loaded (.specified (.pointer ptr))))
    (hY : Ev (file := file) (labels := labels) I env Y (.loaded (.specified (.integer n))))
    (k : List Frame) (m : Mem.Concrete.State) (hm : I m) :
    FailsUB (file := file) (labels := labels) env e k m ∨
    ∃ K m₃ xs, I m₃ ∧ Reads m m₃ ∧ (∀ a ∈ xs, a.write = false) ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.apply (.memop .ptrArrayShift) [.object (.pointer ptr), .ctype ty, .object (.integer n)],
          K, m₃⟩ ∧
      ∀ ptr', ∃ m₄, Reads m₃ m₄ ∧ LocalReaches file labels false ⟨.value (.object (.pointer ptr')), K, m₃⟩
        ⟨.value (.loaded (.specified (.pointer ptr'))), .annotations xs :: k, m₄⟩ := by
  obtain ⟨a0, pp, p1, a, ta, p2, c, tc, au, ac, as, as1, a', as2, c', q0, q1, q2, x, tx, q3, q4,
    y, ty', w0, w1, z, tz, w2, w3, x', w4, w5, y', w6, w7, w8, z', rest, rfl, ha, hc, hx, hy, hz, hca,
    hyx, -⟩ := shiftYOf_inv h
  let TP : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some c, tc))])
  let MEMOP : EE := .mk w2 (.memop .ptrArrayShift [.mk w3 () (.sym x'), .mk w4 () (.val (.ctype ty)),
    .mk w5 () (.sym y')])
  let PURE : EE := .mk w6 (.pure (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))
  let ARM : EE := .mk w0 (.wseq (.mk w1 (.base (some z, tz))) MEMOP PURE)
  let SCRUT : PE := .mk as () (.ctor .tuple [.mk as1 () (.sym a'), .mk as2 () (.sym c')])
  let BS : List (Pattern Sym × EE) := (.mk q0 (.ctor .tuple [.mk q1 (.ctor .specified
    [.mk q2 (.base (some x, tx))]), .mk q3 (.ctor .specified [.mk q4 (.base (some y, ty'))])]), ARM) :: rest
  let CASE : EE := .mk ac (.case_ SCRUT BS)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 TP (.mk au (.unseq [X, Y])) CASE env k m
  rcases ev_pair (file := file) (labels := labels) hI hX hY au
      (.effectBind TP CASE env :: k) m hm with ⟨xs, m₁, rd, g₁, s₁⟩ | f
  · let v₁ : Val := .loaded (.specified (.pointer ptr))
    let v₂ : Val := .loaded (.specified (.integer n))
    let env₁ := extendEnv [(a, v₁), (c, v₂)] env
    let K : List Frame := .annotations xs :: k
    have s₂ : LocalReaches file labels false
        ⟨.value (.tuple [v₁, v₂]), .annotations xs :: .effectBind TP CASE env :: k, m₁⟩
        ⟨.effectExpr CASE env₁, K, m₁⟩ :=
      .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a c ta tc v₁ v₂ CASE env k)
        (plain_effectExpr _ _))
    obtain ⟨l, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ ac SCRUT BS env₁ K false
    obtain ⟨l₁, s₃⟩ := LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
    have heval : PureEval.Eval file (PureEval.tagsOf file m₂) env₁ (.inl SCRUT) (.inl (.tuple [v₁, v₂])) :=
      .ctor (.cons (.sym (lookup2_first ha)) (.cons (.sym (lookup2_second hc hca)) .nil))
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
    obtain ⟨l₂, s₇⟩ := shift_enter (file := file) (labels := labels) (env := env₂) (k := K') (m := m₂) w2
      (.mk w3 () (.sym x')) [.mk w4 () (.val (.ctype ty)), .mk w5 () (.sym y')]
    let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
    have s₈ : LocalReaches file labels false
        ⟨.pureExpr (.mk w3 () (.sym x')) env₂, .arguments (.memop .ptrArrayShift) []
          [.mk w4 () (.val (.ctype ty)), .mk w5 () (.sym y')] env₂ :: K', m₃⟩
        ⟨.apply (.memop .ptrArrayShift) [.object (.pointer ptr), .ctype ty, .object (.integer n)], K', m₃⟩ :=
      .head (.next (LoadTask.requestAux_sym m₃ w3 x' env₂ (lookup2_first hx) _ false) (plain_value _))
        (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ _ env₂ _ false) (plain_pureExpr _ _))
          (.head (.next (LoadTask.requestAux_val m₃ w4 _ env₂ _ false) (plain_value _))
            (.head (.next (LoadTask.requestAux_argument m₃ _ _ _ _ [] env₂ _ false) (plain_pureExpr _ _))
              (.head (.next (LoadTask.requestAux_sym m₃ w5 y' env₂ (lookup2_second hy hyx) _ false)
                (plain_value _))
                (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false)
                  (plain_apply _ _)))))))
    have g₃ : Reads m m₃ := (g₁.location l₁).location l₂
    refine .inr ⟨K', m₃, xs, hI m m₃ hm g₃, g₃, rd,
      s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans s₈))))))), ?_⟩
    intro ptr'
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
    exact ⟨m₄, (Reads.refl m₃).location l₃, s₉.trans (s₁₀.trans (s₁₁.tail
      (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _))))⟩
  · exact .inl (FailsUB.pre s₀ f)

/-- **An array shift by an expression**, from memories where it is `ptr'` or undefined
behaviour. -/
theorem ev_shiftY {I : Mem.Concrete.State → Prop} (hI : Stable I) {e X Y : Eff} {ty : Ctype}
    (h : shiftYOf e = some (X, ty, Y)) {env : Env} {ptr : Mem.Concrete.Pointer} {n : Int}
    (hX : Ev (file := file) (labels := labels) I env X (.loaded (.specified (.pointer ptr))))
    (hY : Ev (file := file) (labels := labels) I env Y (.loaded (.specified (.integer n))))
    {ptr' : Mem.Concrete.Pointer}
    (hs : ∀ m, I m → Mem.Concrete.shiftPointer (PureEval.tagsOf file m) m ptr ty n = .ok ptr' ∨
      ∃ ub, Mem.Concrete.shiftPointer (PureEval.tagsOf file m) m ptr ty n = .error (.ub ub)) :
    Ev (file := file) (labels := labels) I env e (.loaded (.specified (.pointer ptr'))) := by
  refine ⟨shiftYOf_calls h hX.1 hY.1, fun k m hm => ?_⟩
  rcases shiftY_prefix hI h hX hY k m hm with f | ⟨K, m₃, xs, hm₃, g₃, rd, run, rest⟩
  · exact .inr f
  rcases hs m₃ hm₃ with hok | ⟨ub, hub⟩
  · obtain ⟨m₄, g₄, s⟩ := rest ptr'
    exact .inl ⟨xs, m₄, [.annotations xs], .inr rfl, rd, g₃.trans g₄,
      run.trans (.head (.next (requestAux_shift_ok hok K) (plain_value _)) s)⟩
  · exact .inr ⟨.unknown, ub, ArenaFail.Fails.pre file labels run
      (fails_end (fun _ h => nomatch h) (requestAux_shift_ub hub K))⟩

/-- An array shift of the null pointer by an expression is undefined behaviour (UB046). -/
theorem bad_shiftY_null {I : Mem.Concrete.State → Prop} (hI : Stable I) {e X Y : Eff} {ty : Ctype}
    (h : shiftYOf e = some (X, ty, Y)) {env : Env} {t : Ctype} {n : Int}
    (hX : Ev (file := file) (labels := labels) I env X (.loaded (.specified (.pointer (.null t)))))
    (hY : Ev (file := file) (labels := labels) I env Y (.loaded (.specified (.integer n))))
    (hl : ∀ m, I m → ∃ l, Mem.Concrete.typeLayout 64 (PureEval.tagsOf file m) ty = .ok l) :
    Bad (file := file) (labels := labels) I env e := by
  refine ⟨shiftYOf_calls h hX.1 hY.1, fun k m hm => ?_⟩
  rcases shiftY_prefix hI h hX hY k m hm with f | ⟨K, m₃, xs, hm₃, g₃, rd, run, rest⟩
  · exact f
  obtain ⟨l, hl⟩ := hl m₃ hm₃
  have hub : Mem.Concrete.shiftPointer (PureEval.tagsOf file m₃) m₃ (.null t) ty n =
      .error (.ub .UB046_array_pointer_outside) := by
    simp [Mem.Concrete.shiftPointer, hl, bind, Except.bind]
    rfl
  exact ⟨.unknown, _, ArenaFail.Fails.pre file labels run
    (fails_end (fun _ h => nomatch h) (requestAux_shift_ub hub K))⟩

/-! ## The read of the index -/

/-- `let weak p = pure(x) in load(int, p)`: the read of the `int` local `x`. -/
def intReadOf (e : Eff) : Option Sym :=
  match loadOf e with
  | some (.mk _ (.pure (.mk _ () (.sym x))), .mk _ (.basic (.integer (.signed .int)))) => some x
  | _ => none

theorem intReadOf_inv {e : Eff} {x : Sym} (h : intReadOf e = some x) :
    ∃ an ann tann, loadOf e = some (.mk an (.pure (.mk ann () (.sym x))),
      .mk tann (.basic (.integer (.signed .int)))) := by
  unfold intReadOf at h
  split at h
  · rename_i an ann x' tann hl
    cases h
    exact ⟨an, ann, tann, hl⟩
  · cases h

/-- Slots survive reads. -/
theorem slot_reads {m m' : Mem.Concrete.State} {id addr v : Int} (h : Locals.Slot m id addr v)
    (g : Reads m m') : Locals.Slot m' id addr v := by
  obtain ⟨⟨alive, a, look, base, size, atomic, ro⟩, plain, bytes⟩ := h
  obtain ⟨a', look', base', size', atomic', ro'⟩ := g.allocs id a look
  exact ⟨⟨by rw [g.dead]; exact alive, a', look', base'.trans base, size'.trans size,
    atomic'.trans atomic, ro'.trans ro⟩, by unfold Mem.Concrete.PlainAt; rw [g.ptrs]; exact plain,
    by rw [g.bytes]; exact bytes⟩

/-- **The read of an `int` local** whose slot holds `v`. -/
theorem ev_intRead {I : Mem.Concrete.State → Prop} (hI : Stable I) {e : Eff} {x : Sym}
    (h : intReadOf e = some x) {env : Env} {id addr v : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hs : ∀ m, I m → Locals.Slot m id addr v) (hv : ConvInt.IsInt v) :
    Ev (file := file) (labels := labels) I env e (.loaded (.specified (.integer v))) := by
  obtain ⟨an, ann, tann, hl⟩ := intReadOf_inv h
  exact ev_load hI hl (ev_sym I an ann x hx) (mv := .integer (.signed .int) v) fun m hm =>
    ⟨_, Mem.Concrete.load_int _ tann (hs m hm).live (hs m hm).plain hv (hs m hm).bytes⟩

/-! ## `argv[i][x]` -/

/-- `argv[i][x]` with a literal `i` and an `int` local `x`. -/
def charVarOf (argv : Sym) (e : Eff) : Option (Nat × Sym) :=
  match loadOf e with
  | some (c₁, t₁) => match checkOf c₁ with
    | some (s₁, t₂) => match shiftYOf s₁ with
      | some (p₁, t₃, Y) => match intReadOf Y with
        | some x => match loadOf p₁ with
          | some (c₂, t₄) => match checkOf c₂ with
            | some (s₂, t₅) => match shiftOf s₂ with
              | some (l₃, t₆, i) => match loadOf l₃ with
                | some (a, t₇) =>
                  if isSym argv a = true ∧ isChar t₁ = true ∧ isChar t₂ = true ∧ isChar t₃ = true ∧
                      isCharPtr t₄ = true ∧ isCharPtr t₅ = true ∧ isCharPtr t₆ = true ∧
                      isCharPtrPtr t₇ = true ∧ 0 ≤ i then some (i.toNat, x)
                  else none
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | none => none

theorem charVarOf_inv {argv : Sym} {e : Eff} {i : Nat} {x : Sym} (h : charVarOf argv e = some (i, x)) :
    ∃ c₁ t₁ s₁ t₂ p₁ t₃ Y c₂ t₄ s₂ t₅ l₃ t₆ a t₇,
      loadOf e = some (c₁, t₁) ∧ checkOf c₁ = some (s₁, t₂) ∧ shiftYOf s₁ = some (p₁, t₃, Y) ∧
      intReadOf Y = some x ∧
      loadOf p₁ = some (c₂, t₄) ∧ checkOf c₂ = some (s₂, t₅) ∧ shiftOf s₂ = some (l₃, t₆, (i : Int)) ∧
      loadOf l₃ = some (a, t₇) ∧ isSym argv a = true ∧ isChar t₁ = true ∧ isChar t₂ = true ∧
      isChar t₃ = true ∧ isCharPtr t₄ = true ∧ isCharPtr t₅ = true ∧ isCharPtr t₆ = true ∧
      isCharPtrPtr t₇ = true := by
  unfold charVarOf at h
  split at h <;> try cases h
  rename_i c₁ t₁ h1
  split at h <;> try cases h
  rename_i s₁ t₂ h2
  split at h <;> try cases h
  rename_i p₁ t₃ Y h3
  split at h <;> try cases h
  rename_i x' hx
  split at h <;> try cases h
  rename_i c₂ t₄ h4
  split at h <;> try cases h
  rename_i s₂ t₅ h5
  split at h <;> try cases h
  rename_i l₃ t₆ i' h6
  split at h <;> try cases h
  rename_i a t₇ h7
  split at h
  · rename_i hc
    obtain ⟨ha, c1, c2, c3, c4, c5, c6, c7, hi⟩ := hc
    cases h
    refine ⟨c₁, t₁, s₁, t₂, p₁, t₃, Y, c₂, t₄, s₂, t₅, l₃, t₆, a, t₇, h1, h2, h3, hx, h4, h5, ?_, h7, ha,
      c1, c2, c3, c4, c5, c6, c7⟩
    rw [Int.toNat_of_nonneg hi]; exact h6
  · cases h

/-- **`argv[i][x]`** with the argument objects and the slot of `x` holding `v`: byte `v` of
argument `i` for `i < argc` and `0 ≤ v` at most its length; undefined behaviour from the
null slot `i = argc`. -/
theorem charVar_ev {argv : Sym} {e : Eff} {i : Nat} {x : Sym} (h : charVarOf argv e = some (i, x))
    {args : List String} (ha : Spec.ArgsOk args) {idV V idA B : Int} {qs : List Mem.Concrete.Pointer}
    {I : Mem.Concrete.State → Prop} (hI : Stable I)
    (hO : ∀ m, I m → ArgvMem.Objs m args idV V idA B qs) (hm₀ : ∃ m, I m) {env : Env}
    (hargv : env.lookup argv = some (.object (.pointer (.allocated idV V))))
    {id addr v : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hs : ∀ m, I m → Locals.Slot m id addr v) (hv : ConvInt.IsInt v)
    (hi : i ≤ args.length) (hj : ∀ h : i < args.length, 0 ≤ v ∧ v ≤ args[i].length) :
    Ev (file := file) (labels := labels) I env e
      (.loaded (.specified (.integer (charOfArgs args i v.toNat)))) ∧
    (i = args.length → Bad (file := file) (labels := labels) I env e) := by
  obtain ⟨c₁, t₁, s₁, t₂, p₁, t₃, Y, c₂, t₄, s₂, t₅, l₃, t₆, a, t₇, h1, h2, h3, hY, h4, h5, h6, h7, hax,
    k1, k2, k3, k4, k5, k6, k7⟩ := charVarOf_inv h
  obtain ⟨m₀, hm₀⟩ := hm₀
  have hlen : qs.length = args.length := (hO m₀ hm₀).strs.1
  have eY : Ev (file := file) (labels := labels) I env Y (.loaded (.specified (.integer v))) :=
    ev_intRead hI hY hx hs hv
  -- `argv`
  obtain ⟨an, ann, x', rfl, hx'⟩ := isSym_inv hax
  have e₇ : Ev (file := file) (labels := labels) I env (.mk an (.pure (.mk ann () (.sym x'))))
      (.object (.pointer (.allocated idV V))) :=
    ev_sym I an ann x' (by rw [ReturnLit.lookup_key hx']; exact hargv)
  -- `load(char**, argv)`: the array
  obtain ⟨aV, qV, r, hr, rfl⟩ := isCharPtrPtr_inv k7
  have e₆ : Ev (file := file) (labels := labels) I env l₃ (.loaded (.specified (.pointer (.allocated idA B)))) :=
    ev_load hI h7 e₇ (mv := .pointer r (.allocated idA B)) fun m hm =>
      ArgvMem.load_pointer_ann _ m (hO m hm).ptr.live aV qV r le_rfl le_rfl (hO m hm).ptr.bytes
        (by have := (hO m hm).pos; omega) (by have := (hO m hm).top; omega)
        (ArgvMem.abstractPointer_prov m (not_function_of_charPtr hr) (by have := (hO m hm).pos; omega)
          (hO m hm).ptr.prov)
  -- the slot
  obtain ⟨a6, q6, a6', rfl⟩ := isCharPtr_inv k6
  have e₅ : Ev (file := file) (labels := labels) I env s₂
      (.loaded (.specified (.pointer (.allocated idA (B + 8 * i))))) :=
    ev_shift hI h6 e₆ fun m hm => .inl (by
      have := shift_live (tags := PureEval.tagsOf file m) (hO m hm).arr.live
        (ArgvMem.typeLayout_pointer_ann _ a6 q6 (.mk a6' (.basic (.integer .char)))) (a := B) (n := i) (by simp)
        (by simp [hlen]; omega)
      simpa using this)
  obtain ⟨a5, q5, a5', rfl⟩ := isCharPtr_inv k5
  have e₄ : Ev (file := file) (labels := labels) I env c₂ (.object (.pointer (.allocated idA (B + 8 * i)))) :=
    ev_check hI h5 e₅ (fun _ _ => ⟨8, alignment_pointer _ _ _ _⟩) (.inl ⟨_, _, rfl⟩)
  obtain ⟨a4, q4, a4', rfl⟩ := isCharPtr_inv k4
  obtain ⟨a3, rfl⟩ := isChar_inv k3
  obtain ⟨a2, rfl⟩ := isChar_inv k2
  obtain ⟨a1, rfl⟩ := isChar_inv k1
  rcases Nat.lt_or_ge i args.length with hlt | hge
  · -- a string: its pointer
    obtain ⟨b, hq, -, -, -, hbpos⟩ := (hO m₀ hm₀).strs.2 i args[i] (List.getElem?_eq_getElem hlt)
    simp only [Int.zero_add] at hq
    have hb : ∀ m, I m → ∃ str, ArgvMem.Objs m args idV V idA B qs ∧ StartupArgs.StrAt m i b args[i] ∧
        b + args[i].length < 281474976710655 ∧ str = () := by
      intro m hm
      obtain ⟨b', hq', hstr, -, hbtop, -⟩ := (hO m hm).strs.2 i args[i] (List.getElem?_eq_getElem hlt)
      simp only [Int.zero_add, hq, Option.some.injEq, Mem.Concrete.Pointer.allocated.injEq] at hq'
      obtain ⟨-, rfl⟩ := hq'
      simp only [Int.zero_add] at hstr
      exact ⟨(), hO m hm, hstr, by omega, rfl⟩
    have e₃ : Ev (file := file) (labels := labels) I env p₁ (.loaded (.specified (.pointer (.allocated i b)))) :=
      ev_load hI h4 e₄ (mv := .pointer (.mk a4' (.basic (.integer .char))) (.allocated i b)) fun m hm => by
        obtain ⟨hf, hp⟩ := (hO m hm).arr.slot i i b hq
        obtain ⟨-, -, -, htop, -⟩ := hb m hm
        exact ArgvMem.load_pointer_ann _ m (hO m hm).arr.live a4 q4 _ (by omega) (by rw [hlen]; omega) hf
          (by omega) (by omega)
          (ArgvMem.abstractPointer_prov m (not_function_of_char rfl) (by omega) hp)
    obtain ⟨hv0, hvl⟩ := hj hlt
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hv0
    have hjl : j ≤ args[i].length := by exact_mod_cast hvl
    -- `+ x`, its check and the character
    have e₂ : Ev (file := file) (labels := labels) I env s₁
        (.loaded (.specified (.pointer (.allocated i (b + j))))) :=
      ev_shiftY hI h3 e₃ eY fun m hm => .inl (by
        obtain ⟨-, -, hstr, -, -⟩ := hb m hm
        have := shift_live (tags := PureEval.tagsOf file m) hstr.live (ArgvMem.typeLayout_char_ann _ a3)
          (a := b) (n := j) (by simp) (by simp; omega)
        simpa using this)
    have e₁ : Ev (file := file) (labels := labels) I env c₁ (.object (.pointer (.allocated i (b + j)))) :=
      ev_check hI h2 e₂ (fun _ _ => ⟨1, alignment_char _ _⟩) (.inl ⟨_, _, rfl⟩)
    have := ev_load hI h1 e₁ (mv := .integer .char (charOfArgs args i j)) fun m hm => by
      obtain ⟨-, -, hstr, -, -⟩ := hb m hm
      rcases Nat.lt_or_ge j args[i].length with hj' | hj'
      · have hjl' : j < args[i].toList.length := by rw [String.length_toList]; exact hj'
        have hc := hstr.chars j _ (List.getElem?_eq_getElem hjl')
        obtain ⟨h0, h1', -⟩ := ArgvReloc.chars_of_argsOk ha _ (List.getElem_mem hlt) _
          (args[i].toList.getElem_mem hjl')
        rw [charOfArgs_lt hlt hj']
        exact ArgvMem.load_char_ann _ m hstr.live a1 (by omega) (by omega) hc (by omega) (by omega)
      · obtain rfl : j = args[i].length := by omega
        rw [charOfArgs_nul hlt]
        exact ArgvMem.load_char_ann _ m hstr.live a1 (by omega) (by omega) hstr.nul le_rfl (by norm_num)
    exact ⟨by simpa [fromMemory] using this, fun h => by omega⟩
  · -- the null slot
    obtain rfl : i = args.length := by omega
    have e₃ : Ev (file := file) (labels := labels) I env p₁
        (.loaded (.specified (.pointer (.null (.mk a4' (.basic (.integer .char))))))) :=
      ev_load hI h4 e₄ (mv := .pointer (.mk a4' (.basic (.integer .char))) (.null (.mk a4' (.basic (.integer .char)))))
        fun m hm => by
          have hf := (hO m hm).arr.null
          rw [hlen] at hf
          exact ArgvMem.load_pointer_ann _ m (hO m hm).arr.live a4 q4 _ (by omega) (by rw [hlen]; omega) hf
            le_rfl (by norm_num) (StartupArgs.abstractPointer_null m _ _)
    have bad := bad_load h1 (bad_check h2 (bad_shiftY_null hI h3 e₃ eY
      (fun _ _ => ⟨_, ArgvMem.typeLayout_char_ann _ a3⟩)))
    exact ⟨bad.ev _, fun _ => bad⟩

end Silmaril.Compile.Core.Verified.ArgvVar
