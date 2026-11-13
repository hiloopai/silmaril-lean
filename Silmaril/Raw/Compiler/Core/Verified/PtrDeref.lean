module

public import Silmaril.Compiler.Core.Verified.ArgvChar.Defs
public import Silmaril.Compiler.Core.Verified.IntExpr.Defs
public import Silmaril.Compiler.Core.Verified.PtrNull.Defs
public import Silmaril.Compiler.Core.Verified.SubobjectTask.Defs

/-! # Dereferencing a pointer local

Cerberus elaborates `*p` (and `p[0]`) for a local `int *p` to the designator
`CHECK(LOAD(int*, p))` (resp. `CHECK(SHIFT(LOAD(int*, p), int, 0))`): the load of the pointer
from `p`'s object, the array shift by `0`, and `PtrValidForDeref`, which selects the pointer or
`undef(UB043)`. `derefOf` recognises these designators (`ArgvChar.loadOf`, `shiftOf`,
`checkOf`) and returns `p`.

`deref_runs`: when `p`'s object holds a pointer to a live, aligned `int` object (`StrMem.PtrObj`),
the designator runs by local steps to that pointer, with read accesses only and the memory
`Touched` (a pointer load exposes nothing). This is the strengthening of `ArgvChar`'s
`ev_load`/`ev_shift`/`ev_check` (which only keep `ArgvMem.Reads`) that the statement fragments'
read tasks need.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PtrDeref

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ReturnLit (Eff)
open LoadTask (Touched ReadTask)
open Cond (OneAnn)
open ArgvChar (loadOf loadOf_inv shiftOf shiftOf_inv checkOf checkOf_inv wseq_enter value_effectBind
  plain_effectExpr plain_pureExpr plain_value plain_apply pureArms_calls)

/-- `int`. -/
def isInt : Ctype → Bool
  | .mk _ (.basic (.integer (.signed .int))) => true
  | _ => false

/-- A pointer to `int`. -/
def isIntPtr : Ctype → Bool
  | .mk _ (.pointer _ (.mk _ (.basic (.integer (.signed .int))))) => true
  | _ => false

theorem isInt_inv {t : Ctype} (h : isInt t = true) :
    ∃ ann, t = .mk ann (.basic (.integer (.signed .int))) := by
  obtain ⟨ann, node⟩ := t
  unfold isInt at h
  split at h
  · rename_i a heq; cases heq; exact ⟨_, rfl⟩
  · cases h

theorem isIntPtr_inv {t : Ctype} (h : isIntPtr t = true) :
    ∃ ann q ann', t = .mk ann (.pointer q (.mk ann' (.basic (.integer (.signed .int))))) := by
  obtain ⟨ann, node⟩ := t
  unfold isIntPtr at h
  split at h
  · rename_i a q a' heq; cases heq; exact ⟨_, _, _, rfl⟩
  · cases h

/-- `pure(r)`. -/
def symOf : Eff → Option Sym
  | .mk _ (.pure (.mk _ () (.sym r))) => some r
  | _ => none

theorem symOf_inv {e : Eff} {r : Sym} (h : symOf e = some r) :
    ∃ an pa, e = .mk an (.pure (.mk pa () (.sym r))) := by
  unfold symOf at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

/-- `LOAD(int*, r)`: `let weak p = pure(r) in load(int*, p)`. -/
def ptrLoad (e : Eff) : Option Sym :=
  match loadOf e with
  | some (X, ty) => if isIntPtr ty then symOf X else none
  | none => none

/-- The designator `*r` or `r[0]` of a pointer local `r`. -/
def derefOf (e : Eff) : Option Sym :=
  match checkOf e with
  | some (S, ty) =>
    if isInt ty then
      match ptrLoad S with
      | some r => some r
      | none => match shiftOf S with
        | some (X, ty', n) => if isInt ty' ∧ n = 0 then ptrLoad X else none
        | none => none
    else none
  | none => none

theorem ptrLoad_inv {e : Eff} {r : Sym} (h : ptrLoad e = some r) :
    ∃ X ty, loadOf e = some (X, ty) ∧ isIntPtr ty = true ∧ symOf X = some r := by
  unfold ptrLoad at h
  split at h
  · rename_i X ty hl
    split at h
    · exact ⟨X, ty, hl, by assumption, h⟩
    · cases h
  · cases h

theorem derefOf_inv {e : Eff} {r : Sym} (h : derefOf e = some r) :
    ∃ S ty, checkOf e = some (S, ty) ∧ isInt ty = true ∧
      (ptrLoad S = some r ∨ ∃ X ty', shiftOf S = some (X, ty', 0) ∧ isInt ty' = true ∧
        ptrLoad X = some r) := by
  unfold derefOf at h
  split at h
  · rename_i S ty hc
    split at h
    · rename_i hi
      split at h
      · rename_i r' hp; cases h; exact ⟨S, ty, hc, hi, .inl hp⟩
      · split at h
        · rename_i X ty' n hs
          split at h
          · rename_i hn
            obtain ⟨h1, rfl⟩ := hn
            exact ⟨S, ty, hc, hi, .inr ⟨X, ty', hs, h1, h⟩⟩
          · cases h
        · cases h
    · cases h
  · cases h

theorem ptrLoad_noCall {e : Eff} {r : Sym} (h : ptrLoad e = some r) : hasCCall e = false := by
  obtain ⟨X, ty, hl, -, hs⟩ := ptrLoad_inv h
  obtain ⟨an, pa, rfl⟩ := symOf_inv hs
  obtain ⟨a0, pa', p, pt, la, l, u, a3, a4, p', rfl, -⟩ := loadOf_inv hl
  simp [hasCCall]

theorem shiftOf_noCall {e X : Eff} {ty : Ctype} {n : Int} (h : shiftOf e = some (X, ty, n))
    (hX : hasCCall X = false) : hasCCall e = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, rfl, -, -, -, -, -, -, -, hrest⟩ := shiftOf_inv h
  simp [hasCCall, hX]
  exact fun a b hab => pureArms_calls hrest a b hab

theorem derefOf_noCall {e : Eff} {r : Sym} (h : derefOf e = some r) : hasCCall e = false := by
  obtain ⟨S, ty, hc, -, hS⟩ := derefOf_inv h
  refine ArgvChar.checkOf_calls hc ?_
  rcases hS with hS | ⟨X, ty', hs, -, hX⟩
  · exact ptrLoad_noCall hS
  · exact shiftOf_noCall hs (ptrLoad_noCall hX)

/-! ## Local runs that only touch the memory -/

variable {file : Program} {labels : Labels}

/-- From every memory satisfying `I`, over every continuation, `e` (without calls) runs by local
steps to `v`, with read accesses only, over at most one annotation frame, the memory `Touched`. -/
def Runs (I : Mem.Concrete.State → Prop) (env : Env) (e : EE) (v : Val) : Prop :=
  hasCCall e = false ∧ ∀ k m, I m → ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧
    Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value v, fr ++ k, m'⟩

theorem Runs.task {I : Mem.Concrete.State → Prop} {env : Env} {e : EE} {v : Val}
    (h : Runs (file := file) (labels := labels) I env e v) :
    ReadTask (file := file) (labels := labels) I env e v := by
  refine ⟨h.1, fun m hm => ?_⟩
  obtain ⟨xs, m', fr, hfr, rd, tch, run⟩ := h.2 [] m hm
  refine ⟨xs, m', rd, tch, fr, by simpa using run, ?_⟩
  rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]

/-- `pure(r)` runs to the value of `r`. -/
theorem sym_runs (I : Mem.Concrete.State → Prop) (an pa : List Annot) (r : Sym) {env : Env} {v : Val}
    (hr : env.lookup r = some v) :
    Runs (file := file) (labels := labels) I env (.mk an (.pure (.mk pa () (.sym r)))) v := by
  refine ⟨by simp [hasCCall], fun k m _ => ?_⟩
  obtain ⟨l, run⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) an pa
    r env hr k m
  exact ⟨[], _, [], .inl ⟨rfl, rfl⟩, by simp, ⟨l, m.lastUsed, rfl⟩, run⟩

/-- **Loading the pointer** held by the object of `r`. -/
theorem ptrLoad_runs {e : Eff} {r : Sym} (h : ptrLoad e = some r) (I : Mem.Concrete.State → Prop)
    {env : Env} {pid paddr id addr : Int}
    (hr : env.lookup r = some (.object (.pointer (.allocated pid paddr))))
    (hobj : ∀ m, I m → StrMem.PtrObj m pid paddr id addr) :
    Runs (file := file) (labels := labels) I env e
      (.loaded (.specified (.pointer (.allocated id addr)))) := by
  obtain ⟨X, ty, hl, hty, hs⟩ := ptrLoad_inv h
  obtain ⟨an, pa, rfl⟩ := symOf_inv hs
  obtain ⟨a0, pa', p, pt, la, l, u, a3, a4, p', rfl, hp'⟩ := loadOf_inv hl
  obtain ⟨tann, q, ann', rfl⟩ := isIntPtr_inv hty
  refine ⟨by simp [hasCCall], fun k m hm => ?_⟩
  let ptr : Val := .object (.pointer (.allocated pid paddr))
  let LOAD : EE := .mk la (.action (.mk .pos (.mk l u (.load (.mk a3 () (.val (.ctype
    (.mk tann (.pointer q (.mk ann' (.basic (.integer (.signed .int))))))))) (.mk a4 () (.sym p')) .na))))
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk pa' (.base (some p, pt)))
    (.mk an (.pure (.mk pa () (.sym r)))) LOAD env k m
  obtain ⟨l₁, s₁⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) an pa
    r env hr (.effectBind (.mk pa' (.base (some p, pt))) LOAD env :: k) m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  let env₁ := extendEnv [(p, ptr)] env
  have s₂ : LocalReaches file labels false
      ⟨.value ptr, .effectBind (.mk pa' (.base (some p, pt))) LOAD env :: k, m₁⟩
      ⟨.effectExpr LOAD env₁, k, m₁⟩ :=
    .single (.next (LoadTask.requestAux_bind _ _ _ _ _ _ _ _ _) (plain_effectExpr _ _))
  obtain ⟨l₂, s₃⟩ := LoadTask.focus_local (file := file) (labels := labels) (wc := false)
    (plain_pureExpr _ env₁) (LoadTask.requestAux_load m₁ la l u _ (.mk a4 () (.sym p')) env₁ k false)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₂}
  have obj₂ : StrMem.PtrObj m₂ pid paddr id addr := by
    have o := hobj m hm
    exact ⟨⟨o.slot.alive, o.slot.alloc, o.slot.below, o.slot.above⟩, o.bytes, o.prov, o.range⟩
  have hload := StrMem.load_ptr (PureEval.tagsOf file m₂) tann q (.mk ann' (.basic (.integer (.signed .int))))
    rfl obj₂
  obtain ⟨a, ha, hreq⟩ := ArgvChar.requestAux_loadTyped (file := file) (labels := labels) hload k
  have s₄ : LocalReaches file labels false
      ⟨.pureExpr (.mk a3 () (.val (.ctype (.mk tann (.pointer q (.mk ann' (.basic (.integer (.signed .int))))))))) env₁,
        .arguments (.memory .load) [] [.mk a4 () (.sym p')] env₁ :: k, m₂⟩
      ⟨.apply (.memory .load) [.ctype (.mk tann (.pointer q (.mk ann' (.basic (.integer (.signed .int)))))),
        .object (.pointer (.allocated pid paddr))], k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_val m₂ a3 _ env₁ _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₂ _ [] _ _ [] env₁ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_sym m₂ a4 p' env₁ (ConvInt.lookup_one hp') _ false) (plain_value _))
          (.single (.next (LoadTask.requestAux_last_argument m₂ _ _ _ env₁ _ false) (plain_apply _ _)))))
  refine ⟨[a], {m₂ with lastUsed := some pid}, [.annotations [a]], .inr rfl, by simpa using ha,
    ⟨l₂, some pid, rfl⟩, s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (.single (.memory (name := "Load") ?_))))))⟩
  simpa [fromMemory] using hreq

/-- **Loading the null pointer** held by the object of `r`. -/
theorem ptrLoadNull_runs {e : Eff} {r : Sym} (h : ptrLoad e = some r) (I : Mem.Concrete.State → Prop)
    {env : Env} {pid paddr : Int}
    (hr : env.lookup r = some (.object (.pointer (.allocated pid paddr))))
    (hobj : ∀ m, I m → StrMem.PtrNull m pid paddr) :
    ∃ t, Runs (file := file) (labels := labels) I env e (.loaded (.specified (.pointer (.null t)))) := by
  obtain ⟨X, ty, hl, hty, hs⟩ := ptrLoad_inv h
  obtain ⟨an, pa, rfl⟩ := symOf_inv hs
  obtain ⟨a0, pa', p, pt, la, l, u, a3, a4, p', rfl, hp'⟩ := loadOf_inv hl
  obtain ⟨tann, q, ann', rfl⟩ := isIntPtr_inv hty
  refine ⟨.mk ann' (.basic (.integer (.signed .int))), by simp [hasCCall], fun k m hm => ?_⟩
  let ptr : Val := .object (.pointer (.allocated pid paddr))
  let LOAD : EE := .mk la (.action (.mk .pos (.mk l u (.load (.mk a3 () (.val (.ctype
    (.mk tann (.pointer q (.mk ann' (.basic (.integer (.signed .int))))))))) (.mk a4 () (.sym p')) .na))))
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk pa' (.base (some p, pt)))
    (.mk an (.pure (.mk pa () (.sym r)))) LOAD env k m
  obtain ⟨l₁, s₁⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) an pa
    r env hr (.effectBind (.mk pa' (.base (some p, pt))) LOAD env :: k) m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  let env₁ := extendEnv [(p, ptr)] env
  have s₂ : LocalReaches file labels false
      ⟨.value ptr, .effectBind (.mk pa' (.base (some p, pt))) LOAD env :: k, m₁⟩
      ⟨.effectExpr LOAD env₁, k, m₁⟩ :=
    .single (.next (LoadTask.requestAux_bind _ _ _ _ _ _ _ _ _) (plain_effectExpr _ _))
  obtain ⟨l₂, s₃⟩ := LoadTask.focus_local (file := file) (labels := labels) (wc := false)
    (plain_pureExpr _ env₁) (LoadTask.requestAux_load m₁ la l u _ (.mk a4 () (.sym p')) env₁ k false)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₂}
  have obj₂ : StrMem.PtrNull m₂ pid paddr := by
    have o := hobj m hm
    exact ⟨⟨o.slot.alive, o.slot.alloc, o.slot.below, o.slot.above⟩, o.bytes⟩
  have hload := StrMem.load_null (PureEval.tagsOf file m₂) tann q (.mk ann' (.basic (.integer (.signed .int))))
    obj₂
  obtain ⟨a, ha, hreq⟩ := ArgvChar.requestAux_loadTyped (file := file) (labels := labels) hload k
  have s₄ : LocalReaches file labels false
      ⟨.pureExpr (.mk a3 () (.val (.ctype (.mk tann (.pointer q (.mk ann' (.basic (.integer (.signed .int))))))))) env₁,
        .arguments (.memory .load) [] [.mk a4 () (.sym p')] env₁ :: k, m₂⟩
      ⟨.apply (.memory .load) [.ctype (.mk tann (.pointer q (.mk ann' (.basic (.integer (.signed .int)))))),
        .object (.pointer (.allocated pid paddr))], k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_val m₂ a3 _ env₁ _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₂ _ [] _ _ [] env₁ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_sym m₂ a4 p' env₁ (ConvInt.lookup_one hp') _ false) (plain_value _))
          (.single (.next (LoadTask.requestAux_last_argument m₂ _ _ _ env₁ _ false) (plain_apply _ _)))))
  refine ⟨[a], {m₂ with lastUsed := some pid}, [.annotations [a]], .inr rfl, by simpa using ha,
    ⟨l₂, some pid, rfl⟩, s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (.single (.memory (name := "Load") ?_))))))⟩
  simpa [fromMemory] using hreq

/-- **`SHIFT(X, int, 0)`** of a pointer into a live `int` object is the pointer. -/
theorem shift0_runs {e X : Eff} {ty : Ctype} (h : shiftOf e = some (X, ty, 0)) (hty : isInt ty = true)
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int}
    (hX : Runs (file := file) (labels := labels) I env X (.loaded (.specified (.pointer (.allocated id addr)))))
    (live : ∀ m, I m → Mem.Concrete.LiveInt m id addr) (hXne : ∀ an p, X ≠ .mk an (.pure p)) :
    Runs (file := file) (labels := labels) I env e (.loaded (.specified (.pointer (.allocated id addr)))) := by
  refine ⟨shiftOf_noCall h hX.1, fun k m hm => ?_⟩
  obtain ⟨tann, rfl⟩ := isInt_inv hty
  obtain ⟨a0, pp, p1, a, ta, p2, c, tc, au, al, al', ac, as, as1, a', as2, c', q0, q1, q2, x, tx, q3, q4,
    y, ty', w0, w1, z, tz, w2, w3, x', w4, w5, y', w6, w7, w8, z', rest, rfl, ha, hc, hx, hy, hz, hca,
    hyx, -⟩ := shiftOf_inv h
  let ptr : Mem.Concrete.Pointer := .allocated id addr
  let LIT : EE := .mk al (.pure (.mk al' () (.val (.loaded (.specified (.integer 0))))))
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
    (LoadTask.literal_readTask I env al al' (.loaded (.specified (.integer 0))))
    (fun eq => absurd eq hneq) m hm
  let v₁ : Val := .loaded (.specified (.pointer ptr))
  let v₂ : Val := .loaded (.specified (.integer 0))
  let env₁ := extendEnv [(a, v₁), (c, v₂)] env
  let K : List Frame := .annotations xs :: k
  have s₂ : LocalReaches file labels false
      ⟨.value (.tuple [v₁, runtimeValue (.loaded (.specified (.integer 0)))]),
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
  let env₂ := extendEnv [(x, .object (.pointer ptr)), (y, .object (.integer 0))] env₁
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
      ⟨.apply (.memop .ptrArrayShift) [.object (.pointer ptr), .ctype INT, .object (.integer 0)], K', m₃⟩ :=
    .head (.next (LoadTask.requestAux_sym m₃ w3 x' env₂ (ArgvChar.lookup2_first hx) _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ _ env₂ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_val m₃ w4 _ env₂ _ false) (plain_value _))
          (.head (.next (LoadTask.requestAux_argument m₃ _ _ _ _ [] env₂ _ false) (plain_pureExpr _ _))
            (.head (.next (LoadTask.requestAux_sym m₃ w5 y' env₂ (ArgvChar.lookup2_second hy hyx) _ false)
              (plain_value _))
              (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false)
                (plain_apply _ _)))))))
  have g₃ : Touched m m₃ := g₁.trans ⟨l₂, m₁.lastUsed, by simp [m₃, m₂]⟩
  have live₃ : Mem.Concrete.LiveInt m₃ id addr := live m₃ (hI m m₃ hm g₃)
  have hshift : Mem.Concrete.shiftPointer (PureEval.tagsOf file m₃) m₃ ptr INT 0 = .ok ptr := by
    obtain ⟨-, al0, look, base, size, -⟩ := live₃
    have hb : al0.base ≤ addr ∧ addr ≤ al0.base + al0.size := by omega
    rw [show INT = Mem.Concrete.intType tann from rfl]
    simp [Mem.Concrete.shiftPointer, ptr, look, hb, Mem.Concrete.layout_intType, bind, Except.bind,
      pure, Except.pure]
  let env₃ := extendEnv [(z, .object (.pointer ptr))] env₂
  have s₉ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
    (pat := .mk w1 (.base (some z, tz))) (v := .object (.pointer ptr)) rfl PURE env₂ K m₃
  obtain ⟨l₃, s₁₀⟩ := ExitCall.pure_local file labels (wc := false) (env := env₃) (k := K) (m := m₃) w6
    (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')]))
  let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l₃}
  have heval' : PureEval.Eval file (PureEval.tagsOf file m₄) env₃
      (.inl (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))
      (.inl (.loaded (.specified (.pointer ptr)))) :=
    .ctor (.cons (.sym (ConvInt.lookup_one hz)) .nil) (by simp [primitive, pure, Except.pure])
  have s₁₁ := PureLocal.eval_local file (PureEval.tagsOf file m₄) (wc := false) (labels := labels) heval'
    (.diagnosticLocation m₃.currentLocation :: K) m₄ rfl
  refine ⟨xs, m₄, [.annotations xs], .inr rfl, rd, g₃.trans ⟨l₃, m₃.lastUsed, rfl⟩,
    s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans (s₈.trans
      ((Relation.ReflTransGen.single (.next (ArgvChar.requestAux_shift_ok hshift K') (plain_value _))).trans
        (s₉.trans (s₁₀.trans (s₁₁.tail
          (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _))))))))))))))⟩

/-- **`CHECK(S)`** for `int` of a pointer to a live, aligned `int` object is the pointer. -/
theorem check_runs {e S : Eff} {ty : Ctype} (h : checkOf e = some (S, ty)) (hty : isInt ty = true)
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int}
    (hS : Runs (file := file) (labels := labels) I env S (.loaded (.specified (.pointer (.allocated id addr)))))
    (alive : ∀ m, I m → id ∉ m.dead) (aligned : addr % 4 = 0) :
    Runs (file := file) (labels := labels) I env e (.object (.pointer (.allocated id addr))) := by
  refine ⟨ArgvChar.checkOf_calls h hS.1, fun k m hm => ?_⟩
  obtain ⟨tann, rfl⟩ := isInt_inv hty
  obtain ⟨a0, pq, q, tq, ac, as, q', r0, r1, x, tx, w0, w1, b, tb, w2, w3, w4, x', w5, w6, w7, b', w8, x'',
    w9, ul, ub, rest, rfl, hq, hx, hb, hx'', hxb, -⟩ := checkOf_inv h
  let ptr : Mem.Concrete.Pointer := .allocated id addr
  let INT : Ctype := .mk tann (.basic (.integer (.signed .int)))
  let MEMOP : EE := .mk w2 (.memop .ptrValidForDeref [.mk w3 () (.val (.ctype INT)), .mk w4 () (.sym x')])
  let IF : PE := .mk w6 () (.if_ (.mk w7 () (.sym b')) (.mk w8 () (.sym x'')) (.mk w9 () (.undef ul ub)))
  let PURE : EE := .mk w5 (.pure IF)
  let ARM : EE := .mk w0 (.wseq (.mk w1 (.base (some b, tb))) MEMOP PURE)
  let BS : List (Pattern Sym × EE) := (.mk r0 (.ctor .specified [.mk r1 (.base (some x, tx))]), ARM) :: rest
  let CASE : EE := .mk ac (.case_ (.mk as () (.sym q')) BS)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk pq (.base (some q, tq))) S CASE env k m
  obtain ⟨xs, m₁, fr, hfr, rd, g₁, run⟩ := hS.2 (.effectBind (.mk pq (.base (some q, tq))) CASE env :: k) m hm
  let v : Val := .loaded (.specified (.pointer ptr))
  let env₁ := extendEnv [(q, v)] env
  have s₁ := value_effectBind (file := file) (labels := labels) hfr (pat := .mk pq (.base (some q, tq)))
    (v := v) rfl CASE env k m₁
  obtain ⟨l, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ ac (.mk as () (.sym q')) BS
    env₁ (fr ++ k) false
  obtain ⟨l₁, s₂⟩ := LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
  let env₂ := extendEnv [(x, .object (.pointer ptr))] env₁
  have s₃ : LocalReaches file labels false ⟨.pureExpr (.mk as () (.sym q')) env₁,
      .effectCase BS env₁ :: (fr ++ k), m₂⟩ ⟨.effectExpr ARM env₂, fr ++ k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_sym m₂ as q' env₁ (ConvInt.lookup_one hq) _ false) (plain_value _))
      (.single (.next (Cond.requestAux_effectCase m₂ _ BS env₁ (fr ++ k) false
        (by simp [BS, selectCase, matchPattern, v])) (plain_effectExpr _ _)))
  let K' : List Frame := .effectBind (.mk w1 (.base (some b, tb))) PURE env₂ :: (fr ++ k)
  have s₄ := wseq_enter (file := file) (labels := labels) w0 (.mk w1 (.base (some b, tb))) MEMOP PURE env₂
    (fr ++ k) m₂
  obtain ⟨l₂, s₅⟩ := ArgvChar.check_enter (file := file) (labels := labels) (env := env₂) (k := K') (m := m₂) w2
    (.mk w3 () (.val (.ctype INT))) [.mk w4 () (.sym x')]
  let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
  have g₃ : Touched m m₃ := g₁.trans ⟨l₂, m₁.lastUsed, by simp [m₃, m₂]⟩
  have s₆ : LocalReaches file labels false
      ⟨.pureExpr (.mk w3 () (.val (.ctype INT))) env₂, .arguments (.pointerCheck true) []
        [.mk w4 () (.sym x')] env₂ :: K', m₃⟩
      ⟨.apply (.pointerCheck true) [.ctype INT, .object (.pointer ptr)], K', m₃⟩ :=
    .head (.next (LoadTask.requestAux_val m₃ w3 _ env₂ _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ [] env₂ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_sym m₃ w4 x' env₂ (ConvInt.lookup_one hx) _ false)
          (plain_value _))
          (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false) (plain_apply _ _)))))
  have hal : Mem.Concrete.alignment (PureEval.tagsOf file m₃) INT = .ok 4 := by
    have hl := Mem.Concrete.layout_intType (PureEval.tagsOf file m₃) tann
    simp only [Mem.Concrete.intType] at hl
    simp [INT, Mem.Concrete.alignment, hl, bind, Except.bind, pure, Except.pure]
  have hdead : id ∉ m₃.dead := alive m₃ (hI m m₃ hm g₃)
  have s₇ : LocalReaches file labels false
      ⟨.apply (.pointerCheck true) [.ctype INT, .object (.pointer ptr)], K', m₃⟩
      ⟨.value (boolean true), K', m₃⟩ := by
    have := ArgvChar.requestAux_check (file := file) (labels := labels) hal id addr K'
    simp only [aligned, hdead] at this
    exact .single (.next (by simpa using this) (plain_value _))
  let env₃ := extendEnv [(b, boolean true)] env₂
  have s₈ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
    (pat := .mk w1 (.base (some b, tb))) (v := boolean true) rfl PURE env₂ (fr ++ k) m₃
  obtain ⟨l₃, s₉⟩ := ExitCall.pure_local file labels (wc := false) (env := env₃) (k := fr ++ k) (m := m₃)
    w5 IF
  let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l₃}
  have hb₃ : env₃.lookup b' = some (boolean true) := ConvInt.lookup_one hb
  have hx₃ : env₃.lookup x'' = some (.object (.pointer ptr)) := by
    rw [ConvInt.lookup_one_other (by rw [hx'']; exact hxb), ConvInt.lookup_one hx'']
  have heval : PureEval.Eval file (PureEval.tagsOf file m₄) env₃ (.inl IF) (.inl (.object (.pointer ptr))) :=
    .ifTrue (.sym hb₃) (.sym hx₃)
  have s₁₀ := PureLocal.eval_local file (PureEval.tagsOf file m₄) (wc := false) (labels := labels) heval
    (.diagnosticLocation m₃.currentLocation :: (fr ++ k)) m₄ rfl
  exact ⟨xs, m₄, fr, hfr, rd, g₃.trans ⟨l₃, m₃.lastUsed, rfl⟩,
    s₀.trans (run.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans
      (s₈.trans (s₉.trans (s₁₀.tail
        (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _)))))))))))))⟩

/-- **The designator `*r` / `r[0]`** runs to the pointer that `r`'s object holds. -/
theorem deref_runs {e : Eff} {r : Sym} (h : derefOf e = some r) (I : Mem.Concrete.State → Prop)
    (hI : ∀ m m', I m → Touched m m' → I m') {env : Env} {pid paddr id addr : Int}
    (hr : env.lookup r = some (.object (.pointer (.allocated pid paddr))))
    (hobj : ∀ m, I m → StrMem.PtrObj m pid paddr id addr ∧ Mem.Concrete.LiveInt m id addr)
    (aligned : addr % 4 = 0) :
    Runs (file := file) (labels := labels) I env e (.object (.pointer (.allocated id addr))) := by
  obtain ⟨S, ty, hc, hty, hS⟩ := derefOf_inv h
  refine check_runs hc hty I hI ?_ (fun m hm => (hobj m hm).2.alive) aligned
  rcases hS with hS | ⟨X, ty', hs, hty', hX⟩
  · exact ptrLoad_runs hS I hr fun m hm => (hobj m hm).1
  · refine shift0_runs hs hty' I hI (ptrLoad_runs hX I hr fun m hm => (hobj m hm).1)
      (fun m hm => (hobj m hm).2) ?_
    obtain ⟨X', ty'', hl, -, -⟩ := ptrLoad_inv hX
    obtain ⟨a0, pa', p, pt, la, l, u, a3, a4, p', rfl, -⟩ := loadOf_inv hl
    intro an q eq
    cases eq

theorem _root_.Silmaril.Compile.Core.Verified.StrMem.PtrObj.touched {m m' : Mem.Concrete.State}
    {id addr pid paddr : Int} (h : StrMem.PtrObj m id addr pid paddr) (t : Touched m m') :
    StrMem.PtrObj m' id addr pid paddr := by
  obtain ⟨l, u, rfl⟩ := t
  exact ⟨⟨h.slot.alive, h.slot.alloc, h.slot.below, h.slot.above⟩, h.bytes, h.prov, h.range⟩

/-- **The read through a designator** that runs to the pointer of an `int` slot:
`let weak p = d in load(int, p')`. -/
theorem read_runs (a0 pa la a3 c1 a4 : List Annot) (pt : BaseType) (p p' : Sym) (d : Eff)
    (l : Loc) (u : Unit) (hp' : p'.key = p.key) (I : Mem.Concrete.State → Prop) {env : Env}
    {id addr n : Int} (hd : Runs (file := file) (labels := labels) I env d
      (.object (.pointer (.allocated id addr))))
    (hn : Mem.Concrete.IntRange n) (slot : ∀ m, I m → Locals.Slot m id addr n)
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
  have slot₁ : IntSubobject.Slot m₁ id addr n := (IntSubobject.Slot.ofSlot (slot m hm)).touched t₁
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

/-! ## A pointer local as a test -/

/-- `r == NULL` as Cerberus elaborates a pointer local `r` used as a test:
`let weak q = LOAD(int*, r) in case q of Specified(s) => let weak b = PtrEq(s, NULL) in
pure(if b then Specified(1) else Specified(0)) | _ => pure(…)`. -/
def nullTestOf : Eff → Option Sym
  | .mk _ (.wseq (.mk _ (.base (some q, _))) S
      (.mk _ (.case_ (.mk _ () (.sym q'))
        [(.mk _ (.ctor .specified [.mk _ (.base (some s, _))]),
          .mk _ (.wseq (.mk _ (.base (some b, _)))
            (.mk _ (.memop .ptrEq [.mk _ () (.sym s'), .mk _ () (.val (.object (.pointer (.null _))))]))
            (.mk _ (.pure (.mk _ () (.if_ (.mk _ () (.sym b'))
              (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer 1)))]))
              (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer 0)))])))))))),
         (.mk _ (.base (none, _)), .mk _ (.pure _))]))) =>
      if q'.key = q.key ∧ s'.key = s.key ∧ b'.key = b.key ∧ s.key ≠ b.key then ptrLoad S else none
  | _ => none

theorem nullTestOf_inv {e : Eff} {r : Sym} (h : nullTestOf e = some r) :
    ∃ (a0 pq : List Annot) (q : Sym) (tq : BaseType) (S : Eff) (ac as : List Annot) (q' : Sym)
      (r0 r1 : List Annot) (s : Sym) (ts : BaseType) (w0 w1 : List Annot) (b : Sym) (tb : BaseType)
      (w2 w3 : List Annot) (s' : Sym) (w4 : List Annot) (nt : Ctype) (w5 w6 w7 : List Annot) (b' : Sym)
      (w8 w9 w10 w11 : List Annot) (u0 : List Annot) (tu : BaseType) (u1 : List Annot) (pu : PE),
      e = .mk a0 (.wseq (.mk pq (.base (some q, tq))) S
        (.mk ac (.case_ (.mk as () (.sym q'))
          [(.mk r0 (.ctor .specified [.mk r1 (.base (some s, ts))]),
            .mk w0 (.wseq (.mk w1 (.base (some b, tb)))
              (.mk w2 (.memop .ptrEq [.mk w3 () (.sym s'), .mk w4 () (.val (.object (.pointer (.null nt))))]))
              (.mk w5 (.pure (.mk w6 () (.if_ (.mk w7 () (.sym b'))
                (.mk w8 () (.ctor .specified [.mk w9 () (.val (.object (.integer 1)))]))
                (.mk w10 () (.ctor .specified [.mk w11 () (.val (.object (.integer 0)))])))))))),
           (.mk u0 (.base (none, tu)), .mk u1 (.pure pu))]))) ∧
      q'.key = q.key ∧ s'.key = s.key ∧ b'.key = b.key ∧ s.key ≠ b.key ∧ ptrLoad S = some r := by
  unfold nullTestOf at h
  split at h
  · split at h
    · rename_i hc
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, h⟩
    · cases h
  · cases h

theorem nullTestOf_noCall {e : Eff} {r : Sym} (h : nullTestOf e = some r) : hasCCall e = false := by
  obtain ⟨_, _, _, _, S, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, -, -, -, -, hS⟩ := nullTestOf_inv h
  simp [hasCCall, ptrLoad_noCall hS]

/-- A located `memop(PtrEq, p :: ps)`: the focus, then its first operand. -/
theorem eq_enter {env : Env} {k : List Frame} {m : Mem.Concrete.State}
    (annots : List Annot) (p : PE) (ps : List PE) :
    ∃ l, LocalReaches file labels false
      ⟨.effectExpr (.mk annots (.memop .ptrEq (p :: ps))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.pointerCompare false) [] ps env :: k, {m with currentLocation := l}⟩ := by
  have hr : ∃ l, requestAux file labels m (.effectExpr (.mk annots (.memop .ptrEq (p :: ps))) env)
      k false =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.arguments (.pointerCompare false) [] ps env :: k)
      else .next (.setLocation l (.pureExpr p env)) (.arguments (.pointerCompare false) [] ps env :: k) := by
    rw [requestAux.eq_def]
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true, arguments]
    split
    · split
      · exact ⟨m.currentLocation, by simp⟩
      · exact ⟨_, rfl⟩
    · exact ⟨m.currentLocation, by simp⟩
  obtain ⟨l, hr⟩ := hr
  exact LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)

theorem requestAux_ptrEq_null {m : Mem.Concrete.State} (id a : Int) (t : Ctype) (k : List Frame) :
    requestAux file labels m (.apply (.pointerCompare false)
      [.object (.pointer (.allocated id a)), .object (.pointer (.null t))]) k false =
      .next (.value (boolean false)) k := by
  rw [requestAux.eq_def]
  simp [awaitsScheduling, primitive, pure, Except.pure, bind, Except.bind]

/-- **`r == NULL`** of a pointer local holding an allocated pointer is `0`. -/
theorem nullTest_runs {e : Eff} {r : Sym} (h : nullTestOf e = some r) (I : Mem.Concrete.State → Prop)
    {env : Env} {pid paddr id addr : Int}
    (hr : env.lookup r = some (.object (.pointer (.allocated pid paddr))))
    (hobj : ∀ m, I m → StrMem.PtrObj m pid paddr id addr) :
    Runs (file := file) (labels := labels) I env e (.loaded (.specified (.integer 0))) := by
  refine ⟨nullTestOf_noCall h, fun k m hm => ?_⟩
  obtain ⟨a0, pq, q, tq, S, ac, as, q', r0, r1, s, ts, w0, w1, b, tb, w2, w3, s', w4, nt, w5, w6, w7, b',
    w8, w9, w10, w11, u0, tu, u1, pu, rfl, hq, hs, hb, hsb, hS⟩ := nullTestOf_inv h
  let ptr : Mem.Concrete.Pointer := .allocated id addr
  let MEMOP : EE := .mk w2 (.memop .ptrEq [.mk w3 () (.sym s'), .mk w4 () (.val (.object (.pointer (.null nt))))])
  let IF : PE := .mk w6 () (.if_ (.mk w7 () (.sym b'))
    (.mk w8 () (.ctor .specified [.mk w9 () (.val (.object (.integer 1)))]))
    (.mk w10 () (.ctor .specified [.mk w11 () (.val (.object (.integer 0)))])))
  let PURE : EE := .mk w5 (.pure IF)
  let ARM : EE := .mk w0 (.wseq (.mk w1 (.base (some b, tb))) MEMOP PURE)
  let BS : List (Pattern Sym × EE) := [(.mk r0 (.ctor .specified [.mk r1 (.base (some s, ts))]), ARM),
    (.mk u0 (.base (none, tu)), .mk u1 (.pure pu))]
  let CASE : EE := .mk ac (.case_ (.mk as () (.sym q')) BS)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk pq (.base (some q, tq))) S CASE env k m
  obtain ⟨xs, m₁, fr, hfr, rd, g₁, run⟩ := (ptrLoad_runs (file := file) (labels := labels) hS I hr hobj).2
    (.effectBind (.mk pq (.base (some q, tq))) CASE env :: k) m hm
  let v : Val := .loaded (.specified (.pointer ptr))
  let env₁ := extendEnv [(q, v)] env
  have s₁ := value_effectBind (file := file) (labels := labels) hfr (pat := .mk pq (.base (some q, tq)))
    (v := v) rfl CASE env k m₁
  obtain ⟨l, hr'⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ ac (.mk as () (.sym q')) BS
    env₁ (fr ++ k) false
  obtain ⟨l₁, s₂⟩ := LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr')
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
  let env₂ := extendEnv [(s, .object (.pointer ptr))] env₁
  have s₃ : LocalReaches file labels false ⟨.pureExpr (.mk as () (.sym q')) env₁,
      .effectCase BS env₁ :: (fr ++ k), m₂⟩ ⟨.effectExpr ARM env₂, fr ++ k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_sym m₂ as q' env₁ (ConvInt.lookup_one hq) _ false) (plain_value _))
      (.single (.next (Cond.requestAux_effectCase m₂ _ BS env₁ (fr ++ k) false
        (by simp [BS, selectCase, matchPattern, v])) (plain_effectExpr _ _)))
  let K' : List Frame := .effectBind (.mk w1 (.base (some b, tb))) PURE env₂ :: (fr ++ k)
  have s₄ := wseq_enter (file := file) (labels := labels) w0 (.mk w1 (.base (some b, tb))) MEMOP PURE env₂
    (fr ++ k) m₂
  obtain ⟨l₂, s₅⟩ := eq_enter (file := file) (labels := labels) (env := env₂) (k := K') (m := m₂) w2
    (.mk w3 () (.sym s')) [.mk w4 () (.val (.object (.pointer (.null nt))))]
  let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
  have s₆ : LocalReaches file labels false
      ⟨.pureExpr (.mk w3 () (.sym s')) env₂, .arguments (.pointerCompare false) []
        [.mk w4 () (.val (.object (.pointer (.null nt))))] env₂ :: K', m₃⟩
      ⟨.apply (.pointerCompare false) [.object (.pointer ptr), .object (.pointer (.null nt))], K', m₃⟩ :=
    .head (.next (LoadTask.requestAux_sym m₃ w3 s' env₂ (ConvInt.lookup_one hs) _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ [] env₂ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_val m₃ w4 _ env₂ _ false) (plain_value _))
          (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false) (plain_apply _ _)))))
  have s₇ : LocalReaches file labels false
      ⟨.apply (.pointerCompare false) [.object (.pointer ptr), .object (.pointer (.null nt))], K', m₃⟩
      ⟨.value (boolean false), K', m₃⟩ :=
    .single (.next (requestAux_ptrEq_null id addr nt K') (plain_value _))
  let env₃ := extendEnv [(b, boolean false)] env₂
  have s₈ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
    (pat := .mk w1 (.base (some b, tb))) (v := boolean false) rfl PURE env₂ (fr ++ k) m₃
  obtain ⟨l₃, s₉⟩ := ExitCall.pure_local file labels (wc := false) (env := env₃) (k := fr ++ k) (m := m₃)
    w5 IF
  let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l₃}
  have hb₃ : env₃.lookup b' = some (boolean false) := ConvInt.lookup_one hb
  have heval : PureEval.Eval file (PureEval.tagsOf file m₄) env₃ (.inl IF)
      (.inl (.loaded (.specified (.integer 0)))) :=
    .ifFalse (.sym hb₃) (.ctor (.cons .val .nil) (by simp [primitive, pure, Except.pure, runtimeValue,
      runtimeObject]))
  have s₁₀ := PureLocal.eval_local file (PureEval.tagsOf file m₄) (wc := false) (labels := labels) heval
    (.diagnosticLocation m₃.currentLocation :: (fr ++ k)) m₄ rfl
  refine ⟨xs, m₄, fr, hfr, rd, g₁.trans ⟨l₃, m₁.lastUsed, by simp [m₄, m₃, m₂]⟩, ?_⟩
  exact s₀.trans (run.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans
    (s₈.trans (s₉.trans (s₁₀.tail
      (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _)))))))))))))

theorem requestAux_ptrEq_null_null {m : Mem.Concrete.State} (t' t : Ctype) (k : List Frame) :
    requestAux file labels m (.apply (.pointerCompare false)
      [.object (.pointer (.null t')), .object (.pointer (.null t))]) k false =
      .next (.value (boolean true)) k := by
  rw [requestAux.eq_def]
  simp [awaitsScheduling, primitive, pure, Except.pure, bind, Except.bind]

/-- **`r == NULL`** of a pointer local holding the null pointer is `1`. -/
theorem nullTestNull_runs {e : Eff} {r : Sym} (h : nullTestOf e = some r) (I : Mem.Concrete.State → Prop)
    {env : Env} {pid paddr : Int}
    (hr : env.lookup r = some (.object (.pointer (.allocated pid paddr))))
    (hobj : ∀ m, I m → StrMem.PtrNull m pid paddr) :
    Runs (file := file) (labels := labels) I env e (.loaded (.specified (.integer 1))) := by
  refine ⟨nullTestOf_noCall h, fun k m hm => ?_⟩
  obtain ⟨a0, pq, q, tq, S, ac, as, q', r0, r1, s, ts, w0, w1, b, tb, w2, w3, s', w4, nt, w5, w6, w7, b',
    w8, w9, w10, w11, u0, tu, u1, pu, rfl, hq, hs, hb, hsb, hS⟩ := nullTestOf_inv h
  let MEMOP : EE := .mk w2 (.memop .ptrEq [.mk w3 () (.sym s'), .mk w4 () (.val (.object (.pointer (.null nt))))])
  let IF : PE := .mk w6 () (.if_ (.mk w7 () (.sym b'))
    (.mk w8 () (.ctor .specified [.mk w9 () (.val (.object (.integer 1)))]))
    (.mk w10 () (.ctor .specified [.mk w11 () (.val (.object (.integer 0)))])))
  let PURE : EE := .mk w5 (.pure IF)
  let ARM : EE := .mk w0 (.wseq (.mk w1 (.base (some b, tb))) MEMOP PURE)
  let BS : List (Pattern Sym × EE) := [(.mk r0 (.ctor .specified [.mk r1 (.base (some s, ts))]), ARM),
    (.mk u0 (.base (none, tu)), .mk u1 (.pure pu))]
  let CASE : EE := .mk ac (.case_ (.mk as () (.sym q')) BS)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk pq (.base (some q, tq))) S CASE env k m
  obtain ⟨T, hrun⟩ := ptrLoadNull_runs (file := file) (labels := labels) hS I hr hobj
  let ptr : Mem.Concrete.Pointer := .null T
  obtain ⟨xs, m₁, fr, hfr, rd, g₁, run⟩ := hrun.2 (.effectBind (.mk pq (.base (some q, tq))) CASE env :: k) m hm
  let v : Val := .loaded (.specified (.pointer ptr))
  let env₁ := extendEnv [(q, v)] env
  have s₁ := value_effectBind (file := file) (labels := labels) hfr (pat := .mk pq (.base (some q, tq)))
    (v := v) rfl CASE env k m₁
  obtain ⟨l, hr'⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ ac (.mk as () (.sym q')) BS
    env₁ (fr ++ k) false
  obtain ⟨l₁, s₂⟩ := LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr')
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
  let env₂ := extendEnv [(s, .object (.pointer ptr))] env₁
  have s₃ : LocalReaches file labels false ⟨.pureExpr (.mk as () (.sym q')) env₁,
      .effectCase BS env₁ :: (fr ++ k), m₂⟩ ⟨.effectExpr ARM env₂, fr ++ k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_sym m₂ as q' env₁ (ConvInt.lookup_one hq) _ false) (plain_value _))
      (.single (.next (Cond.requestAux_effectCase m₂ _ BS env₁ (fr ++ k) false
        (by simp [BS, selectCase, matchPattern, v])) (plain_effectExpr _ _)))
  let K' : List Frame := .effectBind (.mk w1 (.base (some b, tb))) PURE env₂ :: (fr ++ k)
  have s₄ := wseq_enter (file := file) (labels := labels) w0 (.mk w1 (.base (some b, tb))) MEMOP PURE env₂
    (fr ++ k) m₂
  obtain ⟨l₂, s₅⟩ := eq_enter (file := file) (labels := labels) (env := env₂) (k := K') (m := m₂) w2
    (.mk w3 () (.sym s')) [.mk w4 () (.val (.object (.pointer (.null nt))))]
  let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
  have s₆ : LocalReaches file labels false
      ⟨.pureExpr (.mk w3 () (.sym s')) env₂, .arguments (.pointerCompare false) []
        [.mk w4 () (.val (.object (.pointer (.null nt))))] env₂ :: K', m₃⟩
      ⟨.apply (.pointerCompare false) [.object (.pointer ptr), .object (.pointer (.null nt))], K', m₃⟩ :=
    .head (.next (LoadTask.requestAux_sym m₃ w3 s' env₂ (ConvInt.lookup_one hs) _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ [] env₂ _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_val m₃ w4 _ env₂ _ false) (plain_value _))
          (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false) (plain_apply _ _)))))
  have s₇ : LocalReaches file labels false
      ⟨.apply (.pointerCompare false) [.object (.pointer ptr), .object (.pointer (.null nt))], K', m₃⟩
      ⟨.value (boolean true), K', m₃⟩ :=
    .single (.next (requestAux_ptrEq_null_null T nt K') (plain_value _))
  let env₃ := extendEnv [(b, boolean true)] env₂
  have s₈ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
    (pat := .mk w1 (.base (some b, tb))) (v := boolean true) rfl PURE env₂ (fr ++ k) m₃
  obtain ⟨l₃, s₉⟩ := ExitCall.pure_local file labels (wc := false) (env := env₃) (k := fr ++ k) (m := m₃)
    w5 IF
  let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l₃}
  have hb₃ : env₃.lookup b' = some (boolean true) := ConvInt.lookup_one hb
  have heval : PureEval.Eval file (PureEval.tagsOf file m₄) env₃ (.inl IF)
      (.inl (.loaded (.specified (.integer 1)))) :=
    .ifTrue (.sym hb₃) (.ctor (.cons .val .nil) (by simp [primitive, pure, Except.pure, runtimeValue,
      runtimeObject]))
  have s₁₀ := PureLocal.eval_local file (PureEval.tagsOf file m₄) (wc := false) (labels := labels) heval
    (.diagnosticLocation m₃.currentLocation :: (fr ++ k)) m₄ rfl
  refine ⟨xs, m₄, fr, hfr, rd, g₁.trans ⟨l₃, m₁.lastUsed, by simp [m₄, m₃, m₂]⟩, ?_⟩
  exact s₀.trans (run.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans
    (s₈.trans (s₉.trans (s₁₀.tail
      (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _)))))))))))))

end Silmaril.Compile.Core.Verified.PtrDeref
