module

public import Silmaril.Compiler.Core.Verified.LoadTask.Defs
public import Silmaril.Compiler.Core.Source.PureLocal.Defs

/-! # Cerberus's conditional operator, by local steps

Cerberus elaborates `e ? e₁ : e₂` on `int` operands to

```
let strong c = <e == 0> in
case c of
| Specified(z) =>
    if z = 0 then (let strong u = e₁ in pure(conv_loaded_int(int, u)))
    else (let strong w = e₂ in pure(conv_loaded_int(int, w)))
| Unspecified(_) => pure(undef(...))
```

(the test computes `e == 0`, so its `0` arm is `e₁`). `cond_runs_of_shape` turns this shape into
`CondRuns`, the three pieces of a run that the recursion over expressions needs: from the
whole expression to its test (above one frame `K`); from the test's value `Specified cv` to the
chosen branch's operand, `ea` when `cv = 0` and `eb` otherwise (above one frame `KB`, in an
environment that agrees with the outer one on the local); and from the branch operand's value
`Specified va` (an `int`) to the value of the conditional. Each piece is over any continuation
and at most one annotation frame (the accesses of the test and of the branch), and leaves the
memory `Touched`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Cond

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches)
open ReturnLit (Eff lookup_key)
open LoadTask (Touched)
open ConvInt (IsInt)

variable {file : Program} {labels : Labels}

/-- `Specified n`. -/
abbrev spec (n : Int) : Val := .loaded (.specified (.integer n))

/-- At most one annotation frame, holding the accesses `xs`. -/
def OneAnn (fr : List Frame) (xs : List Access) : Prop := fr = [] ∧ xs = [] ∨ fr = [.annotations xs]

/-! ## Requests -/

theorem requestAux_sseq (m : Mem.Concrete.State) (ann : List Annot) (pat : Pattern Sym) (a b : EE)
    (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.effectExpr (.mk ann (.sseq pat a b)) env) k wc =
      .next (.effectExpr a env) (.strongBind pat b env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_strongBind (m : Mem.Concrete.State) (ann : List Annot) (u : Sym) (ty : BaseType)
    (v : Val) (b : EE) (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.strongBind (.mk ann (.base (some u, ty))) b env :: k) wc =
      .next (.effectExpr b (extendEnv [(u, v)] env)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, matchPattern]

theorem requestAux_strongBind_annotations (m : Mem.Concrete.State) (xs : List Access) (ann : List Annot)
    (u : Sym) (ty : BaseType) (v : Val) (b : EE) (env : Env) (k : List Frame) :
    requestAux file labels m (.value v)
        (.annotations xs :: .strongBind (.mk ann (.base (some u, ty))) b env :: k) false =
      .next (.effectExpr b (extendEnv [(u, v)] env)) (.annotations xs :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, requestAux_strongBind]

theorem requestAux_effectCase (m : Mem.Concrete.State) (v : Val) (bs : List (Pattern Sym × EE))
    (env : Env) (k : List Frame) (wc : Bool) {xs : Bindings} {body : EE}
    (h : selectCase v bs = some (xs, body)) :
    requestAux file labels m (.value v) (.effectCase bs env :: k) wc =
      .next (.effectExpr body (extendEnv xs env)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, h]

theorem requestAux_effectIf (m : Mem.Concrete.State) (b : Bool) (yes no : EE) (env : Env)
    (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value (boolean b)) (.effectIf yes no env :: k) wc =
      .next (.effectExpr (if b then yes else no) env) k := by
  rw [requestAux.eq_def]; cases b <;> simp [awaitsScheduling, boolean]

/-- A focused `case`: its scrutinee above a case frame, after a possible change of the current
location. -/
theorem requestAux_case (m : Mem.Concrete.State) (annots : List Annot) (p : PE)
    (bs : List (Pattern Sym × EE)) (env : Env) (k : List Frame) (wc : Bool) :
    ∃ l, requestAux file labels m (.effectExpr (.mk annots (.case_ p bs)) env) k wc =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.effectCase bs env :: k)
      else .next (.setLocation l (.pureExpr p env)) (.effectCase bs env :: k) := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true]
  split
  · split
    · exact ⟨m.currentLocation, by simp⟩
    · exact ⟨_, rfl⟩
  · exact ⟨m.currentLocation, by simp⟩

/-- A focused `if`: its condition above an if frame, after a possible change of the current
location. -/
theorem requestAux_if (m : Mem.Concrete.State) (annots : List Annot) (p : PE) (yes no : EE)
    (env : Env) (k : List Frame) (wc : Bool) :
    ∃ l, requestAux file labels m (.effectExpr (.mk annots (.if_ p yes no)) env) k wc =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.effectIf yes no env :: k)
      else .next (.setLocation l (.pureExpr p env)) (.effectIf yes no env :: k) := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true]
  split
  · split
    · exact ⟨m.currentLocation, by simp⟩
    · exact ⟨_, rfl⟩
  · exact ⟨m.currentLocation, by simp⟩

/-! ## Frames -/

/-- A value over at most one annotation frame reaches a strong bind of a symbol. -/
theorem value_strongBind {fr : List Frame} {xs : List Access} (hfr : OneAnn fr xs) (v : Val)
    (ann : List Annot) (u : Sym) (ty : BaseType) (b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels false
      ⟨.value v, fr ++ .strongBind (.mk ann (.base (some u, ty))) b env :: k, m⟩
      ⟨.effectExpr b (extendEnv [(u, v)] env), fr ++ k, m⟩ := by
  rcases hfr with ⟨rfl, rfl⟩ | rfl
  · exact .single (.next (requestAux_strongBind m ann u ty v b env k false)
      (LoadTask.plain_effectExpr _ _))
  · exact .single (.next (requestAux_strongBind_annotations m xs ann u ty v b env k)
      (LoadTask.plain_effectExpr _ _))

/-- Two runs' annotation frames merge into at most one. -/
theorem merge {fr fr' : List Frame} {xs ys : List Access} (h : OneAnn fr xs) (h' : OneAnn fr' ys)
    (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ zs fr'', OneAnn fr'' zs ∧ (∀ a ∈ zs, a ∈ ys ∨ a ∈ xs) ∧
      LocalReaches file labels false ⟨.value v, fr' ++ (fr ++ k), m⟩ ⟨.value v, fr'' ++ k, m⟩ := by
  rcases h' with ⟨rfl, rfl⟩ | rfl
  · exact ⟨xs, fr, h, fun a ha => .inr ha, .refl⟩
  · rcases h with ⟨rfl, rfl⟩ | rfl
    · exact ⟨ys, [.annotations ys], .inr rfl, fun a ha => .inl ha, .refl⟩
    · refine ⟨ys ++ xs, [.annotations (ys ++ xs)], .inr rfl, fun a ha => List.mem_append.mp ha, ?_⟩
      exact .single (.next (Interleave.requestAux_value_merge file labels m v ys xs k false)
        (LoadTask.plain_value v))

/-! ## The conditional -/

/-- The pieces of a run of a conditional `e` with test `ec` and branch operands `ea`, `eb`. -/
def CondRuns (x : Sym) (e ec ea eb : Eff) : Prop :=
  ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State), ∃ K : Frame,
    LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr ec env, K :: k, m⟩ ∧
    ∀ (cv : Int) (fr : List Frame) (xs : List Access), OneAnn fr xs → ∀ m₁ : Mem.Concrete.State,
      ∃ (env₂ : Env) (KB : Frame) (m₂ : Mem.Concrete.State),
        env₂.lookup x = env.lookup x ∧ Touched m₁ m₂ ∧
        LocalReaches file labels false ⟨.value (spec cv), fr ++ K :: k, m₁⟩
          ⟨.effectExpr (if cv = 0 then ea else eb) env₂, KB :: (fr ++ k), m₂⟩ ∧
        ∀ va : Int, IsInt va → ∀ (fr' : List Frame) (ys : List Access), OneAnn fr' ys →
          ∀ m₃ : Mem.Concrete.State, ∃ m₄, Touched m₃ m₄ ∧
            LocalReaches file labels false ⟨.value (spec va), fr' ++ (KB :: (fr ++ k)), m₃⟩
              ⟨.value (spec va), fr' ++ (fr ++ k), m₄⟩

/-- The end of a branch: `let strong u = <operand> in pure(conv_loaded_int(int, u'))`. -/
theorem branch_end {u u' s : Sym} (hu : u'.key = u.key) (hs : ConvInt.isConvLoadedInt file s = true)
    (pa : List Annot) (ty : BaseType) (an an₁ a1 c1 a3 : List Annot) (env : Env) (k : List Frame)
    {va : Int} (hva : IsInt va) {fr' : List Frame} {ys : List Access} (h' : OneAnn fr' ys)
    (m₃ : Mem.Concrete.State) :
    ∃ m₄, Touched m₃ m₄ ∧ LocalReaches file labels false
      ⟨.value (spec va), fr' ++ .strongBind (.mk pa (.base (some u, ty)))
        (.mk an (.pure (.mk an₁ () (.call (.sym s) [.mk a1 () (.val (.ctype (.mk c1
          (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])))) env :: k, m₃⟩
      ⟨.value (spec va), fr' ++ k, m₄⟩ := by
  let CALL : PE := .mk an₁ () (.call (.sym s) [.mk a1 () (.val (.ctype (.mk c1
    (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])
  let env₃ := extendEnv [(u, spec va)] env
  have s₁ := value_strongBind (file := file) (labels := labels) h' (spec va) pa u ty
    (.mk an (.pure CALL)) env k m₃
  obtain ⟨l, hr⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m₃ an CALL env₃
    (fr' ++ k) false
  obtain ⟨l', s₂⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr CALL env₃) (by simpa using hr)
  let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l'}
  have heval : Eval file (tagsOf file m₄) env₃ (.inl CALL) (.inl (spec va)) :=
    ConvInt.convLoadedInt_eval (ann := c1) hs hva
      (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
  have s₃ := PureLocal.eval_local file (tagsOf file m₄) (wc := false) (labels := labels) heval
    (.diagnosticLocation m₃.currentLocation :: (fr' ++ k)) m₄ rfl
  refine ⟨m₄, ⟨l', m₃.lastUsed, rfl⟩, s₁.trans (s₂.trans (s₃.tail ?_))⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
    (LoadTask.plain_value _)

/-- **The conditional's shape gives its runs.** -/
theorem cond_runs_of_shape {x c c' z z' u u' w w' s s' : Sym}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 d0 d1 d2 d3 d4 d5 : List Annot}
    {t1 t2 t3 t4 : BaseType} {ec ea eb : Eff} {ps : List (Pattern Sym)} {q : PE}
    (hc : c'.key = c.key) (hz : z'.key = z.key) (hu : u'.key = u.key) (hw : w'.key = w.key)
    (hcx : c.key ≠ x.key) (hzx : z.key ≠ x.key)
    (hs : ConvInt.isConvLoadedInt file s = true) (hs' : ConvInt.isConvLoadedInt file s' = true) :
    CondRuns (file := file) (labels := labels) x
      (.mk a0 (.sseq (.mk a1 (.base (some c, t1))) ec
        (.mk a2 (.case_ (.mk a3 () (.sym c'))
          [(.mk a4 (.ctor .specified [.mk a5 (.base (some z, t2))]),
            .mk a6 (.if_ (.mk a7 () (.op .eq (.mk a8 () (.sym z')) (.mk a9 () (.val (.object (.integer 0))))))
              (.mk b0 (.sseq (.mk b1 (.base (some u, t3))) ea
                (.mk b2 (.pure (.mk b3 () (.call (.sym s) [.mk b4 () (.val (.ctype (.mk b5
                  (.basic (.integer (.signed .int)))))), .mk b6 () (.sym u')]))))))
              (.mk b7 (.sseq (.mk b8 (.base (some w, t4))) eb
                (.mk b9 (.pure (.mk d0 () (.call (.sym s') [.mk d1 () (.val (.ctype (.mk d2
                  (.basic (.integer (.signed .int)))))), .mk d3 () (.sym w')])))))))),
           (.mk d4 (.ctor .unspecified ps), .mk d5 (.pure q))]))))
      ec ea eb := by
  intro env k m
  let CA : PE := .mk b3 () (.call (.sym s) [.mk b4 () (.val (.ctype (.mk b5
      (.basic (.integer (.signed .int)))))), .mk b6 () (.sym u')])
  let CB : PE := .mk d0 () (.call (.sym s') [.mk d1 () (.val (.ctype (.mk d2
      (.basic (.integer (.signed .int)))))), .mk d3 () (.sym w')])
  let BA : EE := .mk b0 (.sseq (.mk b1 (.base (some u, t3))) ea (.mk b2 (.pure CA)))
  let BB : EE := .mk b7 (.sseq (.mk b8 (.base (some w, t4))) eb (.mk b9 (.pure CB)))
  let IF : EE := .mk a6 (.if_ (.mk a7 () (.op .eq (.mk a8 () (.sym z'))
    (.mk a9 () (.val (.object (.integer 0)))))) BA BB)
  let BS : List (Pattern Sym × EE) := [(.mk a4 (.ctor .specified [.mk a5 (.base (some z, t2))]), IF),
    (.mk d4 (.ctor .unspecified ps), .mk d5 (.pure q))]
  let R : EE := .mk a2 (.case_ (.mk a3 () (.sym c')) BS)
  refine ⟨.strongBind (.mk a1 (.base (some c, t1))) R env,
    .single (.next (requestAux_sseq m a0 _ ec R env k false) (LoadTask.plain_effectExpr _ _)), ?_⟩
  intro cv fr xs hfr m₁
  let env₁ := extendEnv [(c, spec cv)] env
  let env₂ := extendEnv [(z, .object (.integer cv))] env₁
  have s₁ := value_strongBind (file := file) (labels := labels) hfr (spec cv) a1 c t1 R env k m₁
  -- the case on the test's value
  obtain ⟨l, hr⟩ := requestAux_case (file := file) (labels := labels) m₁ a2 (.mk a3 () (.sym c')) BS
    env₁ (fr ++ k) false
  obtain ⟨l₁, s₂⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr _ env₁) (by simpa using hr)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
  have s₃ : LocalReaches file labels false ⟨.pureExpr (.mk a3 () (.sym c')) env₁, .effectCase BS env₁ :: (fr ++ k), m₂⟩
      ⟨.effectExpr IF env₂, fr ++ k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_sym m₂ a3 c' env₁ (ConvInt.lookup_one hc) _ false)
      (LoadTask.plain_value _))
      (.single (.next (requestAux_effectCase m₂ _ BS env₁ (fr ++ k) false
        (by simp [BS, selectCase, matchPattern])) (LoadTask.plain_effectExpr _ _)))
  -- the `if` on `z = 0`
  obtain ⟨l', hr'⟩ := requestAux_if (file := file) (labels := labels) m₂ a6 (.mk a7 () (.op .eq
    (.mk a8 () (.sym z')) (.mk a9 () (.val (.object (.integer 0)))))) BA BB env₂ (fr ++ k) false
  obtain ⟨l₂, s₄⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr _ env₂) (by simpa using hr')
  let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
  have heval : Eval file (tagsOf file m₃) env₂ (.inl (.mk a7 () (.op .eq (.mk a8 () (.sym z'))
      (.mk a9 () (.val (.object (.integer 0))))))) (.inl (boolean (cv == 0))) :=
    .op (.cons (.sym (ConvInt.lookup_one hz)) (.cons .val .nil))
      (by simp [primitive, integerBin, runtimeValue, runtimeObject]; rfl)
  have s₅ := PureLocal.eval_local file (tagsOf file m₃) (wc := false) (labels := labels) heval
    (.effectIf BA BB env₂ :: (fr ++ k)) m₃ rfl
  have hx₂ : env₂.lookup x = env.lookup x := by
    rw [ConvInt.lookup_one_other (fun e => hzx e.symm), ConvInt.lookup_one_other (fun e => hcx e.symm)]
  by_cases h0 : cv = 0
  · have hb : (cv == 0) = true := by simp [h0]
    have s₆ : LocalReaches file labels false ⟨.value (boolean (cv == 0)), .effectIf BA BB env₂ :: (fr ++ k), m₃⟩
        ⟨.effectExpr BA env₂, fr ++ k, m₃⟩ :=
      .single (.next (by rw [requestAux_effectIf]; simp [hb]) (LoadTask.plain_effectExpr _ _))
    refine ⟨env₂, .strongBind (.mk b1 (.base (some u, t3))) (.mk b2 (.pure CA)) env₂, m₃, hx₂,
      ⟨l₂, m₁.lastUsed, rfl⟩, ?_, ?_⟩
    · rw [ite_eq_left h0]
      exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.tail
        (.next (requestAux_sseq m₃ b0 _ ea _ env₂ (fr ++ k) false) (LoadTask.plain_effectExpr _ _)))))))
    · intro va hva fr' ys h' m₄
      simpa using branch_end (file := file) (labels := labels) hu hs b1 t3 b2 b3 b4 b5 b6 env₂
        (fr ++ k) hva h' m₄
  · have hb : (cv == 0) = false := by simp [h0]
    have s₆ : LocalReaches file labels false ⟨.value (boolean (cv == 0)), .effectIf BA BB env₂ :: (fr ++ k), m₃⟩
        ⟨.effectExpr BB env₂, fr ++ k, m₃⟩ :=
      .single (.next (by rw [requestAux_effectIf]; simp [hb]) (LoadTask.plain_effectExpr _ _))
    refine ⟨env₂, .strongBind (.mk b8 (.base (some w, t4))) (.mk b9 (.pure CB)) env₂, m₃, hx₂,
      ⟨l₂, m₁.lastUsed, rfl⟩, ?_, ?_⟩
    · rw [ite_eq_right h0]
      exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.tail
        (.next (requestAux_sseq m₃ b7 _ eb _ env₂ (fr ++ k) false) (LoadTask.plain_effectExpr _ _)))))))
    · intro va hva fr' ys h' m₄
      simpa using branch_end (file := file) (labels := labels) hw hs' b8 t4 b9 d0 d1 d2 d3 env₂
        (fr ++ k) hva h' m₄

end Silmaril.Compile.Core.Verified.Cond
