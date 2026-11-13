module

public import Silmaril.Compiler.Core.Verified.CallArg.Defs
/-! # std.core's parameter-list functions on lists of any length

`CallArg.length_one_eval` and `CallArg.nth_zero_eval` evaluate `params_length` and
`params_nth` on one-element lists. A call with several arguments asks for `params_length`
of a longer list and for `params_nth` at every index, through std.core's recursions:

```
params_length_aux(acc, cs) = case cs of [] => acc | _ :: xs => params_length_aux(acc + 1, xs)
params_nth(cs, n) = case cs of [] => error | x :: xs =>
  if n = 0 then x else if n > 0 then params_nth(xs, n - 1) else error
```
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.CallManyEval

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval)
open ConvInt (lookupFun)
open CallArg

/-- A list of ctypes as a Core value. -/
def ctypes (cs : List Ctype) : Val := .list .ctype (cs.map .ctype)

/-- std.core's `params_nth`, with its recursive arm calling `self`. -/
def isNthRec (self : Sym) : ConvInt.Fun → Bool
  | .function _ [(cs, _), (n, _)]
      (.mk _ () (.case_ (.mk _ () (.sym cs₁))
        [(.mk _ (.ctor (.nil _) []), _),
         (.mk _ (.ctor .cons [.mk _ (.base (some x, _)), .mk _ (.base (some xs, _))]),
          .mk _ () (.if_ (.mk _ () (.op .eq (.mk _ () (.sym n₁)) (.mk _ () (.val (.object (.integer z))))))
            (.mk _ () (.sym x₁))
            (.mk _ () (.if_ (.mk _ () (.op .gt (.mk _ () (.sym n₂)) (.mk _ () (.val (.object (.integer z'))))))
              (.mk _ () (.call (.sym self₁) [.mk _ () (.sym xs₁),
                .mk _ () (.op .sub (.mk _ () (.sym n₃)) (.mk _ () (.val (.object (.integer o)))))]))
              _))))])) =>
      decide (cs.key ≠ n.key ∧ cs₁.key = cs.key ∧ n₁.key = n.key ∧ z = 0 ∧ x₁.key = x.key ∧
        n.key ≠ x.key ∧ n.key ≠ xs.key ∧ n₂.key = n.key ∧ z' = 0 ∧ self₁.key = self.key ∧
        xs₁.key = xs.key ∧ n₃.key = n.key ∧ o = 1 ∧ xs.key ≠ x.key)
  | _ => false

/-- The symbol `s` names std.core's recursive `params_nth`. -/
def isParamsNthRec (file : File Codec.wireModel Unit Unit) (s : Sym) : Bool :=
  match lookupFun file s with
  | some d => isNthRec s d
  | none => false

variable {file : Program}

theorem lookupFun_key {a b : Sym} (h : a.key = b.key) : lookupFun file a = lookupFun file b := by
  unfold lookupFun; rw [ReturnLit.lookup_key h, ReturnLit.lookup_key h]

/-- `params_length_aux(acc, cs) = acc + |cs|`. -/
theorem aux_eval {aux : Sym} {d : ConvInt.Fun} (hd : lookupFun file aux = some d)
    (hl : isLengthAux aux d = true) (tags : Mem.Concrete.Tags) (cs : List Ctype) (acc : Int)
    {s : Sym} (hs : s.key = aux.key) {env : Env} {ann : List Annot} {pa pc : PE}
    (ha : Eval file tags env (.inl pa) (.inl (.object (.integer acc))))
    (hc : Eval file tags env (.inl pc) (.inl (ctypes cs))) :
    Eval file tags env (.inl (.mk ann () (.call (.sym s) [pa, pc])))
      (.inl (.object (.integer (acc + cs.length)))) := by
  unfold isLengthAux at hl
  split at hl
  · rename_i bt' accS abt csS cbt' pann' cann' cs'₁ nbt nann sann acc₁ cpa wa wbt xa xs xbt
      capann aux₁ oa1 opann acc₂ oa2 o xsa xs₁
    obtain ⟨hne, hcs', hacc, haux, hacc₂, rfl, hxs, hax⟩ := of_decide_eq_true hl
    have hd₁ : lookupFun file aux₁ = some _ := (lookupFun_key haux).trans hd
    let body : PE := .mk pann' () (.case_ (.mk cann' () (.sym cs'₁))
        [(.mk nbt (.ctor (.nil nann) []), .mk sann () (.sym acc₁)),
         (.mk cpa (.ctor .cons [.mk wa (.base (none, wbt)), .mk xa (.base (some xs, xbt))]),
          .mk capann () (.call (.sym aux₁) [.mk oa1 () (.op .add (.mk opann () (.sym acc₂))
            (.mk oa2 () (.val (.object (.integer 1))))), .mk xsa () (.sym xs₁)]))])
    have key : ∀ (cs : List Ctype) (acc : Int),
        Eval file tags (extendEnv [(accS, .object (.integer acc)), (csS, ctypes cs)] ∅) (.inl body)
          (.inl (.object (.integer (acc + cs.length)))) := by
      intro cs
      induction cs with
      | nil =>
        intro acc
        refine .case_ (xs := []) (body := .mk sann () (.sym acc₁))
          (.sym (ConvInt.lookup_two_second hcs' (fun h => hne h.symm)))
          (by simp [selectCase, matchPattern, ctypes]) ?_
        simpa using (Eval.sym (ConvInt.lookup_two_first hacc) :
          Eval file tags (extendEnv [] (extendEnv [(accS, .object (.integer acc)), (csS, ctypes [])] ∅))
            (.inl (.mk sann () (.sym acc₁))) (.inl (.object (.integer acc))))
      | cons c cs ih =>
        intro acc
        refine .case_ (xs := [(xs, ctypes cs)])
          (body := .mk capann () (.call (.sym aux₁) [.mk oa1 () (.op .add (.mk opann () (.sym acc₂))
            (.mk oa2 () (.val (.object (.integer 1))))), .mk xsa () (.sym xs₁)]))
          (.sym (ConvInt.lookup_two_second hcs' (fun h => hne h.symm)))
          (by simp [selectCase, matchPattern, ctypes, bind, Option.bind]) ?_
        have hv : acc + ((c :: cs).length : Int) = acc + 1 + (cs.length : Int) := by
          simp only [List.length_cons]; push_cast; ring
        rw [hv]
        refine .call (vs := [.object (.integer (acc + 1)), ctypes cs])
          (.cons (.op (vs := [.object (.integer acc), .object (.integer 1)])
            (.cons (.sym ?_) (.cons .val .nil)) ?_) (.cons (.sym ?_) .nil))
          (ConvInt.functionBody_eq hd₁ rfl) (ih (acc + 1))
        · rw [lookup_cons_ne (by rw [hacc₂]; exact hax), lookup_nil]
          exact ConvInt.lookup_two_first hacc₂
        · simp [primitive, integerBin, integer, pure, Except.pure]
        · exact lookup_cons_eq hxs
    have hds : lookupFun file s = some _ := (lookupFun_key hs).trans hd
    exact .call (.cons ha (.cons hc .nil)) (ConvInt.functionBody_eq hds rfl) (key cs acc)
  · cases hl

/-- `params_length(cs) = |cs|`, and `not (params_length(ps) = |cs|)` is false. -/
theorem length_eval {len pty : Sym} {env : Env} {cs : List Ctype} {N : Int}
    {ann an a1 a2 a3 : List Annot}
    (hl : isParamsLength file len = true) (hp : env.lookup pty = some (ctypes cs))
    (hN : (cs.length : Int) = N) (tags : Mem.Concrete.Tags) :
    Eval file tags env (.inl (.mk an () (.not (.mk ann () (.op .eq
      (.mk a1 () (.call (.sym len) [.mk a2 () (.sym pty)])) (.mk a3 () (.val (.object (.integer N)))))))))
      (.inl .false) := by
  unfold isParamsLength at hl
  split at hl
  · rename_i d hd
    unfold isLength at hl
    split at hl
    · rename_i _ bt cs' cbt pann aux vann z wann cs₁
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨⟨rfl, hcs⟩, hl⟩ := hl
      split at hl
      · rename_i d' hd'
        have inner := aux_eval (file := file) hd' hl tags cs 0 rfl (ann := pann)
          (env := extendEnv [(cs', ctypes cs)] ∅) (pa := .mk vann () (.val (.object (.integer 0))))
          (pc := .mk wann () (.sym cs₁)) .val (.sym (ConvInt.lookup_one hcs))
        rw [zero_add, hN] at inner
        refine .not (vs := [.true]) (.cons (.op (vs := [.object (.integer N), .object (.integer N)])
          (.cons (.call (v := .object (.integer N)) (.cons (.sym hp) .nil)
            (ConvInt.functionBody_eq hd rfl) inner) (.cons .val .nil)) ?_) .nil) ?_
        · simp [primitive, integerBin, boolean, pure, Except.pure]
        · simp [primitive, pure, Except.pure]
      · cases hl
    · cases hl
  · cases hl

/-- `params_nth(cs, i) = cs[i]`. -/
theorem nth_eval {nth : Sym} (hn : isParamsNthRec file nth = true) (tags : Mem.Concrete.Tags) :
    ∀ (cs : List Ctype) (i : Nat) (c : Ctype), cs[i]? = some c →
    ∀ {s : Sym}, s.key = nth.key → ∀ {env : Env} {ann : List Annot} {pc pi : PE},
    Eval file tags env (.inl pc) (.inl (ctypes cs)) →
    Eval file tags env (.inl pi) (.inl (.object (.integer i))) →
    Eval file tags env (.inl (.mk ann () (.call (.sym s) [pc, pi]))) (.inl (.ctype c)) := by
  unfold isParamsNthRec at hn
  split at hn
  · rename_i d hd
    unfold isNthRec at hn
    split at hn
    · rename_i rbt csS cbt nS nbt pann cann cs₁ nann na e0 ca xa x xbt xsa xs xsbt ia oa n1a n₁ za z
        x1a x₁ i2a o2a n2a n₂ z2a z' cla self₁ xs1a xs₁ suba n3a n₃ o3a o e2
      obtain ⟨hne, hcs, hn₁, rfl, hx, hnx, hnxs, hn₂, rfl, hself, hxs₁, hn₃, rfl, hxsx⟩ :=
        of_decide_eq_true hn
      let body : PE := .mk pann () (.case_ (.mk cann () (.sym cs₁))
        [(.mk nann (.ctor (.nil na) []), e0),
         (.mk ca (.ctor .cons [.mk xa (.base (some x, xbt)), .mk xsa (.base (some xs, xsbt))]),
          .mk ia () (.if_ (.mk oa () (.op .eq (.mk n1a () (.sym n₁)) (.mk za () (.val (.object (.integer 0))))))
            (.mk x1a () (.sym x₁))
            (.mk i2a () (.if_ (.mk o2a () (.op .gt (.mk n2a () (.sym n₂)) (.mk z2a () (.val (.object (.integer 0))))))
              (.mk cla () (.call (.sym self₁) [.mk xs1a () (.sym xs₁),
                .mk suba () (.op .sub (.mk n3a () (.sym n₃)) (.mk o3a () (.val (.object (.integer 1)))))]))
              e2))))])
      have key : ∀ (cs : List Ctype) (i : Nat) (c : Ctype), cs[i]? = some c →
          Eval file tags (extendEnv [(csS, ctypes cs), (nS, .object (.integer i))] ∅) (.inl body)
            (.inl (.ctype c)) := by
        intro cs
        induction cs with
        | nil => intro i c h; simp at h
        | cons c₀ cs ih =>
          intro i c h
          let env₀ : Env := extendEnv [(csS, ctypes (c₀ :: cs)), (nS, .object (.integer i))] ∅
          let env₁ : Env := extendEnv [(x, .ctype c₀), (xs, ctypes cs)] env₀
          have ln : ∀ {y : Sym}, y.key = nS.key → env₁.lookup y = some (.object (.integer i)) := by
            intro y hy
            rw [lookup_cons_ne (by rw [hy]; exact hnx), lookup_cons_ne (by rw [hy]; exact hnxs),
              lookup_nil]
            exact ConvInt.lookup_two_second hy (fun h => hne h.symm)
          refine .case_ (xs := [(x, .ctype c₀), (xs, ctypes cs)])
            (body := .mk ia () (.if_ (.mk oa () (.op .eq (.mk n1a () (.sym n₁))
              (.mk za () (.val (.object (.integer 0))))))
              (.mk x1a () (.sym x₁))
              (.mk i2a () (.if_ (.mk o2a () (.op .gt (.mk n2a () (.sym n₂))
                (.mk z2a () (.val (.object (.integer 0))))))
                (.mk cla () (.call (.sym self₁) [.mk xs1a () (.sym xs₁),
                  .mk suba () (.op .sub (.mk n3a () (.sym n₃)) (.mk o3a () (.val (.object (.integer 1)))))]))
                e2))))
            (.sym (ConvInt.lookup_two_first hcs))
            (by simp [selectCase, matchPattern, ctypes, bind, Option.bind]) ?_
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at h
            subst h
            refine .ifTrue (.op (vs := [.object (.integer 0), .object (.integer 0)])
              (.cons (.sym (by have h0 := ln hn₁; rw [Nat.cast_zero] at h0; exact h0)) (.cons .val .nil)) ?_) (.sym (lookup_cons_eq hx))
            simp [primitive, integerBin, boolean, pure, Except.pure]
          | succ j =>
            simp only [List.getElem?_cons_succ] at h
            refine .ifFalse (.op (vs := [.object (.integer (j + 1 : Nat)), .object (.integer 0)])
              (.cons (.sym (ln hn₁)) (.cons .val .nil)) ?_) ?_
            · simp [primitive, integerBin, boolean, pure, Except.pure]; omega
            refine .ifTrue (.op (vs := [.object (.integer (j + 1 : Nat)), .object (.integer 0)])
              (.cons (.sym (ln hn₂)) (.cons .val .nil)) ?_) ?_
            · simp [primitive, integerBin, boolean, pure, Except.pure]
            have hd₁ : lookupFun file self₁ = some _ := (lookupFun_key hself).trans hd
            refine .call (vs := [ctypes cs, .object (.integer j)])
              (.cons (.sym ?_) (.cons (.op (vs := [.object (.integer (j + 1 : Nat)), .object (.integer 1)])
                (.cons (.sym (ln hn₃)) (.cons .val .nil)) ?_) .nil))
              (ConvInt.functionBody_eq hd₁ rfl) (ih j c h)
            · rw [lookup_cons_ne (by rw [hxs₁]; exact hxsx)]
              exact lookup_cons_eq hxs₁
            · simp [primitive, integerBin, integer, pure, Except.pure]
      intro cs i c h s hs env ann pc pi hc hi
      have hds : lookupFun file s = some _ := (lookupFun_key hs).trans hd
      exact .call (.cons hc (.cons hi .nil)) (ConvInt.functionBody_eq hds rfl) (key cs i c h)
    · cases hn
  · cases hn

end Silmaril.Compile.Core.Verified.CallManyEval
