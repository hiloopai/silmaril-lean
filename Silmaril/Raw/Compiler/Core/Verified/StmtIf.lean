module

public import Silmaril.Compiler.Core.Verified.LocalExpr.Defs
public import Silmaril.Cerberus.Core.SeqReach.Defs

/-! # The boolean conversion of a C `if` statement

Cerberus first computes `e == 0` as a loaded integer, then converts that result to the
Core boolean `!(z == 1)`. This module recognizes the conversion and proves its run over
arbitrary environments, memories and continuations. `choose` represents the same branch
selection in the existing runtime integer-expression compiler.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StmtIf

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff)
open IntExpr (Term)

/-- The loaded test result is converted to a Core boolean. The `Unspecified` arm is
unconstrained here: the expression fragment produces `Specified` or reaches UB. -/
def boolSource (c : Sym) : Eff → Bool
  | .mk _ (.case_ (.mk _ () (.sym c'))
      [(.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
        .mk _ (.pure (.mk _ () (.if_ (.mk _ () (.not (.mk _ () (.op .eq
          (.mk _ () (.sym z')) (.mk _ () (.val (.object (.integer 1))))))))
          (.mk _ () (.val .true)) (.mk _ () (.val .false)))))),
       (.mk _ (.ctor .unspecified [_]), _)]) => c'.key = c.key && z'.key = z.key
  | _ => false

/-- Syntax without saved labels, including the branching glue of a C `if`.
`nd` is ignored by the dynamics' label collection, as are bounded expressions. -/
def labelFree : Eff → Bool
  | .mk _ (.sseq _ a b) | .mk _ (.wseq _ a b) | .mk _ (.if_ _ a b) =>
      labelFree a && labelFree b
  | .mk _ (.case_ _ [(_, a), (_, b)]) => labelFree a && labelFree b
  | .mk _ (.nd _) => true
  | e => ReturnLit.saveFree e
termination_by e => sizeOf e

theorem labelFree_saves (e : EE) (h : labelFree e = true) : saves e = [] := by
  unfold labelFree at h
  split at h
  · rename_i ann p a b
    simp only [Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simp [saves, labelFree_saves a ha, labelFree_saves b hb]
  · rename_i ann p a b
    simp only [Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simp [saves, labelFree_saves a ha, labelFree_saves b hb]
  · rename_i ann p a b
    simp only [Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simp [saves, labelFree_saves a ha, labelFree_saves b hb]
  · rename_i ann p pa a pb b
    simp only [Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simp [saves, savesCases, labelFree_saves a ha, labelFree_saves b hb]
  · simp [saves]
  · exact ReturnLit.saves_saveFree e h
termination_by sizeOf e

/-- Branch selection computed at run time with the existing comparison and conditional code. -/
def choose (c a b : Term) : Term := .cond (.cmp .eq 1 0 c (.lit 1)) a b

@[simp] theorem choose_val (c a b : Term) (n : Int) :
    (choose c a b).val n = if c.val n = 1 then b.val n else a.val n := by
  by_cases h : c.val n = 1 <;>
    simp [choose, Term.val, Guard.compare, Guard.holds, h]

@[simp] theorem choose_ok (c a b : Term) (n : Int) :
    (choose c a b).Ok n ↔ c.Ok n ∧ if c.val n = 1 then b.Ok n else a.Ok n := by
  have h0 : ConvInt.IsInt 0 := by constructor <;> omega
  have h1 : ConvInt.IsInt 1 := by constructor <;> omega
  by_cases h : c.val n = 1 <;>
    simp [choose, Term.Ok, Term.val, Guard.compare, Guard.holds, h, h0, h1]

variable {file : Program} {labels : Labels}

/-- The recognized conversion evaluates to `false` exactly when the test result is 1. -/
theorem boolSource_reaches {c : Sym} {e : Eff} (h : boolSource c e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (v : Int)
    (hc : env.lookup c = some (IntExpr.spec v)) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (boolean (decide (v ≠ 1))), k, m'⟩ := by
  unfold boolSource at h
  split at h
  · rename_i ann pa c' sa spa z ty ea pif pn pe pz z' pv pt pf ua up un
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hc', hz'⟩ := h
    let env' := extendEnv [(z, (.object (.integer v) : Val))] env
    have hsym : env.lookup c' = some (IntExpr.spec v) := by
      rw [ReturnLit.lookup_key hc']; exact hc
    have hs : SeqReach.PureEval file labels (.mk pa () (.sym c')) env (IntExpr.spec v) :=
      SeqReach.pure_symbol pa c' env _ hsym
    let P : PE := .mk pif () (.if_ (.mk pn () (.not (.mk pe () (.op .eq
      (.mk pz () (.sym z')) (.mk pv () (.val (.object (.integer 1))))))))
      (.mk pt () (.val .true)) (.mk pf () (.val .false)))
    have pre := SeqReach.specified_case_reaches (file := file) (labels := labels)
      ann sa ua (.mk spa (.base (some z, ty))) up (yes := .mk ea (.pure P)) (no := un) hs
      (show matchPattern (.mk spa (.base (some z, ty))) (.object (.integer v)) =
        some [(z, .object (.integer v))] from rfl) k m
    have ev (tags : Mem.Concrete.Tags) : Eval file tags env' (.inl P)
        (.inl (boolean (decide (v ≠ 1)))) := by
      have eq : Eval file tags env'
          (.inl (.mk pe () (.op .eq (.mk pz () (.sym z'))
            (.mk pv () (.val (.object (.integer 1)))))))
          (.inl (boolean (v == 1))) :=
        .op (.cons (.sym (ConvInt.lookup_one hz')) (.cons .val .nil))
          (by simp [primitive, integerBin, runtimeValue, runtimeObject]; rfl)
      have ne : Eval file tags env'
          (.inl (.mk pn () (.not (.mk pe () (.op .eq (.mk pz () (.sym z'))
            (.mk pv () (.val (.object (.integer 1)))))))))
          (.inl (boolean (decide (v ≠ 1)))) := by
        apply Eval.not (.cons eq .nil)
        by_cases hv : v = 1 <;> simp [primitive, hv, boolean] <;> rfl
      by_cases hv : v = 1
      · exact .ifFalse (by simpa [hv, boolean] using ne) (by simpa [hv, boolean, runtimeValue] using
          (Eval.val (file := file) (tags := tags) (env := env') (ann := pf) (v := .false)))
      · exact .ifTrue (by simpa [hv, boolean] using ne) (by simpa [hv, boolean, runtimeValue] using
          (Eval.val (file := file) (tags := tags) (env := env') (ann := pt) (v := .true)))
    have hp : SeqReach.PureEval file labels P env' (boolean (decide (v ≠ 1))) := by
      intro k' m'
      exact (Eval.sound file (tagsOf file m') (ev _)) labels k' m' rfl
    refine ⟨SeqReach.focusMemory ea (SeqReach.focusMemory ann m), by simp, pre.trans ?_⟩
    exact SeqReach.effect_pure_reaches ea hp k _
  · cases h

end Silmaril.Compile.Core.Verified.StmtIf
