module

public import Silmaril.Compiler.Core.Verified.LoopCondition.Defs

/-! # The direct loaded condition of a `do` loop

Unlike the `while` elaboration, a `do` loop branches directly on a specified
integer's comparison with zero. The successors remain effectful syntax. This
boundary preserves locals, enters only the selected successor, and matches an
ordinary runtime Lir branch on the current value.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.DoCondition

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open StateExpr (Key Term term values)
open StateMem (Local Inv Defined defsOf)
open StateStmt
open StateLoopStep (Layout Registers)
open PureEval (Reaches Eval)

/-- The specified arm's direct `z != 0` test. Its other arm is unreachable for
our defined expression fragment, but is retained in the source syntax. -/
def branch (c : Sym) : EE → Option (Sym × EE × EE)
  | .mk _ (.case_ (.mk _ () (.sym c'))
      [(.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
        .mk _ (.if_ (.mk _ () (.not (.mk _ () (.op .eq
          (.mk _ () (.sym z')) (.mk _ () (.val (.object (.integer 0)))))))) yes no)),
       (.mk _ (.ctor .unspecified [_]), _)]) =>
      if c'.key = c.key ∧ z'.key = z.key then some (z, yes, no) else none
  | _ => none

/-- Recognise the bound expression and its direct conditional continuation.
The two temporaries must be fresh for every local object pointer. -/
def recognize (file : File Codec.wireModel Unit Unit) (xs : List Sym) :
    EE → Option (Term × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec)) rest) => do
      let (z, yes, no) ← branch c rest
      if isFresh xs c = true ∧ isFresh xs z = true then
        return (← term file ec, yes, no)
      else none
  | _ => none

/-- The two temporaries a `do` test binds. -/
def binders : EE → List Sym
  | .mk _ (.sseq (.mk _ (.base (some c, _))) _ rest) =>
    c :: match branch c rest with
      | some (z, _, _) => [z]
      | none => []
  | _ => []

variable {file : Program} {labels : Labels}

/-- Direct branch selection, with the exact environment extension and memory
focus. This lemma also covers negative nonzero integers. -/
theorem branch_runs {c z : Sym} {e yes no : EE}
    (shape : branch c e = some (z, yes, no))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (v : Int)
    (hc : env.lookup c = some (IntExpr.spec v)) :
    ∃ m', LoadTask.Touched m m' ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr (if v = 0 then no else yes)
          (extendEnv [(z, .object (.integer v))] env), k, m'⟩ := by
  unfold branch at shape
  split at shape
  · rename_i ann pa c' sa spa zz ty ea pn pe pz z' pv yes' no' ua up un
    split at shape
    · rename_i checks
      obtain ⟨hcc, hzz⟩ := checks
      simp only [Option.some.injEq, Prod.mk.injEq] at shape
      obtain ⟨hz, hy, hn⟩ := shape
      subst zz yes' no'
      let env' := extendEnv [(z, (.object (.integer v) : Val))] env
      have hs : SeqReach.PureEval file labels (.mk pa () (.sym c')) env (IntExpr.spec v) :=
        SeqReach.pure_symbol pa c' env _ (by rw [ReturnLit.lookup_key hcc]; exact hc)
      let test : PE := .mk pn () (.not (.mk pe () (.op .eq (.mk pz () (.sym z'))
        (.mk pv () (.val (.object (.integer 0)))))))
      have pre := SeqReach.specified_case_reaches (file := file) (labels := labels)
        ann sa ua (.mk spa (.base (some z, ty))) up
        (yes := .mk ea (.if_ test yes no)) (no := un) hs
        (show matchPattern (.mk spa (.base (some z, ty))) (.object (.integer v)) =
          some [(z, .object (.integer v))] from rfl) k m
      have hp : SeqReach.PureEval file labels test env' (boolean (decide (v ≠ 0))) := by
        intro k' m'
        have eq : Eval file (PureEval.tagsOf file m') env'
            (.inl (.mk pe () (.op .eq (.mk pz () (.sym z'))
              (.mk pv () (.val (.object (.integer 0)))))))
            (.inl (boolean (v == 0))) :=
          .op (.cons (.sym (ConvInt.lookup_one hzz)) (.cons .val .nil))
            (by simp [primitive, integerBin, runtimeValue, runtimeObject]; rfl)
        have ne : Eval file (PureEval.tagsOf file m') env'
            (.inl (.mk pn () (.not (.mk pe () (.op .eq (.mk pz () (.sym z'))
              (.mk pv () (.val (.object (.integer 0)))))))))
            (.inl (boolean (decide (v ≠ 0)))) := by
          apply Eval.not (.cons eq .nil)
          by_cases hv : v = 0 <;> simp [primitive, hv, boolean] <;> rfl
        exact (Eval.sound file _ ne) labels k' m' rfl
      have selected := pre.trans (SeqReach.effect_if_reaches ea (decide (v ≠ 0)) hp k _)
      have select : (if decide (v ≠ 0) then yes else no) = (if v = 0 then no else yes) := by
        by_cases h : v = 0 <;> simp [h]
      rw [select] at selected
      exact ⟨_, (seqFocus_touched ann m).trans (seqFocus_touched ea _), selected⟩
    · cases shape
  · cases shape

/-- A direct condition runs to precisely one successor; the loaded test may
instead reach integer UB. No compile-time execution is involved. -/
theorem runs {xs : List Sym} {e yes no : EE} {t : Term}
    (shape : recognize file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ env' m',
        LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧
        (∀ y : Sym, (∀ z ∈ binders e, z.key ≠ y.key) → env'.lookup y = env.lookup y) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 0 then no else yes) env', k, m'⟩ := by
  unfold recognize at shape
  split at shape
  · rename_i ann pann c ty bann ec rest
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at shape
    obtain ⟨⟨z, yes', no'⟩, hb, hs⟩ := shape
    split at hs
    · rename_i fresh
      simp only [Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq,
        Prod.mk.injEq] at hs
      obtain ⟨t', ht, ht', hy, hn⟩ := hs
      subst t' yes' no'
      let K := Frame.strongBind (.mk pann (.base (some c, ty))) rest env :: k
      have pre := (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
        (ReturnLit.bound_reaches bann ec env K m)
      by_cases ok : t.Ok (values (defsOf ds))
      · obtain ⟨as, m₁, fr, hfr, _, touch, run⟩ := StateExpr.term_runs
          (file := file) (labels := labels) t ht ok (.bound :: K) m (inv.locs defined)
        have next := (Interleave.reaches_of_local file labels run).trans
          ((bound_pop hfr _ K m₁).trans (ReturnLit.bind_reaches pann c ty _ rest env k m₁))
        obtain ⟨m₂, touch₂, select⟩ := branch_runs hb
          (extendEnv [(c, IntExpr.spec (t.val (values (defsOf ds))))] env) k m₁ _
          (ConvInt.lookup_one rfl)
        have touched := touch.trans touch₂
        refine .inr ⟨ok, _, m₂, touched,
          ((inv.touched touched).extend (keys.fresh fresh.1)).extend (keys.fresh fresh.2),
          fun y hy => ?_, pre.trans (next.trans select)⟩
        have h1 : y.key ≠ c.key := fun h => hy c (by simp [binders]) h.symm
        have h2 : y.key ≠ z.key := fun h => hy z (by simp [binders, hb]) h.symm
        rw [ConvInt.lookup_one_other h2, ConvInt.lookup_one_other h1]
      · exact .inl (Overflows.pre pre (fails_overflows (StateExpr.term_fails
          (file := file) (labels := labels) t ht ok (.bound :: K) m (inv.locs defined))))
    · cases hs
  · cases shape

/-- The ordinary runtime branch implements the direct Core test. Both paths
are nonempty on the target, and locals, linear memory and caller stack survive. -/
theorem test_step {xs : List Sym} {e yes no : EE} {t : Term}
    (shape : recognize file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label yesLabel noLabel : Lir.Label)
    (block : p.block? f label = some (LoopBlocks.testBlock regs d t yesLabel noLabel))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ env' m' fr', m'.stdout = m.stdout ∧ Inv env' m' ls ds ∧ Registers regs ds fr' ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 0 then no else yes) env', k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, if t.val (values (defsOf ds)) = 0 then noLabel else yesLabel, 0⟩, fr', stack, mem⟩ := by
  rcases runs shape inv keys defined k with ub | ⟨ok, env', m', touched, inv', -, source⟩
  · exact .inl ub
  · obtain ⟨fr', target, below⟩ := LoopBlocks.test_steps regs (values (defsOf ds)) d t
      yesLabel noLabel p f label block fr stack mem ok (StateLoopStep.reads layout inv matched defined)
    refine .inr ⟨env', m', fr', touched.stdout, inv', ?_, source, target⟩
    intro q a ha
    obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
    rw [below _ (by rw [← hk]; exact layout.below l hl)]
    exact matched q a ha

end Silmaril.Compile.Core.Verified.DoCondition
