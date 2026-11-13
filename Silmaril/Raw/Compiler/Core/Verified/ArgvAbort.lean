module

public import Silmaril.Compiler.Core.Verified.ArgvExpr.Defs
public import Silmaril.Compiler.Core.Verified.AbortCall.Defs
public import Silmaril.Compiler.Core.Verified.StmtIf.Defs
public import Silmaril.Compiler.Core.Verified.StateStmt.Defs
public import Silmaril.Compiler.Core.Verified.Argc.Defs

/-! # `main(argc, argv)`: `if (c) abort(); return e;` over one character of the arguments

`recognize doc = some P`: the file has no global definitions, `main` takes `argc` and `argv`
(normal calling convention), and its body is the block

```
if (c) abort();
return e;
```

where `c` and `e` are `int` expressions over literals and one character `argv[i][0]`, `i ≤ 1`
(`ArgvExpr.term`; `P.ij = (i, 0)`). Since `argc ≥ 1`, `argv[i]` is a string or (for `i = argc = 1`)
the null slot, whose shift is undefined behaviour; its first character is always within the string
(the terminator for an empty one), so every argument vector is covered.

`recognize_sound`: for every `ArgsOk` argument vector, with `ch = charOfArgs args i 0`, Core reaches
undefined behaviour, or the test is in range and either is not `1` (the C condition holds: the
program aborts with no output) or is `1` and the return expression is in range (the program exits
with its value). The compiled code (`ArgvAbortLink`) reads the same character from the argument
block and computes both expressions at run time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvAbort

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ReturnLit (Eff)
open IntExpr (Term)
open Silmaril.Cerberus.Core.PureEval (Reaches)

/-- The compiled plan: the character's indices, the test (`c == 0`) and the return expression. -/
structure Plan where
  ij : Nat × Nat
  test : Term
  ret : Term

/-- `pure(unit)`. -/
def isUnit : Eff → Bool
  | .mk _ (.pure (.mk _ () (.val .unit))) => true
  | _ => false

/-- `if (c) abort();`: `let strong c = bound(ec) in let strong b = <c as a boolean> in
if b then abort(); else pure(unit)`; the test `c == 0` over the character. -/
def ifAbort (file : File Codec.wireModel Unit Unit) (argv : Sym) (ij : Nat × Nat) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb (.mk _ (.if_ (.mk _ () (.sym b')) ea eb))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ AbortCall.abortStmt file ea = true ∧
          isUnit eb = true ∧ c.key ≠ argv.key ∧ b.key ≠ argv.key then ArgvExpr.term file argv ij ec
      else none
  | _ => none

/-- `return e;`: `let strong u = bound(e) in run ret(conv_loaded_int(int, u))`. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret argv : Sym) (ij : Nat × Nat) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ ConvInt.isConvLoadedInt file s = true then
        ArgvExpr.term file argv ij e
      else none
  | _ => none

/-- The block `{ s₁ s₂ }`: its two statements. -/
def blockParts : Eff → Option (Eff × Eff)
  | .mk _ (.sseq (.mk _ (.base (none, _))) s₁ (.mk _ (.sseq (.mk _ (.base (none, _))) s₂ _))) =>
      some (s₁, s₂)
  | _ => none

/-- The body: `{ if (c) abort(); return e; }`, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (argv : Sym) (ij : Nat × Nat) :
    Eff → Option Plan
  | .mk _ (.sseq (.mk _ (.base (none, _))) blk
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree blk = true then
        match blockParts blk with
        | some (s₁, s₂) =>
          match ifAbort file argv ij s₁, retStmt file ret argv ij s₂ with
          | some tc, some te => some ⟨ij, tc, te⟩
          | _, _ => none
        | none => none
      else none
  | _ => none

/-- No global definitions, `main(argc, argv)` with the normal calling convention, and a body
recognised for `argv[1][0]` or `argv[0][0]`. -/
def recognize (doc : Codec.Document) : Option Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    if doc.file.callingConvention = .normal then do
      let s ← doc.file.main
      let .procedure _ _ _ [(argc, _), (argv, _)] body ← doc.file.funs.lookup s | none
      if argc.key ≠ argv.key then
        (recognizeBody doc.file argv (1, 0) body).orElse fun _ => recognizeBody doc.file argv (0, 0) body
      else none
    else none

/-! ## Inversions -/

theorem ifAbort_inv {file : File Codec.wireModel Unit Unit} {argv : Sym} {ij : Nat × Nat} {e : Eff}
    {t : Term} (h : ifAbort file argv ij e = some t) :
    ∃ (a0 a1 : List Annot) (c : Sym) (tc : BaseType) (a2 : List Annot) (ec : Eff) (a3 a4 : List Annot)
      (b : Sym) (tb : BaseType) (cb : Eff) (a5 a6 : List Annot) (b' : Sym) (ea eb : Eff),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, tc))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, tb))) cb (.mk a5 (.if_ (.mk a6 () (.sym b')) ea eb))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ AbortCall.abortStmt file ea = true ∧
      isUnit eb = true ∧ ArgvExpr.term file argv ij ec = some t := by
  unfold ifAbort at h
  split at h
  · split at h
    · rename_i hc
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, h⟩
    · cases h
  · cases h

theorem retStmt_inv {file : File Codec.wireModel Unit Unit} {ret argv : Sym} {ij : Nat × Nat} {e : Eff}
    {t : Term} (h : retStmt file ret argv ij e = some t) :
    ∃ (a0 a1 : List Annot) (u : Sym) (tu : BaseType) (a2 : List Annot) (ex : Eff) (a3 : List Annot)
      (l : Sym) (a4 a5 a6 : List Annot) (s : Sym) (a7 : List Annot) (u' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some u, tu))) (.mk a2 (.bound ex))
        (.mk a3 (.run () l [.mk a4 () (.call (.sym s)
          [.mk a5 () (.val (.ctype (.mk a6 (.basic (.integer (.signed .int)))))), .mk a7 () (.sym u')])]))) ∧
      l.key = ret.key ∧ u'.key = u.key ∧ ConvInt.isConvLoadedInt file s = true ∧
      ArgvExpr.term file argv ij ex = some t := by
  unfold retStmt at h
  split at h
  · split at h
    · rename_i hc
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2, h⟩
    · cases h
  · cases h

theorem blockParts_inv {e s₁ s₂ : Eff} (h : blockParts e = some (s₁, s₂)) :
    ∃ (a0 a1 : List Annot) (t1 : BaseType) (a2 a3 : List Annot) (t2 : BaseType) (rest : Eff),
      e = .mk a0 (.sseq (.mk a1 (.base (none, t1))) s₁ (.mk a2 (.sseq (.mk a3 (.base (none, t2))) s₂ rest))) := by
  unfold blockParts at h
  split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, rfl⟩
  · cases h

theorem recognizeBody_inv {file : File Codec.wireModel Unit Unit} {argv : Sym} {ij : Nat × Nat} {body : Eff}
    {P : Plan} (h : recognizeBody file argv ij body = some P) :
    ∃ (a0 a1 : List Annot) (t0 : BaseType) (blk : Eff) (sa : List Annot) (ret : Sym) (bt : BaseType) (r : Sym)
      (info : (BaseType × Option (Ctype × PassBy)) × PE) (ba pa : List Annot) (r' : Sym) (s₁ s₂ : Eff),
      body = .mk a0 (.sseq (.mk a1 (.base (none, t0))) blk
        (.mk sa (.save (ret, bt) [(r, info)] (.mk ba (.pure (.mk pa () (.sym r'))))))) ∧
      r'.key = r.key ∧ StmtIf.labelFree blk = true ∧ blockParts blk = some (s₁, s₂) ∧
      ifAbort file argv ij s₁ = some P.test ∧ retStmt file ret argv ij s₂ = some P.ret ∧ P.ij = ij := by
  unfold recognizeBody at h
  split at h
  · split at h
    · rename_i hc
      split at h
      · rename_i s₁ s₂ hb
        split at h
        · rename_i tc te h1 h2
          cases h
          exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2, hb, h1, h2, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## Runs -/

variable {file : Program} {labels : Labels}

/-- An `Ev` run from a top-level state: to the value over at most one annotation frame, or to
undefined behaviour. -/
theorem ev_reaches {I : Mem.Concrete.State → Prop} {env : Env} {e : EE} {v : Val}
    (h : ArgvChar.Ev (file := file) (labels := labels) I env e v) (k : List Frame) (m : Mem.Concrete.State)
    (hm : I m) :
    (∃ xs m' fr, Cond.OneAnn fr xs ∧ ArgvMem.Reads m m' ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value v, fr ++ k, m'⟩) ∨
    ∃ t loc ub, Reaches file labels ⟨.effectExpr e env, k, m⟩ t ∧ t.control = .halt (.ub loc ub) := by
  rcases h.2 k m hm with ⟨xs, m', fr, hfr, -, g, run⟩ | ⟨loc, ub, f⟩
  · exact .inl ⟨xs, m', fr, hfr, g, Interleave.reaches_of_local file labels run⟩
  · obtain ⟨t, reach, halt⟩ := ArenaFail.fail_reaches file labels f
    exact .inr ⟨t, loc, ub, reach, halt⟩

theorem bad_reaches {I : Mem.Concrete.State → Prop} {env : Env} {e : EE}
    (h : ArgvChar.Bad (file := file) (labels := labels) I env e) (k : List Frame) (m : Mem.Concrete.State)
    (hm : I m) :
    ∃ t loc ub, Reaches file labels ⟨.effectExpr e env, k, m⟩ t ∧ t.control = .halt (.ub loc ub) := by
  obtain ⟨loc, ub, f⟩ := h.2 k m hm
  obtain ⟨t, reach, halt⟩ := ArenaFail.fail_reaches file labels f
  exact ⟨t, loc, ub, reach, halt⟩

theorem pop_bound {fr : List Frame} {xs : List Access} (hfr : Cond.OneAnn fr xs) (v : Val) (k : List Frame)
    (m : Mem.Concrete.State) : Reaches file labels ⟨.value v, fr ++ .bound :: k, m⟩ ⟨.value v, k, m⟩ := by
  rcases hfr with ⟨rfl, -⟩ | rfl
  · exact LocalExpr.value_bound_reaches v k m
  · exact Locals.annotations_bound_reaches xs v k m

/-- What a run of the block shows: undefined behaviour, the abort (the test is not `1`), or the
return of the expression's value (the test is `1`), with the output unchanged. -/
def Ends (s : State) (P : Plan) (ch : Int) : Prop :=
  (∃ t loc ub, Reaches file labels s t ∧ t.control = .halt (.ub loc ub)) ∨
  (P.test.Ok ch ∧ P.test.val ch ≠ 1 ∧ ∃ t, Reaches file labels s t ∧ t.control = .halt .aborted ∧
    t.memory.stdout = s.memory.stdout) ∨
  (P.test.Ok ch ∧ P.test.val ch = 1 ∧ P.ret.Ok ch ∧ ∃ t, Reaches file labels s t ∧
    t.control = .halt (.defined (IntExpr.spec (P.ret.val ch))) ∧ t.memory.stdout = s.memory.stdout)

theorem Ends.pre {s s' : State} {P : Plan} {ch : Int} (r : Reaches file labels s s')
    (out : s'.memory.stdout = s.memory.stdout) (h : Ends (file := file) (labels := labels) s' P ch) :
    Ends (file := file) (labels := labels) s P ch := by
  rcases h with ⟨t, loc, ub, r', halt⟩ | ⟨ok, ne, t, r', halt, o⟩ | ⟨ok, eq, okr, t, r', halt, o⟩
  · exact .inl ⟨t, loc, ub, r.trans r', halt⟩
  · exact .inr (.inl ⟨ok, ne, t, r.trans r', halt, o.trans out⟩)
  · exact .inr (.inr ⟨ok, eq, okr, t, r.trans r', halt, o.trans out⟩)

theorem ub_ends {s : State} {P : Plan} {ch : Int}
    (h : ∃ t loc ub, Reaches file labels s t ∧ t.control = .halt (.ub loc ub)) :
    Ends (file := file) (labels := labels) s P ch := .inl h

theorem isUnit_inv {e : Eff} (h : isUnit e = true) :
    ∃ ann pann, e = .mk ann (.pure (.mk pann () (.val .unit))) := by
  unfold isUnit at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

/-- The runs an expression over the character has, in range and out of range. -/
def TermRuns (I : Mem.Concrete.State → Prop) (argv : Sym) (ij : Nat × Nat) (env : Env) (ch : Int) : Prop :=
  ∀ t ex, ArgvExpr.term file argv ij ex = some t →
    (t.Ok ch → ArgvChar.Ev (file := file) (labels := labels) I env ex (IntExpr.spec (t.val ch))) ∧
    (¬ t.Ok ch → ArgvChar.Bad (file := file) (labels := labels) I env ex)

/-- **`if (c) abort();`**: undefined behaviour, the abort when the test is not `1`, or the next
statement when it is, in a memory that still satisfies `I`. -/
theorem if_ends {argv : Sym} {ij : Nat × Nat} {e : Eff} {tc : Term} (h : ifAbort file argv ij e = some tc)
    {I : Mem.Concrete.State → Prop} (hI : ArgvChar.Stable I) {env : Env} {ch : Int}
    (hev : TermRuns (file := file) (labels := labels) I argv ij env ch) (k : List Frame)
    (m : Mem.Concrete.State) (hm : I m) :
    (∃ t loc ub, Reaches file labels ⟨.effectExpr e env, k, m⟩ t ∧ t.control = .halt (.ub loc ub)) ∨
    (tc.Ok ch ∧ tc.val ch ≠ 1 ∧ ∃ t, Reaches file labels ⟨.effectExpr e env, k, m⟩ t ∧
      t.control = .halt .aborted ∧ t.memory.stdout = m.stdout) ∨
    (tc.Ok ch ∧ tc.val ch = 1 ∧ ∃ m', I m' ∧ m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩) := by
  obtain ⟨a0, a1, c, tc', a2, ec, a3, a4, b, tb, cb, a5, a6, b', ea, eb, rfl, hb', hcb, hab, hunit, hterm⟩ :=
    ifAbort_inv h
  let IFE : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea eb)
  let R : EE := .mk a3 (.sseq (.mk a4 (.base (some b, tb))) cb IFE)
  let KC : List Frame := .strongBind (.mk a1 (.base (some c, tc'))) R env :: k
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, tc'))) (.mk a2 (.bound ec)) R))
      env, k, m⟩ ⟨.effectExpr ec env, .bound :: KC, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans (ReturnLit.bound_reaches a2 _ env _ m)
  obtain ⟨hok, hbad⟩ := hev tc ec hterm
  by_cases ok : tc.Ok ch
  · rcases ev_reaches (hok ok) (.bound :: KC) m hm with ⟨xs, m₁, fr, hfr, g₁, run⟩ | ⟨t, loc, ub, r, halt⟩
    · let v := tc.val ch
      let env₁ := extendEnv [(c, IntExpr.spec v)] env
      obtain ⟨m₂, tch₂, conv⟩ := StateStmt.boolSource_touched (file := file) (labels := labels) hcb env₁
        (.strongBind (.mk a4 (.base (some b, tb))) IFE env₁ :: k) m₁ v (ConvInt.lookup_one rfl)
      let flag := decide (v ≠ 1)
      let env₂ := extendEnv [(b, boolean flag)] env₁
      have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
        SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
      let m₃ := SeqReach.focusMemory a5 m₂
      have g₃ : ArgvMem.Reads m m₃ :=
        g₁.trans (ArgvMem.Reads.of_touched (tch₂.trans (StateStmt.seqFocus_touched a5 m₂)))
      have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: KC, m⟩
          ⟨.effectExpr (if flag then ea else eb) env₂, k, m₃⟩ :=
        run.trans ((pop_bound hfr _ KC m₁).trans ((ReturnLit.bind_reaches a1 c tc' _ R env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IFE env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b tb _ IFE env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
      by_cases h1 : v = 1
      · have hf : flag = false := by simp [flag, h1]
        rw [hf] at enter
        obtain ⟨ann, pann, rfl⟩ := isUnit_inv hunit
        have fin := SeqReach.effect_pure_reaches (file := file) (labels := labels) ann
          (SeqReach.pure_value pann .unit env₂) k m₃
        refine .inr (.inr ⟨ok, h1, _, hI m _ hm (g₃.focus ann), ?_, pre.trans (enter.trans fin)⟩)
        exact (g₃.focus ann).stdout
      · have hf : flag = true := by simp [flag, h1]
        rw [hf] at enter
        obtain ⟨m₄, ab, out⟩ := AbortCall.abortStmt_reaches hab env₂ k m₃
        exact .inr (.inl ⟨ok, h1, _, pre.trans (enter.trans ab), rfl, out.trans g₃.stdout⟩)
    · exact .inl ⟨t, loc, ub, pre.trans r, halt⟩
  · obtain ⟨t, loc, ub, r, halt⟩ := bad_reaches (hbad ok) (.bound :: KC) m hm
    exact .inl ⟨t, loc, ub, pre.trans r, halt⟩

/-- **`return e;`**: undefined behaviour, or `main` returns the expression's value. -/
theorem ret_ends {ret argv : Sym} {ij : Nat × Nat} {e : Eff} {te : Term}
    (h : retStmt file ret argv ij e = some te) (hret : ReturnLit.ReturnLabel labels ret)
    {I : Mem.Concrete.State → Prop} {env : Env} {ch : Int}
    (hev : TermRuns (file := file) (labels := labels) I argv ij env ch) {k : List Frame}
    (hk : ReturnLit.NoBoundary k) (m : Mem.Concrete.State) (hm : I m) :
    (∃ t loc ub, Reaches file labels ⟨.effectExpr e env, k, m⟩ t ∧ t.control = .halt (.ub loc ub)) ∨
    (te.Ok ch ∧ ∃ t, Reaches file labels ⟨.effectExpr e env, k, m⟩ t ∧
      t.control = .halt (.defined (IntExpr.spec (te.val ch))) ∧ t.memory.stdout = m.stdout) := by
  obtain ⟨a0, a1, u, tu, a2, ex, a3, l, a4, a5, a6, s, a7, u', rfl, hl, hu, hs, hterm⟩ := retStmt_inv h
  let CALL : PE := .mk a4 () (.call (.sym s)
    [.mk a5 () (.val (.ctype (.mk a6 (.basic (.integer (.signed .int)))))), .mk a7 () (.sym u')])
  let R : EE := .mk a3 (.run () l [CALL])
  let kR := Frame.strongBind (.mk a1 (.base (some u, tu))) R env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some u, tu))) (.mk a2 (.bound ex)) R)) env, k, m⟩
      ⟨.effectExpr ex env, .bound :: kR, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans (ReturnLit.bound_reaches a2 _ env _ m)
  obtain ⟨hok, hbad⟩ := hev te ex hterm
  by_cases ok : te.Ok ch
  · rcases ev_reaches (hok ok) (.bound :: kR) m hm with ⟨xs, m₁, fr, hfr, g₁, run⟩ | ⟨t, loc, ub, r, halt⟩
    · let v : Val := IntExpr.spec (te.val ch)
      let env₁ := extendEnv [(u, v)] env
      have heval : PureEval.Eval file (PureEval.tagsOf file (ReturnConst.focusMemory a3 m₁)) env₁
          (.inl CALL) (.inl v) :=
        ConvInt.convLoadedInt_eval (ann := a6) hs (Term.int_of_ok te ok)
          (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
      obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk (ReturnConst.focusMemory a3 m₁)
      refine .inr ⟨ok, _, pre.trans (run.trans ((pop_bound hfr v kR m₁).trans
        ((ReturnLit.bind_reaches a1 u tu v R env k m₁).trans
          ((Straight.focus_reaches (m := m₁) Straight.request_run).trans
            (((PureEval.Eval.sound file _ heval) labels _ _ rfl).trans halts))))), rfl, ?_⟩
      rw [out, ReturnConst.focusMemory_stdout]
      exact g₁.stdout
    · exact .inl ⟨t, loc, ub, pre.trans r, halt⟩
  · obtain ⟨t, loc, ub, r, halt⟩ := bad_reaches (hbad ok) (.bound :: kR) m hm
    exact .inl ⟨t, loc, ub, pre.trans r, halt⟩

/-- **The block** `{ if (c) abort(); return e; }`. -/
theorem block_ends {ret argv : Sym} {ij : Nat × Nat} {blk s₁ s₂ : Eff} {P : Plan}
    (hb : blockParts blk = some (s₁, s₂)) (h₁ : ifAbort file argv ij s₁ = some P.test)
    (h₂ : retStmt file ret argv ij s₂ = some P.ret) (hret : ReturnLit.ReturnLabel labels ret)
    {I : Mem.Concrete.State → Prop} (hI : ArgvChar.Stable I) {env : Env} {ch : Int}
    (hev : TermRuns (file := file) (labels := labels) I argv ij env ch) {k : List Frame}
    (hk : ReturnLit.NoBoundary k) (m : Mem.Concrete.State) (hm : I m) :
    Ends (file := file) (labels := labels) ⟨.effectExpr blk env, k, m⟩ P ch := by
  obtain ⟨a0, a1, t1, a2, a3, t2, rest, rfl⟩ := blockParts_inv hb
  let REST : EE := .mk a2 (.sseq (.mk a3 (.base (none, t2))) s₂ rest)
  have pre := ReturnConst.sequence_reaches file labels a0 (.mk a1 (.base (none, t1))) s₁ REST env k m
  rcases if_ends h₁ hI hev (.strongBind (.mk a1 (.base (none, t1))) REST env :: k) m hm with
    ⟨t, loc, ub, r, halt⟩ | ⟨ok, ne, t, r, halt, out⟩ | ⟨ok, eq, m₁, hm₁, out₁, r⟩
  · exact .inl ⟨t, loc, ub, pre.trans r, halt⟩
  · exact .inr (.inl ⟨ok, ne, t, pre.trans r, halt, out⟩)
  · have s₃ : Reaches file labels ⟨.value .unit, .strongBind (.mk a1 (.base (none, t1))) REST env :: k, m₁⟩
        ⟨.effectExpr s₂ env, .strongBind (.mk a3 (.base (none, t2))) rest env :: k, m₁⟩ :=
      (SeqReach.strong_bind_reaches (xs := []) (by simp [matchPattern]) k m₁).trans
        (ReturnConst.sequence_reaches file labels a2 _ s₂ rest env k m₁)
    rcases ret_ends h₂ hret hev (k := .strongBind (.mk a3 (.base (none, t2))) rest env :: k)
        (ReturnLit.noBoundary_cons hk trivial) m₁ hm₁ with
      ⟨t, loc, ub, r', halt⟩ | ⟨okr, t, r', halt, out⟩
    · exact .inl ⟨t, loc, ub, pre.trans (r.trans (s₃.trans r')), halt⟩
    · exact .inr (.inr ⟨ok, eq, okr, t, pre.trans (r.trans (s₃.trans r')), halt, out.trans out₁⟩)

/-! ## The whole document -/

theorem charOfArgs_int {args : List String} (ha : Spec.ArgsOk args) (i j : Nat) :
    ConvInt.IsInt (ArgvChar.charOfArgs args i j) := by
  unfold ArgvChar.charOfArgs
  split
  · rename_i hi
    cases hj : ((args[i].toList.map fun c => (c.toNat : Int)) ++ [0])[j]? with
    | none => simp [ConvInt.IsInt]
    | some x =>
      simp only [Option.getD_some]
      have hx : x ∈ (args[i].toList.map fun c => (c.toNat : Int)) ++ [0] := List.mem_of_getElem? hj
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨c, hc, rfl⟩ | rfl
      · obtain ⟨-, h1, -⟩ := ArgvReloc.chars_of_argsOk ha _ (List.getElem_mem hi) c hc
        constructor <;> omega
      · constructor <;> omega
  · constructor <;> omega

theorem recognize_cases {doc : Codec.Document} {P : Plan} (h : recognize doc = some P) :
    (∃ a b, doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) = false ∧ doc.file.callingConvention = .normal ∧
      ∃ s loc marker ty argc tc argv tv body, doc.file.main = some s ∧
        doc.file.funs.lookup s = some (.procedure loc marker ty [(argc, tc), (argv, tv)] body) ∧
        argc.key ≠ argv.key ∧ ((a, b) = ((1 : Nat), (0 : Nat)) ∨ (a, b) = ((0 : Nat), (0 : Nat))) ∧
        recognizeBody doc.file argv (a, b) body = some P) := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
  split at h
  · rename_i normal
    cases main : doc.file.main with
    | none => simp [main] at h
    | some sym =>
      cases decl : doc.file.funs.lookup sym with
      | none => simp [main, decl] at h
      | some entry =>
        cases entry <;> try { simp [main, decl] at h }
        case procedure loc marker ty ps body =>
          match ps, h with
          | [(argc, tc), (argv, tv)], h =>
            simp only [main, decl, bind, Option.bind] at h
            split at h
            · rename_i ne
              cases h1 : recognizeBody doc.file argv (1, 0) body with
              | some P' =>
                rw [h1] at h
                cases h
                exact ⟨1, 0, by simpa using nodefs, normal, sym, loc, marker, ty, argc, tc, argv, tv, body, rfl,
                  decl, ne, .inl rfl, h1⟩
              | none =>
                rw [h1] at h
                exact ⟨0, 0, by simpa using nodefs, normal, sym, loc, marker, ty, argc, tc, argv, tv, body, rfl,
                  decl, ne, .inr rfl, h⟩
            · cases h
          | [], h => simp [main, decl] at h
          | [_], h => simp [main, decl] at h
          | _ :: _ :: _ :: _, h => simp [main, decl] at h
  · cases h

/-- **Core side.** For every `ArgsOk` argument vector, with `ch` the character `argv[i][0]` reads
(`ArgvChar.charOfArgs`), Core reaches undefined behaviour, or the test is in range and the program
aborts (test not `1`) or exits with the return expression's value (test `1`), with no output. -/
theorem recognize_sound (doc : Codec.Document) (P : Plan) (h : recognize doc = some P)
    (args : List String) (ha : Spec.ArgsOk args) :
    Spec.CoreUB doc args ∨
    (P.test.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2) ∧
      P.test.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2) ≠ 1 ∧ Spec.CoreBeh doc args (.abort [])) ∨
    (P.test.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2) ∧
      P.test.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2) = 1 ∧
      P.ret.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2) ∧
      Spec.CoreBeh doc args (.exit ((P.ret.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2)) % 256).toNat [])) := by
  obtain ⟨i, j, nodefs, normal, sym, loc, marker, ty, argc, tc, argv, tv, body, main, decl, ne, hij, hbody⟩ :=
    recognize_cases h
  obtain ⟨a0, a1, t0, blk, sa, ret, bt, r, info, ba, pa, r', s₁, s₂, rfl, hr, hfree, hb, h₁, h₂, hP⟩ :=
    recognizeBody_inv hbody
  have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
    rintro ⟨x, g⟩ hx bt e rfl
    have := List.any_eq_false.mp nodefs _ hx
    simp at this
  obtain ⟨s, labels, xs, qs, pc, V, m, hinit, hreach, hout, B, objs⟩ :=
    ArgvMem.initial_reaches_body_mem doc.file (Map.ofList (doc.enumBindings.getD [])) args ha hdefs main decl
      normal
  have hlabels : labels = Map.ofList (saves (.mk a0 (.sseq (.mk a1 (.base (none, t0))) blk
      (.mk sa (.save (ret, bt) [(r, info)] (.mk ba (.pure (.mk pa () (.sym r'))))))))).reverse := by
    simp [initial, main, decl] at hinit
    exact hinit.2.symm
  have hret : ReturnLit.ReturnLabel labels ret := by
    rw [hlabels]
    refine ⟨r, ba, pa, r', hr, ?_⟩
    simp [saves, StmtIf.labelFree_saves blk hfree, Map.ofList]
  let env : Env := extendEnv [(argc, .object (.pointer pc)),
    (argv, .object (.pointer (.allocated (args.length + 2) V)))] ∅
  have hargv : env.lookup argv = some (.object (.pointer (.allocated (args.length + 2) V))) :=
    ConvInt.lookup_two_second rfl (fun e => ne e.symm)
  let I : Mem.Concrete.State → Prop := fun m => ArgvMem.Objs m args (args.length + 2) V args.length B qs
  have hI : ArgvChar.Stable I := fun m m' hm g => hm.reads g
  let ch := ArgvChar.charOfArgs args i j
  have hlen : 1 ≤ args.length := List.length_pos_iff.mpr ha.1
  have hev : TermRuns (file := doc.file) (labels := labels) I argv (i, j) env ch := by
    intro t ex hterm
    refine ArgvExpr.term_ev hI (charOfArgs_int ha i j) (fun e he => ?_) t hterm
    refine ArgvChar.char_ev he ha ⟨m, objs⟩ hargv ?_ ?_
    · rcases hij with h | h <;> simp only [Prod.mk.injEq] at h <;> omega
    · intro _
      rcases hij with h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  let SAVE : EE := .mk sa (.save (ret, bt) [(r, info)] (.mk ba (.pure (.mk pa () (.sym r')))))
  have pre := hreach.trans (ReturnConst.sequence_reaches doc.file labels a0 _ blk SAVE env _ m)
  have ends := block_ends hb h₁ h₂ hret hI hev (k := [.strongBind (.mk a1 (.base (none, t0))) SAVE env,
    .annotations xs]) (by simp [ReturnLit.NoBoundary, hasBoundary]) m objs
  rw [hP]
  rcases ends with ⟨t, loc, ub, r₁, halt⟩ | ⟨ok, ne₁, t, r₁, halt, out⟩ | ⟨ok, eq₁, okr, t, r₁, halt, out⟩
  · exact .inl (.inr ⟨t, loc, ub, ⟨s, labels, hinit, pre.trans r₁⟩, halt⟩)
  · refine .inr (.inl ⟨ok, ne₁, ?_⟩)
    have beh := Spec.CoreBeh.abort ⟨s, labels, hinit, pre.trans r₁⟩ halt
    simpa [Spec.coreBytes, out, hout] using beh
  · refine .inr (.inr ⟨ok, eq₁, okr, ?_⟩)
    have beh := Spec.CoreBeh.exit (k := (P.ret.val ch % 256).toNat) ⟨s, labels, hinit, pre.trans r₁⟩ halt rfl
    simpa [Spec.coreBytes, out, hout] using beh

/-- The character a recognised plan reads is `argv[1][0]` or `argv[0][0]`. -/
theorem recognize_ij {doc : Codec.Document} {P : Plan} (h : recognize doc = some P) :
    P.ij.1 ≤ 1 ∧ P.ij.2 = 0 := by
  obtain ⟨i, j, _, _, _, _, _, _, _, _, _, _, body, _, _, _, hij, hbody⟩ := recognize_cases h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hP⟩ := recognizeBody_inv hbody
  rw [hP]
  rcases hij with h | h <;> simp only [Prod.mk.injEq] at h <;> omega

end Silmaril.Compile.Core.Verified.ArgvAbort
