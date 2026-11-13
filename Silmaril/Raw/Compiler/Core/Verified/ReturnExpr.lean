module

public import Silmaril.Compiler.Core.Verified.StmtIf.Defs

/-! # `main` returning a closed `int` expression

`recognize doc = some t`: `main`'s body is a statement sequence whose first statement is
`return e;`, `e` an expression of `IntExpr.term` that reads no local (literals, `+`, `-`, `*`;
the `unseq` elaboration of `return 1+2;`), then the return label. As `ReturnLit`:

```
let strong u = bound(e) in run ret(conv_loaded_int(int, u))
```

The recognizer also accepts nested C `if` statements whose branches both return such
expressions. Their `Specified`-to-boolean conversion is recognized by `StmtIf.boolSource`;
`StmtIf.choose` emits the matching runtime comparison and selection.

`recognize_sound`: Core reaches undefined behaviour (an operator leaves `int`) or exits with
`t.val 0 mod 256` and no output, for every argument list. The Lir translation computes `e` at
run time (`IntExpr.exprOps 0 t`); nothing is folded.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ReturnExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory)
open ReturnLit (Eff NoBoundary ReturnLabel saveFree noBoundary_cons)
open ConvInt (isConvLoadedInt IsInt)
open IntExpr (Term term)
open LocalExpr (Shows)

/-- A statement sequence that starts with `return e;` for an expression `e` reading no local. -/
def retTerm (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ isConvLoadedInt file s = true then
        match term file u e with
        | some t => if t.reads = false then some t else none
        | none => none
      else none
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) ea eb))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true then
        match term file c ec, retTerm file ret ea, retTerm file ret eb with
        | some tc, some ta, some tb =>
            if tc.reads = false then some (StmtIf.choose tc ta tb) else none
        | _, _, _ => none
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retTerm file ret a
  | _ => none

/-- The body of `main`: a statement sequence that returns `e`, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then retTerm file ret a else none
  | _ => none

/-- `main` returns a closed `int` expression. -/
def recognize (doc : Codec.Document) : Option Term := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-! ## Core side -/

variable {file : Program} {labels : Labels}

theorem isInt_zero : IsInt 0 := by unfold IsInt; omega

theorem retTerm_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) (t : Term)
    (h : retTerm file ret e = some t) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold retTerm at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i t' hτ
        split at h
        · rename_i hr
          have e := Option.some.inj h
          subst e
          have none₁ : ∀ {P : Prop}, t'.reads = true → P := fun r => by rw [hr] at r; cases r
          let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
          let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
                k, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine LocalExpr.Shows.pre pre ?_
          by_cases ok : t'.Ok 0
          · left
            refine ⟨ok, ?_⟩
            obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
              (labels := labels) (env := env) (id := 0) (addr := 0) t' hτ none₁ isInt_zero ok (.bound :: kR) m
              none₁
            let v : Val := IntExpr.spec (t'.val 0)
            have popped : Reaches file labels ⟨.value v, fr ++ .bound :: kR, m₁⟩ ⟨.value v, kR, m₁⟩ := by
              rcases hfr with ⟨rfl, -⟩ | rfl
              · exact LocalExpr.value_bound_reaches v kR m₁
              · exact Locals.annotations_bound_reaches xs v kR m₁
            let env₁ := extendEnv [(u, v)] env
            have heval : Eval file (tagsOf file (focusMemory rann m₁)) env₁
                (.inl (.mk cann () (.call (.sym s)
                  [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                    .mk a3 () (.sym u')])))
                (.inl v) :=
              ConvInt.convLoadedInt_eval (ann := tyann) hs (IntExpr.Term.ok_int isInt_zero t' ok)
                (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
            obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk (focusMemory rann m₁)
            refine ⟨m', by simp [out, tch.stdout], ?_⟩
            refine (Interleave.reaches_of_local file labels run).trans (popped.trans ?_)
            refine (ReturnLit.bind_reaches pann u ty v R env k m₁).trans ?_
            refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
            exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
          · right
            exact ArenaFail.fail_reaches file labels
              (IntExpr.term_fails (file := file) (labels := labels) (env := env) (id := 0) (addr := 0) t' hτ none₁
                isInt_zero ok (.bound :: kR) m none₁)
        · cases h
      · cases h
    · cases h
  · rename_i _ ann pc c cty bann ec sann pb b bty cb iann bp b' ea eb
    split at h
    · rename_i cond
      obtain ⟨hb', hcb⟩ := cond
      split at h
      · rename_i tc ta tb htc hta htb
        split at h
        · rename_i hreads
          cases h
          have noread : ∀ {P : Prop}, tc.reads = true → P := fun r => by
            rw [hreads] at r; cases r
          let IF : EE := .mk iann (.if_ (.mk bp () (.sym b')) ea eb)
          let REST : EE := .mk sann (.sseq (.mk pb (.base (some b, bty))) cb IF)
          let K := Frame.strongBind (.mk pc (.base (some c, cty))) REST env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pc (.base (some c, cty)))
                (.mk bann (.bound ec)) REST)) env, k, m⟩
              ⟨.effectExpr ec env, .bound :: K, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine Shows.pre pre ?_
          by_cases okc : tc.Ok 0
          · obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
              (labels := labels) (env := env) (id := 0) (addr := 0) tc htc noread
              isInt_zero okc (.bound :: K) m noread
            have popped : Reaches file labels
                ⟨.value (IntExpr.spec (tc.val 0)), fr ++ .bound :: K, m₁⟩
                ⟨.value (IntExpr.spec (tc.val 0)), K, m₁⟩ := by
              rcases hfr with ⟨rfl, -⟩ | rfl
              · exact LocalExpr.value_bound_reaches _ K m₁
              · exact Locals.annotations_bound_reaches xs _ K m₁
            let env₁ := extendEnv [(c, IntExpr.spec (tc.val 0))] env
            let KB := Frame.strongBind (.mk pb (.base (some b, bty))) IF env₁ :: k
            obtain ⟨m₂, out₂, conv⟩ := StmtIf.boolSource_reaches (file := file) (labels := labels)
              hcb env₁ KB m₁ (tc.val 0) (ConvInt.lookup_one rfl)
            let flag := decide (tc.val 0 ≠ 1)
            let env₂ := extendEnv [(b, boolean flag)] env₁
            have hp : SeqReach.PureEval file labels (.mk bp () (.sym b')) env₂ (boolean flag) :=
              SeqReach.pure_symbol bp b' env₂ _ (ConvInt.lookup_one hb')
            have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
                ⟨.effectExpr (if flag then ea else eb) env₂, k, SeqReach.focusMemory iann m₂⟩ :=
              (Interleave.reaches_of_local file labels run).trans (popped.trans
                ((ReturnLit.bind_reaches pc c cty _ REST env k m₁).trans
                  ((ReturnConst.sequence_reaches file labels sann _ cb IF env₁ k m₁).trans
                    (conv.trans ((ReturnLit.bind_reaches pb b bty _ IF env₁ k m₂).trans
                      (SeqReach.effect_if_reaches iann flag hp k m₂))))))
            have outm : (SeqReach.focusMemory iann m₂).stdout = m.stdout := by
              simp [out₂, tch.stdout]
            by_cases hc : tc.val 0 = 1
            · have o := retTerm_halts hret eb tb htb env₂ hk (SeqReach.focusMemory iann m₂)
              rw [outm] at o
              have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
                  ⟨.effectExpr eb env₂, k, SeqReach.focusMemory iann m₂⟩ := by
                simpa [flag, hc] using enter
              have o := Shows.pre enter' o
              rcases o with ⟨okb, m', hout, reach⟩ | ub
              · exact .inl ⟨by simpa [hc] using And.intro okc okb, m', hout,
                  by simpa [hc] using reach⟩
              · exact .inr ub
            · have o := retTerm_halts hret ea ta hta env₂ hk (SeqReach.focusMemory iann m₂)
              rw [outm] at o
              have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
                  ⟨.effectExpr ea env₂, k, SeqReach.focusMemory iann m₂⟩ := by
                simpa [flag, hc] using enter
              have o := Shows.pre enter' o
              rcases o with ⟨oka, m', hout, reach⟩ | ub
              · exact .inl ⟨by simpa [hc] using And.intro okc oka, m', hout,
                  by simpa [hc] using reach⟩
              · exact .inr ub
          · right
            exact ArenaFail.fail_reaches file labels
              (IntExpr.term_fails (file := file) (labels := labels) (env := env) (id := 0) (addr := 0)
                tc htc noread isInt_zero okc (.bound :: K) m noread)
        · cases h
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retTerm_halts hret a t h env (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m)
  · cases h
termination_by sizeOf e

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (t : Term) (h : recognize doc = some t)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s 0 t "" := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
  cases main : doc.file.main with
  | none => simp [main] at h
  | some sym =>
    cases decl : doc.file.funs.lookup sym with
    | none => simp [main, decl] at h
    | some entry =>
      cases entry <;> try { simp [main, decl] at h }
      case procedure loc marker ty ps body =>
        cases ps with
        | cons p ps => simp [main, decl] at h
        | nil =>
          have hbody : recognizeBody doc.file body = some t := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hentry⟩ := StartupReach.initial_reaches_body
            doc.file enums args hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]
                refine ⟨r, bann, pann', r', hr, ?_⟩
                simp [saves, StmtIf.labelFree_saves a hfree, Map.ofList]
              let SAVE : EE :=
                .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
              have o := retTerm_halts hret a t hbody ∅
                (k := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs])
                (by simp [NoBoundary, hasBoundary]) m
              rw [hout] at o
              exact ⟨s, labels, hinit, LocalExpr.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with
`t.val 0 mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (t : Term) (h : recognize doc = some t)
    (args : List String) :
    Spec.CoreUB doc args ∨ t.Ok 0 ∧ Spec.CoreBeh doc args (.exit (t.val 0 % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc t h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (t.val 0 % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.ReturnExpr
