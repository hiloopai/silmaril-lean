module

public import Silmaril.Compiler.Core.Verified.Globals.Defs

/-! # `main` returning an `int` expression over an `int` global

`recognize doc = some (n, t)`: every global definition of the file is an `int` initialised by a
literal (`Globals.inits`; `int x;` is `int x = 0;`), with distinct symbols, `main` is a procedure
without parameters, and `main`'s body is a statement sequence whose first statement is
`return e;` (as in `ReturnExpr`), then the return label, `e` an expression of `IntExpr.term`
(literals, reads of one global `x` initialised by `n`, `+`, `-`, `*`, comparisons and `?:`):

```
let strong u = bound(e) in run ret(conv_loaded_int(int, u))
```

`recognize_sound`: Core reaches undefined behaviour (an operator leaves `int`) or exits with
`t.val n mod 256` and no output, for every argument list: the startup runs the initialisers
(`Globals.initial_reaches_body`), and the reads of `x` find `n` in its object. The Lir
translation is `LocalExpr`'s: `x` lives in register 3, set to its initialiser `n` at entry, and
`e` is computed at run time (`IntExpr.exprOps n t`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.GlobalExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory)
open ReturnLit (Eff NoBoundary ReturnLabel saveFree noBoundary_cons)
open ConvInt (isConvLoadedInt IsInt)
open IntExpr (Term term)
open LocalExpr (Shows)
open Locals (Slot)
open Mem.Concrete (IntRange)

/-- The first global whose reads (if any) make `e` a term: the global, its value, the term. -/
def pick (file : File Codec.wireModel Unit Unit) (e : Eff) : List (Sym × Int) → Option (Sym × Int × Term)
  | [] => none
  | (x, n) :: gs => match term file x e with
    | some t => some (x, n, t)
    | none => pick file e gs

theorem pick_mem {file : File Codec.wireModel Unit Unit} {e : Eff} :
    ∀ {gs : List (Sym × Int)} {x : Sym} {n : Int} {t : Term}, pick file e gs = some (x, n, t) →
      (x, n) ∈ gs ∧ term file x e = some t
  | [], _, _, _, h => by simp [pick] at h
  | (y, w) :: gs, x, n, t, h => by
    unfold pick at h
    split at h
    · rename_i t' ht
      cases h
      exact ⟨List.mem_cons_self, ht⟩
    · obtain ⟨hm, ht⟩ := pick_mem h
      exact ⟨List.mem_cons_of_mem _ hm, ht⟩

/-- A statement sequence that starts with `return e;`, `e` reading at most one global. -/
def retTerm (file : File Codec.wireModel Unit Unit) (ret : Sym) (gs : List (Sym × Int)) :
    Eff → Option (Sym × Int × Term)
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ isConvLoadedInt file s = true then pick file e gs
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retTerm file ret gs a
  | _ => none

/-- The body of `main`: a statement sequence that returns `e`, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (gs : List (Sym × Int)) :
    Eff → Option (Sym × Int × Term)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then retTerm file ret gs a else none
  | _ => none

/-- The globals are `int`s initialised by literals, with distinct symbols, and `main` returns an
`int` expression over one of them. -/
def recognize (doc : Codec.Document) : Option (Int × Term) := do
  let ds := Globals.definitions doc.file
  let gs ← Globals.inits doc.file ds
  if (ds.map fun d => d.1.key).Nodup ∧ 8 * (ds.length + 1) < 281474976710655 then do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    let (_, n, t) ← recognizeBody doc.file gs body
    pure (n, t)
  else none

/-! ## Core side -/

variable {file : Program} {labels : Labels}

theorem retTerm_halts {ret : Sym} (hret : ReturnLabel labels ret) {gs : List (Sym × Int)}
    (e : EE) {x : Sym} {n : Int} {t : Term} (h : retTerm file ret gs e = some (x, n, t)) (env : Env)
    {k : List Frame} (hk : NoBoundary k) (m : Mem.Concrete.State)
    (hgs : ∀ x n, (x, n) ∈ gs → IntRange n ∧ ∃ id addr,
      env.lookup x = some (.object (.pointer (.allocated id addr))) ∧ Slot m id addr n) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ n t m.stdout := by
  unfold retTerm at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      obtain ⟨hmem, hτ⟩ := pick_mem h
      obtain ⟨hn, id, addr, hx, slot⟩ := hgs x n hmem
      let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
        [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
      let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
      have pre : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
            k, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
          (ReturnLit.bound_reaches bann _ env _ m)
      refine LocalExpr.Shows.pre pre ?_
      by_cases ok : t.Ok n
      · left
        refine ⟨ok, ?_⟩
        obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
          (labels := labels) t hτ (fun _ => hx) hn ok (.bound :: kR) m (fun _ => slot)
        let v : Val := IntExpr.spec (t.val n)
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
          ConvInt.convLoadedInt_eval (ann := tyann) hs (IntExpr.Term.ok_int hn t ok)
            (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
        obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk (focusMemory rann m₁)
        refine ⟨m', by simp [out, tch.stdout], ?_⟩
        refine (Interleave.reaches_of_local file labels run).trans (popped.trans ?_)
        refine (ReturnLit.bind_reaches pann u ty v R env k m₁).trans ?_
        refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
        exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
      · right
        exact ArenaFail.fail_reaches file labels
          (IntExpr.term_fails (file := file) (labels := labels) t hτ (fun _ => hx) hn ok (.bound :: kR) m
            (fun _ => slot))
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retTerm_halts hret a h env (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m hgs)
  · cases h
termination_by sizeOf e

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (t : Term)
    (h : recognize doc = some (n, t)) (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s n t "" := by
  unfold recognize at h
  cases hgs : Globals.inits doc.file (Globals.definitions doc.file) with
  | none => simp [hgs] at h
  | some gs =>
    simp only [hgs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i cond
      obtain ⟨nd, room⟩ := cond
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
              cases hb : recognizeBody doc.file gs body with
              | none => simp [main, decl, hb] at h
              | some r =>
                obtain ⟨x, n', t'⟩ := r
                simp [main, decl, hb] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨s, m, env, xs, hinit, hout, hglob, hentry⟩ :=
                  Globals.initial_reaches_body doc.file enums args hgs nd room main decl
                generalize hL : Map.ofList (saves body).reverse = labels at hinit hentry
                unfold recognizeBody at hb
                split at hb
                · rename_i _ ann pann bt0 a sann ret bt rr info bann pann' r'
                  split at hb
                  · rename_i cond
                    obtain ⟨hr, hfree⟩ := cond
                    have hret : ReturnLabel labels ret := by
                      rw [← hL]; exact ReturnLit.returnLabel_body hr hfree
                    let SAVE : EE :=
                      .mk sann (.save (ret, bt) [(rr, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
                    let K : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE env,
                      .annotations xs]
                    have hK : NoBoundary K := by simp [K, NoBoundary, hasBoundary]
                    have pre := hentry.trans
                      (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE env _ m)
                    have o := retTerm_halts (labels := labels) hret a hb env hK m hglob
                    rw [hout] at o
                    exact ⟨s, labels, hinit, LocalExpr.Shows.pre pre o⟩
                  · cases hb
                · cases hb
    · cases h

/-- **Core side.** A recognised document reaches undefined behaviour, or `t` stays in range and
the document exits with `t.val n mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (t : Term)
    (h : recognize doc = some (n, t)) (args : List String) :
    Spec.CoreUB doc args ∨ t.Ok n ∧ Spec.CoreBeh doc args (.exit (t.val n % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc n t h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (t.val n % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.GlobalExpr
