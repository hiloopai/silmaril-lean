module

public import Silmaril.Compiler.Core.Verified.Straight.Defs

/-! # `main` that executes `return n;` for an `int` literal `n`

Cerberus elaborates `return e;` in `main` to
`let strong t = bound(e) in run ret(conv_loaded_int(int, t))`, where `ret` is the procedure's
return label, saved at the end of the body: `{ … } ; save ret(r := Specified 0) in pure(r)`.
`retLit file ret e = some n` recognises, syntactically, a statement sequence whose first
statement is such a `return` of the literal `n` (statements after it are dead: the `run`
leaves them). `recognize` accepts a document whose `main` is a procedure without parameters
whose body is this sequence followed by the return label, and whose file has no global
definitions. Nothing is evaluated.

`recognize_sound`: the Core dynamics, from the document's initial state, halts with
`Specified n` and an empty stdout (`StartupReach` for the start, `ConvInt` for
`conv_loaded_int`, `Straight` for the effects), so `CoreBeh doc args (exit (n mod 256) [])`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ReturnLit

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory focusMemory_stdout)
open ConvInt (isConvLoadedInt IsInt intTy Pure)

/-- Effectful expressions of decoded documents (spelled out: the compiler's closure must not
name the dynamics). -/
abbrev Eff := Expr Codec.wireModel Unit Unit Sym

/-- Expressions without `save`, so they add no label to the procedure's label map. The check
is conservative: only the forms of straight-line bodies are accepted. -/
def saveFree : Eff → Bool
  | .mk _ (.pure _) | .mk _ (.action _) | .mk _ (.run ..) | .mk _ (.bound _) => true
  | .mk _ (.sseq _ a b) | .mk _ (.wseq _ a b) => saveFree a && saveFree b
  | _ => false

/-- A sequence of statements that starts with `return n;` for the `int` literal `n`. -/
def retLit (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option Int
  | .mk _ (.sseq (.mk _ (.base (some t, _)))
      (.mk _ (.bound (.mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n)))))))))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym t')])]))) =>
      if l.key = ret.key ∧ t'.key = t.key ∧ isConvLoadedInt file s = true ∧
        -2147483648 ≤ n ∧ n ≤ 2147483647 then some n else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retLit file ret a
  | _ => none

/-- The body of a recognised `main`: a statement sequence that returns `n`, then the return
label `ret(r) = pure(r)`. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Int
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then retLit file ret a else none
  | _ => none

/-- `main` returns an `int` literal through `return`. -/
def recognize (doc : Codec.Document) : Option Int := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-! ## Proofs -/

variable {file : Program} {labels : Labels}

theorem saves_saveFree : (e : EE) → saveFree e = true → saves e = []
  | .mk ann node, h => by
    cases node <;> simp only [saveFree, Bool.and_eq_true, Bool.false_eq_true] at h
    case sseq p a b =>
      rw [saves, saves_saveFree a h.1, saves_saveFree b h.2]; simp
    case wseq p a b =>
      rw [saves, saves_saveFree a h.1, saves_saveFree b h.2]; simp
    all_goals simp [saves]
termination_by e => sizeOf e

/-- No procedure or initializer boundary: a `run` replaces the whole continuation. -/
def NoBoundary (k : List Frame) : Prop := hasBoundary k = false

theorem procedureContext_noBoundary {k : List Frame} (h : NoBoundary k) (fallback : Labels) :
    procedureContext fallback k = (fallback, []) := by
  induction k with
  | nil => rfl
  | cons f k ih =>
    unfold NoBoundary hasBoundary at h
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    cases f <;> simp_all [procedureContext, NoBoundary, hasBoundary]

theorem noBoundary_cons {f : Frame} {k : List Frame} (h : NoBoundary k)
    (hf : match f with | .procedureReturn _ | .globalResult .. => False | _ => True) :
    NoBoundary (f :: k) := by
  unfold NoBoundary hasBoundary at *
  cases f <;> simp_all

theorem lookup_key {α : Type} {m : Map Sym α} {a b : Sym} (h : a.key = b.key) :
    m.lookup a = m.lookup b := by
  unfold Map.lookup
  change Finmap.lookup a.key m = Finmap.lookup b.key m
  rw [h]

theorem bound_reaches (ann : List Annot) (e : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
      ⟨.effectExpr e env, .bound :: k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

theorem pop_reaches {f : Frame} (v : Val) (k : List Frame) (m : Mem.Concrete.State)
    (hf : f = .bound ∨ ∃ l, f = .diagnosticLocation l) :
    Reaches file labels ⟨.value v, f :: k, m⟩ ⟨.value v, k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  rcases hf with rfl | ⟨l, rfl⟩ <;> simp [request, requestAux, awaitsScheduling]

theorem bind_reaches (ann : List Annot) (t : Sym) (ty : BaseType) (v : Val) (b : EE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .strongBind (.mk ann (.base (some t, ty))) b env :: k, m⟩
      ⟨.effectExpr b (extendEnv [(t, v)] env), k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, matchPattern]

/-- A bound literal: `bound(pure(Specified n))` reaches its value. -/
theorem boundLit_reaches (ann ann' pann : List Annot) (n : Int) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.bound (.mk ann' (.pure (.mk pann () (.val (.loaded (.specified (.integer n))))))))) env, k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), k, focusMemory ann' m⟩ := by
  refine (bound_reaches ann _ env k m).trans ?_
  refine (ReturnConst.effect_pure_reaches file labels ann' _ env _ m).trans ?_
  refine (ReturnConst.pure_value_reaches file labels pann _ env _ _).trans ?_
  simp only [runtimeValue, runtimeLoaded, runtimeObject]
  exact (pop_reaches _ _ _ (.inr ⟨_, rfl⟩)).trans (pop_reaches _ _ _ (.inl rfl))

/-- The return label `ret(r) = pure(r')` of the procedure, with `r'` the parameter. -/
def ReturnLabel (labels : Labels) (ret : Sym) : Prop :=
  ∃ r bann pann r', r'.key = r.key ∧
    labels.lookup ret = some ([r], .mk bann (.pure (.mk pann () (.sym r'))))

/-- `run ret(v)` from a continuation without boundary halts with `v`. -/
theorem jump_halts {ret l : Sym} (hl : l.key = ret.key) (hret : ReturnLabel labels ret)
    (v : Val) (env : Env) {k : List Frame} (hk : NoBoundary k) (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.value v, .runLabel l [] [] env :: k, m⟩ ⟨.halt (.defined v), [], m'⟩ := by
  obtain ⟨r, bann, pann, r', hr, hlook⟩ := hret
  have hlook' : labels.lookup l = some ([r], .mk bann (.pure (.mk pann () (.sym r')))) := by
    rw [lookup_key hl]; exact hlook
  refine ⟨focusMemory bann m, focusMemory_stdout bann m, ?_⟩
  have hk' : hasBoundary k = false := hk
  refine (next_reaches (c' := .effectExpr (.mk bann (.pure (.mk pann () (.sym r'))))
      (extendEnv ([r].zip [v]) env)) (k' := []) (by intro o h; cases h) ?_).trans ?_
  · simp [request, requestAux, awaitsScheduling, requestJump, hk', jump, jumpDestination,
      procedureContext_noBoundary hk, hlook']
  refine (ReturnConst.effect_pure_reaches file labels bann _ _ [] m).trans ?_
  refine (next_reaches (c' := .value v) (k' := [.diagnosticLocation m.currentLocation])
    (by intro o h; cases h) ?_).trans ?_
  · have : (extendEnv [(r, v)] env).lookup r' = some v := ConvInt.lookup_one hr
    simp [request, requestAux, awaitsScheduling, this]
  exact (pop_reaches _ _ _ (.inr ⟨_, rfl⟩)).trans (ReturnConst.value_halts file labels v _)

/-- **The `return` statement.** A recognised statement sequence halts with `Specified n`, from
every environment, continuation without boundary and memory, keeping stdout. -/
theorem retLit_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) (n : Int)
    (h : retLit file ret e = some n) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ := by
  unfold retLit at h
  split at h
  · rename_i _ ann pann t ty bann ann' pann' n' rann l cann s a2 tyann a3 t'
    split at h
    · rename_i cond
      obtain ⟨hl, ht, hs, lo, hi⟩ := cond
      cases h
      let v : Val := .loaded (.specified (.integer n))
      let m₁ := focusMemory ann' m
      let env₁ := extendEnv [(t, v)] env
      let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
        [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym t')])])
      have hk₁ : NoBoundary (.strongBind (.mk pann (.base (some t, ty))) R env :: k) :=
        noBoundary_cons hk trivial
      have heval : Eval file (tagsOf file (focusMemory rann m₁)) env₁
          (.inl (.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym t')])))
          (.inl v) :=
        ConvInt.convLoadedInt_eval (ann := tyann) hs ⟨lo, hi⟩
          (.cons .val (.cons (.sym (ConvInt.lookup_one ht)) .nil))
      obtain ⟨m', out, halts⟩ := jump_halts hl hret v env₁ hk (focusMemory rann m₁)
      refine ⟨m', by simp [out, m₁], ?_⟩
      refine (ReturnConst.sequence_reaches file labels ann _ _ R env k m).trans ?_
      refine (boundLit_reaches bann ann' pann' n env _ m).trans ?_
      refine (bind_reaches pann t ty v R env k m₁).trans ?_
      refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
      exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
    · cases h
  · rename_i _ ann pann ty a b
    obtain ⟨m', out, halts⟩ := retLit_halts hret a n h env
      (k := .strongBind (.mk pann (.base (none, ty))) b env :: k) (noBoundary_cons hk trivial) m
    exact ⟨m', out, (ReturnConst.sequence_reaches file labels ann _ a b env k m).trans halts⟩
  · cases h
termination_by sizeOf e

theorem returnLabel_body {ann sann bann pann' : List Annot} {pat : Pattern Sym} {a : EE}
    {ret : Sym} {bt : BaseType} {r : Sym} {info : (BaseType × Option (Ctype × PassBy)) × PE}
    {r' : Sym} (hr : r'.key = r.key) (hfree : saveFree a = true) :
    let body : EE := .mk ann (.sseq pat a
      (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))))
    ReturnLabel (Map.ofList (saves body).reverse) ret := by
  refine ⟨r, bann, pann', r', hr, ?_⟩
  simp [saves, saves_saveFree a hfree, Map.ofList]

/-- The whole-document run: from the initial state (any arguments, any enum registrations),
the dynamics halts with `Specified n` and empty stdout. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (h : recognize doc = some n)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels t, initial doc.file enums args = .ok (s, labels) ∧ Reaches doc.file labels s t ∧
      t.control = .halt (.defined (.loaded (.specified (.integer n)))) ∧ t.memory.stdout = "" := by
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
          have hbody : recognizeBody doc.file body = some n := by simpa [main, decl] using h
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
                rw [hlabels]; exact returnLabel_body hr hfree
              obtain ⟨m', hout', halts⟩ := retLit_halts hret a n hbody ∅
                (k := [.strongBind (.mk pann (.base (none, bt0))) _ ∅, .annotations xs]) (by simp [NoBoundary, hasBoundary]) m
              exact ⟨s, labels, _, hinit,
                hentry.trans ((ReturnConst.sequence_reaches doc.file labels ann _ a _ ∅ _ m).trans
                  halts), rfl, by simp [hout', hout]⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document exits with `n mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (h : recognize doc = some n)
    (args : List String) :
    Spec.CoreBeh doc args (.exit (n % 256).toNat []) := by
  obtain ⟨s, labels, t, hinit, reach, halt, out⟩ :=
    recognize_reaches doc n h (Map.ofList (doc.enumBindings.getD [])) args
  have beh := Spec.CoreBeh.exit (k := (n % 256).toNat) ⟨s, labels, hinit, reach⟩ halt rfl
  simpa [Spec.coreBytes, out] using beh

end Silmaril.Compile.Core.Verified.ReturnLit
