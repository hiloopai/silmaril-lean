module

public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs
public import Silmaril.Compiler.Core.Verified.LocalsDoc.Defs

/-! # `main` returning an `int` expression over one local

`recognize doc = some (n, t)`: `main` is a procedure without parameters, the file has no global
definitions, and `main`'s body is the block `{ int x = n; return e; }` followed by the return
label, `e` an expression of `IntExpr.term` (literals, reads of `x`, `+`, `-`, `*`). Cerberus
elaborates `return e;` to

```
let strong u = bound(e) in kill(int, x) ; run ret(conv_loaded_int(int, u))
```

`recognize_sound`: Core reaches undefined behaviour (an operator leaves `int`) or exits with
`t.val n mod 256` and no output, for every argument list. The Lir translation keeps `x` in
register 3 and computes `e` at run time (`IntExpr.exprOps`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LocalExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory)
open ReturnLit (Eff NoBoundary ReturnLabel lookup_key saveFree noBoundary_cons)
open ConvInt (isConvLoadedInt IsInt)
open Locals (Slot createInt storeLit killInt)
open IntExpr (Term term)
open Mem.Concrete (LiveInt IntRange nextIntAddress)

/-- `let strong u = bound(e) in kill(int, x) ; run ret(conv_loaded_int(int, u))`: `return e;`. -/
def retExpr (file : File Codec.wireModel Unit Unit) (ret x : Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.sseq (.mk _ (.base (none, _))) kl
        (.mk _ (.run () l [.mk _ () (.call (.sym s)
          [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
            .mk _ () (.sym u')])]))))) =>
      if u'.key = u.key ∧ u.key ≠ x.key ∧ l.key = ret.key ∧ isConvLoadedInt file s = true ∧
        killInt x kl = true then term file x e else none
  | _ => none

/-- `S₁ ; S₂` whose first statement is `return e;`. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret x : Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) r _) => retExpr file ret x r
  | _ => none

/-- The block `{ int x = n; return e; }`. -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option (Int × Term)
  | .mk _ (.sseq (.mk _ (.base (some x, _))) cr (.mk _ (.sseq (.mk _ (.base (none, _))) ini rest))) =>
      if createInt cr = true then
        (storeLit file x ini).bind fun n => (retStmt file ret x rest).map fun t => (n, t)
      else none
  | _ => none

/-- The body of `main`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option (Int × Term)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then block file ret a else none
  | _ => none

/-- `main` is `{ int x = n; return e; }`. -/
def recognize (doc : Codec.Document) : Option (Int × Term) := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-! ## Core side -/

variable {file : Program} {labels : Labels}

theorem value_bound_reaches (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .bound :: k, m⟩ ⟨.value v, k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

/-- What a run from a statement shows: the value of `e` returned, or undefined behaviour. -/
def Shows (s : State) (n : Int) (t : Term) (stdout : String) : Prop :=
  (t.Ok n ∧ ∃ m', m'.stdout = stdout ∧
    Reaches file labels s ⟨.halt (.defined (IntExpr.spec (t.val n))), [], m'⟩) ∨
  ∃ s', Reaches file labels s s' ∧ s'.control = .halt IntExpr.overflow

theorem Shows.pre {s s' : State} {n : Int} {t : Term} {out : String}
    (h : Reaches file labels s s') (o : Shows (file := file) (labels := labels) s' n t out) :
    Shows (file := file) (labels := labels) s n t out := by
  rcases o with ⟨ok, m', hout, r⟩ | ⟨s'', r, hs⟩
  · exact .inl ⟨ok, m', hout, h.trans r⟩
  · exact .inr ⟨s'', h.trans r, hs⟩

theorem retExpr_halts {ret x : Sym} {e : Eff} {t : Term} (h : retExpr file ret x e = some t)
    (hret : ReturnLabel labels ret) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ n t m.stdout := by
  unfold retExpr at h
  split at h
  · rename_i _ ann pann u ty bann E sann kpann kty kl rann l cann s a3 c3 a4 u'
    split at h
    · rename_i cond
      obtain ⟨hu', hux, hl, hs, hkl⟩ := cond
      let CALL : PE := .mk cann () (.call (.sym s)
        [.mk a3 () (.val (.ctype (.mk c3 (.basic (.integer (.signed .int)))))), .mk a4 () (.sym u')])
      let RUN : EE := .mk rann (.run () l [CALL])
      let REST : EE := .mk sann (.sseq (.mk kpann (.base (none, kty))) kl RUN)
      let kR := Frame.strongBind (.mk pann (.base (some u, ty))) REST env :: k
      have pre : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound E)) REST)) env,
            k, m⟩ ⟨.effectExpr E env, .bound :: kR, m⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
          (ReturnLit.bound_reaches bann _ env _ m)
      refine Shows.pre pre ?_
      by_cases ok : t.Ok n
      · left
        refine ⟨ok, ?_⟩
        obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file) (labels := labels) t
          h (fun _ => hx) hn ok (.bound :: kR) m (fun _ => slot)
        let v : Val := IntExpr.spec (t.val n)
        have popped : Reaches file labels ⟨.value v, fr ++ .bound :: kR, m₁⟩ ⟨.value v, kR, m₁⟩ := by
          rcases hfr with ⟨rfl, -⟩ | rfl
          · exact value_bound_reaches v kR m₁
          · exact Locals.annotations_bound_reaches xs v kR m₁
        have hv : IsInt (t.val n) := IntExpr.Term.ok_int hn t ok
        let env₂ := extendEnv [(u, v)] env
        have hx₂ : env₂.lookup x = some (.object (.pointer (.allocated id addr))) := by
          rw [ConvInt.lookup_one_other (fun e => hux e.symm)]; exact hx
        obtain ⟨m₃, out₃, hkill⟩ := Locals.killInt_reaches (file := file) (labels := labels) hkl env₂
          (.strongBind (.mk kpann (.base (none, kty))) RUN env₂ :: k) m₁ hx₂ (tch.slot slot).live
        have heval : Eval file (tagsOf file (focusMemory rann m₃)) env₂ (.inl CALL) (.inl v) :=
          ConvInt.convLoadedInt_eval (ann := c3) hs hv
            (.cons .val (.cons (.sym (ConvInt.lookup_one hu')) .nil))
        obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₂ hk (focusMemory rann m₃)
        refine ⟨m', by simp [out, out₃, tch.stdout], ?_⟩
        refine (Interleave.reaches_of_local file labels run).trans (popped.trans ?_)
        refine (ReturnLit.bind_reaches pann u ty v REST env k m₁).trans ?_
        refine (ReturnConst.sequence_reaches file labels sann _ _ _ env₂ k m₁).trans ?_
        refine hkill.trans ?_
        refine (ReturnConst.wildcard_sequence_reaches file labels kpann kty .unit RUN env₂ k m₃).trans ?_
        refine (Straight.focus_reaches (m := m₃) Straight.request_run).trans ?_
        exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
      · right
        obtain ⟨s', reach, halt⟩ := ArenaFail.fail_reaches file labels
          (IntExpr.term_fails (file := file) (labels := labels) t h (fun _ => hx) hn ok (.bound :: kR) m
            (fun _ => slot))
        exact ⟨s', reach, halt⟩
    · cases h
  · cases h

theorem retStmt_halts {ret x : Sym} {e : Eff} {t : Term} (h : retStmt file ret x e = some t)
    (hret : ReturnLabel labels ret) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ n t m.stdout := by
  unfold retStmt at h
  split at h
  · rename_i _ ann pann ty r b
    exact Shows.pre (ReturnConst.sequence_reaches file labels ann _ r b env k m)
      (retExpr_halts h hret env (noBoundary_cons hk trivial) m hx hn slot)
  · cases h

theorem block_reaches {ret : Sym} {e : Eff} {n : Int} {t : Term}
    (h : block file ret e = some (n, t)) (hret : ReturnLabel labels ret) (env : Env)
    {k : List Frame} (hk : NoBoundary k) (m : Mem.Concrete.State)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ n t m.stdout := by
  unfold block at h
  split at h
  · rename_i _ ann pann x ty cr sann spann sty ini rest
    split at h
    · rename_i hcr
      cases hs : storeLit file x ini with
      | none => simp [hs] at h
      | some n' =>
        cases hr : retStmt file ret x rest with
        | none => simp [hs, hr] at h
        | some t' =>
          simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
          let env₁ := extendEnv [(x, ptr)] env
          let B : EE := .mk sann (.sseq (.mk spann (.base (none, sty))) ini rest)
          obtain ⟨m₁, out₁, live₁, hcreate⟩ := Locals.createInt_reaches (file := file)
            (labels := labels) hcr env (.strongBind (.mk pann (.base (some x, ty))) B env :: k) m
            hpos hdead
          have hx₁ : env₁.lookup x = some ptr := ConvInt.lookup_one rfl
          obtain ⟨hn, m₂, xs, out₂, slot₂, hstore⟩ := Locals.storeLit_reaches (file := file)
            (labels := labels) hs env₁ (.strongBind (.mk spann (.base (none, sty))) rest env₁ :: k) m₁
            hx₁ live₁
          have pre := (ReturnConst.sequence_reaches file labels ann (.mk pann (.base (some x, ty))) cr B
              env k m).trans (hcreate.trans ((ReturnLit.bind_reaches pann x ty ptr B env k m₁).trans
            ((ReturnConst.sequence_reaches file labels sann (.mk spann (.base (none, sty))) ini rest env₁
              k m₁).trans (hstore.trans (Locals.annotations_bind_reaches xs spann sty .unit rest env₁ k
                m₂)))))
          have hk₂ : NoBoundary (.annotations xs :: k) := noBoundary_cons hk trivial
          have o := retStmt_halts hr hret env₁ hk₂ m₂ hx₁ hn slot₂
          rw [out₂, out₁] at o
          exact Shows.pre pre o
    · cases h
  · cases h

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (t : Term)
    (h : recognize doc = some (n, t)) (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s n t "" := by
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
          have hbody : recognizeBody doc.file body = some (n, t) := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ :=
            StartupMem.initial_reaches_body_mem doc.file enums args hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          · rename_i _ ann pann bt0 a sann ret bt rr info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]; exact ReturnLit.returnLabel_body hr hfree
              let SAVE : EE :=
                .mk sann (.save (ret, bt) [(rr, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
              let K : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
              have hK : NoBoundary K := by simp [K, NoBoundary, hasBoundary]
              have pre := (hentry.trans
                (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m))
              have o := block_reaches (labels := labels) hbody hret ∅ hK m
                (Locals.errno_nextIntAddress hlast) (by simp [hdead])
              rw [hout] at o
              exact ⟨s, labels, hinit, Shows.pre pre o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with
`t.val n mod 256` and no output. -/
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

end Silmaril.Compile.Core.Verified.LocalExpr
