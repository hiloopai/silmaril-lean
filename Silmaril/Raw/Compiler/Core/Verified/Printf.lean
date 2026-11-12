module

public import Silmaril.Compiler.Core.Verified.PrintfStmt.Defs
public import Silmaril.Compiler.Core.Verified.PrintfIntStmt.Defs
public import Silmaril.Compiler.Core.Verified.PrintLink.Defs
public import Silmaril.Compiler.Core.Verified.StateGlobals.Defs
public import Silmaril.Compiler.Core.Verified.Call.Defs
/-! # `main` printing string literals, then returning an integer

`recognize doc = some (n, outs)`: every global definition is a string literal
(`StrLit.litsOf`), `main` is a procedure without parameters whose body is sequencing glue
(`sseq`, `wseq`, `bound`, `pure`, `run`, as in `Return.evalE`) over statements `printf(s)`
(`PrintfStmt.printfLit`, `s` a literal without conversions) and `printf(s, e)`
(`PrintfIntStmt.printfInt`, `s` a literal with one `%d`, `e` a closed `int` expression) that
transfers the integer `n` to the return label; `outs` are the statements' outputs (`Out`), in
order. `evalP` folds the glue: the statements' results (their lengths) are constants, everything
else is `Fold.eval`.

A statement may also call a `void` procedure without parameters (`Call.callSite`) whose body is
such glue over `printf` statements that falls off its end (`calleeOuts`): the call prints the
callee's outputs and returns `unit`. `evalP` reads the callees' outputs from a table `calls`;
`recognizeBody` uses `calleeOuts`, which folds each callee's body with the empty table, so
callees do not call further procedures. The machine code prints the callee's outputs in place
of the call (the call is inlined), at run time like the others.

`recognize_sound`: for every argument list, Core exits with `n mod 256` after printing the
literals. The Lir side (`Fragments.printf`) is `PrintLink.link`: the machine code writes the
literals' bytes and the decimal digits of each `%d` operand into the output buffer at run time
(`PrintLink.Item.int`: the digits are computed by the machine code) and returns `n`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Printf

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold (WVal WEnv PExp Doc eval matchP extend EnvSub)
open StrMem PrintfStd StrLit PrintfStmt

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-! ## The recogniser -/

/-- What the glue folds to: a value, or a transfer to a saved label with its arguments. -/
inductive Res where
  | val : WVal → Res
  | jump : Sym → List WVal → Res

/-- What one statement prints: a literal without conversions, or a literal `pre%dsuf` around
the decimal digits of an integer. -/
inductive Out where
  | lit (cs : List Int)
  | dec (pre suf : List Char) (n : Int)

/-- The text of one statement's output. -/
def Out.text : Out → String
  | .lit cs => plainText cs
  | .dec pre suf n => PrintfIntStmt.text pre suf n

/-- Bindings that leave the literals alone. -/
def fresh (xs : List (Sym × WVal)) (ls : List (Sym × List Int)) : Bool :=
  xs.all fun x => ls.all fun y => x.1.key != y.1.key

/-- The symbols that the elaboration of a call `g()` (`Call.callSite`) binds: the function
pointer, the function type and the parameter types. -/
def siteSyms : EExp → Option (List Sym)
  | .mk _ (.sseq (.mk _ (.base (some p, _))) _
      (.mk _ (.let_ (.mk _ (.ctor .tuple [.mk _ (.base (some fty, _)), .mk _ (.base (some pty, _)),
          _, _])) _ _))) => some [p, fty, pty]
  | _ => none

/-- A call `g()` of a `void` procedure whose outputs `calls g` lists, binding no symbol of a
literal. -/
def callOuts (file : Doc) (ls : List (Sym × List Int)) (calls : Sym → Option (List Out))
    (e : EExp) : Option (List Out) :=
  match Call.callSite file e, siteSyms e with
  | some (g, false), some xs => if xs.all (fun x => ls.all fun y => x.key != y.1.key) then calls g else none
  | _, _ => none

/-- Fold the glue of `main`'s body with `printf` statements: the result, and the characters of
every printed literal, in order. -/
def evalP (file : Doc) (ls : List (Sym × List Int)) (calls : Sym → Option (List Out))
    (fuel : Nat) : WEnv → EExp → Option (Res × List Out)
  | env, .mk _ (.pure p) => (eval file fuel env p).map fun v => (.val v, [])
  | env, .mk _ (.bound e) =>
      match printfLit file ls env e with
      | some cs => some (.val (.loaded (.specified (.integer (plainText cs).length))), [.lit cs])
      | none =>
          match PrintfIntStmt.printfInt file ls env e with
          | some (pre, suf, n) =>
              some (.val (.loaded (.specified (.integer (PrintfIntStmt.text pre suf n).length))),
                [.dec pre suf n])
          | none =>
              match callOuts file ls calls e with
              | some outs => some (.val .unit, outs)
              | none =>
                  match StateExpr.term file e with
                  | some t =>
                      if t.vars.isEmpty ∧ PrintfIntStmt.okB (fun _ => 0) t then
                        some (.val (.loaded (.specified (.integer (t.val fun _ => 0)))), [])
                      else evalP file ls calls fuel env e
                  | none => evalP file ls calls fuel env e
  | env, .mk _ (.sseq pat a b) | env, .mk _ (.wseq pat a b) =>
      match evalP file ls calls fuel env a with
      | some (.val v, o₁) =>
          match matchP pat v with
          | some xs =>
              if fresh xs ls then
                (evalP file ls calls fuel (extend xs env) b).map fun (r, o₂) => (r, o₁ ++ o₂)
              else none
          | none => none
      | some (.jump l vs, o₁) => some (.jump l vs, o₁)
      | none => none
  | env, .mk _ (.run _ l (p :: ps)) => ((p :: ps).mapM (eval file fuel env)).map fun vs => (.jump l vs, [])
  | _, _ => none

/-- The body of a `void` procedure that falls off its end: glue `a`, then the return label
`ret(r := unit) = pure(r)`. -/
def fallGlue : EExp → Option EExp
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save _ [(r, (_, .mk _ () (.val .unit)))] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key then some a else none
  | _ => none

/-- The body of `g`: a procedure of the file (not of std.core), `void`, without parameters. -/
def calleeBody (file : Doc) (g : Sym) : Option EExp :=
  if (file.stdlib.lookup g).isSome then none else
  match file.funInfo.lookup g with
  | some (_, _, rty, [], _, _) =>
    if Call.retKind rty = some false then
      match file.funs.lookup g with
      | some (.procedure _ _ _ [] body) => some body
      | _ => none
    else none
  | _ => none

/-- The outputs of a call of `g`: its body falls off its end after glue over `printf`
statements, folded without further calls. -/
def calleeOuts (file : Doc) (ls : List (Sym × List Int)) (g : Sym) : Option (List Out) := do
  let body ← calleeBody file g
  let a ← fallGlue body
  match evalP file ls (fun _ => none) Return.fuel ∅ a with
  | some (.val _, outs) => some outs
  | _ => none

/-- A pattern that binds nothing. -/
def noBind : Pattern Sym → Bool
  | .mk _ (.base (none, _)) => true
  | _ => false

theorem noBind_inv {p : Pattern Sym} (h : noBind p = true) : ∃ a bt, p = .mk a (.base (none, bt)) := by
  unfold noBind at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

/-- `main`'s body: glue that transfers an integer to the return label, or falls off its end
(the label's default `0`), then that label. -/
def recognizeBody (file : Doc) (ls : List (Sym × List Int)) : EExp → Option (Int × List Out)
  | .mk _ (.sseq pat a (.mk _ (.save (ret, _) [(x, d)] (.mk _ (.pure (.mk _ _ (.sym y))))))) =>
      if MapKey.key x = MapKey.key y ∧ ReturnLit.saveFree a = true then
        match evalP file ls (calleeOuts file ls) Return.fuel ∅ a with
        | some (.jump l [.loaded (.specified (.integer n))], outs) =>
            if MapKey.key l = MapKey.key ret ∧ outs.length ≤ 2 ^ 20 then some (n, outs) else none
        | some (.val .unit, outs) =>
            if noBind pat ∧ StateGlobals.zeroDefault d.2 ∧ outs.length ≤ 2 ^ 20 then some (0, outs)
            else none
        | _ => none
      else none
  | _ => none

/-- String-literal globals, `main` without parameters printing literals and returning an integer. -/
def recognize (doc : Codec.Document) : Option (Int × List Out) := do
  let ls ← litsOf doc.file
  let s ← doc.file.main
  let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
  recognizeBody doc.file ls body

/-! ## The Core side -/

/-- The bytes Core prints for the literals. -/
def outBytes (outs : List Out) : List UInt8 := outs.flatMap fun o => Spec.coreBytes o.text

/-- The text of the literals. -/
def text (outs : List Out) : String := String.join (outs.map Out.text)

theorem text_append (o₁ o₂ : List Out) : text (o₁ ++ o₂) = text o₁ ++ text o₂ := by
  simp [text, String.join_append]

theorem text_single (cs : Out) : text [cs] = cs.text := by
  simp [text]

theorem coreBytes_text (outs : List Out) : Spec.coreBytes (text outs) = outBytes outs := by
  induction outs with
  | nil => simp [text, outBytes, Spec.coreBytes]
  | cons cs outs ih =>
    rw [show cs :: outs = [cs] ++ outs from rfl, text_append, text_single]
    simp only [Spec.coreBytes, String.toList_append, List.map_append] at ih ⊢
    rw [ih]
    simp [outBytes, Spec.coreBytes]

/-- What a run of glue guarantees: the literals printed, every earlier object kept, the dead
allocations below the next identifier, at most 16 bytes allocated per statement. -/
structure Post (m m' : Mem.Concrete.State) (outs : List Out) : Prop where
  stdout : m'.stdout = m.stdout ++ text outs
  keeps : Keeps m m'
  dead : DeadBelow m'
  room : m.lastAddress - 32 * outs.length ≤ m'.lastAddress

theorem Post.refl {m : Mem.Concrete.State} (hd : DeadBelow m) : Post m m [] :=
  ⟨by simp [text], Keeps.refl m, hd, by simp⟩

theorem Post.trans {m₁ m₂ m₃ : Mem.Concrete.State} {o₁ o₂ : List Out} (h₁ : Post m₁ m₂ o₁)
    (h₂ : Post m₂ m₃ o₂) : Post m₁ m₃ (o₁ ++ o₂) := by
  refine ⟨by rw [h₂.stdout, h₁.stdout, text_append, String.append_assoc], h₁.keeps.trans h₂.keeps,
    h₂.dead, ?_⟩
  have := h₁.room
  have := h₂.room
  simp only [List.length_append, Nat.cast_add]
  omega

theorem deadBelow_loc {m : Mem.Concrete.State} (h : DeadBelow m) (l : Loc) :
    DeadBelow {m with currentLocation := l} := h

theorem Post.focus {m : Mem.Concrete.State} (hd : DeadBelow m) (ann : List Annot) :
    Post m (ReturnConst.focusMemory ann m) [] := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]
  exact ⟨by simp [text], (Keeps.refl m).location l, deadBelow_loc hd l, by simp⟩

section Glue
variable (file : Program) (labels : Labels) (ls : List (Sym × List Int))
  (calls : Sym → Option (List Out))

open ReturnConst (Reaches next_reaches focusMemory effect_pure_reaches diagnostic_reaches
  sequence_reaches)
open Return (bound_reaches bound_value_reaches wseq_reaches strongBind_reaches effectBind_reaches
  run_reaches procedureContext_nb)

local notation "rv" => runtimeValue

/-- What the table of callees guarantees: a call statement it lists prints the listed outputs
and returns `unit`. -/
def CallsOk : Prop :=
  ∀ (e : EE) (outs : List Out), callOuts file ls calls e = some outs →
    ∀ denv m, LitEnv ls denv m → DeadBelow m → 64 + 32 * outs.length ≤ m.lastAddress → ∀ k,
    ∃ m', Reaches file labels ⟨.effectExpr e denv, k, m⟩ ⟨.value .unit, k, m'⟩ ∧ Post m m' outs

theorem callOuts_none (e : EE) : callOuts file ls (fun _ => none) e = none := by
  unfold callOuts
  split
  · split <;> rfl
  · rfl

/-- The empty table lists no call. -/
theorem callsOk_none : CallsOk file labels ls (fun _ => none) := by
  intro e outs h
  rw [callOuts_none] at h
  cases h

theorem fresh_bmap {xs : List (Sym × WVal)} (h : fresh xs ls = true) :
    ∀ x ∈ Fold.bmap xs, ∀ y ∈ ls, x.1.key ≠ y.1.key := by
  intro x hx y hy
  simp only [Fold.bmap, List.mem_map] at hx
  obtain ⟨⟨s, w⟩, hs, rfl⟩ := hx
  simp only [fresh, List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h _ hs y hy

/-- The arguments of a transfer, then the transfer itself, outside any nested procedure. -/
theorem run_chain_sub {env : WEnv} {denv : Env} (hr : EnvSub env denv) (l : Sym)
    {ps : List Sym} {tgt : EE} (hl : labels.lookup l = some (ps, tgt))
    (k : List Frame) (hk : hasBoundary k = false) (m : Mem.Concrete.State) :
    ∀ (rest : List PE) (p : PE) (done : List Val) (v : WVal) (vs : List WVal),
    eval file Return.fuel env p = some v → rest.mapM (eval file Return.fuel env) = some vs →
    ps.length = (done ++ rv v :: vs.map rv).length →
    Reaches file labels ⟨.pureExpr p denv, .runLabel l done rest denv :: k, m⟩
      ⟨.effectExpr tgt (extendEnv (ps.zip (done ++ rv v :: vs.map rv)) denv), [], m⟩
  | [], p, done, v, vs, hp, hvs, hlen => by
    simp at hvs
    subst hvs
    refine (Fold.eval_reaches_sub file labels _ env p v hp denv hr _ m).trans ?_
    apply next_reaches
    · intro o; simp
    · simp at hlen
      simp [request, requestAux, awaitsScheduling, requestJump, hk, jump, jumpDestination,
        procedureContext_nb labels k hk, hl, hlen]
  | q :: rest, p, done, v, vs, hp, hvs, hlen => by
    obtain ⟨w, ws, hq, hws, rfl⟩ := Fold.mapM_cons_some hvs
    refine (Fold.eval_reaches_sub file labels _ env p v hp denv hr _ m).trans ?_
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr q denv, .runLabel l (done ++ [rv v]) rest denv :: k, m⟩) ?_ ?_
    · apply next_reaches
      · intro o; simp
      · simp [request, requestAux, awaitsScheduling]
    · simpa using run_chain_sub hr l hl k hk m rest q (done ++ [rv v]) w ws hq hws (by simpa using hlen)

theorem evalP_run_val {doc : Doc} {env : WEnv} {ann : List Annot} {u : Unit} {l : Sym}
    {ps : List PE} {v : WVal} {outs : List Out}
    (h : evalP doc ls calls Return.fuel env (.mk ann (.run u l ps)) = some (.val v, outs)) : False := by
  cases ps with
  | nil => simp [evalP] at h
  | cons p ps =>
    simp only [evalP, Option.map_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    cases h

/-- **The glue reduces to its folded value**, printing the literals of its statements. -/
theorem evalP_val (hcalls : CallsOk file labels ls calls) :
    ∀ (e : EE) (env : WEnv) (v : WVal) (outs : List Out),
    evalP file ls calls Return.fuel env e = some (.val v, outs) →
    ∀ denv m, EnvSub env denv → LitEnv ls denv m → DeadBelow m →
    64 + 32 * outs.length ≤ m.lastAddress → ∀ k,
    ∃ m', Reaches file labels ⟨.effectExpr e denv, k, m⟩ ⟨.value (rv v), k, m'⟩ ∧ Post m m' outs
  | .mk ann e, env, v, outs, h, denv, m, hr, hl, hd, hroom, k => by
    cases e
    case pure p =>
      simp only [evalP, Option.map_eq_some_iff, Prod.mk.injEq, Res.val.injEq] at h
      obtain ⟨w, hw, rfl, rfl⟩ := h
      refine ⟨focusMemory ann m, ?_, Post.focus hd ann⟩
      exact (effect_pure_reaches file labels ann p denv k m).trans
        ((Fold.eval_reaches_sub file labels _ env p w hw denv hr _ _).trans
          (diagnostic_reaches file labels m.currentLocation _ k _))
    case bound e =>
      simp only [evalP] at h
      split at h
      · rename_i cs hcs
        simp only [Option.some.injEq, Prod.mk.injEq, Res.val.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m', reach, out, keeps, dead, room⟩ :=
          printfLit_reaches hcs hr hl hd (by simp at hroom; omega) ann k
        refine ⟨m', reach, ⟨by rw [out, text_single]; rfl, keeps, dead, by simp; omega⟩⟩
      · split at h
        · rename_i pre suf n hpi
          simp only [Option.some.injEq, Prod.mk.injEq, Res.val.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨m', reach, out, keeps, dead, room⟩ :=
            PrintfIntStmt.printfInt_reaches hpi hr hl hd (by simp at hroom; omega) ann k
          refine ⟨m', reach, ⟨by rw [out, text_single]; rfl, keeps, dead, by simp; omega⟩⟩
        · split at h
          · rename_i outs' hco
            simp only [Option.some.injEq, Prod.mk.injEq, Res.val.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨m', r, post⟩ := hcalls e outs' hco denv m hl hd hroom (.bound :: k)
            exact ⟨m', (bound_reaches file labels ann e denv k m).trans
              (r.trans (bound_value_reaches file labels _ k m')), post⟩
          · split at h
            · rename_i t ht
              split at h
              · rename_i hc
                simp only [Option.some.injEq, Prod.mk.injEq, Res.val.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hv, hok⟩ := hc
                obtain ⟨xs, m', fr, hfr, -, touched, run⟩ := StateExpr.term_runs (file := file)
                  (labels := labels) t ht (env := denv) (σ := fun _ => 0)
                  (PrintfIntStmt.okB_ok _ t hok) (.bound :: k) m
                  (fun q hq => by simp [List.isEmpty_iff.mp hv] at hq)
                obtain ⟨l, u, rfl⟩ := touched
                refine ⟨_, ?_, ⟨by simp [text], ((Keeps.refl m).location l).lastUsed u, hd, by simp⟩⟩
                have r := Interleave.reaches_of_local file labels run
                rcases hfr with ⟨rfl, rfl⟩ | rfl
                · simp only [List.nil_append] at r
                  exact (bound_reaches file labels ann e denv k m).trans
                    (r.trans (bound_value_reaches file labels _ k _))
                · simp only [List.singleton_append] at r
                  exact (bound_reaches file labels ann e denv k m).trans (r.trans (v_bound _ _ k _))
              · obtain ⟨m', r, post⟩ := evalP_val hcalls e env v outs h denv m hr hl hd hroom (.bound :: k)
                exact ⟨m', (bound_reaches file labels ann e denv k m).trans
                  (r.trans (bound_value_reaches file labels _ k m')), post⟩
            · obtain ⟨m', r, post⟩ := evalP_val hcalls e env v outs h denv m hr hl hd hroom (.bound :: k)
              exact ⟨m', (bound_reaches file labels ann e denv k m).trans
                (r.trans (bound_value_reaches file labels _ k m')), post⟩
    case sseq pat a b =>
      simp only [evalP] at h
      split at h
      · rename_i x o₁ hx
        split at h
        · rename_i xs hm
          split at h
          · rename_i hf
            obtain ⟨⟨r, o₂⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            simp only [List.length_append] at hroom
            obtain ⟨m₁, r₁, p₁⟩ := evalP_val hcalls a env x o₁ hx denv m hr hl hd (by omega)
              (.strongBind pat b denv :: k)
            have hl₁ : LitEnv ls (extendEnv (Fold.bmap xs) denv) m₁ :=
              (hl.keeps p₁.keeps).extend _ (fresh_bmap ls hf)
            obtain ⟨m₂, r₂, p₂⟩ := evalP_val hcalls b (Fold.extend xs env) v o₂ hb _ m₁ (hr.extend xs) hl₁
              p₁.dead (by have := p₁.room; omega) k
            refine ⟨m₂, ?_, p₁.trans p₂⟩
            refine (sequence_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
            refine (strongBind_reaches file labels pat b denv _ (Fold.bmap xs) ?_ k m₁).trans r₂
            rw [Fold.matchP_rv, hm]
            rfl
          · cases h
        · cases h
      · cases h
      · cases h
    case wseq pat a b =>
      simp only [evalP] at h
      split at h
      · rename_i x o₁ hx
        split at h
        · rename_i xs hm
          split at h
          · rename_i hf
            obtain ⟨⟨r, o₂⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            simp only [List.length_append] at hroom
            obtain ⟨m₁, r₁, p₁⟩ := evalP_val hcalls a env x o₁ hx denv m hr hl hd (by omega)
              (.effectBind pat b denv :: k)
            have hl₁ : LitEnv ls (extendEnv (Fold.bmap xs) denv) m₁ :=
              (hl.keeps p₁.keeps).extend _ (fresh_bmap ls hf)
            obtain ⟨m₂, r₂, p₂⟩ := evalP_val hcalls b (Fold.extend xs env) v o₂ hb _ m₁ (hr.extend xs) hl₁
              p₁.dead (by have := p₁.room; omega) k
            refine ⟨m₂, ?_, p₁.trans p₂⟩
            refine (wseq_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
            refine (effectBind_reaches file labels pat b denv _ (Fold.bmap xs) ?_ k m₁).trans r₂
            rw [Fold.matchP_rv, hm]
            rfl
          · cases h
        · cases h
      · cases h
      · cases h
    case run u l ps => exact (evalP_run_val ls calls h).elim
    all_goals simp [evalP] at h
  termination_by e => sizeOf e

/-- **The glue transfers to a saved label** with its folded arguments, printing the literals of
its statements, discarding the continuation up to the procedure. -/
theorem evalP_jump (hcalls : CallsOk file labels ls calls) {ps : List Sym} {tgt : EE} (l : Sym)
    (hlab : labels.lookup l = some (ps, tgt)) :
    ∀ (e : EE) (env : WEnv) (vs : List WVal) (outs : List Out),
    evalP file ls calls Return.fuel env e = some (.jump l vs, outs) → ps.length = vs.length →
    ∀ denv m, EnvSub env denv → LitEnv ls denv m → DeadBelow m →
    64 + 32 * outs.length ≤ m.lastAddress → ∀ k, hasBoundary k = false →
    ∃ m' denv', Reaches file labels ⟨.effectExpr e denv, k, m⟩
      ⟨.effectExpr tgt (extendEnv (ps.zip (vs.map rv)) denv'), [], m'⟩ ∧ Post m m' outs
  | .mk ann e, env, vs, outs, h, hlen, denv, m, hr, hl, hd, hroom, k, hk => by
    cases e
    case pure p =>
      simp [evalP] at h
    case bound e =>
      simp only [evalP] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · have glue : evalP file ls calls Return.fuel env e = some (.jump l vs, outs) := by
            split at h
            · simp at h
            · split at h
              · split at h
                · simp at h
                · exact h
              · exact h
          obtain ⟨m', denv', r, post⟩ := evalP_jump hcalls l hlab e env vs outs glue hlen denv m hr hl hd
            hroom (.bound :: k) (by simpa [hasBoundary] using hk)
          exact ⟨m', denv', (bound_reaches file labels ann e denv k m).trans r, post⟩
    case sseq pat a b =>
      simp only [evalP] at h
      split at h
      · rename_i x o₁ hx
        split at h
        · rename_i xs hm
          split at h
          · rename_i hf
            obtain ⟨⟨r, o₂⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            simp only [List.length_append] at hroom
            obtain ⟨m₁, r₁, p₁⟩ := evalP_val file labels ls calls hcalls a env x o₁ hx denv m hr hl hd
              (by omega) (.strongBind pat b denv :: k)
            have hl₁ : LitEnv ls (extendEnv (Fold.bmap xs) denv) m₁ :=
              (hl.keeps p₁.keeps).extend _ (fresh_bmap ls hf)
            obtain ⟨m₂, denv', r₂, p₂⟩ := evalP_jump hcalls l hlab b (Fold.extend xs env) vs o₂ hb hlen _ m₁
              (hr.extend xs) hl₁ p₁.dead (by have := p₁.room; omega) k hk
            refine ⟨m₂, denv', ?_, p₁.trans p₂⟩
            refine (sequence_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
            refine (strongBind_reaches file labels pat b denv _ (Fold.bmap xs) ?_ k m₁).trans r₂
            rw [Fold.matchP_rv, hm]
            rfl
          · cases h
        · cases h
      · rename_i l' vs' o₁ hx
        simp only [Option.some.injEq, Prod.mk.injEq, Res.jump.injEq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        subst l' vs' o₁
        obtain ⟨m', denv', r, post⟩ := evalP_jump hcalls l hlab a env vs outs hx hlen denv m hr hl hd hroom
          (.strongBind pat b denv :: k) (by simpa [hasBoundary] using hk)
        exact ⟨m', denv', (sequence_reaches file labels ann pat a b denv k m).trans r, post⟩
      · cases h
    case wseq pat a b =>
      simp only [evalP] at h
      split at h
      · rename_i x o₁ hx
        split at h
        · rename_i xs hm
          split at h
          · rename_i hf
            obtain ⟨⟨r, o₂⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            simp only [List.length_append] at hroom
            obtain ⟨m₁, r₁, p₁⟩ := evalP_val file labels ls calls hcalls a env x o₁ hx denv m hr hl hd
              (by omega) (.effectBind pat b denv :: k)
            have hl₁ : LitEnv ls (extendEnv (Fold.bmap xs) denv) m₁ :=
              (hl.keeps p₁.keeps).extend _ (fresh_bmap ls hf)
            obtain ⟨m₂, denv', r₂, p₂⟩ := evalP_jump hcalls l hlab b (Fold.extend xs env) vs o₂ hb hlen _ m₁
              (hr.extend xs) hl₁ p₁.dead (by have := p₁.room; omega) k hk
            refine ⟨m₂, denv', ?_, p₁.trans p₂⟩
            refine (wseq_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
            refine (effectBind_reaches file labels pat b denv _ (Fold.bmap xs) ?_ k m₁).trans r₂
            rw [Fold.matchP_rv, hm]
            rfl
          · cases h
        · cases h
      · rename_i l' vs' o₁ hx
        simp only [Option.some.injEq, Prod.mk.injEq, Res.jump.injEq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        subst l' vs' o₁
        obtain ⟨m', denv', r, post⟩ := evalP_jump hcalls l hlab a env vs outs hx hlen denv m hr hl hd hroom
          (.effectBind pat b denv :: k) (by simpa [hasBoundary] using hk)
        exact ⟨m', denv', (wseq_reaches file labels ann pat a b denv k m).trans r, post⟩
      · cases h
    case run u l' qs =>
      cases qs with
      | nil => simp [evalP] at h
      | cons p rest =>
        simp only [evalP, Option.map_eq_some_iff, Prod.mk.injEq, Res.jump.injEq] at h
        obtain ⟨ws, hws, ⟨rfl, rfl⟩, rfl⟩ := h
        obtain ⟨v, vs, hp, hvs, rfl⟩ := Fold.mapM_cons_some hws
        refine ⟨focusMemory ann m, denv, ?_, Post.focus hd ann⟩
        refine (run_reaches file labels ann u l' p rest denv k m).trans ?_
        simpa using run_chain_sub file labels hr l' hlab k hk (focusMemory ann m) rest p [] v vs hp hvs
          (by simpa using hlen)
    all_goals simp [evalP] at h
  termination_by e => sizeOf e

end Glue

/-! ## Calls of `void` procedures that print -/

section Callee
variable (file : Program) (labels : Labels) (ls : List (Sym × List Int))

open ReturnConst (Reaches focusMemory)

theorem calleeOuts_parts {g : Sym} {outs : List Out} (h : calleeOuts file ls g = some outs) :
    ∃ body, calleeBody file g = some body ∧ ∃ a, fallGlue body = some a ∧
      (match evalP file ls (fun _ => none) Return.fuel ∅ a with
       | some (.val _, outs) => some outs
       | _ => none) = some outs := by
  unfold calleeOuts at h
  cases hb : calleeBody file g with
  | none => simp [hb] at h
  | some body =>
    cases ha : fallGlue body with
    | none => simp [hb, ha] at h
    | some a =>
      exact ⟨body, rfl, a, ha, by simpa [hb, ha] using h⟩

/-- The facts `calleeBody` checks. -/
theorem calleeBody_spec {g : Sym} {body : EE} (h : calleeBody file g = some body) :
    ∃ loc attrs rty variadic proto dloc marker bt,
      file.stdlib.lookup g = none ∧
      file.funInfo.lookup g = some (loc, attrs, rty, [], variadic, proto) ∧
      file.funs.lookup g = some (.procedure dloc marker bt [] body) ∧
      Call.retKind rty = some false := by
  unfold calleeBody at h
  split at h
  · cases h
  rename_i hstd
  split at h
  · rename_i loc attrs rty variadic proto hinfo
    split at h
    · rename_i hk
      split at h
      · rename_i dloc marker bt body' hdecl
        cases h
        exact ⟨loc, attrs, rty, variadic, proto, dloc, marker, bt, by simpa using hstd, hinfo, hdecl,
          hk⟩
      · cases h
    · cases h
  · cases h

theorem Post.focus_right {m m' : Mem.Concrete.State} {outs : List Out} (h : Post m m' outs)
    (ann : List Annot) : Post m (focusMemory ann m') outs := by
  simpa using h.trans (Post.focus h.dead ann)

/-- **A call of a `void` procedure that prints** (`calleeOuts`) prints its literals and returns
`unit`: the call's type checks (`Call.callSite`), the procedure's body over its return frame (the
glue by `evalP_val`, then the default of the return label), the return to the caller. -/
theorem calleeOuts_ok : CallsOk file labels ls (calleeOuts file ls) := by
  intro e outs hco denv m hl hd hroom k
  unfold callOuts at hco
  split at hco
  · rename_i g xs hs hx
    split at hco
    · rename_i hfresh
      obtain ⟨body, hbody, a, ha, he⟩ := calleeOuts_parts file ls hco
      obtain ⟨loc, attrs, fty, variadic, proto, dloc, marker, bt, hstd, hinfo, hdecl, hfk⟩ :=
        calleeBody_spec file hbody
      unfold fallGlue at ha
      split at ha
      · rename_i ann0 pann0 bt0 a' sann lab r pinfo dann bann pann' r'
        split at ha
        · rename_i hr
          cases ha
          split at he
          · rename_i w outs' heval
            cases he
            unfold Call.callSite at hs
            split at hs
            · rename_i ann pann p pbt fann vann g' lann tann fa fty' fbt pa pty pbt' w1a w1 w2a w2 cann
                cpann p₁ iann oann lenann len lnann pty₁ zann z iann' cpa cva rty cfa fty₁ ccann mt pann₂
                p₂ no1 no2
              split at hs
              · rename_i cond
                obtain ⟨hp₁, hp₂, hpty, hfty, hne, hpf, hpp, rfl, hlen⟩ := cond
                have hrk : Call.retKind rty = some false ∧ g' = g := by
                  cases h : Call.retKind rty with
                  | none => simp [h] at hs
                  | some b =>
                    simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                    exact ⟨by rw [hs.2], hs.1⟩
                obtain ⟨hrk, rfl⟩ := hrk
                simp only [siteSyms, Option.some.injEq] at hx
                subst hx
                simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
                  List.all_eq_true, bne_iff_ne, ne_eq] at hfresh
                obtain ⟨fp_, fty_, pty_⟩ := hfresh
                let fp : Val := .loaded (.specified (.pointer (.function g')))
                let env₁ := extendEnv [(p, fp)] denv
                let env₂ := extendEnv [(fty', (.ctype fty : Val)), (pty, .list .ctype [])] env₁
                have l1 : env₁.lookup p₁ = some fp := ConvInt.lookup_one hp₁
                have l2 : env₂.lookup pty₁ = some (.list .ctype []) :=
                  Call.lookup_ext2_second hpty (fun h => hne h.symm)
                have l3 : env₂.lookup fty₁ = some (.ctype fty) := Call.lookup_ext2_first hfty
                have l4 : env₂.lookup p₂ = some fp := by
                  rw [Call.lookup_ext2_other (by rw [hp₂]; exact hpf) (by rw [hp₂]; exact hpp)]
                  exact ConvInt.lookup_one hp₂
                have hmatch : matchPattern (.mk tann (.ctor .tuple [.mk fa (.base (some fty', fbt)),
                    .mk pa (.base (some pty, pbt')), .mk w1a (.base (none, w1)),
                    .mk w2a (.base (none, w2))]))
                    (.tuple [.ctype fty, .list .ctype (([] : List (Option Sym × Ctype)).map
                      fun q => .ctype q.2), boolean variadic, boolean proto]) =
                    some [(fty', .ctype fty), (pty, .list .ctype [])] := rfl
                let m₁ := SeqReach.focusMemory fann m
                let m₂ := SeqReach.focusMemory lann m₁
                let m₃ := SeqReach.focusMemory iann m₂
                let m₄ := SeqReach.focusMemory iann' m₃
                let m₅ := focusMemory ccann m₄
                let env₃ := extendEnv ((([] : List (Sym × BaseType)).map Prod.fst).zip ([] : List Val))
                  env₂
                let SAVE : EE := .mk sann (.save lab [(r, (pinfo, .mk dann () (.val .unit)))]
                  (.mk bann (.pure (.mk pann' () (.sym r')))))
                let L := CallReach.bodyLabels (.mk ann0 (.sseq (.mk pann0 (.base (none, bt0))) a SAVE))
                have post₅ : Post m m₅ [] :=
                  ((((Post.focus hd fann).focus_right lann).focus_right iann).focus_right iann').focus_right
                    ccann
                have hl₅ : LitEnv ls env₃ m₅ := by
                  refine ((hl.keeps post₅.keeps).extend _ ?_).extend _ ?_ |>.extend _ ?_
                  · intro x hx y hy
                    simp only [List.mem_singleton] at hx
                    subst hx
                    exact fp_ y hy
                  · intro x hx y hy
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl
                    · exact fty_ y hy
                    · exact pty_ y hy
                  · intro x hx
                    simp at hx
                obtain ⟨m₆, r₆, p₆⟩ := evalP_val file labels ls (fun _ => none) (callsOk_none file labels ls)
                  a ∅ w outs heval env₃ m₅ (Fold.EnvSub.empty _) hl₅ post₅.dead
                  (by have := post₅.room; simp at this; omega)
                  (.strongBind (.mk pann0 (.base (none, bt0))) SAVE env₃ :: .procedureReturn L :: k)
                let m₇ := focusMemory sann m₆
                refine ⟨focusMemory bann m₇, ?_, by
                  simpa using ((post₅.trans p₆).focus_right sann).focus_right bann⟩
                refine (SeqReach.sseq_pure_reaches ann fann (pat := .mk pann (.base (some p, pbt)))
                  (xs := [(p, fp)]) (SeqReach.pure_value vann (.loaded (.specified (.pointer
                    (.function g')))) denv) rfl k m).trans ?_
                refine (SeqReach.effect_let_reaches lann (Call.cfunction_reaches l1 hinfo) hmatch k m₁).trans ?_
                refine (SeqReach.effect_if_reaches iann true (Call.pureEval_of (Call.length_eval hlen l2)) k
                  m₂).trans ?_
                refine (SeqReach.effect_if_reaches iann' true (Call.compatible_reaches hrk hfk l3) k m₃).trans ?_
                refine (CallReach.ccall_reaches ccann mt (SeqReach.pure_symbol pann₂ p₂ env₂ fp l4) .nil
                  (CallReach.procedure_not_builtin hdecl) (CallReach.procedure_body hstd hdecl rfl) k
                  m₄).trans ?_
                refine (ReturnConst.sequence_reaches file labels ann0 _ a SAVE env₃ _ m₅).trans
                  (r₆.trans ?_)
                refine (ReturnConst.wildcard_sequence_reaches file labels pann0 bt0 _ SAVE env₃ _ m₆).trans ?_
                refine (ReturnConst.save_reaches file labels sann _ r pinfo _ _ env₃ _ m₆).trans ?_
                refine (ReturnConst.pure_value_reaches file labels dann .unit env₃ _ _).trans ?_
                refine (ReturnConst.saveArgument_reaches file labels r .unit _ env₃ _ m₇).trans ?_
                refine (ReturnConst.effect_pure_reaches file labels bann _ (env₃.insert r .unit) _
                  m₇).trans ?_
                refine (ReturnConst.pure_sym_reaches file labels pann' r r' hr.symm .unit env₃ _ _).trans ?_
                refine (ReturnConst.diagnostic_reaches file labels m₇.currentLocation .unit _ _).trans ?_
                exact CallReach.return_reaches .unit L k _
              · cases hs
            · cases hs
          · cases he
        · cases ha
      · cases ha
    · cases hco
  · cases hco

end Callee

theorem recognize_parts {doc : Codec.Document} {n : Int} {outs : List Out}
    (h : recognize doc = some (n, outs)) :
    ∃ ls sym loc marker ty body, litsOf doc.file = some ls ∧ doc.file.main = some sym ∧
      doc.file.funs.lookup sym = some (.procedure loc marker ty [] body) ∧
      recognizeBody doc.file ls body = some (n, outs) := by
  unfold recognize at h
  cases hls : litsOf doc.file with
  | none => simp [hls] at h
  | some ls =>
    cases main : doc.file.main with
    | none => simp [hls, main] at h
    | some sym =>
      cases decl : doc.file.funs.lookup sym with
      | none => simp [hls, main, decl] at h
      | some entry =>
        cases entry <;> try { simp [hls, main, decl] at h }
        case procedure loc marker ty ps body =>
          cases ps with
          | cons p ps => simp [hls, main, decl] at h
          | nil =>
            exact ⟨ls, sym, loc, marker, ty, body, rfl, rfl, decl, by simpa [hls, main, decl] using h⟩

/-- **Core side.** A recognised document exits with `n mod 256` after printing the literals, for
every argument list. -/
theorem recognize_sound (doc : Codec.Document) {n : Int} {outs : List Out}
    (h : recognize doc = some (n, outs)) (args : List String) :
    Spec.CoreBeh doc args (.exit (n % 256).toNat (outBytes outs)) := by
  obtain ⟨ls, sym, loc, marker, ty, body, hls, main, decl, hb⟩ := recognize_parts h
  obtain ⟨s, m, env, xs, hinit, hout, hlit, hdead, hlast, hentry⟩ :=
    StrLit.initial_reaches_body doc.file (Map.ofList (doc.enumBindings.getD [])) args hls main decl
  unfold recognizeBody at hb
  split at hb
  · rename_i ann pat a sann ret bt x info tann pann u y
    split at hb
    · rename_i hc
      obtain ⟨hxy, hs⟩ := hc
      split at hb
      · rename_i l n' outs' he
        split at hb
        · rename_i hl
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨h1, h2⟩ := hb
          subst n' outs'
          let file := doc.file
          let tgt : EE := .mk tann (.pure (.mk pann u (.sym y)))
          let labels : Labels := Map.ofList (saves (.mk ann (.sseq pat a
            (.mk sann (.save (ret, bt) [(x, info)] tgt))))).reverse
          have hlab : labels.lookup l = some ([x], tgt) := by
            simp only [labels, saves, ReturnLit.saves_saveFree a hs, tgt]
            simp only [Map.ofList, Map.lookup, Map.insert]
            rw [hl.1]
            simp
          let w : WVal := .loaded (.specified (.integer n))
          have hdb : DeadBelow m := by intro j hj; rw [hdead] at hj; cases hj
          obtain ⟨m₁, denv, r₁, post⟩ := evalP_jump file labels ls (calleeOuts file ls)
            (calleeOuts_ok file labels ls) l hlab a ∅ [w] outs he rfl env m
            (Fold.EnvSub.empty env) hlit hdb (by
              have := hl.2
              have : (2 : Int) ^ 47 ≤ m.lastAddress := hlast
              omega)
            (.strongBind pat (.mk sann (.save (ret, bt) [(x, info)] tgt)) env :: [.annotations xs])
            (by simp [hasBoundary])
          have henv : extendEnv ([x].zip ([w].map runtimeValue)) denv =
              denv.insert x (runtimeValue w) := rfl
          have reach : Spec.CoreReach doc args ⟨.halt (.defined (.loaded (.specified (.integer n)))), [],
              ReturnConst.focusMemory tann m₁⟩ := by
            refine ⟨s, labels, hinit, hentry.trans ?_⟩
            refine (ReturnConst.sequence_reaches file labels ann pat a _ env _ m).trans (r₁.trans ?_)
            refine (ReturnConst.effect_pure_reaches file labels tann _ _ [] m₁).trans ?_
            rw [henv]
            cases u
            refine (ReturnConst.pure_sym_reaches file labels pann x y hxy _ denv _ _).trans ?_
            refine (ReturnConst.diagnostic_reaches file labels m₁.currentLocation _ [] _).trans ?_
            exact ReturnConst.value_halts file labels _ _
          have beh := Spec.CoreBeh.exit (k := (n % 256).toNat) reach rfl rfl
          have hst : m₁.stdout = text outs := by
            rw [post.stdout, hout]
            simp
          simpa [hst, coreBytes_text] using beh
        · cases hb
      · rename_i outs' he
        split at hb
        · rename_i hc
          obtain ⟨hw, hz, hlen⟩ := hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨h1, h2⟩ := hb
          subst n outs'
          obtain ⟨pann0, bt0, rfl⟩ := noBind_inv hw
          obtain ⟨info1, p⟩ := info
          cases u
          let file := doc.file
          let tgt : EE := .mk tann (.pure (.mk pann () (.sym y)))
          let labels : Labels := Map.ofList (saves (.mk ann (.sseq (.mk pann0 (.base (none, bt0))) a
            (.mk sann (.save (ret, bt) [(x, (info1, p))] tgt))))).reverse
          have hdb : DeadBelow m := by intro j hj; rw [hdead] at hj; cases hj
          obtain ⟨m₁, r₁, post⟩ := evalP_val file labels ls (calleeOuts file ls)
            (calleeOuts_ok file labels ls) a ∅ .unit outs he env m
            (Fold.EnvSub.empty env) hlit hdb (by
              have : (2 : Int) ^ 47 ≤ m.lastAddress := hlast
              omega)
            (.strongBind (.mk pann0 (.base (none, bt0))) (.mk sann (.save (ret, bt) [(x, (info1, p))] tgt))
              env :: [.annotations xs])
          obtain ⟨m', hst', r₂⟩ := StateGlobals.main_falls (file := file) (labels := labels) hxy.symm hz
            env xs none m₁
          have reach : Spec.CoreReach doc args ⟨.halt (.defined (.loaded (.specified (.integer 0)))), [],
              m'⟩ := by
            refine ⟨s, labels, hinit, hentry.trans ?_⟩
            exact (ReturnConst.sequence_reaches file labels ann _ a _ env _ m).trans (r₁.trans r₂)
          have beh := Spec.CoreBeh.exit (k := ((0 : Int) % 256).toNat) reach rfl rfl
          have hst : m'.stdout = text outs := by
            rw [hst', post.stdout, hout]
            simp
          simpa [hst, coreBytes_text] using beh
        · cases hb
      · cases hb
    · cases hb
  · cases hb

/-! ## The machine side -/

/-- The bytes of characters, as output items. -/
def charItems (s : List Char) : List PrintLink.Item := s.map fun c => .byte c.toNat.toUInt8

/-- One statement's output items: the literal bytes, and the integer of a `%d`, whose digits the
machine code computes. -/
def Out.items : Out → List PrintLink.Item
  | .lit cs => charItems (plainText cs).toList
  | .dec pre suf n => charItems pre ++ .int n :: charItems suf

/-- The output items of the statements. -/
def items (outs : List Out) : List PrintLink.Item := outs.flatMap Out.items

theorem render_append (a b : List PrintLink.Item) :
    PrintLink.render (a ++ b) = PrintLink.render a ++ PrintLink.render b := by
  simp [PrintLink.render]

theorem render_cons (i : PrintLink.Item) (l : List PrintLink.Item) :
    PrintLink.render (i :: l) = i.render ++ PrintLink.render l := by
  simp [PrintLink.render]

theorem render_charItems (s : List Char) :
    PrintLink.render (charItems s) = s.map fun c => c.toNat.toUInt8 := by
  induction s with
  | nil => rfl
  | cons c s ih => rw [charItems, List.map_cons, render_cons, ← charItems, ih]; rfl

theorem Out.render_items (o : Out) : PrintLink.render o.items = Spec.coreBytes o.text := by
  cases o with
  | lit cs => simp only [Out.items, Out.text, render_charItems, Spec.coreBytes]
  | dec pre suf n =>
    simp only [Out.items, Out.text, PrintfIntStmt.text, render_append, render_cons, render_charItems,
      PrintLink.Item.render, Spec.coreBytes, String.toList_append, String.toList_ofList, List.map_append]

theorem render_items (outs : List Out) : PrintLink.render (items outs) = outBytes outs := by
  induction outs with
  | nil => rfl
  | cons o outs ih =>
    rw [items, List.flatMap_cons, render_append, Out.render_items, ← items, ih]
    rfl

end Silmaril.Compile.Core.Verified.Printf
