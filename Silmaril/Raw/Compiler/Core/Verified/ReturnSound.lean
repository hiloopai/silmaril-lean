module

public import Silmaril.Compiler.Core.Verified.Return.Defs
public import Silmaril.Compiler.Core.Verified.FoldSound.Defs

/-! # Core side: `main` returning a closed integer expression

`recognize_sound`: when `Return.recognize doc = some n`, the Core dynamics, from the document's
initial state, reaches `halt (defined (Specified n))` with empty stdout, so
`CoreBeh doc args (exit (n mod 256) [])`.

The glue lemmas are parametric in the environment, the continuation and the memory:
`evalE_val` (the glue reduces to its folded value) and `evalE_jump` (the glue transfers to the
saved label with its folded arguments, discarding the continuation up to the procedure).
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Return

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold
open ReturnConst (Reaches next_reaches update_reaches focusMemory focusMemory_stdout effect_pure_reaches
  diagnostic_reaches sequence_reaches pure_sym_reaches value_halts_annotations)

local notation "rv" => runtimeValue

section Steps
variable (file : Program) (labels : Labels)

theorem procedureContext_nb (k : List Frame) (h : hasBoundary k = false) :
    procedureContext labels k = (labels, []) := by
  induction k with
  | nil => rfl
  | cons f k ih =>
    cases f <;> simp_all [hasBoundary, procedureContext]

theorem request_run (ann : List Annot) (u : Unit) (l : Sym) (p : PE) (rest : List PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    request file labels ⟨.effectExpr (.mk ann (.run u l (p :: rest))) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.runLabel l [] rest env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.runLabel l [] rest env :: k) := by
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.runLabel l [] rest env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.runLabel l [] rest env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem run_reaches (ann : List Annot) (u : Unit) (l : Sym) (p : PE) (rest : List PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.run u l (p :: rest))) env, k, m⟩
      ⟨.pureExpr p env, .runLabel l [] rest env :: k, focusMemory ann m⟩ := by
  unfold focusMemory
  split
  · rename_i loc found
    split
    · rename_i lib
      apply next_reaches <;> simp_all [request_run, focusMemory]
    · rename_i lib
      by_cases equal : loc == m.currentLocation
      · have eq : loc = m.currentLocation := by simpa using equal
        subst loc
        apply next_reaches <;> simp_all [request_run, focusMemory]
      · apply Relation.ReflTransGen.trans (b :=
          ⟨.setLocation loc (.pureExpr p env), .runLabel l [] rest env :: k, m⟩)
        · apply next_reaches <;> simp_all [request_run, focusMemory]
        · apply update_reaches <;> simp [request, requestAux, awaitsScheduling]
  · rename_i found
    have focus : focusMemory ann m = m := by
      unfold focusMemory
      rw [found]
    apply next_reaches
    · intro o; simp
    · rw [request_run]
      simp [focus]

theorem bound_reaches (ann : List Annot) (e : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
      ⟨.effectExpr e env, .bound :: k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem bound_value_reaches (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .bound :: k, m⟩ ⟨.value v, k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem wseq_reaches (ann : List Annot) (pat : Pattern Sym) (a b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.wseq pat a b)) env, k, m⟩
      ⟨.effectExpr a env, .effectBind pat b env :: k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem strongBind_reaches (pat : Pattern Sym) (b : EE) (env : Env) (v : Val) (xs : Bindings)
    (h : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .strongBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv xs env), k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, h]

theorem effectBind_reaches (pat : Pattern Sym) (b : EE) (env : Env) (v : Val) (xs : Bindings)
    (h : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .effectBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv xs env), k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, h]

/-- The arguments of a transfer, then the transfer itself, outside any nested procedure. -/
theorem run_chain {env : WEnv} {denv : Env} (hr : EnvRel env denv) (l : Sym)
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
    refine (eval_reaches file labels _ env p v hp denv hr _ m).trans ?_
    apply next_reaches
    · intro o; simp
    · simp at hlen
      simp [request, requestAux, awaitsScheduling, requestJump, hk, jump, jumpDestination,
        procedureContext_nb labels k hk, hl, hlen]
  | q :: rest, p, done, v, vs, hp, hvs, hlen => by
    obtain ⟨w, ws, hq, hws, rfl⟩ := mapM_cons_some hvs
    refine (eval_reaches file labels _ env p v hp denv hr _ m).trans ?_
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr q denv, .runLabel l (done ++ [rv v]) rest denv :: k, m⟩) ?_ ?_
    · apply next_reaches
      · intro o; simp
      · simp [request, requestAux, awaitsScheduling]
    · simpa using run_chain hr l hl k hk m rest q (done ++ [rv v]) w ws hq hws (by simpa using hlen)

end Steps

/-! ## The glue -/

section Glue
variable (file : Program) (labels : Labels)

theorem evalE_run_val {doc : Doc} {env : WEnv} {ann : List Annot} {u : Unit} {l : Sym} {ps : List PE}
    {v : WVal}
    (h : evalE doc Return.fuel env (.mk ann (.run u l ps)) = some (.val v)) : False := by
  cases ps with
  | nil => simp [evalE] at h
  | cons p ps =>
    simp only [evalE, Option.map_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    cases h

theorem evalE_val : ∀ (e : EE) (env : WEnv) (v : WVal), evalE file Return.fuel env e = some (.val v) →
    ∀ denv, EnvRel env denv → ∀ k m, ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e denv, k, m⟩ ⟨.value (rv v), k, m'⟩
  | .mk ann e, env, v, h, denv, hr, k, m => by
    cases e
    case pure p =>
      simp only [evalE, Option.map_eq_some_iff, Res.val.injEq] at h
      obtain ⟨w, hw, rfl⟩ := h
      refine ⟨focusMemory ann m, focusMemory_stdout ann m, ?_⟩
      exact (effect_pure_reaches file labels ann p denv k m).trans
        ((eval_reaches file labels _ env p w hw denv hr _ _).trans
          (diagnostic_reaches file labels m.currentLocation _ k _))
    case bound e =>
      simp only [evalE] at h
      obtain ⟨m', out, r⟩ := evalE_val e env v h denv hr (.bound :: k) m
      exact ⟨m', out, (bound_reaches file labels ann e denv k m).trans
        (r.trans (bound_value_reaches file labels _ k m'))⟩
    case sseq pat a b =>
      simp only [evalE] at h
      split at h
      · rename_i x hx
        split at h
        · rename_i xs hm
          obtain ⟨m₁, out₁, r₁⟩ := evalE_val a env x hx denv hr (.strongBind pat b denv :: k) m
          obtain ⟨m₂, out₂, r₂⟩ := evalE_val b (Fold.extend xs env) v h _ (hr.extend xs) k m₁
          refine ⟨m₂, out₂.trans out₁, ?_⟩
          refine (sequence_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
          refine (strongBind_reaches file labels pat b denv _ (bmap xs) ?_ k m₁).trans r₂
          rw [matchP_rv, hm]
          rfl
        · cases h
      · cases h
      · cases h
    case wseq pat a b =>
      simp only [evalE] at h
      split at h
      · rename_i x hx
        split at h
        · rename_i xs hm
          obtain ⟨m₁, out₁, r₁⟩ := evalE_val a env x hx denv hr (.effectBind pat b denv :: k) m
          obtain ⟨m₂, out₂, r₂⟩ := evalE_val b (Fold.extend xs env) v h _ (hr.extend xs) k m₁
          refine ⟨m₂, out₂.trans out₁, ?_⟩
          refine (wseq_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
          refine (effectBind_reaches file labels pat b denv _ (bmap xs) ?_ k m₁).trans r₂
          rw [matchP_rv, hm]
          rfl
        · cases h
      · cases h
      · cases h
    case run u l ps => exact (evalE_run_val h).elim
    all_goals simp [evalE] at h
  termination_by e => sizeOf e

theorem evalE_jump {ps : List Sym} {tgt : EE} (l : Sym) (hl : labels.lookup l = some (ps, tgt)) :
    ∀ (e : EE) (env : WEnv) (vs : List WVal), evalE file Return.fuel env e = some (.jump l vs) →
    ps.length = vs.length → ∀ denv, EnvRel env denv → ∀ k m, hasBoundary k = false →
    ∃ m' denv', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e denv, k, m⟩
      ⟨.effectExpr tgt (extendEnv (ps.zip (vs.map rv)) denv'), [], m'⟩
  | .mk ann e, env, vs, h, hlen, denv, hr, k, m, hk => by
    cases e
    case pure p =>
      simp [evalE] at h
    case bound e =>
      simp only [evalE] at h
      obtain ⟨m', denv', out, r⟩ := evalE_jump l hl e env vs h hlen denv hr (.bound :: k) m
        (by simpa [hasBoundary] using hk)
      exact ⟨m', denv', out, (bound_reaches file labels ann e denv k m).trans r⟩
    case sseq pat a b =>
      simp only [evalE] at h
      split at h
      · rename_i x hx
        split at h
        · rename_i xs hm
          obtain ⟨m₁, out₁, r₁⟩ := evalE_val file labels a env x hx denv hr (.strongBind pat b denv :: k) m
          obtain ⟨m₂, denv', out₂, r₂⟩ := evalE_jump l hl b (Fold.extend xs env) vs h hlen _
            (hr.extend xs) k m₁ hk
          refine ⟨m₂, denv', out₂.trans out₁, ?_⟩
          refine (sequence_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
          refine (strongBind_reaches file labels pat b denv _ (bmap xs) ?_ k m₁).trans r₂
          rw [matchP_rv, hm]
          rfl
        · cases h
      · rename_i l' vs' hx
        simp only [Option.some.injEq, Res.jump.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m', denv', out, r⟩ := evalE_jump l' hl a env vs' hx hlen denv hr
          (.strongBind pat b denv :: k) m (by simpa [hasBoundary] using hk)
        exact ⟨m', denv', out, (sequence_reaches file labels ann pat a b denv k m).trans r⟩
      · cases h
    case wseq pat a b =>
      simp only [evalE] at h
      split at h
      · rename_i x hx
        split at h
        · rename_i xs hm
          obtain ⟨m₁, out₁, r₁⟩ := evalE_val file labels a env x hx denv hr (.effectBind pat b denv :: k) m
          obtain ⟨m₂, denv', out₂, r₂⟩ := evalE_jump l hl b (Fold.extend xs env) vs h hlen _
            (hr.extend xs) k m₁ hk
          refine ⟨m₂, denv', out₂.trans out₁, ?_⟩
          refine (wseq_reaches file labels ann pat a b denv k m).trans (r₁.trans ?_)
          refine (effectBind_reaches file labels pat b denv _ (bmap xs) ?_ k m₁).trans r₂
          rw [matchP_rv, hm]
          rfl
        · cases h
      · rename_i l' vs' hx
        simp only [Option.some.injEq, Res.jump.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m', denv', out, r⟩ := evalE_jump l' hl a env vs' hx hlen denv hr
          (.effectBind pat b denv :: k) m (by simpa [hasBoundary] using hk)
        exact ⟨m', denv', out, (wseq_reaches file labels ann pat a b denv k m).trans r⟩
      · cases h
    case run u l' qs =>
      cases qs with
      | nil => simp [evalE] at h
      | cons p rest =>
        simp only [evalE, Option.map_eq_some_iff, Res.jump.injEq] at h
        obtain ⟨ws, hws, rfl, rfl⟩ := h
        obtain ⟨v, vs, hp, hvs, rfl⟩ := mapM_cons_some hws
        refine ⟨focusMemory ann m, denv, focusMemory_stdout ann m, ?_⟩
        refine (run_reaches file labels ann u l' p rest denv k m).trans ?_
        simpa using run_chain file labels hr l' hl k hk (focusMemory ann m) rest p [] v vs hp hvs
          (by simpa using hlen)
    all_goals simp [evalE] at h
  termination_by e => sizeOf e

end Glue

/-! ## The whole document -/

theorem simple_saves : ∀ e : EE, simple e = true → saves e = []
  | .mk ann e, h => by
    cases e
    case sseq pat a b =>
      simp only [simple, Bool.and_eq_true] at h
      simp [saves, simple_saves a h.1, simple_saves b h.2]
    case wseq pat a b =>
      simp only [simple, Bool.and_eq_true] at h
      simp [saves, simple_saves a h.1, simple_saves b h.2]
    all_goals simp_all [simple, saves]
  termination_by e => sizeOf e

/-- The startup of `StartupReach.initial_reaches_body`, with `main`'s saved labels named. -/
theorem startup_reaches (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s m xs, initial file enums args = .ok (s, Map.ofList (saves body).reverse) ∧ m.stdout = "" ∧
      Reaches file (Map.ofList (saves body).reverse) s ⟨.effectExpr body ∅, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  obtain ⟨m', xs, out, reach⟩ := StartupReach.startup_errno file labels (.effectExpr body ∅)
    ({enumTypes := enums} : Mem.Concrete.State) rfl rfl
  refine ⟨_, m', xs, ?_, by simpa using out,
    (StartupReach.enter_main_reaches file labels args ∅ _ main decl).trans reach⟩
  simp only [initial]
  rw [List.filterMap_eq_nil_iff.mpr]
  · simp [main, decl]
  · rintro ⟨_, _ | _⟩ hx
    · exact absurd rfl (nodefs _ hx _ _)
    · rfl

theorem recognizeBody_reaches (file : Program) (body : EE) (n : Int)
    (h : recognizeBody file body = some n) (xs : List Access) (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file (Map.ofList (saves body).reverse)
      ⟨.effectExpr body ∅, [.annotations xs], m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ := by
  unfold recognizeBody at h
  split at h
  · rename_i ann pat a sann ret bt x info tann pann u y
    split at h
    · rename_i hc
      obtain ⟨hxy, hs⟩ := hc
      split at h
      · rename_i l n' hj
        split at h
        · rename_i hl
          cases h
          let tgt : EE := .mk tann (.pure (.mk pann u (.sym y)))
          let labels : Labels := Map.ofList (saves (.mk ann (.sseq pat a
            (.mk sann (.save (ret, bt) [(x, info)] tgt))))).reverse
          have hlab : labels.lookup l = some ([x], tgt) := by
            simp only [labels, saves, simple_saves a hs, tgt]
            simp only [Map.ofList, Map.lookup, Map.insert]
            rw [hl]
            simp
          let w : WVal := .loaded (.specified (.integer n))
          obtain ⟨m₁, denv, out₁, r₁⟩ := evalE_jump file labels l hlab a ∅ [w] hj rfl ∅ EnvRel.empty
            (.strongBind pat (.mk sann (.save (ret, bt) [(x, info)] tgt)) ∅ :: [.annotations xs]) m
            (by simp [hasBoundary])
          refine ⟨focusMemory tann m₁, (focusMemory_stdout tann m₁).trans out₁, ?_⟩
          refine (sequence_reaches file labels ann pat a _ ∅ _ m).trans (r₁.trans ?_)
          refine (effect_pure_reaches file labels tann _ _ [] m₁).trans ?_
          have henv : extendEnv ([x].zip ([w].map rv)) denv = denv.insert x (rv w) := rfl
          rw [henv]
          cases u
          refine (pure_sym_reaches file labels pann x y hxy (rv w) denv _ _).trans ?_
          refine (diagnostic_reaches file labels m₁.currentLocation _ [] _).trans ?_
          have hw : rv w = .loaded (.specified (.integer n)) := rfl
          rw [hw]
          exact ReturnConst.value_halts file labels _ _
        · cases h
      · cases h
    · cases h
  · cases h

/-- The whole-document run: from the initial state (any arguments, any enum registrations), the
dynamics halts with `Specified n` and empty stdout. -/
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
          obtain ⟨s, m, xs, hinit, hout, hentry⟩ := startup_reaches doc.file enums args hdefs main decl
          obtain ⟨m', hout', hrun⟩ := recognizeBody_reaches doc.file body n hbody xs m
          exact ⟨s, _, _, hinit, hentry.trans hrun, rfl, hout'.trans hout⟩

/-- **Core side.** A recognised document exits with `n mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (h : recognize doc = some n)
    (args : List String) :
    Spec.CoreBeh doc args (.exit (n % 256).toNat []) := by
  obtain ⟨s, labels, t, hinit, reach, halt, out⟩ :=
    recognize_reaches doc n h (Map.ofList (doc.enumBindings.getD [])) args
  have beh := Spec.CoreBeh.exit (k := (n % 256).toNat) ⟨s, labels, hinit, reach⟩ halt rfl
  simpa [Spec.coreBytes, out] using beh

end Silmaril.Compile.Core.Verified.Return
