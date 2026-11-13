module

public import Silmaril.Compiler.Core.Verified.Fold.Defs
public import Silmaril.Compiler.Core.Verified.ReturnConst.Defs

/-! # The folder agrees with the Core dynamics

`eval_reaches`: if `Fold.eval` folds a pure expression to `v`, the dynamics reduces it to
`runtimeValue v` in every related environment, under every continuation, from every memory,
and leaves the memory unchanged. Each operator agrees with the dynamics' `primitive`, each
pattern with `matchPattern`, each function body with `functionBody`.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Fold

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ReturnConst (Reaches next_reaches)

local notation "rv" => runtimeValue

/-- The folder's environment, seen at run time. -/
def EnvRel (env : WEnv) (denv : Env) : Prop :=
  ∀ s, denv.lookup s = (env.lookup s).map runtimeValue

def bmap (xs : List (Sym × WVal)) : Bindings := xs.map fun (s, v) => (s, rv v)

theorem EnvRel.empty : EnvRel ∅ ∅ := by
  intro s
  simp [Map.lookup]

theorem EnvRel.insert {env : WEnv} {denv : Env} (h : EnvRel env denv) (s : Sym) (v : WVal) :
    EnvRel (env.insert s v) (denv.insert s (rv v)) := by
  intro t
  by_cases e : MapKey.key t = MapKey.key s
  · simp only [Map.lookup, Map.insert]
    rw [e, Finmap.lookup_insert, Finmap.lookup_insert]
    rfl
  · rw [Map.lookup_insert_of_key_ne _ _ e, Map.lookup_insert_of_key_ne _ _ e]
    exact h t

theorem EnvRel.extend {env : WEnv} {denv : Env} (h : EnvRel env denv) (xs : List (Sym × WVal)) :
    EnvRel (Fold.extend xs env) (extendEnv (bmap xs) denv) := by
  induction xs with
  | nil => simpa [Fold.extend, extendEnv, bmap] using h
  | cons x xs ih =>
    obtain ⟨s, v⟩ := x
    have := ih.insert s v
    simpa [Fold.extend, extendEnv, bmap, List.foldr] using this

theorem runtimeValues_eq (vs : List WVal) : runtimeValues vs = vs.map rv := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [runtimeValues, ih]

mutual
theorem matchP_rv : (p : Pattern Sym) → (v : WVal) →
    matchPattern p (rv v) = (matchP p v).map bmap
  | .mk _ (.base (none, _)), v => by simp [matchPattern, matchP, bmap]
  | .mk _ (.base (some s, _)), v => by simp [matchPattern, matchP, bmap]
  | .mk a (.ctor c ps), v => by
    cases c <;> cases v <;> try (simp [matchPattern, matchP, runtimeValue]; done)
    case nil.list ty' vs =>
      rcases ps with _ | ⟨p, ps⟩ <;> rcases vs with _ | ⟨w, ws⟩ <;>
        simp [matchPattern, matchP, runtimeValue, runtimeValues, bmap]
    case cons.list ty vs =>
      rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, rs⟩⟩⟩ <;> rcases vs with _ | ⟨w, ws⟩ <;>
        try (simp [matchPattern, matchP, runtimeValue, runtimeValues]; done)
      have hp := matchP_rv p w
      have hq := matchP_rv q (.list ty ws)
      simp only [runtimeValue] at hq
      simp only [matchPattern, matchP, runtimeValue, runtimeValues, hp, hq]
      cases matchP p w <;> cases matchP q (.list ty ws) <;> simp [bmap]
    case tuple.tuple vs =>
      simpa [matchPattern, matchP, runtimeValue] using matchPs_rv ps vs
    case specified.loaded lv =>
      rcases ps with _ | ⟨p, _ | ⟨q, qs⟩⟩ <;> rcases lv with w | ty <;>
        try (simp [matchPattern, matchP, runtimeValue, runtimeLoaded]; done)
      simpa [matchPattern, matchP, runtimeValue, runtimeLoaded] using matchP_rv p (.object w)
    case unspecified.loaded lv =>
      rcases ps with _ | ⟨p, _ | ⟨q, qs⟩⟩ <;> rcases lv with w | ty <;>
        try (simp [matchPattern, matchP, runtimeValue, runtimeLoaded]; done)
      simpa [matchPattern, matchP, runtimeValue, runtimeLoaded] using matchP_rv p (.ctype ty)
  termination_by p => sizeOf p
theorem matchPs_rv : (ps : List (Pattern Sym)) → (vs : List WVal) →
    matchPatterns ps (runtimeValues vs) = (matchPs ps vs).map bmap
  | p :: ps, v :: vs => by
    simp only [runtimeValues, matchPatterns, matchPs, matchP_rv p v, matchPs_rv ps vs]
    cases matchP p v <;> cases matchPs ps vs <;> simp [bmap]
  | [], _ => by simp [matchPatterns, matchPs, bmap]
  | _ :: _, [] => by simp [matchPatterns, matchPs, runtimeValues, bmap]
  termination_by ps => sizeOf ps
end

/-! ## Operators agree with `primitive` -/

@[simp] theorem rv_integer (n : Int) : rv (Fold.integer n) = Dynamics.integer n := rfl

@[simp] theorem rv_boolean (b : Bool) : rv (Fold.boolean b) = Dynamics.boolean b := by
  cases b <;> rfl

theorem bounds_registered {ty : IntegerType} {b : Int × Int} (h : bounds ty = some b)
    (tags : Mem.Concrete.Tags) : Mem.Concrete.registeredIntegerBounds tags ty = some b := by
  cases ty <;> simp_all [bounds, Mem.Concrete.registeredIntegerBounds, Mem.Concrete.registeredInteger]

theorem layout_registered {ty : IntegerType} {b : Int × Int} (h : bounds ty = some b)
    (tags : Mem.Concrete.Tags) :
    Mem.Concrete.registeredIntegerLayout tags ty = Mem.Concrete.integerLayout ty := by
  cases ty <;> simp_all [bounds, Mem.Concrete.registeredIntegerLayout, Mem.Concrete.registeredInteger]

theorem intType_sound {ty : Ctype} {a : IntegerType} (h : Fold.intType ty = some a) :
    Dynamics.intType ty = some a := by
  rcases ty with ⟨ann, ty⟩
  cases ty with
  | basic b =>
    cases b with
    | integer ity => cases ity <;> simp_all [Fold.intType, Dynamics.intType]
    | _ => simp [Fold.intType] at h
  | _ => simp [Fold.intType] at h

theorem intBin_rv {op : BinOp} {x y : Int} {r : WVal} (h : intBin op x y = some r) :
    integerBin op x y = some (rv r) := by
  cases op <;> simp only [intBin, integerBin] at h ⊢ <;> (try split at h) <;> (try split) <;>
    simp_all <;> (subst h; first | rfl | simp)

theorem bin_ok {op : BinOp} {a b r : WVal} (h : bin op a b = some r) (tags : Mem.Concrete.Tags) :
    primitive (.bin op) [rv a, rv b] tags = .ok (rv r) := by
  have rvi : ∀ n : Int, rv (.object (.integer n) : WVal) = .object (.integer n) := fun _ => rfl
  unfold bin at h
  split at h
  · rename_i x y
    rw [rvi, rvi]
    simp [primitive, intBin_rv h]
    rfl
  · rename_i x y
    split at h
    · rename_i a b ha hb
      split at h
      · rename_i hab
        simp at h hab
        subst h
        obtain ⟨ba, hba⟩ := Option.isSome_iff_exists.mp hab.1
        obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.mp hab.2
        simp [primitive, runtimeValue, intType_sound ha, intType_sound hb,
          bounds_registered hba, bounds_registered hbb]
        rfl
      · cases h
    · cases h
  all_goals (cases op <;> simp at h <;> subst h <;> simp [primitive, runtimeValue] <;> rfl)

theorem sizeof_ok {ty : Ctype} {r : WVal} (h : Fold.ctor .ivSizeof [.ctype ty] = some r)
    (tags : Mem.Concrete.Tags) :
    primitive (.ctor .ivSizeof) [rv (.ctype ty)] tags = .ok (rv r) := by
  simp only [Fold.ctor] at h
  cases hity : Fold.intType ty with
  | none => simp [hity] at h
  | some ity =>
    cases hb : bounds ity with
    | none => simp [hity, hb] at h
    | some b =>
      cases hl : Mem.Concrete.integerLayout ity with
      | none => simp [hity, hb, hl] at h
      | some l =>
        obtain ⟨w, sg⟩ := l
        simp [hity, hb, hl] at h
        subst h
        rcases ty with ⟨ann, ty⟩
        cases ty with
        | basic bt =>
          cases bt with
          | integer i =>
            have hi : i = ity := by
              have := intType_sound hity
              simpa [Dynamics.intType] using this
            subst hi
            simp [primitive, runtimeValue, Mem.Concrete.typeLayout, layout_registered hb tags, hl]
            rfl
          | _ => simp [Fold.intType] at hity
        | _ => simp [Fold.intType] at hity

theorem ctor_ok {c : Ctor} {vs : List WVal} {r : WVal} (h : Fold.ctor c vs = some r)
    (tags : Mem.Concrete.Tags) : primitive (.ctor c) (vs.map rv) tags = .ok (rv r) := by
  by_cases hc : c = .ivSizeof
  · subst hc
    rcases vs with _ | ⟨v, _ | ⟨v', vs⟩⟩
    · simp [Fold.ctor] at h
    · cases v
      case ctype ty => simpa using sizeof_ok h tags
      all_goals simp [Fold.ctor] at h
    · simp [Fold.ctor] at h
  unfold Fold.ctor at h
  split at h
  · cases h; simp [primitive, runtimeValue, runtimeObject, runtimeLoaded]; rfl
  · cases h; simp [primitive, runtimeValue, runtimeLoaded]; rfl
  · cases h; simp [primitive, runtimeValue, runtimeValues_eq]; rfl
  all_goals first
    | cases h
    | exact absurd rfl hc
    | rename_i ty
      cases hity : Fold.intType ty with
      | none => simp [hity] at h
      | some ity =>
        cases hb : bounds ity with
        | none => simp [hity, hb] at h
        | some b =>
          obtain ⟨lo, hi⟩ := b
          simp [hity, hb] at h
          subst h
          simp [primitive, runtimeValue, intType_sound hity, bounds_registered hb]
          rfl

theorem conv_ok {ty : IntegerType} {a r : WVal} (h : conv ty a = some r) (tags : Mem.Concrete.Tags) :
    primitive (.conv ty) [rv a] tags = .ok (rv r) := by
  unfold conv at h
  split at h
  · rename_i n
    cases hb : bounds ty with
    | none => simp [hb] at h
    | some b =>
      obtain ⟨lo, hi⟩ := b
      simp [hb] at h
      subst h
      simp [primitive, runtimeValue, runtimeObject, bounds_registered hb, Fold.wrap, Dynamics.wrap]
      rfl
  · cases h

theorem intOp_eq (op : IntOp) (x y : Int) : intOp op x y = integerOp op x y := by
  cases op <;> rfl

theorem catchInt_ok {ty : IntegerType} {op : IntOp} {a b r : WVal} (h : catchInt ty op a b = some r)
    (tags : Mem.Concrete.Tags) : primitive (.catchInt ty op) [rv a, rv b] tags = .ok (rv r) := by
  unfold catchInt at h
  split at h
  · rename_i x y
    cases hb : bounds ty with
    | none => simp [hb] at h
    | some b =>
      obtain ⟨lo, hi⟩ := b
      cases hn : intOp op x y with
      | none => simp [hb, hn] at h
      | some n =>
        rw [intOp_eq] at hn
        simp [hb, hn, intOp_eq] at h
        obtain ⟨hr, rfl⟩ := h
        simp [primitive, runtimeValue, runtimeObject, bounds_registered hb, hn, hr]
        rfl
  · cases h

theorem wrapInt_ok {ty : IntegerType} {op : IntOp} {a b r : WVal} (h : wrapInt ty op a b = some r)
    (tags : Mem.Concrete.Tags) : primitive (.wrapInt ty op) [rv a, rv b] tags = .ok (rv r) := by
  unfold wrapInt at h
  split at h
  · rename_i x y
    cases hb : bounds ty with
    | none => simp [hb] at h
    | some b =>
      obtain ⟨lo, hi⟩ := b
      cases hn : intOp op x y with
      | none => simp [hb, hn] at h
      | some n =>
        rw [intOp_eq] at hn
        simp [hb, hn, intOp_eq] at h
        subst h
        simp [primitive, runtimeValue, runtimeObject, bounds_registered hb, hn, Fold.wrap, Dynamics.wrap]
        rfl
  · cases h

theorem notBool_ok {a r : WVal} (h : notBool a = some r) (tags : Mem.Concrete.Tags) :
    primitive .notBool [rv a] tags = .ok (rv r) := by
  unfold notBool at h
  split at h <;> cases h <;> simp [primitive, runtimeValue] <;> rfl

theorem nonEnum_eq {x x' : IntegerType} (h : nonEnum x = some x') (enums : Map Sym IntegerType) :
    x' = x ∧ Core.normalizeInteger x enums = Core.normalizeInteger x := by
  cases x <;> simp [nonEnum] at h <;> subst h <;> exact ⟨rfl, rfl⟩

theorem compat_void (c d : List Annot) (tags : Mem.Concrete.Tags) :
    primitive .compatible [.ctype (.mk c .void), .ctype (.mk d .void)] tags = .ok .true := by
  simp [primitive, Core.compatibleWith, Core.noQualifiers, Dynamics.boolean]
  rfl

theorem compat_int {x y : IntegerType} {r : WVal} {c d : List Annot}
    (h : (do
      let a ← Core.normalizeInteger (← nonEnum x)
      let b ← Core.normalizeInteger (← nonEnum y)
      pure (boolean (a == b))) = some r) (tags : Mem.Concrete.Tags) :
    primitive .compatible [.ctype (.mk c (.basic (.integer x))), .ctype (.mk d (.basic (.integer y)))]
      tags = .ok (rv r) := by
  cases hx : nonEnum x with
  | none => simp [hx] at h
  | some x' =>
    cases hy : nonEnum y with
    | none => simp [hx, hy] at h
    | some y' =>
      obtain ⟨rfl, ex⟩ := nonEnum_eq hx tags.enums
      obtain ⟨rfl, ey⟩ := nonEnum_eq hy tags.enums
      cases hna : Core.normalizeInteger x' with
      | none => simp [hx, hy, hna] at h
      | some a =>
        cases hnb : Core.normalizeInteger y' with
        | none => simp [hx, hy, hnb] at h
        | some b =>
          simp [hx, hy, hna, hnb] at h
          subst h
          rcases Bool.eq_false_or_eq_true (a == b) with e | e <;>
            (simp [primitive, Core.compatibleWith, Core.noQualifiers, Core.compatibleBasicWith, ex, ey,
              hna, hnb, e, boolean, runtimeValue]; rfl)

theorem compat_ok {a b r : WVal} (h : compat a b = some r) (tags : Mem.Concrete.Tags) :
    primitive .compatible [rv a, rv b] tags = .ok (rv r) := by
  unfold compat at h
  split at h
  · cases h
    exact compat_void _ _ tags
  · exact compat_int h tags
  · cases h

theorem signedness_ok {s : Bool} {a r : WVal} (h : signedness s a = some r) (tags : Mem.Concrete.Tags) :
    primitive (.isType (if s then 2 else 3)) [rv a] tags = .ok (rv r) := by
  unfold signedness at h
  split at h
  · rename_i ty
    cases hity : Fold.intType ty with
    | none => simp [hity] at h
    | some ity =>
      cases hl : Mem.Concrete.integerLayout ity with
      | none => simp [hity, hl] at h
      | some l =>
        obtain ⟨w, sg⟩ := l
        cases hb : bounds ity with
        | none => simp [hity, hl, hb] at h
        | some b =>
          simp [hity, hl, hb] at h
          subst h
          rcases ty with ⟨ann, ty⟩
          cases ty with
          | basic bt =>
            cases bt with
            | integer i =>
              have hi : i = ity := by
                have := intType_sound hity
                simpa [Dynamics.intType] using this
              subst hi
              have hreg := layout_registered hb tags
              cases s <;> simp [primitive, runtimeValue, Dynamics.intType, bounds_registered hb, hreg, hl] <;> rfl
            | _ => simp [Fold.intType] at hity
          | _ => simp [Fold.intType] at hity
  · cases h

theorem select_rv (v : WVal) : (bs : List (Pattern Sym × PExp)) → {xs : List (Sym × WVal)} → {body : PExp} →
    select v bs = some (xs, body) → selectCase (rv v) bs = some (bmap xs, body)
  | [], _, _, h => by simp [select] at h
  | (p, b) :: rest, xs, body, h => by
    unfold select at h
    simp only [selectCase, matchP_rv]
    cases hm : matchP p v with
    | some ys =>
      rw [hm] at h
      simp_all
    | none =>
      rw [hm] at h
      simp [select_rv v rest h]

theorem mapM_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {bs : List β}
    (h : (a :: l).mapM f = some bs) : ∃ b bs', f a = some b ∧ l.mapM f = some bs' ∧ bs = b :: bs' := by
  rw [List.mapM_cons] at h
  cases ha : f a with
  | none => simp [ha] at h
  | some b =>
    cases hl : l.mapM f with
    | none => simp [ha, hl] at h
    | some bs' =>
      simp [ha, hl] at h
      exact ⟨b, bs', rfl, rfl, h.symm⟩

theorem bmap_zip (params : List Sym) (ws : List WVal) :
    bmap (params.zip ws) = params.zip (ws.map rv) := by
  induction params generalizing ws with
  | nil => simp [bmap]
  | cons p ps ih => cases ws <;> simp_all [bmap]

theorem funBody_sound {doc : Doc} {name : Name Sym} {params : List Sym} {body : PExp}
    {ws : List WVal} (h : funBody doc name = some (params, body)) (hl : params.length = ws.length) :
    functionBody doc name (ws.map rv) = .ok (body, extendEnv (params.zip (ws.map rv)) ∅) := by
  cases name with
  | sym s =>
    simp only [funBody] at h
    cases hs : doc.stdlib.lookup s with
    | some d =>
      rw [hs] at h
      cases d <;> simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp [functionBody, hs, by simpa using hl]
      rfl
    | none =>
      rw [hs] at h
      cases hf : doc.funs.lookup s with
      | none => simp [hf] at h
      | some d =>
        rw [hf] at h
        cases d <;> simp at h
        obtain ⟨rfl, rfl⟩ := h
        simp [functionBody, hs, hf, by simpa using hl]
        rfl
  | impl c =>
    simp only [funBody] at h
    cases hc : doc.impl.lookup c with
    | none => simp [hc] at h
    | some d =>
      rw [hc] at h
      cases d <;> simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp [functionBody, hc, by simpa using hl]
      rfl

/-! ## Steps of the dynamics -/

section Steps
variable (file : Program) (labels : Labels)

/-- What `eval_reaches` says at one fuel level. -/
def Folds (fuel : Nat) : Prop :=
  ∀ (env : WEnv) (p : PExp) (v : WVal), eval file fuel env p = some v →
    ∀ denv, EnvRel env denv → ∀ k m,
      Reaches file labels ⟨.pureExpr p denv, k, m⟩ ⟨.value (rv v), k, m⟩

theorem args_chain {fuel : Nat} (IH : Folds file labels fuel) {env : WEnv} {denv : Env}
    (hr : EnvRel env denv) (op : Prim) (k : List Frame) (m : Mem.Concrete.State) :
    ∀ (rest : List PExp) (p : PExp) (done : List Val) (v : WVal) (vs : List WVal),
    eval file fuel env p = some v → rest.mapM (eval file fuel env) = some vs →
    Reaches file labels ⟨.pureExpr p denv, .arguments op done rest denv :: k, m⟩
      ⟨.apply op (done ++ rv v :: vs.map rv), k, m⟩
  | [], p, done, v, vs, hp, hvs => by
    simp at hvs
    subst hvs
    refine (IH env p v hp denv hr _ m).trans ?_
    apply next_reaches
    · intro o; simp
    · simp [request, requestAux, awaitsScheduling]
  | q :: rest, p, done, v, vs, hp, hvs => by
    obtain ⟨w, ws, hq, hws, rfl⟩ := mapM_cons_some hvs
    refine (IH env p v hp denv hr _ m).trans ?_
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr q denv, .arguments op (done ++ [rv v]) rest denv :: k, m⟩) ?_ ?_
    · apply next_reaches
      · intro o; simp
      · simp [request, requestAux, awaitsScheduling]
    · simpa using args_chain IH hr op k m rest q (done ++ [rv v]) w ws hq hws

theorem args_reaches {fuel : Nat} (IH : Folds file labels fuel) {env : WEnv} {denv : Env}
    (hr : EnvRel env denv) (op : Prim) (ps : List PExp) (ws : List WVal)
    (hps : ps.mapM (eval file fuel env) = some ws) (c : Control) (k : List Frame)
    (m : Mem.Concrete.State) (live : ∀ o, c ≠ .halt o)
    (hreq : request file labels ⟨c, k, m⟩ = arguments op ps denv k) :
    Reaches file labels ⟨c, k, m⟩ ⟨.apply op (ws.map rv), k, m⟩ := by
  cases ps with
  | nil =>
    simp at hps
    subst hps
    exact next_reaches file labels _ _ _ _ m live (by simpa [arguments] using hreq)
  | cons p rest =>
    obtain ⟨v, vs, hp, hvs, rfl⟩ := mapM_cons_some hps
    exact (next_reaches file labels _ _ _ _ m live (by simpa [arguments] using hreq)).trans
      (by simpa using args_chain file labels IH hr op k m rest p [] v vs hp hvs)

theorem apply_value {op : Prim} {vs : List Val} {r : Val} {k : List Frame} {m : Mem.Concrete.State}
    (pure : primitive op vs ⟨file.tagDefs, m.enumTypes⟩ = .ok r)
    (hop : request file labels ⟨.apply op vs, k, m⟩ =
      match primitive op vs ⟨file.tagDefs, m.enumTypes⟩ with
      | .ok v => .next (.value v) k
      | .error o => .end_ o) :
    Reaches file labels ⟨.apply op vs, k, m⟩ ⟨.value r, k, m⟩ := by
  apply next_reaches
  · intro o; simp
  · rw [hop, pure]

theorem request_arguments {op : Prim} {ps : List PExp} {denv : Env} {c : Control} {k : List Frame}
    {m : Mem.Concrete.State} (h : requestAux file labels m c k = arguments op ps denv k) :
    request file labels ⟨c, k, m⟩ = arguments op ps denv k := by
  unfold request
  simp only
  rw [h]
  cases ps <;> rfl

theorem two_mapM {env : WEnv} {fuel : Nat} {p q : PExp} {x y : WVal}
    (hx : eval file fuel env p = some x) (hy : eval file fuel env q = some y) :
    [p, q].mapM (eval file fuel env) = some [x, y] := by
  simp [hx, hy]

theorem one_mapM {env : WEnv} {fuel : Nat} {p : PExp} {x : WVal}
    (hx : eval file fuel env p = some x) : [p].mapM (eval file fuel env) = some [x] := by
  simp [hx]

/-- **Agreement**: a folded pure expression reduces to its folded value. -/
theorem eval_reaches : ∀ fuel, Folds file labels fuel
  | 0 => by intro env p v h; simp [eval] at h
  | fuel+1 => by
    have IH := eval_reaches fuel
    intro env p v h denv hr k m
    have live : ∀ c : Control, (∀ o, c ≠ .halt o) → True := fun _ _ => trivial
    rcases p with ⟨a, u, e⟩
    cases e with
    | val w =>
      simp only [eval, Option.some.injEq] at h
      subst h
      apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
    | sym s =>
      simp only [eval] at h
      have hl : denv.lookup s = some (rv v) := by rw [hr s, h]; rfl
      apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hl]
    | impl c =>
      simp only [eval] at h
      cases hc : file.impl.lookup c with
      | none => simp [hc] at h
      | some d =>
        cases d with
        | constant bt body =>
          simp only [hc] at h
          refine Relation.ReflTransGen.trans (b := ⟨.pureExpr body denv, k, m⟩) ?_ (IH env body v h denv hr k m)
          apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hc]
        | function _ _ _ => simp [hc] at h
    | ctor c ps =>
      simp only [eval] at h
      cases hps : ps.mapM (eval file fuel env) with
      | none => simp [hps] at h
      | some ws =>
        simp only [hps, bind, Option.bind] at h
        refine (args_reaches file labels IH hr (.ctor c) ps ws hps _ k m (by intro o; simp)
          (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, ctor_ok h]
    | op b p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches file labels IH hr (.bin b) [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, bin_ok h]
    | convInt ty p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches file labels IH hr (.conv ty) [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, conv_ok h]
    | catchExceptionalCondition ty op p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches file labels IH hr (.catchInt ty op) [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, catchInt_ok h]
    | wrapI ty op p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches file labels IH hr (.wrapInt ty op) [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, wrapInt_ok h]
    | not p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches file labels IH hr .notBool [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, notBool_ok h]
    | isSigned p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches file labels IH hr (.isType 2) [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        have := fun tags => signedness_ok (s := true) h tags
        simp only [ite_true] at this
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, this]
    | isUnsigned p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches file labels IH hr (.isType 3) [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        have := fun tags => signedness_ok (s := false) h tags
        simp only [Bool.false_eq_true, ite_false] at this
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, this]
    | areCompatible p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches file labels IH hr .compatible [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, compat_ok h]
    | call name ps =>
      simp only [eval] at h
      cases hps : ps.mapM (eval file fuel env) with
      | none => simp [hps] at h
      | some ws =>
        cases hf : funBody file name with
        | none => simp [hps, hf] at h
        | some pb =>
          obtain ⟨params, body⟩ := pb
          simp only [hps, hf, bind, Option.bind] at h
          split at h
          · rename_i hl
            refine (args_reaches file labels IH hr (.call name) ps ws hps _ k m (by intro o; simp)
              (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
            refine Relation.ReflTransGen.trans
              (b := ⟨.pureExpr body (extendEnv (params.zip (ws.map rv)) ∅), k, m⟩) ?_ ?_
            · apply next_reaches
              · intro o; simp
              · simp [request, requestAux, awaitsScheduling, funBody_sound hf hl]
            · have he := EnvRel.empty.extend (params.zip ws)
              rw [bmap_zip] at he
              exact IH _ body v h _ he k m
          · cases h
    | let_ pat p body =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hm : matchP pat x with
        | none => simp [hx, hm] at h
        | some xs =>
          simp only [hx, hm, bind, Option.bind] at h
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr p denv, .pureBind pat body denv :: k, m⟩) ?_ ?_
          · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
          refine (IH env p x hx denv hr _ m).trans ?_
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr body (extendEnv (bmap xs) denv), k, m⟩) ?_ ?_
          · apply next_reaches
            · intro o; simp
            · simp [request, requestAux, awaitsScheduling, matchP_rv, hm]
          · exact IH _ body v h _ (hr.extend xs) k m
    | case_ p bs =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hm : select x bs with
        | none => simp [hx, hm] at h
        | some xb =>
          obtain ⟨xs, body⟩ := xb
          simp only [hx, hm, bind, Option.bind] at h
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr p denv, .pureCase bs denv :: k, m⟩) ?_ ?_
          · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
          refine (IH env p x hx denv hr _ m).trans ?_
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr body (extendEnv (bmap xs) denv), k, m⟩) ?_ ?_
          · apply next_reaches
            · intro o; simp
            · simp [request, requestAux, awaitsScheduling, select_rv x bs hm]
          · exact IH _ body v h _ (hr.extend xs) k m
    | if_ c yes no =>
      simp only [eval] at h
      cases hx : eval file fuel env c with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine Relation.ReflTransGen.trans
          (b := ⟨.pureExpr c denv, .pureIf yes no denv :: k, m⟩) ?_ ?_
        · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
        refine (IH env c x hx denv hr _ m).trans ?_
        cases x
        case true =>
          refine Relation.ReflTransGen.trans (b := ⟨.pureExpr yes denv, k, m⟩) ?_ (IH env yes v h denv hr k m)
          apply next_reaches <;> simp [request, requestAux, awaitsScheduling, runtimeValue]
        case false =>
          refine Relation.ReflTransGen.trans (b := ⟨.pureExpr no denv, k, m⟩) ?_ (IH env no v h denv hr k m)
          apply next_reaches <;> simp [request, requestAux, awaitsScheduling, runtimeValue]
        all_goals simp at h
    | _ => simp [eval] at h

end Steps

end Silmaril.Compile.Core.Verified.Fold
