module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Types
public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Family
public import Silmaril.Wasm.Execution.Core.Exec.Instantiate
public import Silmaril.Wasm.Execution.Core.Exec.ConstExprArity
public import Silmaril.Wasm.Execution.Core.Soundness.ConstEval

@[expose] public section

/-! # Constant initialisers of the profile

Global initialisers of a profile module are numeric constants, global reads and integer
`add`/`sub`/`mul`. Their evaluation (`cfold`, `evalConst?`) never changes the
store, depends on the frame only through the global reads (`cfold_rel`), and
succeeds on typed code whose global reads return typed numeric values
(`cfold_progress`).
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Constant instructions of the profile. -/
def pcI : Instr → Prop
  | .intConst _ _ | .floatConst _ _ => True
  | .globalGet _ => True
  | .intBinOp _ op => constBinOp op = true
  | _ => False

/-- A global's value as read through a frame. -/
def gval (s : Store H) (f : Frame) (x : GlobalIdx) : Option Val := (s.global? f x).map (·.2.value)

/-- Related constant instructions: equal, or reads of globals with equal values. -/
def CRel {H₁ H₂ : Type} (sA : Store H₁) (fA : Frame) (sB : Store H₂) (fB : Frame) (i j : Instr) : Prop :=
  (i = j ∧ pcI i ∧ ∀ x, i ≠ .globalGet x) ∨
    (∃ x y, i = .globalGet x ∧ j = .globalGet y ∧ gval sA fA x = gval sB fB y)

theorem constInstr?_intConst (s : Store H) (f : Frame) (vs : List Val) (t : IntType)
    (c : BitVec t.width) :
    constInstr? s f vs (.intConst t c) = some (s, vs ++ [.num ⟨.int t, c⟩]) := rfl

theorem constInstr?_floatConst (s : Store H) (f : Frame) (vs : List Val) (t : FloatType)
    (c : BitVec t.width) :
    constInstr? s f vs (.floatConst t c) = some (s, vs ++ [.num ⟨.float t, c⟩]) := rfl

theorem constInstr?_globalGet (s : Store H) (f : Frame) (vs : List Val) (x : GlobalIdx) :
    constInstr? s f vs (.globalGet x) = (gval s f x).map (fun v => (s, vs ++ [v])) := by
  unfold gval
  cases h : s.global? f x with
  | none => simp [constInstr?, h]
  | some p => obtain ⟨a, g⟩ := p; simp [constInstr?, h]

theorem constInstr?_binop {H₂ : Type} (s : Store H) (s' : Store H₂) (f f' : Frame) (vs : List Val) (t : IntType)
    (op : IntBinOp) :
    constInstr? s f vs (.intBinOp t op) =
      (constInstr? s' f' vs (.intBinOp t op)).map (fun p => (s, p.2)) := by
  by_cases hop : constBinOp op = true
  · simp only [constInstr?, hop, ite_true]
    cases hp : pop2? vs with
    | none => simp
    | some p =>
      obtain ⟨pre, v₁, v₂⟩ := p
      cases h1 : v₁.int? t with
      | none => simp [h1]
      | some x =>
        cases h2 : v₂.int? t with
        | none => simp [h1, h2]
        | some y =>
          cases h3 : intBinOp t op x y with
          | ok z => simp [h1, h2, h3]
          | error e => simp [h1, h2, h3]
  · simp [constInstr?, hop]

theorem constInstr?_store {s : Store H} {f : Frame} {vs : List Val} {i : Instr} (hi : pcI i)
    {p : Store H × List Val} (h : constInstr? s f vs i = some p) : p.1 = s := by
  cases i with
  | intConst t c => rw [constInstr?_intConst] at h; cases h; rfl
  | floatConst t c => rw [constInstr?_floatConst] at h; cases h; rfl
  | globalGet x =>
    rw [constInstr?_globalGet] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  | intBinOp t op =>
    rw [constInstr?_binop s s f f vs t op] at h
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  | _ => exact absurd hi (by simp [pcI])

theorem CRel.pcI_right {H₁ H₂ : Type} {sA : Store H₁} {sB : Store H₂} {fA fB : Frame} {i j : Instr} (h : CRel sA fA sB fB i j)
    (hi : pcI i) : pcI j := by
  rcases h with ⟨rfl, -, -⟩ | ⟨x, y, rfl, rfl, -⟩
  · exact hi
  · trivial

/-- One related instruction. -/
theorem constInstr?_rel {H₁ H₂ : Type} {sA : Store H₁} {sB : Store H₂} {fA fB : Frame} {i j : Instr}
    (h : CRel sA fA sB fB i j) (vs : List Val) :
    (constInstr? sA fA vs i).map Prod.snd = (constInstr? sB fB vs j).map Prod.snd := by
  rcases h with ⟨rfl, hi, hg⟩ | ⟨x, y, rfl, rfl, hxy⟩
  · cases i with
    | intConst t c => simp [constInstr?_intConst]
    | floatConst t c => simp [constInstr?_floatConst]
    | intBinOp t op =>
      rw [constInstr?_binop sA sB fA fB vs t op, Option.map_map]
      rfl
    | globalGet x => exact absurd rfl (hg x)
    | _ => exact absurd hi (by simp [pcI])
  · simp only [constInstr?_globalGet, Option.map_map]
    rw [hxy]
    rfl

theorem cfold_store {s : Store H} {f : Frame} : ∀ {vs : List Val} {e : List Instr},
    (∀ i ∈ e, pcI i) → ∀ {p : Store H × List Val}, cfold f s vs e = some p → p.1 = s
  | vs, [], _, p, h => by rw [cfold_nil] at h; cases h; rfl
  | vs, i :: e, he, p, h => by
    rw [cfold_cons] at h
    cases hq : constInstr? s f vs i with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq, Option.bind_some] at h
      have hq1 := constInstr?_store (he i (by simp)) hq
      obtain ⟨s₁, ws⟩ := q
      simp only at hq1 h
      subst hq1
      exact cfold_store (fun j hj => he j (by simp [hj])) h

/-- **Related constant code computes the same values.** -/
theorem cfold_rel {H₁ H₂ : Type} {sA : Store H₁} {sB : Store H₂} {fA fB : Frame} : ∀ {e e' : List Instr} {vs : List Val},
    (∀ i ∈ e, pcI i) → List.Forall₂ (CRel sA fA sB fB) e e' →
    (cfold fA sA vs e).map Prod.snd = (cfold fB sB vs e').map Prod.snd
  | [], [], vs, _, .nil => by simp [cfold_nil]
  | i :: e, j :: e', vs, he, .cons hij t => by
    rw [cfold_cons, cfold_cons]
    have key := constInstr?_rel hij vs
    have hi := he i (by simp)
    have hj := hij.pcI_right hi
    cases hA : constInstr? sA fA vs i with
    | none =>
      rw [hA] at key
      cases hB : constInstr? sB fB vs j with
      | none => simp
      | some q => rw [hB] at key; cases key
    | some p =>
      rw [hA] at key
      cases hB : constInstr? sB fB vs j with
      | none => rw [hB] at key; cases key
      | some q =>
        rw [hB] at key
        simp only [Option.map_some, Option.some.injEq] at key
        have hp1 := constInstr?_store hi hA
        have hq1 := constInstr?_store hj hB
        obtain ⟨s₁, ws⟩ := p
        obtain ⟨s₂, ws'⟩ := q
        simp only at hp1 hq1 key
        subst hp1 hq1 key
        simp only [Option.bind_some]
        exact cfold_rel (fun k hk => he k (by simp [hk])) t

theorem evalConst?_eq_some {H' : Type} {s : Store H'} {f : Frame} {e : Expr} {s' : Store H'}
    {v : Val} : evalConst? s f e = some (s', v) ↔ cfold f s [] e = some (s', [v]) := by
  unfold evalConst?
  have : constExpr? s f e = cfold f s [] e := rfl
  rw [this]
  cases cfold f s [] e with
  | none => simp
  | some p =>
    obtain ⟨s₁, ws⟩ := p
    match ws with
    | [] => simp
    | [w] => simp
    | _ :: _ :: _ => simp

/-- Related initialisers evaluate to the same value. -/
theorem evalConst?_rel {H₁ H₂ : Type} {sA : Store H₁} {sB : Store H₂} {fA fB : Frame} {e e' : List Instr}
    (he : ∀ i ∈ e, pcI i) (h : List.Forall₂ (CRel sA fA sB fB) e e') {s' : Store H₁} {v : Val}
    (hv : evalConst? sA fA e = some (s', v)) : evalConst? sB fB e' = some (sB, v) ∧ s' = sA := by
  have key := cfold_rel (vs := []) he h
  have he' : ∀ i ∈ e', pcI i := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := forall₂_mem_right h j hj
    exact hij.pcI_right (he i hi)
  rw [evalConst?_eq_some] at hv
  have h1 : s' = sA := cfold_store he hv
  rw [hv] at key
  cases hB : cfold fB sB [] e' with
  | none => rw [hB] at key; cases key
  | some q =>
    obtain ⟨s₂, ws'⟩ := q
    rw [hB] at key
    have h2 : s₂ = sB := cfold_store he' hB
    simp only [Option.map_some, Option.some.injEq] at key
    subst key h2
    exact ⟨evalConst?_eq_some.2 hB, h1⟩

/-- Constant code is related to itself when the global reads agree. -/
theorem crel_refl {H₁ H₂ : Type} {sA : Store H₁} {sB : Store H₂} {fA fB : Frame} (hg : ∀ x, gval sA fA x = gval sB fB x) :
    ∀ {e : List Instr}, (∀ i ∈ e, pcI i) → List.Forall₂ (CRel sA fA sB fB) e e
  | [], _ => .nil
  | i :: e, he => by
    refine .cons ?_ (crel_refl hg fun j hj => he j (by simp [hj]))
    by_cases hi : ∃ x, i = .globalGet x
    · obtain ⟨x, rfl⟩ := hi
      exact .inr ⟨x, x, rfl, rfl, hg x⟩
    · exact .inl ⟨rfl, he i (by simp), fun x hx => hi ⟨x, hx⟩⟩

/-! ## Evaluation against a list of global values -/

/-- A store holding the values `env` as globals `0, 1, …`. -/
def envStore (env : List Val) : Store H :=
  { globals := env.map fun v => ⟨⟨.const, .num (.int .i32)⟩, v⟩ }

/-- A frame reading global `x` at address `x`. -/
def envFrame (env : List Val) : Frame := ⟨[], { globals := List.range env.length }⟩

theorem gval_env (env : List Val) (x : GlobalIdx) :
    gval (envStore (H := H) env) (envFrame env) x = env[x.toNat]? := by
  unfold gval
  by_cases hx : x.toNat < env.length
  · rw [global?_of (a := x.toNat) (g := ⟨⟨.const, .num (.int .i32)⟩, env[x.toNat]⟩)]
    · simp [List.getElem?_eq_getElem hx]
    · simp [envFrame, List.getElem?_range hx]
    · simp [envStore, List.getElem?_eq_getElem hx]
  · have h1 : (envFrame env).module.globals[x.toNat]? = none := by
      simp [envFrame]; omega
    have h2 : (envStore (H := H) env).global? (envFrame env) x = none := by
      unfold Store.global?; simp [h1]
    rw [h2, List.getElem?_eq_none (by omega)]
    rfl

/-- Evaluate an initialiser against global values. -/
def pureEval (env : List Val) (e : Expr) : Option Val :=
  (evalConst? (envStore (H := Empty) env) (envFrame env) e).map Prod.snd

/-- Evaluate initialisers in sequence, each against the values so far. -/
def gv : List Val → List Expr → Option (List Val)
  | env, [] => some env
  | env, e :: es =>
    match pureEval env e with
    | some v => gv (env ++ [v]) es
    | none => none

theorem gv_prefix : ∀ {acc : List Val} {es : List Expr} {vals : List Val},
    gv acc es = some vals → ∃ rest, vals = acc ++ rest
  | acc, [], vals, h => by
    simp only [gv, Option.some.injEq] at h
    exact ⟨[], by simp [h]⟩
  | acc, e :: es, vals, h => by
    simp only [gv] at h
    split at h
    · obtain ⟨rest, rfl⟩ := gv_prefix h
      exact ⟨_, List.append_assoc _ _ _⟩
    · cases h

/-- Evaluation in any store and frame whose global reads are those of `env`. -/
theorem evalConst?_env {s : Store H} {f : Frame} {env : List Val}
    (hg : ∀ x, gval s f x = env[x.toNat]?) {e : List Instr} (he : ∀ i ∈ e, pcI i) :
    evalConst? s f e = (pureEval env e).map fun v => (s, v) := by
  have hg₁ : ∀ x, gval s f x = gval (envStore (H := Empty) env) (envFrame env) x := fun x => by
    rw [hg, gval_env]
  have hg₂ : ∀ x, gval (envStore (H := Empty) env) (envFrame env) x = gval s f x :=
    fun x => (hg₁ x).symm
  unfold pureEval
  cases h : evalConst? s f e with
  | none =>
    cases h' : evalConst? (envStore (H := Empty) env) (envFrame env) e with
    | none => rfl
    | some p =>
      obtain ⟨s', v⟩ := p
      have := (evalConst?_rel he (crel_refl hg₂ he) h').1
      rw [h] at this; cases this
  | some p =>
    obtain ⟨s', v⟩ := p
    obtain ⟨h1, rfl⟩ := evalConst?_rel he (crel_refl hg₁ he) h
    rw [h1]
    rfl

/-- Temporary globals: `tys`/`vals` allocated after the store's globals. -/
def tmpStore (s : Store H) (tys : List CGlobalType) (vals : List Val) : Store H :=
  { s with globals := s.globals ++ (tys.zip vals).map fun p => (⟨p.1, p.2⟩ : GlobalInst) }

/-- The initialisation frame after `n` temporary globals at `g0, …`. -/
def tmpFrame (mi : ModuleInst) (g0 n : Nat) : Frame := ⟨[], { mi with globals := List.range' g0 n }⟩

theorem gval_tmp {s : Store H} {mi : ModuleInst} {tys : List CGlobalType} {vals : List Val}
    (hl : tys.length = vals.length) (x : GlobalIdx) :
    gval (tmpStore s tys vals) (tmpFrame mi s.globals.length vals.length) x = vals[x.toNat]? := by
  unfold gval
  by_cases hx : x.toNat < vals.length
  · have hz : x.toNat < (tys.zip vals).length := by simp [hl, hx]
    rw [global?_of (a := s.globals.length + x.toNat)
      (g := ⟨tys[x.toNat]'(by omega), vals[x.toNat]⟩)]
    · simp [List.getElem?_eq_getElem hx]
    · simp [tmpFrame, hx]
    · simp [tmpStore, List.getElem?_append_right, List.getElem?_eq_getElem hz]
  · have h1 : (tmpFrame mi s.globals.length vals.length).module.globals[x.toNat]? = none := by
      simp [tmpFrame]; omega
    have h2 : (tmpStore s tys vals).global? (tmpFrame mi s.globals.length vals.length) x = none := by
      unfold Store.global?; simp [h1]
    rw [h2, List.getElem?_eq_none (by omega)]
    rfl

/-- **Global initialisation** computes the values of `gv`, as temporary globals. -/
theorem evalGlobals?_env {s : Store H} {mi : ModuleInst} :
    ∀ (tys : List CGlobalType) (es : List Expr) (tysAcc : List CGlobalType) (acc : List Val),
    tys.length = es.length → tysAcc.length = acc.length → (∀ e ∈ es, ∀ i ∈ e, pcI i) →
    evalGlobals? evalConst? (tmpStore s tysAcc acc) (tmpFrame mi s.globals.length acc.length)
      tys es =
    (gv acc es).map fun vals => (tmpStore s (tysAcc ++ tys) vals,
      tmpFrame mi s.globals.length vals.length, vals.drop acc.length)
  | [], [], tysAcc, acc, _, hacc, _ => by simp [evalGlobals?, gv]
  | g :: tys, e :: es, tysAcc, acc, hl, hacc, hes => by
    have he : ∀ i ∈ e, pcI i := hes e (by simp)
    have hes' : ∀ e' ∈ es, ∀ i ∈ e', pcI i := fun e' h' => hes e' (by simp [h'])
    have hev := evalConst?_env (H := H) (gval_tmp (s := s) (mi := mi) hacc) he
    simp only [evalGlobals?, gv]
    rw [hev]
    cases hp : pureEval acc e with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      have hal : (allocGlobal (tmpStore s tysAcc acc) g v).1 = tmpStore s (tysAcc ++ [g]) (acc ++ [v]) := by
        simp [allocGlobal, tmpStore, List.zip_append hacc]
      have hal2 : (allocGlobal (tmpStore s tysAcc acc) g v).2 = s.globals.length + acc.length := by
        simp [allocGlobal, tmpStore, hacc]
      have hfr : { (tmpFrame mi s.globals.length acc.length) with
          module := { (tmpFrame mi s.globals.length acc.length).module with
            globals := (tmpFrame mi s.globals.length acc.length).module.globals ++
              [(allocGlobal (tmpStore s tysAcc acc) g v).2] } } =
          tmpFrame mi s.globals.length (acc ++ [v]).length := by
        rw [hal2]
        simp [tmpFrame, List.range'_concat]
      rw [hal, hfr]
      have ih := evalGlobals?_env (s := s) (mi := mi) tys es (tysAcc ++ [g]) (acc ++ [v]) (by simpa using hl)
        (by simp [hacc]) hes'
      rw [ih]
      cases hg : gv (acc ++ [v]) es with
      | none => rfl
      | some vals =>
        obtain ⟨rest, rfl⟩ := gv_prefix hg
        simp [List.append_assoc]
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl

/-! ## Progress on typed code -/

/-- A numeric value of its numeric type. -/
def NumV (v : Val) (t : CValType) : Prop := ∃ nt c, t = .num nt ∧ v = .num ⟨nt, c⟩

theorem sub_num {Δ : TypeCtx} {it : NumType} {t : CValType} (h : Sub Δ (.num it) t) :
    t = .num it := by
  cases h; rfl

theorem resultSub_nums {Δ : TypeCtx} :
    ∀ {vs : List Val} {ts us : List CValType}, List.Forall₂ NumV vs ts → ResultSub Δ ts us →
      List.Forall₂ NumV vs us
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons ⟨it, c, rfl, rfl⟩ t, .cons hs hs' => by
    rw [sub_num hs]
    exact .cons ⟨it, c, rfl, rfl⟩ (resultSub_nums t hs')

theorem forall₂_append_right_split {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {ts us : List β}, List.Forall₂ R l (ts ++ us) →
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R l₁ ts ∧ List.Forall₂ R l₂ us
  | l, [], us, h => ⟨[], l, rfl, .nil, h⟩
  | a :: l, t :: ts, us, .cons h hs => by
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := forall₂_append_right_split hs
    exact ⟨a :: l₁, l₂, rfl, .cons h h₁, h₂⟩

theorem constInstr?_binop_ok {s : Store H} {f : Frame} (vpre : List Val) {t : IntType}
    {op : IntBinOp} {x y z : BitVec t.width} (hop : constBinOp op = true)
    (hz : intBinOp t op x y = .ok z) :
    constInstr? s f (vpre ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) (.intBinOp t op) =
      some (s, vpre ++ [.num ⟨.int t, z⟩]) := by
  simp only [constInstr?, hop, ite_true, Option.bind_eq_bind, pop2?_append, Option.bind_some]
  rw [Val.int?_self, Val.int?_self]
  simp [hz]

/-- **Typed profile constant code evaluates.** -/
theorem cfold_progress {C : Context} (hC : C.Wf) (hL : C.locals = []) {f : Frame} {s : Store H}
    (hglob : ∀ (x : GlobalIdx) (gt : CGlobalType), C.globals[x.toNat]? = some gt →
      ∃ v, gval s f x = some v ∧ NumV v gt.type) :
    ∀ (e : List Instr) (ts rs : List CValType) (vs : List Val), (∀ i ∈ e, pcI i) →
      InstrsOk C e ⟨ts, [], rs⟩ → List.Forall₂ NumV vs ts →
      ∃ ws, cfold f s vs e = some (s, ws) ∧ List.Forall₂ NumV ws rs
  | [], ts, rs, vs, _, h, hvs => by
    have := (InstrsOk.nil_inv hC h).1
    exact ⟨vs, cfold_nil f s vs, resultSub_nums hvs this⟩
  | i :: e, ts, rs, vs, he, h, hvs => by
    obtain ⟨pre, p, r, hi, -, hsub, hrest⟩ := InstrsOk.cons_inv' hC hL h
    have hvs' := resultSub_nums hvs hsub
    obtain ⟨vpre, vp, rfl, hpre, hp⟩ := forall₂_append_right_split hvs'
    have hpi := he i (by simp)
    have hrec := fun ws (hws : List.Forall₂ NumV ws (pre ++ r)) =>
      cfold_progress hC hL hglob e (pre ++ r) rs ws (fun j hj => he j (by simp [hj])) hrest hws
    cases i with
    | intConst t c =>
      have hit := InstrOk.intConst_inv hi
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨rfl, -, rfl⟩ := hit
      cases hp
      obtain ⟨ws, hws, hws'⟩ := hrec (vpre ++ [.num ⟨.int t, c⟩])
        (List.rel_append hpre (.cons ⟨.int t, c, rfl, rfl⟩ .nil))
      refine ⟨ws, ?_, hws'⟩
      rw [cfold_cons, constInstr?_intConst]
      simpa using hws
    | floatConst t c =>
      have hit := InstrOk.floatConst_inv hi
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨rfl, -, rfl⟩ := hit
      cases hp
      obtain ⟨ws, hws, hws'⟩ := hrec (vpre ++ [.num ⟨.float t, c⟩])
        (List.rel_append hpre (.cons ⟨.float t, c, rfl, rfl⟩ .nil))
      refine ⟨ws, ?_, hws'⟩
      rw [cfold_cons, constInstr?_floatConst]
      simpa using hws
    | globalGet x =>
      obtain ⟨m', t', hx, hit⟩ := InstrOk.globalGet_inv hi
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨rfl, -, rfl⟩ := hit
      cases hp
      obtain ⟨v, hv, hvt⟩ := hglob x _ hx
      obtain ⟨ws, hws, hws'⟩ := hrec (vpre ++ [v]) (List.rel_append hpre (.cons hvt .nil))
      refine ⟨ws, ?_, hws'⟩
      rw [cfold_cons, constInstr?_globalGet, hv]
      simpa using hws
    | intBinOp t op =>
      have hit := InstrOk.intBinOp_inv hi
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨rfl, -, rfl⟩ := hit
      have hop : constBinOp op = true := hpi
      have hop' : op = .add ∨ op = .sub ∨ op = .mul := by
        cases op <;> simp_all [constBinOp]
      cases hp with
      | cons h1 hp =>
        cases hp with
        | cons h2 hp =>
          cases hp
          obtain ⟨it₁, x, e₁, rfl⟩ := h1
          obtain ⟨it₂, y, e₂, rfl⟩ := h2
          cases e₁
          cases e₂
          obtain ⟨z, hz⟩ : ∃ z, intBinOp t op x y = .ok z := by
            cases hr : intBinOp t op x y with
            | ok z => exact ⟨z, rfl⟩
            | error e => exact absurd hr (intBinOp_const_ne_error hop')
          obtain ⟨ws, hws, hws'⟩ := hrec (vpre ++ [.num ⟨.int t, z⟩])
            (List.rel_append hpre (.cons ⟨.int t, z, rfl, rfl⟩ .nil))
          refine ⟨ws, ?_, hws'⟩
          rw [cfold_cons, constInstr?_binop_ok vpre hop hz]
          simpa using hws
    | _ => exact absurd hpi (by simp [pcI])

/-- Profile constant instructions. -/
theorem pcI_of {C : Context} {i : Instr} (hp : Binaryen.instrInProfile i) (hc : InstrConst C i) :
    pcI i := by
  cases hc with
  | intConst t b => trivial
  | floatConst t b => trivial
  | globalGet h => trivial
  | binop hop => rcases hop with rfl | rfl | rfl <;> rfl
  | _ => unfold Binaryen.instrInProfile at hp; simp [Binaryen.profileInstr] at hp

theorem forall₂_getElem?_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {n : Nat} {b : β}, l₂[n]? = some b →
      ∃ a, l₁[n]? = some a ∧ R a b
  | _, _, .nil, n, b, h => by simp at h
  | a :: _, _ :: _, .cons hr t, 0, b, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨a, rfl, hr⟩
  | _ :: _, _ :: _, .cons _ t, n + 1, b, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem?_left t h

/-- **Valid profile globals evaluate.** -/
theorem gv_progress {C : Context} (hC : ConstCtxOk C) {gs : List Global}
    {gts : List CGlobalType} (h : GlobalsOk C gs gts) (hpc : ∀ g ∈ gs, ∀ i ∈ g.init, pcI i)
    (hint : ∀ gt ∈ gts, ∃ t, gt.type = .num t) :
    ∀ (acc : List Val), List.Forall₂ NumV acc (C.globals.map CGlobalType.type) →
      ∃ vals, gv acc (gs.map Global.init) = some vals ∧
        List.Forall₂ NumV vals ((C.globals ++ gts).map CGlobalType.type) := by
  induction h with
  | nil => exact fun acc hacc => ⟨acc, rfl, by simpa using hacc⟩
  | @cons C g gs gt gts hg hs ih =>
    intro acc hacc
    have hglob : ∀ (x : GlobalIdx) (gt' : CGlobalType), C.globals[x.toNat]? = some gt' →
        ∃ v, gval (envStore (H := Empty) acc) (envFrame acc) x = some v ∧ NumV v gt'.type := by
      intro x gt' hx
      have hx' : (C.globals.map CGlobalType.type)[x.toNat]? = some gt'.type := by simp [hx]
      obtain ⟨v, hv, hvt⟩ := forall₂_getElem?_left hacc hx'
      exact ⟨v, by rw [gval_env]; exact hv, hvt⟩
    have hpc₀ : ∀ i ∈ g.init, pcI i := hpc g (by simp)
    obtain ⟨ws, hws, hws'⟩ := cfold_progress hC.wf hC.locals hglob g.init [] [gt.type] []
      hpc₀ hg.2.2.typed .nil
    obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
      cases hws' with
      | cons h t => cases t; exact ⟨_, rfl⟩
    have hw : NumV w gt.type := by cases hws' with | cons h _ => exact h
    have hpe : pureEval acc g.init = some w := by
      unfold pureEval
      rw [evalConst?_eq_some.2 hws]
      rfl
    obtain ⟨vals, hv, hvt⟩ := ih (hC.addGlobal hg.2.1) (fun g' hg' => hpc g' (by simp [hg']))
      (fun gt' hgt' => hint gt' (by simp [hgt'])) (acc ++ [w])
      (by simpa using List.rel_append hacc (.cons hw .nil))
    refine ⟨vals, ?_, by simpa using hvt⟩
    simp only [List.map_cons, gv, hpe]
    exact hv

end Silmaril.Wasm.Binaryen.RUMESim
