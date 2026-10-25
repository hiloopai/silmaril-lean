module

public import Silmaril.Wasm.Execution.Core.Exec.ConstEvalComplete
public import Silmaril.Wasm.Execution.Core.Soundness.ConstEvalTyping

@[expose] public section

/-! # Arity of the constant evaluator on typed code

If `InstrsOk C e (t₁ → t₂)` and the frame's types agree with `C`, a successful
fold of `constInstr?` over `e` from a stack of at least `|t₁|` values replaces
`|t₁|` values by `|t₂|` values (`cfold_arity`). Consequently a validated constant
expression of one result type evaluates (in the reduction semantics) to exactly
one value, which `evalConst?` finds (`evalConst?_of_exprOkConst`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

theorem Context.withLocals_types_ca :
    ∀ (C : Context) (xs : List Nat) (lts : List LocalType), (C.withLocals xs lts).types = C.types
  | C, x :: xs, lt :: lts => by
    rw [Context.withLocals, Context.withLocals_types_ca]; rfl
  | _, [], _ => by simp [Context.withLocals]
  | _, _ :: _, [] => by simp [Context.withLocals]

theorem Context.initLocals_types_ca (C : Context) (xs : List Nat) :
    (C.initLocals xs).types = C.types := Context.withLocals_types_ca _ _ _

theorem cfold_append (f : Frame) (s : Store H) (vs : List Val) (a b : Expr) :
    cfold f s vs (a ++ b) = (cfold f s vs a).bind (fun st => cfold f st.1 st.2 b) := by
  simp [cfold, List.foldlM_append]

theorem structNew?_len {s s' : Store H} {f : Frame} {vs ws : List Val} {x : TypeIdx}
    (h : structNew? s f vs x = some (s', ws)) :
    ∃ d fs, f.type? x = some d ∧ expandStruct? d = some fs ∧
      ws.length + fs.length = vs.length + 1 := by
  unfold structNew? at h
  cases hd : f.type? x with
  | none => simp [hd] at h
  | some d =>
    cases hfs : expandStruct? d with
    | none => simp [hd, hfs] at h
    | some fs =>
      cases hp : popN? vs fs.length with
      | none => simp [hd, hfs, hp] at h
      | some pa =>
        rcases pa with ⟨pre, args⟩
        obtain ⟨rfl, hl⟩ := popN?_eq hp
        simp only [hd, hfs, hp, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · cases h
          refine ⟨d, fs, rfl, by simp [hfs], ?_⟩
          simp only [List.length_append, List.length_singleton]
          omega
        · cases h

theorem arrayNewFixed?_len {s s' : Store H} {f : Frame} {vs ws : List Val} {x : TypeIdx}
    {n : Fin (2 ^ 32)} (h : arrayNewFixed? s f vs x n = some (s', ws)) :
    ws.length + n.val = vs.length + 1 := by
  unfold arrayNewFixed? at h
  cases hd : f.type? x with
  | none => simp [hd] at h
  | some d =>
    cases hfs : expandArray? d with
    | none => simp [hd, hfs] at h
    | some ft =>
      cases hp : popN? vs n.val with
      | none => simp [hd, hp] at h
      | some pa =>
        rcases pa with ⟨pre, args⟩
        obtain ⟨rfl, hl⟩ := popN?_eq hp
        simp only [hd, hfs, hp, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · cases h
          simp only [List.length_append, List.length_singleton]
          omega
        · cases h

theorem pop1?_len {vs pre : List Val} {v : Val} (h : pop1? vs = some (pre, v)) :
    vs.length = pre.length + 1 := by
  rw [pop1?_eq h]; simp

theorem pop2?_len {vs pre : List Val} {v w : Val} (h : pop2? vs = some (pre, v, w)) :
    vs.length = pre.length + 2 := by
  rw [pop2?_eq h]; simp

theorem mapM_length_ca {α β : Type _} {g : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM g = some ys → ys.length = xs.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, -, zs, hzs, rfl⟩ := h
    simp [mapM_length_ca hzs]

/-- One constant instruction replaces its parameters by its results. -/
theorem constInstr?_len {C : Context} {s s' : Store H} {f : Frame} {vs ws : List Val} {i : Instr}
    {p r : List CValType} {xs : List Nat} (hfa : f.module.types = C.types)
    (h : constInstr? s f vs i = some (s', ws)) (hi : InstrOk C i ⟨p, xs, r⟩) :
    ws.length + p.length = vs.length + r.length := by
  cases i with
  | intConst t b =>
    have hit := hi.intConst_inv; cases hit
    simp only [constInstr?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; simp
  | floatConst t b =>
    have hit := hi.floatConst_inv; cases hit
    simp only [constInstr?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; simp
  | vecConst b =>
    have hit := hi.vecConst_inv; cases hit
    simp only [constInstr?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; simp
  | refNull ht =>
    obtain ⟨hit, -⟩ := hi.refNull_inv; cases hit
    simp only [constInstr?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; simp
  | refFunc x =>
    obtain ⟨_, _, hit⟩ := hi.refFunc_inv; cases hit
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h; simp
  | refI31 =>
    have hit := hi.refI31_inv; cases hit
    simp only [constInstr?] at h
    cases hp : pop1? vs with
    | none => simp [hp] at h
    | some pv =>
      rcases pv with ⟨pre, v⟩
      have hl := pop1?_len hp
      simp only [hp, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, -, -, rfl⟩ := h
      simp; omega
  | globalGet x =>
    obtain ⟨_, _, _, hit⟩ := hi.globalGet_inv; cases hit
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, g⟩, -, h⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; simp
  | intBinOp t op =>
    have hit := hi.intBinOp_inv; cases hit
    simp only [constInstr?] at h
    split at h
    · cases hp : pop2? vs with
      | none => simp [hp] at h
      | some pv =>
        rcases pv with ⟨pre, v, w⟩
        have hl := pop2?_len hp
        simp only [hp, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, _, -, h⟩ := h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h; simp; omega
        · cases h
    · cases h
  | anyConvertExtern =>
    obtain ⟨_, hit⟩ := hi.anyConvertExtern_inv; cases hit
    simp only [constInstr?] at h
    cases hp : pop1? vs with
    | none => simp [hp] at h
    | some pv =>
      rcases pv with ⟨pre, v⟩
      have hl := pop1?_len hp
      simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
      split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
        (obtain ⟨-, rfl⟩ := h; simp; omega)
  | externConvertAny =>
    obtain ⟨_, hit⟩ := hi.externConvertAny_inv; cases hit
    simp only [constInstr?] at h
    cases hp : pop1? vs with
    | none => simp [hp] at h
    | some pv =>
      rcases pv with ⟨pre, v⟩
      have hl := pop1?_len hp
      simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
          (obtain ⟨-, rfl⟩ := h; simp; omega)
      · cases h
  | structNew x =>
    obtain ⟨d', fs', hd', he', hit⟩ := hi.structNew_inv; cases hit
    simp only [constInstr?] at h
    obtain ⟨d, fs, hd, hfs, hl⟩ := structNew?_len h
    obtain rfl := Frame.type?_eq hfa hd hd'
    have := Expand.func_eq (expandStruct?_sound hfs) he'
    cases this
    simp only [List.length_map, List.length_singleton]
    simpa [Ty.length] using hl
  | structNewDefault x =>
    obtain ⟨_, _, _, _, hit⟩ := hi.structNewDefault_inv; cases hit
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨d, hd, fs, hfs, dvs, hdvs, h⟩ := h
    obtain ⟨d₂, fs₂, hd₂, hfs₂, hl⟩ := structNew?_len h
    rw [hd] at hd₂; cases hd₂
    rw [hfs] at hfs₂; cases hfs₂
    have := mapM_length_ca hdvs
    simp only [List.length_append, Ty.length] at hl
    simp only [List.length_nil, List.length_singleton]
    omega
  | arrayNew x =>
    obtain ⟨_, _, _, _, _, hit⟩ := hi.arrayNew_inv; cases hit
    simp only [constInstr?] at h
    cases hp : pop2? vs with
    | none => simp [hp] at h
    | some pv =>
      rcases pv with ⟨pre, v, n⟩
      have hl := pop2?_len hp
      simp only [hp, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨k, -, h⟩ := h
      have := arrayNewFixed?_len h
      simp only [List.length_append, List.length_replicate] at this
      simp only [List.length_cons, List.length_nil]
      omega
  | arrayNewDefault x =>
    obtain ⟨_, _, _, _, _, hit⟩ := hi.arrayNewDefault_inv; cases hit
    simp only [constInstr?] at h
    cases hp : pop1? vs with
    | none => simp [hp] at h
    | some pv =>
      rcases pv with ⟨pre, n⟩
      have hl := pop1?_len hp
      simp only [hp, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨k, -, _, -, _, -, _, -, h⟩ := h
      have := arrayNewFixed?_len h
      simp only [List.length_append, List.length_replicate] at this
      simp only [List.length_cons, List.length_nil]
      omega
  | arrayNewFixed x n =>
    obtain ⟨_, _, _, _, _, hit⟩ := hi.arrayNewFixed_inv; cases hit
    simp only [constInstr?] at h
    have := arrayNewFixed?_len h
    simp only [List.length_replicate, List.length_singleton]
    omega
  | _ => simp [constInstr?] at h

/-- **Arity of the constant fold on typed code.** -/
theorem cfold_arity {C : Context} {e : List Instr} {it : InstrType} (h : InstrsOk C e it) :
    ∀ {f : Frame} {s s' : Store H} {vs ws : List Val}, f.module.types = C.types →
      it.params.length ≤ vs.length → cfold f s vs e = some (s', ws) →
      ws.length + it.params.length = vs.length + it.results.length := by
  induction h using InstrsOk.ind with
  | nil =>
    intro f s s' vs ws _ _ hc
    simp only [cfold_nil, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨-, rfl⟩ := hc; simp
  | instr hi =>
    intro f s s' vs ws hfa _ hc
    rw [cfold_cons] at hc
    simp only [Option.bind_eq_some_iff, cfold_nil, Option.some.injEq] at hc
    obtain ⟨⟨s₁, w₁⟩, h₁, hc⟩ := hc
    cases hc
    exact constInstr?_len hfa h₁ hi
  | seq h₁ _ h₂ ih₁ ih₂ =>
    intro f s s' vs ws hfa hl hc
    rw [cfold_append] at hc
    simp only [Option.bind_eq_some_iff] at hc
    obtain ⟨⟨s₁, w₁⟩, hc₁, hc₂⟩ := hc
    have e₁ := ih₁ hfa hl hc₁
    have e₂ := ih₂ (hfa.trans (Context.initLocals_types_ca _ _).symm) (by simp only at hl e₁ ⊢; omega) hc₂
    simp only at e₁ e₂ ⊢
    omega
  | cons hi _ hs ih =>
    intro f s s' vs ws hfa hl hc
    rw [cfold_cons] at hc
    simp only [Option.bind_eq_some_iff] at hc
    obtain ⟨⟨s₁, w₁⟩, hc₁, hc₂⟩ := hc
    have e₁ := constInstr?_len hfa hc₁ hi
    have e₂ := ih (hfa.trans (Context.initLocals_types_ca _ _).symm) (by simp at hl ⊢; omega) hc₂
    simp only at e₁ e₂ hl ⊢
    omega
  | sub _ hs _ ih =>
    intro f s s' vs ws hfa hl hc
    have hp := List.Forall₂.length_eq hs.1
    have hr := List.Forall₂.length_eq hs.2.1
    have := ih hfa (by omega) hc
    omega
  | frame _ _ ih =>
    intro f s s' vs ws hfa hl hc
    simp only [List.length_append] at hl ⊢
    have := ih hfa (by simp only at hl ⊢; omega) hc
    simp only at this
    omega

/-- A validated constant expression of type `t` evaluates to exactly one value,
keeps the frame, and `evalConst?` finds it, provided the frame's types agree
with the validation context. -/
theorem evalConst?_of_exprOkConst {P : Profile} {host : HostSemantics H} {C : Context}
    {e : Expr} {t : CValType} (he : ExprOkConst C e t) {f : Frame} (hfa : f.module.types = C.types)
    {s s' : Store H} {f' : Frame} {vs : List Val} (h : EvalExpr P host s f e s' f' vs) :
    f' = f ∧ ∃ v, vs = [v] ∧ evalConst? s f e = some (s', v) := by
  have hc : ∀ i ∈ e, i.IsConstI := fun i hi => (he.const i hi).isConstI
  obtain ⟨hf, hr⟩ := steps_cfold (s := s) (f := f) (vs := []) (e := e) h (by simp) hc rfl
  have hl := cfold_arity he.typed hfa (by simp) hr
  simp only [List.length_nil, Nat.add_zero, List.length_singleton, Nat.zero_add] at hl
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hl
  exact ⟨hf, v, rfl, (evalConst?_complete hc (hf ▸ h)).2⟩

end Silmaril.Wasm.Execution.Core
