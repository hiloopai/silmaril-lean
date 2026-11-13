module

public import Silmaril.Wasm.V2.Execution.Instantiation
public import Silmaril.Raw.Wasm.Versions.V2.Validation.Inversion

/-!
# WebAssembly 2.0 reduction: closure properties and initializer soundness

Closure of `Steps` and `Diverges` under the two evaluation contexts of
`8-reduction:161-169` together with the imported `Step/ctxt-instrs` (deviation 1
of `Step.lean`, from wasm-1.0 `8-reduction:165-168`), and the fact that the
constant expressions
`Expr_ok_const` (`6-typing:564`) accepts really do evaluate, in finitely many
steps and without touching the store, to the value they denote. The latter is
what makes the `Eval_expr` premises of `$instantiate` (`9-module:184-185`)
satisfiable, and it is why those premises may write the **same** state `z` on
both sides.

## What is already proved elsewhere

`Silmaril.Wasm.V2.Execution.Step` already proves the three `Steps` closure
properties and two of the `Diverges` ones, so they are *not* restated here:

| statement | where |
| --- | --- |
| `Steps.ctxtInstrs` | `Step.lean` |
| `Steps.ctxtLabel` | `Step.lean` |
| `Steps.ctxtFrame` | `Step.lean` |
| `Diverges.label` | `Step.lean` |
| `Diverges.frame` | `Step.lean` |

`Steps.ctxtInstrs` holds for *every* rule only because `Step.ctxtInstrs` is in
the relation — deviation 1 of `Step.lean`'s docstring, SpecTec 2.0's missing
`Step/ctxt-instrs`. This file adds the remaining closure property,
`Diverges.ctxtInstrs`, and the `Diverges` introduction rules.

## Constant expressions denote values

A 2.0 constant expression is a *single* instruction: `Instr_const`
(`6-typing:539-557`) lists five forms, each of which consumes nothing and
produces exactly one value, and `Expr_ok_const` demands the result type
`[t]`. `exprOkConst_singleton` is that statement, proved. `constInstr?` and
`constExpr?` are the denotation — the 2.0 analogue of
`Silmaril.Wasm.V1.Execution.constInstr?`/`constExpr?` — and
`exprOkConst_evalExpr` is the soundness theorem: under the (necessary)
assumption that the module instance resolves the indices the context declares,
the denotation exists and `Eval_expr` relates the expression to it, in at most
one step and with the store and the frame unchanged.

The two hypotheses `hfuncs` and `hglobals` of `exprOkConst_evalExpr` are the
agreement between the module instance and the validation context that a store
typing would supply. 2.0 SpecTec has no store typing (`6-typing` stops at
`Module_ok`), so they are spelled out; `Moduleinst_ok` of the eventual soundness
unit implies both.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Divergence is closed under the evaluation contexts -/

/-- `Step/ctxt-instrs` for divergence. As for `Steps.ctxtInstrs`, the side
condition `val* =/= eps \/ instr_1* =/= eps` is unnecessary: when both lists are
empty the statement is the hypothesis. -/
theorem Diverges.ctxtInstrs (vs : List Val) (rest : List Admin) {s : Store H} {f : Frame}
    {is : List Admin} (h : Diverges P host ⟨s, f, is⟩) :
    Diverges P host ⟨s, f, vals vs ++ is ++ rest⟩ := by
  rcases Classical.em (vs = [] ∧ rest = []) with ⟨rfl, rfl⟩ | hne
  · simpa using h
  · have hne' : vs ≠ [] ∨ rest ≠ [] := by
      by_contra hc
      exact hne ⟨by simpa using (not_or.mp hc).1, by simpa using (not_or.mp hc).2⟩
    exact InfiniteTrace.map
      (fun c : Config H => (⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩ : Config H))
      (fun _ _ hab => Step.ctxtInstrs hab hne') h

/-- A step into a divergent configuration diverges. -/
theorem Step.diverges {c c' : Config H} (h : Step P host c c') (hd : Diverges P host c') :
    Diverges P host c :=
  InfiniteTrace.fold h hd

/-- A reduction sequence into a divergent configuration diverges. -/
theorem Steps.diverges {c c' : Config H} (h : Steps P host c c') (hd : Diverges P host c') :
    Diverges P host c :=
  InfiniteTrace.of_steps h hd

/-- A configuration that steps to itself diverges. This is what makes
`Step.callAddrHostDiv` (deviation 3 of `Step.lean`) observable. -/
theorem Step.diverges_self {c : Config H} (h : Step P host c c) : Diverges P host c :=
  InfiniteTrace.coinduct (fun x => x = c) (fun _ ha => ⟨c, ha ▸ h, rfl⟩) rfl

/-! ## The denotation of a constant expression -/

/-- The value a 2.0 constant instruction denotes in a given state. The five
cases are exactly the five rules of `Instr_const` (`6-typing:539-557`); every
other instruction has no denotation. -/
def constInstr? (s : Store H) (mi : ModuleInst) : Instr → Option Val
  | .intConst t c => some (.num ⟨.int t, c⟩)
  | .floatConst t c => some (.num ⟨.float t, c⟩)
  | .vecConst c => some (.vec c)
  | .refNull rt => some (.ref (.null rt))
  | .refFunc x => (mi.funcAddr? x).map fun a => .ref (.funcAddr a)
  | .globalGet x => (mi.globalAddr? x).bind fun a => (s.globalInst? a).map GlobalInst.value
  | _ => none

/-- The value a 2.0 constant *expression* denotes. A constant expression is a
single instruction (`exprOkConst_singleton`), so no sequencing is needed. -/
def constExpr? (s : Store H) (mi : ModuleInst) : Expr → Option Val
  | [i] => constInstr? s mi i
  | _ => none

/-- A constant instruction reaches its denotation in at most one step, leaving
the store and the frame untouched. -/
theorem evalExpr_of_constInstr? {s : Store H} {f : Frame} {i : Instr} {v : Val}
    (h : constInstr? s f.module i = some v) : EvalExpr P host s f [i] s f [v] := by
  cases i with
  | intConst t c => simp only [constInstr?, Option.some.injEq] at h; subst h; exact .refl
  | floatConst t c => simp only [constInstr?, Option.some.injEq] at h; subst h; exact .refl
  | vecConst c => simp only [constInstr?, Option.some.injEq] at h; subst h; exact .refl
  | refNull rt => simp only [constInstr?, Option.some.injEq] at h; subst h; exact .refl
  | refFunc x =>
    simp only [constInstr?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact Step.steps (Step.read (ReadStep.refFunc ha))
  | globalGet x =>
    simp only [constInstr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, gi, hgi, rfl⟩ := h
    refine Step.steps (Step.read (ReadStep.globalGet (gi := gi) ?_))
    simp [State.global?, ha, hgi]
  | _ => simp [constInstr?] at h

/-- A constant expression reaches its denotation in at most one step, leaving
the store and the frame untouched. -/
theorem evalExpr_of_constExpr? {s : Store H} {f : Frame} {e : Expr} {v : Val}
    (h : constExpr? s f.module e = some v) : EvalExpr P host s f e s f [v] := by
  match e with
  | [] => simp [constExpr?] at h
  | [i] => exact evalExpr_of_constInstr? h
  | _ :: _ :: _ => simp [constExpr?] at h

/-! ## Constant expressions are single instructions -/

/-- Every constant instruction consumes nothing and produces exactly one
(non-`BOT`) value: `Instr_const` (`6-typing:539-557`) against the matching
`Instr_ok` rules. -/
theorem InstrConst.instrOk_shape {C : Context} {i : Instr} {it : InstrType}
    (hc : InstrConst C i) (h : InstrOk C i it) : ∃ u : ValType, it = ⟨[], [.val u]⟩ := by
  cases hc with
  | intConst t c => exact ⟨_, InstrOk.valueType?_eq (t := .num (.int t)) rfl h⟩
  | floatConst t c => exact ⟨_, InstrOk.valueType?_eq (t := .num (.float t)) rfl h⟩
  | vecConst c => exact ⟨_, InstrOk.valueType?_eq (t := .vec .v128) rfl h⟩
  | refNull rt => exact ⟨_, InstrOk.valueType?_eq (t := .ref rt) rfl h⟩
  | refFunc x => exact ⟨.ref .funcref, (InstrOk.refFunc_inv h).2.2⟩
  | globalGet hx hmut =>
    obtain ⟨gt, -, hit⟩ := InstrOk.globalGet_inv h
    exact ⟨gt.value, hit⟩

/-- A sequence of constant instructions pushes exactly one value per
instruction. -/
theorem ExprConst.length_eq {C : Context} : ∀ {e : Expr} {t₁ t₂ : CResultType},
    ExprConst C e → InstrsOk C e ⟨t₁, t₂⟩ → t₂.length = t₁.length + e.length
  | [], t₁, t₂, _, h => by
    have := CResultType.sub_length (InstrsOk.nil_inv h)
    simpa using this.symm
  | i :: is, t₁, t₃, hc, h => by
    obtain ⟨t₂, it, hit, ⟨ts, hw₁, hw₂⟩, hrest⟩ := InstrsOk.cons_inv h
    obtain ⟨u, rfl⟩ := InstrConst.instrOk_shape (hc i (by simp)) hit
    have h₁ : t₁.length = ts.length := by simpa using CResultType.sub_length hw₁
    have h₂ : t₂.length = ts.length + 1 := by simpa using (CResultType.sub_length hw₂).symm
    have ih := ExprConst.length_eq (C := C) (fun j hj => hc j (by simp [hj])) hrest
    simp only [List.length_cons]
    omega

/-- **A 2.0 constant expression is a single instruction**, and that instruction
has exactly the type the expression is given. `Instr_const` (`6-typing:539`)
has five forms, each of arity `eps -> t`, and `Expr_ok_const` (`6-typing:564`)
demands one result; 2.0 has no extended constant expressions, so there is
nothing else in the language. -/
theorem exprOkConst_singleton {C : Context} {e : Expr} {t : ValType}
    (h : ExprOkConst C e t) :
    ∃ i : Instr, e = [i] ∧ InstrConst C i ∧ InstrOk C i ⟨[], [.val t]⟩ := by
  have hlen : e.length = 1 := by
    have := ExprConst.length_eq h.const h.typed
    simpa using this.symm
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨it, hit, ts, hw₁, hw₂⟩ := InstrsOk.singleton_inv h.typed
  have hc : InstrConst C i := h.const i (by simp)
  obtain ⟨u, rfl⟩ := InstrConst.instrOk_shape hc hit
  have hts : ts = [] := by
    have := CResultType.sub_length hw₁
    simpa using List.eq_nil_of_length_eq_zero (by simpa using this.symm)
  subst hts
  simp only [List.nil_append] at hw₂
  have hsub : CValType.Sub (.val u) (.val t) := (List.forall₂_cons.mp hw₂).1
  rcases CValType.sub_iff.mp hsub with heq | hbot
  · injection heq with heq
    subst heq
    exact ⟨i, rfl, hc, hit⟩
  · exact absurd hbot (by simp)

/-! ## Initializer soundness -/

/-- **Every constant expression `Expr_ok_const` accepts evaluates, in finitely
many steps and without changing the state, to the value its initializer
denotes.**

The two hypotheses are the module-instance/context agreement a store typing
would supply; see the module docstring. -/
theorem exprOkConst_evalExpr {C : Context} {s : Store H} {f : Frame} {e : Expr} {t : ValType}
    (h : ExprOkConst C e t)
    (hfuncs : ∀ x : FuncIdx, x.toNat < C.funcs.length → (f.module.funcAddr? x).isSome)
    (hglobals : ∀ x : GlobalIdx, x.toNat < C.globals.length →
      ∃ a : GlobalAddr, f.module.globalAddr? x = some a ∧ (s.globalInst? a).isSome) :
    ∃ v : Val, constExpr? s f.module e = some v ∧ EvalExpr P host s f e s f [v] := by
  obtain ⟨i, rfl, hc, hit⟩ := exprOkConst_singleton h
  have hden : ∃ v : Val, constInstr? s f.module i = some v := by
    cases hc with
    | intConst t c => exact ⟨_, rfl⟩
    | floatConst t c => exact ⟨_, rfl⟩
    | vecConst c => exact ⟨_, rfl⟩
    | refNull rt => exact ⟨_, rfl⟩
    | refFunc x =>
      obtain ⟨⟨ft, hft⟩, -, -⟩ := InstrOk.refFunc_inv hit
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
        (hfuncs x (List.getElem?_eq_some_iff.mp hft).1)
      exact ⟨.ref (.funcAddr a), by simp [constInstr?, ha]⟩
    | @globalGet x gt hx hmut =>
      obtain ⟨a, ha, hgi⟩ := hglobals x (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨gi, hgi⟩ := Option.isSome_iff_exists.mp hgi
      exact ⟨gi.value, by simp [constInstr?, ha, hgi]⟩
  obtain ⟨v, hv⟩ := hden
  exact ⟨v, hv, evalExpr_of_constInstr? hv⟩

/-- The denotation has the type the expression is given, provided the store's
globals agree with the context. -/
theorem constExpr?_type {C : Context} {s : Store H} {f : Frame} {e : Expr} {t : ValType}
    {v : Val} (h : ExprOkConst C e t) (hv : constExpr? s f.module e = some v)
    (hglobals : ∀ (x : GlobalIdx) (gt : GlobalType) (a : GlobalAddr) (gi : GlobalInst),
      C.globals[x.toNat]? = some gt → f.module.globalAddr? x = some a →
      s.globalInst? a = some gi → gi.value.type = gt.value) :
    v.type = t := by
  obtain ⟨i, rfl, hc, hit⟩ := exprOkConst_singleton h
  simp only [constExpr?] at hv
  cases hc with
  | intConst t' c =>
    simp only [constInstr?, Option.some.injEq] at hv
    subst hv
    have := InstrOk.valueType?_eq (t := .num (.int t')) rfl hit
    simp only [InstrType.mk.injEq, List.cons.injEq, CValType.val.injEq] at this
    exact this.2.1.symm ▸ rfl
  | floatConst t' c =>
    simp only [constInstr?, Option.some.injEq] at hv
    subst hv
    have := InstrOk.valueType?_eq (t := .num (.float t')) rfl hit
    simp only [InstrType.mk.injEq, List.cons.injEq, CValType.val.injEq] at this
    exact this.2.1.symm ▸ rfl
  | vecConst c =>
    simp only [constInstr?, Option.some.injEq] at hv
    subst hv
    have := InstrOk.valueType?_eq (t := .vec .v128) rfl hit
    simp only [InstrType.mk.injEq, List.cons.injEq, CValType.val.injEq] at this
    exact this.2.1.symm ▸ rfl
  | refNull rt =>
    simp only [constInstr?, Option.some.injEq] at hv
    subst hv
    have := InstrOk.valueType?_eq (t := .ref rt) rfl hit
    simp only [InstrType.mk.injEq, List.cons.injEq, CValType.val.injEq] at this
    exact this.2.1.symm ▸ rfl
  | refFunc x =>
    simp only [constInstr?, Option.map_eq_some_iff] at hv
    obtain ⟨a, -, rfl⟩ := hv
    obtain ⟨-, -, hty⟩ := InstrOk.refFunc_inv hit
    simp only [InstrType.mk.injEq, List.cons.injEq, CValType.val.injEq] at hty
    exact hty.2.1.symm ▸ rfl
  | globalGet hx hmut =>
    simp only [constInstr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
    obtain ⟨a, ha, gi, hgi, rfl⟩ := hv
    obtain ⟨gt, hgt, hty⟩ := InstrOk.globalGet_inv hit
    simp only [InstrType.mk.injEq, List.cons.injEq, CValType.val.injEq] at hty
    rw [hglobals _ _ _ _ hgt ha hgi, hty.2.1]

end Silmaril.Wasm.V2.Execution
