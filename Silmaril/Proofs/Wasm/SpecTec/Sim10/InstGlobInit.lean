module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstValid10
public import Silmaril.Wasm.Component.Lime1Inst.Thms

/-!
# Lime1 initializer values have their declared types, with imported globals

The component work's `Lime1Inst.constExpr?_type` types the value of an initializer evaluated in
a module instance **without** globals, which is all a component (no imports) needs. A module
instantiated into an arbitrary store reads its imported globals with `global.get`. This module
restates the typing for a module instance whose globals are typed by the context:

* `GlobalsTyped s mod C`: every global address of `mod` that the store allocates holds a value
  of the type `C` gives its index;
* **`constExpr?_typeG`**: a typed initializer evaluated in such an instance has its type;
* **`globalsTyped_of_importsMatch`**: Lime1's `ImportsMatch s m imports` gives
  `GlobalsTyped s {globals := imported globals} (initializerContext m)`, the instance and context
  in which `allocate?` evaluates and validation types global initializers.

New proofs; the shape lemmas follow `Lime1Inst/InitType`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstG

open Silmaril.Wasm Silmaril.Wasm.Lime1 Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst GlobalInst ExternVal)
open Silmaril.Proofs.Wasm.Component.Lime1Inst (StackTy stackTy_cons instrType_intConst
  instrType_floatConst instrType_intBinOp constStep_bin)

/-- **The globals of `mod` are typed by `C` in `s`.** -/
def GlobalsTyped {H : Type} (s : Lime1.Execution.Store H) (mod : ModuleInst) (C : Context) :
    Prop :=
  ∀ (x : Nat) a g gt, mod.globals[x]? = some a → s.globals[a.value]? = some g →
    C.globals[x]? = some gt → g.value.type = gt.value

theorem instrType_globalGet {C : Context} {x : GlobalIdx} :
    ∀ {i : Lime1.Instr} {a b : V1.ResultType}, InstrType C i a b → i = .globalGet x →
      ∃ gt, C.globals[x.toNat]? = some gt ∧ b = a ++ [gt.value]
  | _, _, _, .frame pre h, hi => by
    obtain ⟨gt, hg, hb⟩ := instrType_globalGet h hi
    exact ⟨gt, hg, by rw [hb, List.append_assoc]⟩
  | _, _, _, .globalGet _ h, hi => by cases hi; exact ⟨_, h, rfl⟩
  | _, _, _, .nop .., hi | _, _, _, .unreachable .., hi | _, _, _, .drop .., hi
  | _, _, _, .select .., hi | _, _, _, .block .., hi | _, _, _, .loop .., hi
  | _, _, _, .if_ .., hi | _, _, _, .br .., hi | _, _, _, .brIf .., hi
  | _, _, _, .brTable .., hi | _, _, _, .return_ .., hi | _, _, _, .call .., hi
  | _, _, _, .callIndirect .., hi | _, _, _, .localGet .., hi | _, _, _, .localSet .., hi
  | _, _, _, .localTee .., hi | _, _, _, .intConst .., hi | _, _, _, .globalSet .., hi
  | _, _, _, .intLoad .., hi | _, _, _, .floatLoad .., hi | _, _, _, .intStore .., hi
  | _, _, _, .floatStore .., hi | _, _, _, .memorySize .., hi | _, _, _, .memoryGrow .., hi
  | _, _, _, .memoryFill .., hi | _, _, _, .memoryCopy .., hi | _, _, _, .floatConst .., hi
  | _, _, _, .intUnOp .., hi | _, _, _, .intBinOp .., hi | _, _, _, .intTestOp .., hi
  | _, _, _, .intRelOp .., hi | _, _, _, .floatUnOp .., hi | _, _, _, .floatBinOp .., hi
  | _, _, _, .floatRelOp .., hi | _, _, _, .convert .., hi => nomatch hi

/-- The shapes of a successful constant step. -/
theorem constStep_shapeG {H : Type} {s : Lime1.Execution.Store H} {mod : ModuleInst}
    {i : Lime1.Instr} {st st' : List Value}
    (h : Lime1.Execution.constStep? s mod i st = some st') :
    (∃ t x, i = .intConst t x ∧ st' = ⟨.int t, x⟩ :: st) ∨
      (∃ t x, i = .floatConst t x ∧ st' = ⟨.float t, x⟩ :: st) ∨
      (∃ t op y x rest z, i = .intBinOp t op ∧ st = y :: x :: rest ∧ y.type = .int t ∧
        x.type = .int t ∧ st' = z :: rest ∧ z.type = .int t) ∨
      (∃ x a g, i = .globalGet x ∧ mod.globals[x.toNat]? = some a ∧
        s.globals[a.value]? = some g ∧ st' = g.value :: st) := by
  cases i with
  | intConst t x =>
    have h' : some (Value.int t x :: st) = some st' := by simpa only [
      Lime1.Execution.constStep?, Lime1.Execution.constInstr?, Option.map_some] using h
    exact .inl ⟨t, x, rfl, (Option.some.inj h').symm⟩
  | floatConst t x =>
    have h' : some (Value.float t x :: st) = some st' := by simpa only [
      Lime1.Execution.constStep?, Lime1.Execution.constInstr?, Option.map_some] using h
    exact .inr (.inl ⟨t, x, rfl, (Option.some.inj h').symm⟩)
  | intBinOp t op => exact .inr (.inr (.inl (constStep_bin h)))
  | globalGet x =>
    simp only [Lime1.Execution.constStep?, Lime1.Execution.constInstr?, Option.bind_eq_bind,
      Option.map_eq_some_iff, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨v, ⟨a, ha, g, hg, rfl⟩, rfl⟩ := h
    exact .inr (.inr (.inr ⟨x, a, g, rfl, ha, hg, rfl⟩))
  | _ => simp [Lime1.Execution.constStep?, Lime1.Execution.constInstr?] at h

/-- A `global.get` step keeps the stack typed. -/
theorem step_ty_globalGet {H : Type} {s : Lime1.Execution.Store H} {mod : ModuleInst}
    {C : Context} (hG : GlobalsTyped s mod C) {x : GlobalIdx} {a b : V1.ResultType}
    (hi : InstrType C (.globalGet x) a b) {st : List Value} {ad : Execution.Runtime.GlobalAddr}
    {g : GlobalInst} (ha : mod.globals[x.toNat]? = some ad) (hg : s.globals[ad.value]? = some g)
    (hst : StackTy st a) : StackTy (g.value :: st) b := by
  obtain ⟨gt, hgt, rfl⟩ := instrType_globalGet hi rfl
  have e : g.value.type = gt.value := hG _ _ _ _ ha hg hgt
  rw [← e]
  exact stackTy_cons hst

/-- One successful constant step keeps the stack typed. -/
theorem step_tyG {H : Type} {s : Lime1.Execution.Store H} {mod : ModuleInst} {C : Context}
    (hG : GlobalsTyped s mod C) {i : Lime1.Instr} {a b : V1.ResultType}
    (hi : InstrType C i a b) {st st' : List Value}
    (h : Lime1.Execution.constStep? s mod i st = some st') (hst : StackTy st a) :
    StackTy st' b := by
  rcases constStep_shapeG h with ⟨t, x, rfl, rfl⟩ | ⟨t, x, rfl, rfl⟩ |
    ⟨t, op, y, x, rest, z, rfl, rfl, hy, hx, rfl, hz⟩ | ⟨x, ad, g, rfl, ha, hg, rfl⟩
  · rw [instrType_intConst hi rfl]; exact stackTy_cons hst
  · rw [instrType_floatConst hi rfl]; exact stackTy_cons hst
  · obtain ⟨pre, rfl, rfl⟩ := instrType_intBinOp hi rfl
    have hr : (rest.map (·.type)).reverse ++ [NumType.int t, .int t] =
        pre ++ [.int t, .int t] := by
      simpa only [StackTy, List.map_cons, List.reverse_cons, hx, hy, List.append_assoc,
        List.cons_append, List.nil_append] using hst
    have hpre : (rest.map (·.type)).reverse = pre := List.append_inj_left' hr rfl
    have hz' : StackTy (z :: rest) (pre ++ [z.type]) := stackTy_cons hpre
    rwa [hz] at hz'
  · exact step_ty_globalGet hG hi ha hg hst

/-- A typed sequence of successful constant steps ends in a stack of the result type. -/
theorem fold_tyG {H : Type} {s : Lime1.Execution.Store H} {mod : ModuleInst} {C : Context}
    (hG : GlobalsTyped s mod C) :
    ∀ {es : Lime1.Expr} {a c : V1.ResultType} {st st' : List Value}, ExprType C es a c →
      StackTy st a →
      es.foldlM (fun stack i => Lime1.Execution.constStep? s mod i stack) st = some st' →
      StackTy st' c
  | [], _, _, _, _, he, hst, h => by
    cases he
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ hst
  | i :: es, _, _, _, _, .cons hi his, hst, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    exact fold_tyG hG his (step_tyG hG hi h₁ hst) h₂

/-- **A typed Lime1 initializer evaluates to a value of its type**, in a module instance whose
globals are typed by the context. -/
theorem constExpr?_typeG {H : Type} {s : Lime1.Execution.Store H} {mod : ModuleInst}
    {C : Context} (hG : GlobalsTyped s mod C) {es : Lime1.Expr} {t : V1.ValType}
    (he : ExprType C es [] [t]) {v : Value}
    (h : Lime1.Execution.constExpr? s mod es = some v) : v.type = t := by
  simp only [Lime1.Execution.constExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vs, hvs, hv⟩ := h
  have hty := fold_tyG hG he (st := []) rfl hvs
  rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at hv
  subst hv
  simpa [StackTy] using hty

/-! ## From `ImportsMatch` -/

/-- The global import types of a list of imports. -/
def importGlobalTypes (is : List V1.Import) : List V1.GlobalType :=
  is.filterMap fun i => match i.desc with | .global gt => some gt | _ => none

/-- The global addresses of a list of external values. -/
def externGlobals (es : List ExternVal) : List Execution.Runtime.GlobalAddr :=
  es.filterMap fun e => match e with | .global a => some a | _ => none

/-- A matched import list matches its global imports pointwise. -/
theorem globals_of_importsMatch {H : Type} {s : Lime1.Execution.Store H}
    {types : List V1.FuncType} :
    ∀ {is : List V1.Import} {es : List ExternVal},
      List.Forall₂ (fun i e => ∃ et, importType? types i.desc = some et ∧
        Lime1.Execution.ExternMatches s e et) is es →
      List.Forall₂ (fun gt a => ∃ g, s.globals[a.value]? = some g ∧ g.value.type = gt.value)
        (importGlobalTypes is) (externGlobals es)
  | [], [], .nil => .nil
  | i :: is, e :: es, .cons ⟨et, hit, hm⟩ hrest => by
    have ih := globals_of_importsMatch hrest
    rcases i with ⟨mn, nm, desc⟩
    cases desc with
    | global gt =>
      simp only [importType?, Option.some.injEq] at hit
      subst hit
      cases hm with
      | global a g _ hf hty _ => exact .cons ⟨g, hf, hty⟩ ih
    | func ti =>
      simp only [importType?, Option.map_eq_some_iff] at hit
      obtain ⟨ft, -, rfl⟩ := hit
      cases hm
      exact ih
    | table tt =>
      simp only [importType?, Option.some.injEq] at hit
      subst hit
      cases hm
      exact ih
    | memory mt =>
      simp only [importType?, Option.some.injEq] at hit
      subst hit
      cases hm
      exact ih

/-- Pointwise reading of `List.Forall₂`. -/
theorem forall₂_getElem? {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a : α} {b : β},
      l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, h₁, _ => by simp at h₁
  | _, _, .cons hr _, 0, _, _, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    exact hr
  | _, _, .cons _ hs, i + 1, _, _, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h₁ h₂
    exact forall₂_getElem? hs h₁ h₂

/-- **`ImportsMatch` types the imported globals** in the instance and context of the module's
global initializers. -/
theorem globalsTyped_of_importsMatch {H : Type} {s : Lime1.Execution.Store H}
    {m : Lime1.Module} {imports : List ExternVal}
    (hi : Lime1.Execution.ImportsMatch s m imports) :
    GlobalsTyped s { globals := (Lime1.Execution.importedInstance imports).globals }
      (initializerContext m) := by
  intro x a g gt ha hg hgt
  have e₁ : (importGlobalTypes m.imports)[x]? = some gt := hgt
  have e₂ : (externGlobals imports)[x]? = some a := ha
  obtain ⟨g', hg', hty⟩ := forall₂_getElem? (globals_of_importsMatch hi) e₁ e₂
  rw [hg] at hg'
  obtain rfl := Option.some.inj hg'
  exact hty

end Silmaril.Wasm.SpecTec.Sim10.InstG
