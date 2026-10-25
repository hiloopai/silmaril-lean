module

public import Silmaril.Wasm.Execution.Core.Instantiation

@[expose] public section

/-! # Computable instantiation for Core 3.0

`instantiate?` computes the configuration of `$instantiate`, parametrised over a
constant-expression evaluator `ev` with a soundness hypothesis `EvalSound`.
Module validity remains a hypothesis of `instantiate?_sound`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Soundness of an initializer evaluator against `EvalExpr`. -/
def EvalSound (P : Profile) (host : HostSemantics H)
    (ev : Store H → Frame → Expr → Option (Store H × Val)) : Prop :=
  ∀ s f e s' v, ev s f e = some (s', v) → EvalExpr P host s f e s' f [v]

section
variable (ev : Store H → Frame → Expr → Option (Store H × Val))

/-- Computable `$evalglobals`. -/
def evalGlobals? : Store H → Frame → List CGlobalType → List Expr →
    Option (Store H × Frame × List Val)
  | s, f, [], [] => some (s, f, [])
  | s, f, g :: gs, e :: es =>
    match ev s f e with
    | none => none
    | some (s', v) =>
      match evalGlobals? (allocGlobal s' g v).1
          { f with module := { f.module with globals := f.module.globals ++ [(allocGlobal s' g v).2] } }
          gs es with
      | none => none
      | some (s'', f'', vs) => some (s'', f'', v :: vs)
  | _, _, _, _ => none

/-- Computable `$evalexprs`: every value must be a reference. -/
def evalExprs? : Store H → Frame → List Expr → Option (Store H × Frame × List Ref)
  | s, f, [] => some (s, f, [])
  | s, f, e :: es =>
    match ev s f e with
    | some (s', .ref r) =>
      match evalExprs? s' f es with
      | none => none
      | some (s'', f'', rs) => some (s'', f'', r :: rs)
    | _ => none

/-- Computable `$evalexprss`. -/
def evalExprss? : Store H → Frame → List (List Expr) → Option (Store H × Frame × List (List Ref))
  | s, f, [] => some (s, f, [])
  | s, f, es :: ess =>
    match evalExprs? ev s f es with
    | none => none
    | some (s', f', rs) =>
      match evalExprss? s' f' ess with
      | none => none
      | some (s'', f'', rss) => some (s'', f'', rs :: rss)

/-- Computable `$instantiate`, following `Instantiate.run`. -/
def instantiate? (s : Store H) (m : Module) (xas : List ExternAddr) : Option (Config H) :=
  if m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32) then
    match evalGlobals? ev s ⟨[], ModuleInst.initial s m xas⟩
        (m.globals.map fun g => ⟨g.type.mutability,
          (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
        (m.globals.map Global.init) with
    | none => none
    | some (s₁, f₁, valsG) =>
      match evalExprs? ev s₁ f₁ (m.tables.map Table.init) with
      | none => none
      | some (s₂, f₂, refsT) =>
        match evalExprss? ev s₂ f₂ (m.elems.map Elem.init) with
        | none => none
        | some (s₃, _, refsE) =>
          match allocModule? s₃ m xas valsG refsT refsE with
          | none => none
          | some (s₄, mi) =>
            some ⟨s₄, { module := mi },
              expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
              expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d) ++
              (match m.start with | some x => [.plain (.call x)] | none => [])⟩
  else none

end

variable {P : Profile} {host : HostSemantics H}
  {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem evalGlobals?_sound (hev : EvalSound P host ev) :
    ∀ {s : Store H} {f : Frame} {gs : List CGlobalType} {es : List Expr}
      {s' : Store H} {f' : Frame} {vs : List Val},
      evalGlobals? ev s f gs es = some (s', f', vs) → EvalGlobals P host s f gs es s' f' vs
  | s, f, [], [], s', f', vs, h => by
    simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact .nil
  | s, f, g :: gs, e :: es, s', f', vs, h => by
    simp only [evalGlobals?] at h
    split at h
    · cases h
    · rename_i s₁ v he
      split at h
      · cases h
      · rename_i s'' f'' vs' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .cons (hev _ _ _ _ _ he) (evalGlobals?_sound hev hr)
  | s, f, [], _ :: _, s', f', vs, h => by simp [evalGlobals?] at h
  | s, f, _ :: _, [], s', f', vs, h => by simp [evalGlobals?] at h

theorem evalExprs?_sound (hev : EvalSound P host ev) :
    ∀ {s : Store H} {f : Frame} {es : List Expr} {s' : Store H} {f' : Frame} {rs : List Ref},
      evalExprs? ev s f es = some (s', f', rs) → EvalExprs P host s f es s' f' rs
  | s, f, [], s', f', rs, h => by
    simp only [evalExprs?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact .nil
  | s, f, e :: es, s', f', rs, h => by
    simp only [evalExprs?] at h
    split at h
    · rename_i s₁ r he
      split at h
      · cases h
      · rename_i s'' f'' rs' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .cons (hev _ _ _ _ _ he) (evalExprs?_sound hev hr)
    · cases h

theorem evalExprss?_sound (hev : EvalSound P host ev) :
    ∀ {s : Store H} {f : Frame} {ess : List (List Expr)} {s' : Store H} {f' : Frame}
      {rss : List (List Ref)},
      evalExprss? ev s f ess = some (s', f', rss) → EvalExprss P host s f ess s' f' rss
  | s, f, [], s', f', rss, h => by
    simp only [evalExprss?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact .nil
  | s, f, es :: ess, s', f', rss, h => by
    simp only [evalExprss?] at h
    split at h
    · cases h
    · rename_i s₁ f₁ rs he
      split at h
      · cases h
      · rename_i s'' f'' rss' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .cons (evalExprs?_sound hev he) (evalExprss?_sound hev hr)

theorem instantiate?_sound (hev : EvalSound P host ev) {s : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} (h : instantiate? ev s m xas = some c)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    Instantiate P host s m xas c := by
  unfold instantiate? at h
  split at h
  · rename_i hb
    split at h
    · cases h
    · rename_i s₁ f₁ valsG hG
      split at h
      · cases h
      · rename_i s₂ f₂ refsT hT
        split at h
        · cases h
        · rename_i s₃ f₃ refsE hE
          split at h
          · cases h
          · rename_i s₄ mi hM
            cases h
            exact ⟨hvalid, hb, s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi,
              evalGlobals?_sound hev hG, evalExprs?_sound hev hT, evalExprss?_sound hev hE, hM, rfl⟩
  · cases h

/-- Computable `$invoke` (already a definition in `Instantiation`). -/
abbrev invoke? (s : Store H) (a : Nat) (vs : List Val) : Config H := invoke s a vs

end Silmaril.Wasm.Execution.Core
