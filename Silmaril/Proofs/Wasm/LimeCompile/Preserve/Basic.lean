module

public import Silmaril.Wasm.LimeCompile.Preserve.Defs
public import Silmaril.Wasm.Component.Lime1Inst.Thms

/-!
# The Lime-preserving variant: proofs

* `elemsCanon_toCore`, `funcrefElems_eq`: Lime1 images have `funcref` element segments, and on
  such modules `funcrefElems` is the identity;
* `limeView_eq_some_iff`: `limeView M = some l ↔ l.toCore = M`;
* `limePres_preserving`, `limePres_correct`, `limePres_eq_self_iff`;
* `naive_not_identity`: the bare decoder short-circuit returns a module whose Core image differs
  from its input;
* `instr_retract`: the Lime1 instruction decoder is an exact retraction (derived from
  `Lime1Inst.module_retract` through a one-function module);
* `exprCompile_instrPres_toCore`: the instruction-level variant is the identity on Lime1 code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Preserve

open Silmaril.Wasm Silmaril.Wasm.LimeCompile.Preserve

theorem elemsCanon_toCore (l : Lime1.Module) : ElemsCanon l.toCore = true := by
  simp [ElemsCanon, Lime1.Module.toCore, Lime1.Elem.toCore]

theorem funcrefElems_eq {M : Silmaril.Wasm.Module} (h : ElemsCanon M = true) :
    Silmaril.Wasm.Component.Lime1Inst.funcrefElems M = M := by
  have hm : M.elems.map (fun e => { e with type := V1.funcref }) = M.elems := by
    conv_rhs => rw [← List.map_id M.elems]
    apply List.map_congr_left
    intro e he
    have he' := List.all_eq_true.1 h e he
    simp only [decide_eq_true_eq] at he'
    cases e
    simp_all
  cases M
  simp_all [Silmaril.Wasm.Component.Lime1Inst.funcrefElems,
    Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems]

theorem limeView_toCore (l : Lime1.Module) : limeView l.toCore = some l := by
  simp [limeView, elemsCanon_toCore]

theorem limeView_retract {M : Silmaril.Wasm.Module} {l : Lime1.Module}
    (h : limeView M = some l) : l.toCore = M := by
  unfold limeView at h
  split at h
  · rename_i l' hl'
    split at h
    · rename_i hc
      cases h
      rw [Silmaril.Wasm.Component.Lime1Inst.module_retract hl', funcrefElems_eq hc]
    · cases h
  · cases h

theorem limeView_eq_some_iff {M : Silmaril.Wasm.Module} {l : Lime1.Module} :
    limeView M = some l ↔ l.toCore = M := by
  constructor
  · exact limeView_retract
  · rintro rfl
    exact limeView_toCore l

theorem limeView_eq_none_iff {M : Silmaril.Wasm.Module} :
    limeView M = none ↔ ∀ l : Lime1.Module, l.toCore ≠ M := by
  constructor
  · intro h l hl
    rw [← limeView_eq_some_iff] at hl
    simp [h] at hl
  · intro h
    cases hv : limeView M with
    | none => rfl
    | some l => exact absurd (limeView_retract hv) (h l)

theorem limePres_preserving (c : Compiler) : LimePreserving (limePres c) := by
  intro l
  simp [limePres, limeView_toCore]

theorem limePres_of_nonLime (c : Compiler) {M : Silmaril.Wasm.Module}
    (h : ∀ l : Lime1.Module, l.toCore ≠ M) : limePres c M = c M := by
  simp [limePres, limeView_eq_none_iff.2 h]

theorem limePres_correct {R : Silmaril.Wasm.Module → Silmaril.Wasm.Module → Prop}
    (hR : ∀ M, R M M) {c : Compiler} (hc : Correct R c) : Correct R (limePres c) := by
  intro M l h
  cases hv : limeView M with
  | none =>
    simp only [limePres, hv] at h
    exact hc M l h
  | some l' =>
    simp only [limePres, hv, Option.some.injEq] at h
    subst h
    rw [limeView_retract hv]
    exact hR M

theorem limePres_eq_self_iff (c : Compiler) : limePres c = c ↔ LimePreserving c := by
  constructor
  · intro h
    rw [← h]
    exact limePres_preserving c
  · intro hc
    funext M
    cases hv : limeView M with
    | none => simp [limePres, hv]
    | some l =>
      simp only [limePres, hv]
      rw [← limeView_retract hv, hc l]

/-- A Core module with one element segment typed `(ref func)` (non-null). -/
def refFuncElemModule : Silmaril.Wasm.Module :=
  { elems := [⟨⟨false, .abstract .func⟩, [], .active ⟨0⟩ []⟩] }

/-- Its Lime1 decoding. -/
def refFuncElemLime : Lime1.Module :=
  { elems := [⟨⟨0⟩, [], []⟩] }

theorem refFuncElem_ofCore :
    Lime1.Module.ofCore? refFuncElemModule = some refFuncElemLime := by
  simp [Lime1.Module.ofCore?, refFuncElemModule, refFuncElemLime, Lime1.Elem.ofCore?,
    Lime1.Expr.ofCore?, V1.funcref]

theorem refFuncElem_toCore_ne : refFuncElemLime.toCore ≠ refFuncElemModule := by
  intro h
  have h' := congrArg (fun M : Silmaril.Wasm.Module => M.elems.map Elem.type) h
  simp [Lime1.Module.toCore, refFuncElemLime, refFuncElemModule, Lime1.Elem.toCore,
    V1.funcref] at h'

theorem naive_not_identity (c : Compiler) :
    naivePres c refFuncElemModule = some refFuncElemLime ∧
      refFuncElemLime.toCore ≠ refFuncElemModule := by
  refine ⟨?_, refFuncElem_toCore_ne⟩
  simp [naivePres, refFuncElem_ofCore]

theorem naivePres_correct {R : Silmaril.Wasm.Module → Silmaril.Wasm.Module → Prop}
    (hR : ∀ M, R M (Silmaril.Wasm.Component.Lime1Inst.funcrefElems M)) {c : Compiler}
    (hc : Correct R c) : Correct R (naivePres c) := by
  intro M l h
  cases hv : Lime1.Module.ofCore? M with
  | none =>
    simp only [naivePres, hv] at h
    exact hc M l h
  | some l' =>
    simp only [naivePres, hv, Option.some.injEq] at h
    subst h
    rw [Silmaril.Wasm.Component.Lime1Inst.module_retract hv]
    exact hR M

/-! ## Instruction level -/

theorem instr_retract {i : Silmaril.Wasm.Instr} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? i = some j) : Lime1.Instr.toCore j = i := by
  let M : Silmaril.Wasm.Module := { funcs := [⟨⟨0⟩, [], [i]⟩] }
  let l : Lime1.Module := { funcs := [⟨⟨0⟩, [], [j]⟩] }
  have hM : Lime1.Module.ofCore? M = some l := by
    simp [M, l, Lime1.Module.ofCore?, Lime1.Func.ofCore?, Lime1.Expr.ofCore?, h]
  have hr := congrArg (fun M : Silmaril.Wasm.Module => M.funcs.map Func.body)
    (Silmaril.Wasm.Component.Lime1Inst.module_retract hM)
  simpa [M, l, Lime1.Module.toCore, Lime1.Func.toCore, Lime1.Expr.toCore,
    Silmaril.Wasm.Component.Lime1Inst.funcrefElems,
    Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems] using hr

theorem instrPres_lime (t : InstrCompiler) {i : Silmaril.Wasm.Instr} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? i = some j) :
    instrPres t i = some [j] ∧ Lime1.Expr.toCore [j] = [i] := by
  refine ⟨by simp [instrPres, h], ?_⟩
  simp [Lime1.Expr.toCore_eq_map, instr_retract h]

theorem instrPres_nonLime (t : InstrCompiler) {i : Silmaril.Wasm.Instr}
    (h : Lime1.Instr.ofCore? i = none) : instrPres t i = t i := by
  simp [instrPres, h]

theorem mapM_instrPres_toCore (t : InstrCompiler) :
    ∀ e : Lime1.Expr, (e.map Lime1.Instr.toCore).mapM (instrPres t) = some (e.map fun j => [j])
  | [] => rfl
  | j :: e => by
    simp [instrPres, mapM_instrPres_toCore t e]

theorem exprCompile_instrPres_toCore (t : InstrCompiler) (e : Lime1.Expr) :
    exprCompile (instrPres t) (Lime1.Expr.toCore e) = some e := by
  rw [exprCompile, Lime1.Expr.toCore_eq_map, mapM_instrPres_toCore]
  induction e with
  | nil => rfl
  | cons j e ih => simpa using ih

end Silmaril.Proofs.Wasm.LimeCompile.Preserve
