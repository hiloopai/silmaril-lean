module

public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Decidability of subtyping

Computable decision procedures for `Sub` and `ExternSub`, from the checkers
`Sub.check`/`ExternSub.check` of `Subtyping/Check.lean` via `decidable_of_iff`.

The checkers are **sound unconditionally** (`Sub.check_sound`,
`ExternSub.check_sound`), and **complete** for valid types in a well-formed
context (`TypeCtx.Ok`) without `RECS` (every context after the type section,
in particular the closed context `{}` used for import matching and the
component model). Completeness needs these hypotheses because the premise of
`Heaptype_sub/trans` and the termination measure of the supertype search both
rely on validity, so the decision procedures take them as arguments.

For closed goals, `Sub.of_check`/`ExternSub.of_check` turn a kernel `decide`
on the Boolean checker into a proof (see separate subtyping decision examples (not included in this package)).
-/

namespace Silmaril.Wasm.Validation

/-- Decidability of subtyping between valid types in a well-formed context
without `RECS`. -/
def Sub.decide (Δ : TypeCtx) {k : TKind} (a b : Ty k) (hΔ : Δ.Ok) (hr : Δ.recs = [])
    (ha : TyOk Δ a) (hb : TyOk Δ b) : Decidable (Sub Δ a b) :=
  decidable_of_iff _ (Sub.check_iff hΔ hr ha hb)

/-- Decidability of `ExternSub` between valid extern types in a well-formed
context without `RECS` (the component model uses `ExternSub {}`). -/
def ExternSub.decide (Δ : TypeCtx) (a b : CExternType) (hΔ : Δ.Ok) (hr : Δ.recs = [])
    (ha : ExternTypeOk Δ a) (hb : ExternTypeOk Δ b) : Decidable (ExternSub Δ a b) :=
  decidable_of_iff _ (ExternSub.check_iff hΔ hr ha hb)

/-- The empty context is well formed. -/
theorem TypeCtx.ok_empty : TypeCtx.Ok {} := by
  intro d hd
  simp at hd

/-- Subtyping between valid types of the empty context is decidable. -/
def Sub.decideEmpty {k : TKind} (a b : Ty k) (ha : TyOk {} a) (hb : TyOk {} b) :
    Decidable (Sub {} a b) :=
  Sub.decide {} a b TypeCtx.ok_empty rfl ha hb

/-- `ExternSub {}` between valid extern types is decidable. -/
def ExternSub.decideEmpty (a b : CExternType) (ha : ExternTypeOk {} a)
    (hb : ExternTypeOk {} b) : Decidable (ExternSub {} a b) :=
  ExternSub.decide {} a b TypeCtx.ok_empty rfl ha hb

/-- A closed subtyping goal from a kernel evaluation of the checker. -/
theorem Sub.of_check {Δ : TypeCtx} {k : TKind} {a b : Ty k}
    (h : Sub.check Δ a b = true) : Sub Δ a b :=
  Sub.check_sound h

/-- A closed `ExternSub` goal from a kernel evaluation of the checker. -/
theorem ExternSub.of_check {Δ : TypeCtx} {a b : CExternType}
    (h : ExternSub.check Δ a b = true) : ExternSub Δ a b :=
  ExternSub.check_sound h

/-- Refuting a subtyping goal between valid types by evaluating the checker. -/
theorem Sub.not_of_check {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {k : TKind}
    {a b : Ty k} (ha : TyOk Δ a) (hb : TyOk Δ b) (h : Sub.check Δ a b = false) :
    ¬ Sub Δ a b := by
  rw [← Sub.check_iff hΔ hr ha hb, h]
  simp

/-! ### Instances

The procedures need validity, so the instances take the context and type
validity as `Fact`s (`Fact (ValidCtx {})` is global; type validity is supplied
locally with `have`). The kernel reduces them through the checker. -/

/-- A well-formed context without `RECS`: the contexts in which the checkers are
complete. Provided as a `Fact` for `{}`. -/
structure ValidCtx (Δ : TypeCtx) : Prop where
  ok : Δ.Ok
  recs : Δ.recs = []

instance Sub.instDecidable {Δ : TypeCtx} [hΔ : Fact (ValidCtx Δ)] {k : TKind} {a b : Ty k}
    [ha : Fact (TyOk Δ a)] [hb : Fact (TyOk Δ b)] : Decidable (Sub Δ a b) :=
  Sub.decide Δ a b hΔ.out.ok hΔ.out.recs ha.out hb.out

instance ExternSub.instDecidable {Δ : TypeCtx} [hΔ : Fact (ValidCtx Δ)] {a b : CExternType}
    [ha : Fact (ExternTypeOk Δ a)] [hb : Fact (ExternTypeOk Δ b)] :
    Decidable (ExternSub Δ a b) :=
  ExternSub.decide Δ a b hΔ.out.ok hΔ.out.recs ha.out hb.out

instance : Fact (ValidCtx {}) := ⟨⟨TypeCtx.ok_empty, rfl⟩⟩

end Silmaril.Wasm.Validation
