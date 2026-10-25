module

public import Silmaril.Wasm.Validation.Instructions

@[expose] public section

/-! # Widening `REFS` to all function indices

`ref.func x` requires both `x ∈ C.REFS` and `C.FUNCS[x]` to exist, so code typed in
`C` types in `C` with `REFS` replaced by all function indices `[0, |C.FUNCS|)`.
This is the `REFS` of `Moduleinst_ok`, and is used by instantiation soundness.
-/

namespace Silmaril.Wasm.Validation

/-- `C` with `REFS` all function indices. -/
abbrev Context.rangeRefs (C : Context) : Context := { C with refs := List.range C.funcs.length }

theorem Context.withLocals_rangeRefs (C : Context) (xs : List Nat) (lts : List LocalType) :
    (C.withLocals xs lts).rangeRefs = C.rangeRefs.withLocals xs lts := by
  induction xs generalizing C lts with
  | nil => cases lts <;> rfl
  | cons x xs ih =>
    cases lts with
    | nil => rfl
    | cons lt lts => exact ih (C.setLocal x lt) lts

theorem Context.initLocals_rangeRefs (C : Context) (xs : List Nat) :
    (C.initLocals xs).rangeRefs = C.rangeRefs.initLocals xs :=
  Context.withLocals_rangeRefs _ _ _

section families
variable {C : Context} {i : Instr} {it : InstrType}

theorem ParametricInstrOk.rangeRefs (h : ParametricInstrOk C i it) :
    ParametricInstrOk C.rangeRefs i it := by
  cases h <;> (constructor <;> assumption)

theorem NumericInstrOk.rangeRefs (h : NumericInstrOk C i it) :
    NumericInstrOk C.rangeRefs i it := by
  cases h <;> constructor
  assumption

theorem VectorInstrOk.rangeRefs (h : VectorInstrOk C i it) :
    VectorInstrOk C.rangeRefs i it := by
  cases h <;> constructor <;> assumption

theorem VariableInstrOk.rangeRefs (h : VariableInstrOk C i it) :
    VariableInstrOk C.rangeRefs i it := by
  cases h <;> constructor <;> assumption

theorem MemoryInstrOk.rangeRefs (h : MemoryInstrOk C i it) :
    MemoryInstrOk C.rangeRefs i it := by
  cases h <;> constructor <;> assumption

theorem TableInstrOk.rangeRefs (h : TableInstrOk C i it) :
    TableInstrOk C.rangeRefs i it := by
  cases h <;> constructor <;> assumption

theorem RefInstrOk.rangeRefs (h : RefInstrOk C i it) :
    RefInstrOk C.rangeRefs i it := by
  cases h
  case refFunc x d hf _ =>
    exact .refFunc hf (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hf).1)
  all_goals constructor <;> assumption

theorem BlockTypeOk.rangeRefs {bt : BlockType} {t₁ t₂ : List CValType}
    (h : BlockTypeOk C bt t₁ t₂) : BlockTypeOk C.rangeRefs bt t₁ t₂ := by
  cases h <;> constructor <;> assumption

theorem CatchOk.rangeRefs {c : Catch} (h : CatchOk C c) : CatchOk C.rangeRefs c := by
  cases h <;> constructor <;> assumption

end families

/-- Code typed in `C` types with `REFS` all function indices. -/
theorem InstrsOk.rangeRefs {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : InstrsOk C.rangeRefs is it := by
  refine InstrsOk.rec (motive_1 := fun C i it _ => InstrOk C.rangeRefs i it)
    (motive_2 := fun C is it _ => InstrsOk C.rangeRefs is it) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals intros
  all_goals first
    | exact InstrOk.parametric (ParametricInstrOk.rangeRefs ‹_›)
    | exact InstrOk.numeric (NumericInstrOk.rangeRefs ‹_›)
    | exact InstrOk.vector (VectorInstrOk.rangeRefs ‹_›)
    | exact InstrOk.variable (VariableInstrOk.rangeRefs ‹_›)
    | exact InstrOk.memory (MemoryInstrOk.rangeRefs ‹_›)
    | exact InstrOk.table (TableInstrOk.rangeRefs ‹_›)
    | exact InstrOk.reference (RefInstrOk.rangeRefs ‹_›)
    | exact InstrOk.block (BlockTypeOk.rangeRefs ‹_›) ‹_›
    | exact InstrOk.loop (BlockTypeOk.rangeRefs ‹_›) ‹_›
    | exact InstrOk.if_ (BlockTypeOk.rangeRefs ‹_›) ‹_› ‹_›
    | exact InstrOk.tryTable (BlockTypeOk.rangeRefs ‹_›) ‹_›
        (fun c hc => CatchOk.rangeRefs (‹∀ c ∈ _, CatchOk _ c› c hc))
    | (apply InstrOk.br <;> assumption)
    | (apply InstrOk.brIf <;> assumption)
    | (apply InstrOk.brTable <;> assumption)
    | (apply InstrOk.brOnNull <;> assumption)
    | (apply InstrOk.brOnNonNull <;> assumption)
    | (apply InstrOk.brOnCast <;> assumption)
    | (apply InstrOk.brOnCastFail <;> assumption)
    | (apply InstrOk.call <;> assumption)
    | (apply InstrOk.callRef <;> assumption)
    | (apply InstrOk.callIndirect <;> assumption)
    | (apply InstrOk.return_ <;> assumption)
    | (apply InstrOk.returnCall <;> assumption)
    | (apply InstrOk.returnCallRef <;> assumption)
    | (apply InstrOk.returnCallIndirect <;> assumption)
    | (apply InstrOk.throw <;> assumption)
    | (apply InstrOk.throwRef <;> assumption)
    | exact InstrsOk.nil
    | exact InstrsOk.instr ‹_›
    | (refine InstrsOk.seq ‹_› ‹_› ?_; rwa [← Context.initLocals_rangeRefs])
    | (refine InstrsOk.cons ‹_› ‹_› ?_; rwa [← Context.initLocals_rangeRefs])
    | exact InstrsOk.sub ‹_› ‹_› ‹_›
    | exact InstrsOk.frame ‹_› ‹_›

end Silmaril.Wasm.Validation
