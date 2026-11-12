module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XFlat
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XOk
public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Thms
public import Silmaril.Wasm.SpecTec.Institution.FwdB30.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# The redexes that use primitives are short flat redexes

* `FlatA k t code`: the image of `code` is `FlatK k t`, and `code` is not a cast redex.
* `flatA_list`: a code list literal whose last instruction encodes as `t` and whose other
  instructions are values is `FlatA`.
* `pureHeadX_cases`: every `FwdX30.PureHeadX` redex is a `FwdB30.PureG` redex, or `FlatA k t`
  at a shape `(k, t)` of `pureCombos`.
* `readB_flat`: every `ReadB` redex is `FlatA k t` at a shape of `readCombos`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (PureHeadX noCastAdmin noCastAdmin_toAdmin
  not_castRedex_of_all)
open Silmaril.Wasm.SpecTec.Institution.FwdB30 (PureG)

variable {H : Type}

/-- The image of `code` is `FlatK k t`, and `code` is not a cast redex. -/
def FlatA (k : Nat) (t : MixopS) (code : List Admin) : Prop :=
  FlatK k t (adminsToV code) ∧ ¬ Round6.Target.CastRedex code

/-- An instruction of a literal is a value. -/
syntax "val_tac" : tactic
macro_rules
  | `(tactic| val_tac) => `(tactic| first
    | exact ⟨_, rfl⟩
    | exact ⟨.num ⟨.int _, _⟩, rfl⟩
    | exact ⟨.num ⟨.float _, _⟩, rfl⟩
    | exact ⟨.vec _, rfl⟩
    | exact ⟨.ref _, rfl⟩)

/-- Membership of a shape in a literal list. -/
syntax "mem_tac" : tactic
macro_rules
  | `(tactic| mem_tac) =>
    `(tactic| (repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) <;> done)

/-- The head of a value is a value constructor. -/
theorem adminHead_toAdmin (v : Val) : Typing.adminHead v.toAdmin ∈ valTags := by
  cases v with
  | num n =>
    obtain ⟨ty, b⟩ := n
    cases ty <;> mem_tac
  | vec b => mem_tac
  | ref r => cases r <;> mem_tac

/-- **Values followed by one instruction are `FlatA`.** -/
theorem flatA_split (vs : List Admin) {a : Admin} (hnc : noCastAdmin a = true)
    (hv : ∀ b ∈ vs, ∃ v : Val, v.toAdmin = b) :
    FlatA vs.length (Typing.adminHead a) (vs ++ [a]) := by
  refine ⟨⟨adminsToV vs, adminToV a, adminsToV_append _ _, adminsToV_length vs, ?_, ?_⟩,
    not_castRedex_of_all fun b hb => ?_⟩
  · intro x hx op w' hxe
    rw [adminsToV_eq_map, List.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hv b hb
    rw [Typing.adminToV_case hxe]
    exact adminHead_toAdmin v
  · intro x hx op w' hxe
    rw [List.mem_singleton.1 hx] at hxe
    exact List.mem_singleton.2 (Typing.adminToV_case hxe)
  · rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨v, rfl⟩ := hv b hb
      exact noCastAdmin_toAdmin v
    · rw [List.mem_singleton.1 hb]
      exact hnc

/-- `IsVal b`: `b` is the instruction of a value. -/
def IsVal (b : Admin) : Prop := ∃ v : Val, v.toAdmin = b

/-- `FlatA` at 0 values and an instruction. -/
theorem flatA0 {a : Admin} (hnc : noCastAdmin a = true) :
    FlatA 0 (Typing.adminHead a) [a] :=
  flatA_split [] hnc (by simp)

set_option linter.unusedTactic false in
/-- `FlatA` at 1 value and an instruction. -/
theorem flatA1 {b₁ a : Admin} (hnc : noCastAdmin a = true)
    (h₁ : IsVal b₁) :
    FlatA 1 (Typing.adminHead a) [b₁, a] :=
  flatA_split [b₁] hnc fun b hb => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- `FlatA` at 2 values and an instruction. -/
theorem flatA2 {b₁ b₂ a : Admin} (hnc : noCastAdmin a = true)
    (h₁ : IsVal b₁) (h₂ : IsVal b₂) :
    FlatA 2 (Typing.adminHead a) [b₁, b₂, a] :=
  flatA_split [b₁, b₂] hnc fun b hb => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- `FlatA` at 3 values and an instruction. -/
theorem flatA3 {b₁ b₂ b₃ a : Admin} (hnc : noCastAdmin a = true)
    (h₁ : IsVal b₁) (h₂ : IsVal b₂) (h₃ : IsVal b₃) :
    FlatA 3 (Typing.adminHead a) [b₁, b₂, b₃, a] :=
  flatA_split [b₁, b₂, b₃] hnc fun b hb => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- `FlatA` at 4 values and an instruction. -/
theorem flatA4 {b₁ b₂ b₃ b₄ a : Admin} (hnc : noCastAdmin a = true)
    (h₁ : IsVal b₁) (h₂ : IsVal b₂) (h₃ : IsVal b₃) (h₄ : IsVal b₄) :
    FlatA 4 (Typing.adminHead a) [b₁, b₂, b₃, b₄, a] :=
  flatA_split [b₁, b₂, b₃, b₄] hnc fun b hb => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- `FlatA` at 5 values and an instruction. -/
theorem flatA5 {b₁ b₂ b₃ b₄ b₅ a : Admin} (hnc : noCastAdmin a = true)
    (h₁ : IsVal b₁) (h₂ : IsVal b₂) (h₃ : IsVal b₃) (h₄ : IsVal b₄) (h₅ : IsVal b₅) :
    FlatA 5 (Typing.adminHead a) [b₁, b₂, b₃, b₄, b₅, a] :=
  flatA_split [b₁, b₂, b₃, b₄, b₅] hnc fun b hb => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- A redex literal is `FlatA` at one of the listed shapes. -/
syntax "flat_tac" : tactic
macro_rules
  | `(tactic| flat_tac) => `(tactic| (
    first
      | refine ⟨_, _, ?_, flatA0 rfl⟩
      | refine ⟨_, _, ?_, flatA1 rfl ?_⟩
      | refine ⟨_, _, ?_, flatA2 rfl ?_ ?_⟩
      | refine ⟨_, _, ?_, flatA3 rfl ?_ ?_ ?_⟩
      | refine ⟨_, _, ?_, flatA4 rfl ?_ ?_ ?_ ?_⟩
      | refine ⟨_, _, ?_, flatA5 rfl ?_ ?_ ?_ ?_ ?_⟩
    all_goals first | mem_tac | val_tac))

/-! ## The families -/

/-- The numeric family. -/
theorem numeric_flat {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    ∃ k t, (k, t) ∈ pureCombos ∧ FlatA k t is := by
  cases h <;> flat_tac

/-- The vector family. -/
theorem vector_flat {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    ∃ k t, (k, t) ∈ pureCombos ∧ FlatA k t is := by
  cases h <;> flat_tac

/-- **Every `PureHeadX` redex is a `PureG` redex or a checked flat redex.** -/
theorem pureHeadX_cases {P : Profile} {is is' : List Admin} (h : PureHeadX P is is') :
    PureG is is' ∨ ∃ k t, (k, t) ∈ pureCombos ∧ FlatA k t is := by
  cases h with
  | numeric h => exact .inr (numeric_flat h)
  | vector h _ => exact .inr (vector_flat h)
  | refI31 i => exact .inr (by flat_tac)
  | i31GetNum sx i => exact .inr (by flat_tac)
  | isNullTrue => exact .inl .isNullTrue
  | isNullFalse h => exact .inl (.isNullFalse h)
  | asNonNullNull => exact .inl .asNonNullNull
  | asNonNullAddr h => exact .inl (.asNonNullAddr h)
  | eqNull => exact .inl .eqNull
  | eqTrue h => exact .inl (.eqTrue h)
  | eqFalse h => exact .inl (.eqFalse h)
  | i31GetNull sx => exact .inl (.i31GetNull sx)
  | externConvertNull => exact .inl .externConvertNull
  | externConvertAddr h => exact .inl (.externConvertAddr h)
  | anyConvertNull => exact .inl .anyConvertNull
  | anyConvertAddr r => exact .inl (.anyConvertAddr r)
  | arrayNew v n => exact .inl (.arrayNew v n)
  | brOnNullAddr hv => exact .inl (.brOnNullAddr hv)
  | brOnNonNullAddr hv => exact .inl (.brOnNonNullAddr hv)
  | localTee => exact .inl .localTee
  | handlerVals => exact .inl .handlerVals

/-- A code whose last instruction fails `p` does not end in a `p`-instruction. -/
theorem not_lastIs_of {p : Instr → Bool} {is : List Admin} {j : Instr}
    (h : is.getLast? = some (.plain j)) (hj : p j = false) : ¬ FwdX30.LastIs p is := by
  rintro ⟨i, hi, hp⟩
  rw [h] at hi
  rw [Admin.plain.inj (Option.some.inj hi).symm, hj] at hp
  exact Bool.false_ne_true hp

/-- The table reads. -/
theorem table_flat {P : Profile} {c c' : Config H} (h : TableStep P c c')
    (hl : FwdX30.LastIs FwdX30.tableReadInstr c.code) :
    ∃ k t, (k, t) ∈ readCombos ∧ FlatA k t c.code := by
  cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | flat_tac

/-- The memory reads. -/
theorem mem_flat {P : Profile} {c c' : Config H} (h : MemoryStep P c c')
    (hl : FwdX30.LastIs FwdX30.memReadInstr c.code) :
    ∃ k t, (k, t) ∈ readCombos ∧ FlatA k t c.code := by
  cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | flat_tac

/-- The aggregate reads. -/
theorem agg_flat {c c' : Config H} (h : AggregateStep c c')
    (hl : FwdX30.LastIs FwdX30.aggReadInstr c.code) :
    ∃ k t, (k, t) ∈ readCombos ∧ FlatA k t c.code := by
  cases h <;> first
    | exact absurd hl (not_lastIs_of rfl rfl)
    | exact absurd hl (not_lastIs_of List.getLast?_concat rfl)
    | flat_tac

/-- **Every `ReadB` redex is a checked flat redex.** -/
theorem readB_flat {P : Profile} {c : Config H} {is' : List Admin} (h : ReadB P c is') :
    ∃ k t, (k, t) ∈ readCombos ∧ FlatA k t c.code := by
  cases h with
  | refFunc _ => flat_tac
  | table h => exact table_flat h.1 h.2
  | memory h => exact mem_flat h.1 h.2
  | aggregate h => exact agg_flat h.1 h.2

/-- `ReadB` redexes are `ReadHeadX` redexes. -/
theorem ReadB.toX {P : Profile} {c : Config H} {is' : List Admin} (h : ReadB P c is') :
    FwdX30.ReadHeadX P c is' := by
  cases h with
  | refFunc h => exact .refFunc h
  | table h => exact .table h
  | memory h => exact .memory h
  | aggregate h => exact .aggregate h

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
