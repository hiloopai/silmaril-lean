module

public import Silmaril.Wasm.Logic.V1.Examples.Defs

/-!
# Straight-line Wasm Logic examples

The proof sketch of §3.3 of Watt, Maksimović, Krishnaswami and Gardner, and a
few variants. These exercise the parts of the logic that have nothing to do with
control flow: the structured stack assertion, `[extension]`, `[frame]` and
`[consequence]`, and the interaction between the stack and local variables.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1.Examples

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Logic.V1

variable {Γ : Ctx}

/-! ### Glue not in `Derived.lean`

`[consequence]` between two `(S | H)` assertions, and the independence of an
`emp ∧ φ` assertion from the variables `φ` does not mention. -/

/-- Entailment of `(S' | H')` by `(S | H)`: the stack parts need only agree on
the stores the heap part admits, which is how a pure precondition is used to
replace a term by an equal one. -/
private theorem entails_mk {S S' : List (Term Value)} {H H' : HAssert}
    (h : ∀ ρ hp, H ρ hp → S.map (fun τ => τ ρ) = S'.map (fun τ => τ ρ) ∧ H' ρ hp) :
    Assert.Entails (Assert.mk S H) (Assert.mk S' H') := by
  rintro ρ vs hp ⟨rfl, hH⟩
  exact h ρ hp hH

/-- `emp ∧ φ` is insensitive to `X` as soon as `φ` is. -/
private theorem indep_empAnd {X : Set Var} {φ : Sto → Prop}
    (h : ∀ ρ ρ' : Sto, (∀ x, x ∉ X → ρ x = ρ' x) → (φ ρ ↔ φ ρ')) :
    HAssert.Indep X (HAssert.empAnd φ) := by
  intro ρ ρ' hp agree
  simp only [HAssert.empAnd, HAssert.and, HAssert.pure, HAssert.emp]
  exact and_congr_right fun _ => h ρ ρ' agree

/-- `(i32.const 2) (i32.const 3) (i32.add)`: addition from an empty stack,
Figure 2 of the paper. -/
def addConsts : Silmaril.Wasm.V1.Expr :=
  [.intConst .i32 2, .intConst .i32 3, .intBinOp .i32 .add]

theorem addConsts_spec :
    Triple Γ (Assert.stack []) addConsts (Assert.stack [Term.i32 fun _ => 5]) := by
  obtain ⟨F, A, L, R⟩ := Γ
  have h₁ : Triple (⟨F, A, L, R⟩ : Ctx) (Assert.mk [] HAssert.emp) [Silmaril.Wasm.V1.Instr.intConst .i32 2]
      (Assert.mk [Term.i32 fun _ => 2] HAssert.emp) :=
    Triple.constOn [] HAssert.emp (Value.int .i32 2)
  have h₂ : Triple (⟨F, A, L, R⟩ : Ctx) (Assert.mk [Term.i32 fun _ => 2] HAssert.emp)
      [Silmaril.Wasm.V1.Instr.intConst .i32 3]
      (Assert.mk [Term.i32 fun _ => 2, Term.i32 fun _ => 3] HAssert.emp) :=
    Triple.constOn [Term.i32 fun _ => 2] HAssert.emp (Value.int .i32 3)
  have h₃ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.i32 fun _ => 2, Term.i32 fun _ => 3] HAssert.emp)
      [Silmaril.Wasm.V1.Instr.intBinOp .i32 .add] (Assert.mk [Term.i32 fun _ => 5] HAssert.emp) :=
    Triple.intBinOpOn [] HAssert.emp .i32 .add (fun _ => 2) (fun _ => 3) (fun _ => 5)
      (fun _ => rfl)
  exact Triple.cons h₁ (Triple.cons h₂ h₃)

/-- The proof sketch of §3.3: `(get_local 1) (i32.const 3) (i32.add)` run from a
state in which the first local holds `2`. -/
def addLocal : Silmaril.Wasm.V1.Expr :=
  [.localGet ⟨1⟩, .intConst .i32 3, .intBinOp .i32 .add]

theorem addLocal_spec :
    Triple Γ (Assert.stackIf [] fun ρ => ρ (.loc 1) = Value.int .i32 2) addLocal
      (Assert.stackIf [Term.i32 fun _ => 5] fun ρ => ρ (.loc 1) = Value.int .i32 2) := by
  obtain ⟨F, A, L, R⟩ := Γ
  have h₁ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2))
      [Silmaril.Wasm.V1.Instr.localGet ⟨1⟩]
      (Assert.mk [Term.local_ 1]
        (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2)) :=
    Triple.localGetOn [] _ ⟨1⟩
  have h₂ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.local_ 1] (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2))
      [Silmaril.Wasm.V1.Instr.intConst .i32 3]
      (Assert.mk [Term.local_ 1, Term.i32 fun _ => 3]
        (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2)) :=
    Triple.constOn [Term.local_ 1] _ (Value.int .i32 3)
  -- `l₁` is immediately replaced by `2`, which is what the pure part knows.
  have h₃ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.local_ 1, Term.i32 fun _ => 3]
        (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2))
      [Silmaril.Wasm.V1.Instr.intBinOp .i32 .add]
      (Assert.mk [Term.i32 fun _ => 5]
        (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2)) := by
    refine Triple.conseqPre
      (Triple.intBinOpOn [] _ .i32 .add (fun _ => 2) (fun _ => 3) (fun _ => 5)
        (fun _ => rfl)) (entails_mk ?_)
    rintro ρ hp ⟨hemp, hφ⟩
    simp only [HAssert.pure] at hφ
    exact ⟨by simp [Term.local_, Term.i32, Term.int, IntType.width, hφ], hemp, hφ⟩
  exact Triple.cons h₁ (Triple.cons h₂ h₃)

/-- The same program on a larger stack and heap, by `[extension]` and `[frame]`:
what the paper's Figure 12 does around every instruction. -/
theorem addLocal_spec_on (S : List (Term Value)) (H : HAssert)
    (indepS : ∀ τ ∈ S, Term.Indep (Expr.modified addLocal) τ)
    (indepH : HAssert.Indep (Expr.modified addLocal) H) :
    Triple Γ (Assert.mk S (HAssert.and H (HAssert.pure fun ρ => ρ (.loc 1) = Value.int .i32 2)))
      addLocal
      (Assert.mk (S ++ [Term.i32 fun _ => 5])
        (HAssert.and H (HAssert.pure fun ρ => ρ (.loc 1) = Value.int .i32 2))) := by
  obtain ⟨F, A, L, R⟩ := Γ
  have base : Triple (⟨F, A, [], none⟩ : Ctx)
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2)) addLocal
      (Assert.mk [Term.i32 fun _ => 5]
        (HAssert.empAnd fun ρ => ρ (.loc 1) = Value.int .i32 2)) :=
    addLocal_spec
  have h := Triple.liftOn (L := L) (R := R) S H base (subset_refl _) indepS indepH
  simpa using h

/-- `(get_local i) (set_local j)` on a purely pure state: the value read is the
`u` the precondition pins down, and `[set_local]`'s logical variable is that
same `u`. The postcondition `ψ` must not mention `lⱼ` except through `u`. -/
private theorem getSet {F : List FuncDef} {A : FuncSpecs} {L : List Assert} {R : Option Assert}
    (i j : LocalIdx) (m n : Nat) (hi : i.toNat = m) (hj : j.toNat = n) (u : Value)
    (φ ψ : Sto → Prop) (hget : ∀ ρ, φ ρ → ρ (.loc m) = u)
    (hindep : ∀ ρ ρ' : Sto, (∀ x, x ∉ ({Var.loc n} : Set Var) → ρ x = ρ' x) → (φ ρ ↔ φ ρ'))
    (hpost : ∀ ρ, φ ρ → ρ (.loc n) = u → ψ ρ) :
    Triple (⟨F, A, L, R⟩ : Ctx) (Assert.mk [] (HAssert.empAnd φ))
      [Silmaril.Wasm.V1.Instr.localGet i, Silmaril.Wasm.V1.Instr.localSet j] (Assert.mk [] (HAssert.empAnd ψ)) := by
  subst hi; subst hj
  have g : Triple (⟨F, A, L, R⟩ : Ctx) (Assert.mk [] (HAssert.empAnd φ)) [Silmaril.Wasm.V1.Instr.localGet i]
      (Assert.mk [Term.const u] (HAssert.empAnd φ)) := by
    refine Triple.conseqPost (Triple.localGetOn [] _ i) (entails_mk ?_)
    rintro ρ hp ⟨hemp, hφ⟩
    simp only [HAssert.pure] at hφ
    exact ⟨by simp [Term.local_, Term.const, hget ρ hφ], hemp, hφ⟩
  have s : Triple (⟨F, A, L, R⟩ : Ctx) (Assert.mk [Term.const u] (HAssert.empAnd φ))
      [Silmaril.Wasm.V1.Instr.localSet j] (Assert.mk [] (HAssert.empAnd ψ)) := by
    refine Triple.conseqPost
      (Triple.localSetOn [] (HAssert.empAnd φ) j u (by simp) (indep_empAnd hindep))
      (entails_mk ?_)
    rintro ρ hp ⟨⟨hemp, hφ⟩, hset⟩
    simp only [HAssert.pure] at hφ hset
    exact ⟨rfl, hemp, hpost ρ hφ hset⟩
  exact Triple.cons g s

/-- Swapping two locals through a third: the classic three-assignment swap,
which exercises `[set_local]`'s use of a logical variable for the stored value. -/
def swapLocals01 : Silmaril.Wasm.V1.Expr :=
  [.localGet ⟨0⟩, .localSet ⟨2⟩,
   .localGet ⟨1⟩, .localSet ⟨0⟩,
   .localGet ⟨2⟩, .localSet ⟨1⟩]

theorem swapLocals01_spec (a b : Value) :
    Triple Γ (Assert.stackIf [] fun ρ => ρ (.loc 0) = a ∧ ρ (.loc 1) = b) swapLocals01
      (Assert.stackIf [] fun ρ => ρ (.loc 0) = b ∧ ρ (.loc 1) = a) := by
  obtain ⟨F, A, L, R⟩ := Γ
  have s₁ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 0) = a ∧ ρ (.loc 1) = b))
      [Silmaril.Wasm.V1.Instr.localGet ⟨0⟩, Silmaril.Wasm.V1.Instr.localSet ⟨2⟩]
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 1) = b ∧ ρ (.loc 2) = a)) := by
    refine getSet ⟨0⟩ ⟨2⟩ 0 2 rfl rfl a _ _ (fun ρ hφ => hφ.1) ?_ ?_
    · intro ρ ρ' agree
      rw [agree (Var.loc 0) (by simp), agree (Var.loc 1) (by simp)]
    · exact fun ρ hφ hset => ⟨hφ.2, hset⟩
  have s₂ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 1) = b ∧ ρ (.loc 2) = a))
      [Silmaril.Wasm.V1.Instr.localGet ⟨1⟩, Silmaril.Wasm.V1.Instr.localSet ⟨0⟩]
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 2) = a ∧ ρ (.loc 0) = b)) := by
    refine getSet ⟨1⟩ ⟨0⟩ 1 0 rfl rfl b _ _ (fun ρ hφ => hφ.1) ?_ ?_
    · intro ρ ρ' agree
      rw [agree (Var.loc 1) (by simp), agree (Var.loc 2) (by simp)]
    · exact fun ρ hφ hset => ⟨hφ.2, hset⟩
  have s₃ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 2) = a ∧ ρ (.loc 0) = b))
      [Silmaril.Wasm.V1.Instr.localGet ⟨2⟩, Silmaril.Wasm.V1.Instr.localSet ⟨1⟩]
      (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc 0) = b ∧ ρ (.loc 1) = a)) := by
    refine getSet ⟨2⟩ ⟨1⟩ 2 1 rfl rfl a _ _ (fun ρ hφ => hφ.1) ?_ ?_
    · intro ρ ρ' agree
      rw [agree (Var.loc 2) (by simp), agree (Var.loc 0) (by simp)]
    · exact fun ρ hφ hset => ⟨hφ.2, hset⟩
  exact Triple.seq3 s₁ s₂ s₃

/-- Reading a memory cell, adding one, and writing it back. -/
def bumpCell : Silmaril.Wasm.V1.Expr :=
  [.localGet ⟨0⟩, .localGet ⟨0⟩, .intLoad .i32 none ⟨2, 0⟩,
   .intConst .i32 1, .intBinOp .i32 .add, .intStore .i32 none ⟨2, 0⟩]

theorem bumpCell_spec (a : Term Nat) (v : Term (BitVec 32))
    (addr : ∀ ρ, ρ (.loc 0) = Value.int .i32 (BitVec.ofNat 32 (a ρ)))
    (inBounds : ∀ ρ, a ρ < 2 ^ 32) :
    Triple Γ (Assert.mk [] (cell32 a v)) bumpCell
      (Assert.mk [] (cell32 a fun ρ => v ρ + 1)) := by
  obtain ⟨F, A, L, R⟩ := Γ
  have harg : memAddr ⟨2, 0⟩ (fun ρ => BitVec.ofNat 32 (a ρ)) = a := by
    funext ρ
    simpa [memAddr] using inBounds ρ
  have hloc : Term.local_ 0 = Term.i32 fun ρ => BitVec.ofNat 32 (a ρ) := by
    funext ρ
    simpa [Term.local_, Term.i32, Term.int] using addr ρ
  have h₁ : Triple (⟨F, A, L, R⟩ : Ctx) (Assert.mk [] (cell32 a v)) [Silmaril.Wasm.V1.Instr.localGet ⟨0⟩]
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ)] (cell32 a v)) := by
    rw [← hloc]; exact Triple.localGetOn [] _ ⟨0⟩
  have h₂ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ)] (cell32 a v)) [Silmaril.Wasm.V1.Instr.localGet ⟨0⟩]
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ),
        Term.i32 fun ρ => BitVec.ofNat 32 (a ρ)] (cell32 a v)) := by
    rw [← hloc]; exact Triple.localGetOn [Term.local_ 0] _ ⟨0⟩
  have h₃ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ),
        Term.i32 fun ρ => BitVec.ofNat 32 (a ρ)] (cell32 a v))
      [Silmaril.Wasm.V1.Instr.intLoad .i32 none ⟨2, 0⟩]
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 v] (cell32 a v)) := by
    simpa only [harg, HAssert.star_emp, List.cons_append, List.nil_append, Term.i32] using
      Triple.intLoadOn (F := F) (A := A) (L := L) (R := R)
      [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ)] HAssert.emp .i32 ⟨2, 0⟩
      (fun ρ => BitVec.ofNat 32 (a ρ)) v
  have h₄ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 v] (cell32 a v))
      [Silmaril.Wasm.V1.Instr.intConst .i32 1]
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 v,
        Term.i32 fun _ => 1] (cell32 a v)) :=
    Triple.constOn [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 v] _
      (Value.int .i32 1)
  have h₅ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 v,
        Term.i32 fun _ => 1] (cell32 a v))
      [Silmaril.Wasm.V1.Instr.intBinOp .i32 .add]
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 fun ρ => v ρ + 1]
        (cell32 a v)) :=
    Triple.intBinOpOn [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ)] _ .i32 .add v (fun _ => 1)
      (fun ρ => v ρ + (1 : BitVec 32)) (fun _ => rfl)
  have h₆ : Triple (⟨F, A, L, R⟩ : Ctx)
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 fun ρ => v ρ + 1]
        (cell32 a v))
      [Silmaril.Wasm.V1.Instr.intStore .i32 none ⟨2, 0⟩]
      (Assert.mk [] (cell32 a fun ρ => v ρ + 1)) := by
    have h : Triple (⟨F, A, L, R⟩ : Ctx)
        (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (a ρ), Term.i32 fun ρ => v ρ + 1]
          (cell32Any a))
        [Silmaril.Wasm.V1.Instr.intStore .i32 none ⟨2, 0⟩] (Assert.mk [] (cell32 a fun ρ => v ρ + 1)) := by
      simpa only [harg, HAssert.star_emp, List.nil_append, Term.i32] using
        Triple.intStoreOn (F := F) (A := A) (L := L) (R := R) [] HAssert.emp .i32 ⟨2, 0⟩
          (fun ρ => BitVec.ofNat 32 (a ρ)) (fun ρ => v ρ + (1 : BitVec 32))
    refine Triple.conseqPre h (entails_mk ?_)
    intro ρ hp hH
    exact ⟨rfl, v ρ, hH⟩
  exact Triple.cons h₁ (Triple.cons h₂ (Triple.cons h₃ (Triple.cons h₄ (Triple.cons h₅ h₆))))

end Silmaril.Wasm.Logic.V1.Examples
