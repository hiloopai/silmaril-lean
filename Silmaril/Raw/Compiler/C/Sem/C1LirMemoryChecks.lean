module

public import Silmaril.Compiler.C.Sem.C1LirMemory.Defs
/-! Realizable byte resources and counterexamples to recovering source access
metadata from LIR bytes. These guard the exact interpretation theorem's scope. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirMemoryChecks
open Silmaril.Cerberus.Assertion ConcreteResources
open C1LirMemory

theorem pair_related (v w : UInt8) : Rel (pairMemory v w) (embed (pairMemory v w)) :=
  embed_related _

theorem pair_loads (v w : UInt8) :
    (embed (pairMemory v w)).load .b1 .zero C1.base = some (word v) ∧
      (embed (pairMemory v w)).load .b1 .zero (C1.base + 1) = some (word w) :=
  ⟨((pair_related v w).load_owned (pair_left v w)).2,
    ((pair_related v w).load_owned (pair_right v w)).2⟩

theorem pair_resources (v w : UInt8) :
    C1LirMemory.Realizes (embed (pairMemory v w))
      [(C1.base, (v.toNat : Int)), (C1.base + 1, (w.toNat : Int))] :=
  (pair_related v w).realizes (pair_realizes v w)

def uninitialized : C1.Memory :=
  ⟨⟨#[7]⟩, ⟨#[0]⟩, C1.base, C1.base + 1⟩

def readonly : C1.Memory :=
  ⟨⟨#[7]⟩, ⟨#[1]⟩, C1.base + 1, C1.base + 1⟩

theorem uninitialized_related : Rel uninitialized (embed uninitialized) := embed_related _
theorem readonly_related : Rel readonly (embed readonly) := embed_related _

/-- Linear target bytes can load successfully even when the source is undefined. -/
example : (embed uninitialized).load .b1 .zero C1.base = some (word 7) := by decide
example : (C1.load uninitialized (.int 1 false) C1.base).toBool = false := by
  have zeroByte : (⟨#[0]⟩ : ByteArray)[0]! = 0 := rfl
  simp [C1.load, C1.width, C1.Memory.readBytes, C1.Memory.valid, uninitialized,
    C0.ub, C1.base, zeroByte,
    Bind.bind, Except.bind, Except.toBool]

theorem uninitialized_no_owned (value : UInt8) : ¬ OwnedByte uninitialized C1.base value := by
  intro owned
  exact owned.initialized rfl

/-- Target stores do not encode the source readonly boundary. -/
example : ((embed readonly).store .b1 C1.base (word 8)).isSome = true := by decide
example : (C1.store readonly (.int 1 false) C1.base 8).toBool = false := by
  simp [C1.store, C1.width, C1.Memory.writeBytes, C1.Memory.valid, C1.Memory.le,
    C1.wrap, C1.inRange, readonly, C0.ub, C1.base, Bind.bind, Except.bind, Except.toBool]
  split_ifs <;> rfl

theorem readonly_no_owned (value : UInt8) : ¬ OwnedByte readonly C1.base value := by
  intro owned
  have access : C1.base + 1 ≤ C1.base := owned.writable
  omega

/-- No permission hypothesis is silently recovered by `Rel.realizes_iff`. -/
theorem uninitialized_no_access : ¬ Access uninitialized [(C1.base, 7)] := by
  intro access
  obtain ⟨value, owned⟩ := access C1.base 7 (by simp)
  exact uninitialized_no_owned value owned

end Silmaril.Compile.C.Sem.C1LirMemoryChecks
