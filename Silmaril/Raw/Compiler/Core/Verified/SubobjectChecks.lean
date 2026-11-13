module

public import Silmaril.Compiler.Core.Verified.SubobjectPointer.Defs
public import Silmaril.Compiler.Core.Verified.AggregateUninit.Defs
/-! # Two adjacent ints within one allocation

These witnesses exercise the difference from whole-object scalar slots: the
second int is an interior address, both ints have the same provenance id, and
killing that id invalidates both. Concrete positive and lifted negative action
runs retain the neighboring value. One-past accesses are rejected, not treated
as a fabricated UB escape.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.SubobjectChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open IntSubobject (Live Slot)
open Locals (stored)

/-- An eight-byte array/struct allocation, rather than two four-byte allocations. -/
def memory : Mem.Concrete.State :=
  {nextId := 1, lastAddress := 4096,
    allocations := (∅ : Map Int Mem.Concrete.Allocation).insert 0 {base := 4096, size := 8}}

theorem first_live : Live memory 0 4096 := by
  refine ⟨by simp [memory], ⟨{base := 4096, size := 8}, ?_, by decide, by decide, rfl, rfl⟩⟩
  simp [memory]

theorem second_live : Live memory 0 4100 := by
  refine ⟨by simp [memory], ⟨{base := 4096, size := 8}, ?_, by decide, by decide, rfl, rfl⟩⟩
  simp [memory]

/-- Neither int is a whole-object scalar slot; the interior address cannot be its base. -/
theorem neither_whole : ¬ Mem.Concrete.LiveInt memory 0 4096 ∧
    ¬ Mem.Concrete.LiveInt memory 0 4100 := by
  constructor <;> intro h <;> obtain ⟨a, look, base, size, _⟩ := h.found <;>
    simp only [memory, Map.lookup_insert, Option.some.injEq] at look <;>
    subst a <;> norm_num at size

/-- Byte-range framing retains both values despite identical allocation ids. -/
theorem two_values :
    let m := stored (stored memory 0 4096 17) 0 4100 (-23)
    Slot m 0 4096 17 ∧ Slot m 0 4100 (-23) :=
  ⟨(IntSubobject.stored_slot first_live 17).stored _ _ _ (by unfold Slots.Apart; decide),
    IntSubobject.stored_slot (second_live.stored _ _ _) (-23)⟩

/-- A real typed load reads each interior value, with the correct signed representation. -/
theorem load_two (tags : Mem.Concrete.Tags) (ann : List Annot) :
    let m := stored (stored memory 0 4096 17) 0 4100 (-23)
    Mem.Concrete.loadTyped tags m (Mem.Concrete.intType ann) (.allocated 0 4096) =
      .ok (.integer (.signed .int) 17, {m with lastUsed := some 0}) ∧
    Mem.Concrete.loadTyped tags m (Mem.Concrete.intType ann) (.allocated 0 4100) =
      .ok (.integer (.signed .int) (-23), {m with lastUsed := some 0}) :=
  ⟨IntSubobject.load tags ann two_values.1.live two_values.1.plain
      (by unfold Mem.Concrete.IntRange; decide) two_values.1.bytes,
    IntSubobject.load tags ann two_values.2.live two_values.2.plain
      (by unfold Mem.Concrete.IntRange; decide) two_values.2.bytes⟩

/-- One-past is not an int subobject; the current canonical semantics reports unsupported. -/
theorem one_past (tags : Mem.Concrete.Tags) (ann : List Annot) :
    ¬ Live memory 0 4104 ∧
    Mem.Concrete.accessTyped tags memory (Mem.Concrete.intType ann) (.allocated 0 4104) =
      .error (.unsupported "out of bounds access UB mapping") := by
  constructor
  · intro h
    obtain ⟨a, look, lo, hi, _⟩ := h.found
    simp only [memory, Map.lookup_insert, Option.some.injEq] at look
    subst a
    norm_num at hi
  · simp [Mem.Concrete.accessTyped, Mem.Concrete.layout_intType, memory]
    rfl

/-- Killing the enclosing object invalidates both elements. -/
theorem killed_both : ¬ Live (Locals.killed memory 0) 0 4096 ∧
    ¬ Live (Locals.killed memory 0) 0 4100 := by
  constructor <;> intro h <;> have := h.alive <;> simp [Locals.killed] at this

/-- A negative store to element zero with a runtime destination binding. -/
def write (x : Sym) : EE :=
  .mk [] (.action (.mk .neg (.mk .unknown ()
    (.store false (Locals.intVal [] []) (.mk [] () (.sym x))
      (.mk [] () (.val (.loaded (.specified (.integer 99))))) .na))))

def assign (x : Sym) : EE := .mk [] (.bound (write x))

/-- A complete lifted negative store writes element zero and frames element one. -/
theorem assign_reaches (file : Program) (labels : Labels) (env : Env) (x : Sym)
    (k : List Frame) :
    let m := stored memory 0 4100 (-23)
    let m' := stored {m with nextExcluded := m.nextExcluded + 1} 0 4096 99
    PureEval.Reaches file labels
      ⟨.effectExpr (assign x)
        (env.insert x (.object (.pointer (.allocated 0 4096)))), k, m⟩
      ⟨.value .unit, k, m'⟩ ∧ Slot m' 0 4096 99 ∧ Slot m' 0 4100 (-23) := by
  let m := stored memory 0 4100 (-23)
  have live : Live m 0 4096 := first_live.stored _ _ _
  have live' : Live {m with nextExcluded := m.nextExcluded + 1} 0 4096 := live.mono rfl rfl
  refine ⟨?_, IntSubobject.stored_slot live' 99, ?_⟩
  · exact SubobjectTask.bound_store [] .unknown () _ _ _ _ k m [] live
      (by unfold Mem.Concrete.IntRange; decide)
      (fun _ => .cons .val (.cons (.sym (by simp)) (.cons .val .nil)))
  · exact ((IntSubobject.stored_slot second_live (-23)).nextExcluded
      (m.nextExcluded + 1)).stored _ _ _ (by unfold Slots.Apart; decide)

/-- Runtime-index pointer computation preserves provenance and scales by sizeof(int). -/
theorem index_local (file : Program) (labels : Labels) (env : Env) (x n : Sym)
    (different : x.key ≠ n.key) (k : List Frame) (index : Int) :
    let e := (env.insert x (.object (.pointer (.allocated 0 4096)))).insert n (.object (.integer index))
    Interleave.LocalReaches file labels false
      ⟨.pureExpr (.mk [] () (.arrayShift (.mk [] () (.sym x)) (Mem.Concrete.intType [])
        (.mk [] () (.sym n)))) e, k, memory⟩
      ⟨.value (.object (.pointer (.allocated 0 (4096 + 4 * index)))), k, memory⟩ := by
  apply SubobjectPointer.array_local [] [] _ _ _ _ _ false 0 4096 index
  exact .cons (.sym (by simp [Map.lookup_insert_of_key_ne (x := n) (x' := x) _ _ different]))
    (.cons (.sym (by simp)) .nil)


/-- A concrete placement has unspecified source bytes and arbitrary target bytes. -/
def target : Silmaril.Machine.Lir.Memory := ⟨64, fun _ => 170⟩

def object : MemRel.Obj := ⟨0, 4096, 16, 8⟩

theorem related : MemRel.Rel memory target [object] := by
  refine ⟨?_, .cons (by simp) .nil, ?_, ?_⟩
  · intro o ho
    obtain rfl := List.mem_singleton.mp ho
    refine ⟨by simp [memory, object], ⟨{base := 4096, size := 8}, ?_, rfl, rfl, rfl, rfl⟩,
      by decide, ?_, ?_⟩
    · simp [object, memory]
    · intro i hi v hv
      simp [Mem.Concrete.readByte, memory, Map.lookup] at hv
    · intro i hi
      simp [memory, Map.lookup]
  · intro o ho
    obtain rfl := List.mem_singleton.mp ho
    decide
  · intro o ho
    obtain rfl := List.mem_singleton.mp ho
    decide

/-- The same two integer stores execute in Lir linear memory and both loads agree.
The first initialized slot survives the second store in the very same object. -/
theorem lir_two_values (tags : Mem.Concrete.Tags) :
    ∃ lm₁ lm₂,
      target.store .b4 16 (BitVec.ofInt 64 17) = some lm₁ ∧
      lm₁.store .b4 20 (BitVec.ofInt 64 (-23)) = some lm₂ ∧
      lm₂.load .b4 .sign 16 = some (BitVec.ofInt 64 17) ∧
      lm₂.load .b4 .sign 20 = some (BitVec.ofInt 64 (-23)) ∧
      MemRel.Rel (stored (stored memory 0 4096 17) 0 4100 (-23)) lm₂ [object] := by
  have hl : Mem.Concrete.registeredIntegerLayout tags (.signed .int) = some (4, true) := rfl
  have ho : object ∈ [object] := by simp
  have h₁ := MemRel.store tags [] hl (Or.inr (Or.inr (Or.inl rfl))) related ho
    (a := 4096) (n := 17) (by decide) (by decide) (by decide)
  have h₂ := MemRel.store tags [] hl (Or.inr (Or.inr (Or.inl rfl))) h₁.2.2 ho
    (a := 4100) (n := -23) (by decide) (by decide) (by decide)
  have decode₁ : Mem.Concrete.decodeInteger
      (Mem.Concrete.fetchBytes 4 4096 (stored (stored memory 0 4096 17) 0 4100 (-23)).bytes) =
      some 17 := by
    rw [two_values.1.bytes, Mem.Concrete.decode_encode]
    rfl
  have decode₂ : Mem.Concrete.decodeInteger
      (Mem.Concrete.fetchBytes 4 4100 (stored (stored memory 0 4096 17) 0 4100 (-23)).bytes) =
      some 4294967273 := by
    rw [two_values.2.bytes, Mem.Concrete.decode_encode]
    rfl
  have read₁ := MemRel.load tags [] hl (Or.inr (Or.inr (Or.inl rfl))) h₂.2.2 ho
    (a := 4096) (by decide) (by decide) decode₁
  have read₂ := MemRel.load tags [] hl (Or.inr (Or.inr (Or.inl rfl))) h₂.2.2 ho
    (a := 4100) (by decide) (by decide) decode₂
  exact ⟨_, _, h₁.2.1, h₂.2.1, read₁.2, read₂.2, h₂.2.2⟩

/-- Explicit unspecified initialization of the eight-byte aggregate preserves placement. -/
theorem unspecified_keeps_target :
    MemRel.Rel (AggregateUninit.stored memory object) target [object] :=
  AggregateUninit.rel related (by simp)

end Silmaril.Compile.Core.Verified.SubobjectChecks
