module

public import Silmaril.Compiler.C.Sem.TargetsCoreC5.Defs
@[expose] public section

/-!
# Non-vacuous C5/Core realisation

The witness is a minimal defined main. Kernel-checked evaluation uses abstract
HashMap equations, including a Boolean form of the insertion-size equation;
it never unfolds the platform-dependent hash-table implementation, as in
`C2CoreProofs`. Heap coverage (`malloc`, `calloc`, `realloc`, `free`) is tested
separately in `examples/csem/core/c5`.
-/

namespace Silmaril.Compile.C.Sem.ElabC5
open Silmaril.Cerberus Silmaril.Cerberus.Ail
/-- A minimal defined main with a checked Core elaboration. -/
private def witnessProgram : TypedProgram :=
  let main : Sym := ⟨⟨[]⟩, 1, .id "main"⟩
  (some main, {
    declarations := [], objectDefinitions := [],
    functionDefinitions := [(main,
      ⟨.unknown, 0, ⟨[]⟩, [], .mk .unknown ⟨false, none⟩ ⟨[]⟩ .returnVoid⟩)],
    staticAssertions := [], tagDefinitions := [], externIdmap := [],
    typedefAttributes := [], loopAttributes := [], cnFunctions := [],
    cnLemmata := [], cnPredicates := [], cnDatatypes := [],
    cnDeclSpecs := [], cnIdents := [] })

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'
  Std.HashMap.size_emptyWithCapacity
  Std.HashMap.contains_emptyWithCapacity Std.HashMap.contains_insert
  Std.HashMap.getElem?_emptyWithCapacity
  Std.HashMap.toList_emptyWithCapacity
  Std.HashSet.contains_emptyWithCapacity Std.HashSet.contains_insert
private theorem size_insert_bool {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v).size = if m.contains k then m.size else m.size + 1 := by
  simpa only [Std.HashMap.mem_iff_contains] using (Std.HashMap.size_insert (m := m) (k := k) (v := v))
attribute [local cbv_eval] size_insert_bool
private theorem witness_accepted : (elaborate witnessProgram).isSome = true := by
  cbv
/-- The structural elaborator accepts at least one program, proved by the kernel. -/
theorem elaborate_nonempty : ∃ (p : TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elaborate p = some q := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp witness_accepted
  exact ⟨witnessProgram, q, hq⟩

end Silmaril.Compile.C.Sem.ElabC5

namespace Silmaril.Compile.Targets.Proofs

/-- Non-vacuous, exact C5 realisation through worker-written Core elaboration. -/
theorem c5_core_realises : Targets.c5_core_realises :=
  ⟨C.Sem.ElabC5.elaborate_nonempty, fun _ _ h => C.Sem.ElabC5.elaborate_sound h⟩

end Silmaril.Compile.Targets.Proofs
