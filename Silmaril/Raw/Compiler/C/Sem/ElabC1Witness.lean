module

public import Silmaril.Compiler.C.Sem.ElabC1.Defs
@[expose] public section

/-! # A program the C1 Core elaboration accepts

`ElabC1.elaborate` declines unless C1's check, C1's run, the structural translation and the
exact Core run all succeed and agree, so its acceptance of a concrete program is a computation.
`cbv` performs it in the kernel. C1 keeps its tables in `Std.HashMap`/`Std.HashSet`, whose
bucket arithmetic is platform dependent (`USize`), so the maps stay abstract: their sizes are
rewritten by the Boolean `size_insert` laws below and their lookups by Std's `cbv_eval` laws.
-/

namespace Silmaril.Compile.C.Sem.ElabC1

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- `HashMap.size_insert` with a Boolean test, so `cbv` decides it through `contains`. -/
theorem hashMap_size_insert {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k : α} {v : β} :
    (m.insert k v).size = bif m.contains k then m.size else m.size + 1 := by
  cases h : m.contains k <;> simp [Std.HashMap.size_insert, Std.HashMap.mem_iff_contains, h]

/-- `HashSet.size_insert` with a Boolean test, so `cbv` decides it through `contains`. -/
theorem hashSet_size_insert {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashSet α} {k : α} :
    (m.insert k).size = bif m.contains k then m.size else m.size + 1 := by
  cases h : m.contains k <;> simp [Std.HashSet.size_insert, Std.HashSet.mem_iff_contains, h]

attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'
attribute [local cbv_opaque] Std.HashMap.size Std.HashSet.size Std.HashMap.toList
  Std.HashSet.toList Std.HashMap.contains Std.HashSet.contains
attribute [local cbv_eval] Std.HashMap.size_emptyWithCapacity hashMap_size_insert
  Std.HashSet.size_emptyWithCapacity hashSet_size_insert
  Std.HashMap.toList_emptyWithCapacity Std.HashSet.toList_emptyWithCapacity

/-- `void main(void) {}`: the smallest defined C1 program. -/
def witnessProgram : TypedProgram :=
  let main : Sym := ⟨⟨[]⟩, 1, .id "main"⟩
  (some main, {
    declarations := [], objectDefinitions := [],
    functionDefinitions := [(main,
      ⟨.unknown, 0, ⟨[]⟩, [], .mk .unknown ⟨false, none⟩ ⟨[]⟩ .returnVoid⟩)],
    staticAssertions := [], tagDefinitions := [], externIdmap := [],
    typedefAttributes := [], loopAttributes := [], cnFunctions := [],
    cnLemmata := [], cnPredicates := [], cnDatatypes := [],
    cnDeclSpecs := [], cnIdents := [] })

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem witness_accepted : (elaborate witnessProgram).isSome = true := by
  cbv

theorem exists_accepted : ∃ p q, elaborate p = some q :=
  ⟨witnessProgram, Option.isSome_iff_exists.mp witness_accepted⟩

end Silmaril.Compile.C.Sem.ElabC1
