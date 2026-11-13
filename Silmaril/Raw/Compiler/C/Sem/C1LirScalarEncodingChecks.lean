module
public import Silmaril.Compiler.C.Sem.C1LirScalarEncoding.Defs
public import Silmaril.Compiler.C.Sem.C1LirScalarMemoryChecks.Defs
@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirScalarEncoding.Checks
open Silmaril.Machine C1LirMemory C1LirScalarStore C1LirScalarMemory.Checks

/-- Arbitrary old memory and every 64-bit word admit actual stores, related
updated memories, and an unchanged ninth byte on both sides. -/
theorem all_words (old : Fin 9 → UInt8) (word : Lir.Word) :
    ∃ source target,
      C1.store (memory old) (.int 8 false) C1.base (word.toNat : Int) = .ok source ∧
      (embed (memory old)).store .b8 C1.base word = some target ∧
      Rel source target ∧
      target.bytes (C1.base + 8) = (old ⟨8, by decide⟩).toBitVec ∧
      source.bytes[8]! = old ⟨8, by decide⟩ ∧
      source.init[8]! = (memory old).init[8]! := by
  have stores := store_owned (embed_related (memory old)) (scalar_owned old) word
  have sourceFrame := store_source_frame (memory old) C1.base 8 word
    le_rfl (Or.inr le_rfl)
  have targetFrame := store_target_frame (embed (memory old)) C1.base (C1.base + 8) word
    (Or.inr le_rfl)
  refine ⟨written (memory old) C1.base (C1.Memory.le 8 (word.toNat : Int)),
    ⟨(embed (memory old)).size, Lir.writeLE (embed (memory old)).bytes C1.base 8 word⟩,
    stores.1, stores.2.1, stores.2.2, ?_, ?_, sourceFrame.2⟩
  · exact targetFrame.trans ((embed_related (memory old)).byte (cell old ⟨8, by decide⟩))
  · have oldValue : (memory old).bytes[8]! = old ⟨8, by decide⟩ := by
      simpa only [Nat.add_sub_cancel_left] using (cell old ⟨8, by decide⟩).value
    exact sourceFrame.1.trans oldValue

/-- Every old nine-byte memory and every replacement word establish initialized
scalar ownership and successful actual readback of that full word on both sides. -/
theorem all_words_readback (old : Fin 9 → UInt8) (word : Lir.Word) :
    ∃ source target,
      C1.store (memory old) (.int 8 false) C1.base (word.toNat : Int) = .ok source ∧
      (embed (memory old)).store .b8 C1.base word = some target ∧
      Rel source target ∧
      C1LirScalarMemory.OwnedBytes source C1.base (fun i => encoded word i.val) ∧
      C1.load source (.int 8 false) C1.base = .ok (word.toNat : Int) ∧
      target.load .b8 .zero C1.base = some word := by
  have stores := store_owned (embed_related (memory old)) (scalar_owned old) word
  have reads := store_readback (embed_related (memory old)) (scalar_owned old) word
  exact ⟨_, _, stores.1, stores.2.1, stores.2.2,
    store_owned_bytes (scalar_owned old) word, reads.1, reads.2⟩

end Silmaril.Compile.C.Sem.C1LirScalarEncoding.Checks
