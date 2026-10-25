module

public import Silmaril.Wasm.Extensions.SharedMemory
public import Silmaril.Wasm.Binary.Core.Types

/-! # Shared-memory binary types

The threads proposal adds bit 1 to memory limits flags: `0x03` for shared
memory32 and `0x07` for shared memory64. A maximum is mandatory for this slice.
The grammar retains the flag in an extended AST and does not reinterpret these
bytes as ordinary Core encodings. This is binary syntax, not memory validation.

Source: WebAssembly threads proposal, `document/core/binary/types.rst`, memory
types, and `document/core/valid/types.rst`, mandatory shared-memory maximum.
https://github.com/WebAssembly/threads/tree/main/document/core
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.SharedMemory

open Core
abbrev MemoryType := Wasm.Extensions.SharedMemory.MemoryType

inductive MemType (F : Forms) : Bytes → MemoryType → Prop where
  | unshared {b : Bytes} {m : Wasm.MemoryType} (h : Core.MemType F b m) :
      MemType F b ⟨m, false⟩
  | shared32 {bn bm : Bytes} {n m : Fin (2 ^ 64)}
      (hn : Bound F bn n) (hm : Bound F bm m) :
      MemType F ([0x03] ++ bn ++ bm) ⟨⟨.i32, ⟨n, some m⟩⟩, true⟩
  | shared64 {bn bm : Bytes} {n m : Fin (2 ^ 64)} (g : F .limits64 = true)
      (hn : U64 bn n.val) (hm : U64 bm m.val) :
      MemType F ([0x07] ++ bn ++ bm) ⟨⟨.i64, ⟨n, some m⟩⟩, true⟩

theorem MemType.shared_has_max {F : Forms} {b : Bytes} {m : MemoryType}
    (h : MemType F b m) (hs : m.shared = true) : m.core.limits.max.isSome := by
  cases h <;> simp_all

end Silmaril.Wasm.Binary.Extensions.SharedMemory
