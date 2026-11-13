module

public import Silmaril.Compiler.Native.Correctness.MainLoader.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralLoader.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.MainLoader
open Silmaril Silmaril.X86
open Silmaril.Process (Memory)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The existing code region permits every byte of any fitting image. -/
theorem code_permitted (code : List Byte) (bound : code.length ≤ 0x1000)
    (access : Process.Access) (allowed : access = .read ∨ access = .execute) :
    (image code).initial.memory.Permitted access 0x1000 code.length := by
  apply (Memory.checkSpan_iff _ _ _ _).mpr
  refine ⟨by decide +kernel, by change 0x1000 + code.length ≤ 2^64; omega, ?_⟩
  intro index below
  have inside : 0x1000 + index < 0x1000 + 0x1000 := by omega
  rcases allowed with rfl | rfl <;>
    simp [Memory.permits, image, LiteralLoader.image, Literal42.loadImage,
      Process.Region.Contains, Process.Permissions.allows, inside]

theorem code_read (code : List Byte) (bound : code.length ≤ 0x1000) :
    (image code).initial.memory.readBytes 0x1000 code.length = some code := by
  apply Memory.readWith_eq
  · exact code_permitted code bound .read (.inl rfl)
  · intro index below
    change (Memory.install (Memory.install (Memory.install ∅ 0x1000 code)
      0x2ff8 (Machine.LittleEndian.encodeWords [0x4000]))
      0x5000 ((Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).map
        fun byte => BitVec.ofNat 8 byte.toNat)).get? (0x1000 + index) = some code[index]
    rw [Memory.install_outside _ _ _ _ (.inl (by omega))]
    rw [Memory.install_outside _ _ _ _ (.inl (by omega))]
    exact Memory.install_get _ _ code index below

theorem code_fetch (code : List Byte) (bound : code.length ≤ 0x1000) :
    (image code).initial.memory.fetchBytes 0x1000 code.length = some code := by
  apply Memory.readWith_eq
  · exact code_permitted code bound .execute (.inr rfl)
  · intro index below
    exact Memory.readWith_get (code_read code bound) index below

/-- The native closed-main loading contract follows from actual installed
bytes and independent code-size bounds; no execution is an input. -/
theorem loaded (code : List Byte) (positive : 0 < code.length) (bound : code.length ≤ 0x1000) :
    Loaded ["a.out"] (image code) := by
  refine ⟨rfl, by change (0x1000 : Nat) ≤ 0x1000; decide +kernel, ?_, ?_, code_read code bound,
    code_permitted code bound .execute (.inr rfl), rfl, rfl,
    LiteralLoader.arguments_read code, LiteralLoader.return_read code,
    by change (0x2ff8 + 8) % 16 = 0; decide +kernel, rfl, rfl, rfl, rfl⟩
  · change 0x1000 < 0x1000 + code.length
    omega
  · right
    change 0x1000 + code.length ≤ 0x4000
    omega

end Silmaril.Compiler.Native.Correctness.MainLoader
