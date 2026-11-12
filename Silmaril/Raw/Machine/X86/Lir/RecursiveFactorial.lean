module

public import Silmaril.Machine.X86.Lir.Correct.Defs
public import Silmaril.Machine.CBackend.Lir.RecursiveFactorial.Defs

/-!
# Compiled recursive factorial

The existing Lir recursive factorial is proved for every word input, spilled,
then compiled to x86 bytes. The backend simulation supplies a machine execution
with the same factorial result and ABI state, or an explicit stack-limit stop.
The source has an unbounded call stack; the loaded machine has one MiB.
-/

@[expose] public section

namespace Silmaril.X86.Backend.RecursiveFactorial

open Silmaril.Machine
open Relation

/-- Seven physical registers, plus the spiller's two scratch registers. -/
def program : Lir.Prog (Fin 9) :=
  Lir.Alloc.spill (Lir.Alloc.firstK 7) Lir.Examples.recFactorial

def assignment : Assign (Fin 9) := Assign.fin 9 le_rfl

/-- Code at 0x401000, one MiB of stack and an empty linear-memory region. -/
def space : Space := ⟨0x401000, 0x7f000000, 0x7f100000, 0x10000000, 0⟩

/-- The compiler's exact output bytes and placement. -/
def image : Image :=
  ⟨encodeAt (layout assignment program space.codeBase) space.codeBase
    (progCode assignment program), layout assignment program space.codeBase⟩

theorem compiled : compile assignment program space.codeBase = .ok image := by
  have errors : progErrors assignment program = [] := by decide +kernel
  unfold compile
  rw [errors]
  rfl

theorem space_valid : space.Valid image.code.length := by
  constructor <;> decide +kernel

/-- For every input, the loaded recursive machine returns the factorial with
its ABI state restored, or reaches the stack guard's UD2. -/
theorem returns_or_overflow (n : Word) (saved : Reg → Word) (init : State) :
    let E : Env (Fin 9) := ⟨assignment, program, space, 0, space.stackHi - 8, saved⟩
    ∃ last, ReflTransGen (RStep 0) (E.load Lir.Examples.emptyMem 0 [n] init) last ∧
      ((∃ final, Ext.step 0 last = .returned final ∧
        final.core.read .rax = BitVec.ofNat 64 n.toNat.factorial ∧
        E.Final [BitVec.ofNat 64 n.toNat.factorial] Lir.Examples.emptyMem final) ∨
        E.Overflow last) := by
  intro E
  obtain ⟨start, starts, source⟩ :=
    Lir.Examples.recFactorial_spilled_returns 7 n Lir.Examples.emptyMem
  obtain ⟨_, _, returns, _, _⟩ := compile_correct assignment program space compiled space_valid
    0 (space.stackHi - 8) saved (by decide) (by decide) (by decide)
    (by decide +kernel) (by rfl : Lir.Examples.emptyMem.size = space.memSize) starts init
  obtain ⟨last, steps, result⟩ := returns _ _ source
  refine ⟨last, steps, ?_⟩
  rcases result with ⟨final, returned, frame⟩ | overflow
  · exact Or.inl ⟨final, returned, frame.vals 0 (by simp), frame⟩
  · exact Or.inr overflow

/-- The static conditions hold for a real loaded initial state for every input. -/
theorem entry_realizable (n : Word) (saved : Reg → Word) (init : State) :
    let E : Env (Fin 9) := ⟨assignment, program, space, 0, space.stackHi - 8, saved⟩
    E.Entry 0 [n] [] Lir.Examples.emptyMem
      (E.load Lir.Examples.emptyMem 0 [n] init) (space.stackHi - 8) := by
  intro E
  have code : E.code = image.code := rfl
  have ok : E.Ok := ⟨(compile_ok compiled).1, code ▸ space_valid,
    by change space.stackHi - 8 + 8 ≤ space.stackHi; decide,
    by change space.stackLo ≤ space.stackHi - 8; decide,
    by change (space.stackHi - 8) % 16 = 8; decide,
    by exact Or.inl (by change (0#64 : Word).toNat < space.codeBase; decide)⟩
  exact E.load_entry ok rfl 0 (by change 1 ≤ 6; decide) init

end Silmaril.X86.Backend.RecursiveFactorial
