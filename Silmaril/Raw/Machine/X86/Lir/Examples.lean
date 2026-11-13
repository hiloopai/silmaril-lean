module

public import Silmaril.Machine.X86.Lir.Correct.Defs
public import Silmaril.Machine.CBackend.Lir.Examples.Defs

/-!
# Examples of the Lir-to-x86-64 backend

`factorialX` is the factorial loop of `Lir.Examples`, spilled onto the nine
allocatable registers (`Lir.Alloc.firstK 7`). Its compiled bytes are checked
by `decide` (`factorialX_code`), and `factorialX_returns` instantiates
`compile_correct` with a concrete memory layout: for every 64-bit `n`, the
loaded machine reaches a RET that pops the return address with `n! mod 2^64`
in `rax`, or stops at the stack-limit check. The layout conditions are
discharged by `decide`, so the hypotheses of `compile_correct` are satisfiable.
-/

@[expose] public section

namespace Silmaril.X86.Backend.Examples

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

/-- The factorial loop over the nine allocatable registers. -/
def factorialX : Lir.Prog (Fin 9) := Lir.Alloc.spill (Lir.Alloc.firstK 7) Lir.Examples.factorial

def assign9 : Assign (Fin 9) := Assign.fin 9 le_rfl

/-- Code at `0x401000`, a 1 MiB stack below `0x7f100000`, 4 KiB of linear
memory at `0x10000000`. -/
def space : Space := ⟨0x401000, 0x7f000000, 0x7f100000, 0x10000000, 0x1000⟩

theorem factorialX_errors : progErrors assign9 factorialX = [] := by decide

/-- The exact bytes of the compiled factorial. -/
theorem factorialX_code :
    encodeAt (layout assign9 factorialX space.codeBase) space.codeBase (progCode assign9 factorialX) =
      [73, 137, 227, 77, 41, 243, 73, 129, 251, 128, 0, 0, 0, 15, 131, 2, 0, 0, 0, 15, 11, 85, 83,
        65, 84, 65, 85, 72, 129, 236, 88, 0, 0, 0, 72, 137, 124, 36, 8, 72, 139, 116, 36, 8, 233,
        0, 0, 0, 0, 72, 191, 1, 0, 0, 0, 0, 0, 0, 0, 73, 184, 1, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0,
        0, 0, 72, 133, 246, 15, 133, 5, 0, 0, 0, 233, 24, 0, 0, 0, 73, 137, 251, 76, 15, 175, 222,
        76, 137, 223, 73, 137, 243, 77, 41, 195, 76, 137, 222, 233, 218, 255, 255, 255, 72, 137,
        248, 72, 129, 196, 88, 0, 0, 0, 65, 93, 65, 92, 91, 93, 195] := by
  decide

theorem factorialX_compile : ∃ img, compile assign9 factorialX space.codeBase = .ok img ∧
    img.code.length = 129 := by
  refine ⟨_, rfl, ?_⟩
  show (encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
    (progCode assign9 factorialX)).length = 129
  rw [factorialX_code]; rfl

theorem space_valid : space.Valid 129 := by
  constructor <;> decide

/-- For every input, the loaded machine holding the compiled factorial reaches a
RET to `exit` with the factorial in `rax`, or stops at the stack-limit check. -/
theorem factorialX_returns (n : Word) {lm : Lir.Memory} (hsize : lm.size = space.memSize)
    (saved : Reg → Word) (init : State) :
    let E : Env (Fin 9) := ⟨assign9, factorialX, space, 0, space.stackHi - 8, saved⟩
    ∃ t', ReflTransGen (RStep 0) (E.load lm 0 [n] init) t' ∧
      ((∃ final, Ext.step 0 t' = .returned final ∧
          final.core.read .rax = BitVec.ofNat 64 n.toNat.factorial ∧ E.Final
            [BitVec.ofNat 64 n.toNat.factorial] lm final) ∨ E.Overflow t') := by
  intro E
  obtain ⟨img, hc, hlen⟩ := factorialX_compile
  obtain ⟨s₀, hs, hb⟩ := Lir.Examples.factorial_spilled_returns 7 n lm
  obtain ⟨-, -, hret, -, -⟩ := compile_correct assign9 factorialX space hc (by rw [hlen]; exact space_valid)
    0 (space.stackHi - 8) saved (by decide) (by decide) (by decide) (by rw [hlen]; decide) hsize hs init
  obtain ⟨t', h, r⟩ := hret _ _ hb
  refine ⟨t', h, ?_⟩
  rcases r with ⟨final, hstep, hfin⟩ | hov
  · exact .inl ⟨final, hstep, hfin.vals 0 (by simp), hfin⟩
  · exact .inr hov

/-! ## Rejected programs -/

/-- A call with seven arguments: more than the six System V argument registers. -/
def sevenArgs : Lir.Prog (Fin 9) :=
  ⟨[⟨[], 0, [⟨[.call 0 (List.replicate 7 (.reg 0)) []], .ret []⟩]⟩]⟩

theorem sevenArgs_rejected : progErrors assign9 sevenArgs = [.tooManyArgs 0 7] := by decide

/-- Three returned values: more than the two System V result registers. -/
def threeResults : Lir.Prog (Fin 9) :=
  ⟨[⟨[.reg 0], 0, [⟨[], .ret [.reg 0, .reg 0, .reg 0]⟩]⟩]⟩

theorem threeResults_rejected :
    progErrors assign9 threeResults = [.tooManyReturnValues 0 3] := by decide

/-- High multiplications are compiled (by the 32-bit-half sequence). -/
def highMul : Lir.Prog (Fin 9) :=
  ⟨[⟨[.reg 0, .reg 1], 0, [⟨[.op (.binary .mulhu 2 0 1), .op (.binary .mulhs 3 0 1)],
    .ret [.reg 2, .reg 3]⟩]⟩]⟩

theorem highMul_accepted : progErrors assign9 highMul = [] := by decide

/-- A branch to a missing block. -/
def badJump : Lir.Prog (Fin 9) := ⟨[⟨[], 0, [⟨[], .jump 5⟩]⟩]⟩

theorem badJump_rejected : progErrors assign9 badJump = [.badLabel 0 5] := by decide

theorem clz_uses : usesBitCount (P := Fin 9) ⟨[⟨[.reg 0], 0, [⟨[.op (.unary .clz 1 0)],
    .ret [.reg 1]⟩]⟩]⟩ = true := by decide

end Silmaril.X86.Backend.Examples
