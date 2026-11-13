module

public import Silmaril.Machine.CBackend.RTL.ImplementsX86.Defs
public import Silmaril.Machine.CBackend.RTL.Examples.Defs
/-!
# The RTL factorial, lowered and compiled to x86-64

`RTL.Examples.factorial` carried end to end through the pipeline of
`Silmaril/Machine/RTL/ImplementsX86.lean`: lowered one Lir block per RTL node
(`toLir`), spilled onto the nine allocatable registers
(`Lir.Alloc.spill (firstK 7)`) and compiled by `X86.Backend.compile`. The
layout conditions are discharged by `decide`, as in
`Silmaril/X86/Lir/Examples.lean`, so the hypotheses of the composed theorems
are visibly satisfiable rather than assumed.

What is checked here:

* `factorialLir_runs` and `factorialX_runs` — the lowered and the spilled
  program still compute `5! = 120`, by kernel evaluation;
* `factorialX_errors`, `factorialX_compile`, `space_valid` — the program is
  accepted by the backend at a concrete memory layout, with 139 bytes of code;
* `factorial_admissible` — the call `factorial(n)` is `Admissible`, **including
  the safety conjunct**: the RTL run returns, so by `Behaves.unique` it does not
  get stuck;
* `factorial_first_step` — the loaded machine actually takes a retiring step.
  This is the clause that keeps the witness from being vacuous one level down:
  `Implements.Live` concludes "steps *or* is final", and a represented state
  whose own step were absent would satisfy nothing of interest. It is proved,
  not assumed, from `Env.start_match`, which produces a **nonempty** machine run
  from `Env.load`;
* `factorial_exists_beh` — `exists_beh_sysv64` instantiated with every
  hypothesis discharged: the represented machine state exists, has a behaviour,
  and each of its behaviours implements a behaviour of the RTL call;
* `factorial_returns_x86` — the concrete payoff: the loaded machine reaches a
  RET that pops the return address with `n! mod 2^64` in `rax`, or stops at the
  stack-limit check.

The stack-limit alternative is not eliminated, exactly as in
`Silmaril/X86/Lir/Examples.lean`: it is the one difference between the finite
machine stack and RTL's unbounded one, and under the `⟨.strict, .allowed⟩` mode
it is the resource outcome the instance permits.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.X86.Examples

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.Behaviour (Implements Outcome)
open Silmaril.X86 (MState Reg)
open Silmaril.X86.Backend (Space Env RStep Assign Image compile progErrors encodeAt layout
  progCode)
open Relation

/-! ## The lowered and compiled program -/

/-- The RTL factorial lowered to Lir: one block per node. -/
def factorialLir : Lir.Prog Nat := toLir Silmaril.Machine.RTL.Examples.factorial

theorem factorialLir_runs :
    (factorialLir.runMain 200 0 [5] (Lir.Memory.ofList 0 [])).returnedValues? = some [120] := by
  decide

/-- The lowered factorial spilled onto the nine allocatable x86-64 registers. -/
def factorialX : Lir.Prog (Fin 9) := lirOf (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial

theorem factorialX_runs :
    (factorialX.runMain 400 0 [5] (Lir.Memory.ofList 0 [])).returnedValues? = some [120] := by
  decide

/-- Seven virtual registers in physical registers, two scratch: nine in all,
which is what the x86-64 backend allocates. -/
theorem hk7 : 7 + 2 ≤ 9 := by decide

/-- The canonical assignment of the nine allocatable registers. -/
def assign9 : Assign (Fin 9) := Assign.fin (7 + 2) hk7

/-- Code at `0x401000`, a 1 MiB stack below `0x7f100000`, 4 KiB of linear
memory at `0x10000000`. -/
def space : Space := ⟨0x401000, 0x7f000000, 0x7f100000, 0x10000000, 0x1000⟩

/-- The entry stack pointer: the top of the stack, less the eight bytes holding
the return address. -/
def E0 : Nat := space.stackHi - 8

set_option maxRecDepth 8000 in
theorem factorialX_errors : progErrors assign9 factorialX = [] := by decide

set_option maxRecDepth 8000 in
theorem factorialX_code_length :
    (encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
      (progCode assign9 factorialX)).length = 139 := by
  decide

theorem factorialX_compile :
    ∃ img, compile assign9 factorialX space.codeBase = .ok img ∧ img.code.length = 139 :=
  ⟨_, rfl, factorialX_code_length⟩

theorem space_valid : space.Valid 139 := by constructor <;> decide

/-- `0x7f100000 - 8` is a System V entry stack pointer: congruent to 8 modulo
16, because the call that would have produced it pushed eight bytes. -/
theorem E0_entryAligned : Silmaril.X86.sysv64.EntryAligned E0 :=
  (Silmaril.X86.sysv64_entryAligned_iff E0).mpr (by decide)

/-! ## The call -/

/-- The linear memory of the call: 4 KiB of zeros, the size the layout
declares. -/
def factMem : Memory := Lir.Memory.ofList space.memSize []

theorem factMem_size : factMem.size = space.memSize := rfl

/-- The RTL state the call `factorial(n)` starts from. -/
def startState (n : Word) : State Nat := ⟨⟨0, 0⟩, Frame.empty.set 0 n, [], factMem⟩

theorem start_eq (n : Word) :
    Silmaril.Machine.RTL.Examples.factorial.start 0 [n] factMem = some (startState n) := rfl

/-- The call data of `factorial(n)`. -/
def call (n : Word) (init : Silmaril.X86.State) : CallData Nat :=
  ⟨0, [n], factMem, startState n, init⟩

/-- **The call is admissible**, safety conjunct included: the RTL run of
`factorial(n)` returns `n!`, so by `Behaves.unique` it does not get stuck. This
is the hypothesis most easily left unchecked, and it is the one that scopes the
whole instance. -/
theorem factorial_admissible (n : Word) (init : Silmaril.X86.State) :
    Admissible Silmaril.Machine.RTL.Examples.factorial space.memSize (call n init) := by
  refine ⟨start_eq n, factMem_size, fun hstuck => ?_⟩
  obtain ⟨s, hs, hb⟩ := Silmaril.Machine.RTL.Examples.factorial_returns n factMem
  rw [start_eq n] at hs
  cases hs
  exact absurd (Behaves.unique hstuck hb) (by intro e; cases e)

/-! ## The discharged hypotheses of the backend -/

section Discharged

variable {saved : Reg → Silmaril.X86.Word}

/-- The compiled image of the factorial, at `space`. -/
theorem hc : compile (Assign.fin (7 + 2) hk7) (lirOf (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial)
    space.codeBase = .ok ⟨encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
      (progCode assign9 factorialX), layout assign9 factorialX space.codeBase⟩ := rfl

theorem hS : space.Valid
    (⟨encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
      (progCode assign9 factorialX), layout assign9 factorialX space.codeBase⟩ :
      Image).code.length := by
  show space.Valid (encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
    (progCode assign9 factorialX)).length
  rw [factorialX_code_length]
  exact space_valid

theorem hhi : E0 + 8 ≤ space.stackHi := by decide

theorem hlo : space.stackLo ≤ E0 := by decide

/-- The return address `0` is below the code, hence outside it. -/
theorem exit_below : (0 : Silmaril.X86.Word).toNat < space.codeBase := by decide

theorem hexit : (0 : Silmaril.X86.Word).toNat < space.codeBase ∨
    space.codeBase + (⟨encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
      (progCode assign9 factorialX), layout assign9 factorialX space.codeBase⟩ :
      Image).code.length ≤ (0 : Silmaril.X86.Word).toNat := .inl exit_below

/-- The environment of the compiled factorial: return address `0`, entry stack
pointer `E0`, callee-saved values `saved`. -/
abbrev factEnv (saved : Reg → Silmaril.X86.Word) : Env (Fin (7 + 2)) :=
  env hk7 (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial space 0 E0 saved

/-- The environment satisfies the backend's layout conditions. -/
theorem factEnv_ok : (factEnv saved).Ok where
  errors := factorialX_errors
  valid := by
    show space.Valid (encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
      (progCode assign9 factorialX)).length
    rw [factorialX_code_length]; exact space_valid
  e0_hi := hhi
  e0_lo := hlo
  e0_align := E0_entryAligned
  exit_out := .inl exit_below

/-- The spilled program has a start state for `factorial(n)`. -/
theorem lir_start (n : Word) :
    ∃ s₀, (lirOf (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial).start 0 [n] factMem = some s₀ := by
  obtain ⟨t₀, ht₀, -⟩ :=
    Lir.Alloc.spill_start (Lir.Alloc.firstK_valid 7) (toLir_start (start_eq n))
  exact ⟨t₀, ht₀⟩

/-- **The loaded machine takes a first step**, and the step is proved rather
than assumed. `Env.start_match` runs the prologue of `factorial` from
`Env.load`, and a `TransGen` is a *nonempty* chain, so its head is a retiring
machine step. Without this the witness below could be satisfied by a machine
that is already stuck. -/
theorem factorial_first_step (n : Word) (init : Silmaril.X86.State) :
    ∃ u, RStep 0 (loaded hk7 (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial space 0 E0 saved
      (call n init)) u := by
  obtain ⟨s₀, hs₀⟩ := lir_start n
  obtain ⟨t₁, hstep, -⟩ := (factEnv saved).start_match factEnv_ok factMem_size hs₀ init
  obtain ⟨u, hu, -⟩ := TransGen.head'_iff.mp hstep
  exact ⟨u, hu⟩

/-! ## The instance, instantiated -/

/-- **`exists_beh_sysv64` for the compiled factorial, with every hypothesis
discharged.** The machine state representing the call exists, it *has* a
behaviour, and each of its behaviours implements a behaviour of the RTL call in
the mode `⟨.strict, .allowed⟩`. Together with `factorial_first_step` this is a
concrete inhabitant of the hypothesis set of `nonvacuous_sysv64`. -/
theorem factorial_exists_beh (n : Word) (init : Silmaril.X86.State) :
    ∃ t, Represents hk7 (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial space 0 E0 saved space.memSize
        (call n init) t ∧
      (∃ o, (tgtSem (factEnv saved)).Beh t o) ∧
      ∀ o, (tgtSem (factEnv saved)).Beh t o →
        ∃ o', (sem Silmaril.Machine.RTL.Examples.factorial).Beh (entryState (call n init)) o' ∧
          Outcome.Rel ⟨.strict, .allowed⟩
            (obs hk7 (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial space 0 E0 saved (call n init) t)
            o o' :=
  exists_beh_sysv64 (Lir.Alloc.firstK_valid 7) hc hS hhi hlo E0_entryAligned hexit (factorial_admissible n init)

/-- **The compiled RTL factorial returns `n!` in `rax`.** The loaded machine
reaches a RET to `exit` whose state has `n! mod 2^64` in the first System V
result register, with the callee-saved registers restored and the stack pointer
popped by `sysv64.linkSize`, or it stops at the stack-limit check. -/
theorem factorial_returns_x86 (n : Word) (init : Silmaril.X86.State) :
    ∃ t', ReflTransGen (RStep 0)
        (loaded hk7 (Lir.Alloc.firstK 7) Silmaril.Machine.RTL.Examples.factorial space 0 E0 saved (call n init)) t' ∧
      ((∃ fin, Silmaril.X86.Ext.step 0 t' = .returned fin ∧
          fin.core.read .rax = BitVec.ofNat 64 n.toNat.factorial ∧
          (factEnv saved).Final [BitVec.ofNat 64 n.toNat.factorial] factMem fin) ∨
        (factEnv saved).Overflow t') := by
  obtain ⟨hr, -, -⟩ :=
    compiled_behaviours (Lir.Alloc.firstK_valid 7) hc hS hhi hlo E0_entryAligned hexit (factorial_admissible n init)
  obtain ⟨s, hs, hb⟩ := Silmaril.Machine.RTL.Examples.factorial_returns n factMem
  rw [start_eq n] at hs
  cases hs
  obtain ⟨t', ht, r⟩ := hr _ _ hb
  refine ⟨t', ht, ?_⟩
  rcases r with ⟨fin, hstep, hfinal⟩ | hov
  · exact .inl ⟨fin, hstep, hfinal.vals 0 (by simp), hfinal⟩
  · exact .inr hov

end Discharged

end Silmaril.Machine.RTL.X86.Examples
