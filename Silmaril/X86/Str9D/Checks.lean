module

public import Silmaril.X86.Str9D.Defs

/-!
# Checker for the direction-flag hardware vectors

`checkLine` runs one vector of `scripts/x86-dir/gen_dir_vectors.py`: it builds the state the
native harness started from (the instructions at `0x1000` in an executable region, a 64-byte
read-write buffer at `0x10000`, the fifteen registers other than `rsp`, the six arithmetic
flags and DF), runs **`Str9D.step` until RIP leaves the code** (a `rep` form takes one
step per element), and compares RIP, every register but `rsp`, every
flag the model defines, DF and the buffer with what the processor produced. The processor
never faulted, so a run that stops early fails the check.

`checkExecStr` also runs a string form through `execStr` alone, in the direction of the input
DF, so `execStr false` (the forward reading, which `step` does not use) is compared with the
processor as well. A vector may be a short instruction sequence (`__memmove_erms`'s backward
tail `lea; lea; std; rep movsb; cld`); the run stops when RIP leaves it, after at most
`rcx + 8` steps.
-/

@[expose] public section

namespace Silmaril.X86.Str9D.Checks

open Silmaril.X86 (Byte Word Reg State Flags MState)
open Silmaril.Process (Memory)

/-- The code address. -/
def ripBase : Nat := 0x1000

/-- The buffer address. -/
def memBase : Nat := 0x10000

/-- The buffer length. -/
def memLen : Nat := 64

/-- A hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

/-- A hexadecimal number. -/
def hexNat? (s : String) : Option Nat :=
  if s.isEmpty then none else s.toList.foldlM (fun acc c => (hexDigit? c).map (16 * acc + ·)) 0

/-- Pairs of hexadecimal digits as bytes. -/
def hexBytes? : List Char → Option (List Byte)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigit? a
    let y ← hexDigit? b
    let t ← hexBytes? rest
    pure (BitVec.ofNat 8 (16 * x + y) :: t)
  | _ => none

/-- The registers in hardware order. -/
def regs : List Reg := [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The six arithmetic flags of an RFLAGS image. -/
def flagsOf (fl : Nat) : Flags :=
  let b := fun i => some (fl >>> i % 2 == 1)
  ⟨b 0, b 2, b 4, b 6, b 7, b 11⟩

/-- DF of an RFLAGS image. -/
def dfOf (fl : Nat) : Bool := fl >>> 10 % 2 == 1

/-- Every flag the model defines has the hardware value. -/
def flagsMatch (f : Flags) (fl : Nat) : Bool :=
  let ok := fun (o : Option Bool) (i : Nat) => o.all (· == (fl >>> i % 2 == 1))
  ok f.carry 0 && ok f.parity 2 && ok f.adjust 4 && ok f.zero 6 && ok f.sign 7 && ok f.overflow 11

/-- The memory: the code (read, execute) and the buffer (read, write). -/
def memoryOf (code : List Byte) (buf : Nat) : Memory :=
  let data := (List.range memLen).map fun i => BitVec.ofNat 8 (buf >>> (8 * i))
  ⟨[⟨ripBase, code.length, ⟨true, false, true⟩⟩, ⟨memBase, memLen, ⟨true, true, false⟩⟩],
    Memory.install (Memory.install ∅ ripBase code) memBase data⟩

/-- The input core. -/
def coreOf (rv : List Nat) (fl : Nat) : State :=
  { regs := fun r => BitVec.ofNat 64 (rv.getD (regs.idxOf r) 0)
    rip := BitVec.ofNat 64 ripBase, flags := flagsOf fl }

/-- The input state. -/
def stateOf (code : List Byte) (rv : List Nat) (fl buf : Nat) : DState :=
  ⟨⟨⟨⟨⟨coreOf rv fl, memoryOf code buf⟩, fun _ => 0⟩, fun _ => 0, true⟩, fun _ => 0⟩, dfOf fl⟩

/-- A vector line: the code bytes and the 36 numbers that follow. -/
def lineFields (line : String) : Option (List Byte × List Nat) :=
  match (line.splitOn " ").filter (!·.isEmpty) with
  | [] => none
  | enc :: rest => do
    let code ← hexBytes? enc.toList
    let nums ← rest.mapM hexNat?
    if nums.length = 36 then some (code, nums) else none

/-- The lines of a vector text. -/
def vectorLines (text : String) : List (List Byte × List Nat) :=
  (text.splitOn "\n").filterMap lineFields

/-- Step until RIP is at `stop`, at most `fuel` steps. -/
def runTo (stop : Word) : Nat → DState → Option DState
  | 0, _ => none
  | fuel + 1, d =>
    match step d with
    | none => none
    | some d' => if d'.core.rip = stop then some d' else runTo stop fuel d'

/-- The output core, flags, DF and buffer agree with the processor's. -/
def outMatches (code : List Byte) (c : State) (df : Bool) (memory : Memory) (out : List Nat) :
    Bool :=
  let rv' := out.take 16
  let fl' := out.getD 16 0
  let buf' := out.getD 17 0
  c.rip.toNat == ripBase + code.length &&
    (List.range 16).all (fun k => k == 4 || (c.read (regs.getD k .rax)).toNat == rv'.getD k 0) &&
    flagsMatch c.flags fl' && df == dfOf fl' &&
    (memory.readBytes memBase memLen).map Silmaril.X86.Ext.leValue == some buf'

/-- **One vector**: `Str9D.step` from the input state reaches the end of the instruction with
the processor's result. -/
def checkLine (v : List Byte × List Nat) : Bool :=
  let (code, nums) := v
  let rv := nums.take 16
  let fl := nums.getD 16 0
  let buf := nums.getD 17 0
  let stop := BitVec.ofNat 64 (ripBase + code.length)
  match runTo stop (rv.getD 1 0 + 8) (stateOf code rv fl buf) with
  | none => false
  | some d => outMatches code d.core d.df d.memory (nums.drop 18)

/-- Iterate `execStr back f` until RIP is at `next`. -/
def runStr (back : Bool) (f : Str) (next : Word) : Nat → State → Memory → Option (State × Memory)
  | 0, _, _ => none
  | fuel + 1, s, m =>
    match execStr back f s m next with
    | none => none
    | some (s', m') => if s'.rip = next then some (s', m') else runStr back f next fuel s' m'

/-- **One string-form vector through `execStr` alone**, in the direction of its DF (`true`
for a vector that is not a string form). -/
def checkExecStr (v : List Byte × List Nat) : Bool :=
  let (code, nums) := v
  let rv := nums.take 16
  let fl := nums.getD 16 0
  let buf := nums.getD 17 0
  match decodeStr code with
  | none => true
  | some (f, n) =>
    let next := BitVec.ofNat 64 (ripBase + n)
    n == code.length &&
      match runStr (dfOf fl) f next (rv.getD 1 0 + 1) (coreOf rv fl) (memoryOf code buf) with
      | none => false
      | some (c, m) => outMatches code c (dfOf fl) m (nums.drop 18)

end Silmaril.X86.Str9D.Checks
