module

public import Silmaril.Machine.X86.Lir.Correct.Defs
public import Silmaril.X86.Ext.Behaviour

/-!
# The loaded image, independently of an `Env`

`Env.load` (in `Lir.Correct`) builds the loaded machine from an `Env`, reading
the code bytes and the entry address from the compiled program. `loadImage`
is the same construction with the code bytes and the entry address as
parameters, so that a loaded state can be described without an `Env` or a Lir
program: `Env.load_eq_loadImage` holds by `rfl`.

The loaded memory has exactly the three regions of the space (code, stack,
linear memory) and holds only the code at `codeBase`, the return address
`exit` in the eight bytes at `E0` and the linear memory at `memBase`. RSP is
`E0`, `r14` and `r15` hold the stack limit and the linear-memory base,
`rbx rbp r12 r13` the `saved` values, the arguments are in `rdi rsi rdx rcx r8
r9`, RIP is the entry, and every other register and the flags come from
`init`.

`stackSites p L` lists, for every function of `p` laid out by `L`, the address
of the UD2 of its stack-limit check and the number of stack bytes the check
requires. `Env.Overflow.exhausted` shows that a stop at a stack-limit check
(`Env.Overflow`) is resource exhaustion in the sense of
`Ext.StackCheck.Exhausted` for these sites.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine

/-- The bytes of a loaded image: `code` at `codeBase`, `exit` at `E0`, the
linear memory `lm` at `memBase`. -/
def imageBytes (S : Space) (code : List Byte) (exit : Word) (E0 : Nat) (lm : Lir.Memory) :
    Process.ByteMemory :=
  Memory.install (Memory.install (Memory.install ∅ S.codeBase code) E0 (Ext.leBytes exit 8))
    S.memBase (List.ofFn fun i : Fin lm.size => lm.bytes i)

/-- The registers of a loaded image. -/
def imageRegs (S : Space) (E0 : Nat) (saved : Reg → Word) (args : List Word) (init : State)
    (r : Reg) : Word :=
  if r = .rsp then BitVec.ofNat 64 E0
  else if r = .r14 then BitVec.ofNat 64 S.stackLo
  else if r = .r15 then BitVec.ofNat 64 S.memBase
  else if r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 then saved r
  else match argIndex r with
    | some j => args.getD j 0
    | none => init.read r

/-- The loaded machine at `entry`: the body of `Env.load`, with the code bytes
and the entry address as parameters. -/
def loadImage (S : Space) (code : List Byte) (entry : Nat) (exit : Word) (E0 : Nat)
    (saved : Reg → Word) (args : List Word) (lm : Lir.Memory) (init : State) : MState where
  core := { regs := imageRegs S E0 saved args init, rip := BitVec.ofNat 64 entry, flags := init.flags }
  memory := ⟨S.regions code.length, imageBytes S code exit E0 lm⟩

theorem Env.load_eq_loadImage {P : Type} (E : Env P) (lm : Lir.Memory)
    (main : Lir.FuncId) (args : List Word) (init : State) :
    E.load lm main args init =
      loadImage E.S E.code (E.L.func main) E.exit E.E0 E.saved args lm init := rfl

/-! ## Registers of the loaded image -/

section Regs

variable {S : Space} {code : List Byte} {entry : Nat} {exit : Word} {E0 : Nat}
  {saved : Reg → Word} {args : List Word} {lm : Lir.Memory} {init : State}

theorem loadImage_read (r : Reg) :
    (loadImage S code entry exit E0 saved args lm init).core.read r =
      imageRegs S E0 saved args init r := rfl

@[simp] theorem loadImage_rip :
    (loadImage S code entry exit E0 saved args lm init).core.rip = BitVec.ofNat 64 entry := rfl

theorem loadImage_rsp :
    (loadImage S code entry exit E0 saved args lm init).core.read .rsp = BitVec.ofNat 64 E0 := rfl

theorem loadImage_r14 :
    (loadImage S code entry exit E0 saved args lm init).core.read .r14 =
      BitVec.ofNat 64 S.stackLo := rfl

theorem loadImage_r15 :
    (loadImage S code entry exit E0 saved args lm init).core.read .r15 =
      BitVec.ofNat 64 S.memBase := rfl

theorem loadImage_saved {r : Reg} (hr : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13) :
    (loadImage S code entry exit E0 saved args lm init).core.read r = saved r := by
  rw [loadImage_read]
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

/-- The `j`-th argument register holds the `j`-th argument word (zero beyond
the list). -/
theorem loadImage_arg {j : Nat} (hj : j < 6) :
    (loadImage S code entry exit E0 saved args lm init).core.read (argRegN j) = args.getD j 0 := by
  rw [loadImage_read]
  have hne : ∀ i : Fin 6, argReg i ≠ .rsp ∧ argReg i ≠ .r14 ∧ argReg i ≠ .r15 ∧
      argReg i ≠ .rbx ∧ argReg i ≠ .rbp ∧ argReg i ≠ .r12 ∧ argReg i ≠ .r13 := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hne ⟨j, hj⟩
  rw [← argRegN_lt hj] at h1 h2 h3 h4 h5 h6 h7
  simp only [imageRegs, h1, h2, h3, h4, h5, h6, h7, ite_false, or_self, argIndex_argRegN hj]

end Regs

/-! ## Stack-check sites -/

/-- The stack-check sites of `p` laid out by `L`: for every function, the
address of the UD2 of its stack-limit check (`checkSeq`) and the number of
stack bytes the check requires (`need`). -/
def stackSites {P : Type} (p : Lir.Prog P) (L : Layout) : List (Nat × Nat) :=
  (List.range p.funcs.length).map fun f =>
    (L.func f + (((checkSeq (nslots ((p.func? f).getD emptyFunc))).take 4).flatMap
      Ext.encode).length, need (nslots ((p.func? f).getD emptyFunc)))

/-- The stack-check sites of an environment. They depend only on the register
assignment, the program and `S.codeBase`. -/
def Env.stackSites {P : Type} (E : Env P) : List (Nat × Nat) := Backend.stackSites E.p E.L

/-- A stop at a stack-limit check is exhaustion at a declared site. -/
theorem Env.Overflow.exhausted {P : Type} {E : Env P} {t : MState} (h : E.Overflow t) :
    Ext.StackCheck.Exhausted E.S.stackLo E.stackSites t := by
  obtain ⟨-, f, fn, hfn, hrip, hrsp⟩ := h
  have hlt : f < E.p.funcs.length := (List.getElem?_eq_some_iff.mp hfn).1
  refine ⟨E.ovfAddr f, need (nslots fn), List.mem_map.mpr ⟨f, List.mem_range.mpr hlt, ?_⟩,
    hrip, hrsp⟩
  simp only [Env.ovfAddr, Env.ns, hfn, Option.getD_some]

end Silmaril.X86.Backend
