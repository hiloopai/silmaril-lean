module

public import Silmaril.Machine.RiscV.Lir.Loader.Defs
/-!
# The loaded image, with the entry PC as a parameter

`loadState S code p f args lm` (in `Lir.Loader`) uses the Lir program `p` and
the function `f` only to compute the entry PC `addrOf S.codeBase (funcStart p
f)`. `loadImage S code pc args lm` is the same state with the PC as a
parameter, so that a loaded state can be described without a Lir program:
`loadState_eq_loadImage` holds by `rfl`.

The memory has exactly the three regions of the space: the encoded code at
`codeBase`, a zero-filled stack and the linear memory `lm` at `memBase`.
`sp = stackHi`, `ra` is the halt stub, `s10 = stackLo`, `s11 = memBase`,
`a0 …` hold the arguments and every other register is zero.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.RiscV.Ext (MState)

/-- The loaded state with entry PC `pc`. -/
def loadImage (S : Space) (code : List Ext.Instr) (pc : Word) (args : List Word)
    (lm : Machine.Lir.Memory) : MState :=
  ⟨⟨initRegs S (addrOf S.codeBase haltIdx) args, pc⟩, loadMemory S code lm⟩

theorem loadState_eq_loadImage {P : Type} (S : Space) (code : List Ext.Instr)
    (p : Machine.Lir.Prog P) (f : Machine.Lir.FuncId) (args : List Word)
    (lm : Machine.Lir.Memory) :
    loadState S code p f args lm = loadImage S code (addrOf S.codeBase (funcStart p f)) args lm :=
  rfl

@[simp] theorem loadImage_pc (S : Space) (code : List Ext.Instr) (pc : Word) (args : List Word)
    (lm : Machine.Lir.Memory) : (loadImage S code pc args lm).core.pc = pc := rfl

/-- The registers of the loaded image: stack pointer, return address (the halt
stub), stack limit, linear-memory base and the arguments in `a0 … a7`. -/
theorem loadImage_read (S : Space) (code : List Ext.Instr) (pc : Word) (args : List Word)
    (lm : Machine.Lir.Memory) :
    let s := (loadImage S code pc args lm).core
    s.read sp = BitVec.ofNat 64 S.stackHi ∧ s.read ra = addrOf S.codeBase haltIdx ∧
      s.read s10 = BitVec.ofNat 64 S.stackLo ∧ s.read s11 = BitVec.ofNat 64 S.memBase ∧
      ∀ k < 8, s.read (argRegN k) = args.getD k 0 :=
  initRegs_read S (addrOf S.codeBase haltIdx) args pc

end Silmaril.RiscV.Backend
