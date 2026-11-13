module

public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.Machine.RTL.Thms

/-!
# The RTL and SSA instances of the lifting shape

Two `Ir`s for `silmaril.shapes.sysv.lifts`, over the machine RTL of `Silmaril.Machine.RTL`:

* `rtl R`: a function of an RTL program (`Silmaril.Machine.RTL.Prog R`: a control-flow graph
  of three-address instructions over registers `R`, with calls), run by its small-step
  semantics `Prog.step`;
* `rtlSSA R`: a function of an RTL program in SSA form (`Silmaril.Machine.RTL.SSA.Prog R`:
  blocks with block arguments in place of φ-nodes), run by its own small-step semantics
  `SSA.Prog.step`, together with its well-formedness (`SSA.Func.WellFormed`: single
  assignment, uses dominated, arguments matching their targets). `Silmaril.Machine.RTL`
  relates it to λSSA (`toLambdaSSA`, with a semantic `iff`).

The **System V reading** is the same for both: an INTEGER argument is passed as its 64-bit
word, zero-extended (`argWords`), as the RTL's call convention takes a list of words
(`Prog.start`); a scalar result is the one returned word, read as the signature's return scalar
(`ResultIs`, the relational `SystemV.Encodes`: for a 32-bit result the upper bits are free).
The machine RTL's memory is its own (`Silmaril.Machine.Lir.Memory`); a function's meaning
quantifies over every initial memory for safety and asks for one for a result.

**Meaning.** Safe on `a`: from every initial memory the run starts and *returns* (no trap, no
stuck state, no divergence: `Behaves … (.returned …)`). Returns `r`: from some initial memory
the run returns the words that read as `r`. Both semantics are deterministic
(`Behaves.unique`), so the meaning is functional on each memory.

**Not here.** The flat λRTL CFG (`Silmaril.SSA.LambdaRTL.CFG`) is stated over abstract models
of its operators, with no machine words; its lowering to `Lir` functions with a simulation
against `Lir` execution is still open, so it gets no System V reading yet. λSSA itself is
reached through `toLambdaSSA` once a word model of λSSA is fixed.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.SysV

open Silmaril.X86 (Word)
open Silmaril.X86.SystemV.CApi (Signature Scalar Arguments ReturnValue)

/-- The 64-bit word an INTEGER argument is passed in: zero-extended. -/
def argWord : (kind : Scalar) → kind.Value → Word
  | .int32, v => v.setWidth 64
  | .uint32, v => v.setWidth 64
  | .int64, v => v
  | .uint64, v => v
  | .pointer, v => v

/-- The argument words of a call, in order. -/
def argWords : {kinds : List Scalar} → Arguments kinds → List Word
  | _, .nil => []
  | _, .cons (kind := kind) v rest => argWord kind v :: argWords rest

/-- The returned words `vs` are the C result `r`: no word for `void`, otherwise one word that
encodes `r` (`SystemV.Encodes`). -/
def ResultIs : (kind : Option Scalar) → List Word → ReturnValue kind → Prop
  | none, vs, _ => vs = []
  | some kind, vs, r => ∃ w, vs = [w] ∧ Silmaril.X86.SystemV.Encodes kind r w

/-! ## RTL -/

/-- **An RTL function**: a C signature, an RTL program and the function of it. -/
structure RtlFn (R : Type) where
  sig : Silmaril.X86.SystemV.CApi.Signature
  prog : Silmaril.Machine.RTL.Prog R
  fn : Silmaril.Machine.RTL.FuncId

/-- **RTL functions as an IR**, with the System V reading of arguments and results. -/
def rtl (R : Type) [DecidableEq R] : Ir where
  Fn := RtlFn R
  sig := RtlFn.sig
  meaning f :=
    { Safe := fun a => ∀ mem, ∃ s, f.prog.start f.fn (argWords a) mem = some s ∧
        ∃ vs m, Silmaril.Machine.RTL.Behaves f.prog s (.returned vs m)
      Returns := fun a r => ∃ mem s vs m, f.prog.start f.fn (argWords a) mem = some s ∧
        Silmaril.Machine.RTL.Behaves f.prog s (.returned vs m) ∧ ResultIs f.sig.result vs r }

/-! ## RTL in SSA form -/

/-- **An SSA-form RTL function**: a C signature, an SSA program, the function of it, and that
function's well-formedness. -/
structure RtlSSAFn (R : Type) [DecidableEq R] where
  sig : Silmaril.X86.SystemV.CApi.Signature
  prog : Silmaril.Machine.RTL.SSA.Prog R
  fn : Silmaril.Machine.RTL.FuncId
  wellFormed : ∀ F, prog.func? fn = some F → F.WellFormed

/-- **SSA-form RTL functions as an IR**, with the System V reading of arguments and results. -/
def rtlSSA (R : Type) [DecidableEq R] : Ir where
  Fn := RtlSSAFn R
  sig := RtlSSAFn.sig
  meaning f :=
    { Safe := fun a => ∀ mem, ∃ s, f.prog.start f.fn (argWords a) mem = some s ∧
        ∃ vs m, Silmaril.Machine.RTL.SSA.Behaves f.prog s (.returned vs m)
      Returns := fun a r => ∃ mem s vs m, f.prog.start f.fn (argWords a) mem = some s ∧
        Silmaril.Machine.RTL.SSA.Behaves f.prog s (.returned vs m) ∧
        ResultIs f.sig.result vs r }

end Silmaril.Project.Shapes.SysV

end
