module

public import Silmaril.Elf.Link.Dyn.Program.Defs

/-!
# A lattice of libc specifications for the dynamic process model

The dynamic process model (`Proc.proc`, `Program.Verified`) runs the executable's own code
instruction by instruction and every call into the C library as **one atomic step**: the
import's **contract**, a relation `PState → Res PState → Prop` from the call to its return
(`Proc.Contract pre post`: under `pre`, every outcome is an `ok` satisfying `post`; outside
`pre`, anything, including `stop`). A theorem about the process holds for **every** library whose
calls behave as their contracts allow: the contracts are the library's specification, and the
process theorems are proved against it.

This module makes that specification a first-class object.

* `SymContract`: the contract of one symbol, given the context it may read (`Ctx`: the
  library's stdio environment `Program.Std`, the program name, the process world).
* `LibcSpec`: a list of symbol contracts, by name (the `Program.LibTable` `table` of the
  specification; `named` is its contract at a name, `stop` off it).
* **The order.** `Refines c' c`: wherever `c` makes a claim (it does not allow `stop`), every
  outcome of `c'` is one of `c` (weaker precondition, stronger postcondition). `L ≤ M`
  (`LibcSpec.Le`): at every name and context, `M`'s contract refines `L`'s. So **fewer symbols
  and weaker contracts are lower (looser)**: `bot` (no symbol) is the least specification,
  `restrict` drops symbols, `override` puts other contracts in front (interposition).
* `ofTable`, `Program.Bin.needs`: the specification a verified program actually uses, the
  contracts of its imports. `Thms.Verified.of_needs`: **a program verified against a table runs
  correctly against every specification above its `needs`** (any other libc, any version, any
  interposed allocator meeting those contracts).

Instances (for example an allocator table) and implementation relations of ELF files build on
this.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Libc

open Silmaril.X86 (Byte)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Elf.Link.Dyn.Proc (PState)

/-- **What a contract may read** besides the process state: the library's stdio environment
(stream representation, `FILE` pointers, file system, resource bounds), the program name
(`argv[0]`, for diagnostics) and the process world without its import contracts. -/
structure Ctx where
  S : Program.Std
  prog : List Byte
  W : Proc.World

/-- An atomic library step. -/
abbrev Step := PState → Res PState → Prop

/-- **The contract of a symbol**, in a context. -/
abbrev SymContract := Ctx → Step

/-- The step of an unknown symbol: the process stops (nothing is claimed of runs that call it). -/
def stopStep : Step := fun _ r => r = .stop

/-- **Refinement of steps**: wherever `c` makes a claim (does not allow `stop`), every outcome of
`c'` is one of `c`. -/
def Refines (c' c : Step) : Prop := ∀ s, ¬ c s .stop → ∀ r, c' s r → c s r

/-- **A libc specification**: symbol contracts by name (the first entry of a name counts). -/
structure LibcSpec where
  syms : List (Name × SymContract)

namespace LibcSpec

/-- The contract of the name `n`, if the specification has one. -/
def lookup (L : LibcSpec) (n : Name) : Option SymContract := L.syms.lookup n

/-- **The contract at a name** in a context: `stopStep` off the specification. -/
def named (L : LibcSpec) (c : Ctx) (n : Name) : Step :=
  match L.lookup n with
  | some k => k c
  | none => stopStep

/-- The specification as the process model's import table. -/
def table (L : LibcSpec) : Program.LibTable :=
  fun S prog W => L.syms.map fun e => (e.1, e.2 ⟨S, prog, W⟩)

/-- **`L ≤ M`**: `M` is at least as strong as `L` (refines it at every name, in every context);
`L` is the looser specification. -/
def Le (L M : LibcSpec) : Prop := ∀ c n, Refines (M.named c n) (L.named c n)

instance : LE LibcSpec := ⟨Le⟩

/-- **The least specification**: no symbol. -/
def bot : LibcSpec := ⟨[]⟩

/-- Only the symbols named in `ks`. -/
def restrict (L : LibcSpec) (ks : List Name) : LibcSpec :=
  ⟨L.syms.filter fun e => decide (e.1 ∈ ks)⟩

/-- **Interposition**: the contracts of `A` in front of `L`'s (`LD_PRELOAD`, or an allocator
object earlier in the link order than the C library). -/
def override (L A : LibcSpec) : LibcSpec := ⟨A.syms ++ L.syms⟩

/-- The names of the specification. -/
def names (L : LibcSpec) : List Name := L.syms.map (·.1)

/-- **The specification of the names `ns` in a table**: each name's contract as the table gives
it. -/
def ofTable (T : Program.LibTable) (ns : List Name) : LibcSpec :=
  ⟨ns.map fun n => (n, fun c => Streams.namedOf (T c.S c.prog c.W) n)⟩

/-- A specification is **covered** by `L` when every name it has, `L` has. -/
def Covers (L M : LibcSpec) : Prop := ∀ n, (M.lookup n).isSome → (L.lookup n).isSome

end LibcSpec

/-- **What a program needs** of a table: the contracts of its imports. -/
def _root_.Silmaril.Elf.Link.Dyn.Program.Bin.needs (B : Program.Bin) (T : Program.LibTable) :
    LibcSpec :=
  LibcSpec.ofTable T (B.imports.map (·.name))

/-- **Open: verification is generic in the binding.** A program verified with one library pin
(glibc's lookups give its imports' addresses) is verified, against the same table, with every
other pin that binds the same imports (another glibc build, musl, …): the same file, its facts
regenerated for the other library (`B'.ok libc' ld'`). The program proofs are generic in the load
bases but read the import offsets from the pin; this Task is what moves them to another library
file. (An allocator object *preloaded* in front of the C library adds an object to the loader's
search scope, `ExeLoaded [exe, preload, libc, ld]`, which `Program.Verified` does not have yet.) -/
def Task.bindingGeneric (B : Program.Bin) (libc ld : Program.LibPin) (spec : Program.Spec)
    (tier : Program.Tier) (L : Program.LibTable) (env : Program.Std → Prop) : Prop :=
  Program.Verified B libc ld spec tier L env →
    ∀ (B' : Program.Bin) (libc' ld' : Program.LibPin), B'.file = B.file →
      B'.imports.map (·.name) = B.imports.map (·.name) →
      B'.ok libc' ld' = true → libc'.ok = true → ld'.ok = true →
      Program.Verified B' libc' ld' spec tier L env

end Silmaril.Elf.Link.Dyn.Libc
