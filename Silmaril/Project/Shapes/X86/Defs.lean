module

public import Silmaril.Project.Shapes.Elf.Defs
public import Silmaril.X86.Str9.Thms
public import Silmaril.Problems.Shapes.X86.Defs

/-!
# Standard problem shapes: x86-64 functions

System V function contracts (`Silmaril.X86.FnContract`) as shapes, parametrized by the x86-64
**model** `M : Model` (a segment-VC machine on the open state `MState`). The standard models
are the named instances `….open` (`Open.isa`), `….open9` (`Open9.isa`) and `….str9`
(`Str9.isa`, with the string forms); each extends the previous one, and
`Silmaril.Project.Shapes.X86.Thms` transfers a solved contract along that order. The demonic
shapes over a *class* of machines are `x86.correct` and `x86.correct_loose`, the problem
templates `Silmaril.Problems.Shapes.Correct` and `CorrectLoose` registered as shapes.

| name | statement |
|---|---|
| `silmaril.shapes.x86.contract` | `Contract M S`: the spec `S` is totally correct on `M` (`S.Total M`) |
| `silmaril.shapes.x86.contract.{open,open9,str9}` | the same on a standard model |
| `silmaril.shapes.x86.contract_strict` | `ContractStrict M S`: first-return total correctness (`S.Strict M`) |
| `silmaril.shapes.x86.abi_function` | `AbiFn M p S`: the contract `S` is entered at the function placed by `p` (`EntersAt`), is not vacuous (`Nonvacuous`), and holds on `M` |
| `silmaril.shapes.x86.abi_function.{open,open9,str9}` | the same on a standard model |
| `silmaril.shapes.elf.fn_contract` | `ElfFn L M exe addr code S`: `exe` loads `code` at `addr` (`rx`), `S` is tied to those bytes and that `rip` range (`EntersCode`; `S.entry` may assume more memory than the ELF provides) and not vacuous (`Nonvacuous`), and `S` holds on `M` |
| `silmaril.shapes.elf.fn_contract.{x86_open,x86_open9}` | the same with `Loader.x86` and `Open.isa` / `Open9.isa` |
| `silmaril.shapes.x86.correct` | `Correct 𝓜 S`: for every placement `entry`, `S entry` is demonically totally correct on every member of the class `𝓜` (`FnCorrect`) |
| `silmaril.shapes.x86.correct_loose` | `CorrectLoose D S`: the same on the down-set of the loose top over the listing table `D` |

`Contract M S` alone is a statement about `S`: it names no code, and a spec with an
unsatisfiable `entry` fills it. The function shapes add the two facts that make the contract
*about the code*:

* `EntersCode M addr code S` (`elf.fn_contract`): every entry state `S` admits holds `code` at
  `addr` as fetchable code (`Ext.Loaded`) and has `rip` inside it; `EntersAt M p S`
  (`x86.abi_function`): the same for the region of `p`, with `rip` at the function's entry.
  Without it, a contract about entirely different code fills the row.
* `Nonvacuous M S`: some live state meeting the System V entry obligations satisfies
  `S.entry`. Without it, a spec with `entry := False` fills the row (`ElfFnWeak.of_vacuous`,
  `ElfFn.not_vacuous` in `Thms`).

`ElfFn` is the **segment theorem ⇒ ELF theorem** shape: a contract about the code segment
`code` placed at `addr` is proved once for every image that holds it, and `ElfFn.of_segment`
ties it to the executable that loads it. `rip` is only required to lie *inside* the code, not
at `addr`: a row names the loaded region and the function is entered at its offset in it.
`ElfFnWeak` (`Loads ∧ Contract`) is the statement without the two conditions, kept to state
what they exclude; it is not a shape.

`AbiFn` is the same statement for a function given by its placement `p : Placement` (a code
region `p.code` at `p.base` and the function's offset `p.off` in it) instead of an executable;
`S.entry` may ask more than `EntersAt` (readable inputs, a writable frame, loaded read-only
constants). A project that also has the function's assembly listing states that the listing
assembles to `p.code` as a separate fact. `AbiFn.elfFn` turns a row and the loader fact for
the region into the `elf.fn_contract` row. A row:

```lean
silmaril instance demo.f.abi := silmaril.shapes.x86.abi_function.open9
  (p := Demo.placement) (S := Demo.spec)
```
-/

@[expose] public section

namespace Silmaril.Project.Shapes

open Silmaril.X86 (MState Word Byte)
open Silmaril.X86 (FnContract)

/-- An x86-64 model: a segment-VC machine on the open machine state. -/
abbrev Model := Silmaril.X86.SegVC.Isa MState

/-- **The System V contract `S` holds on the model `M`**: from every live entry state meeting
the ABI entry obligations and `S.entry`, `M` reaches a System V return with `S.post`, writing
only inside the footprint (`FnContract.Spec.Total`).

This is a statement about `S` alone: it names no code, and a spec with an unsatisfiable
`entry` fills it. A row that is meant to be about a function pairs it with `EntersCode` and
`Nonvacuous` (as `elf.fn_contract` does). -/
@[problem "silmaril.shapes.x86.contract"
  (title := "A System V function contract holds on an x86-64 model")]
def Contract (M : Model) (S : FnContract.Spec MState) : Prop := S.Total M

/-- **First-return total correctness of `S` on `M`** (`FnContract.Spec.Strict`): the run
reaches a result state without passing a returned state before. -/
@[problem "silmaril.shapes.x86.contract_strict"
  (title := "A System V function contract holds to the first return")]
def ContractStrict (M : Model) (S : FnContract.Spec MState) : Prop := S.Strict M

/-- **`S` is a contract about `code` at `addr`** on `M`: every entry state `S` admits holds
`code` at `addr` as fetchable code (`Ext.Loaded`) and has `rip` inside it. -/
def EntersCode (M : Model) (addr : Nat) (code : List Byte) (S : FnContract.Spec MState) :
    Prop :=
  ∀ s, S.entry s → Silmaril.X86.Ext.Loaded (M.mem s) (BitVec.ofNat 64 addr) code ∧
    addr ≤ (M.core s).rip.toNat ∧ (M.core s).rip.toNat < addr + code.length

/-- **`S` is not vacuous on `M`**: some live state meeting the System V entry obligations
(`FnContract.AbiEntry`) satisfies `S.entry`, so `Contract M S` promises a run from it. -/
def Nonvacuous (M : Model) (S : FnContract.Spec MState) : Prop :=
  ∃ s, M.live s ∧ FnContract.AbiEntry (M.core s) (M.mem s) ∧ S.entry s

/-- **A placed function**: a loaded code region (`code` at `base`) and the function's offset
in it. -/
structure Placement where
  base : Word
  code : List Byte
  off : Nat

/-- The function's entry, as a word. -/
def Placement.entry (p : Placement) : Word := p.base + BitVec.ofNat 64 p.off

/-- The states at which the function placed by `p` is entered: the region loaded, `rip` at
the entry. -/
def Placement.Entered (p : Placement) (m : MState) : Prop :=
  Silmaril.X86.Ext.Loaded m.memory p.base p.code ∧ m.core.rip = p.entry

/-- The spec of the function placed by `p` with entry exactly `Entered p`, write footprint
`footprint` and postcondition `post`. -/
def Placement.spec (p : Placement) (footprint : MState → Nat → Prop)
    (post : MState → MState → Prop) : FnContract.Spec MState where
  entry := p.Entered
  footprint := footprint
  post := post

/-- **`S` is a contract about the function placed by `p`** on `M`: every entry state `S` admits
holds the region of `p` as fetchable code and has `rip` at the function's entry. -/
def EntersAt (M : Model) (p : Placement) (S : FnContract.Spec MState) : Prop :=
  ∀ s, S.entry s →
    Silmaril.X86.Ext.Loaded (M.mem s) p.base p.code ∧ (M.core s).rip = p.entry

/-- **A placed function meets its System V contract** on `M`: the contract `S` is about the
function placed by `p` (`EntersAt`: its entry states have the region loaded and `rip` at the
function) and not vacuous (`Nonvacuous`: some System V entry state meets it); and `S` holds on
`M`. `S.entry` may require more than `EntersAt` (inputs, a frame, constants). -/
@[problem "silmaril.shapes.x86.abi_function"
  (title := "A placed x86-64 function meets its System V contract")]
def AbiFn (M : Model) (p : Placement) (S : FnContract.Spec MState) : Prop :=
  EntersAt M p S ∧ Nonvacuous M S ∧ Contract M S

/-- **A function of an executable meets its System V contract** (segment theorem ⇒ ELF
theorem): the loader `L` puts `code` at `addr` in an `rx` segment of `exe`; the contract `S`
is tied to those bytes and that `rip` range (`EntersCode`: every entry state has `code` at
`addr` and `rip` in it; `S.entry` may still assume more memory than the ELF provides) and
not vacuous (`Nonvacuous`: some System V entry state meets it); and `S` holds on `M`. -/
@[problem "silmaril.shapes.elf.fn_contract"
  (title := "A function an executable loads meets its System V contract")]
def ElfFn (L : Loader) (M : Model) {V : Type} (exe : Value V) (addr : Nat)
    (code : List Byte) (S : FnContract.Spec MState) : Prop :=
  Loads L exe "rx" addr code ∧ EntersCode M addr code S ∧ Nonvacuous M S ∧ Contract M S

/-- **The weak form of `ElfFn`**: the loader fact and the contract, with nothing tying `S` to
`code`. A vacuous spec or a spec about other code fills it (`ElfFnWeak.of_vacuous`). Not a
shape; `ElfFn.weak` forgets the two conditions. -/
def ElfFnWeak (L : Loader) (M : Model) {V : Type} (exe : Value V) (addr : Nat)
    (code : List Byte) (S : FnContract.Spec MState) : Prop :=
  Loads L exe "rx" addr code ∧ Contract M S

/-- **Demonic function correctness on the class `𝓜`** (`Silmaril.Problems.FnCorrect`): for
every placement `entry`, `S entry` is totally correct on every member of `𝓜`. -/
@[problem "silmaril.shapes.x86.correct"
  (title := "A function is correct on every machine of a model class")]
def Correct (𝓜 : Silmaril.Problems.Class MState) (S : Word → FnContract.Spec MState) : Prop :=
  Silmaril.Problems.Shapes.Correct 𝓜 S

/-- **Demonic function correctness below the loose top** over the listing table `D`
(`Silmaril.Problems.Shapes.CorrectLoose`). -/
@[problem "silmaril.shapes.x86.correct_loose"
  (title := "A function is correct on every refinement of the loose x86-64 top")]
def CorrectLoose (D : Silmaril.X86.Loose.DTable Silmaril.X86.Loose.Listing.LForm)
    (S : Word → FnContract.Spec MState) : Prop :=
  Silmaril.Problems.Shapes.CorrectLoose D S

end Silmaril.Project.Shapes

end

silmaril instance silmaril.shapes.x86.contract.open (title := "contract, on the open machine (Open)") :=
  silmaril.shapes.x86.contract (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.x86.contract.open9 (title := "contract, on the open machine (Open9)") :=
  silmaril.shapes.x86.contract (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.x86.contract.str9
    (title := "contract, on the open machine with string forms (Str9)") :=
  silmaril.shapes.x86.contract (M := Silmaril.X86.Str9.isa)
silmaril instance silmaril.shapes.x86.abi_function.open
    (title := "abi_function, on the open machine (Open)") :=
  silmaril.shapes.x86.abi_function (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.x86.abi_function.open9
    (title := "abi_function, on the open machine (Open9)") :=
  silmaril.shapes.x86.abi_function (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.x86.abi_function.str9
    (title := "abi_function, on the open machine with string forms (Str9)") :=
  silmaril.shapes.x86.abi_function (M := Silmaril.X86.Str9.isa)
silmaril instance silmaril.shapes.elf.fn_contract.x86_open
    (title := "fn_contract, with the x86-64 loader and the open machine (Open)") :=
  silmaril.shapes.elf.fn_contract (L := Silmaril.Project.Shapes.Loader.x86)
    (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.elf.fn_contract.x86_open9
    (title := "fn_contract, with the x86-64 loader and the open machine (Open9)") :=
  silmaril.shapes.elf.fn_contract (L := Silmaril.Project.Shapes.Loader.x86)
    (M := Silmaril.X86.Open9.isa)
