module

public import Silmaril.X86.Decompile.Functions
public import Silmaril.Semantics.CPort.Formats.ELF.Extract.Defs
/-!
# Proposing a partition

**Nothing in this file is trusted.** These are heuristics that guess where the
functions are; `Decompile.check` is the judge, and the soundness theorems
depend on the checker alone. Nothing is proved about the proposals beyond the
fact that they are total functions.

* `ofSymbols` reads the function symbols of an object's section. It is exact
  when the symbol table is, which for a compiler-produced object it is.
* `ofStripped` guesses from the code alone, for objects with no symbol table.

## What `ofSymbols` does with padding

Function symbols do not tile a `.text` section: an assembler aligns each
function, leaving a NOP run before the next one. Every byte between the end of
one symbol and the start of the next becomes a `Partition.padding` range, and
so does any tail after the last symbol. The checker then requires those ranges
to decode entirely to NOPs.

The alternative — appending the padding to the preceding function — does not
survive the checker: the last NOP of the run falls through past the extended
extent, which is `Reject.fallsOffEnd`. Prepending it to the following function
would survive, but `FunctionSpec` has no extent start separate from its entry,
so that is not expressible. Explicit padding ranges are the honest form.

## What `ofSymbols` does with relocations

Every `R_X86_64_PC32` and `R_X86_64_PLT32` relocation against the section
becomes a `Partition.relocs` entry: an internal target when the relocation's
symbol is defined in the section, an external one when it is undefined. Every
undefined symbol so reached is declared in `Partition.externals`. The checker
records both in the `Accepted` result, so a proposal that over-declares
relocations weakens the stated guarantee rather than hiding the weakening.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.Propose

open Silmaril.X86.Decompile
open Silmaril.Formats.ELF

/-! ## Names -/

/-- A Lean string as the NUL-free byte string an ELF name table holds. -/
def nameBytes (name : String) : NameBytes :=
  name.toUTF8.toList.map fun byte => BitVec.ofNat 8 byte.toNat

/-- An ELF name as a Lean string, or `""` when the bytes are not UTF-8. -/
def nameString (name : NameBytes) : String :=
  (String.fromUTF8? ⟨(name.map fun byte => UInt8.ofNat byte.toNat).toArray⟩).getD ""

/-! ## From a symbol table -/

/-- `STT_FUNC`: the symbol type of a defined function. -/
def STT_FUNC : Nat := 2

/-- The ranges of `[cursor, limit)` that the given extents, in address order,
leave unclaimed. -/
def gaps (cursor limit : Nat) : List FunctionSpec → List (Nat × Nat)
  | [] => if cursor < limit then [(cursor, limit)] else []
  | f :: rest =>
    (if cursor < f.entry then [(cursor, f.entry)] else []) ++ gaps (f.entry + f.size) limit rest

/-- Every PC32 or PLT32 relocation against section `index`, as a declared call
target keyed by the address of its displacement field. -/
def relocTargets (file : ObjectFile) (index : Nat) : List (Nat × Target) :=
  file.relocations.filterMap fun relocation =>
    if relocation.targetSection = index ∧
        (relocation.kind = X86_64.R_PC32 ∨ relocation.kind = X86_64.R_PLT32) then
      match file.symbols[relocation.symbol]? with
      | none => none
      | some symbol =>
        if symbol.raw.sectionIndex = 0 then
          some (relocation.offset, .external (nameString symbol.name))
        else some (relocation.offset, .internal symbol.raw.value)
    else none

/-- Build a partition from the function symbols of a named section. Addresses
are offsets from the start of the section, so the matching `Region` has
`base = 0`. `none` if the file has no section of that name. -/
def ofSymbols (file : ObjectFile) (sectionName : String) : Option Partition := do
  let index ← file.sections.findIdx? fun part => part.name == nameBytes sectionName
  let owner ← file.sections[index]?
  let defined := file.symbols.filter fun symbol =>
    symbol.kind == STT_FUNC && symbol.raw.sectionIndex == index
  let funcs := (defined.map fun symbol =>
      ({ name := nameString symbol.name, entry := symbol.raw.value,
         size := symbol.raw.size } : FunctionSpec)).mergeSort fun a b => a.entry ≤ b.entry
  let relocs := relocTargets file index
  let externals := (relocs.filterMap fun entry =>
    match entry.2 with
    | .external name => some name
    | .internal _ => none).eraseDups
  pure { funcs, padding := gaps 0 owner.data.size funcs, relocs, externals }

/-! ## From the code alone -/

/-- The literal targets of the jumps and branches of a listing. -/
def branchTargets (ds : List Decoded) : List Nat :=
  ds.flatMap fun d => d.edges.filterMap fun e =>
    match e with
    | .jump t => some t
    | .branch t => some t
    | _ => none

/-- The literal targets of the calls of a listing. -/
def callTargets (ds : List Decoded) : List Nat :=
  ds.flatMap fun d => d.edges.filterMap fun e =>
    match e with
    | .call t => some t
    | _ => none

/-- The address after each `ret` or `ud2`: where a following function would
start if the one before it has ended. -/
def afterTerminators (ds : List Decoded) : List Nat :=
  (ds.zip ds.tail).filterMap fun pair =>
    if pair.1.instr == .ret || pair.1.instr == .ud2 then some pair.2.addr else none

/-- A prologue start: `endbr64`, or a `push %rbp` that begins the frame setup.
Both are seeds, since a function may be entered only by an indirect call the
model does not represent. -/
def prologueStarts (ds : List Decoded) : List Nat :=
  ds.filterMap fun d =>
    match d.instr with
    | .endbr64 => some d.addr
    | .push .rbp => some d.addr
    | _ => none

/-- Consecutive seeds as extents, the last running to `limit`. -/
def spansOfSeeds (limit : Nat) : List Nat → List FunctionSpec
  | [] => []
  | [a] => [{ name := "fn_" ++ toString a, entry := a, size := limit - a }]
  | a :: b :: rest =>
    { name := "fn_" ++ toString a, entry := a, size := b - a } :: spansOfSeeds limit (b :: rest)

/-- Guess a partition from the code alone, for a region with no symbol table.
Seeds are the region base, the literal targets of calls, and the address after
a `ret` or `ud2` that no jump or branch targets and at which a prologue starts;
each seed runs to the next one. There is no padding, no relocation table and no
external declaration: a stripped region offers no evidence for any of the
three, and `check` will say so. -/
def ofStripped (r : Region) (fuel : Nat) : Partition :=
  let ds := (r.decode? fuel).getD []
  let limit := r.base + r.bytes.length
  let branches := branchTargets ds
  let prologues := prologueStarts ds
  let extra := (afterTerminators ds).filter fun a => !(a ∈ branches) && a ∈ prologues
  let seeds := (r.base :: (callTargets ds ++ extra)).eraseDups
  let kept := (seeds.filter fun a => decide (IsStart ds a)).mergeSort fun a b => a ≤ b
  { funcs := spansOfSeeds limit kept, padding := [], relocs := [], externals := [] }

end Silmaril.X86.Decompile.Propose
