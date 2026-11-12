module

public import Silmaril.Libc.Contract.Alloc.Defs
public import Silmaril.Libc.Contract.Stdio.Defs

/-!
# The C library as a tensor, and the generated diagram of contracts

**The tensor.** `libcSig k l := allocSig k ⊗ stdioSigOf l`: the allocator at level `k` and the
`stdio` functions of the catalogue list `l`, side by side; the invariant interface is the pair
(`Heap`, `Streams`). Its contract `libcC k l K L` is the tensor of `allocC k` and `stdioC l K L`
(a `stdio` call leaves the heap alone, an allocator call the streams), its model `libcModel k l`
the tensor of the bottom allocator and the stream model. `Thms` proves that the tensor model
meets the tensor contract and that each factor is recovered through the injections.

**The diagram** (`Diagram.mermaid`) is generated from the catalogue: one node per named
signature (its Lean name, its contract, its functions), and an edge `S --> T` for every inclusion
of function sets with nothing strictly between (the Hasse diagram of the signatures under
inclusion). Every edge is a signature morphism along which the contract of `T` restricts to the
contract of `S` (`allocC_restrict`, `stdioC_restrict`, and for the tensor `le_restrict_inl`,
`le_restrict_inr`). `Thms` checks the rendered text (`#guard`).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

/-! ## The tensor -/

/-- **The C library's signature**: the allocator at level `k` and the `stdio` list `l`. -/
def libcSig (k : Nat) (l : List LFn) : Sig libcApi := Sig.tensor (allocSig k) (stdioSigOf l)

/-- **Its contract**: the tensor of the allocator's and `stdio`'s. -/
def libcC (k : Nat) (l : List LFn) (K L : FmtSet) : Contract (libcSig k l) :=
  (allocC k).tensor (stdioC l K L)

/-- **Its model**: the bottom allocator beside the stream model. -/
def libcModel (k : Nat) (l : List LFn) : Model (libcSig k l) :=
  (bottomAlloc k).tensor (streamModel l)

/-! ## The diagram -/

namespace Diagram

/-- A node: an identifier, the signature's and the contract's Lean names, the functions. -/
structure Node where
  id : String
  sig : String
  contract : String
  fns : List LFn
  /-- For a tensor node, the identifiers of its factors. -/
  factors : List String := []

/-- **The named signatures.** -/
def nodes : List Node :=
  [⟨"A1", "allocSig 1", "allocC 1", allocList 1, []⟩,
   ⟨"A2", "allocSig 2", "allocC 2", allocList 2, []⟩,
   ⟨"A3", "allocSig 3", "allocC 3", allocList 3, []⟩,
   ⟨"A4", "allocSig 4", "allocC 4", allocList 4, []⟩,
   ⟨"P", "putsSig", "stdioC putsList K L", putsList, []⟩,
   ⟨"O", "outSig", "stdioC outList K L", outList, []⟩,
   ⟨"I", "inSig", "stdioC inList K L", inList, []⟩,
   ⟨"S", "stdioSig", "stdioC stdioList K L", stdioList, []⟩,
   ⟨"L", "libcSig 4 stdioList", "libcC 4 stdioList K L", allocList 4 ++ stdioList, ["A4", "S"]⟩]

/-- `a ⊆ b` as lists of functions. -/
def sub (a b : List LFn) : Bool := a.all fun f => b.contains f

/-- `a ⊂ b`. -/
def ssub (a b : List LFn) : Bool := sub a b && !sub b a

/-- **The edges**: strict inclusions with no named signature strictly between. -/
def edges : List (Node × Node) :=
  (nodes.flatMap fun x => nodes.map fun y => (x, y)).filter fun e =>
    ssub e.1.fns e.2.fns && !nodes.any fun z => ssub e.1.fns z.fns && ssub z.fns e.2.fns

/-- A node's line. -/
def nodeLine (n : Node) : String :=
  "  " ++ n.id ++ "[\"" ++ n.sig ++ "<br/>" ++ n.contract ++ "<br/><small>" ++
    ", ".intercalate (n.fns.map LFn.name) ++ "</small>\"]"

/-- **The diagram of contracts**, as mermaid (bottom to top: smaller signatures below). -/
def mermaid : String :=
  "graph BT\n" ++ "\n".intercalate (nodes.map nodeLine) ++ "\n" ++
    "\n".intercalate (edges.map fun e =>
      "  " ++ e.1.id ++ (if e.2.factors.contains e.1.id then " -- ⊗ --> " else " --> ") ++ e.2.id) ++
    "\n"

end Diagram

end Silmaril.Libc.Contracts
