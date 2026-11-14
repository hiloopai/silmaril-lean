module

public import Silmaril.Compiler.Contract.Defs
/-! # A checker for the link

`LinkCheck.check L base us l` decides, for units `us` and the result `l` of linking them
(`Mir.link L us`), the facts that make `l` refine the independent Mir semantics
`Contract.MirSem` (`Silmaril/Compile/Contract.lean`, contract `link`). It does not
re-run the link: it reads `l` against the definitions in force (`MirSem.funcDefs`,
`MirSem.dataDefs`), under the placement `place L l` (the link's data addresses and
function pointers):

* **functions**: every function `n ↦ j` of `l.funcs` has exactly one definition `f` in
  force, no data object of its name, a pointer below `2 ^ 64`, and Lir function `j` is
  `f` with every `addr` replaced by the value of its symbol (`MirSem.symValue`), every
  `call` by a call of the function index of its callee, and every `callIndirect` by a
  call of a *dispatcher* of its shape (`Mir.dispatcher`) whose candidates are
  pointer-correct and include every address-taken function of that shape;
* **entry**: the first function in force is Lir function 0;
* **data**: every placed object is inside the image, aligned, below the end of the data,
  with a unique name, disjoint from the others, and every symbol it relocates has a
  value; the image is exactly the bytes of the placed objects (`MirSem.objectByte`) and
  zeros elsewhere;
* the reserved symbol `MirSem.heapSymbol` has no definition, and the data end fits
  `MirSem.need`.

`Silmaril.Compile.Mir.LinkCorrect` proves that a link that passes the check satisfies
the contract; the registry's `Stage.link` runs `Mir.link` and rejects what fails the
check. Each check is a direct reading of a fact the proof needs; the costs are linear in
the program, except the lookups of definitions by name (linear in the number of
definitions) and the pairwise disjointness of placed objects (quadratic in their
number). -/

@[expose] public section

namespace Silmaril.Compile.Mir.LinkCheck

open Silmaril.Machine
open Silmaril.Compile.Contract

/-- The placement a link realises: its data addresses (the reserved heap symbol is not
an object), its function pointers, and its data end. -/
def place (L : Layout) (l : Linked) : MirSem.Placement where
  data s := if s = MirSem.heapSymbol then none else l.data[s]?
  func s := l.funcs[s]?.map fun i => L.funcPtrBase + 16 * i
  heap := l.dataEnd

/-- `MirSem.funcOf` over precomputed definitions. -/
def funcOf (fs : List Func) (n : String) : Option Func := fs.find? (·.name == n)

/-- `MirSem.dataOf` over precomputed definitions. -/
def dataOf (ds : List Data) (n : String) : Option Data := ds.find? (·.name == n)

/-- `MirSem.symValue` over precomputed definitions. -/
def symValue (fs : List Func) (ds : List Data) (P : MirSem.Placement) (s : String) : Option Nat :=
  if s = MirSem.heapSymbol then some P.heap else
  match dataOf ds s with
  | some _ => P.data s
  | none => if (funcOf fs s).isSome then P.func s else none

/-! ## Functions and dispatchers -/

/-- The candidates `(function index, pointer)` of a dispatcher's blocks, read back. The
check compares the function with `Mir.dispatcher` of what is read, so a misreading
only rejects. -/
def candsOf : List (Lir.Block Nat) → List (Nat × Nat)
  | b₁ :: b₂ :: rest =>
    let ptr := match b₁.instrs with
      | [.op (.const _ v), _] => v.toNat
      | _ => 0
    let fid := match b₂.instrs with
      | [.call f _ _] => f
      | _ => 0
    (fid, ptr) :: candsOf rest
  | _ => []

/-- The symbols whose address is taken (`addr` or a relocation), as `MirSem.taken`. -/
def takenNames (us : Array Mir.Unit) : List String :=
  us.toList.flatMap fun u =>
    (u.funcs.toList.flatMap fun f => f.blocks.toList.flatMap fun b =>
      b.instrs.toList.filterMap fun
        | .addr _ s _ => some s
        | _ => none) ++
    u.data.toList.flatMap fun d => d.relocs.map (·.sym)

/-- The linked functions whose address is taken: index, parameter and result counts. -/
def takenLive (fs : List Func) (l : Linked) (taken : Std.HashSet String) :
    List (Nat × Nat × Nat) :=
  l.funcs.toList.filterMap fun (g, i) =>
    if taken.contains g then (funcOf fs g).map fun f => (i, f.params.length, f.results)
    else none

/-- Lir function `k` is a dispatcher for `n` arguments and `r` results whose candidates
have the link's pointers and include every address-taken function of that shape. -/
def dispOK (L : Layout) (l : Linked) (tl : List (Nat × Nat × Nat)) (k n r : Nat) : Bool :=
  match l.prog.funcs[k]? with
  | none => false
  | some fn =>
    let cands := candsOf fn.blocks
    decide (fn = dispatcher n r cands) &&
    cands.all (fun c => c.2 == L.funcPtrBase + 16 * c.1 && decide (c.2 < 2 ^ 64)) &&
    tl.all fun t => !(t.2.1 == n && t.2.2 == r) || decide ((t.1, L.funcPtrBase + 16 * t.1) ∈ cands)

/-- A Mir instruction and the Lir instruction the link made of it. -/
def instrOK (fs : List Func) (ds : List Data) (P : MirSem.Placement) (l : Linked)
    (disp : Nat → Nat → Nat → Bool) : Instr × Lir.Instr Nat → Bool
  | (.op o, li) => decide (li = .op o)
  | (.fop op d x y, li) => decide (li = .fop op d x y)
  | (.addr d s off, li) =>
    match symValue fs ds P s with
    | some v => decide (li = .op (.const d (BitVec.ofNat 64 (v + off))))
    | none => false
  | (.call c args res, li) =>
    match l.funcs[c]? with
    | some j => decide (li = .call j (args.map .reg) (res.map .reg))
    | none => false
  | (.callIndirect t args res, li) =>
    match li with
    | .call k a r => decide (a = (t :: args).map .reg) && decide (r = res.map .reg) &&
        disp k args.length res.length
    | _ => false

/-- A Mir block and its Lir block. -/
def blockOK (iok : Instr × Lir.Instr Nat → Bool) (p : Block × Lir.Block Nat) : Bool :=
  decide (p.2.term = p.1.term) && p.2.instrs.length == p.1.instrs.size &&
    (p.1.instrs.toList.zip p.2.instrs).all iok

/-- A Mir function and its Lir function. -/
def funcOK (iok : Instr × Lir.Instr Nat → Bool) (f : Func) (lf : Lir.Func Nat) : Bool :=
  decide (lf.params = f.params.map .reg) && lf.entry == 0 && lf.blocks.length == f.blocks.size &&
    (f.blocks.toList.zip lf.blocks).all (blockOK iok)

/-- An entry `n ↦ j` of the link's function table. -/
def funcEntryOK (L : Layout) (fs : List Func) (ds : List Data) (l : Linked)
    (iok : Instr × Lir.Instr Nat → Bool) (n : String) (j : Nat) : Bool :=
  n != MirSem.heapSymbol && (dataOf ds n).isNone && decide (0 < L.funcPtrBase + 16 * j) &&
    decide (L.funcPtrBase + 16 * j < 2 ^ 64) &&
    match fs.filter (·.name == n), l.prog.funcs[j]? with
    | [f], some lf => funcOK iok f lf
    | _, _ => false

/-! ## Data and the image -/

/-- An entry `n` of the link's data table: a data object and no function, whose
relocated symbols have values. -/
def dataEntryOK (fs : List Func) (ds : List Data) (P : MirSem.Placement) (n : String) : Bool :=
  n == MirSem.heapSymbol || ((funcOf fs n).isNone &&
    match dataOf ds n with
    | some d => d.relocs.all fun r => (symValue fs ds P r.sym).isSome
    | none => false)

/-- The placed objects and their addresses. -/
def placed (ds : List Data) (P : MirSem.Placement) : List (Data × Nat) :=
  ds.filterMap fun d => (P.data d.name).map (d, ·)

/-- A placed object is valid and inside the image. -/
def placedOK (l : Linked) (P : MirSem.Placement) (x : Data × Nat) : Bool :=
  decide (0 < x.2) && decide (x.2 + x.1.size ≤ P.heap) &&
    (decide (x.1.align ≤ 1) || x.2 % x.1.align == 0) && decide (l.dataBase ≤ x.2) &&
    decide (x.2 + x.1.size ≤ l.dataBase + l.image.size)

/-- Two placed objects have different names and do not overlap. -/
def disjoint (x y : Data × Nat) : Bool :=
  x.1.name != y.1.name && (decide (x.2 + x.1.size ≤ y.2) || decide (y.2 + y.1.size ≤ x.2))

/-- The bytes of one relocation's value. -/
def relocWord (fs : List Func) (ds : List Data) (P : MirSem.Placement) (r : Reloc) : BitVec 64 :=
  BitVec.ofNat 64 (Int.toNat (((symValue fs ds P r.sym).getD 0 : Int) + r.addend))

/-- The initial bytes of an object (`MirSem.objectByte`), as an array of its size. -/
def objectBytes (fs : List Func) (ds : List Data) (P : MirSem.Placement) (d : Data) :
    Array (BitVec 8) :=
  d.relocs.foldl (fun arr r =>
      (List.range 8).foldl (fun arr i =>
        arr.setIfInBounds (r.offset + i) (LittleEndian.wordByte (relocWord fs ds P r) i)) arr)
    (Array.ofFn (n := d.size) fun j =>
      if h : j.1 < d.init.size then BitVec.ofNat 8 d.init[j.1].toNat else 0)

/-- Write the bytes `bs` of an object of `size` bytes at offset `off`. -/
def writeObject (img : Array (BitVec 8)) (off size : Nat) (bs : Array (BitVec 8)) :
    Array (BitVec 8) :=
  Nat.fold size (fun j _ img => img.setIfInBounds (off + j) (bs[j]?.getD 0)) img

/-- The image the placement implies: each placed object's bytes, zeros elsewhere. -/
def expectedImage (fs : List Func) (ds : List Data) (P : MirSem.Placement) (l : Linked) :
    Array (BitVec 8) :=
  (placed ds P).foldl (fun img x => writeObject img (x.2 - l.dataBase) x.1.size (objectBytes fs ds P x.1))
    (Array.replicate l.image.size 0)

/-! ## The check -/

/-- **The link check**: `l`, the link of `us` under the layout `L` with data from
`base`, refines `MirSem` (`Mir.LinkCorrect.check_sound`). -/
def check (L : Layout) (base : Nat) (us : Array Mir.Unit) (l : Linked) : Bool :=
  let fs := MirSem.funcDefs us
  let ds := MirSem.dataDefs us
  let P := place L l
  let tl := takenLive fs l (Std.HashSet.ofList (takenNames us))
  let iok := instrOK fs ds P l (dispOK L l tl)
  (funcOf fs MirSem.heapSymbol).isNone && (dataOf ds MirSem.heapSymbol).isNone &&
    (match fs.head? with
      | some f => l.funcs[f.name]? == some 0
      | none => true) &&
    l.funcs.toList.all (fun e => funcEntryOK L fs ds l iok e.1 e.2) &&
    decide (l.funcs.toList.map (·.2)).Nodup &&
    l.data.toList.all (fun e => dataEntryOK fs ds P e.1) &&
    (placed ds P).all (placedOK l P) &&
    decide ((placed ds P).Pairwise fun x y => disjoint x y = true) &&
    decide (l.dataEnd ≤ MirSem.need us base) &&
    let img := expectedImage fs ds P l
    Nat.all l.image.size fun i h => img[i]? == some (BitVec.ofNat 8 (l.image[i]'h).toNat)

end Silmaril.Compile.Mir.LinkCheck
