module

public import Silmaril.Compiler.Mir.Syntax.Defs
public import Std.Data.HashMap
public import Std.Data.HashSet

/-! # Linking Mir units into one Lir program

`link L units entry` resolves every symbol of `units` and produces one `Lir.Prog Nat`
(function `i` of the link is Lir function `i`), the initial image of the linear memory
from `L.dataBase`, and the address of every data object:

1. **Functions.** All functions of all units, in order. A weak definition is dropped
   when a non-weak one of the same name exists; a symbol defined twice otherwise, or
   used and never defined, is an error. Static (non-exported) symbols must already be
   unique: front ends mangle them.
2. **Data.** Objects are placed from `L.dataBase` upwards in order, each aligned. The
   symbol `dataEndSymbol` names the first page-aligned address after the last object.
3. **Function pointers.** The pointer of function `i` is `L.funcPtrBase + 16 * i`, a
   value outside the linear memory. `callIndirect` with `n` arguments and `r` results
   becomes a call of a generated *dispatcher*, which compares the pointer with every
   address-taken function of that shape and calls it, and traps when none matches.
4. **Dead code.** Only the functions and data reachable from the first function (the
   entry) and the first data object, through calls, `addr` and relocations, are kept.
5. **Instructions.** `addr` becomes a constant, `call` a Lir call with register
   locations.

## Correctness

The registry's `Stage.link` runs `link` and the checker `Mir.LinkCheck.check`, which
`Mir.LinkCorrect.check_sound` proves sufficient for the contract `Contract.link`: the
linked program refines the independent Mir semantics `Contract.MirSem` (calls resolve
by name, `addr` gives the placed address or function pointer, the initial memory holds
every object's image with its relocations applied, and a dispatcher call with pointer
`funcPtr i` behaves as a direct call of function `i`). `link` itself is unproved; the
checker validates each result.
-/

@[expose] public section

namespace Silmaril.Compile.Mir

open Silmaril.Machine

/-- Where the link places data and function pointers. -/
structure Layout where
  /-- The address of the first data object. -/
  dataBase : Nat
  /-- Function pointers are `funcPtrBase + 16 * i`. -/
  funcPtrBase : Nat

/-- The symbol whose address is the page-aligned end of the data. -/
def dataEndSymbol : Symbol := "__mir_data_end"

/-- Link errors. -/
inductive LinkError where
  | duplicate (sym : Symbol)
  | undefined (sym : Symbol) (user : Symbol)
  | notData (sym : Symbol) (user : Symbol)
  | badReloc (object : Symbol) (offset : Nat)
  | tooManyArgs (func : Symbol) (count : Nat)
  deriving Repr, Inhabited

def LinkError.message : LinkError → String
  | .duplicate s => s!"duplicate symbol {s}"
  | .undefined s u => s!"undefined symbol {s} (used by {u})"
  | .notData s u => s!"symbol {s} is not addressable (used by {u})"
  | .badReloc o off => s!"relocation outside data object {o} at offset {off}"
  | .tooManyArgs f n => s!"call with {n} arguments in {f} (at most {maxArgs})"

/-- The result of a link. -/
structure Linked where
  prog : Lir.Prog Reg
  /-- The Lir function index of every function symbol. -/
  funcs : Std.HashMap Symbol Nat
  /-- The address of every data symbol (and of `dataEndSymbol`). -/
  data : Std.HashMap Symbol Nat
  dataBase : Nat
  /-- The page-aligned end of the data. -/
  dataEnd : Nat
  /-- The initial bytes of `[dataBase, dataEnd)`. -/
  image : ByteArray

def alignUp (n a : Nat) : Nat := if a ≤ 1 then n else (n + a - 1) / a * a

/-- Write the low `n` bytes of `v` little-endian at `off`. -/
def writeLE (b : ByteArray) (off n : Nat) (v : Nat) : ByteArray := Id.run do
  let mut b := b
  for i in [0:n] do
    b := b.set! (off + i) ((v >>> (8 * i)) % 256).toUInt8
  return b

/-- The value of a symbol inside the link: a data address or a function pointer. -/
def symbolValue (L : Layout) (funcs : Std.HashMap Symbol Nat) (data : Std.HashMap Symbol Nat)
    (sym user : Symbol) : Except LinkError Nat :=
  match data[sym]?, funcs[sym]? with
  | some a, _ => .ok a
  | none, some i => .ok (L.funcPtrBase + 16 * i)
  | none, none => .error (.undefined sym user)

/-- Symbols whose function pointer is taken. -/
def takenFunctions (units : Array Unit) : Std.HashSet Symbol := Id.run do
  let mut s : Std.HashSet Symbol := {}
  for u in units do
    for f in u.funcs do
      for b in f.blocks do
        for i in b.instrs do
          if let .addr _ sym _ := i then s := s.insert sym
    for d in u.data do
      for r in d.relocs do s := s.insert r.sym
  return s

/-- The dispatcher of indirect calls with `n` arguments and `r` results over the
candidates `cands` (Lir function index and pointer value): register 0 is the pointer,
`1 … n` the arguments. -/
def dispatcher (n r : Nat) (cands : List (Nat × Nat)) : Lir.Func Reg :=
  let args := (List.range n).map fun j => Lir.Loc.reg (j + 1)
  let res := (List.range r).map fun j => Lir.Loc.reg (n + 3 + j)
  let tmp := n + 1
  let cmp := n + 2
  let blocks := cands.zipIdx.flatMap fun ((fid, ptr), i) =>
    [ ⟨[.op (.const tmp (BitVec.ofNat 64 ptr)), .op (.binary (.cmp .eq) cmp 0 tmp)],
        .branch cmp (2 * i + 1) (2 * i + 2)⟩,
      ⟨[.call fid args res], .ret res⟩ ]
  ⟨(List.range (n + 1)).map .reg, 0, blocks ++ [⟨[], .trap⟩]⟩

/-- The functions and data objects reachable from `roots` through calls, `addr` and
relocations (what `ld --gc-sections` keeps). -/
def reachable (funcs : Array Func) (data : Array Data) (roots : List Symbol) : Std.HashSet Symbol := Id.run do
  let fmap : Std.HashMap Symbol Func := funcs.foldl (fun m f => m.insert f.name f) {}
  let dmap : Std.HashMap Symbol Data := data.foldl (fun m d => m.insert d.name d) {}
  let mut seen : Std.HashSet Symbol := {}
  let mut todo := roots
  -- every reference is pushed at most once per visited definition
  let refs := funcs.foldl (fun n f => f.blocks.foldl (fun n b => n + b.instrs.size) n) 0 +
    data.foldl (fun n d => n + d.relocs.length) 0
  let mut fuel := refs + roots.length + 1
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => fuel := 0
    | s :: rest =>
      todo := rest
      if seen.contains s then continue
      seen := seen.insert s
      if let some f := fmap[s]? then
        for b in f.blocks do
          for i in b.instrs do
            match i with
            | .addr _ t _ => todo := t :: todo
            | .call t _ _ => todo := t :: todo
            | .callIndirect .. => pure ()
            | .op _ | .fop .. => pure ()
      if let some d := dmap[s]? then
        for r in d.relocs do todo := r.sym :: todo
  return seen

/-- Link `units`. -/
def link (L : Layout) (units : Array Unit) : Except LinkError Linked := do
  let strong : Std.HashSet Symbol := units.foldl (fun s u =>
    (u.funcs.filter (!·.weak)).foldl (fun s f => s.insert f.name)
      ((u.data.filter (!·.weak)).foldl (fun s d => s.insert d.name) s)) {}
  let allFuncs := (units.flatMap (·.funcs)).filter fun f => !f.weak || !strong.contains f.name
  let allData := (units.flatMap (·.data)).filter fun d => !d.weak || !strong.contains d.name
  -- keep what the first function (the entry) and the first data object reach
  let roots := (allFuncs[0]?.map (·.name)).toList ++ (allData[0]?.map (·.name)).toList
  let live := reachable allFuncs allData roots
  let allFuncs := allFuncs.filter fun f => live.contains f.name
  let allData := allData.filter fun d => live.contains d.name
  -- function indices
  let mut funcs : Std.HashMap Symbol Nat := {}
  for f in allFuncs do
    if funcs.contains f.name then throw (.duplicate f.name)
    funcs := funcs.insert f.name funcs.size
  -- data layout
  let mut data : Std.HashMap Symbol Nat := {}
  let mut cur := L.dataBase
  for d in allData do
    if data.contains d.name || funcs.contains d.name then throw (.duplicate d.name)
    cur := alignUp cur d.align
    data := data.insert d.name cur
    cur := cur + d.size
  let dataEnd := alignUp cur 4096
  data := data.insert dataEndSymbol dataEnd
  -- image
  let mut image := ByteArray.mk (Array.replicate (dataEnd - L.dataBase) 0)
  for d in allData do
    let base := data[d.name]! - L.dataBase
    for i in [0:min d.init.size d.size] do
      image := image.set! (base + i) d.init[i]!
    for rl in d.relocs do
      if rl.offset + 8 > d.size then throw (.badReloc d.name rl.offset)
      let v ← symbolValue L funcs data rl.sym d.name
      image := writeLE image (base + rl.offset) 8 (Int.toNat ((v : Int) + rl.addend) % 2 ^ 64)
  -- dispatchers
  let taken := takenFunctions units
  let mut shapes : Array (Nat × Nat) := #[]
  for f in allFuncs do
    for b in f.blocks do
      for i in b.instrs do
        if let .callIndirect _ args res := i then
          if !shapes.contains (args.length, res.length) then shapes := shapes.push (args.length, res.length)
  let dispatchBase := allFuncs.size
  let dispatchId (n r : Nat) : Nat :=
    dispatchBase + (shapes.findIdx? (· == (n, r))).getD 0
  let dispatchers := shapes.toList.map fun (n, r) =>
    let cands := allFuncs.toList.zipIdx.filterMap fun (f, i) =>
      if taken.contains f.name && f.params.length == n && f.results == r then
        some (i, L.funcPtrBase + 16 * i) else none
    dispatcher n r cands
  -- functions
  let mut lfuncs : Array (Lir.Func Reg) := #[]
  for f in allFuncs do
    let mut blocks : Array (Lir.Block Reg) := #[]
    for b in f.blocks do
      let mut instrs : Array (Lir.Instr Reg) := #[]
      for i in b.instrs do
        match i with
        | .op o => instrs := instrs.push (.op o)
        | .fop op d x y => instrs := instrs.push (.fop op d x y)
        | .addr d sym off =>
          let v ← symbolValue L funcs data sym f.name
          instrs := instrs.push (.op (.const d (BitVec.ofNat 64 (v + off))))
        | .call callee args res =>
          if args.length > maxArgs then throw (.tooManyArgs f.name args.length)
          let some fid := funcs[callee]? | throw (.undefined callee f.name)
          instrs := instrs.push (.call fid (args.map .reg) (res.map .reg))
        | .callIndirect t args res =>
          if args.length + 1 > maxArgs then throw (.tooManyArgs f.name (args.length + 1))
          instrs := instrs.push
            (.call (dispatchId args.length res.length) ((t :: args).map .reg) (res.map .reg))
      blocks := blocks.push ⟨instrs.toList, b.term⟩
    lfuncs := lfuncs.push ⟨f.params.map .reg, 0, blocks.toList⟩
  return { prog := ⟨lfuncs.toList ++ dispatchers⟩, funcs, data, dataBase := L.dataBase, dataEnd, image }

end Silmaril.Compile.Mir
