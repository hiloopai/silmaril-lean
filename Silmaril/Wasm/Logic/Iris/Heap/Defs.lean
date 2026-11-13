module

public import Silmaril.Wasm.Logic.Iris.Language.Defs
public import Iris.BI.Lib.GenHeap
public import Iris.ProgramLogic.WeakestPre
public import Iris.Std.HeapInstances
public import Mathlib.Data.Nat.Pairing

/-!
# Ghost state for the Iris logic of Wasm Core 3.0: definitions

A Wasm 3.0 heap as iris-lean ghost state (`Iris.BI.Lib.GenHeap`): one
`genHeap` over locations `ILoc` with contents `ICell`. The locations are the
store's own addresses, so several linear memories, tables and GC objects are
separate address spaces:

* `frame`: the current frame (locals and module instance) as one cell;
* `byte m i`: byte `i` of the linear memory at address `m` (memory64 memories
  too: addresses are natural numbers);
* `mem m`: the memory type and the byte size of the memory at address `m` (what
  `memory.grow` and `memory.size` read);
* `global a`: the value of the global at address `a`;
* `tableElem t i`: entry `i` of the table at address `t`;
* `field a i`: field `i` of the GC structure at address `a`;
* `elem a i`, `arrLen a`: element `i` and the length of the GC array at
  address `a`;
* `tag a`: the exception tag at address `a` (tags never change; `throw` reads
  them).

Exception instances, functions, data and element segments are not tracked: no
instruction rule needs to own them.

`cellOf s f l` is what the store and the frame hold at `l`. The state
interpretation `wasmInterp (s, f)` owns the authoritative ghost heap `m` and
asks only that it agrees with the store where it is defined (`Sub m s f`): the
ghost heap tracks the cells somebody owns a points-to for. Steps that change
cells nobody owns keep the interpretation, and fresh cells (new GC objects, the
bytes added by `memory.grow`) are allocated in the ghost heap when they appear.

`WasmGpreS`/`WasmGS` bundle the invariant and later-credit machinery with the
heap, after `Iris.HeapLang.PrimitiveLaws` (`HeapLangGpreS`/`HeapLangGS`);
`WasmGF` is one concrete bundle of functors. `irisGS` makes Iris's weakest
precondition `WP (IExpr.run c) {{ Φ }}` available for `IExpr P host`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.Algebra _root_.Iris.ProgramLogic

variable {H : Type}

/-! ## Locations and cells -/

/-- A location of the Wasm 3.0 heap. -/
inductive ILoc where
  /-- The current frame. -/
  | frame
  /-- Byte `i` of the memory at address `m`. -/
  | byte (m i : Nat)
  /-- The type and size of the memory at address `m`. -/
  | mem (m : Nat)
  /-- The global at address `a`. -/
  | global (a : Nat)
  /-- Entry `i` of the table at address `t`. -/
  | tableElem (t i : Nat)
  /-- Field `i` of the structure at address `a`. -/
  | field (a i : Nat)
  /-- Element `i` of the array at address `a`. -/
  | elem (a i : Nat)
  /-- The length of the array at address `a`. -/
  | arrLen (a : Nat)
  /-- The tag at address `a` (read only). -/
  | tag (a : Nat)
  deriving DecidableEq

/-- An injective code of locations, to order them. -/
def ILoc.enc : ILoc → Nat
  | .frame => Nat.pair 0 0
  | .byte m i => Nat.pair 1 (Nat.pair m i)
  | .mem m => Nat.pair 2 m
  | .global a => Nat.pair 3 a
  | .tableElem t i => Nat.pair 4 (Nat.pair t i)
  | .field a i => Nat.pair 5 (Nat.pair a i)
  | .elem a i => Nat.pair 6 (Nat.pair a i)
  | .arrLen a => Nat.pair 7 a
  | .tag a => Nat.pair 8 a

theorem ILoc.enc_inj {l l' : ILoc} (h : l.enc = l'.enc) : l = l' := by
  cases l <;> cases l' <;> simp_all [ILoc.enc, Nat.pair_eq_pair]

instance : Ord ILoc where
  compare l l' := compare l.enc l'.enc

instance : Std.TransOrd ILoc where
  eq_swap {l l'} := Nat.instTransOrd.eq_swap (a := l.enc) (b := l'.enc)
  isLE_trans {l₁ l₂ l₃} := Nat.instTransOrd.isLE_trans (a := l₁.enc) (b := l₂.enc) (c := l₃.enc)

instance : Std.LawfulEqOrd ILoc where
  eq_of_compare h := ILoc.enc_inj (Std.LawfulEqOrd.eq_of_compare (α := Nat) h)

/-- The contents of a location. -/
inductive ICell where
  /-- A frame. -/
  | frame (f : Frame)
  /-- A byte. -/
  | byte (b : UInt8)
  /-- A memory's type and byte size. -/
  | mem (t : MemoryType) (size : Nat)
  /-- A value (of a global). -/
  | val (v : Val)
  /-- A reference (in a table). -/
  | ref (r : Ref)
  /-- A field of a structure or an element of an array. -/
  | field (fv : FieldVal)
  /-- A length. -/
  | len (n : Nat)
  /-- A tag. -/
  | tag (ti : TagInst)

/-- What the store and the current frame hold at a location. -/
def cellOf (s : Store H) (f : Frame) : ILoc → Option ICell
  | .frame => some (.frame f)
  | .byte m i => (s.mems[m]?.bind fun mi => mi.bytes[i]?).map .byte
  | .mem m => s.mems[m]?.map fun mi => .mem mi.type mi.bytes.size
  | .global a => s.globals[a]?.map fun g => .val g.value
  | .tableElem t i => (s.tables[t]?.bind fun ti => ti.refs[i]?).map .ref
  | .field a i => (s.structs[a]?.bind fun si => si.fields[i]?).map .field
  | .elem a i => (s.arrays[a]?.bind fun ai => ai.fields[i]?).map .field
  | .arrLen a => s.arrays[a]?.map fun ai => .len ai.fields.length
  | .tag a => s.tags[a]?.map .tag

/-- Finite maps over locations. -/
abbrev HeapF := fun V => Std.ExtTreeMap ILoc V compare

/-- A ghost heap agrees with the store and the frame where it is defined. -/
def Sub (m : HeapF ICell) (s : Store H) (f : Frame) : Prop :=
  ∀ l c, get? m l = some c → cellOf s f l = some c

/-- The store and the frame hold the cells `ps`. -/
def Cells (ps : List (ILoc × ICell)) (s : Store H) (f : Frame) : Prop :=
  ∀ p ∈ ps, cellOf s f p.1 = some p.2

/-- A change of store and frame, from `s, f` to `s', f'`, that turns the cells `ps`
into `ps'` (same locations), creates the fresh cells `qs` and keeps every other
cell. -/
structure Change (s : Store H) (f : Frame) (s' : Store H) (f' : Frame)
    (ps ps' qs : List (ILoc × ICell)) : Prop where
  /-- The updated cells are at the same locations. -/
  fst : ps.map Prod.fst = ps'.map Prod.fst
  /-- The locations are distinct. -/
  nodup : (ps'.map Prod.fst ++ qs.map Prod.fst).Nodup
  /-- The created cells are fresh. -/
  fresh : ∀ q ∈ qs, cellOf s f q.1 = none
  /-- The new cells. -/
  new : Cells (ps' ++ qs) s' f'
  /-- Every other cell is kept. -/
  old : ∀ l c, l ∉ ps.map Prod.fst → cellOf s f l = some c → cellOf s' f' l = some c

/-! ## Ghost state -/

/-- The functors needed before the ghost names are allocated. -/
class WasmGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  /-- The heap. -/
  heap_pre : genHeapPreS ILoc ICell GF HeapF

attribute [reducible, instance] WasmGpreS.heap_pre

/-- The ghost names of the logic: invariants and later credits, and the heap. -/
class WasmGS (GF : BundledGFunctors) where
  [invGS : InvGS_gen .hasLC GF]
  /-- The heap. -/
  heap : genHeapGS ILoc ICell GF HeapF

attribute [reducible, instance] WasmGS.heap

-- The invariant machinery is an instance too; `irisGS` uses the same one, so the two
-- agree definitionally.
attribute [reducible, instance] WasmGS.invGS

variable {GF : BundledGFunctors}

/-- **The state interpretation**: an authoritative ghost heap that agrees with the
store and the frame. -/
def wasmInterp [WasmGS GF] (σ : IState H) : IProp GF :=
  iprop(∃ m : HeapF ICell, ⌜Sub m σ.1 σ.2⌝ ∗ genHeapInterp m)

/-- The weakest precondition of `IExpr P host` is Iris's, with `wasmInterp` as the
state interpretation, no later credits per step and trivial fork
postconditions. -/
instance irisGS [WasmGS GF] {P : Profile} {host : HostSemantics H} :
    IrisGS_gen .hasLC (IExpr P host) GF where
  invGS := WasmGS.invGS
  toStateInterp := ⟨fun σ _ _ _ => wasmInterp σ⟩
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by
    let := @WasmGS.invGS GF _
    exact fupd_intro

/-- One concrete bundle of functors (after `Iris.HeapLang.PrimitiveLaws.HeapLangS`). -/
noncomputable def WasmGF : BundledGFunctors
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF CoPsetDisjL⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit)⟩
  | 4 => ⟨constOF (HeapView ILoc (Agree (DiscreteO ICell)) HeapF)⟩
  | 5 => ⟨constOF (HeapView ILoc (Agree (DiscreteO GName)) HeapF)⟩
  | 6 => ⟨constOF MetaUR⟩
  | _ => ⟨constOF Unit⟩

instance instWasmGpreS : WasmGpreS WasmGF where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6

/-! ## Points-to assertions -/

/-- The cells `cell x₀, cell x₁, …` at the locations `loc i, loc (i + 1), …`. -/
def idxCells {α : Type} (loc : Nat → ILoc) (cell : α → ICell) : Nat → List α → List (ILoc × ICell)
  | _, [] => []
  | i, x :: xs => (loc i, cell x) :: idxCells loc cell (i + 1) xs

section PointsTo

variable [WasmGS GF]

/-- `l ↦ c` with full ownership. -/
abbrev pts (l : ILoc) (c : ICell) : IProp GF := pointsTo l (DFrac.own 1) c

/-- Full ownership of a list of cells. -/
def ownCells : List (ILoc × ICell) → IProp GF
  | [] => iprop(emp)
  | p :: ps => iprop(pts p.1 p.2 ∗ ownCells ps)

/-- The current frame is `f`. -/
abbrev ownFrame (f : Frame) : IProp GF := pts .frame (.frame f)

/-- The bytes `bs` from address `i` of the memory at address `m`. -/
abbrev ownBytes (m i : Nat) (bs : List UInt8) : IProp GF := ownCells (idxCells (.byte m) .byte i bs)

/-- The memory at address `m` has type `t` and `size` bytes. -/
abbrev ownMem (m : Nat) (t : MemoryType) (size : Nat) : IProp GF := pts (.mem m) (.mem t size)

/-- The global at address `a` holds `v`. -/
abbrev ownGlobal (a : Nat) (v : Val) : IProp GF := pts (.global a) (.val v)

/-- Entry `i` of the table at address `t` holds `r`. -/
abbrev ownTableElem (t i : Nat) (r : Ref) : IProp GF := pts (.tableElem t i) (.ref r)

/-- The cells of a structure with the fields `fvs` (and maybe more). -/
abbrev structCells (a : Nat) (fvs : List FieldVal) : List (ILoc × ICell) :=
  idxCells (.field a) .field 0 fvs

/-- The structure at address `a` has the fields `fvs` (and maybe more). -/
abbrev ownStruct (a : Nat) (fvs : List FieldVal) : IProp GF := ownCells (structCells a fvs)

/-- The cells of an array with exactly the elements `fvs`. -/
abbrev arrayCells (a : Nat) (fvs : List FieldVal) : List (ILoc × ICell) :=
  (.arrLen a, .len fvs.length) :: idxCells (.elem a) .field 0 fvs

/-- The array at address `a` has exactly the elements `fvs`. -/
abbrev ownArray (a : Nat) (fvs : List FieldVal) : IProp GF := ownCells (arrayCells a fvs)

end PointsTo

end Silmaril.Wasm.Logic.IrisWasm
