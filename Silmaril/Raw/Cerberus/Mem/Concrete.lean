module

public import Silmaril.Cerberus.Floating.Defs
public import Silmaril.Cerberus.Mem.Defs
public import Silmaril.Cerberus.Map.Defs
public import Mathlib.Data.Finset.Sort
public import Silmaril.Cerberus.Undefined.Defs

/-! Concrete runtime state and the original signed-int byte operations at
b3e11ea3. Typed operations are in Mem.Typed. Source line citations refer to
memory/concrete/impl_mem.ml. Unsupported paths are explicit. -/

@[expose] public section
namespace Silmaril.Cerberus.Mem.Concrete

/-- Lines 104-123. This slice enables empty and allocation provenance. -/
inductive Pointer where
  | null : Ctype → Pointer
  | function : Sym → Pointer
  | allocated : Int → Int → Pointer
  | unprovenanced : Int → Pointer
  deriving Repr
noncomputable instance : DecidableEq Pointer := Classical.typeDecidableEq _

/-- Lines 126-141. Typed integers, real floats, pointers, arrays and struct members.
Unions remain outside the executable memory fragment. -/
inductive MemoryValue where
  | unspecified : Ctype → MemoryValue
  | integer : IntegerType → Int → MemoryValue
  | floating : RealFloatingType → Numeric.Ieee754.F64 → MemoryValue
  | pointer : Ctype → Pointer → MemoryValue
  | array : List MemoryValue → MemoryValue
  | struct_ : Sym → List (Identifier × Ctype × MemoryValue) → MemoryValue
  deriving Repr

noncomputable instance : DecidableEq MemoryValue := Classical.typeDecidableEq _

/-- Lines 126-141,450-467. PNVI integer values carry no provenance. -/
noncomputable abbrev model : MemoryModel where
  PointerValue := Pointer
  IntegerValue := Int
  FloatingValue := Numeric.Ieee754.F64
  MemValue := MemoryValue
  Footprint := Int × Int

/-- Lines 227-237. Writable unexposed allocations retain size and atomic status. -/
structure Allocation where
  base : Int
  size : Int := 4
  exposed : Bool := false
  atomic : Bool := false
  objectType : Option Ctype := none
  readonly : Option UndefinedBehaviour := none
  readonlyKind : UndefinedBehaviour := .UB064_modifying_const
  deriving Repr

/-- Lines 241-247. None is unspecified. State.pointerBytes retains copy metadata. -/
abbrev Byte := Option Int

/-- Lines 305-344. Finite maps index allocations by ID and bytes by address.
Unsupported iota, function-address maps, varargs, unions and requested addresses
have no enabled operations. -/
structure State where
  /-- Pinned frontend enum registrations, keyed by Lem symbol equality. -/
  enumTypes : Map Sym IntegerType := ∅
  nextId : Int := 0
  lastAddress : Int := 281474976710655
  allocations : Map Int Allocation := ∅
  bytes : Map Int Byte := ∅
  dead : List Int := []
  lastUsed : Option Int := none
  pointerBytes : Map Int (Option Int × Nat) := ∅
  functions : Map Int Sym := ∅
  stdout : String := ""
  nextExcluded : Nat := 0
  /-- Sequential driver diagnostic location, core_run.lem:758-769. -/
  currentLocation : Loc := .unknown

/-- Lines 358-370. Failures remain labelled rather than raising host exceptions. -/
inductive Failure where
  | unsupported : String → Failure
  | invalid : String → Failure
  | ub : UndefinedBehaviour → Failure
  deriving DecidableEq, Repr

/-- Lines 26-51, 96-98. Only the pinned signed-int layout is enabled. -/
def signedInt : Ctype → Bool
  | .mk _ (.basic (.integer (.signed .int))) => true
  | _ => false

/-- Lines 96-98. The implementation's sizeof/alignof are both four here. -/
def layout (ty : Ctype) : Except Failure Int :=
  if signedInt ty then .ok 4 else .error (.unsupported "layout outside signed int")

/-- Lines 531-561. Missing or unspecified bytes read as unspecified. -/
def readByte (addr : Int) (xs : Map Int Byte) : Byte :=
  (xs.lookup addr).getD none

/-- Lines 531-561,1506-1517. Replace the byte at its address. -/
def writeByte (addr : Int) (b : Byte) (xs : Map Int Byte) : Map Int Byte :=
  xs.insert addr b

/-- Lines 584-633,1948-1987. The PNVI-ae-udi exposed allocation search
includes one-past addresses. Ambiguous results require symbolic iota state. -/
def addressPointer (allocs : Map Int Allocation) (dead : List Int)
    (refTy : Ctype) (n : Int) : Except Failure Pointer := do
  if n == 0 then return .null refTy
  let eligible := ((show Finset Int from allocs.keys).sort (· ≤ ·)).filter fun id =>
    (allocs.lookup id).any fun a => a.exposed &&
      ((!(id ∈ dead) && a.base ≤ n && n < a.base+a.size) || n == a.base+a.size)
  match eligible with
  | [] => pure (.unprovenanced n)
  | [id] => pure (.allocated id n)
  | _ => throw (.unsupported "PNVI-ae-udi symbolic provenance from ambiguous exposure")

/-- Lines 918-936, 962-973. Little-endian integer representation. -/
def reprInt (n : Int) : List Byte :=
  [some (n % 256), some (n / 256 % 256), some (n / 65536 % 256), some (n / 16777216 % 256)]

/-- Lines 531-561, 1506-1517. Overwrite four consecutive bytes. -/
def writeInt (addr : Int) (bs : List Byte) (xs : Map Int Byte) : Map Int Byte :=
  match bs with
  | [] => xs
  | b :: rest => writeByte addr b (writeInt (addr + 1) rest xs)

/-- Lines 562-579, 768-783. Unspecified bytes give an unspecified integer. -/
def readInt (addr : Int) (xs : Map Int Byte) : Option Int := do
  let a ← readByte addr xs
  let b ← readByte (addr + 1) xs
  let c ← readByte (addr + 2) xs
  let d ← readByte (addr + 3) xs
  let u := a + 256*b + 65536*c + 16777216*d
  pure (if u ≥ 2147483648 then u - 4294967296 else u)

/-- Lines 1069-1090. Descending allocation rounded down to alignment. -/
def allocationBase (s : State) (align : Int) : Int :=
  let z := s.lastAddress - 4
  z - z % align

/-- Lines 1111-1170. No requested address, initializer or zero-init switch. -/
def allocate (s : State) (align : Int) (ty : Ctype) : Except Failure (Pointer × State) := do
  let _ ← layout ty
  if align ≤ 0 then throw (.invalid "nonpositive allocation alignment")
  let addr := allocationBase s align
  if addr ≤ 0 then throw (.invalid "allocation exhausted")
  let p := Pointer.allocated s.nextId addr
  pure (p, {s with
    nextId := s.nextId + 1, lastAddress := addr,
    allocations := s.allocations.insert s.nextId {base := addr},
    bytes := writeInt addr [none, none, none, none] s.bytes,
    lastUsed := some s.nextId})

/-- Lines 496-514, 1443-1485, 1580-1610. Whole signed-int footprints only. -/
def access (s : State) (ty : Ctype) (p : Pointer) : Except Failure (Int × Int) := do
  let _ ← layout ty
  match p with
  | .unprovenanced _ => throw (.unsupported "unprovenanced object access")
  | .function _ => throw (.unsupported "function pointer object access")
  | .null _ => throw (.unsupported "null pointer access UB mapping")
  | .allocated id addr =>
      if id ∈ s.dead then throw (.unsupported "dead pointer access UB mapping")
      let some alloc := s.allocations.lookup id
        | throw (.unsupported "outside allocation lifetime UB mapping")
      if alloc.base != addr then throw (.unsupported "partial object access")
      pure (id, addr)

/-- Lines 1490-1610. NA, nonlocking, writable whole-int store. -/
def store (s : State) (ty : Ctype) (p : Pointer) (n : Option Int) : Except Failure ((Int × Int) × State) := do
  let (id, addr) ← access s ty p
  let bs ← match n with
    | none => pure [none, none, none, none]
    | some n =>
        if -2147483648 ≤ n ∧ n ≤ 2147483647 then pure (reprInt n)
        else throw (.invalid "integer representation out of range")
  pure ((addr, 4), {s with bytes := writeInt addr bs s.bytes, lastUsed := some id})

/-- Lines 1375-1485. Default non-strict reads preserve unspecified values. -/
def load (s : State) (ty : Ctype) (p : Pointer) : Except Failure (Option Int × State) := do
  let (id, addr) ← access s ty p
  pure (readInt addr s.bytes, {s with lastUsed := some id})

/-- Lines 1287-1373. Static kill at the allocation base; byte map is retained. -/
def kill (s : State) (ty : Ctype) (p : Pointer) : Except Failure (Unit × State) := do
  let (id, _) ← access s ty p
  pure ((), {s with
    allocations := s.allocations.erase id,
    dead := id :: s.dead, lastUsed := some id})

end Silmaril.Cerberus.Mem.Concrete
