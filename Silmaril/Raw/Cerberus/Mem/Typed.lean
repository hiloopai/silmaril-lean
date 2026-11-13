module

public import Silmaril.Cerberus.Mem.Layout.Defs

/-! Typed concrete memory. References are to impl_mem.ml at b3e11ea3.
Pointer copy offsets preserve PNVI-ae-udi provenance. Invalid copy sequences
use the exposed-allocation search; ambiguous iota state remains unsupported. -/

@[expose] public section
namespace Silmaril.Cerberus.Mem.Concrete

/-- Lines 918-936. Least significant byte first, without padding bits. -/
def encodeInteger : Nat → Int → List Byte
  | 0, _ => []
  | n+1, value => some (value % 256) :: encodeInteger n (value / 256)

/-- Lines 562-579. Unsigned abstraction, before sign extension. -/
def decodeInteger : List Byte → Option Int
  | [] => some 0
  | b :: bs => do pure ((← b) + 256 * (← decodeInteger bs))

/-- Lines 919-935,974-978. Eight raw binary64 bytes, with no provenance. -/
def encodeFloating (x : Numeric.Ieee754.F64) : List Byte :=
  encodeInteger 8 x.bits.toNat

/-- Lines 562-580,797-807. Unspecified bytes give an unspecified float. -/
def decodeFloating (bs : List Byte) : Option Numeric.Ieee754.F64 :=
  (decodeInteger bs).map fun n => ⟨UInt64.ofNat n.toNat⟩

def fetchBytes : Nat → Int → Map Int Byte → List Byte
  | 0, _, _ => []
  | n+1, a, xs => readByte a xs :: fetchBytes n (a+1) xs

/-- Lines 918-936,1012-1019. Pointer addresses must fit eight unsigned bytes. -/
def encodeAddress (addr : Int) : Except Failure (List Byte) :=
  if 0 ≤ addr ∧ addr < 18446744073709551616 then .ok (encodeInteger 8 addr)
  else .error (.invalid "pointer representation out of range")

/-- Lines 918-936. Representation bounds use signedness and storage width,
independently of min_ival/max_ival's wchar/wint special cases. -/
def representationBounds (w : Nat) (signed : Bool) : Int × Int :=
  let modulus : Int := 256 ^ w
  if signed then (-modulus / 2, modulus / 2 - 1) else (0, modulus - 1)

abbrev Representation := List (Byte × Option (Option Int × Nat))

/-- Lines 241-278,1506-1517. Every overwritten byte replaces copy metadata too. -/
def writeRepresentation : Int → Representation → State → State
  | _, [], s => s
  | a, (b, prov) :: bs, s =>
      let s := writeRepresentation (a+1) bs s
      {s with
        bytes := writeByte a b s.bytes,
        pointerBytes := (match prov with
          | none => s.pointerBytes.erase a
          | some pr => s.pointerBytes.insert a pr)}

def plainBytes (bs : List Byte) : Representation := bs.map (·, none)

/-- Function-byte representation registers named functions by numeric symbol ID. -/
def registerFunction (s : State) (sym : Sym) : State :=
  match sym with
  | .mk _ n (.id _) => {s with functions := s.functions.insert n sym}
  | _ => s

/-- Lines 980-1019. Pointer representation records copy offsets or a function registry entry. -/
def representPointer (p : Pointer) (s : State) : Except Failure (Representation × State) := do
  match p with
  | .null _ => pure (plainBytes (encodeInteger 8 0), s)
  | .allocated id addr =>
      let bs ← encodeAddress addr
      pure (bs.zipIdx |>.map (fun (b, i) => (b, some (some id, i))), s)
  | .unprovenanced addr =>
      let bs ← encodeAddress addr
      pure (bs.zipIdx |>.map (fun (b, i) => (b, some (none, i))), s)
  | .function sym@(.mk _ n _) =>
      let bs ← encodeAddress n
      pure (plainBytes bs, registerFunction s sym)

/-- Lines 962-1037. Aggregate representation leaves all padding unspecified. -/
def represent : Nat → Tags → MemoryValue → State → Except Failure (Representation × State)
  | 0, _, _, _ => .error (.unsupported "representation fuel")
  | fuel+1, tags, value, s => do
      match value with
      | .unspecified t =>
          let l ← typeLayout 64 tags t
          pure (plainBytes (List.replicate l.size.toNat none), s)
      | .integer ty n =>
          let some (w, signed) := registeredIntegerLayout tags ty | throw (.unsupported "integer representation")
          let (lo, hi) := representationBounds w signed
          if lo ≤ n ∧ n ≤ hi then pure (plainBytes (encodeInteger w n), s)
          else throw (.invalid "integer representation out of range")
      | .floating _ x => pure (plainBytes (encodeFloating x), s)
      | .pointer _ p => representPointer p s
      | .array xs =>
          xs.foldlM (fun (acc, s) x => do
            let (bs, s) ← represent fuel tags x s
            pure (acc ++ bs, s)) ([], s)
      | .struct_ sym xs =>
          let l ← typeLayout 64 tags (.mk [] (.struct sym))
          if xs.length != l.members.length then throw (.invalid "struct member count mismatch")
          let (bs, finish, s) ← (l.members.zip xs).foldlM (fun (acc, finish, s) ((_, _, off), (_, _, value)) => do
            let (bs, s) ← represent fuel tags value s
            pure (acc ++ plainBytes (List.replicate (off-finish).toNat none) ++ bs,
              off + bs.length, s)) ([], 0, s)
          pure (bs ++ plainBytes (List.replicate (l.size-finish).toNat none), s)

/-- Lines 807-877. Only an intact pointer-copy sequence carries allocation
provenance without exposure. Zero bytes always abstract to a null pointer. -/
def abstractPointer (s : State) (refTy : Ctype) (addr n : Int) : Except Failure Pointer := do
  if n == 0 then pure (.null refTy)
  else match refTy with
    | .mk _ (.function _ _ _) =>
        if (List.range 8).any (fun i => (s.pointerBytes.lookup (addr+i)).any (·.1.isSome)) then
          throw (.unsupported "function pointer bytes with allocation provenance")
        let some sym := s.functions.lookup n
          | throw (.unsupported "unknown function pointer representation")
        pure (.function sym)
    | _ =>
        let some (id, _) := s.pointerBytes.lookup addr
          | addressPointer s.allocations s.dead refTy n
        if (List.range 8).all (fun i =>
            s.pointerBytes.lookup (addr + i) == some (id, i)) then
          pure (match id with | some id => .allocated id n | none => .unprovenanced n)
        else addressPointer s.allocations s.dead refTy n

/-- Lines 768-914. Arrays and structs abstract their members independently. -/
def abstractValue : Nat → Tags → State → Ctype → Int → Except Failure MemoryValue
  | 0, _, _, _, _ => .error (.unsupported "abstraction fuel")
  | fuel+1, tags, s, t@(.mk _ ty), addr => do
      let l ← typeLayout 64 tags t
      match ty with
      | .basic (.integer _) | .byte =>
          let ity := match ty with | .basic (.integer i) => i | _ => .unsigned .ichar
          let some (_, signed) := registeredIntegerLayout tags ity | throw (.unsupported "integer abstraction")
          match decodeInteger (fetchBytes l.size.toNat addr s.bytes) with
          | none => pure (.unspecified t)
          | some n =>
              let modulus : Int := 256 ^ l.size.toNat
              pure (.integer ity (if signed && n ≥ modulus / 2 then n-modulus else n))
      | .basic (.floating (.realFloating fty)) =>
          match decodeFloating (fetchBytes 8 addr s.bytes) with
          | none => pure (.unspecified t)
          | some x => pure (.floating fty x)
      | .pointer _ refTy =>
          match decodeInteger (fetchBytes 8 addr s.bytes) with
          | none => pure (.unspecified t)
          | some n => pure (.pointer refTy (← abstractPointer s refTy addr n))
      | .array elem (some n) =>
          let e ← typeLayout 64 tags elem
          pure (.array (← (List.range n.toNat).mapM (fun (i : Nat) => abstractValue fuel tags s elem (addr+(i : Int)*e.size))))
      | .struct sym =>
          pure (.struct_ sym (← l.members.mapM (fun (name, ty, off) => do
            pure (name, ty, ← abstractValue fuel tags s ty (addr+off)))))
      | .atomic elem => abstractValue fuel tags s elem addr
      | _ => throw (.unsupported "typed abstraction")

/-- Lines 1069-1170. Allocation size and alignment come from the requested type. -/
def allocateTyped (tags : Tags) (s : State) (align : Int) (ty : Ctype) : Except Failure (Pointer × State) := do
  let l ← typeLayout 64 tags ty
  if align ≤ 0 then throw (.invalid "nonpositive allocation alignment")
  let z := s.lastAddress - l.size
  let addr := z - z % align
  if addr ≤ 0 then throw (.invalid "allocation exhausted")
  let s := writeRepresentation addr (plainBytes (List.replicate l.size.toNat none)) s
  pure (.allocated s.nextId addr, {s with
    nextId := s.nextId+1, lastAddress := addr,
    allocations := s.allocations.insert s.nextId {base := addr, size := l.size, objectType := some ty, atomic := match ty with | .mk _ (.atomic _) => true | _ => false}, lastUsed := some s.nextId})

/-- integerType.lem: enum equality compares symbol keys. -/
def integerTypeEqual : IntegerType → IntegerType → Bool
  | .enum a, .enum b => a.key == b.key
  | a, b => a == b

/-- ctype.lem:134-178. The enabled atomic whole-object types ignore annotations.
Other atomic types stop before equality is needed. -/
def atomicTypeEqual : Ctype → Ctype → Option Bool
  | .mk _ (.atomic a), .mk _ (.atomic b) => match a, b with
      | .mk _ (.basic (.integer a)), .mk _ (.basic (.integer b)) => some (integerTypeEqual a b)
      | .mk _ (.basic (.floating (.realFloating a))),
        .mk _ (.basic (.floating (.realFloating b))) => some (decide (a = b))
      | .mk _ (.struct a), .mk _ (.struct b) => some (a.key == b.key)
      | .mk _ (.union a), .mk _ (.union b) => some (a.key == b.key)
      | .mk _ (.pointer _ _), .mk _ (.pointer _ _) => some true
      | _, _ => none
  | .mk _ (.atomic _), _ => some false
  | _, _ => none

def unatomic : Ctype → Ctype
  | .mk _ (.atomic ty) => ty
  | ty => ty

/-- impl_mem.ml:513-529. Atomic member access has UB042; exact whole-object
access retains the allocation type, base and size. -/
def checkAtomic (a : Allocation) (ty : Ctype) (addr size : Int) : Except Failure Unit := do
  if a.atomic then
    let some allocated := a.objectType | throw (.unsupported "atomic allocation type")
    let some equal := atomicTypeEqual allocated ty | throw (.unsupported "atomic whole-object type equality")
    if !(equal && addr == a.base && size == a.size) then
      throw (.ub .UB042_access_atomic_structUnion_member)
  pure ()

/-- Lines 496-514,1443-1485,1580-1610. Interior member and array accesses
use the requested type's footprint, bounded by the containing allocation. -/
def accessTyped (tags : Tags) (s : State) (ty : Ctype) (p : Pointer) : Except Failure (Int × Int × Int) := do
  let l ← typeLayout 64 tags ty
  match p with
  | .allocated id addr =>
      if id ∈ s.dead then throw (.unsupported "dead pointer access UB mapping")
      let some a := s.allocations.lookup id
        | throw (.unsupported "outside allocation lifetime UB mapping")
      if a.base ≤ addr ∧ addr + l.size ≤ a.base+a.size then
        let _ ← checkAtomic a ty addr l.size
        pure (id, addr, l.size)
      else throw (.unsupported "out of bounds access UB mapping")
  | _ => throw (.unsupported "null or function object access UB mapping")

/-- Lines 1590-1597. Read-only status is checked before representation writes. -/
def checkWritable (s : State) (id : Int) : Except Failure Unit := do
  let some a := s.allocations.lookup id | throw (.unsupported "store allocation")
  if let some kind := a.readonly then throw (.ub kind)
  pure ()

/-- Lines 1490-1610. Typed NA store, with exact member/pointer bytes. -/
def storeTyped (tags : Tags) (s : State) (ty : Ctype) (p : Pointer) (v : MemoryValue) : Except Failure ((Int × Int) × State) := do
  let (id, addr, size) ← accessTyped tags s ty p
  let _ ← checkWritable s id
  let (bs, s) ← represent 64 tags v s
  if bs.length != size.toNat then throw (.invalid "store representation size mismatch")
  pure ((addr, size), {(writeRepresentation addr bs s) with lastUsed := some id})

/-- impl_mem.ml:286-304,676-688,777-797,1382-1391. Integer reads of
pointer representation bytes expose every allocation mentioned by those bytes.
Pointer reads themselves do not expose, and aggregates merge only member taint. -/
def exposeReadBytes (s : State) (addr : Int) (size : Nat) : State :=
  (List.range size).foldl (fun s i =>
    match (s.pointerBytes.lookup (addr+i)).bind (·.1) with
    | none => s
    | some id => match s.allocations.lookup id with
        | none => s
        | some a => {s with allocations := s.allocations.insert id {a with exposed := true}}) s

def exposeRead : Nat → Tags → State → Ctype → Int → State
  | 0, _, s, _, _ => s
  | fuel+1, tags, s, .mk _ ty, addr =>
      match ty with
      | .basic (.integer ity) =>
          match registeredIntegerLayout tags ity with
          | some (w, _) => exposeReadBytes s addr w
          | none => s
      | .byte => exposeReadBytes s addr 1
      | .array elem (some count) =>
          match typeLayout 64 tags elem with
          | .error _ => s
          | .ok layout => (List.range count.toNat).foldl
              (fun s i => exposeRead fuel tags s elem (addr + (i : Int)*layout.size)) s
      | .struct sym =>
          match typeLayout 64 tags (.mk [] (.struct sym)) with
          | .error _ => s
          | .ok layout => layout.members.foldl
              (fun s (_, ty, off) => exposeRead fuel tags s ty (addr+off)) s
      | .atomic elem => exposeRead fuel tags s elem addr
      | _ => s

/-- Lines 1375-1485. Default reads preserve unspecified subobjects. -/
def loadTyped (tags : Tags) (s : State) (ty : Ctype) (p : Pointer) : Except Failure (MemoryValue × State) := do
  let (id, addr, _) ← accessTyped tags s ty p
  let value ← abstractValue 64 tags s ty addr
  pure (value, {exposeRead 64 tags s ty addr with lastUsed := some id})

/-- Update the allocation identified by the last successful memory access. -/
def updateLastAllocation (s : State) (f : Allocation → Allocation) : State :=
  match s.lastUsed with
  | none => s
  | some id => match s.allocations.lookup id with
      | none => s
      | some a => {s with allocations := s.allocations.insert id (f a)}

/-- Lines 1129-1168,1527-1533. The allocation prefix chooses the read-only UB. -/
def readonlyKind : Prefix → UndefinedBehaviour
  | .stringLiteral _ _ => .UB033_modifying_string_literal
  | .temporaryLifetime _ _ => .UB_modifying_temporary_lifetime
  | _ => .UB064_modifying_const

/-- Lines 1148-1168. Initialized allocation is read-only from creation. -/
def createReadOnly (tags : Tags) (s : State) (align : Int) (ty : Ctype)
    (v : MemoryValue) (pref : Prefix) : Except Failure (Pointer × State) := do
  let (p, s) ← allocateTyped tags s align ty
  let (_, s) ← storeTyped tags s ty p v
  let kind := readonlyKind pref
  pure (p, updateLastAllocation s fun a => {a with readonly := some kind, readonlyKind := kind})

/-- Lines 1586-1608. A locking store makes the entire allocation read-only. -/
def storeLocking (tags : Tags) (s : State) (ty : Ctype) (p : Pointer)
    (v : MemoryValue) (locking : Bool) : Except Failure ((Int × Int) × State) := do
  let (fp, s) ← storeTyped tags s ty p v
  pure (fp, if locking then updateLastAllocation s (fun a => {a with readonly := some a.readonlyKind}) else s)

/-- Lines 1287-1373. Static kill requires the allocation's base. -/
def killTyped (tags : Tags) (s : State) (ty : Ctype) (p : Pointer) : Except Failure (Unit × State) := do
  let (id, addr, _) ← accessTyped tags s ty p
  let some a := s.allocations.lookup id | throw (.unsupported "kill allocation")
  if a.base != addr then throw (.unsupported "kill interior pointer")
  pure ((), {s with
    allocations := s.allocations.erase id,
    dead := id :: s.dead, lastUsed := some id})

end Silmaril.Cerberus.Mem.Concrete
