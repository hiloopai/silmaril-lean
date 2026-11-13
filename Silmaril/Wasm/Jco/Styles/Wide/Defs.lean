module

public import Silmaril.Wasm.Jco.Styles.XAdaptor.Defs
public import Silmaril.Wasm.Jco.Meta.Defs
public import Silmaril.Wasm.Jco.Wrap.Defs

/-!
# Wide results: multi-value against the canonical return pointer

`Sig.Ok` of the first fragment excludes memory-free results that flatten to more than
`MAX_FLAT_RESULTS = 1` core value. The canonical ABI returns such a result **through memory**:
the callee returns one `i32` pointer `rp`, and `lift_flat_values` (`definitions.py`, `a25fc0b`)
traps unless `rp` is aligned to the result's alignment and `rp + size` is in bounds, then
`load`s the value at `rp`.

The fragment here is a **record (or tuple) of at least two scalars** (`bool`, integers, floats,
`char`). Its layout follows `alignment`/`elem_size`/`load` of the reference: the alignment of a
scalar is its size, fields are placed at increasing offsets aligned to their size, and the
record's size is the end rounded up to the largest alignment. A `bool` is loaded as `byte ≠ 0`,
a `char` is checked as a Unicode scalar value. NaN canonicalisation of floats is not modelled.
Nested records and variants inside wide results are not covered.

* `wideOf r`: the fields and sizes of a wide result.
* `liftResultW`, `canonCallW`: `canon lift` with wide results (and the first fragment
  otherwise).
* **The multi-value style** (FFI style 5): the core function returns the flat values of the
  result directly, as a multi-value function (`Meta.specCallMV`, with the C convention for the
  parameters). Its wrapper `wrapW md` adds, for each world function with a wide result, an export
  shim (`mvShim`). The shim calls the function, pops its results into locals, allocates the
  result block with `alloc(size, align)`, stores each field (normalising a `bool` with
  `i32.eqz; i32.eqz`) and returns the pointer. Other functions keep the export shims of `wrap`.
* `MemLawful M`: the instance's memory behaves as a memory (reading back what was set, and a
  second set overriding the first). The roundtrip needs it; `CoreInst` does not require it.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy Val charOfBits liftArgs)
open Silmaril.Wasm (NumType)

/-- The size (and alignment) of a scalar type. -/
def scalarSize : ValTy → Option Nat
  | .bool | .s8 | .u8 => some 1
  | .s16 | .u16 => some 2
  | .s32 | .u32 | .f32 | .char => some 4
  | .s64 | .u64 | .f64 => some 8
  | _ => none

/-- `align_to(x, a)`. -/
def alignUp (x a : Nat) : Nat := (x + a - 1) / a * a

/-- The offsets of fields of the given sizes, from `off`. -/
def fieldOffs : Nat → List Nat → List Nat
  | _, [] => []
  | off, n :: ns => alignUp off n :: fieldOffs (alignUp off n + n) ns

/-- The end of the last field. -/
def fieldsEnd : Nat → List Nat → Nat
  | off, [] => off
  | off, n :: ns => fieldsEnd (alignUp off n + n) ns

/-- The alignment of a record of scalars. -/
def tupleAlign (ns : List Nat) : Nat := ns.foldr max 1

/-- The size of a record of scalars. -/
def tupleSize (ns : List Nat) : Nat := alignUp (fieldsEnd 0 ns) (tupleAlign ns)

/-- A wide result: a record of at least two scalars; its fields and their sizes. -/
def wideOf : Option PTy → Option (List ValTy × List Nat)
  | some (.val (.record ts)) =>
    if 2 ≤ ts.length then (ts.mapM scalarSize).map fun ns => (ts, ns) else none
  | _ => none

/-- `load` of a scalar from its bytes. -/
def loadScalar : ValTy → List UInt8 → Option Val
  | .bool, bs => some (.bool (leNat bs != 0))
  | .s8, bs => some (.s8 (BitVec.ofNat 8 (leNat bs)))
  | .u8, bs => some (.u8 (BitVec.ofNat 8 (leNat bs)))
  | .s16, bs => some (.s16 (BitVec.ofNat 16 (leNat bs)))
  | .u16, bs => some (.u16 (BitVec.ofNat 16 (leNat bs)))
  | .s32, bs => some (.s32 (BitVec.ofNat 32 (leNat bs)))
  | .u32, bs => some (.u32 (BitVec.ofNat 32 (leNat bs)))
  | .s64, bs => some (.s64 (BitVec.ofNat 64 (leNat bs)))
  | .u64, bs => some (.u64 (BitVec.ofNat 64 (leNat bs)))
  | .f32, bs => some (.f32 (BitVec.ofNat 32 (leNat bs)))
  | .f64, bs => some (.f64 (BitVec.ofNat 64 (leNat bs)))
  | .char, bs => (charOfBits (BitVec.ofNat 32 (leNat bs))).map .char
  | _, _ => none

variable (M : CoreInst)

/-- Load the fields at `rp + off`. -/
def loadFields (rp : Nat) : List ValTy → List Nat → List Nat → RM M.St (List Val)
  | [], _, _ => pure []
  | t :: ts, o :: os, n :: ns => do
    let bs ← M.load (rp + o) n
    let v ← RM.ofOption (loadScalar t bs)
    let vs ← loadFields rp ts os ns
    pure (v :: vs)
  | _, _, _ => RM.fail

/-- The canonical lift of a wide result from its return pointer. -/
def liftWide (ts : List ValTy) (ns : List Nat) (rp : BitVec 32) : RM M.St (Option PVal) := do
  RM.check (rp.toNat % tupleAlign ns == 0)
  let s ← RM.get
  RM.check (decide (rp.toNat + tupleSize ns ≤ (M.mem s).length))
  let vs ← loadFields M rp.toNat ts (fieldOffs 0 ns) ns
  pure (some (.val (.record vs)))

/-- Lifting a result, wide results through their return pointer. -/
def liftResultW (r : Option PTy) (xs : List Flat) : RM M.St (Option PVal) :=
  match wideOf r, xs with
  | some (ts, ns), [x] => do
    let rp ← RM.ofOption (asI32? x)
    liftWide M ts ns rp
  | some _, _ => RM.fail
  | none, xs => liftResult M r xs

/-- **`canon lift` with wide results.** -/
def canonCallW (R callee : List Flat → RM M.St (List Flat)) (sig : Sig) (vs : List PVal) :
    RM M.St (Option PVal) := do
  let xs ← lowerParams M R sig.params vs
  let rs ← callee xs
  liftResultW M sig.result rs

/-! ## The multi-value style -/

/-- The stored form of a flat field value: a `bool` is normalised to 0 or 1. -/
def normField : ValTy → Flat → Flat
  | .bool, r =>
    match asI32? r with
    | some x => Flat.i32 (if x == 0 then 0 else 1)
    | none => r
  | _, r => r

/-- The type `bool`. -/
def isBoolTy : ValTy → Bool
  | .bool => true
  | _ => false

/-- The writes of a wide result's fields at `p`: address and bytes of each field. -/
def fieldWrites (p : Nat) : List ValTy → List Nat → List Nat → List Flat → List (Nat × List UInt8)
  | t :: ts, o :: os, n :: ns, r :: rs =>
    (p + o, leBytes n (normField t r).bits.toNat) :: fieldWrites p ts os ns rs
  | _, _, _, _ => []

/-- Perform writes in order. -/
def storeAll : List (Nat × List UInt8) → RM M.St Unit
  | [] => pure ()
  | (a, bs) :: ws => do
    M.store a bs
    storeAll ws

namespace Meta

variable (md : Meta)

/-- A world function with a wide result under the multi-value style: the C convention's
parameters, the multi-value call, the result block allocated with `alloc(size, align)` and the
fields stored there, the canonical checks of the block, and the flat lift of the results. -/
def specCallMV (sig : Sig) (ts : List ValTy) (ns : List Nat) (vs : List PVal) :
    RM M.St (Option PVal) := do
  let xs ← md.specParams M sig.params vs
  let rs ← M.call sig.name xs
  let r ← M.call md.alloc [i32n (tupleSize ns), i32n (tupleAlign ns)]
  let p ← RM.ofOption (single32? r)
  storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns rs)
  RM.check (p.toNat % tupleAlign ns == 0)
  let s ← RM.get
  RM.check (decide (p.toNat + tupleSize ns ≤ (M.mem s).length))
  let v ← RM.ofOption (liftArgs ts rs)
  pure (some (.val (.record v)))

/-- **The multi-value style** (other functions: the C convention). -/
def specW (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some sig =>
    match wideOf sig.result with
    | some (ts, ns) => md.specCallMV M sig ts ns vs
    | none => md.specCall M sig vs
  | none => RM.fail

/-- A function with a wide result returns as many values as its result has fields, of the
flattened core types (what validation of the module gives). -/
def ConformsMV : Prop :=
  ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
    ∀ xs, RM.Returns (M.call s.name xs) fun rs => rs.map (·.type) = ValTy.flatList ts

end Meta

/-- The memory of `M` behaves as a memory. -/
structure MemLawful : Prop where
  mem_set : ∀ s m, M.mem (M.setMem s m) = m
  set_set : ∀ s m m', M.setMem (M.setMem s m) m' = M.setMem s m'

/-! ## The multi-value wrapper -/

/-- `local.set (base + k - 1)`, …, `local.set base`: pop `k` values into consecutive locals. -/
def setsRev (base : Nat) : Nat → List XInstr
  | 0 => []
  | k + 1 => .base (.localSet (base + k)) :: setsRev base k

/-- Store field `j` (local `base + j`) at `p` (local `pl`). -/
def storeField (pl base j : Nat) (t : ValTy) (n off : Nat) (ft : NumType) : List XInstr :=
  [.base (.localGet pl), .base (.localGet (base + j))] ++
    (if isBoolTy t then [.i32Eqz, .i32Eqz] else []) ++ [.store ft n off]

/-- The stores of the fields `j, j + 1, …`. -/
def storeFields (pl base : Nat) : Nat → List ValTy → List Nat → List Nat → List XInstr
  | j, t :: ts, o :: os, n :: ns =>
    storeField pl base j t n o (t.flat.headD (.int .i32)) ++ storeFields pl base (j + 1) ts os ns
  | _, _, _, _ => []

/-- The export shim of a function with a wide result (`n` flat parameters, `k` fields): call,
pop the results into locals `n + 1 …`, allocate the block into local `n`, store, return it. -/
def mvShim (md : Meta) (s : Sig) (ts : List ValTy) (ns : List Nat) : XFn :=
  let n := (flatParams s.params).length
  let k := ts.length
  { params := n, locals := k + 1,
    body := (gets n).map .base ++ [.base (.call s.name n)] ++ setsRev (n + 1) k ++
      [.base (.i32Const (BitVec.ofNat 32 (tupleSize ns))),
        .base (.i32Const (BitVec.ofNat 32 (tupleAlign ns))), .base (.call md.alloc 2),
        .base (.localSet n)] ++
      storeFields n (n + 1) 0 ts (fieldOffs 0 ns) ns ++ [.base (.localGet n)] }

/-- The export shim of a world function in the multi-value style. -/
def exportShimW (md : Meta) (s : Sig) : XFn :=
  match wideOf s.result with
  | some (ts, ns) => mvShim md s ts ns
  | none => (exportShim md s).toX

/-- **The multi-value wrapper.** -/
def wrapW (md : Meta) : XComp :=
  { adaptor := ⟨("cabi_realloc", (reallocShim md.alloc).toX) ::
      md.world.map fun s => (s.name, exportShimW md s)⟩
    lifts := (liftsFrom 0 md.world).map fun l => ⟨l.sig, l.callee, l.realloc, .utf8⟩ }

end Silmaril.Wasm.Jco
