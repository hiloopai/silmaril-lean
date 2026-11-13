module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Std.Data.HashMap

/-! # Bit-fields lowered to storage units

Typed Ail has no bit-field members (Cerberus rejects them at desugaring), so the Clang frontend
desugars them itself. A struct with bit-fields becomes an ordinary struct:

* **Placement** follows the SysV x86-64 rules (gcc's): a named or unnamed bit-field of declared
  type `T` (size and alignment `s`) of width `w > 0` is placed at the current bit unless that
  would cross an `s`-aligned boundary, in which case it starts at the next one; a zero-width
  bit-field moves the current bit to the next boundary of its type; only named bit-fields add
  their type's alignment to the struct's. Ordinary members are placed as ccomp places them
  (`Silmaril.Cerberus.Mem.Layout.typeLayout`, mirrored by `sizeAlign` here, since cfront may not
  import it), at the next byte aligned for them.
* **Storage.** The bytes between two ordinary members (or the end of the struct) that hold
  bit-fields form a region that no ordinary member overlaps. The region is covered exactly by
  unsigned integer members (`__cfront_bf<offset>`, 1, 2, 4 or 8 bytes, each at an offset aligned
  for it and no wider than the struct's alignment) cut so that no named bit-field straddles two
  of them. Every ordinary member keeps its offset; the first member is given the struct's
  alignment (`_Alignas`) when the storage members alone do not reach it. `layout` checks the
  result against ccomp's layout and fails closed on any difference.
* **Access** (little-endian): a read is `(T)(((W)u >> off) & mask)`, sign-extended for a signed
  `T` as `(v ^ m) - m` (no implementation-defined shift); a write is
  `u = (((W)(T)v & mask) << off) | ((W)u & ~(mask << off))` (the right operand first, as gcc
  stores after evaluating it), followed by a read of the new value as the assignment's value.
  `W` is `unsigned int` or `unsigned long`.

* **`volatile`.** A storage member that holds a `volatile` bit-field is `volatile`, and so is
  every access to it. An access reads (and writes) the whole unit, as gcc's does; an assignment's
  value is read back from the unit, one volatile read more than gcc makes.

* **Unions.** Each bit-field of a union has a storage member of its own (`unionLayout`).

Unnamed bit-fields in unions, 32-bit fields of an enumerated type without negative
enumerators (gcc's `unsigned int`, Cerberus's `int`), and bit-fields straddling two storage
members are rejected. A narrower field of an enumerated type has gcc's signedness: unsigned
unless an enumerator is negative. A field wider than `int` and narrower than its type
(`Field.wide`) has gcc's type of its own width: arithmetic on it is reduced to that width
(`reduce`) where gcc's and Clang's computations differ only by it, and rejected where they differ
otherwise. There is no Cerberus differential for these programs: they are judged against gcc
only.
-/

@[expose] public section

namespace Silmaril.Clang.Bitfield

open Silmaril.Cerberus Ail

/-! ## ccomp's layout (LP64, `Mem.Layout.typeLayout`) -/

def roundUp (n a : Nat) : Nat := if a == 0 then n else (n + a - 1) / a * a

/-- The size in bytes of an integer type (an enumerated type is ccomp's `int`). -/
def intSize : IntegerType → Except String Nat
  | .char | .bool => return 1
  | .signed b | .unsigned b => base b
  | .enum _ | .wchar | .wint => return 4
  | .size | .ptrdiff | .ptraddr => return 8
where
  base : IntegerBaseType → Except String Nat
    | .ichar => return 1 | .short => return 2 | .int => return 4
    | .long | .longLong | .intmax | .intptr => return 8
    | .intN n | .intLeastN n | .intFastN n =>
      if n == 8 || n == 16 || n == 32 || n == 64 then return n / 8 else throw s!"int{n}_t"

mutual

/-- Size and alignment of a complete type as ccomp lays it out (floating types are 8 and 8, as
in Cerberus's implementation). -/
partial def sizeAlign (defs : Std.HashMap Nat TagDefinition) : Ctype → Except String (Nat × Nat)
  | .mk _ (.basic (.integer it)) => do let w ← intSize it; return (w, w)
  | .mk _ (.basic (.floating _)) => return (8, 8)
  | .mk _ .byte => return (1, 1)
  | .mk _ (.pointer ..) => return (8, 8)
  | .mk _ (.atomic t) => sizeAlign defs t
  | .mk _ (.array t (some n)) => do
    let (s, a) ← sizeAlign defs t
    return (n.toNat * s, a)
  | .mk _ (.struct s) => match defs[s.number]? with
    | some (.struct ms fam) => do
      let (_, size, align) ← structLayout defs ms fam
      return (size, align)
    | _ => throw "layout of an incomplete struct"
  | .mk _ (.union s) => match defs[s.number]? with
    | some (.union ms) => do
      let mut size := 0
      let mut align := 0
      for (_, (_, al, _, t)) in ms do
        let (s, a) ← sizeAlign defs t
        size := max size s
        align := max align (← memberAlign defs al a)
      if align == 0 then throw "layout of an empty union"
      return (roundUp size align, align)
    | _ => throw "layout of an incomplete union"
  | _ => throw "layout of an unsupported type"

partial def memberAlign (defs : Std.HashMap Nat TagDefinition) (al : Option Alignment) (natural : Nat) :
    Except String Nat :=
  match al with
  | none => return natural
  | some (.integer a) => return a.toNat
  | some (.ctype t) => return (← sizeAlign defs t).2

/-- The member offsets, size and alignment of a struct. -/
partial def structLayout (defs : Std.HashMap Nat TagDefinition)
    (ms : List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)))
    (fam : Option FlexibleArrayMember) : Except String (List Nat × Nat × Nat) := do
  let mut align ← match fam with
    | none => pure 0
    | some (.mk _ _ _ t) => pure (← sizeAlign defs t).2
  let mut off := 0
  let mut offs := #[]
  for (_, (_, al, _, t)) in ms do
    let (s, a) ← sizeAlign defs t
    let a ← memberAlign defs al a
    off := roundUp off a
    offs := offs.push off
    off := off + s
    align := max align a
  if align == 0 then throw "layout of an empty struct"
  return (offs.toList, roundUp off align, align)

end

/-! ## Bit-field placement and storage -/

/-- A named bit-field: the storage member holding it and its place there. -/
structure Field where
  name : String
  /-- The storage member (an unsigned integer member of the struct). -/
  unit : Identifier
  unitTy : IntegerType
  /-- The bit offset in the storage member. -/
  off : Nat
  width : Nat
  unitBits : Nat
  /-- The declared type (an integer type) and its width in bits. -/
  ty : IntegerType
  tyBits : Nat
  signed : Bool
  /-- The storage member is `volatile` (it holds a `volatile` bit-field). -/
  volatile : Bool := false

/-- A field wider than `int` and narrower than its type: gcc computes with its value in the
field's own width (it reads C's DR 315 so), Clang in the declared type. -/
def Field.wide (f : Field) : Bool := 32 < f.width && f.width < f.tyBits

/-- A member of a struct definition, in declaration order. -/
inductive Item where
  /-- An ordinary member: its declaration id, name and type. -/
  | member (declId : String) (x : Identifier) (m : Attributes × Option Alignment × Qualifiers × Ctype)
  /-- A bit-field: its declaration id, its name (none: unnamed), type, width and whether it is
  `volatile`. -/
  | bit (declId : String) (name : Option String) (ty : IntegerType) (signed : Bool) (width : Nat)
      (volatile : Bool)

/-- The unsigned storage type of `k` bytes. -/
def unitType : Nat → IntegerType
  | 1 => .unsigned .ichar
  | 2 => .unsigned .short
  | 4 => .unsigned .int
  | _ => .unsigned .long

/-- A cover of the bytes `[lo, hi)` by storage units `(offset, size)`, each aligned for its size
and at most `maxK` bytes, cut only at the byte boundaries `cut` allows (widest first). -/
def cover (lo hi maxK : Nat) (cut : Nat → Bool) : Option (List (Nat × Nat)) := Id.run do
  -- best[i]: a cover of [lo + i, hi)
  let n := hi - lo
  let mut best : Array (Option (List (Nat × Nat))) := Array.replicate (n + 1) none
  best := best.set! n (some [])
  for j in [0:n] do
    let i := n - 1 - j
    let o := lo + i
    for k in [8, 4, 2, 1] do
      if (best[i]?).bind id |>.isSome then continue
      if k ≤ maxK && o % k == 0 && i + k ≤ n && cut (o + k) then
        if let some (some rest) := best[i + k]? then
          best := best.set! i (some ((o, k) :: rest))
  return (best[0]?).bind id

/-- The integer type, signedness and volatility of an ordinary member that a storage unit may
absorb: a character, signed or unsigned integer member without `_Alignas` (as wide as its type,
it is read by a conversion to the type, so the signedness given for `char` is not used). -/
def absorbable : Item → Option (IntegerType × Bool × Bool)
  | .member _ _ (_, none, q, .mk _ (.basic (.integer .char))) => some (.char, true, q.volatile)
  | .member _ _ (_, none, q, .mk _ (.basic (.integer it@(.signed _)))) => some (it, true, q.volatile)
  | .member _ _ (_, none, q, .mk _ (.basic (.integer it@(.unsigned _)))) => some (it, false, q.volatile)
  | _ => none

/-- Why a storage pass failed: no cover for the bit-fields between the ordinary members of these
indices (none: the start or the end of the struct), or anything else. -/
inductive Failure where
  | cover (prev next : Option Nat) (msg : String)
  | other (msg : String)

/-- Pass 2 of `layout`: storage units over each region of bit-fields, given the SysV placement
(`offs`, `size`, `align`). The members `absorb` marks are stored in the units too, each as a
bit-field as wide as its type. -/
def storage (defs : Std.HashMap Nat TagDefinition) (items : Array Item) (offs : Array Nat)
    (size align : Nat) (absorb : Array Bool) :
    Except Failure (Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) ×
      Array (String × Field)) := do
  let other {α} (r : Except String α) : Except Failure α := r.mapError .other
  let mut out := #[]
  let mut fields := #[]
  let mut start := 0  -- the end of the previous ordinary member
  let mut prev : Option Nat := none  -- its index
  let mut run : Array (Item × Nat) := #[]
  let mut memberOffs := #[]
  for (it, i) in (items.push (.member "" ⟨.unknown, ""⟩ (.mk [], none, ⟨false, false, false⟩, .mk [] .void))).zipIdx do
    let last := i == items.size
    match it, absorbable it with
    | .bit .., _ => run := run.push (it, offs[i]!)
    | .member d x _, some (ty, sg, v) =>
      if absorb[i]?.getD false then
        run := run.push (.bit d (some x.name) ty sg (8 * (← other (intSize ty))) v, 8 * offs[i]!)
        continue
    | _, _ => pure ()
    let .member _ x m := it | continue
    let o := if last then size else offs[i]!
    if !run.isEmpty then
      let named := run.filterMap fun
        | (.bit d (some n) ty sg w v, p) => if w > 0 then some (d, n, ty, sg, w, v, p) else none
        | _ => none
      let cut (b : Nat) := named.all fun (_, _, _, _, w, _, p) => !(p < 8 * b && 8 * b < p + w)
      let some units := cover start o align cut
        | throw (.cover prev (if last then none else some i) s!"bit-fields at bytes {start}..{o} have no storage cover")
      for (uo, k) in units do
        let ux : Identifier := ⟨.unknown, s!"__cfront_bf{uo}"⟩
        let inUnit := named.filter fun (_, _, _, _, w, _, p) => 8 * uo ≤ p && p + w ≤ 8 * (uo + k)
        let vol := inUnit.any (·.2.2.2.2.2.1)
        out := out.push (ux, (Attributes.mk [], none, ⟨false, false, vol⟩, .mk [] (.basic (.integer (unitType k)))))
        for (d, n, ty, sg, w, _, p) in inUnit do
            let f : Field :=
              { name := n, unit := ux, unitTy := unitType k, unitBits := 8 * k, off := p - 8 * uo,
                width := w, ty, tyBits := 8 * (← other (intSize ty)), signed := sg, volatile := vol }
            fields := fields.push (d, f)
      run := #[]
    if !last then
      out := out.push (x, m)
      memberOffs := memberOffs.push (out.size - 1, o)
      let (s, _) ← other <| match m.2.2.2 with
        | .mk _ (.array _ none) => pure (0, 1)
        | t => sizeAlign defs t
      start := o + s
      prev := some i
  -- the struct's alignment: on the first member when the members do not reach it
  let ms := out.toList
  let (ms, fam) := match ms.getLast? with
    | some (x, (as, none, q, .mk _ (.array e none))) => (ms.dropLast, some (FlexibleArrayMember.mk as x q e))
    | _ => (ms, none)
  let (_, _, a) ← other (structLayout defs ms fam)
  if a < align then
    let some (x, (as, al, q, t)) := out[0]? | throw (.other "an empty struct")
    out := out.set! 0 (x, (as, some (.integer (max align (← other (memberAlign defs al 0)))), q, t))
  -- check the result against ccomp's layout
  let ms := out.toList
  let (ms', fam) := match ms.getLast? with
    | some (x, (as, none, q, .mk _ (.array e none))) => (ms.dropLast, some (FlexibleArrayMember.mk as x q e))
    | _ => (ms, none)
  let (offs', size', align') ← other (structLayout defs ms' fam)
  for (j, o) in memberOffs do
    if j < ms'.length && offs'[j]? != some o then throw (.other "bit-field storage moved an ordinary member")
  if size' != size || align' != align then
    throw (.other s!"bit-field storage gives size {size'} and alignment {align'}, not {size} and {align}")
  let stored := (items.filter fun | .bit _ (some _) _ _ w _ => w > 0 | _ => false).size +
    (absorb.filter id).size
  if fields.size != stored then throw (.other "a bit-field straddles two storage units")
  return (out, fields)

/-- `storage`, absorbing the members next to a region without a cover: the one before, the one
after, or both (at most `fuel` times). -/
def absorbing (defs : Std.HashMap Nat TagDefinition) (items : Array Item) (offs : Array Nat)
    (size align : Nat) :
    Nat → Array Bool → Except String (Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) ×
      Array (String × Field))
  | fuel, absorb => match storage defs items offs size align absorb, fuel with
    | .ok r, _ => .ok r
    | .error (.other e), _ => .error e
    | .error (.cover _ _ e), 0 => .error e
    | .error (.cover p n e), fuel + 1 => Id.run do
      let can (j : Option Nat) := j.filter fun j => (items[j]?.bind absorbable).isSome
      for c in [[can p], [can n], [can p, can n]] do
        unless c.all Option.isSome do continue
        let absorb := c.foldl (fun a j => a.set! (j.getD 0) true) absorb
        if let .ok r := absorbing defs items offs size align fuel absorb then return .ok r
      return .error e

/-- The struct's members with the bit-fields' storage, and where each named bit-field lives
(by declaration id). Bit-fields that share gcc's storage unit with an ordinary integer member
(`char c; unsigned f : 23;`: `f` is in bytes 1 to 3) have no cover of their own; the member next
to them is then absorbed into the unit (`storage`), and so lives (by its declaration id) as a
bit-field as wide as its type: its address cannot be taken. -/
def layout (defs : Std.HashMap Nat TagDefinition) (items : Array Item) :
    Except String (Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) ×
      Array (String × Field)) := do
  -- pass 1: SysV placement; ordinary members as ccomp places them
  let isFam (i : Nat) (t : Ctype) : Bool := match t with
    | .mk _ (.array _ none) => i + 1 == items.size
    | _ => false
  let mut cur := 0  -- bits
  let mut align := 0
  let mut offs : Array Nat := #[]  -- per item: byte offset (member) or bit position (bit-field)
  for (it, i) in items.zipIdx do
    match it with
    | .member _ _ (_, al, _, t) =>
      let (s, a) ← if isFam i t then match t with
          | .mk _ (.array e _) => do pure (0, (← sizeAlign defs e).2)
          | _ => pure (0, 1)
        else sizeAlign defs t
      let a ← memberAlign defs al a
      let o := roundUp (roundUp cur 8 / 8) a
      offs := offs.push o
      cur := 8 * (o + s)
      align := max align a
    | .bit _ name ty _ w _ =>
      let s ← intSize ty
      if w > 8 * s then throw "bit-field wider than its type"
      if w == 0 then
        cur := roundUp cur (8 * s)
        offs := offs.push cur
      else
        if cur % (8 * s) + w > 8 * s then cur := roundUp cur (8 * s)
        offs := offs.push cur
        cur := cur + w
        if name.isSome then align := max align s
  if align == 0 then throw "a struct with no named member"
  let size := roundUp (roundUp cur 8 / 8) align
  -- pass 2
  absorbing defs items offs size align 4 (Array.replicate items.size false)

/-- A union's members with its bit-fields' storage, and where each bit-field lives. Every
bit-field of a union starts at its bit 0, so each has a storage member of its own, unsigned and
of its declared type's size: the union's size and alignment stay gcc's (a named bit-field
aligns the union for its type, and its size, the bytes of its width, rounds up to that
alignment as the declared type's size does). Unnamed bit-fields are rejected. -/
def unionLayout (items : Array Item) :
    Except String (Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) ×
      Array (String × Field)) := do
  let mut out := #[]
  let mut fields := #[]
  for (it, i) in items.zipIdx do
    match it with
    | .member _ x m => out := out.push (x, m)
    | .bit _ none .. => throw "an unnamed bit-field in a union"
    | .bit d (some n) ty sg w vol =>
      let s ← intSize ty
      if w == 0 || w > 8 * s then throw s!"bit-field {n}: width {w}"
      let ux : Identifier := ⟨.unknown, s!"__cfront_bf{i}"⟩
      out := out.push (ux, (Attributes.mk [], none, ⟨false, false, vol⟩, .mk [] (.basic (.integer (unitType s)))))
      fields := fields.push (d, { name := n, unit := ux, unitTy := unitType s, unitBits := 8 * s, off := 0,
                                  width := w, ty, tyBits := 8 * s, signed := sg, volatile := vol })
  return (out, fields)

/-! ## Reads and writes -/

def noQ : Qualifiers := ⟨false, false, false⟩

def ity (t : IntegerType) : Ctype := .mk [] (.basic (.integer t))

def rv (t : IntegerType) (n : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete t)))) [] .unknown n

def castTo (t : IntegerType) (e : TypedExpression) : TypedExpression := rv t (.cast noQ (ity t) e)

/-- The working type of a storage unit's arithmetic. -/
def Field.work (f : Field) : IntegerType :=
  if f.unitTy == .unsigned .long then .unsigned .long else .unsigned .int

def Field.workBits (f : Field) : Nat := if f.work == .unsigned .long then 64 else 32

def Field.mask (f : Field) : Nat := 2 ^ f.width - 1

def uconst (t : IntegerType) (v : Nat) : TypedExpression :=
  rv t (.const (.integer (.iconstant v .decimal (some (if t == .unsigned .long then .ul else .u)))))

def bin (t : IntegerType) (a : TypedExpression) (op : ArithmeticOperator) (b : TypedExpression) :
    TypedExpression :=
  rv t (.binary a (.arithmetic op) b)

/-- The storage unit, as an lvalue of a struct lvalue `base` (or a pointer to one, `arrow`). -/
def Field.unitLvalue (f : Field) (q : Qualifiers) (base : TypedExpression) (arrow : Bool) : TypedExpression :=
  .mk (.lvalue { q with volatile := q.volatile || f.volatile } (ity f.unitTy) false) [] .unknown
    (if arrow then .memberofptr base f.unit else .memberof base f.unit)

/-- The storage unit's value in the working type. -/
def Field.load (f : Field) (u : TypedExpression) : TypedExpression :=
  castTo f.work (rv f.unitTy (.rvalue u))

/-- `v & mask` in the working type (nothing when the field is as wide as it). -/
def Field.masked (f : Field) (v : TypedExpression) : TypedExpression :=
  if f.width == f.workBits then v else bin f.work v .band (uconst f.work f.mask)

def intC (v : Nat) : TypedExpression := rv (.signed .int) (.const (.integer (.iconstant v .decimal none)))

/-- The bit-field's bits, `((W)u >> off) & mask`. -/
def Field.bits (f : Field) (u : TypedExpression) : TypedExpression :=
  let v := f.load u
  f.masked (if f.off == 0 then v else bin f.work v .shr (intC f.off))

/-- The value of bits `b` (in the working type, below `2 ^ width`) as the declared type: for a
signed type, `(b ^ m) - m` with `m` the sign bit, in a signed type wide enough. -/
def Field.ofBits (f : Field) (b : TypedExpression) : TypedExpression :=
  if !f.signed || f.width == f.tyBits then castTo f.ty b
  else
    let s : IntegerType := if f.width ≤ 31 then .signed .int else .signed .long
    let m := uconst f.work (2 ^ (f.width - 1))
    castTo f.ty (bin s (castTo s (bin f.work b .bxor m)) .sub (castTo s m))

def Field.read (f : Field) (u : TypedExpression) : TypedExpression := f.ofBits (f.bits u)

/-- `v`, of the 64-bit integer type `t`, converted to gcc's `w`-bit integer type of `t`'s
signedness (`0 < w < 64`): its low `w` bits, `(unsigned long)v & mask`, sign-extended for a
signed type as `(b ^ m) - m`, as a value of type `t`. -/
def reduce (w : Nat) (signed : Bool) (t : IntegerType) (v : TypedExpression) : TypedExpression :=
  let ul : IntegerType := .unsigned .long
  let b := bin ul (castTo ul v) .band (uconst ul (2 ^ w - 1))
  if !signed then (if t == ul then b else castTo t b)
  else
    let sl : IntegerType := .signed .long
    let m := uconst ul (2 ^ (w - 1))
    castTo t (bin sl (castTo sl (bin ul b .bxor m)) .sub (castTo sl m))

/-- A value converted to the declared type, as the bits it stores, in place in the unit. -/
def Field.toBits (f : Field) (v : TypedExpression) : TypedExpression :=
  let b := f.masked (castTo f.work (castTo f.ty v))
  if f.off == 0 then b else bin f.work b .shl (intC f.off)

/-- The bits a constant stores, in place in the unit. -/
def Field.constBits (f : Field) (v : Int) : Nat :=
  let v := if f.ty == .bool then (if v == 0 then 0 else 1) else v
  let m : Int := 2 ^ f.width
  ((v % m + m) % m).toNat * 2 ^ f.off

/-- `u = toBits(v) | ((W)u & ~(mask << off))`: the value first, then the unit's other bits. -/
def Field.store (f : Field) (u v : TypedExpression) : TypedExpression :=
  let place := f.mask * 2 ^ f.off
  let new := f.toBits v
  if place == 2 ^ f.unitBits - 1 then rv f.unitTy (.assign u new)
  else
    let keep := bin f.work (f.load u) .band (uconst f.work (2 ^ f.workBits - 1 - place))
    rv f.unitTy (.assign u (bin f.work new .bor keep))

/-- The type of `T + 1` for the declared type `T` (its promotion and `int`'s usual arithmetic
conversion). -/
def Field.arith (f : Field) : IntegerType := if f.tyBits < 32 then .signed .int else f.ty

/-- An assignment of `v` (`=`, compound, prefix `++`/`--`): the store, then the stored value. -/
def Field.assign (f : Field) (u v : TypedExpression) : TypedExpression :=
  rv f.ty (.binary (f.store u v) .comma (f.read u))

/-- `v ± 1` for prefix and postfix `++`/`--`. -/
def Field.step (f : Field) (u : TypedExpression) (incr : Bool) : TypedExpression :=
  bin f.arith (f.read u) (if incr then .add else .sub) (intC 1)

/-- Postfix `++`/`--`: the store, then the old value, recovered from the new bits as
`(new ∓ 1) & mask` (not for `_Bool`, where the new value does not determine the old one). -/
def Field.postfix (f : Field) (u : TypedExpression) (incr : Bool) : TypedExpression :=
  let old := f.ofBits (f.masked (bin f.work (f.bits u) (if incr then .sub else .add) (uconst f.work 1)))
  rv f.ty (.binary (f.store u (f.step u incr)) .comma old)

end Silmaril.Clang.Bitfield
