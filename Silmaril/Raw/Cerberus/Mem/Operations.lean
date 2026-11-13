module

public import Silmaril.Cerberus.Mem.Typed.Defs

/-! Memory operations reached by Core requests. Source lines refer to
memory/concrete/impl_mem.ml at b3e11ea3, with the default PNVI-ae-udi switches. -/

@[expose] public section
namespace Silmaril.Cerberus.Mem.Concrete

/-- Lines 2096-2175. Effectful shifts check the containing allocation and
permit its one-past address. Pure shifts have separate rules. -/
def shiftPointer (tags : Tags) (s : State) (p : Pointer) (ty : Ctype)
    (n : Int) : Except Failure Pointer := do
  let l ← typeLayout 64 tags ty
  match p with
  | .null _ => throw (.ub .UB046_array_pointer_outside)
  | .function _ => throw (.unsupported "effectful function array shift exception")
  | .unprovenanced _ => throw (.unsupported "out-of-bound pointer arithmetic (Prov_none)")
  | .allocated id addr =>
      let some a := s.allocations.lookup id
        | throw (.ub .UB009_outside_lifetime)
      let shifted := addr + l.size*n
      if a.base ≤ shifted && shifted ≤ a.base+a.size then pure (.allocated id shifted)
      else throw (.ub .UB046_array_pointer_outside)

/-- Lines 1780-1810; mem_common.lem:251-252. Subtraction requires equal live
allocation provenance and inclusive bounds. Array types use their element size. -/
def difference (tags : Tags) (s : State) (ty : Ctype) (p q : Pointer) : Except Failure Int := do
  match p, q with
  | .allocated i x, .allocated j y =>
      if i != j then throw (.ub .UB048_disjoint_array_pointers_subtraction)
      let some a := s.allocations.lookup i
        | throw (.ub .UB009_outside_lifetime)
      if !(a.base ≤ x && x ≤ a.base+a.size && a.base ≤ y && y ≤ a.base+a.size) then
        throw (.ub .UB048_disjoint_array_pointers_subtraction)
      let elem := match ty with | .mk _ (.array e _) => e | _ => ty
      let l ← typeLayout 64 tags elem
      if l.size == 0 then throw (.unsupported "pointer difference zero-size division exception")
      pure ((x-y).tdiv l.size)
  | _, _ => throw (.ub .UB048_disjoint_array_pointers_subtraction)

/-- Lines 1069-1090,1243-1260. A dynamic region has no object type or
initializer. The source ignores the supplied prefix and uses PrefMalloc. -/
def allocateRegion (s : State) (align size : Int) : Except Failure (Pointer × State) := do
  if align ≤ 0 || size < 0 then throw (.unsupported "dynamic allocator host exception")
  let z := s.lastAddress - size
  let addr := z - z % align
  if addr ≤ 0 then throw (.unsupported "dynamic allocator out of memory")
  pure (.allocated s.nextId addr, {s with
    nextId := s.nextId+1, lastAddress := addr, lastUsed := some s.nextId,
    allocations := s.allocations.insert s.nextId {base := addr, size := size}})

/-- Lines 666-675,2264-2285. Concrete pointer casts expose their allocation
under PNVI-ae-udi and check integer bounds. Null and function cases bypass
that check at the pin. This slice needs no symbolic provenance. -/
def integerFromPointer (s : State) (ity : IntegerType)
    (p : Pointer) : Except Failure (Int × State) := do
  match p with
  | .null _ => pure (0, s)
  | .function (.mk _ n _) => pure (n, s)
  | .allocated _ addr | .unprovenanced addr =>
      let s := match p with
        | .allocated id _ => match s.allocations.lookup id with
            | none => s
            | some a => {s with allocations := s.allocations.insert id {a with exposed := true}}
        | _ => s
      let some (lo, hi) := registeredIntegerBounds {enums := s.enumTypes} ity | throw (.unsupported "pointer-to-integer bounds")
      if lo ≤ addr && addr ≤ hi then pure (addr, s)
      else throw (.ub .UB024_out_of_range_pointer_to_integer_conversion)

end Silmaril.Cerberus.Mem.Concrete
