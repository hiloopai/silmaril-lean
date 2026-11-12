module

public import Silmaril.Cerberus.Mem.Concrete.Defs

/-! Concrete LP64 layouts at b3e11ea3. impl_mem.ml:96-98 delegates to
ocaml_frontend/ocaml_implementation.ml, whose DefaultImpl is selected at this pin.
The .impl supplies arithmetic functions, not sizeof constants. -/

@[expose] public section
namespace Silmaril.Cerberus.Mem.Concrete

/-- Runtime tag definitions and the pinned frontend's enum registrations. -/
structure Tags where
  definitions : Map Sym (Loc × TagDefinition) := ∅
  enums : Map Sym IntegerType := ∅

instance : EmptyCollection Tags := ⟨{}⟩
instance : Coe (Map Sym (Loc × TagDefinition)) Tags := ⟨fun definitions => {definitions}⟩

def Tags.lookup (tags : Tags) (sym : Sym) := tags.definitions.lookup sym

/-- ocaml_implementation.ml:130-149. Registration selects signed int when
any enumerator is negative, otherwise unsigned int. Missing tags stay explicit. -/
def registeredInteger (tags : Tags) : IntegerType → Option IntegerType
  | .enum tag => tags.enums.lookup tag
  | ty => some ty

/-- symbol.lem: symbol descriptions do not contribute to equality. -/
def symbolEq (a b : Sym) : Bool := a.key == b.key

/-- symbol.lem: identifier equality ignores source location. -/
def identifierEq (a b : Identifier) : Bool := a.key == b.key

/-- ocaml_implementation.ml:38-65,151-204,214-245. Alias widths in bytes. -/
def baseWidth : IntegerBaseType → Option Nat
  | .ichar => some 1
  | .short => some 2
  | .int => some 4
  | .long | .longLong | .intmax | .intptr => some 8
  | .intN n | .intLeastN n | .intFastN n =>
      match n with | 8 => some 1 | 16 => some 2 | 32 => some 4 | 64 => some 8 | _ => none

/-- ocaml_implementation.ml:81-109,151-204. Plain char is signed. -/
def integerLayout : IntegerType → Option (Nat × Bool)
  | .char => some (1, true)
  | .bool => some (1, false)
  | .signed b => (baseWidth b).map (·, true)
  | .unsigned b => (baseWidth b).map (·, false)
  | .size | .ptraddr => some (8, false)
  | .ptrdiff => some (8, true)
  | .wchar | .wint => some (4, true)
  | .enum _ => none

def integerBounds (ty : IntegerType) : Option (Int × Int) := do
  let (w, signed) ← integerLayout ty
  let modulus : Int := 256 ^ w
  pure (match ty with
    | .wchar => (0, modulus - 1)
    | .wint => (0, modulus / 2 - 1)
    | _ => if signed then (-modulus / 2, modulus / 2 - 1) else (0, modulus - 1))

/-- Layout and bounds use the registered implementation type for enums. -/
def registeredIntegerLayout (tags : Tags) (ty : IntegerType) : Option (Nat × Bool) :=
  registeredInteger tags ty >>= integerLayout

def registeredIntegerBounds (tags : Tags) (ty : IntegerType) : Option (Int × Int) :=
  registeredInteger tags ty >>= integerBounds

structure TypeLayout where
  size : Int
  align : Int
  members : List (Identifier × Ctype × Int) := []
  deriving Repr

/-- ocaml_implementation.ml:449-457,500-502. Padding to the next boundary. -/
def roundUp (n align : Int) : Int := if n % align = 0 then n else n + align - n % align

/-- ocaml_implementation.ml:437-575. Explicit fuel bounds recursive tag lookup;
exhaustion is Unsupported, including malformed recursively embedded structs. -/
def typeLayout : Nat → Tags → Ctype → Except Failure TypeLayout
  | 0, _, _ => .error (.unsupported "recursive layout fuel")
  | fuel+1, tags, .mk _ ty => do
      match ty with
      | .basic (.integer ity) =>
          let some (w, _) := registeredIntegerLayout tags ity | throw (.unsupported "enum or unknown integer layout")
          pure ⟨w, w, []⟩
      -- ocaml_implementation.ml:206-212,247-253, including Float/LongDouble hacks.
      | .basic (.floating (.realFloating _)) => pure ⟨8, 8, []⟩
      | .byte => pure ⟨1, 1, []⟩
      | .pointer _ _ => pure ⟨8, 8, []⟩
      | .atomic t => typeLayout fuel tags t
      | .array t count =>
          let l ← typeLayout fuel tags t
          let some n := count | throw (.unsupported "sizeof incomplete array")
          if n < 0 then throw (.invalid "negative array length")
          pure ⟨n * l.size, l.align, []⟩
      | .struct sym =>
          let some (_, .struct ms flexible) := tags.lookup sym
            | throw (.unsupported "missing struct definition")
          let initialAlign ← match flexible with
            | none => pure 0
            | some (.mk _ _ _ t) => do pure (← typeLayout fuel tags t).align
          let (members, finish, align) ← ms.foldlM (fun (acc, offset, maxAlign) (name, _, al, _, t) => do
            let l ← typeLayout fuel tags t
            let a ← match al with
              | none => pure l.align
              | some (.integer a) => pure a
              | some (.ctype t) => do pure (← typeLayout fuel tags t).align
            if a ≤ 0 then throw (.unsupported "nonpositive member alignment")
            let offset := roundUp offset a
            pure (acc ++ [(name, t, offset)], offset + l.size, max maxAlign a))
            ([], 0, initialAlign)
          if align ≤ 0 then throw (.unsupported "empty struct alignment")
          pure ⟨roundUp finish align, align, members⟩
      | .union sym =>
          -- ocaml_implementation.ml:503-520,566-583. Layout only;
          -- value representation and active-member tracking remain unsupported.
          let some (_, .union ms) := tags.lookup sym
            | throw (.unsupported "missing union definition")
          let (size, align) ← ms.foldlM (fun (maxSize, maxAlign) (_, _, al, _, t) => do
            let l ← typeLayout fuel tags t
            let a ← match al with
              | none => pure l.align
              | some (.integer a) => pure a
              | some (.ctype t) => do pure (← typeLayout fuel tags t).align
            if a ≤ 0 then throw (.unsupported "nonpositive member alignment")
            pure (max maxSize l.size, max maxAlign a)) (0, 0)
          if align ≤ 0 then throw (.unsupported "empty union alignment")
          pure ⟨roundUp size align, align, []⟩
      | _ => throw (.unsupported "layout outside integer pointer array struct union")

/-- Ordinary offsetsof includes the flexible member, lines 437-459. Stored
members remain fixed-only; the flexible offset follows their unpadded end. -/
def memberOffsets (fuel : Nat) (tags : Tags) (tag : Sym) :
    Except Failure (List (Identifier × Ctype × Int)) := do
  let l ← typeLayout fuel tags (.mk [] (.struct tag))
  let some (_, .struct _ flexible) := tags.lookup tag
    | throw (.unsupported "missing struct definition")
  match flexible with
  | none => pure l.members
  | some (.mk _ name _ ty) =>
      let finish ← match l.members.getLast? with
        | none => pure 0
        | some (_, lastTy, off) => do
            pure (off + (← typeLayout (fuel - 1) tags lastTy).size)
      let field ← typeLayout (fuel - 1) tags ty
      pure (l.members ++ [(name, ty, roundUp finish field.align)])

/-- alignof an incomplete array depends only on its element, lines 530-531. -/
def alignment (tags : Tags) : Ctype → Except Failure Int
  | .mk _ (.array t none) => do pure (← typeLayout 64 tags t).align
  | t => do pure (← typeLayout 64 tags t).align

end Silmaril.Cerberus.Mem.Concrete
