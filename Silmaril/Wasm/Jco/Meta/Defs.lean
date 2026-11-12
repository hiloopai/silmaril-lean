module

public import Silmaril.Wasm.Jco.Canon.Defs
public import Silmaril.Wasm.Wit.Binary.Embed.Defs

/-!
# WIT metadata and the C calling convention it fixes for a core module

`Meta` is the metadata the monadic construction of `Silmaril.Wasm.Jco.Wrap` starts from: the
exported functions of a world (`Sig`s of the first fragment) and the name of the core module's
allocator. It comes from a resolved WIT world (`Meta.ofWorld`, over `Silmaril.Wasm.Wit.Binary.World`) or from the
`component-type` custom section a core module embeds (`Meta.ofModule`, through
`Silmaril.Wasm.Wit.Binary.extractWorldType`; only the UTF-8 string encoding is accepted).

**The C convention (FFI style 1).** The metadata fixes how the core module `M` implements each
world function `f`, as a C compiler would lay it out:

* `M` exports an allocator `alloc(size: i32, align: i32) -> i32`;
* `M` exports `f` under the world name; a memory-free parameter is passed flat
  (`ValTy.lower`, after a type check); a string (UTF-8) or `list<u8>` parameter is copied into
  `M`'s memory at `alloc(len, 1)` and passed as `(ptr, len)`;
* a memory-free result is returned flat; a string or `list<u8>` result is written by `f` as a
  `(ptr, len)` pair to an **out-pointer**: the caller allocates it with `alloc(8, 4)` and passes
  it as the last argument, and `f` returns no core values. The pair is read as the canonical ABI
  reads one (4-aligned out-pointer, bounds checks, UTF-8 validation).

`Meta.spec M md name vs` is the behaviour of world function `name` on values `vs` under this
convention: **"M's behaviour at the world"**, the right-hand side of the behaviour theorem.
`Meta.Conforms M md` says that `M`'s exports have the convention's core result types (what
core validation and type soundness of `M` guarantee): the allocator returns one `i32`, and
functions with an out-pointer return nothing. This is the canonical ABI's convention except for
the allocator's signature and the out-pointer, which is why a wrapper needs an adaptor.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy Val)

/-- WIT metadata of a core module: the world's exported functions and the allocator export. -/
structure Meta where
  world : List Sig
  alloc : String := "alloc"
  deriving Repr, Inhabited, DecidableEq

variable (M : CoreInst) (md : Meta)

namespace Meta

/-- Copy bytes into `M`'s memory at `alloc(len, 1)`; the flat result is `(ptr, len)`. -/
def specBytes (limit : Nat) (bs : List UInt8) : RM M.St (List Flat) := do
  RM.check (decide (bs.length ≤ limit))
  let r ← M.call md.alloc [i32n bs.length, i32n 1]
  let p ← RM.ofOption (single32? r)
  M.store p.toNat bs
  pure [Flat.i32 p, i32n bs.length]

/-- One parameter under the C convention. -/
def specParam : PTy → PVal → RM M.St (List Flat)
  | .val t, .val v => do
    RM.check (t.check v)
    pure (t.lower v)
  | .string, .string s => specBytes M md maxStringBytes (utf8 s)
  | .bytes, .bytes bs => specBytes M md maxListBytes bs
  | _, _ => RM.fail

/-- The parameters under the C convention. -/
def specParams : List PTy → List PVal → RM M.St (List Flat)
  | [], [] => pure []
  | t :: ts, v :: vs => do
    let a ← specParam M md t v
    let b ← specParams ts vs
    pure (a ++ b)
  | _, _ => RM.fail

/-- A world function called under the C convention. -/
def specCall (sig : Sig) (vs : List PVal) : RM M.St (Option PVal) := do
  let xs ← specParams M md sig.params vs
  if inMem sig.result then do
    let r ← M.call md.alloc [i32n 8, i32n 4]
    let o ← RM.ofOption (single32? r)
    let _ ← M.call sig.name (xs ++ [Flat.i32 o])
    liftResult M sig.result [Flat.i32 o]
  else do
    let rs ← M.call sig.name xs
    liftResult M sig.result rs

/-- **M's behaviour at the world**: calling world function `name` under the C convention. -/
def spec (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some sig => specCall M md sig vs
  | none => RM.fail

/-- `M`'s exports have the convention's core result types. -/
structure Conforms : Prop where
  /-- The allocator returns one `i32`. -/
  alloc : ∀ xs, RM.Returns (M.call md.alloc xs) fun r => ∃ p, r = [Flat.i32 p]
  /-- A function with an out-pointer returns no core values. -/
  outPtr : ∀ s ∈ md.world, inMem s.result = true → ∀ xs, RM.Returns (M.call s.name xs) (· = [])

end Meta

/-! ## Metadata from WIT -/

section ofWit
open Silmaril.Wasm.Wit.Binary (Ty)
open Silmaril.Wasm.Component.Binary (PrimValType)

/-- A primitive WIT type that is memory-free. -/
def valOfPrim : PrimValType → Option ValTy
  | .bool => some .bool
  | .s8 => some .s8 | .u8 => some .u8 | .s16 => some .s16 | .u16 => some .u16
  | .s32 => some .s32 | .u32 => some .u32 | .s64 => some .s64 | .u64 => some .u64
  | .f32 => some .f32 | .f64 => some .f64 | .char => some .char
  | .string | .errorContext => none

mutual
/-- A memory-free resolved WIT type: primitives, tuples, `option`, `result` (named types are not
resolved in this fragment). -/
def valOfWit : Silmaril.Wasm.Wit.Binary.Ty → Option ValTy
  | .prim p => valOfPrim p
  | .tuple ts => (valsOfWit ts).map .record
  | .option t => (valOfWit t).map ValTy.option
  | .result ok err => do
    let a ← optOfWit ok
    let b ← optOfWit err
    pure (ValTy.result a b)
  | _ => none
/-- A list of memory-free WIT types. -/
def valsOfWit : List Silmaril.Wasm.Wit.Binary.Ty → Option (List ValTy)
  | [] => some []
  | t :: ts => do
    let a ← valOfWit t
    let b ← valsOfWit ts
    pure (a :: b)
/-- An optional payload type. -/
def optOfWit : Option Silmaril.Wasm.Wit.Binary.Ty → Option (Option ValTy)
  | none => some none
  | some t => (valOfWit t).map some
end

/-- A resolved WIT type of the fragment: memory-free, `string`, or `list<u8>`. -/
def PTy.ofWit : Silmaril.Wasm.Wit.Binary.Ty → Option PTy
  | .prim .string => some .string
  | .list (.prim .u8) => some .bytes
  | t => (valOfWit t).map .val

/-- The signature of a freestanding world function. -/
def Sig.ofWit (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Sig := do
  if f.async then throw s!"{f.name}: async functions are not in the fragment"
  if f.kind ≠ .freestanding then throw s!"{f.name}: resource functions are not in the fragment"
  let ps ← f.params.mapM fun (p, t) => match PTy.ofWit t with
    | some t' => pure t'
    | none => throw s!"{f.name}: parameter {p} is not in the fragment"
  let r ← match f.result with
    | none => pure none
    | some t => match PTy.ofWit t with
      | some t' => pure (some t')
      | none => throw s!"{f.name}: the result is not in the fragment"
  let s : Sig := ⟨f.name, ps, r⟩
  if s.Ok then pure s else throw s!"{f.name}: too many flat parameters or a wide flat result"

/-- The function of one exported world item. -/
def exportSig : Silmaril.Wasm.Wit.Binary.WorldItem → Except String Sig
  | .func f => Sig.ofWit f
  | _ => throw "only exported functions (not interfaces or types) are in the fragment"

/-- Metadata from a resolved WIT world (no imports) and the name of the allocator export. -/
def Meta.ofWorld (w : Silmaril.Wasm.Wit.Binary.World) (alloc : String := "alloc") :
    Except String Meta := do
  if !w.imports.isEmpty then throw "imports are not in the fragment"
  let ss ← w.exports.mapM exportSig
  pure ⟨ss, alloc⟩

/-- Metadata from the `component-type` custom section of a core module's bytes. -/
def Meta.ofModule (m : ByteArray) (alloc : String := "alloc") : Except String Meta := do
  let (_, _, w, se) ← Silmaril.Wasm.Wit.Binary.extractWorldType m
  if se ≠ .utf8 then throw "only the utf8 string encoding is in the fragment"
  Meta.ofWorld w alloc

end ofWit

end Silmaril.Wasm.Jco
