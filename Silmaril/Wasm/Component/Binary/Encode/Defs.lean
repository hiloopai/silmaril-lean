module

public import Silmaril.Wasm.Component.Binary.Defs

/-!
# WebAssembly component binaries: an encoder

`Encode.ast c` writes the component `c` with minimal LEB128 numbers. It fails
(`none`) only on numbers, lengths or sizes of `2 ^ 32` or more. Every encoder
mirrors one production of the grammar in `Silmaril.Wasm.Component.Binary`; the
round trip `parse (encode c) = ok c` is `Silmaril.Wasm.Component.Binary.parse_encode`.

The encoder is list-based: it is a specification and a test-input builder,
not a fast serializer.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary.Encode

open Silmaril.Wasm.ByteParse (Bytes)
open Silmaril.Wasm.ByteParse.Enc (u32 sized)

def name (s : String) : Option Bytes := Silmaril.Wasm.ByteParse.Enc.name s

def attribute_ : Attribute → Option Bytes
  | .implements s => (0x00 :: ·) <$> name s
  | .versionSuffix s => (0x01 :: ·) <$> name s
  | .externalId s => (0x02 :: ·) <$> name s

/-- `nameattributes`. -/
def externName (n : ExternName) : Option Bytes :=
  match n.form with
  | .plain0 => (0x00 :: ·) <$> name n.name
  | .plain1 => (0x01 :: ·) <$> name n.name
  | .attrs as => do
    let a ← name n.name
    let b ← Silmaril.Wasm.ByteParse.Enc.vec attribute_ as
    pure (0x02 :: (a ++ b))

def vec {α : Type} (f : α → Option Bytes) (xs : List α) : Option Bytes :=
  Silmaril.Wasm.ByteParse.Enc.vec f xs

def opt {α : Type} (f : α → Option Bytes) (o : Option α) : Option Bytes :=
  Silmaril.Wasm.ByteParse.Enc.opt f o

def coreSort : CoreSort → Bytes
  | .func => [0x00] | .table => [0x01] | .memory => [0x02] | .global => [0x03]
  | .tag => [0x04] | .type => [0x10] | .module => [0x11] | .instance => [0x12]

def sort : ItemSort → Bytes
  | .core s => 0x00 :: coreSort s
  | .func => [0x01] | .value => [0x02] | .type => [0x03] | .component => [0x04]
  | .instance => [0x05]

def coreSortIdx (x : CoreSortIdx) : Option Bytes := do
  let i ← u32 x.idx
  pure (coreSort x.sort ++ i)

def sortIdx (x : SortIdx) : Option Bytes := do
  let i ← u32 x.idx
  pure (sort x.sort ++ i)

def coreInstArg (p : String × Nat) : Option Bytes := do
  let n ← name p.1
  let i ← u32 p.2
  pure (n ++ ([0x12] ++ i))

def coreInlineExport (p : String × CoreSortIdx) : Option Bytes := do
  let n ← name p.1
  let s ← coreSortIdx p.2
  pure (n ++ s)

def coreInstanceExpr : CoreInstanceExpr → Option Bytes
  | .instantiate m args => do
    let mi ← u32 m
    let a ← vec coreInstArg args
    pure (0x00 :: (mi ++ a))
  | .exports es => do
    let e ← vec coreInlineExport es
    pure (0x01 :: e)

def instArg (p : String × SortIdx) : Option Bytes := do
  let n ← name p.1
  let s ← sortIdx p.2
  pure (n ++ s)

def inlineExport (p : ExternName × SortIdx) : Option Bytes := do
  let n ← externName p.1
  let s ← sortIdx p.2
  pure (n ++ s)

def instanceExpr : InstanceExpr → Option Bytes
  | .instantiate c args => do
    let ci ← u32 c
    let a ← vec instArg args
    pure (0x00 :: (ci ++ a))
  | .exports es => do
    let e ← vec inlineExport es
    pure (0x01 :: e)

def aliasTarget : AliasTarget → Option Bytes
  | .export i n => do
    let a ← u32 i
    let b ← name n
    pure (0x00 :: (a ++ b))
  | .coreExport i n => do
    let a ← u32 i
    let b ← name n
    pure (0x01 :: (a ++ b))
  | .outer c i => do
    let a ← u32 c
    let b ← u32 i
    pure (0x02 :: (a ++ b))

def alias_ (a : Alias) : Option Bytes := do
  let t ← aliasTarget a.target
  pure (sort a.sort ++ t)

def coreValType : CoreValType → Bytes
  | .i32 => [0x7f] | .i64 => [0x7e] | .f32 => [0x7d] | .f64 => [0x7c] | .v128 => [0x7b]
  | .funcref => [0x70] | .externref => [0x6f]

def limits (l : Limits) : Option Bytes :=
  match l.max with
  | none => do
    let a ← u32 l.min
    pure (0x00 :: a)
  | some m => do
    let a ← u32 l.min
    let b ← u32 m
    pure (0x01 :: (a ++ b))

def mut_ (b : Bool) : Bytes := if b then [0x01] else [0x00]

def coreImportDesc : CoreImportDesc → Option Bytes
  | .func t => do
    let a ← u32 t
    pure (0x00 :: a)
  | .table e l => do
    let b ← limits l
    pure (0x01 :: (coreValType e ++ b))
  | .memory l => do
    let b ← limits l
    pure (0x02 :: b)
  | .global t m => pure (0x03 :: (coreValType t ++ mut_ m))
  | .tag t => do
    let a ← u32 t
    pure (0x04 :: ([0x00] ++ a))

def coreFuncTypeBody (t : CoreFuncType) : Option Bytes := do
  let p ← vec (fun v => some (coreValType v)) t.params
  let r ← vec (fun v => some (coreValType v)) t.results
  pure (p ++ r)

def moduleDecl : ModuleDecl → Option Bytes
  | .import m n d => do
    let a ← name m
    let b ← name n
    let c ← coreImportDesc d
    pure (0x00 :: ((a ++ b) ++ c))
  | .type t => do
    let b ← coreFuncTypeBody t
    pure (0x01 :: ([0x60] ++ b))
  | .alias c i => do
    let a ← u32 c
    let b ← u32 i
    pure (0x02 :: ([0x10, 0x01] ++ (a ++ b)))
  | .export n d => do
    let a ← name n
    let c ← coreImportDesc d
    pure (0x03 :: (a ++ c))

def coreType : CoreType → Option Bytes
  | .func t => do
    let b ← coreFuncTypeBody t
    pure (0x60 :: b)
  | .module ds => do
    let b ← vec moduleDecl ds
    pure (0x50 :: b)

def valType : ValType → Option Bytes
  | .prim p => some [p.byte]
  | .idx i => if i < 2 ^ 32 then Silmaril.Wasm.ByteParse.Enc.sN 33 i else none

def labelValType (p : String × ValType) : Option Bytes := do
  let n ← name p.1
  let t ← valType p.2
  pure (n ++ t)

def case (p : String × Option ValType) : Option Bytes := do
  let n ← name p.1
  let t ← opt valType p.2
  pure (n ++ (t ++ [0x00]))

def resultList : Option ValType → Option Bytes
  | some t => (0x00 :: ·) <$> valType t
  | none => some [0x01, 0x00]

def funcTypeBody (f : FuncType) : Option Bytes := do
  let p ← vec labelValType f.params
  let r ← resultList f.result
  pure (p ++ r)

def defValType : DefValType → Option Bytes
  | .prim p => some [p.byte]
  | .record fs => (0x72 :: ·) <$> vec labelValType fs
  | .variant cs => (0x71 :: ·) <$> vec case cs
  | .list t => (0x70 :: ·) <$> valType t
  | .tuple ts => (0x6f :: ·) <$> vec valType ts
  | .flags ls => (0x6e :: ·) <$> vec name ls
  | .enum ls => (0x6d :: ·) <$> vec name ls
  | .option t => (0x6b :: ·) <$> valType t
  | .result o e => do
    let a ← opt valType o
    let b ← opt valType e
    pure (0x6a :: (a ++ b))
  | .own i => (0x69 :: ·) <$> u32 i
  | .borrow i => (0x68 :: ·) <$> u32 i
  | .fixedList t n => do
    let a ← valType t
    let b ← u32 n
    pure (0x67 :: (a ++ b))
  | .stream t => (0x66 :: ·) <$> opt valType t
  | .future t => (0x65 :: ·) <$> opt valType t
  | .map k v => do
    let a ← valType k
    let b ← valType v
    pure (0x63 :: (a ++ b))

def valueBound : ValueBound → Option Bytes
  | .eq i => (0x00 :: ·) <$> u32 i
  | .type t => (0x01 :: ·) <$> valType t

def typeBound : TypeBound → Option Bytes
  | .eq i => (0x00 :: ·) <$> u32 i
  | .subResource => some [0x01]

def externDesc : ExternDesc → Option Bytes
  | .coreModule i => (fun b => 0x00 :: ([0x11] ++ b)) <$> u32 i
  | .func i => (0x01 :: ·) <$> u32 i
  | .value b => (0x02 :: ·) <$> valueBound b
  | .type b => (0x03 :: ·) <$> typeBound b
  | .component i => (0x04 :: ·) <$> u32 i
  | .instance i => (0x05 :: ·) <$> u32 i

def import_ (i : Import) : Option Bytes := do
  let n ← externName i.name
  let d ← externDesc i.desc
  pure (n ++ d)

mutual
def defType : DefType → Option Bytes
  | .val d => defValType d
  | .func f => ((if f.async then 0x43 else 0x40) :: ·) <$> funcTypeBody f
  | .component ds => do
    let n ← u32 ds.length
    let b ← componentDecls ds
    pure (0x41 :: (n ++ b))
  | .instance ds => do
    let n ← u32 ds.length
    let b ← instanceDecls ds
    pure (0x42 :: (n ++ b))
  | .resource r d => do
    let o ← opt u32 d
    pure (0x3f :: (coreValType r ++ o))

def instanceDecl : InstanceDecl → Option Bytes
  | .coreType t => (0x00 :: ·) <$> coreType t
  | .type t => (0x01 :: ·) <$> defType t
  | .alias a => (0x02 :: ·) <$> alias_ a
  | .export n d => do
    let a ← externName n
    let b ← externDesc d
    pure (0x04 :: (a ++ b))

def componentDecl : ComponentDecl → Option Bytes
  | .import n d => do
    let a ← externName n
    let b ← externDesc d
    pure (0x03 :: (a ++ b))
  | .inst d => instanceDecl d

def instanceDecls : List InstanceDecl → Option Bytes
  | [] => some []
  | d :: ds => do
    let a ← instanceDecl d
    let b ← instanceDecls ds
    pure (a ++ b)

def componentDecls : List ComponentDecl → Option Bytes
  | [] => some []
  | d :: ds => do
    let a ← componentDecl d
    let b ← componentDecls ds
    pure (a ++ b)
end

def canonOpt : CanonOpt → Option Bytes
  | .utf8 => some [0x00] | .utf16 => some [0x01] | .latin1utf16 => some [0x02]
  | .memory i => (0x03 :: ·) <$> u32 i
  | .realloc i => (0x04 :: ·) <$> u32 i
  | .postReturn i => (0x05 :: ·) <$> u32 i
  | .async => some [0x06]
  | .callback i => (0x07 :: ·) <$> u32 i

def canon : Canon → Option Bytes
  | .lift f opts t => do
    let a ← u32 f
    let b ← vec canonOpt opts
    let c ← u32 t
    pure (0x00 :: ([0x00] ++ ((a ++ b) ++ c)))
  | .lower f opts => do
    let a ← u32 f
    let b ← vec canonOpt opts
    pure (0x01 :: ([0x00] ++ (a ++ b)))
  | .resourceNew t => (0x02 :: ·) <$> u32 t
  | .resourceDrop t => (0x03 :: ·) <$> u32 t
  | .resourceRep t => (0x04 :: ·) <$> u32 t

def start (s : Start) : Option Bytes := do
  let a ← u32 s.func
  let b ← vec u32 s.args
  let c ← u32 s.results
  pure ((a ++ b) ++ c)

def export_ (e : Export) : Option Bytes := do
  let a ← externName e.name
  let b ← sortIdx e.item
  let c ← opt externDesc e.desc
  pure ((a ++ b) ++ c)

def value (v : Value) : Option Bytes := do
  let t ← valType v.type
  let n ← u32 v.bytes.size
  pure (t ++ (n ++ v.bytes.data.toList))

/-- A size-prefixed `vec` section with id `id`. -/
def vecSection {α : Type} (id : UInt8) (f : α → Option Bytes) (xs : List α) : Option Bytes := do
  let v ← vec f xs
  let s ← sized v
  pure (id :: s)

mutual
def section_ : Section → Option Bytes
  | .custom n d => do
    let a ← name n
    let s ← sized (a ++ d.data.toList)
    pure (0x00 :: s)
  | .coreModule m => do
    let s ← sized m.data.toList
    pure (0x01 :: s)
  | .coreInstances xs => vecSection 0x02 coreInstanceExpr xs
  | .coreTypes xs => vecSection 0x03 coreType xs
  | .component c => do
    let b ← ast c
    let s ← sized b
    pure (0x04 :: s)
  | .instances xs => vecSection 0x05 instanceExpr xs
  | .aliases xs => vecSection 0x06 alias_ xs
  | .types xs => vecSection 0x07 defType xs
  | .canons xs => vecSection 0x08 canon xs
  | .start st => do
    let b ← start st
    let s ← sized b
    pure (0x09 :: s)
  | .imports xs => vecSection 0x0a import_ xs
  | .exports xs => vecSection 0x0b export_ xs
  | .values xs => vecSection 0x0c value xs

def sections : List Section → Option Bytes
  | [] => some []
  | s :: ss => do
    let a ← section_ s
    let b ← sections ss
    pure (a ++ b)

def ast : Ast → Option Bytes
  | .mk ss => do
    let b ← sections ss
    pure (preambleBytes ++ b)
end

end Encode

/-- Encode a component binary. -/
def encode (c : Ast) : Option ByteArray := (Encode.ast c).map fun l => ⟨l.toArray⟩

end Silmaril.Wasm.Component.Binary
