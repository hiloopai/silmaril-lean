module

public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Defs

/-!
# SpecTec ↔ Core 3.0, aggregates track: definitions

Track namespace `Silmaril.Wasm.SpecTec.Sim.Aggregates` (round 2, gap 6 of `docs/projects/spectec/README.md`):
the GC aggregate instructions `struct.*` / `array.*`, i.e. Core's `AggregateStep`.

* `Bounded s`: every array, element segment and data segment of `s` has fewer than `2 ^ 32`
  entries. Core computes lengths and indices of aggregates in 32-bit arithmetic and SpecTec in
  unbounded naturals; they disagree on larger stores (finding R1 of family R: `array.len` returns
  `len mod 2 ^ 32` in Core and the untyped `% len` in SpecTec). Every store Core can build
  satisfies it (arrays are allocated with a 32-bit count), but `Typed` does not enforce it, so the
  forward lemmas that need it take it as a hypothesis.
* `AggTypes env`: the type-level facts the aggregate rules consume and that are not evaluated
  here: SpecTec's `Expand` relation holds of the images of Core's `Expand d ct` (the general form of
  family C's `CtrlCall.expand`), and encoded storage types and mutability flags inhabit their IL
  types (family E). Assumed, not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.Validation (tyV mutV)

/-- Every array, element segment and data segment of the store has fewer than `2 ^ 32` entries. -/
structure Bounded {H : Type} (s : Store H) : Prop where
  /-- Arrays. -/
  arrays : ∀ ai ∈ s.arrays, ai.fields.length < 2 ^ 32
  /-- Element segments. -/
  elems : ∀ ei ∈ s.elems, ei.refs.length < 2 ^ 32
  /-- Data segments. -/
  datas : ∀ di ∈ s.datas, di.bytes.size < 2 ^ 32

/-- The IL type `storagetype`. -/
abbrev storagetypeT : Typ := .varT "storagetype" []
/-- The IL type `arrayinst`. -/
abbrev arrayinstT : Typ := .varT "arrayinst" []
/-- The IL type `structinst`. -/
abbrev structinstT : Typ := .varT "structinst" []
/-- The IL type `mut?`. -/
abbrev mutOptT : Typ := .iterT (.varT "mut" []) .opt

/-- **The type-level facts of the aggregate rules** (assumed; for the typing/encoding track).
`expand` generalises `CtrlCall.expand` from function types to every composite type. -/
structure AggTypes (env : Env) : Prop where
  /-- SpecTec's `Expand` on the images of Core's `Expand`. -/
  expand : ∀ (d : DefType) (ct : CCompType), Expand d ct →
    DDerives env (otherwise env) "Expand" "%~~%" [] (.tuple [CT.defType d, tyV ct])
  /-- An encoded storage type is a `storagetype`. -/
  storagetype : ∀ zt : CStorageType, TypedV env storagetypeT (tyV zt)
  /-- An encoded mutability flag is a `mut?`. -/
  mut_ : ∀ m : Mutability, TypedV env mutOptT (mutV m)
  /-- An array instance of a typed store is an `arrayinst` (inversion of the store's typing;
  stated conditionally, since a float field value is never typed). -/
  arrayOfStore : ∀ {H : Type} (hn : H → String) (s : Store H) (ai : ArrayInst),
    TypedV env storeT (storeV hn s) → ai ∈ s.arrays → TypedV env arrayinstT (arrayInstV ai)
  /-- A struct instance of a typed store is a `structinst`. -/
  structOfStore : ∀ {H : Type} (hn : H → String) (s : Store H) (si : StructInst),
    TypedV env storeT (storeV hn s) → si ∈ s.structs → TypedV env structinstT (structInstV si)

open Silmaril.SpecTec.Equiv.Execution (caseNilV) in
/-- **Decoders of the aggregate opcodes** (assumed; the typing/encoding track's decoders): an
image carrying an aggregate instruction's tag, or `CONST I32`, comes from that instruction. True by
inspection of `instrToV`; used only by the backward lemmas. -/
structure AggDecode : Prop where
  /-- `STRUCT.GET`. -/
  structGet : ∀ (a : Admin) (w : Value), adminToV a = .case "STRUCT.GET" w →
    ∃ sx x i, a = .plain (.structGet sx x i)
  /-- `ARRAY.GET`. -/
  arrayGet : ∀ (a : Admin) (w : Value), adminToV a = .case "ARRAY.GET" w →
    ∃ sx x, a = .plain (.arrayGet sx x)
  /-- `ARRAY.LEN`. -/
  arrayLen : ∀ (a : Admin) (w : Value), adminToV a = .case "ARRAY.LEN" w → a = .plain .arrayLen
  /-- `CONST I32`. -/
  constI32 : ∀ (a : Admin) (w : Value), adminToV a = .case "CONST" (.tuple [caseNilV "I32", w]) →
    ∃ b, a = constI32 b

end Silmaril.Wasm.SpecTec.Sim.Aggregates
