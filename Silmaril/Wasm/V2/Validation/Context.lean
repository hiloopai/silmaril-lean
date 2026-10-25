module

public import Silmaril.Wasm.V2.Validation.Types
public import Silmaril.Wasm.V2.Instructions

/-!
# WebAssembly 2.0 validation contexts

Transcribed from the official SpecTec source
`specification/wasm-2.0/6-typing.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (see `specs/wasm/core-2.0.json`).
Line references of the form `6-typing:NN` point into that file.

`Context` is `syntax context` (`6-typing:5-9`):

```
{ TYPES functype*, FUNCS functype*, GLOBALS globaltype*,
  TABLES tabletype*, MEMS memtype*,
  ELEMS elemtype*, DATAS datatype*,
  LOCALS valtype*, LABELS resulttype*, RETURN resulttype? }
```

The fields are declared here in that order.

## Syntactic versus semantic value types

`LOCALS` holds `valtype*`. The only rule that populates it is `Func_ok`
(`6-typing:592`), whose premise `(if t =/= BOT)*` excludes `BOT` from the
declared locals, and whose parameters come from a `functype` in `C.TYPES`,
which is built from the module's syntax. So `locals` holds *syntactic*
`ValType`s, and no rule can ever put `BOT` there.

`LABELS` and `RETURN` hold `resulttype*` and `resulttype?`. These are consumed
by `Instr_ok/br`, `/br_if`, `/br_table` (`6-typing:232-243`) and
`Instr_ok/return` (`6-typing:258`), all of which feed the stored result type
into a conclusion that `Instrs_ok/sub` (`6-typing:168`) may then weaken through
`Resulttype_sub`; `Resulttype_sub` is stated on `valtype`, which includes `BOT`.
Although every label pushed by `Instr_ok/block`, `/loop` and `/if`
(`6-typing:213-227`) comes from `Blocktype_ok` and is therefore `BOT`-free in
any concrete derivation, nothing in the judgment restricts it, and the Core 3.0
layer (`Silmaril/Wasm/Validation/Context.lean`) keeps `labels` and `return_` at
the semantic type. We follow Core 3.0: `labels : List CResultType` and
`return_ : Option CResultType`, while `locals : List ValType`. This is the
weaker (hence safer) assumption for anyone consuming the context, and it keeps
`Instr_ok/br_table`, which compares a *semantic* result type against
`C.LABELS[l]`, free of coercions.

**Deviation (`C.REFS`), decided for this development.** `6-typing` has no
`REFS` field and `Module_ok` (`6-typing:681`) carries `;; TODO: refs`, so the
pinned SpecTec 2.0 source omits the `x \in C.REFS` premise that the W3C 2.0
prose puts on `ref.func`. The reference interpreter does enforce it
(`interpreter/valid/valid.ml`), `test/core/ref_func.wast` contains
`assert_invalid` cases that rely on it, and Core 3.0 has the field
(`Silmaril/Wasm/Validation/Context.lean`). We therefore add
`refs : List FuncIdx` and implement the check. See `Silmaril.Wasm.V2.Validation`.

## Context extension

Two different record concatenations occur in `6-typing`, and they differ in
which side contributes the *front* of each sequence. They are modelled by
`Context.withLabel` and `Context.withFuncFrame` rather than by a general
monoid instance, because the second is only well defined at its use site (see
its doc comment).

No other deviation from the pinned SpecTec source is taken in this file.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Validation

/-! ## The context -/

/-- `syntax context` (`6-typing:5`). All fields default to the empty sequence,
so `({} : Context)` is the empty context used by `Module_ok` (`6-typing:682`)
for `Import_ok`. -/
structure Context where
  /-- `TYPES functype*`. -/
  types : List FuncType := []
  /-- `FUNCS functype*`; imported functions first, as in `Module_ok`. -/
  funcs : List FuncType := []
  /-- `GLOBALS globaltype*`. -/
  globals : List GlobalType := []
  /-- `TABLES tabletype*`. -/
  tables : List TableType := []
  /-- `MEMS memtype*`. -/
  mems : List MemoryType := []
  /-- `ELEMS elemtype*`; `elemtype = reftype` (`1-syntax:175`). -/
  elems : List ElemType := []
  /-- `DATAS datatype*`; `datatype = OK` (`1-syntax:177`) carries no
  information, so only the length matters. -/
  datas : List Unit := []
  /-- `LOCALS valtype*`: syntactic value types, never `BOT` (see the module
  doc). -/
  locals : List ValType := []
  /-- `LABELS resulttype*`, innermost label first, as in `{LABELS (t*)} ++ C`
  (`6-typing:216`). -/
  labels : List CResultType := []
  /-- `RETURN resulttype?`. -/
  return_ : Option CResultType := none
  /-- `REFS funcidx*`: the functions that `ref.func` may name. Not in the
  pinned SpecTec 2.0 source; see the module doc. -/
  refs : List FuncIdx := []
  deriving DecidableEq, Repr

instance : Inhabited Context := ⟨{}⟩

namespace Context

/-- `{LABELS (t*)} ++ C`, as used by `Instr_ok/block`, `/loop` and `/if`
(`6-typing:216`, `221`, `227-228`).

The left operand is a singleton record, so field-wise concatenation leaves every
field of `C` alone except `LABELS`, where the new label is prepended: index `0`
is the innermost label, which is what `C.LABELS[l]` means for a relative label
index `l`. -/
def withLabel (C : Context) (ts : CResultType) : Context :=
  { C with labels := ts :: C.labels }

/-- `C ++ {LOCALS t_1* t*, LABELS (t_2*), RETURN (t_2*)}`, the function-entry
context of `Func_ok` (`6-typing:596`).

Here `C` is the *left* operand, so field-wise concatenation appends the new
locals *after* `C.LOCALS` and the new label *after* `C.LABELS`. `RETURN` is an
option, and concatenating two present options is not well formed; at the single
use site `C` is the module-level context of `Module_ok` (`6-typing:701`), whose
`LOCALS`, `LABELS` and `RETURN` are all empty, so every field is in effect
*set*. We implement the append for `locals` and `labels` and the set for
`return_`, which agrees with SpecTec wherever SpecTec is defined. -/
def withFuncFrame (C : Context) (locals : List ValType) (label ret : CResultType) : Context :=
  { C with locals := C.locals ++ locals, labels := C.labels ++ [label], return_ := some ret }

end Context

/-! ## Instruction types -/

/-- `functype = resulttype -> resulttype` (`1-syntax:169`) at the validation
value type: the type assigned to an instruction or an instruction sequence by
`Instr_ok`/`Instrs_ok` (`6-typing:142-143`). Both sides are bottom-first
stacks. -/
structure InstrType where
  /-- The operand types consumed, bottom-first. -/
  params : CResultType
  /-- The operand types produced, bottom-first. -/
  results : CResultType
  deriving DecidableEq, Repr

namespace InstrType

/-- `t_1* -> t_2*` built from syntactic result types. -/
abbrev lift (params results : ResultType) : InstrType :=
  ⟨liftResult params, liftResult results⟩

/-- `Instrs_ok/sub` (`6-typing:168`) read as subtyping of instruction types.

The rule derives the *conclusion* `C |- instr* : t'_1* -> t'_2*` from the
*premise* `C |- instr* : t_1* -> t_2*` together with `|- t'_1* <: t_1*` and
`|- t_2* <: t'_2*`. So the weaker type `t'_1* -> t'_2*` has **smaller**
parameters and **larger** results: the relation is contravariant in `params`
and covariant in `results`. `InstrType.Sub it it'` holds when `it'` is the
weaker type, i.e. `it'.params <: it.params` and `it.results <: it'.results`,
matching `Silmaril.Wasm.Validation.InstrTypeSub`. -/
def Sub (it it' : InstrType) : Prop :=
  CResultType.Sub it'.params it.params ∧ CResultType.Sub it.results it'.results

instance (it it' : InstrType) : Decidable (InstrType.Sub it it') :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem sub_refl (it : InstrType) : InstrType.Sub it it :=
  ⟨CResultType.sub_refl _, CResultType.sub_refl _⟩

theorem sub_trans {a b c : InstrType} (h₁ : InstrType.Sub a b) (h₂ : InstrType.Sub b c) :
    InstrType.Sub a c :=
  ⟨CResultType.sub_trans h₂.1 h₁.1, CResultType.sub_trans h₁.2 h₂.2⟩

/-- Well-formedness of an instruction type. SpecTec 2.0 has no `Instrtype_ok`
relation; the corresponding judgment on the underlying `functype` is
`Functype_ok` (`6-typing:32`), which has no premises, and 2.0 value types carry
no type indices that could dangle. So every instruction type is well formed.
The judgment is kept as a named definition because the Core 3.0 layer's
`InstrTypeOk` is non-trivial and the subset theorems line the two up. -/
def Ok (_it : InstrType) : Prop := True

instance (it : InstrType) : Decidable (InstrType.Ok it) := by
  unfold InstrType.Ok; infer_instance

theorem ok (it : InstrType) : InstrType.Ok it := trivial

end InstrType

/-! ## Block types -/

/-- `Blocktype_ok: context |- blocktype : functype` (`6-typing:203`), with its
two rules.

* `/valtype` (`6-typing:205`): `C |- _RESULT valtype? : eps -> valtype?`.
* `/typeidx` (`6-typing:208`): `C |- _IDX typeidx : t_1* -> t_2*` provided
  `C.TYPES[typeidx] = t_1* -> t_2*`. An out-of-range index makes the premise
  undefined, so no rule applies and the block type is ill formed. -/
inductive BlockTypeOk (C : Context) : BlockType → InstrType → Prop where
  /-- `Blocktype_ok/valtype` (`6-typing:205`). -/
  | result (t : Option ValType) : BlockTypeOk C (.result t) ⟨[], liftResult t.toList⟩
  /-- `Blocktype_ok/typeidx` (`6-typing:208`). -/
  | typeIdx {x : TypeIdx} {ft : FuncType} (h : C.types[x.toNat]? = some ft) :
      BlockTypeOk C (.typeIdx x) (InstrType.lift ft.params ft.results)

/-! ## Memory argument alignment

The side conditions `$(2^(memarg.ALIGN) <= N/8)` attached to every memory
instruction (`6-typing:468-532`). `N` is a *bit* width and `/` is natural-number
division, so the condition bounds the alignment by the access size in bytes;
for the packed widths used in 2.0 (`8`, `16`, `32`, `64`, `128`) the division is
exact. SpecTec 2.0 attaches no bound to `memarg.OFFSET`: the offset is a `u32`
and 2.0 memories are 32-bit, so the Core 3.0 premise `memarg.OFFSET < 2^|at|`
has no 2.0 counterpart. -/

/-- `$(2^(memarg.ALIGN) <= N/8)` for an access of `N` bits, as in
`Instr_ok/load-val` (`6-typing:468`), `/load-pack` (`6-typing:473`),
`/store-val` (`6-typing:487`), `/vload-splat` (`6-typing:507`),
`/vload_lane` (`6-typing:517`) and `/vstore` (`6-typing:523`). -/
def MemArgOk (arg : MemArg) (N : Nat) : Prop := 2 ^ arg.align.val ≤ N / 8

instance (arg : MemArg) (N : Nat) : Decidable (MemArgOk arg N) := by
  unfold MemArgOk; infer_instance

/-- `$(2^(memarg.ALIGN) <= M/8 * N)` of `Instr_ok/vload-pack` (`6-typing:502`),
where the operand is `N` lanes of `M` bits each. Note that SpecTec divides
*before* multiplying; for `M \in {8, 16, 32}` this agrees with
`MemArgOk arg (M * N)`. -/
def MemArgOkPack (arg : MemArg) (M N : Nat) : Prop := 2 ^ arg.align.val ≤ M / 8 * N

instance (arg : MemArg) (M N : Nat) : Decidable (MemArgOkPack arg M N) := by
  unfold MemArgOkPack; infer_instance

end Silmaril.Wasm.V2.Validation
