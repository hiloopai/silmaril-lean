module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryValues
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryTypes
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Numerics
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary.Instructions
public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary.Modules
-- `spectec_import` and `spectec_erratum` add their constants with
-- `Lean.addDecl`, which bypasses the `@[expose]` of the section they sit in,
-- so the *values* of `Specs.wasm10` and `Wasm10.wasm10corrected` are not
-- visible to an importing module without these two lines; they are what makes
-- the provenance theorems below `rfl`s the kernel can actually do.
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10

/-!
# The corrected wasm-1.0 binary grammar, against `Silmaril/Wasm/V1/`

`Silmaril/SpecTec/Equiv/BinaryValues.lean` and
`Silmaril/SpecTec/Equiv/BinaryTypes.lean` do this for wasm-3.0.  This file is
the wasm-1.0 counterpart: it compares the denotation of
`Silmaril.SpecTec.IL.Wasm10.wasm10corrected` — the pinned wasm-1.0 stream with
the seven errata of `#679` applied — with
`Silmaril/Wasm/V1/Binary/`, Silmaril's hand-written transcription of the W3C
Recommendation of 5 December 2019, through the `Encode` bridge of
`Silmaril/SpecTec/Sem/Bridge.lean`.

Everything is relative to the pin `608711107b7f1edb13efd57b7d79b49477462d36`.
Bare line citations `A-binary:n` are line `n` of
`specification/wasm-1.0/A-binary.spectec`; `1-syntax.spectec` is its sibling.

## Why wasm-1.0 is the version where this reaches furthest

wasm-1.0's §A is 541 lines against wasm-3.0's four §5.x files, its errata are
already applied (`Silmaril/SpecTec/Errata/Wasm10.lean`), and its type system
has no reference types, no vectors and no recursive types.  The §5.2 defect
that `Equiv/BinaryTypes.lean` reports — `$s33_to_u32` declared and never
defined, which makes every concrete type reference unreachable in wasm-3.0 —
has no wasm-1.0 analogue, because wasm-1.0's `Bvaltype` (`A-binary:85-89`) is
four byte terminals.

## Two verdicts carried over from wasm-3.0

**`#654` does not apply to wasm-1.0.**  `A-binary:40-41` already reads
`grammar Bi32 : i32 = BiN(32)`, the *signed* grammar; the `BuN(32)` of
`wasm-3.0/5.1-binary.values.spectec:31` is a 3.0-only regression.
`hasCorrectedBi_v1` is that, by `rfl` against the stream: wasm-1.0 satisfies
`Equiv.HasCorrectedBi` with no patch at all.

**The `BsN` defect *does* apply to wasm-1.0, unchanged.**  The elaborated
`BuN`, `BsN`, `BiN`, `Bbyte`, `Blist` and `Bname` of `specs/spectec/wasm-1.0.ast`
are **byte-identical** to those of `specs/spectec/wasm-3.0.ast` — the two
specifications' §5.1/§A sources agree there, and `--ast` prints the same
characters.  Every statement `Equiv/BinaryValues.lean` makes about them
therefore transports verbatim; `hasLeb_v1` and `hasSignedLeb_v1` are the two
`rfl`s that do it.  In wasm-1.0 the consequence is *sharper* than in 3.0,
because 1.0's `Bi32` is already `BiN(32)`: the signed grammar is the only
thing standing between the specification and `Silmaril.Wasm.Binary.IN 32`, and
it loses every multi-byte negative encoding.  `bi32_v1_disagrees_with_in` is
the corrected wasm-1.0 specification disagreeing with `IN 32`, with nothing
left to patch at the `Bi32` level.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.V1Binary

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Binary

set_option maxRecDepth 4000000

/-! ## The script and its environment -/

/-- The corrected wasm-1.0 specification: `Silmaril.SpecTec.Specs.wasm10` with
the seven errata of `#679` that are expressible as AST
patches (`Silmaril/SpecTec/Errata/Wasm10.lean`). -/
noncomputable abbrev wasm10corrected : Script := IL.Wasm10.wasm10corrected

/-- The environment every theorem below about the corrected specification is
stated at. -/
noncomputable abbrev envV1 : Env := envOfScript wasm10corrected

/-! ## Provenance: the productions, read out of the corrected stream

Each `private` theorem below is a `rfl` against the actual script, and nothing
else in this file reads the stream.  They are `private` for the reason
`Equiv/BinaryValues.lean` gives: `Specs.wasm10` is added with `Lean.addDecl`
and is not exposed to importers. -/

private theorem findGram_bbyte_v1 :
    envV1.findGram? "Bbyte" = some ([], .varT "byte" [], bbyteProds) := rfl

private theorem findGram_bun_v1 :
    envV1.findGram? "BuN" = some (bunParams, bunTyp, bunProds) := rfl

private theorem findGram_bsn_v1 :
    envV1.findGram? "BsN" = some (bsnParams, bsnTyp, bsnProds) := rfl

private theorem findGram_bin_v1 :
    envV1.findGram? "BiN"
      = some (bsnParams, .varT "iN" [.expA (.varE "N")], binProds) := rfl

private theorem findGram_bu32_v1 :
    envV1.findGram? "Bu32"
      = some ([], .varT "u32" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 32))]) "BuN" (.numE (.natN 32))) := rfl

private theorem findGram_bu64_v1 :
    envV1.findGram? "Bu64"
      = some ([], .varT "u64" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 64))]) "BuN" (.numE (.natN 64))) := rfl

private theorem findGram_bi32_v1 :
    envV1.findGram? "Bi32"
      = some ([], .varT "i32" [],
          wrapProds (.varT "iN" [.expA (.numE (.natN 32))]) "BiN" (.numE (.natN 32))) := rfl

private theorem findGram_bi64_v1 :
    envV1.findGram? "Bi64"
      = some ([], .varT "i64" [],
          wrapProds (.varT "iN" [.expA (.numE (.natN 64))]) "BiN" (.numE (.natN 64))) := rfl

/-- **`Bbyte` and `BuN` are the ones `Sem/Grammar.lean` proves about.**  The
elaborated wasm-1.0 and wasm-3.0 streams agree on them character for
character, so `bun_iff_un` applies to wasm-1.0 unchanged. -/
theorem hasLeb_v1 : HasLeb envV1 := ⟨findGram_bbyte_v1, findGram_bun_v1⟩

/-- **`BsN` and `BiN` are the ones `Equiv/BinaryValues.lean` proves about.**
Same productions, same elaboration, same defect. -/
theorem hasSignedLeb_v1 : HasSignedLeb envV1 := ⟨findGram_bsn_v1, findGram_bin_v1⟩

/-- **wasm-1.0 does not have `#654`.**  `A-binary:40-41` already uses the
signed grammar, so the corrected wasm-1.0 script satisfies
`Equiv.HasCorrectedBi` with no patch. -/
theorem hasCorrectedBi_v1 : HasCorrectedBi envV1 := ⟨findGram_bi32_v1, findGram_bi64_v1⟩

/-! ## The values section

`A-binary:18-44`.  `Bbyte`, `BuN`, `BsN` and `BiN` are the definitions
`Equiv/BinaryValues.lean` characterises; the four one-line wrappers are the
same `wrapProds` shape as wasm-3.0's. -/

/-- **`Bbyte` is `Silmaril.Wasm.Binary.Byte`** (`A-binary:18`). -/
theorem bbyte_iff_byte_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bbyte" []) bs v ↔
      ∃ b : UInt8, Byte bs b ∧ v = Encode.toValue b :=
  bbyte_iff_byte hasLeb_v1 ρ bs v

/-- **`BuN(N)` is `Silmaril.Wasm.Binary.UN N`** (`A-binary:20-22`). -/
theorem bun_iff_un_v1 (W : Nat) (bs : Grammar.Bytes) (v : Value) (ρ : VarEnv) :
    gramRelSup envV1 ρ (.varG "BuN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ m, UN W bs m ∧ v = uNV m :=
  bun_iff_un hasLeb_v1 W bs v ρ

/-- **`Bu32` is `Silmaril.Wasm.Binary.U32`** (`A-binary:37`). -/
theorem bu32_iff_u32_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bu32" []) bs v ↔ ∃ m, U32 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff findGram_bu32_v1 hasLeb_v1.bun ρ bs v]
  exact bun_iff_un_v1 32 bs v VarEnv.empty

/-- **`Bu64` is `Silmaril.Wasm.Binary.U64`** (`A-binary:38`). -/
theorem bu64_iff_u64_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bu64" []) bs v ↔ ∃ m, U64 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff findGram_bu64_v1 hasLeb_v1.bun ρ bs v]
  exact bun_iff_un_v1 64 bs v VarEnv.empty

/-! ### `BsN`: the wasm-3.0 defect, in wasm-1.0

`A-binary:24-27` is the same three productions as
`wasm-3.0/5.1-binary.values.spectec:14-16`, and SpecTec elaborates them to the
same IL: the third production infers its arithmetic at `nat`, so it narrows
the recursive `sN` value with `cvt int nat` before multiplying, and
`Xl.Num.cvt` (`spectec/src/xl/num.ml:86`) is undefined on a negative integer.
`Equiv/BinaryValues.lean`'s `bsn_iff_sn` is therefore exactly the
characterisation of wasm-1.0's `BsN` too. -/

/-- **The corrected wasm-1.0 `BsN(N)` is `Silmaril.Wasm.Binary.SN N`
restricted to single-byte encodings and non-negative values, exactly.** -/
theorem bsn_iff_sn_v1 (W : Nat) (hW : 0 < W) (bs : Grammar.Bytes) (v : Value) (ρ : VarEnv) :
    gramRelSup envV1 ρ (.varG "BsN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ i, SN W bs i ∧ (0 ≤ i ∨ bs.length = 1) ∧ v = sNV i :=
  bsn_iff_sn hasLeb_v1 hasSignedLeb_v1 W hW bs v ρ

/-- **The corrected wasm-1.0 `BsN(32)` derives nothing from `FF 7E`**, the
two-byte signed LEB128 encoding of `-129`. -/
theorem not_bsn_FF7E_v1 (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envV1 ρ (.varG "BsN" [.expA (.numE (.natN 32))]) [0xFF, 0x7E] v :=
  not_bsn_FF7E hasLeb_v1 hasSignedLeb_v1 ρ v

/-- **The corrected wasm-1.0 `Bi32` derives nothing from `FF 7E`** either:
`Bi32 = BiN(32)` and `BiN`'s byte language is `BsN`'s. -/
theorem not_bi32_FF7E_v1 (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envV1 ρ (.varG "Bi32" []) [0xFF, 0x7E] v := by
  intro hd
  rw [wrap_rel_iff hasCorrectedBi_v1.bi32 hasSignedLeb_v1.bin ρ _ v] at hd
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
  exact not_bin_FF7E hasLeb_v1 hasSignedLeb_v1 VarEnv.empty ρ' v hd

/-- **The verdict.**  wasm-1.0 has no `#654` to apply and its `Bi32` is
already the signed grammar, yet the corrected wasm-1.0 specification still
disagrees with `Silmaril.Wasm.Binary.IN 32`: `FF 7E`, the encoding of
`i32.const -129`, has no derivation at all.  Unlike wasm-3.0, where
`bi32_corrected_disagrees_with_in` can be read as "`#654` is necessary but not
sufficient", here there is no patch in flight and `BsN` is the sole cause. -/
theorem bi32_v1_disagrees_with_in (ρ : VarEnv) :
    ¬ ∀ (bs : Grammar.Bytes) (v : Value),
        gramRelSup envV1 ρ (.varG "Bi32" []) bs v ↔
          ∃ bv : BitVec 32, IN 32 bs bv ∧ v = iNV bv := by
  intro h
  exact not_bi32_FF7E_v1 ρ (iNV (BitVec.ofInt 32 (-129)))
    ((h [0xFF, 0x7E] _).mpr ⟨BitVec.ofInt 32 (-129), in32_FF7E, rfl⟩)

/-- The same for `Bi64` and `IN 64`: `FF 7E` is `i64.const -129`. -/
theorem not_bi64_FF7E_v1 (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envV1 ρ (.varG "Bi64" []) [0xFF, 0x7E] v := by
  intro hd
  rw [wrap_rel_iff hasCorrectedBi_v1.bi64 hasSignedLeb_v1.bin ρ _ v] at hd
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
  obtain ⟨w, ρa, hinner⟩ := bsn_of_bin hasSignedLeb_v1 hd
  obtain ⟨i, hi, hcond, -⟩ := sn_of_bsn hasLeb_v1 hasSignedLeb_v1 64 (by omega)
    (evalExp_varE_iff.mpr (findVal_bunScope_N 64)) hinner
  have hieq : i = -129 := SN.functional 64 hi (SN.mono (by omega) sn32_FF7E)
  rcases hcond with hc | hc
  · rw [hieq] at hc; exact absurd hc (by decide)
  · exact absurd hc (by decide)


/-! ## The types section: the productions

`A-binary:85-126`.  wasm-1.0 has four value types and no reference types, so
`Bvaltype` is a byte table; `mut`, `limits`, `globaltype`, `tabletype` and
`memtype` are the shapes `1-syntax.spectec:108-130` declares. -/

/-- The four productions of `grammar Bvaltype : valtype` (`A-binary:85-89`). -/
def bvaltypeV1Prods : List IL.Prod :=
  [ .prodD [] (.numG 0x7F) (.caseE "I32" (.tupE [])) [],
    .prodD [] (.numG 0x7E) (.caseE "I64" (.tupE [])) [],
    .prodD [] (.numG 0x7D) (.caseE "F32" (.tupE [])) [],
    .prodD [] (.numG 0x7C) (.caseE "F64" (.tupE [])) [] ]

/-- The two productions of `grammar Bmut : mut` (`A-binary:104-106`).
`1-syntax.spectec:119` makes `mut` the *option* `MUT?`, so the value is an
`opt`. -/
def bmutV1Prods : List IL.Prod :=
  [ .prodD [] (.numG 0x00) (.optE none) [],
    .prodD [] (.numG 0x01) (.optE (some (.caseE "MUT" (.tupE [])))) [] ]

/-- The two productions of `grammar Blimits : limits` (`A-binary:108-110`).
Both bounds are `Bu32`, not wasm-3.0's `Bu64`, and there is no address type:
`1-syntax.spectec:121-122` is `` `[u32 .. u32?] ``. -/
def blimitsV1Prods : List IL.Prod :=
  [ .prodD [.expP "n" (.varT "n" [])]
      (.seqG [.seqG [.numG 0x00],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])]])
      (.caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]), .optE none])) [],
    .prodD [.expP "n" (.varT "n" []), .expP "m" (.varT "m" [])]
      (.seqG [.seqG [.numG 0x01],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "m"])) (.varG "Bu32" [])]])
      (.caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]),
        .optE (some (.caseE "%" (.tupE [.varE "m"])))])) [] ]

/-- The sole production of `grammar Bglobaltype : globaltype`
(`A-binary:112-113`).  The value type comes first in the bytes and second in
the `%%` injection, as `1-syntax.spectec:123-124` has it. -/
def bglobaltypeV1Prods : List IL.Prod :=
  [ .prodD [.expP "mut" (.varT "mut" []), .expP "t" (.varT "valtype" [])]
      (.seqG [.seqG [.attrG (.varE "t") (.varG "Bvaltype" [])],
              .seqG [.attrG (.varE "mut") (.varG "Bmut" [])]])
      (.caseE "%%" (.tupE [.varE "mut", .varE "t"])) [] ]

/-- The sole production of `grammar Btabletype : tabletype`
(`A-binary:115-116`).  `0x70` is the only element type, and
`1-syntax.spectec:127-128` makes `tabletype` an alias of `limits`, so the
production's value is the limits. -/
def btabletypeV1Prods : List IL.Prod :=
  [ .prodD [.expP "lim" (.varT "limits" [])]
      (.seqG [.seqG [.numG 0x70], .seqG [.attrG (.varE "lim") (.varG "Blimits" [])]])
      (.varE "lim") [] ]

/-- The sole production of `grammar Bmemtype : memtype` (`A-binary:118-119`):
`memtype` is an alias of `limits` too (`1-syntax.spectec:129-130`). -/
def bmemtypeV1Prods : List IL.Prod :=
  [ .prodD [.expP "lim" (.varT "limits" [])]
      (.attrG (.varE "lim") (.varG "Blimits" [])) (.varE "lim") [] ]

/-- The two productions of `grammar Bblocktype : blocktype`
(`A-binary:135-137`).  `1-syntax.spectec:195` makes `blocktype` the option
`valtype?`; wasm-1.0 has no `s33` form. -/
def bblocktypeV1Prods : List IL.Prod :=
  [ .prodD [] (.numG 0x40) (.optE none) [],
    .prodD [.expP "t" (.varT "valtype" [])]
      (.attrG (.varE "t") (.varG "Bvaltype" [])) (.optE (some (.varE "t"))) [] ]

/-- The sole production of `grammar Bmemarg : memarg` (`A-binary:179-180`),
whose value is the struct `{ALIGN u32, OFFSET u32}`
(`1-syntax.spectec:185`). -/
def bmemargV1Prods : List IL.Prod :=
  [ .prodD [.expP "n" (.varT "n" []), .expP "m" (.varT "m" [])]
      (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "m"])) (.varG "Bu32" [])]])
      (.strE [.mk "ALIGN" (.caseE "%" (.tupE [.varE "n"])),
              .mk "OFFSET" (.caseE "%" (.tupE [.varE "m"]))]) [] ]

/-- The four productions of `grammar Bexternidx : externidx`
(`A-binary:72-76`). -/
def bexternidxV1Prods : List IL.Prod :=
  [ .prodD [.expP "x" (.varT "idx" [])]
      (.seqG [.seqG [.numG 0x00], .seqG [.attrG (.varE "x") (.varG "Bfuncidx" [])]])
      (.caseE "FUNC" (.varE "x")) [],
    .prodD [.expP "x" (.varT "idx" [])]
      (.seqG [.seqG [.numG 0x01], .seqG [.attrG (.varE "x") (.varG "Btableidx" [])]])
      (.caseE "TABLE" (.varE "x")) [],
    .prodD [.expP "x" (.varT "idx" [])]
      (.seqG [.seqG [.numG 0x02], .seqG [.attrG (.varE "x") (.varG "Bmemidx" [])]])
      (.caseE "MEM" (.varE "x")) [],
    .prodD [.expP "x" (.varT "idx" [])]
      (.seqG [.seqG [.numG 0x03], .seqG [.attrG (.varE "x") (.varG "Bglobalidx" [])]])
      (.caseE "GLOBAL" (.varE "x")) [] ]

/-! ## Provenance for the types section -/

private theorem findGram_bu32_prods_v1 :
    envV1.findGram? "Bu32" = some ([], .varT "u32" [], bu32Prods) := findGram_bu32_v1

private theorem findGram_bu64_prods_v1 :
    envV1.findGram? "Bu64" = some ([], .varT "u64" [], bu64Prods) := findGram_bu64_v1

private theorem findGram_btypeidx_v1 :
    envV1.findGram? "Btypeidx" = some ([], .varT "typeidx" [], btypeidxProds) := rfl

private theorem findGram_bfuncidx_v1 :
    envV1.findGram? "Bfuncidx" = some ([], .varT "funcidx" [], btypeidxProds) := rfl

private theorem findGram_bglobalidx_v1 :
    envV1.findGram? "Bglobalidx" = some ([], .varT "globalidx" [], btypeidxProds) := rfl

private theorem findGram_btableidx_v1 :
    envV1.findGram? "Btableidx" = some ([], .varT "tableidx" [], btypeidxProds) := rfl

private theorem findGram_bmemidx_v1 :
    envV1.findGram? "Bmemidx" = some ([], .varT "memidx" [], btypeidxProds) := rfl

private theorem findGram_blocalidx_v1 :
    envV1.findGram? "Blocalidx" = some ([], .varT "localidx" [], btypeidxProds) := rfl

private theorem findGram_blabelidx_v1 :
    envV1.findGram? "Blabelidx" = some ([], .varT "labelidx" [], btypeidxProds) := rfl

private theorem findGram_bvaltype_v1 :
    envV1.findGram? "Bvaltype" = some ([], .varT "valtype" [], bvaltypeV1Prods) := rfl

private theorem findGram_bmut_v1 :
    envV1.findGram? "Bmut" = some ([], .varT "mut" [], bmutV1Prods) := rfl

private theorem findGram_blimits_v1 :
    envV1.findGram? "Blimits" = some ([], .varT "limits" [], blimitsV1Prods) := rfl

private theorem findGram_bglobaltype_v1 :
    envV1.findGram? "Bglobaltype" = some ([], .varT "globaltype" [], bglobaltypeV1Prods) := rfl

private theorem findGram_btabletype_v1 :
    envV1.findGram? "Btabletype" = some ([], .varT "tabletype" [], btabletypeV1Prods) := rfl

private theorem findGram_bmemtype_v1 :
    envV1.findGram? "Bmemtype" = some ([], .varT "memtype" [], bmemtypeV1Prods) := rfl

private theorem findGram_bblocktype_v1 :
    envV1.findGram? "Bblocktype" = some ([], .varT "blocktype" [], bblocktypeV1Prods) := rfl

private theorem findGram_bmemarg_v1 :
    envV1.findGram? "Bmemarg" = some ([], .varT "memarg" [], bmemargV1Prods) := rfl

private theorem findGram_bexternidx_v1 :
    envV1.findGram? "Bexternidx" = some ([], .varT "externidx" [], bexternidxV1Prods) := rfl


/-! ## The bridge for the wasm-1.0 types

`Equiv/BinaryTypes.lean` already supplies `Encode` for `Wasm.NumType` —
which **is** `Wasm.V1.ValType` (`Silmaril/Wasm/V1/Types.lean:20`) — for
`Wasm.Mutability` and for `Wasm.Idx`, and `Sem/Bridge.lean` supplies the
`Option` instance that `blocktype = valtype?` needs.  What is new here is the
32-bit limits bound and the four wasm-1.0 type structures. -/

/-- A limits bound, which is `u32` in wasm-1.0 (`1-syntax.spectec:121-122`)
where wasm-3.0 has a `u64`. -/
def fin32OfNat? (n : Nat) : Option (Fin (2 ^ 32)) :=
  if h : n < 2 ^ 32 then some ⟨n, h⟩ else none

/-- `u32` as a `%`-wrapped numeral, at the Lean type both `Wasm.V1.Limits`
bounds use. -/
instance instEncodeFin32 : Encode (Fin (2 ^ 32)) :=
  Encode.ofPercentNat Fin.val fin32OfNat?
    (fun n => by simp [fin32OfNat?])
    (fun n i h => by
      simp only [fin32OfNat?] at h
      split at h
      · cases h; rfl
      · exact absurd h (by simp))

/-- `limits` (`1-syntax.spectec:121-122`), `` `[u32 .. u32?] ``. -/
instance instEncodeV1Limits : Encode Wasm.V1.Limits :=
  Encode.ofCase
    (fun l => ("[%..%]", .tuple [Encode.toValue l.min, Encode.toValue l.max]))
    (fun op v => match op, v with
      | "[%..%]", .tuple [a, b] =>
          (Encode.ofValue (α := Fin (2 ^ 32)) a).bind fun n =>
            (Encode.ofValue (α := Option (Fin (2 ^ 32))) b).bind fun m => some ⟨n, m⟩
      | _, _ => none)
    (by
      rintro ⟨n, m⟩
      simp only [Encode.ofValue_toValue]
      rfl)
    (by
      intro op v a h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨x, hx, y, hy, rfl⟩ := h
        rw [Encode.toValue_eq_of_ofValue hx, Encode.toValue_eq_of_ofValue hy]
      · exact absurd h (by simp))

/-- `memtype` is an *alias* of `limits` (`1-syntax.spectec:129-130`), so a
`Wasm.V1.MemoryType` encodes as its limits and nothing more. -/
instance instEncodeV1MemoryType : Encode Wasm.V1.MemoryType where
  toValue m := Encode.toValue m.limits
  ofValue v := (Encode.ofValue (α := Wasm.V1.Limits) v).map Wasm.V1.MemoryType.mk
  ofValue_toValue a := by cases a; simp [Encode.ofValue_toValue]
  toValue_ofValue v a h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact Encode.toValue_eq_of_ofValue hl

/-- `tabletype` is an alias of `limits` too (`1-syntax.spectec:127-128`):
wasm-1.0 has a single element type, carried by the `0x70` terminal of
`A-binary:112-113` and not by the abstract syntax. -/
instance instEncodeV1TableType : Encode Wasm.V1.TableType where
  toValue t := Encode.toValue t.limits
  ofValue v := (Encode.ofValue (α := Wasm.V1.Limits) v).map Wasm.V1.TableType.mk
  ofValue_toValue a := by cases a; simp [Encode.ofValue_toValue]
  toValue_ofValue v a h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact Encode.toValue_eq_of_ofValue hl

/-- `globaltype = mut valtype` (`1-syntax.spectec:123-124`). -/
instance instEncodeV1GlobalType : Encode Wasm.V1.GlobalType :=
  Encode.ofCase
    (fun g => ("%%", .tuple [Encode.toValue g.mutability, Encode.toValue g.value]))
    (fun op v => match op, v with
      | "%%", .tuple [a, b] =>
          (Encode.ofValue (α := Wasm.Mutability) a).bind fun m =>
            (Encode.ofValue (α := Wasm.V1.ValType) b).bind fun t => some ⟨m, t⟩
      | _, _ => none)
    (by
      rintro ⟨m, t⟩
      simp only [Encode.ofValue_toValue]
      rfl)
    (by
      intro op v a h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨x, hx, y, hy, rfl⟩ := h
        rw [Encode.toValue_eq_of_ofValue hx, Encode.toValue_eq_of_ofValue hy]
      · exact absurd h (by simp))

/-- `externidx` (`1-syntax.spectec:282-283`): a one-component injection of an
index, with no tuple around it — `A-binary:72-76` spells the value
`FUNC x`, not `FUNC (x)`. -/
instance instEncodeV1ExternIdx : Encode Wasm.V1.ExternIdx :=
  Encode.ofCase
    (fun e => match e with
      | .func x => ("FUNC", Encode.toValue x)
      | .table x => ("TABLE", Encode.toValue x)
      | .memory x => ("MEM", Encode.toValue x)
      | .global x => ("GLOBAL", Encode.toValue x))
    (fun op v => match op, v with
      | "FUNC", w => (Encode.ofValue (α := Wasm.FuncIdx) w).map .func
      | "TABLE", w => (Encode.ofValue (α := Wasm.TableIdx) w).map .table
      | "MEM", w => (Encode.ofValue (α := Wasm.MemIdx) w).map .memory
      | "GLOBAL", w => (Encode.ofValue (α := Wasm.GlobalIdx) w).map .global
      | _, _ => none)
    (by intro a; cases a <;> simp [Encode.ofValue_toValue])
    (by
      intro op v a h
      split at h
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
        exact congrArg (fun w => ("FUNC", w)) (Encode.toValue_eq_of_ofValue hx)
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
        exact congrArg (fun w => ("TABLE", w)) (Encode.toValue_eq_of_ofValue hx)
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
        exact congrArg (fun w => ("MEM", w)) (Encode.toValue_eq_of_ofValue hx)
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
        exact congrArg (fun w => ("GLOBAL", w)) (Encode.toValue_eq_of_ofValue hx)
      · exact absurd h (by simp))


/-! ## The hypotheses on an environment

As in `Equiv/BinaryTypes.lean`, every result below is stated for an arbitrary
environment that defines the nonterminals it uses exactly as the corrected
stream does, so that no proof depends on the other 300-odd definitions. -/

/-- An environment whose wasm-1.0 index, value and type nonterminals are the
corrected stream's. -/
structure HasV1Types (env : Env) : Prop where
  /-- `Bu32 = BuN(32)` (`A-binary:37`). -/
  bu32 : env.findGram? "Bu32" = some ([], .varT "u32" [], bu32Prods)
  /-- `Bu64 = BuN(64)` (`A-binary:38`). -/
  bu64 : env.findGram? "Bu64" = some ([], .varT "u64" [], bu64Prods)
  /-- `Btypeidx` (`A-binary:64`). -/
  btypeidx : env.findGram? "Btypeidx" = some ([], .varT "typeidx" [], btypeidxProds)
  /-- `Bfuncidx` (`A-binary:65`). -/
  bfuncidx : env.findGram? "Bfuncidx" = some ([], .varT "funcidx" [], btypeidxProds)
  /-- `Bglobalidx` (`A-binary:66`). -/
  bglobalidx : env.findGram? "Bglobalidx" = some ([], .varT "globalidx" [], btypeidxProds)
  /-- `Btableidx` (`A-binary:67`). -/
  btableidx : env.findGram? "Btableidx" = some ([], .varT "tableidx" [], btypeidxProds)
  /-- `Bmemidx` (`A-binary:68`). -/
  bmemidx : env.findGram? "Bmemidx" = some ([], .varT "memidx" [], btypeidxProds)
  /-- `Blocalidx` (`A-binary:69`). -/
  blocalidx : env.findGram? "Blocalidx" = some ([], .varT "localidx" [], btypeidxProds)
  /-- `Blabelidx` (`A-binary:70`). -/
  blabelidx : env.findGram? "Blabelidx" = some ([], .varT "labelidx" [], btypeidxProds)
  /-- `Bvaltype` (`A-binary:85-89`). -/
  bvaltype : env.findGram? "Bvaltype" = some ([], .varT "valtype" [], bvaltypeV1Prods)
  /-- `Bmut` (`A-binary:104-106`). -/
  bmut : env.findGram? "Bmut" = some ([], .varT "mut" [], bmutV1Prods)
  /-- `Blimits` (`A-binary:108-110`). -/
  blimits : env.findGram? "Blimits" = some ([], .varT "limits" [], blimitsV1Prods)
  /-- `Bglobaltype` (`A-binary:112-113`). -/
  bglobaltype : env.findGram? "Bglobaltype" = some ([], .varT "globaltype" [], bglobaltypeV1Prods)
  /-- `Btabletype` (`A-binary:115-116`). -/
  btabletype : env.findGram? "Btabletype" = some ([], .varT "tabletype" [], btabletypeV1Prods)
  /-- `Bmemtype` (`A-binary:118-119`). -/
  bmemtype : env.findGram? "Bmemtype" = some ([], .varT "memtype" [], bmemtypeV1Prods)
  /-- `Bblocktype` (`A-binary:135-137`). -/
  bblocktype : env.findGram? "Bblocktype" = some ([], .varT "blocktype" [], bblocktypeV1Prods)
  /-- `Bexternidx` (`A-binary:72-76`). -/
  bexternidx : env.findGram? "Bexternidx" = some ([], .varT "externidx" [], bexternidxV1Prods)

/-- The corrected wasm-1.0 environment satisfies it, by `rfl` against the
stream. -/
theorem hasV1Types_v1 : HasV1Types envV1 :=
  ⟨findGram_bu32_prods_v1, findGram_bu64_prods_v1, findGram_btypeidx_v1,
    findGram_bfuncidx_v1, findGram_bglobalidx_v1, findGram_btableidx_v1,
    findGram_bmemidx_v1, findGram_blocalidx_v1, findGram_blabelidx_v1,
    findGram_bvaltype_v1, findGram_bmut_v1, findGram_blimits_v1,
    findGram_bglobaltype_v1, findGram_btabletype_v1, findGram_bmemtype_v1,
    findGram_bblocktype_v1, findGram_bexternidx_v1⟩

/-! ## The `u32` wrappers and the index grammars -/

/-- `grammar Bu32 : u32 = BuN(32)` is `Silmaril.Wasm.Binary.U32`, as a
`SymDerives`. -/
theorem symDerives_bu32_v1 {env : Env} (h : HasV1Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bu32" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ m, U32 bs m ∧ l = [numCase m] := by
  rw [symDerives_wrapper rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hd => ((symDerives_varG hl.bun).mp hd).1) h.bu32]
  constructor
  · rintro ⟨rfl, w, hw, rfl⟩
    obtain ⟨m, hm, rfl⟩ := (symDerives_bun hl).mp hw
    exact ⟨rfl, m, hm, rfl⟩
  · rintro ⟨rfl, m, hm, rfl⟩
    exact ⟨rfl, _, (symDerives_bun hl).mpr ⟨m, hm, rfl⟩, rfl⟩

/-- `grammar Bu64 : u64 = BuN(64)` is `Silmaril.Wasm.Binary.U64`. -/
theorem symDerives_bu64_v1 {env : Env} (h : HasV1Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bu64" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ m, U64 bs m ∧ l = [numCase m] := by
  rw [symDerives_wrapper rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hd => ((symDerives_varG hl.bun).mp hd).1) h.bu64]
  constructor
  · rintro ⟨rfl, w, hw, rfl⟩
    obtain ⟨m, hm, rfl⟩ := (symDerives_bun hl).mp hw
    exact ⟨rfl, m, hm, rfl⟩
  · rintro ⟨rfl, m, hm, rfl⟩
    exact ⟨rfl, _, (symDerives_bun hl).mpr ⟨m, hm, rfl⟩, rfl⟩

/-- **All seven index grammars are `Silmaril.Wasm.Binary.Index`.**
`A-binary:64-70` writes them with one and the same production
`x:Bu32 => x`, so the elaborated production list is literally shared and one
lemma covers `Btypeidx`, `Bfuncidx`, `Bglobalidx`, `Btableidx`, `Bmemidx`,
`Blocalidx` and `Blabelidx`. -/
theorem symDerives_idxGram_v1 {env : Env} {x : IL.Id} {t : Typ} (h : HasV1Types env)
    (hl : HasLeb env) (hg : env.findGram? x = some ([], t, btypeidxProds))
    {k : Wasm.IndexKind} {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG x []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ y : Wasm.Idx k, Index bs y ∧ l = [Encode.toValue y] := by
  rw [symDerives_wrapper rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hd => ((symDerives_varG h.bu32).mp hd).1) hg]
  constructor
  · rintro ⟨rfl, w, hw, rfl⟩
    obtain ⟨-, m, hm, hl'⟩ := (symDerives_bu32_v1 h hl).mp hw
    exact ⟨rfl, ⟨⟨m, UN.lt_two_pow hm⟩⟩, hm, hl'⟩
  · rintro ⟨rfl, y, hy, rfl⟩
    exact ⟨rfl, _, (symDerives_bu32_v1 h hl).mpr ⟨rfl, y.toNat, hy, rfl⟩, rfl⟩

/-! ## The types section: agreement -/

/-- **`Bvaltype` is `Silmaril.Wasm.V1.Binary.ValType`** (`A-binary:85-89`):
the four numeric types, with no reference, vector or bottom type. -/
theorem symDerives_bvaltype_v1 {env : Env} (h : HasV1Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bvaltype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.V1.ValType, Wasm.V1.Binary.ValType bs t ∧
        l = [Encode.toValue t] := by
  rw [symDerives_varG h.bvaltype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bvaltypeV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
        rw [evalExp_nullaryCase] at hv
        subst hv
        first
          | exact ⟨.int .i32, .i32, rfl⟩
          | exact ⟨.int .i64, .i64, rfl⟩
          | exact ⟨.float .f32, .f32, rfl⟩
          | exact ⟨.float .f64, .f64, rfl⟩
  · rintro ⟨rfl, t, ht, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht <;>
      exact ⟨_, by simp [bvaltypeV1Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩

/-- **`Bmut` is `Silmaril.Wasm.V1.Binary.Mut`** (`A-binary:104-106`).  The
grammar's own type is the option `MUT?` (`1-syntax.spectec:119`), so its value
is an `opt`. -/
theorem symDerives_bmut_v1 {env : Env} (h : HasV1Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bmut" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ m : Wasm.Mutability, Wasm.V1.Binary.Mut bs m ∧ l = [Encode.toValue m] := by
  rw [symDerives_varG h.bmut]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bmutV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [evalExp_optE_none_iff] at hv
      subst hv
      exact ⟨.const, .const, rfl⟩
    · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [evalExp_optE_some_iff] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      rw [evalExp_nullaryCase] at hw
      subst hw
      exact ⟨.var, .var, rfl⟩
  · rintro ⟨rfl, m, hm, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hm
    · exact ⟨_, by simp [bmutV1Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_optE_none_iff.mpr rfl, rfl⟩⟩
    · exact ⟨_, by simp [bmutV1Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_optE_some_iff.mpr ⟨_, evalExp_nullaryCase.mpr rfl, rfl⟩, rfl⟩⟩

/-- A `(attr (case "%" (tup (var y))) Bu32)` factor: it derives a `u32` and
binds `y` to the bare numeral.  The wasm-1.0 counterpart of
`Equiv.symDerives_bu64Factor`. -/
theorem symDerives_bu32Factor_v1 {env : Env} (h : HasV1Types env) (hl : HasLeb env)
    {σ σ' : VarEnv} {y : IL.Id} {b : Grammar.Bytes} {ls : List Value}
    (hy : σ.findVal? y = none) :
    SymDerives env σ (.seqG [.attrG (.caseE "%" (.tupE [.varE y])) (.varG "Bu32" [])]) b ls σ'
      ↔ ∃ k, U32 b k ∧ ls = [numCase k] ∧ σ' = σ.bindVal y (.num (.natN k)) := by
  rw [symDerives_attrNT (fun _ _ _ _ hd => ((symDerives_varG h.bu32).mp hd).1)]
  constructor
  · rintro ⟨w, hw, rfl, hm⟩
    obtain ⟨-, k, hk, hlw⟩ := (symDerives_bu32_v1 h hl).mp hw
    have hw' : w = numCase k := by simpa using hlw
    subst hw'
    obtain ⟨u, hu, hmv⟩ := matchExp_case_var_elim hm
    have hu' : u = .num (.natN k) := by simpa [numCase] using hu.symm
    subst hu'
    rw [matchExp_varE_of_none_iff hy] at hmv
    exact ⟨k, hk, rfl, hmv⟩
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨numCase k, (symDerives_bu32_v1 h hl).mpr ⟨rfl, k, hk, rfl⟩, rfl,
      matchExp_case_var hy⟩

/-- **`Blimits` is `Silmaril.Wasm.V1.Binary.Limits`** (`A-binary:108-110`).
Both bounds are `u32`, and wasm-1.0 has no address type to carry. -/
theorem symDerives_blimits_v1 {env : Env} (h : HasV1Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Blimits" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ q : Wasm.V1.Limits, Wasm.V1.Binary.Limits bs q ∧ l = [Encode.toValue q] := by
  rw [symDerives_varG h.blimits]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [blimitsV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu32Factor_v1 h hl rfl).mp h₂
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_case_var rfl,
          evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩)
      exact ⟨⟨⟨k, UN.lt_two_pow hk⟩, none⟩, .min hk, rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, rfl, rfl⟩ :=
        symDerives_seqG_triple.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu32Factor_v1 h hl rfl).mp h₂
      obtain ⟨m, hm, rfl, rfl⟩ := (symDerives_bu32Factor_v1 h hl rfl).mp h₃
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_case_var rfl,
          evalExp_optE_some_iff.mpr ⟨_, evalExp_case_var rfl, rfl⟩, rfl⟩, rfl⟩)
      exact ⟨⟨⟨k, UN.lt_two_pow hk⟩, some ⟨m, UN.lt_two_pow hm⟩⟩, .minMax hk hm, rfl⟩
  · rintro ⟨rfl, q, hq, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hq with
    | min hb =>
        refine ⟨_, List.mem_cons_self .., (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_bu32Factor_v1 h hl rfl).mpr ⟨_, hb, rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
          evalExp_case_var rfl, evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩
    | minMax hb hb' =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_triple.mpr ⟨_, _, VarEnv.empty, _, _, _, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_bu32Factor_v1 h hl rfl).mpr ⟨_, hb, rfl, rfl⟩,
            (symDerives_bu32Factor_v1 h hl rfl).mpr ⟨_, hb', rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
          evalExp_case_var rfl,
          evalExp_optE_some_iff.mpr ⟨_, evalExp_case_var rfl, rfl⟩, rfl⟩, rfl⟩

/-- **`Bmemtype` is `Silmaril.Wasm.V1.Binary.MemType`** (`A-binary:118-119`):
`memtype` is an alias of `limits`, so the production is a bare wrapper. -/
theorem symDerives_bmemtype_v1 {env : Env} (h : HasV1Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bmemtype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ m : Wasm.V1.MemoryType, Wasm.V1.Binary.MemType bs m ∧
        l = [Encode.toValue m] := by
  rw [symDerives_varG h.bmemtype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bmemtypeV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨w, τ, hw, rfl, hm⟩ := symDerives_attrG.mp hs
    obtain ⟨rfl, q, hq, hlw⟩ := (symDerives_blimits_v1 h hl).mp hw
    have hw' : w = Encode.toValue q := by simpa using hlw
    subst hw'
    rw [matchExp_varE_of_none_iff rfl] at hm
    subst hm
    obtain rfl := EvalExp.unique hev (evalExp_varE_iff.mpr rfl)
    exact ⟨⟨q⟩, .mk hq, rfl⟩
  · rintro ⟨rfl, m, hm, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases hm with
    | mk hq =>
      refine (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_attrG.mpr
        ⟨Encode.toValue (_ : Wasm.V1.Limits), VarEnv.empty,
          (symDerives_blimits_v1 h hl).mpr ⟨rfl, _, hq, rfl⟩, rfl,
          matchExp_varE_of_none rfl⟩, ?_, rfl⟩
      exact evalExp_varE_iff.mpr rfl

/-- **`Btabletype` is `Silmaril.Wasm.V1.Binary.TableType`**
(`A-binary:115-116`): the `0x70` terminal is the only element type, and
`tabletype` is an alias of `limits`. -/
theorem symDerives_btabletype_v1 {env : Env} (h : HasV1Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Btabletype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.V1.TableType, Wasm.V1.Binary.TableType bs t ∧
        l = [Encode.toValue t] := by
  have hlim : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Blimits" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.blimits).mp hd).1
  rw [symDerives_varG h.btabletype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [btabletypeV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
    obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hlim).mp h₂
    obtain ⟨-, q, hq, hlw⟩ := (symDerives_blimits_v1 h hl).mp hw
    have hw' : w = Encode.toValue q := by simpa using hlw
    subst hw'
    rw [matchExp_varE_of_none_iff rfl] at hm
    subst hm
    obtain rfl := EvalExp.unique hev (evalExp_varE_iff.mpr rfl)
    exact ⟨⟨q⟩, .mk hq, rfl⟩
  · rintro ⟨rfl, t, ht, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases ht with
    | mk hq =>
      refine (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_seqG_pair.mpr
        ⟨_, _, VarEnv.empty, _, _, (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
          (symDerives_attrNT hlim).mpr ⟨Encode.toValue (_ : Wasm.V1.Limits),
            (symDerives_blimits_v1 h hl).mpr ⟨rfl, _, hq, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩
      exact evalExp_varE_iff.mpr rfl

/-- **`Bglobaltype` is `Silmaril.Wasm.V1.Binary.GlobalType`**
(`A-binary:112-113`): the value type is encoded first and the mutability
second, and the `%%` injection takes them in the other order. -/
theorem symDerives_bglobaltype_v1 {env : Env} (h : HasV1Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bglobaltype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ g : Wasm.V1.GlobalType, Wasm.V1.Binary.GlobalType bs g ∧
        l = [Encode.toValue g] := by
  have hvt : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bvaltype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bvaltype).mp hd).1
  have hmu : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bmut" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bmut).mp hd).1
  rw [symDerives_varG h.bglobaltype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bglobaltypeV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨wt, hwt, rfl, hmt⟩ := (symDerives_attrNT hvt).mp h₁
    obtain ⟨-, t, ht, hlt⟩ := (symDerives_bvaltype_v1 h).mp hwt
    have hwt' : wt = Encode.toValue t := by simpa using hlt
    subst hwt'
    rw [matchExp_varE_of_none_iff rfl] at hmt
    subst hmt
    obtain ⟨wm, hwm, rfl, hmm⟩ := (symDerives_attrNT hmu).mp h₂
    obtain ⟨-, m, hm, hlm⟩ := (symDerives_bmut_v1 h).mp hwm
    have hwm' : wm = Encode.toValue m := by simpa using hlm
    subst hwm'
    rw [matchExp_varE_of_none_iff rfl] at hmm
    subst hmm
    obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
      evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_varE_iff.mpr rfl,
        evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩)
    exact ⟨⟨m, t⟩, .mk ht hm, rfl⟩
  · rintro ⟨rfl, g, hg, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases hg with
    | mk ht hm =>
      refine (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_seqG_pair.mpr
        ⟨_, _, _, _, _,
          (symDerives_attrNT hvt).mpr ⟨Encode.toValue (_ : Wasm.V1.ValType),
            (symDerives_bvaltype_v1 h).mpr ⟨rfl, _, ht, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩,
          (symDerives_attrNT hmu).mpr ⟨Encode.toValue (_ : Wasm.Mutability),
            (symDerives_bmut_v1 h).mpr ⟨rfl, _, hm, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩
      exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_varE_iff.mpr rfl, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩

/-- **`Bblocktype` is `Silmaril.Wasm.V1.Binary.BlockType`**
(`A-binary:135-137`): `0x40` for the empty type, a value type otherwise.
wasm-1.0 has no multi-value block type, hence no `s33` production and none of
wasm-3.0's `$s33_to_u32` problem. -/
theorem symDerives_bblocktype_v1 {env : Env} (h : HasV1Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bblocktype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.V1.BlockType, Wasm.V1.Binary.BlockType bs t ∧
        l = [Encode.toValue t] := by
  rw [symDerives_varG h.bblocktype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bblocktypeV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [evalExp_optE_none_iff] at hv
      subst hv
      exact ⟨none, .empty, rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨w, τ, hw, rfl, hm⟩ := symDerives_attrG.mp hs
      obtain ⟨rfl, t, ht, hlw⟩ := (symDerives_bvaltype_v1 h).mp hw
      have hw' : w = Encode.toValue t := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev
        (evalExp_optE_some_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩)
      exact ⟨some t, .value ht, rfl⟩
  · rintro ⟨rfl, t, ht, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht with
    | empty =>
        exact ⟨_, by simp [bblocktypeV1Prods], (prodDerives_byte (by decide)).mpr
          ⟨rfl, _, evalExp_optE_none_iff.mpr rfl, rfl⟩⟩
    | value hv =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_attrG.mpr
            ⟨Encode.toValue (_ : Wasm.V1.ValType), VarEnv.empty,
              (symDerives_bvaltype_v1 h).mpr ⟨rfl, _, hv, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, ?_, rfl⟩⟩
        exact evalExp_optE_some_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩


/-- **`Bexternidx` is `Silmaril.Wasm.Scalar.Binary.ExportDesc`**
(`A-binary:72-76`), the four tagged indices an export description is.
wasm-1.0 has no `importdesc`: `Bimport` (`A-binary:429-430`) carries a whole
`Bexterntype` (`:122-126`), which needs `Blist`; see the closing section. -/
theorem symDerives_bexternidx_v1 {env : Env} (h : HasV1Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bexternidx" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ x : Wasm.V1.ExternIdx, Wasm.Scalar.Binary.ExportDesc bs x ∧
        l = [Encode.toValue x] := by
  have hf : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bfuncidx" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bfuncidx).mp hd).1
  have ht : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Btableidx" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.btableidx).mp hd).1
  have hm : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bmemidx" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bmemidx).mp hd).1
  have hg : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bglobalidx" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bglobalidx).mp hd).1
  rw [symDerives_varG h.bexternidx]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bexternidxV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hmt⟩ := (symDerives_attrNT hf).mp h₂
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v1 (k := .func) h hl h.bfuncidx).mp hw
      have hw' : w = Encode.toValue y := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hmt
      subst hmt
      obtain rfl := EvalExp.unique hev
        (evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩)
      exact ⟨.func y, .func hy, rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hmt⟩ := (symDerives_attrNT ht).mp h₂
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v1 (k := .table) h hl h.btableidx).mp hw
      have hw' : w = Encode.toValue y := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hmt
      subst hmt
      obtain rfl := EvalExp.unique hev
        (evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩)
      exact ⟨.table y, .table hy, rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hmt⟩ := (symDerives_attrNT hm).mp h₂
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v1 (k := .memory) h hl h.bmemidx).mp hw
      have hw' : w = Encode.toValue y := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hmt
      subst hmt
      obtain rfl := EvalExp.unique hev
        (evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩)
      exact ⟨.memory y, .memory hy, rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hmt⟩ := (symDerives_attrNT hg).mp h₂
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v1 (k := .global) h hl h.bglobalidx).mp hw
      have hw' : w = Encode.toValue y := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hmt
      subst hmt
      obtain rfl := EvalExp.unique hev
        (evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩)
      exact ⟨.global y, .global hy, rfl⟩
  · rintro ⟨rfl, x, hx, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hx with
    | func hy =>
        refine ⟨_, List.mem_cons_self .., (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT hf).mpr ⟨Encode.toValue (_ : Wasm.FuncIdx),
              (symDerives_idxGram_v1 h hl h.bfuncidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩
    | table hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT ht).mpr ⟨Encode.toValue (_ : Wasm.TableIdx),
              (symDerives_idxGram_v1 h hl h.btableidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩
    | memory hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT hm).mpr ⟨Encode.toValue (_ : Wasm.MemIdx),
              (symDerives_idxGram_v1 h hl h.bmemidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩
    | global hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT hg).mpr ⟨Encode.toValue (_ : Wasm.GlobalIdx),
              (symDerives_idxGram_v1 h hl h.bglobalidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩


/-! ## The denotations, as `gramRelSup`, at the corrected wasm-1.0 script

`gramRelSup envV1 ρ g` is the byte-string/value relation the corrected
wasm-1.0 specification gives `g` (`Sem/Grammar.lean`).  These are the
`SymDerives` results above read at that level and discharged at `envV1`: one
equation per nonterminal, each an agreement with `Silmaril/Wasm/V1/Binary/`.
-/

/-- `Btypeidx` (`A-binary:64`) denotes `Silmaril.Wasm.Binary.Index`. -/
theorem gramRel_btypeidx_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Btypeidx" []) bs v ↔
      ∃ x : Wasm.TypeIdx, Index bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ :=
      (symDerives_idxGram_v1 hasV1Types_v1 hasLeb_v1 hasV1Types_v1.btypeidx).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_idxGram_v1 hasV1Types_v1 hasLeb_v1
      hasV1Types_v1.btypeidx).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bfuncidx` (`A-binary:65`) denotes `Silmaril.Wasm.Binary.Index`. -/
theorem gramRel_bfuncidx_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bfuncidx" []) bs v ↔
      ∃ x : Wasm.FuncIdx, Index bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ :=
      (symDerives_idxGram_v1 hasV1Types_v1 hasLeb_v1 hasV1Types_v1.bfuncidx).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_idxGram_v1 hasV1Types_v1 hasLeb_v1
      hasV1Types_v1.bfuncidx).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Blabelidx` (`A-binary:70`) denotes `Silmaril.Wasm.Binary.Index`; the same
production carries `Bglobalidx`, `Btableidx`, `Bmemidx` and `Blocalidx`. -/
theorem gramRel_blabelidx_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Blabelidx" []) bs v ↔
      ∃ x : Wasm.LabelIdx, Index bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ :=
      (symDerives_idxGram_v1 hasV1Types_v1 hasLeb_v1 hasV1Types_v1.blabelidx).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_idxGram_v1 hasV1Types_v1 hasLeb_v1
      hasV1Types_v1.blabelidx).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bvaltype` (`A-binary:85-89`) denotes exactly
`Silmaril.Wasm.V1.Binary.ValType`. -/
theorem gramRel_bvaltype_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bvaltype" []) bs v ↔
      ∃ t : Wasm.V1.ValType, Wasm.V1.Binary.ValType bs t ∧ v = Encode.toValue t := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bvaltype_v1 hasV1Types_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bvaltype_v1 hasV1Types_v1).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bmut` (`A-binary:104-106`) denotes exactly
`Silmaril.Wasm.V1.Binary.Mut`. -/
theorem gramRel_bmut_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bmut" []) bs v ↔
      ∃ m : Wasm.Mutability, Wasm.V1.Binary.Mut bs m ∧ v = Encode.toValue m := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bmut_v1 hasV1Types_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bmut_v1 hasV1Types_v1).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Blimits` (`A-binary:108-110`) denotes exactly
`Silmaril.Wasm.V1.Binary.Limits`. -/
theorem gramRel_blimits_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Blimits" []) bs v ↔
      ∃ q : Wasm.V1.Limits, Wasm.V1.Binary.Limits bs q ∧ v = Encode.toValue q := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_blimits_v1 hasV1Types_v1 hasLeb_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_blimits_v1 hasV1Types_v1 hasLeb_v1).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bmemtype` (`A-binary:118-119`) denotes exactly
`Silmaril.Wasm.V1.Binary.MemType`. -/
theorem gramRel_bmemtype_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bmemtype" []) bs v ↔
      ∃ m : Wasm.V1.MemoryType, Wasm.V1.Binary.MemType bs m ∧ v = Encode.toValue m := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bmemtype_v1 hasV1Types_v1 hasLeb_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bmemtype_v1 hasV1Types_v1 hasLeb_v1).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Btabletype` (`A-binary:115-116`) denotes exactly
`Silmaril.Wasm.V1.Binary.TableType`. -/
theorem gramRel_btabletype_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Btabletype" []) bs v ↔
      ∃ t : Wasm.V1.TableType, Wasm.V1.Binary.TableType bs t ∧ v = Encode.toValue t := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_btabletype_v1 hasV1Types_v1 hasLeb_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_btabletype_v1 hasV1Types_v1 hasLeb_v1).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bglobaltype` (`A-binary:112-113`) denotes exactly
`Silmaril.Wasm.V1.Binary.GlobalType`. -/
theorem gramRel_bglobaltype_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bglobaltype" []) bs v ↔
      ∃ g : Wasm.V1.GlobalType, Wasm.V1.Binary.GlobalType bs g ∧ v = Encode.toValue g := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bglobaltype_v1 hasV1Types_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bglobaltype_v1 hasV1Types_v1).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bblocktype` (`A-binary:135-137`) denotes exactly
`Silmaril.Wasm.V1.Binary.BlockType`. -/
theorem gramRel_bblocktype_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bblocktype" []) bs v ↔
      ∃ t : Wasm.V1.BlockType, Wasm.V1.Binary.BlockType bs t ∧ v = Encode.toValue t := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bblocktype_v1 hasV1Types_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bblocktype_v1 hasV1Types_v1).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bexternidx` (`A-binary:72-76`) denotes exactly
`Silmaril.Wasm.Scalar.Binary.ExportDesc`. -/
theorem gramRel_bexternidx_v1 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV1 ρ (.varG "Bexternidx" []) bs v ↔
      ∃ x : Wasm.V1.ExternIdx, Wasm.Scalar.Binary.ExportDesc bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bexternidx_v1 hasV1Types_v1 hasLeb_v1).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bexternidx_v1 hasV1Types_v1 hasLeb_v1).mpr ⟨rfl, a, ha, rfl⟩⟩


/-! ## UTF-8: `$utf8` is a *function* in wasm-1.0, and it has no clause that fires

wasm-3.0 spells the UTF-8 encoding partly as a grammar; wasm-1.0 spells it
entirely as the function `$utf8` of `A-binary:52-56`, and `Bname`
(`A-binary:58-59`) uses it in a premise:

```
grammar Bname : name =
  | b*:Blist(Bbyte) => name  -- if $utf8(name) = b*
```

So the wasm-1.0 UTF-8 statement is about `Sem/Eval.lean`'s `callDef`, not
about a grammar denotation.  `Errata/Wasm10.lean`'s `erratum685` corrects the
continuation-byte bounds of that function (and, folded in, `#684`'s
`U+110000`), and the theorems below are about the **corrected** `$utf8`.

### The shape the stream has

`findDef_utf8_shape_v1` reads the corrected definition off `envV1` and records
the one thing that matters: each of the four single-character clauses has the
argument pattern `(list (var "ch"))` and a result expression that begins with
`(var "b")` or `(var "b_1")`.  Those names are *quantifiers* of the clause
(`spectec/src/il/ast.ml:149`), not binders of the pattern, and
`spectec/src/il/eval.ml:654` builds a clause's scope by matching the arguments
and nothing else.  So the result expression mentions a variable the scope does
not contain, and the clause cannot produce a value whichever way its premise
goes. -/

/-- The corrected `$utf8` of the wasm-1.0 stream, to the precision the results
below need: five clauses, of which the first four take a one-character
argument and return a list beginning with an unbound byte variable.  The
premises `p₁ … p₄`, the quantifier lists `q₁ … q₄` and the fifth clause are
left as they are read off the stream. -/
private theorem findDef_utf8_shape_v1 :
    ∃ (ps : List Param) (t : Typ) (q₁ q₂ q₃ q₄ : List Param) (p₁ p₂ p₃ p₄ : Exp)
      (es₂ es₃ es₄ : List Exp) (c₅ : Clause),
      envV1.findDef? "utf8" = some (ps, t,
        [ .defD q₁ [.expA (.listE [.varE "ch"])] (.listE [.varE "b"]) [.ifPr p₁],
          .defD q₂ [.expA (.listE [.varE "ch"])] (.listE (.varE "b_1" :: es₂)) [.ifPr p₂],
          .defD q₃ [.expA (.listE [.varE "ch"])] (.listE (.varE "b_1" :: es₃)) [.ifPr p₃],
          .defD q₄ [.expA (.listE [.varE "ch"])] (.listE (.varE "b_1" :: es₄)) [.ifPr p₄],
          c₅ ]) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-! ### The three lemmas the argument needs -/

/-- Evaluating a list expression whose first element is a variable the scope
does not bind has no value: `evalExp`'s `VarE` clause is a lookup
(`Sem/Eval.lean`, `eval.ml:226`) and `evalExps` fails as soon as one element
does (`eval.ml:39-41`). -/
theorem not_evalExp_listE_unbound {env : Env} {σ : VarEnv} {y : IL.Id} {es : List Exp}
    {v : Value} (h : σ.findVal? y = none) : ¬ EvalExp env σ (.listE (.varE y :: es)) v := by
  intro hv
  obtain ⟨vs, hvs, -⟩ := evalExp_listE_iff.mp hv
  obtain ⟨w, -, hw, -, -⟩ := evalExps_cons_iff.mp hvs
  rw [evalExp_varE_iff, h] at hw
  exact absurd hw (by simp)

/-- `matchArgs` is functional: two successful matches of the same patterns
against the same arguments build the same scope. -/
theorem matchArgs_unique_v1 {env : Env} {ρ ρ₁ ρ₂ : VarEnv} {pats : List Arg}
    {ws : List ArgV} (h₁ : MatchArgs env ρ pats ws ρ₁) (h₂ : MatchArgs env ρ pats ws ρ₂) :
    ρ₁ = ρ₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e1 := matchArgs_ok_of_le (le_max_left n₁ n₂) h₁
  have e2 := matchArgs_ok_of_le (le_max_right n₁ n₂) h₂
  rw [e1] at e2
  exact Except.ok.inj e2

/-- A one-element list pattern matches a one-element list. -/
theorem matchExp_listE_one_v1 {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : MatchExp env ρ e v ρ') : MatchExp env ρ (.listE [e]) (.list [v]) ρ' := by
  obtain ⟨n, h⟩ := h
  refine ⟨n + 3, ?_⟩
  simp only [matchExp, Res.ofOption, Value.asList?, Bind.bind, Except.bind, matchExps,
    matchExp_ok_of_le (show n ≤ n + 1 by omega) h]

/-- **`tryClauses`, inverted.**  `Sem/Eval.lean` has introduction lemmas for
clause selection (`Equiv/Numerics.lean`'s `tryClauses_hit`, `_skip_match`,
`_skip_prem`) and no elimination; this is the elimination.  Either the head
clause fired — its patterns matched, its premises held, and its body evaluated
to the result — or the value came from the rest of the list.  `outOfFuel` is
not a value, which is what makes the third branch of `Res.elimUndef`
harmless. -/
theorem tryClauses_cons_elim_v1 {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {v : Value} {n : Nat}
    (h : tryClauses n env (.defD q pats e prems :: cs) ws = .ok v) :
    (∃ ρ₀ ρ₁, MatchArgs env VarEnv.empty pats ws ρ₀ ∧ PremsHold env ρ₀ prems ρ₁ ∧
        EvalExp env ρ₁ e v) ∨ TryClauses env cs ws v := by
  cases n with
  | zero => simp [tryClauses] at h
  | succ m =>
      rw [tryClauses] at h
      cases hA : (do let ρ₀ ← matchArgs m env VarEnv.empty pats ws
                     premsHold m env ρ₀ prems : Res VarEnv) with
      | ok ρ₁ =>
          rw [hA, Res.elimUndef_ok] at h
          obtain ⟨ρ₀, hm, hp⟩ := Res.bind_eq_ok.mp hA
          exact Or.inl ⟨ρ₀, ρ₁, ⟨m, hm⟩, ⟨m, hp⟩, ⟨m, h⟩⟩
      | error err =>
          cases err with
          | undef =>
              rw [hA, Res.elimUndef_undef] at h
              exact Or.inr ⟨m, h⟩
          | outOfFuel =>
              rw [hA, Res.elimUndef_oof] at h
              exact absurd h (by simp)

/-- **A single-character clause of `$utf8` is always skipped.**  Its argument
pattern binds only `ch`, its premise is a side condition and binds nothing, so
the scope its body is evaluated in is exactly `ch ↦ u` — and the body begins
with `b` or `b_1`, which that scope does not bind. -/
theorem tryClauses_skip_charClause_v1 {env : Env} {q : List Param} {p : Exp} {y : IL.Id}
    {es : List Exp} {cs : List Clause} {u v : Value}
    (hy : (VarEnv.empty.bindVal "ch" u).findVal? y = none)
    (h : TryClauses env
      (.defD q [.expA (.listE [.varE "ch"])] (.listE (.varE y :: es)) [.ifPr p] :: cs)
      [.val (.list [u])] v) :
    TryClauses env cs [.val (.list [u])] v := by
  obtain ⟨n, hn⟩ := h
  rcases tryClauses_cons_elim_v1 hn with ⟨ρ₀, ρ₁, hm, hp, he⟩ | hr
  · have hm0 : MatchArgs env VarEnv.empty [Arg.expA (.listE [.varE "ch"])]
        [ArgV.val (.list [u])] (VarEnv.empty.bindVal "ch" u) :=
      matchArgs_cons (matchArg_expA (matchExp_listE_one_v1 (matchExp_varE rfl))) matchArgs_nil
    obtain rfl := matchArgs_unique_v1 hm hm0
    obtain rfl := (premsHold_ifPr_iff.mp hp).2
    exact absurd he (not_evalExp_listE_unbound hy)
  · exact hr

/-- **`callDef`, inverted.**  A call's value comes from the clause list of the
definition its name resolves to, applied to the evaluated arguments. -/
theorem callDef_elim_v1 {env : Env} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {v : Value}
    (h : CallDef env ρ x args v)
    (hb : ∀ ws, env.builtins.call ((ρ.findDef? x).getD x) ws = Option.none) :
    ∃ (ws : List ArgV) (d : DefDef), EvalArgs env ρ args ws ∧
      env.findDef? ((ρ.findDef? x).getD x) = some d ∧ TryClauses env d.2.2 ws v := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [callDef] at hn
  | succ m =>
      rw [callDef] at hn
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
      obtain ⟨ws, hws, d, hd, hc⟩ := hn
      refine ⟨ws, d, ⟨m, hws⟩, hd, ?_⟩
      cases hr : tryClauses m env d.2.2 ws with
      | ok u =>
          rw [hr, Res.elimUndef_ok] at hc
          exact ⟨m, by rw [hr, hc]⟩
      | error e =>
          cases e with
          | outOfFuel => rw [hr] at hc; simp [Res.elimUndef] at hc
          | undef => rw [hr, Res.elimUndef, hb ws] at hc; simp at hc

/-- `evalArgs` is functional. -/
theorem evalArgs_unique_v1 {env : Env} {ρ : VarEnv} {args : List Arg} {ws₁ ws₂ : List ArgV}
    (h₁ : EvalArgs env ρ args ws₁) (h₂ : EvalArgs env ρ args ws₂) : ws₁ = ws₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e1 := evalArgs_ok_of_le (le_max_left n₁ n₂) h₁
  have e2 := evalArgs_ok_of_le (le_max_right n₁ n₂) h₂
  rw [e1] at e2
  exact Except.ok.inj e2

/-- **The finding, at the clause list.**  On a one-character argument, none of
the four clauses of the corrected wasm-1.0 `$utf8` that *define* the UTF-8
encoding can fire: whatever value the function has comes from the fifth
clause, `def $utf8(ch*) = $concat_(byte, $utf8(ch)*)` (`A-binary:56`). -/
theorem utf8_charArg_only_last_clause_v1 (u v : Value) :
    ∃ (ps : List Param) (t : Typ) (cs : List Clause) (c₅ : Clause),
      envV1.findDef? "utf8" = some (ps, t, cs) ∧ cs.getLast? = some c₅ ∧
      (TryClauses envV1 cs [.val (.list [u])] v →
        TryClauses envV1 [c₅] [.val (.list [u])] v) := by
  obtain ⟨ps, t, q₁, q₂, q₃, q₄, p₁, p₂, p₃, p₄, es₂, es₃, es₄, c₅, hd⟩ :=
    findDef_utf8_shape_v1
  refine ⟨ps, t, _, c₅, hd, rfl, fun h => ?_⟩
  exact tryClauses_skip_charClause_v1 rfl
    (tryClauses_skip_charClause_v1 rfl
      (tryClauses_skip_charClause_v1 rfl
        (tryClauses_skip_charClause_v1 rfl h)))

/-- **The finding, at `callDef`.**  If the corrected wasm-1.0 `$utf8` has a
value on a one-character argument, that value comes from its fifth clause —
the one that calls `$utf8` again on the same one-character list. -/
theorem callDef_utf8_charArg_v1 {ρ : VarEnv} {args : List Arg} {u v : Value}
    (hρ : ρ.findDef? "utf8" = none)
    (hws : EvalArgs envV1 ρ args [.val (.list [u])])
    (h : CallDef envV1 ρ "utf8" args v) :
    ∃ (ps : List Param) (t : Typ) (cs : List Clause) (c₅ : Clause),
      envV1.findDef? "utf8" = some (ps, t, cs) ∧ cs.getLast? = some c₅ ∧
      TryClauses envV1 [c₅] [.val (.list [u])] v := by
  obtain ⟨ws, d, hargs, hd, hc⟩ := callDef_elim_v1 h (fun _ => by simp [envV1, Builtins.none])
  rw [hρ, Option.getD_none] at hd
  obtain rfl := evalArgs_unique_v1 hargs hws
  obtain ⟨ps, t, cs, c₅, hd', hlast, hskip⟩ := utf8_charArg_only_last_clause_v1 u v
  rw [hd'] at hd
  obtain rfl := Option.some.inj hd
  exact ⟨ps, t, cs, c₅, hd', hlast, hskip hc⟩

/-! ## What is proved, and what is not

### Proved

**The values section** (`A-binary:18-44`), at the corrected wasm-1.0 script:

* `Bbyte` is `Silmaril.Wasm.Binary.Byte` (`bbyte_iff_byte_v1`).
* `BuN(N)` is `UN N` (`bun_iff_un_v1`), hence `Bu32 = U32` and `Bu64 = U64`
  (`bu32_iff_u32_v1`, `bu64_iff_u64_v1`).
* `BsN(N)` is `SN N` restricted to single-byte encodings and non-negative
  values, **exactly** (`bsn_iff_sn_v1`).
* All seven index grammars are `Silmaril.Wasm.Binary.Index`
  (`symDerives_idxGram_v1`, with `gramRel_btypeidx_v1`, `gramRel_bfuncidx_v1`
  and `gramRel_blabelidx_v1` spelled out).
* `Bexternidx` is `Silmaril.Wasm.Scalar.Binary.ExportDesc`
  (`gramRel_bexternidx_v1`).

**The types section** (`A-binary:85-126`), each an equality of relations
proved in both directions and transported along `Encode.toValue`:

| SpecTec | Lean | statement |
| --- | --- | --- |
| `Bvaltype` | `Wasm.V1.Binary.ValType` | `gramRel_bvaltype_v1` |
| `Bmut` | `Wasm.V1.Binary.Mut` | `gramRel_bmut_v1` |
| `Blimits` | `Wasm.V1.Binary.Limits` | `gramRel_blimits_v1` |
| `Bmemtype` | `Wasm.V1.Binary.MemType` | `gramRel_bmemtype_v1` |
| `Btabletype` | `Wasm.V1.Binary.TableType` | `gramRel_btabletype_v1` |
| `Bglobaltype` | `Wasm.V1.Binary.GlobalType` | `gramRel_bglobaltype_v1` |
| `Bblocktype` | `Wasm.V1.Binary.BlockType` | `gramRel_bblocktype_v1` |

Unlike `Equiv/BinaryTypes.lean`'s wasm-3.0 results, **none of these carries a
side condition**: wasm-1.0 has no reference types, so there is no `RefAbs`,
no `ValAbs`, and no `$s33_to_u32` to make a production unreachable.

**The `BsN` verdict for wasm-1.0.**  The defect is there, and in a sharper
form than in wasm-3.0:

* `hasSignedLeb_v1` — the elaborated `BuN`, `BsN`, `BiN` and `Bbyte` of
  `specs/spectec/wasm-1.0.ast` are the same values as wasm-3.0's, so
  `Equiv/BinaryValues.lean`'s `bsn_iff_sn` applies verbatim;
* `not_bsn_FF7E_v1`, `not_bi32_FF7E_v1`, `not_bi64_FF7E_v1` — `FF 7E`, the
  encoding of `i32.const -129`, has no derivation;
* `bi32_v1_disagrees_with_in` — the corrected wasm-1.0 `Bi32` disagrees with
  `Silmaril.Wasm.Binary.IN 32`;
* `hasCorrectedBi_v1` — and wasm-3.0's `#654` has no wasm-1.0 analogue:
  `A-binary:40-41` already reads `Bi32 = BiN(32)`, so there is nothing left to
  patch at that level and `BsN` is the sole cause.

**UTF-8, at `callDef`.**  `tryClauses_cons_elim_v1` and `callDef_elim_v1` are
the elimination rules `Sem/Eval.lean` and `Equiv/Numerics.lean` did not have;
with them, `utf8_charArg_only_last_clause_v1` and `callDef_utf8_charArg_v1`
show that on a one-character argument the four clauses of the corrected
`$utf8` that define the encoding are **dead**, and only the fifth,
`$concat_(byte, $utf8(ch)*)`, can fire.

### Not proved

* **`$utf8` diverges, and `Bname` therefore derives only the empty name.**
  The fifth clause's body calls `$utf8` on the same one-character list, so no
  fuel can make `callDef` return; `Bname` (`A-binary:58-59`) has the premise
  `$utf8(name) = b*`, and so would derive nothing for a non-empty name.  That
  is a statement about *every* fuel level, and proving it means a strong
  induction on fuel through `evalExp`'s `CallE` and `IterE` clauses,
  `evalArgs`, `evalIterE`, `evalIterList` and `evalRounds` — eight nested
  fuel decrements, for which this tree has no lemmas.  What *is* proved is the
  step that makes the induction's base case unavoidable
  (`utf8_charArg_only_last_clause_v1`): there is no other clause to fall back
  on.  The same shape is in wasm-2.0 and wasm-3.0, and it is a defect of the
  IL, not of the prose: SpecTec writes a *relation* — "these bytes encode this
  character" — as a *function*, and `spectec/src/il/eval.ml:654` binds a
  clause's variables only by matching its arguments.  Whether SpecTec's own
  backends ever reduce `$utf8` is not established here.
* **`Blist`, and everything above it.**  `Blist(BX) = n:Bu32 (el:BX)^n`
  (`A-binary:7`) denotes an `IterG` with a `ListN` counter, the L-attributed
  case `Sem/Grammar.lean` handles but that no worked instance exercises.  The
  generic bridge "`Blist(BX)` denotes `Silmaril.Wasm.Binary.Vec R` whenever
  `BX` denotes `R`" is not proved, and without it `Bresulttype`
  (`A-binary:92-93`), `Bfunctype` (`:98-99`), `Bexterntype` (`:122-126`),
  `Bname` (`:58-59`) and the whole module section (`:397-540`) are out of
  reach.  This is the single lemma that would unlock the most, and it is the
  same gap `Equiv/BinaryTypes.lean` records for wasm-3.0.
* **The instruction section.**  `Binstr` is one 18 709-character grammar with
  about 190 productions; transcribing its production list is what
  `symDerives_varG` would need, and nothing less will do, because the
  elimination direction has to rule out *every* production.  `Bblocktype` and
  `Bmemarg`'s neighbours are done above; the opcode tables are not.  The
  consequence of the `BsN` defect for instructions is nevertheless exact at
  the level it is stated: `A-binary:215` encodes `I32.CONST` with `Bi32`, and
  `not_bi32_FF7E_v1` says that grammar rejects `FF 7E`, so the corrected
  wasm-1.0 specification cannot read the `i32.const -129` that
  `Silmaril.Wasm.V1.Binary.Instr.i32Const` accepts.
* **`Bmemarg`** (`A-binary:179-180`) is transcribed (`bmemargV1Prods`) and its
  provenance checked, but its agreement with `Silmaril.Wasm.V1.Binary.Memarg`
  is not proved: the production's value is a `struct`, and `Sem/Bridge.lean`'s
  `Encode.ofStruct` has no instance in this tree yet.
* **`BfN`, `Bf32`, `Bf64`** (`A-binary:33-34`, `:43-44`) are untouched;
  `$inv_fbytes_` is a `CallE` like `$inv_signed_`.
* **`$inv_signed_` is not evaluated**, exactly as in
  `Equiv/BinaryValues.lean`: the results about `BiN` and `Bi32` are about
  their **byte language**, not about the values they attach.
* **Width `0`.**  Every statement about `BsN` assumes `0 < W`, for the reason
  `Equiv/BinaryValues.lean` gives.
-/

end Silmaril.SpecTec.Equiv.V1Binary
