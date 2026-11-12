module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Grammar
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Bridge
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
public import Silmaril.Wasm.Binary.Core.Types
-- `spectec_import` and `spectec_erratum` add their constants with
-- `Lean.addDecl`, which bypasses the `@[expose]` of the section they sit in,
-- so the *values* of `Specs.wasm30` and `Binary51.wasm30binary51` are not
-- visible to an importing module without these two lines; they are what makes
-- `hasBinTypes_wasm30binary51` a `rfl` the kernel can actually do.
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51

/-!
# The corrected wasm-3.0 binary grammar for types, against `Silmaril/Wasm/Binary/`

Phase 4, the types section.  `Silmaril/SpecTec/Errata/Binary51.lean` builds the
*corrected* wasm-3.0 specification as a Lean value; `Silmaril/SpecTec/Sem/
Grammar.lean` gives every `GramD` a denotation as an `EncRel Bytes Value`; and
`Silmaril/Wasm/Binary/Core/Types.lean` is Silmaril's hand-written `Encodes`
relation for the same section.  This file proves the two agree, through the
`Encode` bridge of `Silmaril/SpecTec/Sem/Bridge.lean`.

Every citation `5.2:n` is line `n` of
`specification/wasm-3.0/5.2-binary.types.spectec` at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`; `5.1-binary.values.spectec` and
`1.2-syntax.types.spectec` are cited by name.

## The correspondence

| SpecTec | Lean | statement |
| --- | --- | --- |
| `Bnumtype` (5.2:7) | `Core.NumType` | `gramRel_bnumtype` |
| `Bvectype` (5.2:13) | `Core.VecType` | `gramRel_bvectype` |
| `Babsheaptype` (5.2:16) | `Core.AbsHeapType` | `gramRel_babsheaptype` |
| `Bheaptype` (5.2:30) | `Core.AbsHeapType` **only** | `gramRel_bheaptype` |
| `Breftype` (5.2:34) | `Core.RefType` ∩ `RefAbs` | `gramRel_breftype` |
| `Bvaltype` (5.2:39) | `Core.ValType` ∩ `ValAbs` | `gramRel_bvaltype` |
| `Bmut` (5.2:51) | `Core.Mut` | `gramRel_bmut` |
| `Bpacktype` (5.2:55) | `Core.PackType` | `gramRel_bpacktype` |
| `Bstoragetype` (5.2:59) | `Core.StorageType` ∩ `StorageAbs` | `gramRel_bstoragetype` |
| `Bfieldtype` (5.2:63) | `Core.FieldType` ∩ `FieldAbs` | `gramRel_bfieldtype` |
| `Blimits` (5.2:83) | `Core.Limits Forms.all` | `gramRel_blimits` |
| `Btagtype` (5.2:89) | `Core.TagType` | `gramRel_btagtype` |
| `Bglobaltype` (5.2:92) | `Core.GlobalType` ∩ `GlobalAbs` | `gramRel_bglobaltype` |
| `Bmemtype` (5.2:95) | `Core.MemType Forms.all` | `gramRel_bmemtype` |
| `Btabletype` (5.2:98) | `Core.TableType` ∩ `TableAbs` | `gramRel_btabletype` |
| `Bexterntype` (5.2:102) | `Core.ExternType` ∩ `ExternAbs` | `gramRel_bexterntype` |
| `Bu32`, `Bu64` (5.1:26-27) | `U32`, `U64` | `gramRel_bu32`, `gramRel_bu64` |
| `Btypeidx` (5.1:70) | `Index` | `gramRel_btypeidx` |

Every one of them is an **equality of relations**, proved in both directions:
the byte strings the corrected specification derives, with the values it
assigns, are exactly those of the hand-written relation, transported along
`Encode.toValue`.  The specification's grammar is `Forms.all`, where every
Core-3.0-only encoding form is enabled and `Bound.u32` is subsumed by
`Bound.u64` (`Core/Types.lean`, `Bound.all_iff`).

## Provenance

`HasBinTypes env` lists, one field per nonterminal, the `IL.Prod` list the
pinned stream contains, and `hasBinTypes_wasm30binary51` /
`hasBinTypes_wasm30` discharge it by `rfl` against
`Silmaril.SpecTec.IL.Binary51.wasm30binary51` and
`Silmaril.SpecTec.Specs.wasm30`.  Both hold, with the *same* productions:
`#650` corrects `Bi32`, `Bi64`, `$cont` and `$utf8`, none of which §5.2
mentions, so the types section of the corrected specification is the types
section of the pinned one.  `hasLeb_wasm30binary51` says the same for `Bbyte`
and `BuN`, which is what carries `Sem/Grammar.lean`'s `bun_iff_un` over to the
corrected script.

## The finding: `$s33_to_u32` is declared and never defined

`5.2:32` is

```
  | x33:Bs33 => _IDX $s33_to_u32(x33)  -- if x33 >= 0
```

and `$s33_to_u32` is declared at `3.1-numerics.scalar.spectec:7` as
`def $s33_to_u32(s33) : u32  hint(show %)` — with no clauses anywhere in the
specification and, unlike `$ibits_` and the other external numerics
(`3.1-numerics.scalar.spectec:31-47`), without `hint(builtin)`.
`HasBinTypes.s33ToU32` is the machine-checked statement that the elaborated
script really does carry a clause-less `DecD`, and `Sem/Eval.lean`'s
`tryClauses` on an empty clause list is `.error .undef`
(`spectec/src/il/eval.ml:647`), so the call has no value, the production's
value expression denotes nothing, and that production derives nothing:

* `not_callDef_s33ToU32` — the call is undefined;
* `symDerives_bheaptype` — `Bheaptype` derives **exactly** the twelve abstract
  heap types;
* `bheaptype_misses_typeIdx` — the byte `0x00` is `Core.HeapType.typeIdx 0`
  for Silmaril and is derived by nothing in the corrected specification.

That restriction is why `Breftype` and everything above it are stated modulo
`RefAbs`/`ValAbs`/… rather than as plain equalities: the corrected
specification cannot reach a reference to a declared type, so `(ref $t)`,
`(ref null $t)`, every struct/array/function reference to a concrete type,
and the `s33` form of a block type are all unreachable in it.

## What this file does not prove

* `Bresulttype` (5.2:45-46), `Bcomptype` (5.2:66-69), `Bsubtype` (5.2:71-74)
  and `Brectype` (5.2:76-78).  All four go through
  `Blist(BX) = n:Bu32 (el:BX)^n`, whose denotation is an `IterG` with a
  `ListN` count — the L-attributed dependency `Sem/Grammar.lean`'s module
  docstring describes.  The generic bridge "`Blist(BX)` denotes
  `Silmaril.Wasm.Binary.Vec R` whenever `BX` denotes `R`" is *not* proved
  here; the productions are transcribed and their provenance checked
  (`HasBinTypes.bresulttype`, `.bcomptype`, `.bsubtype`, `.brectype`,
  `.blist`), but nothing is claimed about what they derive.
* `BsN`/`Bs33` against `Silmaril.Wasm.Binary.SN`.  `Sem/Grammar.lean` proves
  `BuN(N) = UN N`; the signed counterpart is not done, and it is not needed
  for anything above, because the one §5.2 use of `Bs33` is the production the
  finding kills.
* The *unambiguity* of the §5.2 nonterminals.  `Core/Types.lean` proves
  `PrefixFree` for all of them, and `Sem/Grammar.lean` has
  `unambiguous_bun`; transporting the former along the equalities here is
  immediate but is not written down.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv

open Silmaril.SpecTec.IL Silmaril.SpecTec.Sem Silmaril.Wasm.Binary

set_option maxRecDepth 4000000

/-- The sole `mut?` pattern the §5.2 productions use. -/
def mutOptE : Exp := .iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")])

/-- The four productions of `grammar Bnumtype : numtype`
(`specification/wasm-3.0/5.2-binary.types.spectec:7-11`), as elaborated. -/
def bnumtypeProds : List IL.Prod :=
  [ .prodD [] (.numG 0x7C) (.caseE "F64" (.tupE [])) [],
    .prodD [] (.numG 0x7D) (.caseE "F32" (.tupE [])) [],
    .prodD [] (.numG 0x7E) (.caseE "I64" (.tupE [])) [],
    .prodD [] (.numG 0x7F) (.caseE "I32" (.tupE [])) [] ]

/-- The sole production of `grammar Bvectype : vectype` (5.2:13-14). -/
def bvectypeProds : List IL.Prod :=
  [ .prodD [] (.numG 0x7B) (.caseE "V128" (.tupE [])) [] ]

/-- The twelve productions of `grammar Babsheaptype : heaptype` (5.2:16-28). -/
def babsheaptypeProds : List IL.Prod :=
  [ .prodD [] (.numG 0x69) (.caseE "EXN" (.tupE [])) [],
    .prodD [] (.numG 0x6A) (.caseE "ARRAY" (.tupE [])) [],
    .prodD [] (.numG 0x6B) (.caseE "STRUCT" (.tupE [])) [],
    .prodD [] (.numG 0x6C) (.caseE "I31" (.tupE [])) [],
    .prodD [] (.numG 0x6D) (.caseE "EQ" (.tupE [])) [],
    .prodD [] (.numG 0x6E) (.caseE "ANY" (.tupE [])) [],
    .prodD [] (.numG 0x6F) (.caseE "EXTERN" (.tupE [])) [],
    .prodD [] (.numG 0x70) (.caseE "FUNC" (.tupE [])) [],
    .prodD [] (.numG 0x71) (.caseE "NONE" (.tupE [])) [],
    .prodD [] (.numG 0x72) (.caseE "NOEXTERN" (.tupE [])) [],
    .prodD [] (.numG 0x73) (.caseE "NOFUNC" (.tupE [])) [],
    .prodD [] (.numG 0x74) (.caseE "NOEXN" (.tupE [])) [] ]

/-- The two productions of `grammar Bheaptype : heaptype` (5.2:30-32).  The
second is the one `$s33_to_u32` makes unreachable; see
`symDerives_bheaptype`. -/
def bheaptypeProds : List IL.Prod :=
  [ .prodD [.expP "ht" (.varT "heaptype" [])]
      (.attrG (.varE "ht") (.varG "Babsheaptype" [])) (.varE "ht") [],
    .prodD [.expP "x33" (.varT "s33" [])]
      (.attrG (.varE "x33") (.varG "Bs33" []))
      (.caseE "_IDX" (.callE "s33_to_u32" [.expA (.varE "x33")]))
      [ .ifPr (.cmpE .geOp (.numT .intT)
          (.projE (.uncaseE (.varE "x33") "%") 0)
          (.cvtE (.numE (.natN 0)) .natT .intT)) ] ]

/-- The three productions of `grammar Breftype : reftype` (5.2:34-37). -/
def breftypeProds : List IL.Prod :=
  [ .prodD [.expP "ht" (.varT "heaptype" [])]
      (.seqG [.seqG [.numG 0x63], .seqG [.attrG (.varE "ht") (.varG "Bheaptype" [])]])
      (.caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))), .varE "ht"])) [],
    .prodD [.expP "ht" (.varT "heaptype" [])]
      (.seqG [.seqG [.numG 0x64], .seqG [.attrG (.varE "ht") (.varG "Bheaptype" [])]])
      (.caseE "REF" (.tupE [.optE none, .varE "ht"])) [],
    .prodD [.expP "ht" (.varT "heaptype" [])]
      (.attrG (.varE "ht") (.varG "Babsheaptype" []))
      (.caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))), .varE "ht"])) [] ]

/-- The three productions of `grammar Bvaltype : valtype` (5.2:39-42); the
`sub` nodes are the variant inclusions the elaborator inserts. -/
def bvaltypeProds : List IL.Prod :=
  [ .prodD [.expP "nt" (.varT "numtype" [])] (.attrG (.varE "nt") (.varG "Bnumtype" []))
      (.subE (.varE "nt") (.varT "numtype" []) (.varT "valtype" [])) [],
    .prodD [.expP "vt" (.varT "vectype" [])] (.attrG (.varE "vt") (.varG "Bvectype" []))
      (.subE (.varE "vt") (.varT "vectype" []) (.varT "valtype" [])) [],
    .prodD [.expP "rt" (.varT "reftype" [])] (.attrG (.varE "rt") (.varG "Breftype" []))
      (.subE (.varE "rt") (.varT "reftype" []) (.varT "valtype" [])) [] ]

/-- The sole production of `grammar Bresulttype : resulttype` (5.2:45-46). -/
def bresulttypeProds : List IL.Prod :=
  [ .prodD [.expP "t*" (.iterT (.varT "valtype" []) .list)]
      (.attrG (.iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")]))
        (.varG "Blist" [.typA (.varT "valtype" []), .gramA (.varG "Bvaltype" [])]))
      (.caseE "%" (.tupE [.iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")])])) [] ]

/-- The two productions of `grammar Bmut : mut?` (5.2:51-53). -/
def bmutProds : List IL.Prod :=
  [ .prodD [] (.numG 0x00) (.optE none) [],
    .prodD [] (.numG 0x01) (.optE (some (.caseE "MUT" (.tupE [])))) [] ]

/-- The two productions of `grammar Bpacktype : packtype` (5.2:55-57). -/
def bpacktypeProds : List IL.Prod :=
  [ .prodD [] (.numG 0x77) (.caseE "I16" (.tupE [])) [],
    .prodD [] (.numG 0x78) (.caseE "I8" (.tupE [])) [] ]

/-- The two productions of `grammar Bstoragetype : storagetype` (5.2:59-61). -/
def bstoragetypeProds : List IL.Prod :=
  [ .prodD [.expP "t" (.varT "valtype" [])] (.attrG (.varE "t") (.varG "Bvaltype" []))
      (.subE (.varE "t") (.varT "valtype" []) (.varT "storagetype" [])) [],
    .prodD [.expP "pt" (.varT "packtype" [])] (.attrG (.varE "pt") (.varG "Bpacktype" []))
      (.subE (.varE "pt") (.varT "packtype" []) (.varT "storagetype" [])) [] ]

/-- The sole production of `grammar Bfieldtype : fieldtype` (5.2:63-64). -/
def bfieldtypeProds : List IL.Prod :=
  [ .prodD [.expP "mut?" (.iterT (.varT "mut" []) .opt), .expP "zt" (.varT "storagetype" [])]
      (.seqG [.seqG [.attrG (.varE "zt") (.varG "Bstoragetype" [])],
              .seqG [.attrG mutOptE (.varG "Bmut" [])]])
      (.caseE "%%" (.tupE [mutOptE, .varE "zt"])) [] ]

/-- The three productions of `grammar Bcomptype : comptype` (5.2:66-69). -/
def bcomptypeProds : List IL.Prod :=
  [ .prodD [.expP "ft" (.varT "fieldtype" [])]
      (.seqG [.seqG [.numG 0x5E], .seqG [.attrG (.varE "ft") (.varG "Bfieldtype" [])]])
      (.caseE "ARRAY" (.varE "ft")) [],
    .prodD [.expP "ft*" (.iterT (.varT "fieldtype" []) .list)]
      (.seqG [.seqG [.numG 0x5F],
              .seqG [.attrG (.iterE (.varE "ft") (.mk .list [.mk "ft" (.varE "ft*")]))
                (.varG "Blist" [.typA (.varT "fieldtype" []), .gramA (.varG "Bfieldtype" [])])]])
      (.caseE "STRUCT"
        (.caseE "%" (.tupE [.iterE (.varE "ft") (.mk .list [.mk "ft" (.varE "ft*")])]))) [],
    .prodD [.expP "t_1*" (.iterT (.varT "valtype" []) .list),
            .expP "t_2*" (.iterT (.varT "valtype" []) .list)]
      (.seqG [.seqG [.numG 0x60],
              .seqG [.attrG (.caseE "%" (.tupE
                [.iterE (.varE "t_1") (.mk .list [.mk "t_1" (.varE "t_1*")])]))
                (.varG "Bresulttype" [])],
              .seqG [.attrG (.caseE "%" (.tupE
                [.iterE (.varE "t_2") (.mk .list [.mk "t_2" (.varE "t_2*")])]))
                (.varG "Bresulttype" [])]])
      (.caseE "FUNC%->%" (.tupE
        [.caseE "%" (.tupE [.iterE (.varE "t_1") (.mk .list [.mk "t_1" (.varE "t_1*")])]),
         .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk .list [.mk "t_2" (.varE "t_2*")])])])) [] ]

/-- The three productions of `grammar Bsubtype : subtype` (5.2:71-74). -/
def bsubtypeProds : List IL.Prod :=
  [ .prodD [.expP "x*" (.iterT (.varT "idx" []) .list), .expP "ct" (.varT "comptype" [])]
      (.seqG [.seqG [.numG 0x4F],
              .seqG [.attrG (.iterE (.varE "x") (.mk .list [.mk "x" (.varE "x*")]))
                (.varG "Blist" [.typA (.varT "typeidx" []), .gramA (.varG "Btypeidx" [])])],
              .seqG [.attrG (.varE "ct") (.varG "Bcomptype" [])]])
      (.caseE "SUB" (.tupE [.optE (some (.caseE "FINAL" (.tupE []))),
        .iterE (.caseE "_IDX" (.varE "x")) (.mk .list [.mk "x" (.varE "x*")]),
        .varE "ct"])) [],
    .prodD [.expP "x*" (.iterT (.varT "idx" []) .list), .expP "ct" (.varT "comptype" [])]
      (.seqG [.seqG [.numG 0x50],
              .seqG [.attrG (.iterE (.varE "x") (.mk .list [.mk "x" (.varE "x*")]))
                (.varG "Blist" [.typA (.varT "typeidx" []), .gramA (.varG "Btypeidx" [])])],
              .seqG [.attrG (.varE "ct") (.varG "Bcomptype" [])]])
      (.caseE "SUB" (.tupE [.optE none,
        .iterE (.caseE "_IDX" (.varE "x")) (.mk .list [.mk "x" (.varE "x*")]),
        .varE "ct"])) [],
    .prodD [.expP "ct" (.varT "comptype" [])]
      (.attrG (.varE "ct") (.varG "Bcomptype" []))
      (.caseE "SUB" (.tupE [.optE (some (.caseE "FINAL" (.tupE []))), .listE [],
        .varE "ct"])) [] ]

/-- The two productions of `grammar Brectype : rectype` (5.2:76-78). -/
def brectypeProds : List IL.Prod :=
  [ .prodD [.expP "st*" (.iterT (.varT "subtype" []) .list)]
      (.seqG [.seqG [.numG 0x4E],
              .seqG [.attrG (.iterE (.varE "st") (.mk .list [.mk "st" (.varE "st*")]))
                (.varG "Blist" [.typA (.varT "subtype" []), .gramA (.varG "Bsubtype" [])])]])
      (.caseE "REC" (.caseE "%" (.tupE
        [.iterE (.varE "st") (.mk .list [.mk "st" (.varE "st*")])]))) [],
    .prodD [.expP "st" (.varT "subtype" [])]
      (.attrG (.varE "st") (.varG "Bsubtype" []))
      (.caseE "REC" (.caseE "%" (.tupE [.listE [.varE "st"]]))) [] ]

/-- The four productions of `grammar Blimits : (addrtype, limits)`
(5.2:83-87). -/
def blimitsProds : List IL.Prod :=
  [ .prodD [.expP "n" (.varT "n" [])]
      (.seqG [.seqG [.numG 0x00],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu64" [])]])
      (.tupE [.caseE "I32" (.tupE []),
              .caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]), .optE none])]) [],
    .prodD [.expP "n" (.varT "n" []), .expP "m" (.varT "m" [])]
      (.seqG [.seqG [.numG 0x01],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu64" [])],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "m"])) (.varG "Bu64" [])]])
      (.tupE [.caseE "I32" (.tupE []),
              .caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]),
                .optE (some (.caseE "%" (.tupE [.varE "m"])))])]) [],
    .prodD [.expP "n" (.varT "n" [])]
      (.seqG [.seqG [.numG 0x04],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu64" [])]])
      (.tupE [.caseE "I64" (.tupE []),
              .caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]), .optE none])]) [],
    .prodD [.expP "n" (.varT "n" []), .expP "m" (.varT "m" [])]
      (.seqG [.seqG [.numG 0x05],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu64" [])],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "m"])) (.varG "Bu64" [])]])
      (.tupE [.caseE "I64" (.tupE []),
              .caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]),
                .optE (some (.caseE "%" (.tupE [.varE "m"])))])]) [] ]

/-- The sole production of `grammar Btagtype : tagtype` (5.2:89-90). -/
def btagtypeProds : List IL.Prod :=
  [ .prodD [.expP "x" (.varT "idx" [])]
      (.seqG [.seqG [.numG 0x00], .seqG [.attrG (.varE "x") (.varG "Btypeidx" [])]])
      (.caseE "_IDX" (.varE "x")) [] ]

/-- The sole production of `grammar Bglobaltype : globaltype` (5.2:92-93). -/
def bglobaltypeProds : List IL.Prod :=
  [ .prodD [.expP "mut?" (.iterT (.varT "mut" []) .opt), .expP "t" (.varT "valtype" [])]
      (.seqG [.seqG [.attrG (.varE "t") (.varG "Bvaltype" [])],
              .seqG [.attrG mutOptE (.varG "Bmut" [])]])
      (.caseE "%%" (.tupE [mutOptE, .varE "t"])) [] ]

/-- The sole production of `grammar Bmemtype : memtype` (5.2:95-96). -/
def bmemtypeProds : List IL.Prod :=
  [ .prodD [.expP "at" (.varT "addrtype" []), .expP "lim" (.varT "limits" [])]
      (.attrG (.tupE [.varE "at", .varE "lim"]) (.varG "Blimits" []))
      (.caseE "%%PAGE" (.tupE [.varE "at", .varE "lim"])) [] ]

/-- The sole production of `grammar Btabletype : tabletype` (5.2:98-99). -/
def btabletypeProds : List IL.Prod :=
  [ .prodD [.expP "at" (.varT "addrtype" []), .expP "lim" (.varT "limits" []),
            .expP "rt" (.varT "reftype" [])]
      (.seqG [.seqG [.attrG (.varE "rt") (.varG "Breftype" [])],
              .seqG [.attrG (.tupE [.varE "at", .varE "lim"]) (.varG "Blimits" [])]])
      (.caseE "%%%" (.tupE [.varE "at", .varE "lim", .varE "rt"])) [] ]

/-- The five productions of `grammar Bexterntype : externtype` (5.2:102-107). -/
def bexterntypeProds : List IL.Prod :=
  [ .prodD [.expP "x" (.varT "idx" [])]
      (.seqG [.seqG [.numG 0x00], .seqG [.attrG (.varE "x") (.varG "Btypeidx" [])]])
      (.caseE "FUNC" (.caseE "_IDX" (.varE "x"))) [],
    .prodD [.expP "tt" (.varT "tabletype" [])]
      (.seqG [.seqG [.numG 0x01], .seqG [.attrG (.varE "tt") (.varG "Btabletype" [])]])
      (.caseE "TABLE" (.varE "tt")) [],
    .prodD [.expP "mt" (.varT "memtype" [])]
      (.seqG [.seqG [.numG 0x02], .seqG [.attrG (.varE "mt") (.varG "Bmemtype" [])]])
      (.caseE "MEM" (.varE "mt")) [],
    .prodD [.expP "gt" (.varT "globaltype" [])]
      (.seqG [.seqG [.numG 0x03], .seqG [.attrG (.varE "gt") (.varG "Bglobaltype" [])]])
      (.caseE "GLOBAL" (.varE "gt")) [],
    .prodD [.expP "jt" (.varT "tagtype" [])]
      (.seqG [.seqG [.numG 0x04], .seqG [.attrG (.varE "jt") (.varG "Btagtype" [])]])
      (.caseE "TAG" (.varE "jt")) [] ]

/-- The sole production of `grammar Bu32 : u32 = BuN(32)`
(`specification/wasm-3.0/5.1-binary.values.spectec:26`). -/
def bu32Prods : List IL.Prod :=
  [ .prodD [.expP "<implicit-prod-result>" (.varT "uN" [.expA (.numE (.natN 32))])]
      (.attrG (.varE "<implicit-prod-result>") (.varG "BuN" [.expA (.numE (.natN 32))]))
      (.varE "<implicit-prod-result>") [] ]

/-- The sole production of `grammar Bu64 : u64 = BuN(64)`
(`5.1-binary.values.spectec:27`). -/
def bu64Prods : List IL.Prod :=
  [ .prodD [.expP "<implicit-prod-result>" (.varT "uN" [.expA (.numE (.natN 64))])]
      (.attrG (.varE "<implicit-prod-result>") (.varG "BuN" [.expA (.numE (.natN 64))]))
      (.varE "<implicit-prod-result>") [] ]

/-- The sole production of `grammar Btypeidx : typeidx = x:Bu32 => x`
(`5.1-binary.values.spectec:72`). -/
def btypeidxProds : List IL.Prod :=
  [ .prodD [.expP "x" (.varT "idx" [])]
      (.attrG (.varE "x") (.varG "Bu32" [])) (.varE "x") [] ]

/-- The sole production of `grammar Bs33 : s33 = BsN(33)`
(`5.1-binary.values.spectec:29`). -/
def bs33Prods : List IL.Prod :=
  [ .prodD [.expP "<implicit-prod-result>" (.varT "sN" [.expA (.numE (.natN 33))])]
      (.attrG (.varE "<implicit-prod-result>") (.varG "BsN" [.expA (.numE (.natN 33))]))
      (.varE "<implicit-prod-result>") [] ]

/-- The parameters of `grammar Blist(grammar BX : el) : el*`
(`5.1-binary.values.spectec:40-41`): a type parameter `el` and a grammar
parameter `BX`. -/
def blistParams : List Param :=
  [.typP "el", .gramP "BX" [] (.varT "el" [])]

/-- The sole production of `grammar Blist` (`5.1-binary.values.spectec:41`). -/
def blistProds : List IL.Prod :=
  [ .prodD [.expP "n" (.varT "n" []), .expP "el*" (.iterT (.varT "el" []) .list)]
      (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
              .seqG [.iterG (.attrG (.varE "el") (.varG "BX" []))
                (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])]])
      (.iterE (.varE "el") (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])) [] ]

/-- The hypotheses the comparison needs of an environment: it defines the
nonterminals of `5.2-binary.types.spectec`, and the two §5.1 nonterminals they
use, exactly as the pinned stream does.  Stating the results this way keeps
every proof independent of the other 950-odd definitions, and makes the
comparison apply verbatim to the pinned script and to the corrected one, which
agree on all of them (`#650` touches only `Bi32`, `Bi64`, `$cont` and `$utf8`).
-/
structure HasBinTypes (env : Env) : Prop where
  /-- `Bnumtype` is the pinned one. -/
  bnumtype : env.findGram? "Bnumtype" = some ([], .varT "numtype" [], bnumtypeProds)
  /-- `Bvectype` is the pinned one. -/
  bvectype : env.findGram? "Bvectype" = some ([], .varT "vectype" [], bvectypeProds)
  /-- `Babsheaptype` is the pinned one. -/
  babsheaptype : env.findGram? "Babsheaptype" = some ([], .varT "heaptype" [], babsheaptypeProds)
  /-- `Bheaptype` is the pinned one. -/
  bheaptype : env.findGram? "Bheaptype" = some ([], .varT "heaptype" [], bheaptypeProds)
  /-- `Breftype` is the pinned one. -/
  breftype : env.findGram? "Breftype" = some ([], .varT "reftype" [], breftypeProds)
  /-- `Bvaltype` is the pinned one. -/
  bvaltype : env.findGram? "Bvaltype" = some ([], .varT "valtype" [], bvaltypeProds)
  /-- `Bresulttype` is the pinned one. -/
  bresulttype : env.findGram? "Bresulttype" = some ([], .varT "resulttype" [], bresulttypeProds)
  /-- `Bmut` is the pinned one. -/
  bmut : env.findGram? "Bmut" = some ([], .iterT (.varT "mut" []) .opt, bmutProds)
  /-- `Bpacktype` is the pinned one. -/
  bpacktype : env.findGram? "Bpacktype" = some ([], .varT "packtype" [], bpacktypeProds)
  /-- `Bstoragetype` is the pinned one. -/
  bstoragetype : env.findGram? "Bstoragetype" = some ([], .varT "storagetype" [], bstoragetypeProds)
  /-- `Bfieldtype` is the pinned one. -/
  bfieldtype : env.findGram? "Bfieldtype" = some ([], .varT "fieldtype" [], bfieldtypeProds)
  /-- `Bcomptype` is the pinned one. -/
  bcomptype : env.findGram? "Bcomptype" = some ([], .varT "comptype" [], bcomptypeProds)
  /-- `Bsubtype` is the pinned one. -/
  bsubtype : env.findGram? "Bsubtype" = some ([], .varT "subtype" [], bsubtypeProds)
  /-- `Brectype` is the pinned one. -/
  brectype : env.findGram? "Brectype" = some ([], .varT "rectype" [], brectypeProds)
  /-- `Blimits` is the pinned one. -/
  blimits : env.findGram? "Blimits"
    = some ([], .tupT [.mk "_" (.varT "addrtype" []), .mk "_" (.varT "limits" [])],
        blimitsProds)
  /-- `Btagtype` is the pinned one. -/
  btagtype : env.findGram? "Btagtype" = some ([], .varT "tagtype" [], btagtypeProds)
  /-- `Bglobaltype` is the pinned one. -/
  bglobaltype : env.findGram? "Bglobaltype" = some ([], .varT "globaltype" [], bglobaltypeProds)
  /-- `Bmemtype` is the pinned one. -/
  bmemtype : env.findGram? "Bmemtype" = some ([], .varT "memtype" [], bmemtypeProds)
  /-- `Btabletype` is the pinned one. -/
  btabletype : env.findGram? "Btabletype" = some ([], .varT "tabletype" [], btabletypeProds)
  /-- `Bexterntype` is the pinned one. -/
  bexterntype : env.findGram? "Bexterntype" = some ([], .varT "externtype" [], bexterntypeProds)
  /-- `Bu32` is the pinned one. -/
  bu32 : env.findGram? "Bu32" = some ([], .varT "u32" [], bu32Prods)
  /-- `Bu64` is the pinned one. -/
  bu64 : env.findGram? "Bu64" = some ([], .varT "u64" [], bu64Prods)
  /-- `Btypeidx` is the pinned one. -/
  btypeidx : env.findGram? "Btypeidx" = some ([], .varT "typeidx" [], btypeidxProds)
  /-- `Blist` is the pinned one. -/
  blist : env.findGram? "Blist"
    = some (blistParams, .iterT (.varT "el" []) .list, blistProds)
  /-- `Bs33` is the pinned one. -/
  bs33 : env.findGram? "Bs33" = some ([], .varT "s33" [], bs33Prods)
  /-- `$s33_to_u32` is *declared* with a parameter and a result type and
  **no clauses** (`specification/wasm-3.0/3.1-numerics.scalar.spectec:7`). -/
  s33ToU32 : env.findDef? "s33_to_u32"
    = some ([.expP "s33" (.varT "s33" [])], .varT "u32" [], [])
  /-- …and no builtin interpretation supplies one either.  `Sem/Env.lean`'s
  `Builtins` can give a `hint(builtin)` function a meaning from outside the
  IL; the finding below is about the script *as pinned*, so it has to say
  that nothing is installed here.  `Builtins.none` discharges it. -/
  s33ToU32Builtin : ∀ ws, env.builtins.call "s33_to_u32" ws = Option.none

/-- **Provenance.**  The corrected wasm-3.0 script defines §5.2 exactly as
transcribed above; the `rfl` is checked by the kernel against
`Silmaril.SpecTec.IL.Binary51.wasm30binary51`. -/
theorem hasBinTypes_wasm30binary51 :
    HasBinTypes (envOfScript IL.Binary51.wasm30binary51) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- **Provenance.**  The pinned script defines §5.2 the same way: the §5.1
errata of `#650` change `Bi32`, `Bi64`, `$cont` and `$utf8`, none of which
§5.2 mentions. -/
theorem hasBinTypes_wasm30 : HasBinTypes (envOfScript Specs.wasm30) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- The LEB128 hypotheses of `Sem/Grammar.lean` hold for the corrected script
too: `#650` leaves `Bbyte` and `BuN` untouched. -/
theorem hasLeb_wasm30binary51 : HasLeb (envOfScript IL.Binary51.wasm30binary51) :=
  ⟨rfl, rfl⟩

/-! ## The bridge -/

/-- `numtype` (`1.2-syntax.types.spectec:13-14`). -/
instance instEncodeNumType : Encode Wasm.NumType :=
  Encode.ofCase
    (fun t => match t with
      | .int .i32 => ("I32", .tuple [])
      | .int .i64 => ("I64", .tuple [])
      | .float .f32 => ("F32", .tuple [])
      | .float .f64 => ("F64", .tuple []))
    (fun op v => match op, v with
      | "I32", .tuple [] => some (.int .i32)
      | "I64", .tuple [] => some (.int .i64)
      | "F32", .tuple [] => some (.float .f32)
      | "F64", .tuple [] => some (.float .f64)
      | _, _ => none)
    (by intro a; match a with
      | .int .i32 => rfl | .int .i64 => rfl | .float .f32 => rfl | .float .f64 => rfl)
    (by intro op v a h; split at h <;> first | (cases h; rfl) | simp at h)

/-- `vectype` (`1.2-syntax.types.spectec:16-17`). -/
instance instEncodeVecType : Encode Wasm.VecType :=
  Encode.ofCase
    (fun _ => ("V128", .tuple []))
    (fun op v => match op, v with
      | "V128", .tuple [] => some .v128
      | _, _ => none)
    (by rintro ⟨⟩; rfl)
    (by intro op v a h; split at h <;> first | (cases h; rfl) | simp at h)

/-- `absheaptype/syn` (`1.2-syntax.types.spectec:22-27`). -/
instance instEncodeAbsHeapType : Encode Wasm.AbsHeapType :=
  Encode.ofCase
    (fun t => match t with
      | .any => ("ANY", .tuple [])
      | .eq => ("EQ", .tuple [])
      | .i31 => ("I31", .tuple [])
      | .struct => ("STRUCT", .tuple [])
      | .array => ("ARRAY", .tuple [])
      | .none => ("NONE", .tuple [])
      | .func => ("FUNC", .tuple [])
      | .nofunc => ("NOFUNC", .tuple [])
      | .exn => ("EXN", .tuple [])
      | .noexn => ("NOEXN", .tuple [])
      | .extern => ("EXTERN", .tuple [])
      | .noextern => ("NOEXTERN", .tuple []))
    (fun op v => match op, v with
      | "ANY", .tuple [] => some .any
      | "EQ", .tuple [] => some .eq
      | "I31", .tuple [] => some .i31
      | "STRUCT", .tuple [] => some .struct
      | "ARRAY", .tuple [] => some .array
      | "NONE", .tuple [] => some .none
      | "FUNC", .tuple [] => some .func
      | "NOFUNC", .tuple [] => some .nofunc
      | "EXN", .tuple [] => some .exn
      | "NOEXN", .tuple [] => some .noexn
      | "EXTERN", .tuple [] => some .extern
      | "NOEXTERN", .tuple [] => some .noextern
      | _, _ => none)
    (by rintro ⟨⟩ <;> rfl)
    (by intro op v a h; split at h <;> first | (cases h; rfl) | simp at h)

/-- `packtype` (`1.2-syntax.types.spectec:90`). -/
instance instEncodePackType : Encode Wasm.PackType :=
  Encode.ofCase
    (fun t => match t with
      | .i8 => ("I8", .tuple [])
      | .i16 => ("I16", .tuple []))
    (fun op v => match op, v with
      | "I8", .tuple [] => some .i8
      | "I16", .tuple [] => some .i16
      | _, _ => none)
    (by rintro ⟨⟩ <;> rfl)
    (by intro op v a h; split at h <;> first | (cases h; rfl) | simp at h)

/-- `addrtype` (`1.2-syntax.types.spectec:10-11`). -/
instance instEncodeAddrType : Encode Wasm.AddrType :=
  Encode.ofCase
    (fun t => match t with
      | .i32 => ("I32", .tuple [])
      | .i64 => ("I64", .tuple []))
    (fun op v => match op, v with
      | "I32", .tuple [] => some .i32
      | "I64", .tuple [] => some .i64
      | _, _ => none)
    (by rintro ⟨⟩ <;> rfl)
    (by intro op v a h; split at h <;> first | (cases h; rfl) | simp at h)

/-- `mut?` as a value: `Bmut`'s own type is the *option*
(`specification/wasm-3.0/5.2-binary.types.spectec:51`), so a `Mutability`
encodes as an `opt`, not as a `case`. -/
def mutToValue : Wasm.Mutability → Value
  | .const => .opt none
  | .var => .opt (some (.case "MUT" (.tuple [])))

/-- The partial inverse of `mutToValue`. -/
def mutOfValue : Value → Option Wasm.Mutability
  | .opt none => some .const
  | .opt (some (.case "MUT" (.tuple []))) => some .var
  | _ => none

/-- `mut?` (`1.2-syntax.types.spectec:109`, `5.2-binary.types.spectec:51-53`). -/
instance instEncodeMutability : Encode Wasm.Mutability where
  toValue := mutToValue
  ofValue := mutOfValue
  ofValue_toValue a := by cases a <;> rfl
  toValue_ofValue v a h := by
    unfold mutOfValue at h
    split at h <;> first | (cases h; rfl) | simp at h

/-- `idx`, hence `typeidx`, which is `u32`
(`1.1-syntax.values.spectec`): the `%`-wrapped numeral. -/
instance instEncodeIdx {k : Wasm.IndexKind} : Encode (Wasm.Idx k) :=
  Encode.ofPercentNat Wasm.Idx.toNat Wasm.Idx.ofNat?
    (fun i => Wasm.Idx.ofNat?_toNat i)
    (fun n i h => ((Wasm.Idx.ofNat?_eq_some_iff n i).mp h).symm)

/-- A 64-bit limits bound, which is `u64` and so also a `%`-wrapped numeral. -/
def u64OfNat? (n : Nat) : Option (Fin (2 ^ 64)) :=
  if h : n < 2 ^ 64 then some ⟨n, h⟩ else none

/-- `u64` (`1.1-syntax.values.spectec`), the type of both limits bounds. -/
instance instEncodeFin64 : Encode (Fin (2 ^ 64)) :=
  Encode.ofPercentNat Fin.val u64OfNat?
    (fun n => by simp [u64OfNat?])
    (fun n i h => by
      simp only [u64OfNat?] at h
      split at h
      · cases h; rfl
      · exact absurd h (by simp))

/-- `limits` (`1.2-syntax.types.spectec:128`). -/
instance instEncodeLimits : Encode Wasm.Limits :=
  Encode.ofCase
    (fun l => ("[%..%]", .tuple [Encode.toValue l.min, Encode.toValue l.max]))
    (fun op v => match op, v with
      | "[%..%]", .tuple [a, b] =>
          (Encode.ofValue (α := Fin (2 ^ 64)) a).bind fun n =>
            (Encode.ofValue (α := Option (Fin (2 ^ 64))) b).bind fun m => some ⟨n, m⟩
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

/-- `memtype` (`1.2-syntax.types.spectec:132`). -/
instance instEncodeMemoryType : Encode Wasm.MemoryType :=
  Encode.ofCase
    (fun m => ("%%PAGE", .tuple [Encode.toValue m.address, Encode.toValue m.limits]))
    (fun op v => match op, v with
      | "%%PAGE", .tuple [a, b] =>
          (Encode.ofValue (α := Wasm.AddrType) a).bind fun at_ =>
            (Encode.ofValue (α := Wasm.Limits) b).bind fun lim => some ⟨at_, lim⟩
      | _, _ => none)
    (by
      rintro ⟨a, l⟩
      simp only [Encode.ofValue_toValue]
      rfl)
    (by
      intro op v a h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨x, hx, y, hy, rfl⟩ := h
        rw [Encode.toValue_eq_of_ofValue hx, Encode.toValue_eq_of_ofValue hy]
      · exact absurd h (by simp))

/-- `heaptype` (`1.2-syntax.types.spectec:44`): an abstract heap type, or a
`typeuse`, whose only binary form is `_IDX typeidx`. -/
def heapTypeView : Wasm.HeapType → MixopS × Value
  | .abstract .any => ("ANY", .tuple [])
  | .abstract .eq => ("EQ", .tuple [])
  | .abstract .i31 => ("I31", .tuple [])
  | .abstract .struct => ("STRUCT", .tuple [])
  | .abstract .array => ("ARRAY", .tuple [])
  | .abstract .none => ("NONE", .tuple [])
  | .abstract .func => ("FUNC", .tuple [])
  | .abstract .nofunc => ("NOFUNC", .tuple [])
  | .abstract .exn => ("EXN", .tuple [])
  | .abstract .noexn => ("NOEXN", .tuple [])
  | .abstract .extern => ("EXTERN", .tuple [])
  | .abstract .noextern => ("NOEXTERN", .tuple [])
  | .typeIdx x => ("_IDX", Encode.toValue x)

/-- The partial inverse of `heapTypeView`. -/
def heapTypeUnview : MixopS → Value → Option Wasm.HeapType
  | "ANY", .tuple [] => some (.abstract .any)
  | "EQ", .tuple [] => some (.abstract .eq)
  | "I31", .tuple [] => some (.abstract .i31)
  | "STRUCT", .tuple [] => some (.abstract .struct)
  | "ARRAY", .tuple [] => some (.abstract .array)
  | "NONE", .tuple [] => some (.abstract .none)
  | "FUNC", .tuple [] => some (.abstract .func)
  | "NOFUNC", .tuple [] => some (.abstract .nofunc)
  | "EXN", .tuple [] => some (.abstract .exn)
  | "NOEXN", .tuple [] => some (.abstract .noexn)
  | "EXTERN", .tuple [] => some (.abstract .extern)
  | "NOEXTERN", .tuple [] => some (.abstract .noextern)
  | "_IDX", v => (Encode.ofValue (α := Wasm.TypeIdx) v).map .typeIdx
  | _, _ => none

/-- `heaptype` (`1.2-syntax.types.spectec:44`). -/
instance instEncodeHeapType : Encode Wasm.HeapType :=
  Encode.ofCase heapTypeView heapTypeUnview
    (by
      intro a
      match a with
      | .abstract .any => rfl
      | .abstract .eq => rfl
      | .abstract .i31 => rfl
      | .abstract .struct => rfl
      | .abstract .array => rfl
      | .abstract .none => rfl
      | .abstract .func => rfl
      | .abstract .nofunc => rfl
      | .abstract .exn => rfl
      | .abstract .noexn => rfl
      | .abstract .extern => rfl
      | .abstract .noextern => rfl
      | .typeIdx x => simp [heapTypeView, heapTypeUnview, Encode.ofValue_toValue])
    (by
      intro op v a h
      unfold heapTypeUnview at h
      split at h <;>
        first
          | (cases h; rfl)
          | (simp only [Option.map_eq_some_iff] at h
             obtain ⟨x, hx, rfl⟩ := h
             rw [heapTypeView, Encode.toValue_eq_of_ofValue hx])
          | simp at h)

/-- `null?` (`1.2-syntax.types.spectec:8`), the first component of a
`reftype`. -/
def nullToValue : Bool → Value
  | true => .opt (some (.case "NULL" (.tuple [])))
  | false => .opt none

/-- The partial inverse of `nullToValue`. -/
def nullOfValue : Value → Option Bool
  | .opt none => some false
  | .opt (some (.case "NULL" (.tuple []))) => some true
  | _ => none

/-- `nullOfValue` inverts `nullToValue`. -/
@[simp] theorem nullOfValue_nullToValue (b : Bool) : nullOfValue (nullToValue b) = some b := by
  cases b <;> rfl

/-- `nullOfValue` accepts nothing else. -/
theorem nullToValue_of_nullOfValue {v : Value} {b : Bool} (h : nullOfValue v = some b) :
    nullToValue b = v := by
  unfold nullOfValue at h
  split at h <;> first | (cases h; rfl) | exact absurd h (by simp)

/-- The `reftype` payload: `REF null? heaptype`. -/
def refTypeUnview (op : MixopS) (v : Value) : Option Wasm.RefType :=
  if op = "REF" then
    match v with
    | .tuple [n, w] =>
        (nullOfValue n).bind fun b =>
          (Encode.ofValue (α := Wasm.HeapType) w).map fun ht => ⟨b, ht⟩
    | _ => none
  else none

/-- `reftype = REF null? heaptype` (`1.2-syntax.types.spectec:47`). -/
instance instEncodeRefType : Encode Wasm.RefType :=
  Encode.ofCase
    (fun r => ("REF", .tuple [nullToValue r.nullable, Encode.toValue r.heap]))
    refTypeUnview
    (by
      rintro ⟨b, ht⟩
      simp only [refTypeUnview, nullOfValue_nullToValue, Encode.ofValue_toValue]
      rfl)
    (by
      intro op v a h
      unfold refTypeUnview at h
      split at h
      · split at h
        · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨b, hb, ht, hht, rfl⟩ := h
          rw [nullToValue_of_nullOfValue hb, Encode.toValue_eq_of_ofValue hht]
          simp_all
        · simp at h
      · simp at h)

/-- `tagtype = typeuse` (`1.2-syntax.types.spectec:130`), whose binary form is
`_IDX x`.  This is *not* an `Encode` instance: `Wasm.TagType` is a Lean
abbreviation of `Wasm.TypeIdx`, which already has the bare `u32` encoding of
`typeidx`, and the two differ by the `_IDX` injection. -/
def tagTypeToValue (x : Wasm.TagType) : Value := .case "_IDX" (Encode.toValue x)

/-! ## Generic lemmas -/

/-- A list of no expressions denotes no values. -/
theorem evalExps_nil_iff {env : Env} {ρ : VarEnv} {vs : List Value} :
    EvalExps env ρ [] vs ↔ vs = [] := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExps] at h
    | succ n =>
        rw [evalExps_nil_eq env ρ n] at h
        exact (Except.ok.inj h).symm
  · rintro rfl
    exact ⟨1, evalExps_nil_eq env ρ 0⟩

/-- A nullary variant case denotes itself. -/
theorem evalExp_nullaryCase {env : Env} {ρ : VarEnv} {op : MixopS} {v : Value} :
    EvalExp env ρ (.caseE op (.tupE [])) v ↔ v = .case op (.tuple []) := by
  rw [evalExp_caseE_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [evalExp_tupE_iff] at hw
    obtain ⟨vs, hvs, rfl⟩ := hw
    rw [evalExps_nil_iff] at hvs
    subst hvs
    rfl
  · rintro rfl
    exact ⟨.tuple [], evalExp_tupE_iff.mpr ⟨[], evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩

/-- A production whose body is a single byte terminal, with no parameters, no
arguments and no premises: the shape of every §5.2 "byte table" grammar. -/
theorem prodDerives_byte {env : Env} {ρ : VarEnv} {n : Nat} {e : Exp}
    {bs : Grammar.Bytes} {l : List Value} (hn : n < 256) :
    ProdDerives env ρ [] [] (.prodD [] (.numG n) e []) bs l ↔
      bs = [UInt8.ofNat n] ∧ ∃ v, EvalExp env VarEnv.empty e v ∧ l = [v] := by
  constructor
  · rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hs, hpr, hev, hl⟩
    rw [evalArgs_nil_iff] at hw
    subst hw
    rw [bindParams] at hbp
    obtain rfl := (Option.some.inj hbp).symm
    rw [show substSym (gramArgSubst [] ([] : List IL.Arg)) (.numG n) = .numG n from rfl,
      symDerives_numG hn] at hs
    obtain ⟨rfl, -, rfl⟩ := hs
    rw [premsHold_nil_iff] at hpr
    subst hpr
    exact ⟨rfl, v, hev, hl⟩
  · rintro ⟨rfl, v, hev, rfl⟩
    refine ⟨[], VarEnv.empty, [.num (.natN (UInt8.ofNat n).toNat)], VarEnv.empty,
      VarEnv.empty, v, evalArgs_nil env ρ, rfl, ?_, premsHold_nil .., hev, rfl⟩
    rw [show substSym (gramArgSubst [] ([] : List IL.Arg)) (.numG n) = .numG n from rfl,
      symDerives_numG hn]
    exact ⟨rfl, rfl, rfl⟩

/-! ## Sequencing -/

/-- A one-element sequence is its only factor. -/
theorem symDerives_seq1 {env : Env} {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value}
    {A : IL.Sym} :
    SymDerives env ρ (.seqG [A]) bs l ρ' ↔ SymDerives env ρ A bs l ρ' := by
  rw [symDerives_seqG_cons]
  constructor
  · rintro ⟨b₁, l₁, σ, b₂, l₂, h₁, h₂, rfl, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := symDerives_seqG_nil.mp h₂
    simpa using h₁
  · intro h
    exact ⟨bs, l, ρ', [], [], h, symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, by simp, by simp⟩

/-- A two-element sequence, which is how `print.ml` spells `A B`. -/
theorem symDerives_seqG_pair {env : Env} {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} {X Y : IL.Sym} :
    SymDerives env ρ (.seqG [X, Y]) bs l ρ' ↔
      ∃ b₁ l₁ σ b₂ l₂, SymDerives env ρ X b₁ l₁ σ ∧ SymDerives env σ Y b₂ l₂ ρ' ∧
        bs = b₁ ++ b₂ ∧ l = l₁ ++ l₂ := by
  rw [symDerives_seqG_cons]
  constructor
  · rintro ⟨b₁, l₁, σ, b₂, l₂, h₁, h₂, rfl, rfl⟩
    exact ⟨b₁, l₁, σ, b₂, l₂, h₁, symDerives_seq1.mp h₂, rfl, rfl⟩
  · rintro ⟨b₁, l₁, σ, b₂, l₂, h₁, h₂, rfl, rfl⟩
    exact ⟨b₁, l₁, σ, b₂, l₂, h₁, symDerives_seq1.mpr h₂, rfl, rfl⟩

/-- A three-element sequence. -/
theorem symDerives_seqG_triple {env : Env} {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} {X Y Z : IL.Sym} :
    SymDerives env ρ (.seqG [X, Y, Z]) bs l ρ' ↔
      ∃ b₁ l₁ σ₁ b₂ l₂ σ₂ b₃ l₃, SymDerives env ρ X b₁ l₁ σ₁ ∧
        SymDerives env σ₁ Y b₂ l₂ σ₂ ∧ SymDerives env σ₂ Z b₃ l₃ ρ' ∧
        bs = b₁ ++ b₂ ++ b₃ ∧ l = l₁ ++ l₂ ++ l₃ := by
  rw [symDerives_seqG_cons]
  constructor
  · rintro ⟨b₁, l₁, σ₁, b, l, h₁, hr, rfl, rfl⟩
    obtain ⟨b₂, l₂, σ₂, b₃, l₃, h₂, h₃, rfl, rfl⟩ := symDerives_seqG_pair.mp hr
    exact ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, by simp, by simp⟩
  · rintro ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, rfl, rfl⟩
    exact ⟨b₁, l₁, σ₁, b₂ ++ b₃, l₂ ++ l₃, h₁,
      symDerives_seqG_pair.mpr ⟨b₂, l₂, σ₂, b₃, l₃, h₂, h₃, rfl, rfl⟩, by simp, by simp⟩

/-- Matching a variable that the scope does not bind, as an equivalence. -/
theorem matchExp_varE_of_none_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v : Value}
    (h : ρ.findVal? x = none) :
    MatchExp env ρ (.varE x) v ρ' ↔ ρ' = ρ.bindVal x v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        rw [matchExp, h] at hn
        exact (Except.ok.inj hn).symm
  · rintro rfl
    exact matchExp_varE_of_none h

/-- `evalExps` of a non-empty list, unfolded one step. -/
theorem evalExps_cons_eq (env : Env) (ρ : VarEnv) (n : Nat) (e : Exp) (es : List Exp) :
    (evalExps (n + 1) env ρ (e :: es) : Res (List Value))
      = (do let v ← evalExp n env ρ e
            let vs ← evalExps (n + 1) env ρ es
            pure (v :: vs)) := by
  simp [evalExps, List.mapM_cons]

/-- `evalExps` of a non-empty list. -/
theorem evalExps_cons_iff {env : Env} {ρ : VarEnv} {e : Exp} {es : List Exp}
    {vs : List Value} :
    EvalExps env ρ (e :: es) vs ↔
      ∃ v vs', EvalExp env ρ e v ∧ EvalExps env ρ es vs' ∧ vs = v :: vs' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [evalExps] at hn
    | succ n =>
        rw [evalExps_cons_eq] at hn
        simp only [Res.bind_eq_ok] at hn
        obtain ⟨v, hv, vs', hvs, hp⟩ := hn
        refine ⟨v, vs', ⟨n, hv⟩, ⟨n + 1, hvs⟩, ?_⟩
        rw [show (pure (v :: vs') : Res (List Value)) = .ok (v :: vs') from rfl] at hp
        exact (Except.ok.inj hp).symm
  · rintro ⟨v, vs', ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, rfl⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    rw [evalExps_cons_eq, evalExp_ok_of_le (le_max_left n₁ n₂) h₁,
      evalExps_ok_of_le (by omega) h₂]
    rfl

/-! ## Factoring a production -/

/-- A production of a parameterless grammar, called with no arguments and with
no premises: the body derives in a *fresh* scope, and the value expression is
evaluated in whatever scope the body left. -/
theorem prodDerives_simple {env : Env} {ρ : VarEnv} {q : List Param} {g : IL.Sym}
    {e : Exp} {bs : Grammar.Bytes} {l : List Value}
    (hsub : substSym (gramArgSubst [] ([] : List IL.Arg)) g = g) :
    ProdDerives env ρ [] [] (.prodD q g e []) bs l ↔
      ∃ l₀ σ v, SymDerives env VarEnv.empty g bs l₀ σ ∧ EvalExp env σ e v ∧ l = [v] := by
  constructor
  · rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hs, hpr, hev, hl⟩
    rw [evalArgs_nil_iff] at hw
    subst hw
    rw [bindParams] at hbp
    obtain rfl := (Option.some.inj hbp).symm
    rw [hsub] at hs
    rw [premsHold_nil_iff] at hpr
    subst hpr
    exact ⟨l₀, _, v, hs, hev, hl⟩
  · rintro ⟨l₀, σ, v, hs, hev, rfl⟩
    refine ⟨[], VarEnv.empty, l₀, σ, σ, v, evalArgs_nil env _, rfl, ?_,
      premsHold_nil .., hev, rfl⟩
    rw [hsub]
    exact hs

/-- A byte-terminal factor `(seq (num 0xNN))` of a §5.2 sequence. -/
theorem symDerives_byteFactor {env : Env} {σ σ' : VarEnv} {n : Nat}
    {b : Grammar.Bytes} {ls : List Value} (hn : n < 256) :
    SymDerives env σ (.seqG [.numG n]) b ls σ' ↔
      b = [UInt8.ofNat n] ∧ ls = [.num (.natN (UInt8.ofNat n).toNat)] ∧ σ' = σ := by
  rw [symDerives_seq1, symDerives_numG hn]

/-- An attributed-nonterminal factor `(seq (attr pat Z))` of a §5.2 sequence,
for a `Z` that restores its caller's scope — which every `VarG` does. -/
theorem symDerives_attrNT {env : Env} {σ σ' : VarEnv} {pe : Exp} {z : IL.Id}
    {args : List IL.Arg} {b : Grammar.Bytes} {ls : List Value}
    (hz : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
        SymDerives env τ (.varG z args) c ws τ' → τ' = τ) :
    SymDerives env σ (.seqG [.attrG pe (.varG z args)]) b ls σ' ↔
      ∃ w, SymDerives env σ (.varG z args) b [w] σ ∧ ls = [w] ∧ MatchExp env σ pe w σ' := by
  rw [symDerives_seq1, symDerives_attrG]
  constructor
  · rintro ⟨w, τ, hu, rfl, hm⟩
    obtain rfl := hz _ _ _ _ hu
    exact ⟨w, hu, rfl, hm⟩
  · rintro ⟨w, hu, rfl, hm⟩
    exact ⟨w, σ, hu, rfl, hm⟩

/-! ## Agreement: the `%`-wrapper grammars -/

/-- A wrapper production `grammar X : t = y:Z(args) => y`.  `Bu32`, `Bu64`
(`5.1-binary.values.spectec:26-27`) and `Btypeidx` (`:72`) all have this
shape. -/
theorem symDerives_wrapper {env : Env} {x y z : IL.Id} {t : Typ} {q : List Param}
    {args : List IL.Arg} {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value}
    (hsub : substSym (gramArgSubst [] ([] : List IL.Arg))
        (.attrG (.varE y) (.varG z args)) = .attrG (.varE y) (.varG z args))
    (hfind : VarEnv.empty.findVal? y = none)
    (hbind : ∀ w : Value, (VarEnv.empty.bindVal y w).findVal? y = some w)
    (hz : ∀ (σ σ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
        SymDerives env σ (.varG z args) b ws σ' → σ' = σ)
    (hg : env.findGram? x
      = some ([], t, [.prodD q (.attrG (.varE y) (.varG z args)) (.varE y) []])) :
    SymDerives env ρ (.varG x []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ w, SymDerives env VarEnv.empty (.varG z args) bs [w] VarEnv.empty
        ∧ l = [w] := by
  rw [symDerives_varG hg]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hs, hpr, hev, hl⟩ := hd
    rw [evalArgs_nil_iff] at hw
    subst hw
    rw [bindParams] at hbp
    obtain rfl := (Option.some.inj hbp).symm
    rw [hsub, symDerives_attrG] at hs
    obtain ⟨u, σ, hu, rfl, hm⟩ := hs
    obtain rfl := hz _ _ _ _ hu
    rw [matchExp_varE_of_none_iff hfind] at hm
    subst hm
    rw [premsHold_nil_iff] at hpr
    subst hpr
    rw [evalExp_varE_iff, hbind] at hev
    obtain rfl := Option.some.inj hev
    exact ⟨rfl, u, hu, hl⟩
  · rintro ⟨rfl, w, hw, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., [], VarEnv.empty, [w],
      VarEnv.empty.bindVal y w, VarEnv.empty.bindVal y w, w,
      evalArgs_nil env _, rfl, ?_, premsHold_nil .., ?_, rfl⟩
    · rw [hsub, symDerives_attrG]
      exact ⟨w, VarEnv.empty, hw, rfl, matchExp_varE_of_none hfind⟩
    · exact evalExp_varE_iff.mpr (hbind w)

/-- `BuN(W)` as a `SymDerives`, from `Sem/Grammar.lean`'s `bun_iff_un`. -/
theorem symDerives_bun {env : Env} (hl : HasLeb env) {W : Nat} {bs : Grammar.Bytes}
    {w : Value} :
    SymDerives env VarEnv.empty (.varG "BuN" [.expA (.numE (.natN W))]) bs [w] VarEnv.empty
      ↔ ∃ m, UN W bs m ∧ w = numCase m := by
  constructor
  · intro hd
    exact (bun_iff_un hl W bs w VarEnv.empty).mp (gramRelSup_iff.mpr ⟨_, hd⟩)
  · intro hm
    obtain ⟨σ, hd⟩ := gramRelSup_iff.mp ((bun_iff_un hl W bs w VarEnv.empty).mpr hm)
    obtain rfl := ((symDerives_varG hl.bun).mp hd).1
    exact hd

/-- `grammar Bu32 : u32 = BuN(32)` is `Silmaril.Wasm.Binary.U32`. -/
theorem symDerives_bu32 {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
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
theorem symDerives_bu64 {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
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

/-- An index encodes as the bare `u32` numeral. -/
theorem toValue_idx {k : Wasm.IndexKind} (x : Wasm.Idx k) :
    Encode.toValue x = numCase x.toNat := rfl

/-- `grammar Btypeidx : typeidx = x:Bu32 => x` (`5.1:70`) is
`Silmaril.Wasm.Binary.Index`. -/
theorem symDerives_btypeidx {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Btypeidx" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ x : Wasm.TypeIdx, Index bs x ∧ l = [Encode.toValue x] := by
  rw [symDerives_wrapper rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hd => ((symDerives_varG h.bu32).mp hd).1) h.btypeidx]
  constructor
  · rintro ⟨rfl, w, hw, rfl⟩
    obtain ⟨-, m, hm, hl'⟩ := (symDerives_bu32 h hl).mp hw
    exact ⟨rfl, ⟨⟨m, UN.lt_two_pow hm⟩⟩, hm, hl'⟩
  · rintro ⟨rfl, x, hx, rfl⟩
    exact ⟨rfl, _, (symDerives_bu32 h hl).mpr ⟨rfl, x.toNat, hx, rfl⟩, rfl⟩

/-- A two-component tuple expression. -/
theorem evalExp_tupE_pair_iff {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value} :
    EvalExp env ρ (.tupE [e₁, e₂]) v ↔
      ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ v = .tuple [v₁, v₂] := by
  rw [evalExp_tupE_iff]
  constructor
  · rintro ⟨vs, hvs, rfl⟩
    rw [evalExps_cons_iff] at hvs
    obtain ⟨v₁, vs', h₁, hvs', rfl⟩ := hvs
    rw [evalExps_cons_iff] at hvs'
    obtain ⟨v₂, vs'', h₂, hvs'', rfl⟩ := hvs'
    rw [evalExps_nil_iff] at hvs''
    subst hvs''
    exact ⟨v₁, v₂, h₁, h₂, rfl⟩
  · rintro ⟨v₁, v₂, h₁, h₂, rfl⟩
    exact ⟨[v₁, v₂], evalExps_cons_iff.mpr ⟨v₁, _, h₁,
      evalExps_cons_iff.mpr ⟨v₂, _, h₂, evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩

/-- Matching a two-variable tuple pattern against a two-component tuple. -/
theorem matchExp_tupE_pair {env : Env} {ρ ρ' : VarEnv} {x y : IL.Id} {v₁ v₂ : Value}
    (hx : ρ.findVal? x = none) (hy : (ρ.bindVal x v₁).findVal? y = none) :
    MatchExp env ρ (.tupE [.varE x, .varE y]) (.tuple [v₁, v₂]) ρ' ↔
      ρ' = (ρ.bindVal x v₁).bindVal y v₂ := by
  constructor
  · rintro ⟨n, hn⟩
    have h4 : matchExp (n + 4) env ρ (.tupE [.varE x, .varE y]) (.tuple [v₁, v₂]) = .ok ρ' :=
      matchExp_ok_of_le (by omega) hn
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asTuple?_eq_some] at h4
    obtain ⟨a, ha, h4⟩ := h4
    obtain rfl := Value.tuple.inj ha
    simp only [matchExps, matchExp, hx, Res.bind_eq_ok, Except.ok.injEq] at h4
    obtain ⟨a, rfl, c, hc, rfl⟩ := h4
    rw [hy] at hc
    exact (Except.ok.inj hc).symm
  · rintro rfl
    exact ⟨4, by simp [matchExp, matchExps, Value.asTuple?, hx, hy]⟩

/-! ## Agreement: tag types, limits and memory types -/

/-- `Btagtype = 0x00 x:Btypeidx => _IDX x` (5.2:89-90) is
`Silmaril.Wasm.Binary.Core.TagType`. -/
theorem symDerives_btagtype {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Btagtype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ x : Wasm.TagType, Core.TagType bs x ∧ l = [tagTypeToValue x] := by
  have hidx : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Btypeidx" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.btypeidx).mp hd).1
  rw [symDerives_varG h.btagtype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [btagtypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
    obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hidx).mp h₂
    obtain ⟨-, x, hx, hlw⟩ := (symDerives_btypeidx h hl).mp hw
    have hw' : w = Encode.toValue x := by simpa using hlw
    subst hw'
    rw [matchExp_varE_of_none_iff rfl] at hm
    subst hm
    obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr
      ⟨_, evalExp_varE_iff.mpr (show _ = some (Encode.toValue x) from rfl), rfl⟩)
    exact ⟨x, .mk hx, rfl⟩
  · rintro ⟨rfl, x, hx, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases hx with
    | mk hidx' =>
      refine (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_seqG_pair.mpr
        ⟨_, _, VarEnv.empty, _, _, (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
          (symDerives_attrNT hidx).mpr ⟨Encode.toValue x,
            (symDerives_btypeidx h hl).mpr ⟨rfl, x, hidx', rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩
      exact evalExp_caseE_iff.mpr
        ⟨_, evalExp_varE_iff.mpr (show _ = some (Encode.toValue x) from rfl), rfl⟩

/-- A `(attr (case "%" (tup (var y))) Bu64)` factor: it derives a `u64` and
binds `y` to the bare numeral. -/
theorem symDerives_bu64Factor {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {σ σ' : VarEnv} {y : IL.Id} {b : Grammar.Bytes} {ls : List Value}
    (hy : σ.findVal? y = none) :
    SymDerives env σ (.seqG [.attrG (.caseE "%" (.tupE [.varE y])) (.varG "Bu64" [])]) b ls σ'
      ↔ ∃ k, U64 b k ∧ ls = [numCase k] ∧ σ' = σ.bindVal y (.num (.natN k)) := by
  rw [symDerives_attrNT (fun _ _ _ _ hd => ((symDerives_varG h.bu64).mp hd).1)]
  constructor
  · rintro ⟨w, hw, rfl, hm⟩
    obtain ⟨-, k, hk, hlw⟩ := (symDerives_bu64 h hl).mp hw
    have hw' : w = numCase k := by simpa using hlw
    subst hw'
    obtain ⟨u, hu, hmv⟩ := matchExp_case_var_elim hm
    have hu' : u = .num (.natN k) := by simpa [numCase] using hu.symm
    subst hu'
    rw [matchExp_varE_of_none_iff hy] at hmv
    exact ⟨k, hk, rfl, hmv⟩
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨numCase k, (symDerives_bu64 h hl).mpr ⟨rfl, k, hk, rfl⟩, rfl,
      matchExp_case_var hy⟩

/-- `Blimits` (5.2:83-87) is `Silmaril.Wasm.Binary.Core.Limits Forms.all`.
The specification's grammar is `F = Forms.all`, where `Bound.u32` is subsumed
by `Bound.u64` (`Core/Types.lean`'s `Bound.all_iff`). -/
theorem symDerives_blimits {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Blimits" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ p : Wasm.AddrType × Wasm.Limits,
        Core.Limits Core.Forms.all bs p ∧ l = [Encode.toValue p] := by
  rw [symDerives_varG h.blimits]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [blimitsProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu64Factor h hl rfl).mp h₂
      obtain rfl := EvalExp.unique hev (evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_nullaryCase.mpr rfl, evalExp_caseE_iff.mpr ⟨_,
          evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_case_var rfl,
            evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩)
      exact ⟨(.i32, ⟨⟨k, UN.lt_two_pow hk⟩, none⟩), .i32 (.u64 rfl hk), rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, rfl, rfl⟩ :=
        symDerives_seqG_triple.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu64Factor h hl rfl).mp h₂
      obtain ⟨m, hm, rfl, rfl⟩ := (symDerives_bu64Factor h hl rfl).mp h₃
      obtain rfl := EvalExp.unique hev (evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_nullaryCase.mpr rfl, evalExp_caseE_iff.mpr ⟨_,
          evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_case_var rfl,
            evalExp_optE_some_iff.mpr ⟨_, evalExp_case_var rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩)
      exact ⟨(.i32, ⟨⟨k, UN.lt_two_pow hk⟩, some ⟨m, UN.lt_two_pow hm⟩⟩),
        .i32Max (.u64 rfl hk) (.u64 rfl hm), rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu64Factor h hl rfl).mp h₂
      obtain rfl := EvalExp.unique hev (evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_nullaryCase.mpr rfl, evalExp_caseE_iff.mpr ⟨_,
          evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_case_var rfl,
            evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩)
      exact ⟨(.i64, ⟨⟨k, UN.lt_two_pow hk⟩, none⟩), .i64 rfl hk, rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, rfl, rfl⟩ :=
        symDerives_seqG_triple.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu64Factor h hl rfl).mp h₂
      obtain ⟨m, hm, rfl, rfl⟩ := (symDerives_bu64Factor h hl rfl).mp h₃
      obtain rfl := EvalExp.unique hev (evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_nullaryCase.mpr rfl, evalExp_caseE_iff.mpr ⟨_,
          evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_case_var rfl,
            evalExp_optE_some_iff.mpr ⟨_, evalExp_case_var rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩)
      exact ⟨(.i64, ⟨⟨k, UN.lt_two_pow hk⟩, some ⟨m, UN.lt_two_pow hm⟩⟩),
        .i64Max rfl hk hm, rfl⟩
  · rintro ⟨rfl, p, hp, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hp with
    | i32 hb =>
        refine ⟨_, List.mem_cons_self .., (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_bu64Factor h hl rfl).mpr
              ⟨_, (Core.Bound.all_iff _ _).mp hb, rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_nullaryCase.mpr rfl,
          evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
            evalExp_case_var rfl, evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩
    | i32Max hb hb' =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_triple.mpr ⟨_, _, VarEnv.empty, _, _, _, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_bu64Factor h hl rfl).mpr
              ⟨_, (Core.Bound.all_iff _ _).mp hb, rfl, rfl⟩,
            (symDerives_bu64Factor h hl rfl).mpr
              ⟨_, (Core.Bound.all_iff _ _).mp hb', rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_nullaryCase.mpr rfl,
          evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
            evalExp_case_var rfl,
            evalExp_optE_some_iff.mpr ⟨_, evalExp_case_var rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    | i64 g hb =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_bu64Factor h hl rfl).mpr ⟨_, hb, rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_nullaryCase.mpr rfl,
          evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
            evalExp_case_var rfl, evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩
    | i64Max g hb hb' =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_triple.mpr ⟨_, _, VarEnv.empty, _, _, _, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_bu64Factor h hl rfl).mpr ⟨_, hb, rfl, rfl⟩,
            (symDerives_bu64Factor h hl rfl).mpr ⟨_, hb', rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_nullaryCase.mpr rfl,
          evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
            evalExp_case_var rfl,
            evalExp_optE_some_iff.mpr ⟨_, evalExp_case_var rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- `Bmemtype = (at,lim):Blimits => at lim PAGE` (5.2:95-96) is
`Silmaril.Wasm.Binary.Core.MemType Forms.all`. -/
theorem symDerives_bmemtype {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bmemtype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ m : Wasm.MemoryType, Core.MemType Core.Forms.all bs m ∧
        l = [Encode.toValue m] := by
  rw [symDerives_varG h.bmemtype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bmemtypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨w, τ, hw, rfl, hm⟩ := symDerives_attrG.mp hs
    obtain ⟨rfl, q, hq, hlw⟩ := (symDerives_blimits h hl).mp hw
    have hw' : w = Encode.toValue q := by simpa using hlw
    subst hw'
    rw [show Encode.toValue q = Value.tuple [Encode.toValue q.1, Encode.toValue q.2] from rfl,
      matchExp_tupE_pair rfl rfl] at hm
    subst hm
    obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
      evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_varE_iff.mpr rfl,
        evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩)
    exact ⟨⟨q.1, q.2⟩, .mk hq, rfl⟩
  · rintro ⟨rfl, m, hm, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases hm with
    | mk hq =>
      refine (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_attrG.mpr
        ⟨Encode.toValue ((_ : Wasm.AddrType), (_ : Wasm.Limits)), VarEnv.empty,
          (symDerives_blimits h hl).mpr ⟨rfl, _, hq, rfl⟩, rfl,
          matchExp_tupE_pair rfl rfl |>.mpr rfl⟩, ?_, rfl⟩
      exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_varE_iff.mpr rfl, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩

/-! ## Agreement: the byte-table grammars -/

/-- `Bnumtype` (5.2:7-11) is `Silmaril.Wasm.Binary.Core.NumType`. -/
theorem symDerives_bnumtype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bnumtype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.NumType, Core.NumType bs t ∧ l = [Encode.toValue t] := by
  rw [symDerives_varG h.bnumtype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bnumtypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
        rw [evalExp_nullaryCase] at hv
        subst hv
        first
          | exact ⟨.float .f64, .f64, rfl⟩
          | exact ⟨.float .f32, .f32, rfl⟩
          | exact ⟨.int .i64, .i64, rfl⟩
          | exact ⟨.int .i32, .i32, rfl⟩
  · rintro ⟨rfl, t, ht, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht <;>
      exact ⟨_, by simp [bnumtypeProds], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩

/-- `Bvectype` (5.2:13-14) is `Silmaril.Wasm.Binary.Core.VecType`. -/
theorem symDerives_bvectype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bvectype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.VecType, Core.VecType bs t ∧ l = [Encode.toValue t] := by
  rw [symDerives_varG h.bvectype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bvectypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
    rw [evalExp_nullaryCase] at hv
    subst hv
    exact ⟨.v128, .v128, rfl⟩
  · rintro ⟨rfl, t, ht, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht
    exact ⟨_, by simp [bvectypeProds], (prodDerives_byte (by decide)).mpr
      ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩

/-- `Babsheaptype` (5.2:16-28) is `Silmaril.Wasm.Binary.Core.AbsHeapType`. -/
theorem symDerives_babsheaptype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Babsheaptype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.AbsHeapType, Core.AbsHeapType bs t ∧ l = [Encode.toValue t] := by
  rw [symDerives_varG h.babsheaptype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [babsheaptypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
        rw [evalExp_nullaryCase] at hv
        subst hv
        first
          | exact ⟨.exn, .exn, rfl⟩
          | exact ⟨.array, .array, rfl⟩
          | exact ⟨.struct, .struct, rfl⟩
          | exact ⟨.i31, .i31, rfl⟩
          | exact ⟨.eq, .eq, rfl⟩
          | exact ⟨.any, .any, rfl⟩
          | exact ⟨.extern, .extern, rfl⟩
          | exact ⟨.func, .func, rfl⟩
          | exact ⟨Wasm.AbsHeapType.none, Core.AbsHeapType.none, rfl⟩
          | exact ⟨.noextern, .noextern, rfl⟩
          | exact ⟨.nofunc, .nofunc, rfl⟩
          | exact ⟨.noexn, .noexn, rfl⟩
  · rintro ⟨rfl, t, ht, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht <;>
      exact ⟨_, by simp [babsheaptypeProds], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩

/-- `Bpacktype` (5.2:55-57) is `Silmaril.Wasm.Binary.Core.PackType`. -/
theorem symDerives_bpacktype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bpacktype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.PackType, Core.PackType bs t ∧ l = [Encode.toValue t] := by
  rw [symDerives_varG h.bpacktype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bpacktypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
        rw [evalExp_nullaryCase] at hv
        subst hv
        first
          | exact ⟨.i16, .i16, rfl⟩
          | exact ⟨.i8, .i8, rfl⟩
  · rintro ⟨rfl, t, ht, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht <;>
      exact ⟨_, by simp [bpacktypeProds], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩

/-- `Bmut` (5.2:51-53) is `Silmaril.Wasm.Binary.Core.Mut`.  The grammar's own
type is `mut?`, so its value is an `opt`, not a `case`. -/
theorem symDerives_bmut {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bmut" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ m : Wasm.Mutability, Core.Mut bs m ∧ l = [Encode.toValue m] := by
  rw [symDerives_varG h.bmut]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bmutProds, List.mem_cons, List.not_mem_nil, or_false] at hp
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
    · exact ⟨_, by simp [bmutProds], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_optE_none_iff.mpr rfl, rfl⟩⟩
    · exact ⟨_, by simp [bmutProds], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_optE_some_iff.mpr ⟨_, evalExp_nullaryCase.mpr rfl, rfl⟩, rfl⟩⟩

/-- A production of a parameterless grammar called with no arguments, with
its premises kept. -/
theorem prodDerives_prem {env : Env} {ρ : VarEnv} {q : List Param} {g : IL.Sym}
    {e : Exp} {prems : List Prem} {bs : Grammar.Bytes} {l : List Value}
    (hsub : substSym (gramArgSubst [] ([] : List IL.Arg)) g = g) :
    ProdDerives env ρ [] [] (.prodD q g e prems) bs l ↔
      ∃ l₀ σ σ' v, SymDerives env VarEnv.empty g bs l₀ σ ∧ PremsHold env σ prems σ' ∧
        EvalExp env σ' e v ∧ l = [v] := by
  constructor
  · rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hs, hpr, hev, hl⟩
    rw [evalArgs_nil_iff] at hw
    subst hw
    rw [bindParams] at hbp
    obtain rfl := (Option.some.inj hbp).symm
    rw [hsub] at hs
    exact ⟨l₀, ρ₁, ρ₂, v, hs, hpr, hev, hl⟩
  · rintro ⟨l₀, σ, σ', v, hs, hpr, hev, rfl⟩
    refine ⟨[], VarEnv.empty, l₀, σ, σ', v, evalArgs_nil env _, rfl, ?_, hpr, hev, rfl⟩
    rw [hsub]
    exact hs

/-! ## A finding: `$s33_to_u32` is declared and never defined

`specification/wasm-3.0/5.2-binary.types.spectec:32` reads

```
  | x33:Bs33 => _IDX $s33_to_u32(x33)  -- if x33 >= 0
```

and `$s33_to_u32` is declared at `3.1-numerics.scalar.spectec:7` as

```
def $s33_to_u32(s33) : u32  hint(show %)
```

with **no clauses anywhere** and, unlike `$ibits_` and the other external
numerics (`3.1-numerics.scalar.spectec:31-47`), with no `hint(builtin)`.
`HasBinTypes.s33ToU32` is the machine-checked statement that the elaborated
script really does contain a clause-less `DecD`, so under `Sem/Eval.lean`'s
`callDef` — `tryClauses` on an empty clause list is `.error .undef`
(`spectec/src/il/eval.ml:647`) — the call is undefined, the production's
value expression denotes nothing, and that production of `Bheaptype` derives
nothing at all. -/

/-- `$s33_to_u32` has no clauses, so a call to it has no value. -/
theorem not_callDef_s33ToU32 {env : Env} (h : HasBinTypes env) {ρ : VarEnv}
    {args : List Arg} {v : Value} (hρ : ρ.findDef? "s33_to_u32" = none) :
    ¬ CallDef env ρ "s33_to_u32" args v := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [callDef] at hn
  | succ n =>
      rw [callDef] at hn
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hρ, Option.getD_none, h.s33ToU32] at hn
      obtain ⟨ws, -, d, hdd, hc⟩ := hn
      obtain rfl := (Option.some.inj hdd).symm
      cases n with
      | zero => simp [tryClauses, Res.elimUndef] at hc
      | succ m =>
          have hnil : tryClauses (m + 1) env [] ws = .error .undef := by simp [tryClauses]
          rw [hnil, Res.elimUndef, h.s33ToU32Builtin ws] at hc
          simp at hc

/-- **The finding, as a theorem.**  In the corrected wasm-3.0 script
`Bheaptype` (5.2:30-32) derives exactly the twelve abstract heap types: its
second production, the one that would admit a concrete type index, has no
derivation because `$s33_to_u32` is undefined. -/
theorem symDerives_bheaptype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bheaptype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ ht : Wasm.AbsHeapType, Core.AbsHeapType bs ht ∧ l = [Encode.toValue ht] := by
  rw [symDerives_varG h.bheaptype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bheaptypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨w, τ, hu, rfl, hm⟩ := symDerives_attrG.mp hs
      obtain ⟨rfl, ht, hht, hlw⟩ := (symDerives_babsheaptype h).mp hu
      have hw' : w = Encode.toValue ht := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev
        (evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl))
      exact ⟨ht, hht, rfl⟩
    · exfalso
      obtain ⟨l₀, σ, σ', v, hs, hpr, hev, -⟩ := (prodDerives_prem rfl).mp hd
      obtain ⟨w, τ, hu, rfl, hm⟩ := symDerives_attrG.mp hs
      obtain rfl := ((symDerives_varG h.bs33).mp hu).1
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain ⟨-, rfl⟩ := premsHold_ifPr_iff.mp hpr
      obtain ⟨u, hu', -⟩ := evalExp_caseE_iff.mp hev
      exact not_callDef_s33ToU32 h rfl (evalExp_callE_iff.mp hu')
  · rintro ⟨rfl, ht, hht, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., (prodDerives_simple rfl).mpr
      ⟨_, _, _, symDerives_attrG.mpr ⟨Encode.toValue ht, VarEnv.empty,
        (symDerives_babsheaptype h).mpr ⟨rfl, ht, hht, rfl⟩, rfl,
        matchExp_varE_of_none rfl⟩, ?_, rfl⟩⟩
    exact evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl)

/-- **The disagreement, exhibited.**  The single byte `0x00` is a type-index
heap type for `Silmaril/Wasm/Binary/Core/Types.lean` — `s33` `0`, the index
`0` — and the corrected wasm-3.0 grammar derives nothing from it. -/
theorem bheaptype_misses_typeIdx {env : Env} (h : HasBinTypes env) (ρ : VarEnv) :
    Core.HeapType [0x00] (.typeIdx ⟨⟨0, Nat.two_pow_pos 32⟩⟩) ∧
      ∀ v : Value, ¬ gramRelSup env ρ (.varG "Bheaptype" []) [0x00] v := by
  refine ⟨.idx _ (SN.pos 0 (by decide) (by decide)), fun v hv => ?_⟩
  obtain ⟨σ, hd⟩ := gramRelSup_iff.mp hv
  obtain ⟨-, ht, hht, -⟩ := (symDerives_bheaptype h).mp hd
  cases hht


/-- An abstract heap type encodes the same whether it is read as an
`absheaptype` or as a `heaptype`. -/
@[simp] theorem toValue_abstract (ht : Wasm.AbsHeapType) :
    Encode.toValue (Wasm.HeapType.abstract ht) = Encode.toValue ht := by
  cases ht <;> rfl

/-- A reference type to an abstract heap type, encoded. -/
@[simp] theorem toValue_refType_abs (nu : Bool) (ht : Wasm.AbsHeapType) :
    Encode.toValue (⟨nu, .abstract ht⟩ : Wasm.RefType)
      = .case "REF" (.tuple [nullToValue nu, Encode.toValue ht]) := by
  rw [show Encode.toValue (⟨nu, .abstract ht⟩ : Wasm.RefType)
    = Value.case "REF" (.tuple [nullToValue nu,
        Encode.toValue (Wasm.HeapType.abstract ht)]) from rfl, toValue_abstract]

/-- **`Breftype` (5.2:34-37), and the same finding again.**  The corrected
wasm-3.0 grammar derives exactly the reference types whose heap type is
*abstract*; `(ref $t)` and `(ref null $t)` are out of reach for the reason
`symDerives_bheaptype` gives. -/
theorem symDerives_breftype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Breftype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ (nu : Bool) (ht : Wasm.AbsHeapType),
        Core.RefType Core.Forms.all bs ⟨nu, .abstract ht⟩ ∧
        l = [Encode.toValue (⟨nu, .abstract ht⟩ : Wasm.RefType)] := by
  have hht : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bheaptype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bheaptype).mp hd).1
  rw [symDerives_varG h.breftype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [breftypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hht).mp h₂
      obtain ⟨-, ht, hab, hlw⟩ := (symDerives_bheaptype h).mp hw
      have hw' : w = Encode.toValue ht := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _,
          evalExp_optE_some_iff.mpr ⟨_, evalExp_nullaryCase.mpr rfl, rfl⟩,
          evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl), rfl⟩, rfl⟩)
      exact ⟨true, ht, .null rfl (.abs hab), by simp [toValue_refType_abs, nullToValue]⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hht).mp h₂
      obtain ⟨-, ht, hab, hlw⟩ := (symDerives_bheaptype h).mp hw
      have hw' : w = Encode.toValue ht := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_optE_none_iff.mpr rfl,
          evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl), rfl⟩, rfl⟩)
      exact ⟨false, ht, .nonNull rfl (.abs hab), by simp [toValue_refType_abs, nullToValue]⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨w, τ, hw, rfl, hm⟩ := symDerives_attrG.mp hs
      obtain ⟨rfl, ht, hab, hlw⟩ := (symDerives_babsheaptype h).mp hw
      have hw' : w = Encode.toValue ht := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _,
          evalExp_optE_some_iff.mpr ⟨_, evalExp_nullaryCase.mpr rfl, rfl⟩,
          evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl), rfl⟩, rfl⟩)
      exact ⟨true, ht, .abs hab, by simp [toValue_refType_abs, nullToValue]⟩
  · rintro ⟨rfl, nu, ht, hr, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hr with
    | null g hh =>
        cases hh with
        | abs hab =>
            refine ⟨_, List.mem_cons_self .., (prodDerives_simple rfl).mpr
              ⟨_, _, _, symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
                (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
                (symDerives_attrNT hht).mpr ⟨Encode.toValue ht,
                  (symDerives_bheaptype h).mpr ⟨rfl, ht, hab, rfl⟩, rfl,
                  matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
            exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
              evalExp_optE_some_iff.mpr ⟨_, evalExp_nullaryCase.mpr rfl, rfl⟩,
              evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl), rfl⟩,
              by simp [toValue_refType_abs, nullToValue]⟩
    | nonNull g hh =>
        cases hh with
        | abs hab =>
            refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
              (prodDerives_simple rfl).mpr
              ⟨_, _, _, symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
                (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
                (symDerives_attrNT hht).mpr ⟨Encode.toValue ht,
                  (symDerives_bheaptype h).mpr ⟨rfl, ht, hab, rfl⟩, rfl,
                  matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
            exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
              evalExp_optE_none_iff.mpr rfl,
              evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl), rfl⟩,
              by simp [toValue_refType_abs, nullToValue]⟩
    | abs hab =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_attrG.mpr
            ⟨Encode.toValue ht, VarEnv.empty,
              (symDerives_babsheaptype h).mpr ⟨rfl, ht, hab, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
          evalExp_optE_some_iff.mpr ⟨_, evalExp_nullaryCase.mpr rfl, rfl⟩,
          evalExp_varE_iff.mpr (show _ = some (Encode.toValue ht) from rfl), rfl⟩,
          by simp [toValue_refType_abs, nullToValue]⟩

/-! ## The reach of the corrected grammar

`symDerives_bheaptype` is a *restriction*, and it propagates: every §5.2
nonterminal above `Bheaptype` can only reach the part of our abstract syntax
whose reference types point at abstract heap types.  These predicates name
that part, one per syntactic class. -/

/-- A heap type the corrected wasm-3.0 binary grammar can reach. -/
def HeapAbs : Wasm.HeapType → Prop
  | .abstract _ => True
  | .typeIdx _ => False

/-- A reference type the corrected wasm-3.0 binary grammar can reach. -/
def RefAbs (r : Wasm.RefType) : Prop := HeapAbs r.heap

/-- A value type the corrected wasm-3.0 binary grammar can reach. -/
def ValAbs : Wasm.ValType → Prop
  | .ref r => RefAbs r
  | .num _ | .vec _ => True

/-- A storage type the corrected wasm-3.0 binary grammar can reach. -/
def StorageAbs : Wasm.StorageType → Prop
  | .val t => ValAbs t
  | .packed _ => True

/-- A table type the corrected wasm-3.0 binary grammar can reach. -/
def TableAbs (tt : Wasm.TableType) : Prop := RefAbs tt.element

/-- `Breftype`, in the `RefAbs` form the nonterminals above it use. -/
theorem symDerives_breftype' {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Breftype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ r : Wasm.RefType, Core.RefType Core.Forms.all bs r ∧ RefAbs r ∧
        l = [Encode.toValue r] := by
  rw [symDerives_breftype h]
  constructor
  · rintro ⟨rfl, nu, ht, hr, rfl⟩
    exact ⟨rfl, ⟨nu, .abstract ht⟩, hr, trivial, rfl⟩
  · rintro ⟨rfl, ⟨nu, hp⟩, hr, hab, rfl⟩
    cases hp with
    | abstract ht => exact ⟨rfl, nu, ht, hr, rfl⟩
    | typeIdx x => exact absurd hab (by simp [RefAbs, HeapAbs])

/-! ## Agreement: value types, storage types and table types -/

/-- `valtype` (`1.2-syntax.types.spectec:50`), a union of three variants. -/
def valTypeToValue : Wasm.ValType → Value
  | .num t => Encode.toValue t
  | .vec t => Encode.toValue t
  | .ref t => Encode.toValue t

/-- The partial inverse of `valTypeToValue`. -/
def valTypeOfValue (v : Value) : Option Wasm.ValType :=
  match Encode.ofValue (α := Wasm.NumType) v with
  | some t => some (.num t)
  | none =>
    match Encode.ofValue (α := Wasm.VecType) v with
    | some t => some (.vec t)
    | none => (Encode.ofValue (α := Wasm.RefType) v).map .ref

/-- `valtype` (`1.2-syntax.types.spectec:50`). -/
instance instEncodeValType : Encode Wasm.ValType where
  toValue := valTypeToValue
  ofValue := valTypeOfValue
  ofValue_toValue a := by
    match a with
    | .num (.int .i32) | .num (.int .i64) | .num (.float .f32) | .num (.float .f64)
    | .vec .v128 => rfl
    | .ref r =>
        show valTypeOfValue (Encode.toValue r) = some (.ref r)
        rw [valTypeOfValue, show Encode.ofValue (α := Wasm.NumType) (Encode.toValue r)
          = none from rfl, show Encode.ofValue (α := Wasm.VecType) (Encode.toValue r)
          = none from rfl, Encode.ofValue_toValue]
        rfl
  toValue_ofValue v a h := by
    rw [valTypeOfValue] at h
    split at h
    · rename_i t ht
      cases h
      exact Encode.toValue_eq_of_ofValue ht
    · split at h
      · rename_i t ht
        cases h
        exact Encode.toValue_eq_of_ofValue ht
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        exact Encode.toValue_eq_of_ofValue hr

/-- `storagetype` (`1.2-syntax.types.spectec:92`). -/
def storageTypeToValue : Wasm.StorageType → Value
  | .val t => Encode.toValue t
  | .packed t => Encode.toValue t

/-- The partial inverse of `storageTypeToValue`. -/
def storageTypeOfValue (v : Value) : Option Wasm.StorageType :=
  match Encode.ofValue (α := Wasm.ValType) v with
  | some t => some (.val t)
  | none => (Encode.ofValue (α := Wasm.PackType) v).map .packed

/-- `storagetype` (`1.2-syntax.types.spectec:92`). -/
instance instEncodeStorageType : Encode Wasm.StorageType where
  toValue := storageTypeToValue
  ofValue := storageTypeOfValue
  ofValue_toValue a := by
    match a with
    | .val t =>
        show storageTypeOfValue (Encode.toValue t) = some (.val t)
        rw [storageTypeOfValue, Encode.ofValue_toValue]
    | .packed .i8 | .packed .i16 => rfl
  toValue_ofValue v a h := by
    rw [storageTypeOfValue] at h
    split at h
    · rename_i t ht
      cases h
      exact Encode.toValue_eq_of_ofValue ht
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨t, ht, rfl⟩ := h
      exact Encode.toValue_eq_of_ofValue ht

/-- `tabletype = addrtype limits reftype` (`1.2-syntax.types.spectec:133`). -/
instance instEncodeTableType : Encode Wasm.TableType :=
  Encode.ofCase
    (fun tt => ("%%%", .tuple [Encode.toValue tt.address, Encode.toValue tt.limits,
      Encode.toValue tt.element]))
    (fun op v => match op, v with
      | "%%%", .tuple [a, b, c] =>
          (Encode.ofValue (α := Wasm.AddrType) a).bind fun at_ =>
            (Encode.ofValue (α := Wasm.Limits) b).bind fun lim =>
              (Encode.ofValue (α := Wasm.RefType) c).map fun rt => ⟨at_, lim, rt⟩
      | _, _ => none)
    (by
      rintro ⟨a, l, r⟩
      simp only [Encode.ofValue_toValue]
      rfl)
    (by
      intro op v a h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
        rw [Encode.toValue_eq_of_ofValue hx, Encode.toValue_eq_of_ofValue hy,
          Encode.toValue_eq_of_ofValue hz]
      · exact absurd h (by simp))

/-- A three-component tuple expression. -/
theorem evalExp_tupE_triple_iff {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v : Value} :
    EvalExp env ρ (.tupE [e₁, e₂, e₃]) v ↔
      ∃ v₁ v₂ v₃, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ EvalExp env ρ e₃ v₃ ∧
        v = .tuple [v₁, v₂, v₃] := by
  rw [evalExp_tupE_iff]
  constructor
  · rintro ⟨vs, hvs, rfl⟩
    rw [evalExps_cons_iff] at hvs
    obtain ⟨v₁, vs₁, h₁, hvs₁, rfl⟩ := hvs
    rw [evalExps_cons_iff] at hvs₁
    obtain ⟨v₂, vs₂, h₂, hvs₂, rfl⟩ := hvs₁
    rw [evalExps_cons_iff] at hvs₂
    obtain ⟨v₃, vs₃, h₃, hvs₃, rfl⟩ := hvs₂
    rw [evalExps_nil_iff] at hvs₃
    subst hvs₃
    exact ⟨v₁, v₂, v₃, h₁, h₂, h₃, rfl⟩
  · rintro ⟨v₁, v₂, v₃, h₁, h₂, h₃, rfl⟩
    exact ⟨[v₁, v₂, v₃], evalExps_cons_iff.mpr ⟨v₁, _, h₁,
      evalExps_cons_iff.mpr ⟨v₂, _, h₂,
        evalExps_cons_iff.mpr ⟨v₃, _, h₃, evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- A production `y:Z => y` with a subtype coercion on the result: the three
productions of `Bvaltype` (5.2:39-42) and the two of `Bstoragetype`
(5.2:59-61). -/
theorem prodDerives_subWrapper {env : Env} {ρ : VarEnv} {q : List Param} {y z : IL.Id}
    {t₁ t₂ : Typ} {bs : Grammar.Bytes} {l : List Value}
    (hz : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
        SymDerives env τ (.varG z []) c ws τ' → τ' = τ)
    (hfind : VarEnv.empty.findVal? y = none)
    (hbind : ∀ w : Value, (VarEnv.empty.bindVal y w).findVal? y = some w) :
    ProdDerives env ρ [] []
        (.prodD q (.attrG (.varE y) (.varG z [])) (.subE (.varE y) t₁ t₂) []) bs l ↔
      ∃ w, SymDerives env VarEnv.empty (.varG z []) bs [w] VarEnv.empty ∧ l = [w] := by
  rw [prodDerives_simple rfl]
  constructor
  · rintro ⟨l₀, σ, v, hs, hev, rfl⟩
    obtain ⟨w, τ, hu, rfl, hm⟩ := symDerives_attrG.mp hs
    obtain rfl := hz _ _ _ _ hu
    rw [matchExp_varE_of_none_iff hfind] at hm
    subst hm
    rw [evalExp_subE_iff, evalExp_varE_iff, hbind] at hev
    obtain rfl := Option.some.inj hev
    exact ⟨w, hu, rfl⟩
  · rintro ⟨w, hu, rfl⟩
    exact ⟨[w], _, w,
      symDerives_attrG.mpr ⟨w, VarEnv.empty, hu, rfl, matchExp_varE_of_none hfind⟩,
      evalExp_subE_iff.mpr (evalExp_varE_iff.mpr (hbind w)), rfl⟩

/-- `Bvaltype` (5.2:39-42) is `Core.ValType Forms.all` restricted to `ValAbs`. -/
theorem symDerives_bvaltype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bvaltype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.ValType, Core.ValType Core.Forms.all bs t ∧ ValAbs t ∧
        l = [Encode.toValue t] := by
  rw [symDerives_varG h.bvaltype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bvaltypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · obtain ⟨w, hw, rfl⟩ := (prodDerives_subWrapper
        (fun _ _ _ _ hd => ((symDerives_varG h.bnumtype).mp hd).1) rfl (fun _ => rfl)).mp hd
      obtain ⟨-, t, ht, hlw⟩ := (symDerives_bnumtype h).mp hw
      exact ⟨.num t, .num ht, trivial, hlw⟩
    · obtain ⟨w, hw, rfl⟩ := (prodDerives_subWrapper
        (fun _ _ _ _ hd => ((symDerives_varG h.bvectype).mp hd).1) rfl (fun _ => rfl)).mp hd
      obtain ⟨-, t, ht, hlw⟩ := (symDerives_bvectype h).mp hw
      exact ⟨.vec t, .vec ht, trivial, hlw⟩
    · obtain ⟨w, hw, rfl⟩ := (prodDerives_subWrapper
        (fun _ _ _ _ hd => ((symDerives_varG h.breftype).mp hd).1) rfl (fun _ => rfl)).mp hd
      obtain ⟨-, r, hr, hab, hlw⟩ := (symDerives_breftype' h).mp hw
      exact ⟨.ref r, .ref hr, hab, hlw⟩
  · rintro ⟨rfl, t, ht, hab, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht with
    | num ht =>
        exact ⟨_, List.mem_cons_self .., (prodDerives_subWrapper
          (fun _ _ _ _ hd => ((symDerives_varG h.bnumtype).mp hd).1) rfl (fun _ => rfl)).mpr
          ⟨_, (symDerives_bnumtype h).mpr ⟨rfl, _, ht, rfl⟩, rfl⟩⟩
    | vec ht =>
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (prodDerives_subWrapper
          (fun _ _ _ _ hd => ((symDerives_varG h.bvectype).mp hd).1) rfl (fun _ => rfl)).mpr
          ⟨_, (symDerives_bvectype h).mpr ⟨rfl, _, ht, rfl⟩, rfl⟩⟩
    | ref hr =>
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_subWrapper
          (fun _ _ _ _ hd => ((symDerives_varG h.breftype).mp hd).1) rfl (fun _ => rfl)).mpr
          ⟨_, (symDerives_breftype' h).mpr ⟨rfl, _, hr, hab, rfl⟩, rfl⟩⟩

/-- `Bstoragetype` (5.2:59-61) is `Core.StorageType Forms.all` restricted to
`StorageAbs`. -/
theorem symDerives_bstoragetype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bstoragetype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.StorageType, Core.StorageType Core.Forms.all bs t ∧ StorageAbs t ∧
        l = [Encode.toValue t] := by
  rw [symDerives_varG h.bstoragetype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bstoragetypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨w, hw, rfl⟩ := (prodDerives_subWrapper
        (fun _ _ _ _ hd => ((symDerives_varG h.bvaltype).mp hd).1) rfl (fun _ => rfl)).mp hd
      obtain ⟨-, t, ht, hab, hlw⟩ := (symDerives_bvaltype h).mp hw
      exact ⟨.val t, .val ht, hab, hlw⟩
    · obtain ⟨w, hw, rfl⟩ := (prodDerives_subWrapper
        (fun _ _ _ _ hd => ((symDerives_varG h.bpacktype).mp hd).1) rfl (fun _ => rfl)).mp hd
      obtain ⟨-, t, ht, hlw⟩ := (symDerives_bpacktype h).mp hw
      exact ⟨.packed t, .packed ht, trivial, hlw⟩
  · rintro ⟨rfl, t, ht, hab, rfl⟩
    refine ⟨rfl, ?_⟩
    cases ht with
    | val ht =>
        exact ⟨_, List.mem_cons_self .., (prodDerives_subWrapper
          (fun _ _ _ _ hd => ((symDerives_varG h.bvaltype).mp hd).1) rfl (fun _ => rfl)).mpr
          ⟨_, (symDerives_bvaltype h).mpr ⟨rfl, _, ht, hab, rfl⟩, rfl⟩⟩
    | packed ht =>
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (prodDerives_subWrapper
          (fun _ _ _ _ hd => ((symDerives_varG h.bpacktype).mp hd).1) rfl (fun _ => rfl)).mpr
          ⟨_, (symDerives_bpacktype h).mpr ⟨rfl, _, ht, rfl⟩, rfl⟩⟩

/-- `Btabletype = rt:Breftype (at,lim):Blimits => at lim rt` (5.2:98-99) is
`Core.TableType Forms.all` restricted to `TableAbs`. -/
theorem symDerives_btabletype {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Btabletype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ tt : Wasm.TableType, Core.TableType Core.Forms.all bs tt ∧ TableAbs tt ∧
        l = [Encode.toValue tt] := by
  have href : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Breftype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.breftype).mp hd).1
  have hlim : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Blimits" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.blimits).mp hd).1
  rw [symDerives_varG h.btabletype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [btabletypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT href).mp h₁
    obtain ⟨-, r, hr, hab, hlw⟩ := (symDerives_breftype' h).mp hw
    have hw' : w = Encode.toValue r := by simpa using hlw
    subst hw'
    rw [matchExp_varE_of_none_iff rfl] at hm
    subst hm
    obtain ⟨u, hu, rfl, hm'⟩ := (symDerives_attrNT hlim).mp h₂
    obtain ⟨-, q, hq, hlu⟩ := (symDerives_blimits h hl).mp hu
    have hu' : u = Encode.toValue q := by simpa using hlu
    subst hu'
    rw [show Encode.toValue q = Value.tuple [Encode.toValue q.1, Encode.toValue q.2] from rfl,
      matchExp_tupE_pair rfl rfl] at hm'
    subst hm'
    obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
      evalExp_tupE_triple_iff.mpr ⟨_, _, _, evalExp_varE_iff.mpr rfl,
        evalExp_varE_iff.mpr rfl, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩)
    exact ⟨⟨q.1, q.2, r⟩, .mk hr hq, hab, rfl⟩
  · rintro ⟨rfl, tt, htt, hab, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases htt with
    | mk hr hq =>
      refine (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_seqG_pair.mpr
        ⟨_, _, VarEnv.empty.bindVal "rt" (Encode.toValue _), _, _,
          (symDerives_attrNT href).mpr ⟨Encode.toValue _,
            (symDerives_breftype' h).mpr ⟨rfl, _, hr, hab, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩,
          (symDerives_attrNT hlim).mpr ⟨Encode.toValue ((_ : Wasm.AddrType), (_ : Wasm.Limits)),
            (symDerives_blimits h hl).mpr ⟨rfl, _, hq, rfl⟩, rfl,
            matchExp_tupE_pair rfl rfl |>.mpr rfl⟩, rfl, rfl⟩, ?_, rfl⟩
      exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_triple_iff.mpr
        ⟨_, _, _, evalExp_varE_iff.mpr rfl, evalExp_varE_iff.mpr rfl,
          evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩

/-! ## The `mut?` iteration

`Bfieldtype` (5.2:63-64) and `Bglobaltype` (5.2:92-93) bind `Bmut`'s value
through the pattern `(iter (var "mut") opt (dom "mut" (var "mut?")))`, which
`Sem/Eval.lean` reads with `matchIterE`/`evalIterE`.  Both directions collapse
to "bind `mut?` to the option itself", which is what these two lemmas say. -/

/-- The `mut?` pattern binds `mut?` to the option it is matched against. -/
theorem matchExp_mutOptE_mk {env : Env} {ρ : VarEnv} {o : Option Value}
    (h1 : ρ.findVal? "mut" = none) (h2 : ρ.findVal? "mut?" = none)
    (h3 : ∀ w : Value, (ρ.bindVal "mut" w).findVal? "mut" = some w) :
    MatchExp env ρ mutOptE (.opt o) (ρ.bindVal "mut?" (.opt o)) := by
  cases o with
  | none =>
      exact ⟨6, by
        simp [mutOptE, matchExp, matchIterE, matchExps, Value.asOpt?, Res.ofOption,
          domSrc, domVar, h2]⟩
  | some w =>
      exact ⟨6, by
        simp [mutOptE, matchExp, matchIterE, matchExps, Value.asOpt?, Res.ofOption,
          VarEnv.findVals?, domSrc, domVar, h1, h2, h3]⟩

/-- The `mut?` pattern, as an equivalence, via `MatchExp.unique`. -/
theorem matchExp_mutOptE {env : Env} {ρ ρ' : VarEnv} {o : Option Value}
    (h1 : ρ.findVal? "mut" = none) (h2 : ρ.findVal? "mut?" = none)
    (h3 : ∀ w : Value, (ρ.bindVal "mut" w).findVal? "mut" = some w) :
    MatchExp env ρ mutOptE (.opt o) ρ' ↔ ρ' = ρ.bindVal "mut?" (.opt o) := by
  constructor
  · intro hm
    exact hm.unique (matchExp_mutOptE_mk h1 h2 h3)
  · rintro rfl
    exact matchExp_mutOptE_mk h1 h2 h3

/-- The `mut?` expression evaluates back to the option `mut?` is bound to. -/
theorem evalExp_mutOptE {env : Env} {ρ : VarEnv} {o : Option Value}
    (h : ρ.findVal? "mut?" = some (.opt o))
    (h' : ∀ w : Value, (ρ.bindVals [("mut", w)]).findVal? "mut" = some w) :
    EvalExp env ρ mutOptE (.opt o) := by
  cases o with
  | none =>
      exact ⟨6, by
        simp [mutOptE, evalExp, evalIterE, evalDoms, Value.asOpt?, Res.ofOption,
          domSrc, domVar, h]⟩
  | some w =>
      exact ⟨6, by
        simp [mutOptE, evalExp, evalIterE, evalDoms, Value.asOpt?, Res.ofOption,
          domSrc, domVar, h, h']⟩

/-- The option a `Mutability` encodes as. -/
def mutOpt : Wasm.Mutability → Option Value
  | .const => none
  | .var => some (.case "MUT" (.tuple []))

/-- `Encode.toValue` of a `Mutability`, as an `opt`. -/
@[simp] theorem toValue_mut (m : Wasm.Mutability) :
    Encode.toValue m = Value.opt (mutOpt m) := by
  cases m <;> rfl

/-! ## Agreement: field types, global types and external types -/

/-- A field type the corrected wasm-3.0 binary grammar can reach. -/
def FieldAbs (f : Wasm.FieldType) : Prop := StorageAbs f.storage

/-- A global type the corrected wasm-3.0 binary grammar can reach. -/
def GlobalAbs (g : Wasm.GlobalType) : Prop := ValAbs g.value

/-- An external type the corrected wasm-3.0 binary grammar can reach. -/
def ExternAbs : Wasm.ExternType → Prop
  | .table tt => TableAbs tt
  | .global g => GlobalAbs g
  | .func _ | .memory _ | .tag _ => True

/-- `fieldtype = mut? storagetype` (`1.2-syntax.types.spectec:112`). -/
instance instEncodeFieldType : Encode Wasm.FieldType :=
  Encode.ofCase
    (fun f => ("%%", .tuple [Encode.toValue f.mutability, Encode.toValue f.storage]))
    (fun op v => match op, v with
      | "%%", .tuple [a, b] =>
          (Encode.ofValue (α := Wasm.Mutability) a).bind fun m =>
            (Encode.ofValue (α := Wasm.StorageType) b).map fun zt => ⟨m, zt⟩
      | _, _ => none)
    (by
      rintro ⟨m, zt⟩
      simp only [Encode.ofValue_toValue]
      rfl)
    (by
      intro op v a h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨m, hm, zt, hzt, rfl⟩ := h
        rw [Encode.toValue_eq_of_ofValue hm, Encode.toValue_eq_of_ofValue hzt]
      · exact absurd h (by simp))

/-- `globaltype = mut? valtype` (`1.2-syntax.types.spectec:131`). -/
instance instEncodeGlobalType : Encode Wasm.GlobalType :=
  Encode.ofCase
    (fun g => ("%%", .tuple [Encode.toValue g.mutability, Encode.toValue g.value]))
    (fun op v => match op, v with
      | "%%", .tuple [a, b] =>
          (Encode.ofValue (α := Wasm.Mutability) a).bind fun m =>
            (Encode.ofValue (α := Wasm.ValType) b).map fun t => ⟨m, t⟩
      | _, _ => none)
    (by
      rintro ⟨m, t⟩
      simp only [Encode.ofValue_toValue]
      rfl)
    (by
      intro op v a h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨m, hm, t, ht, rfl⟩ := h
        rw [Encode.toValue_eq_of_ofValue hm, Encode.toValue_eq_of_ofValue ht]
      · exact absurd h (by simp))

/-- `Encode.toValue` of a field type, with the mutability spelled out. -/
@[simp] theorem toValue_fieldType (m : Wasm.Mutability) (zt : Wasm.StorageType) :
    Encode.toValue (⟨m, zt⟩ : Wasm.FieldType)
      = .case "%%" (.tuple [Value.opt (mutOpt m), Encode.toValue zt]) := by
  rw [show Encode.toValue (⟨m, zt⟩ : Wasm.FieldType)
    = Value.case "%%" (.tuple [Encode.toValue m, Encode.toValue zt]) from rfl, toValue_mut]

/-- `Encode.toValue` of a global type, with the mutability spelled out. -/
@[simp] theorem toValue_globalType (m : Wasm.Mutability) (t : Wasm.ValType) :
    Encode.toValue (⟨m, t⟩ : Wasm.GlobalType)
      = .case "%%" (.tuple [Value.opt (mutOpt m), Encode.toValue t]) := by
  rw [show Encode.toValue (⟨m, t⟩ : Wasm.GlobalType)
    = Value.case "%%" (.tuple [Encode.toValue m, Encode.toValue t]) from rfl, toValue_mut]

/-- A `(attr pat Bmut)` factor: it derives a `mut?` and binds `mut?` to it. -/
theorem symDerives_bmutFactor {env : Env} (h : HasBinTypes env) {σ σ' : VarEnv}
    {b : Grammar.Bytes} {ls : List Value}
    (h1 : σ.findVal? "mut" = none) (h2 : σ.findVal? "mut?" = none)
    (h3 : ∀ w : Value, (σ.bindVal "mut" w).findVal? "mut" = some w) :
    SymDerives env σ (.seqG [.attrG mutOptE (.varG "Bmut" [])]) b ls σ' ↔
      ∃ m : Wasm.Mutability, Core.Mut b m ∧ ls = [Encode.toValue m] ∧
        σ' = σ.bindVal "mut?" (.opt (mutOpt m)) := by
  rw [symDerives_attrNT (fun _ _ _ _ hd => ((symDerives_varG h.bmut).mp hd).1)]
  constructor
  · rintro ⟨w, hw, rfl, hm⟩
    obtain ⟨-, m, hmm, hlw⟩ := (symDerives_bmut h).mp hw
    have hw' : w = Encode.toValue m := by simpa using hlw
    subst hw'
    rw [toValue_mut, matchExp_mutOptE h1 h2 h3] at hm
    exact ⟨m, hmm, rfl, hm⟩
  · rintro ⟨m, hmm, rfl, rfl⟩
    refine ⟨Encode.toValue m, (symDerives_bmut h).mpr ⟨rfl, m, hmm, rfl⟩, rfl, ?_⟩
    rw [toValue_mut]
    exact matchExp_mutOptE_mk h1 h2 h3

/-- `Bfieldtype = zt:Bstoragetype mut?:Bmut => mut? zt` (5.2:63-64) is
`Core.FieldType Forms.all` restricted to `FieldAbs`. -/
theorem symDerives_bfieldtype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bfieldtype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ f : Wasm.FieldType, Core.FieldType Core.Forms.all bs f ∧ FieldAbs f ∧
        l = [Encode.toValue f] := by
  have hst : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bstoragetype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bstoragetype).mp hd).1
  rw [symDerives_varG h.bfieldtype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bfieldtypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hst).mp h₁
    obtain ⟨-, zt, hzt, hab, hlw⟩ := (symDerives_bstoragetype h).mp hw
    have hw' : w = Encode.toValue zt := by simpa using hlw
    subst hw'
    rw [matchExp_varE_of_none_iff rfl] at hm
    subst hm
    obtain ⟨m, hmm, rfl, rfl⟩ := (symDerives_bmutFactor h rfl rfl (fun _ => rfl)).mp h₂
    obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
      evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_mutOptE rfl (fun _ => rfl),
        evalExp_varE_iff.mpr (show _ = some (Encode.toValue zt) from rfl), rfl⟩, rfl⟩)
    exact ⟨⟨m, zt⟩, .mk hzt hmm, hab, by simp [toValue_fieldType]⟩
  · rintro ⟨rfl, f, hf, hab, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases hf with
    | @mk b b' zt m hzt hmm =>
      refine (prodDerives_simple rfl).mpr ⟨_, _,
        Value.case "%%" (.tuple [Value.opt (mutOpt m), Encode.toValue zt]),
        symDerives_seqG_pair.mpr
        ⟨_, _, VarEnv.empty.bindVal "zt" (Encode.toValue zt), _, _,
          (symDerives_attrNT hst).mpr ⟨Encode.toValue zt,
            (symDerives_bstoragetype h).mpr ⟨rfl, zt, hzt, hab, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩,
          (symDerives_bmutFactor h rfl rfl (fun _ => rfl)).mpr ⟨m, hmm, rfl, rfl⟩,
          rfl, rfl⟩, ?_, by simp [toValue_fieldType]⟩
      exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_mutOptE rfl (fun _ => rfl),
        evalExp_varE_iff.mpr (show _ = some (Encode.toValue zt) from rfl), rfl⟩, rfl⟩

/-- `Bglobaltype = t:Bvaltype mut?:Bmut => mut? t` (5.2:92-93) is
`Core.GlobalType Forms.all` restricted to `GlobalAbs`. -/
theorem symDerives_bglobaltype {env : Env} (h : HasBinTypes env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bglobaltype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ g : Wasm.GlobalType, Core.GlobalType Core.Forms.all bs g ∧ GlobalAbs g ∧
        l = [Encode.toValue g] := by
  have hvt : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bvaltype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bvaltype).mp hd).1
  rw [symDerives_varG h.bglobaltype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bglobaltypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hvt).mp h₁
    obtain ⟨-, t, ht, hab, hlw⟩ := (symDerives_bvaltype h).mp hw
    have hw' : w = Encode.toValue t := by simpa using hlw
    subst hw'
    rw [matchExp_varE_of_none_iff rfl] at hm
    subst hm
    obtain ⟨m, hmm, rfl, rfl⟩ := (symDerives_bmutFactor h rfl rfl (fun _ => rfl)).mp h₂
    obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
      evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_mutOptE rfl (fun _ => rfl),
        evalExp_varE_iff.mpr (show _ = some (Encode.toValue t) from rfl), rfl⟩, rfl⟩)
    exact ⟨⟨m, t⟩, .mk ht hmm, hab, by simp [toValue_globalType]⟩
  · rintro ⟨rfl, g, hg, hab, rfl⟩
    refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
    cases hg with
    | @mk b b' t m ht hmm =>
      refine (prodDerives_simple rfl).mpr ⟨_, _,
        Value.case "%%" (.tuple [Value.opt (mutOpt m), Encode.toValue t]),
        symDerives_seqG_pair.mpr
        ⟨_, _, VarEnv.empty.bindVal "t" (Encode.toValue t), _, _,
          (symDerives_attrNT hvt).mpr ⟨Encode.toValue t,
            (symDerives_bvaltype h).mpr ⟨rfl, t, ht, hab, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩,
          (symDerives_bmutFactor h rfl rfl (fun _ => rfl)).mpr ⟨m, hmm, rfl, rfl⟩,
          rfl, rfl⟩, ?_, by simp [toValue_globalType]⟩
      exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
        evalExp_mutOptE rfl (fun _ => rfl),
        evalExp_varE_iff.mpr (show _ = some (Encode.toValue t) from rfl), rfl⟩, rfl⟩

/-- `externtype` (`1.2-syntax.types.spectec:137-138`). -/
def externTypeView : Wasm.ExternType → MixopS × Value
  | .func i => ("FUNC", .case "_IDX" (Encode.toValue i))
  | .table t => ("TABLE", Encode.toValue t)
  | .memory m => ("MEM", Encode.toValue m)
  | .global g => ("GLOBAL", Encode.toValue g)
  | .tag j => ("TAG", .case "_IDX" (Encode.toValue j))

/-- The partial inverse of `externTypeView`. -/
def externTypeUnview : MixopS → Value → Option Wasm.ExternType
  | "FUNC", .case "_IDX" w => (Encode.ofValue (α := Wasm.TypeIdx) w).map .func
  | "TABLE", w => (Encode.ofValue (α := Wasm.TableType) w).map .table
  | "MEM", w => (Encode.ofValue (α := Wasm.MemoryType) w).map .memory
  | "GLOBAL", w => (Encode.ofValue (α := Wasm.GlobalType) w).map .global
  | "TAG", .case "_IDX" w => (Encode.ofValue (α := Wasm.TypeIdx) w).map .tag
  | _, _ => none

/-- `externtype` (`1.2-syntax.types.spectec:137-138`). -/
instance instEncodeExternType : Encode Wasm.ExternType :=
  Encode.ofCase externTypeView externTypeUnview
    (by
      intro a
      cases a <;> simp [externTypeView, externTypeUnview, Encode.ofValue_toValue])
    (by
      intro op v a h
      unfold externTypeUnview at h
      split at h <;>
        first
          | (simp only [Option.map_eq_some_iff] at h
             obtain ⟨x, hx, rfl⟩ := h
             simp [externTypeView, Encode.toValue_eq_of_ofValue hx])
          | simp at h)

/-- A production `0xNN y:Z => e`, where `e` mentions only `y`: the five of
`Bexterntype` (5.2:102-107) and the one of `Btagtype` (5.2:89-90). -/
theorem prodDerives_bytePrefixAttr {env : Env} {ρ : VarEnv} {q : List Param} {n : Nat}
    {y z : IL.Id} {e : Exp} {f : Value → Value} {bs : Grammar.Bytes} {l : List Value}
    (hn : n < 256)
    (hz : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
        SymDerives env τ (.varG z []) c ws τ' → τ' = τ)
    (hfind : VarEnv.empty.findVal? y = none)
    (hf : ∀ w : Value, EvalExp env (VarEnv.empty.bindVal y w) e (f w)) :
    ProdDerives env ρ [] []
        (.prodD q (.seqG [.seqG [.numG n], .seqG [.attrG (.varE y) (.varG z [])]]) e [])
        bs l ↔
      ∃ b' w, SymDerives env VarEnv.empty (.varG z []) b' [w] VarEnv.empty ∧
        bs = [UInt8.ofNat n] ++ b' ∧ l = [f w] := by
  rw [prodDerives_simple rfl]
  constructor
  · rintro ⟨l₀, σ, v, hs, hev, rfl⟩
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor hn).mp h₁
    obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hz).mp h₂
    rw [matchExp_varE_of_none_iff hfind] at hm
    subst hm
    obtain rfl := EvalExp.unique hev (hf w)
    exact ⟨b₂, w, hw, rfl, rfl⟩
  · rintro ⟨b', w, hw, rfl, rfl⟩
    exact ⟨_, _, f w, symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
      (symDerives_byteFactor hn).mpr ⟨rfl, rfl, rfl⟩,
      (symDerives_attrNT hz).mpr ⟨w, hw, rfl, matchExp_varE_of_none hfind⟩, rfl, rfl⟩,
      hf w, rfl⟩

/-- `Bexterntype` (5.2:102-107) is `Core.ExternType Forms.all` restricted to
`ExternAbs`. -/
theorem symDerives_bexterntype {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bexterntype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ xt : Wasm.ExternType, Core.ExternType Core.Forms.all bs xt ∧ ExternAbs xt ∧
        l = [Encode.toValue xt] := by
  have hx : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Btypeidx" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.btypeidx).mp hd).1
  have htt : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Btabletype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.btabletype).mp hd).1
  have hmt : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bmemtype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bmemtype).mp hd).1
  have hgt : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bglobaltype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bglobaltype).mp hd).1
  have hjt : ∀ (τ τ' : VarEnv) (c : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Btagtype" []) c ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.btagtype).mp hd).1
  have hfIdx : ∀ w : Value, EvalExp env (VarEnv.empty.bindVal "x" w)
      (.caseE "FUNC" (.caseE "_IDX" (.varE "x"))) (.case "FUNC" (.case "_IDX" w)) :=
    fun w => evalExp_caseE_iff.mpr ⟨_, evalExp_caseE_iff.mpr
      ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩
  rw [symDerives_varG h.bexterntype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bexterntypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨b', w, hw, rfl, rfl⟩ :=
        (prodDerives_bytePrefixAttr (by decide) hx rfl hfIdx).mp hd
      obtain ⟨-, x, hidx, hlw⟩ := (symDerives_btypeidx h hl).mp hw
      have hw' : w = Encode.toValue x := by simpa using hlw
      subst hw'
      exact ⟨.func x, .func hidx, trivial, rfl⟩
    · obtain ⟨b', w, hw, rfl, rfl⟩ := (prodDerives_bytePrefixAttr (by decide) htt rfl
        (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mp hd
      obtain ⟨-, tt, htt', hab, hlw⟩ := (symDerives_btabletype h hl).mp hw
      have hw' : w = Encode.toValue tt := by simpa using hlw
      subst hw'
      exact ⟨.table tt, .table htt', hab, rfl⟩
    · obtain ⟨b', w, hw, rfl, rfl⟩ := (prodDerives_bytePrefixAttr (by decide) hmt rfl
        (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mp hd
      obtain ⟨-, mt, hmt', hlw⟩ := (symDerives_bmemtype h hl).mp hw
      have hw' : w = Encode.toValue mt := by simpa using hlw
      subst hw'
      exact ⟨.memory mt, .memory hmt', trivial, rfl⟩
    · obtain ⟨b', w, hw, rfl, rfl⟩ := (prodDerives_bytePrefixAttr (by decide) hgt rfl
        (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mp hd
      obtain ⟨-, gt, hgt', hab, hlw⟩ := (symDerives_bglobaltype h).mp hw
      have hw' : w = Encode.toValue gt := by simpa using hlw
      subst hw'
      exact ⟨.global gt, .global hgt', hab, rfl⟩
    · obtain ⟨b', w, hw, rfl, rfl⟩ := (prodDerives_bytePrefixAttr (by decide) hjt rfl
        (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mp hd
      obtain ⟨-, jt, hjt', hlw⟩ := (symDerives_btagtype h hl).mp hw
      have hw' : w = tagTypeToValue jt := by simpa using hlw
      subst hw'
      exact ⟨.tag jt, .tag hjt', trivial, rfl⟩
  · rintro ⟨rfl, xt, hxt, hab, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hxt with
    | @func b x hidx =>
        exact ⟨_, List.mem_cons_self ..,
          (prodDerives_bytePrefixAttr (by decide) hx rfl hfIdx).mpr
          ⟨b, Encode.toValue x, (symDerives_btypeidx h hl).mpr ⟨rfl, x, hidx, rfl⟩, rfl, rfl⟩⟩
    | @table b tt htt' =>
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_bytePrefixAttr (by decide) htt rfl
            (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mpr
          ⟨b, Encode.toValue tt,
            (symDerives_btabletype h hl).mpr ⟨rfl, tt, htt', hab, rfl⟩, rfl, rfl⟩⟩
    | @memory b mt hmt' =>
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_bytePrefixAttr (by decide) hmt rfl
            (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mpr
          ⟨b, Encode.toValue mt, (symDerives_bmemtype h hl).mpr ⟨rfl, mt, hmt', rfl⟩,
            rfl, rfl⟩⟩
    | @global b gt hgt' =>
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          (prodDerives_bytePrefixAttr (by decide) hgt rfl
            (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mpr
          ⟨b, Encode.toValue gt, (symDerives_bglobaltype h).mpr ⟨rfl, gt, hgt', hab, rfl⟩,
            rfl, rfl⟩⟩
    | @tag b jt hjt' =>
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
          (prodDerives_bytePrefixAttr (by decide) hjt rfl
            (fun w => evalExp_caseE_iff.mpr ⟨w, evalExp_varE_iff.mpr rfl, rfl⟩)).mpr
          ⟨b, tagTypeToValue jt, (symDerives_btagtype h hl).mpr ⟨rfl, jt, hjt', rfl⟩,
            rfl, rfl⟩⟩

/-! ## The denotations, as `gramRelSup`

`gramRelSup env ρ g` is the byte-string/value relation a symbol denotes
(`Sem/Grammar.lean`).  These are the `SymDerives` results above, read at that
level: one equation per nonterminal, each the agreement statement the brief
asks for.
-/

/-- `Bnumtype` (5.2:7-11) denotes exactly `Silmaril.Wasm.Binary.Core.NumType`. -/
theorem gramRel_bnumtype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bnumtype" []) bs v ↔
      ∃ a : Wasm.NumType, Core.NumType bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bnumtype h).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bnumtype h).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bvectype` (5.2:13-14) denotes exactly `Silmaril.Wasm.Binary.Core.VecType`. -/
theorem gramRel_bvectype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bvectype" []) bs v ↔
      ∃ a : Wasm.VecType, Core.VecType bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bvectype h).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bvectype h).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Babsheaptype` (5.2:16-28) denotes exactly `Core.AbsHeapType`. -/
theorem gramRel_babsheaptype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Babsheaptype" []) bs v ↔
      ∃ a : Wasm.AbsHeapType, Core.AbsHeapType bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_babsheaptype h).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_babsheaptype h).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bpacktype` (5.2:55-57) denotes exactly `Core.PackType`. -/
theorem gramRel_bpacktype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bpacktype" []) bs v ↔
      ∃ a : Wasm.PackType, Core.PackType bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bpacktype h).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bpacktype h).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bmut` (5.2:51-53) denotes exactly `Core.Mut`. -/
theorem gramRel_bmut {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bmut" []) bs v ↔
      ∃ a : Wasm.Mutability, Core.Mut bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bmut h).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bmut h).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Btypeidx` (`5.1-binary.values.spectec:72`) denotes exactly
`Silmaril.Wasm.Binary.Index`. -/
theorem gramRel_btypeidx {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Btypeidx" []) bs v ↔
      ∃ a : Wasm.TypeIdx, Index bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_btypeidx h hl).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_btypeidx h hl).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Btagtype` (5.2:89-90) denotes exactly `Core.TagType`. -/
theorem gramRel_btagtype {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Btagtype" []) bs v ↔
      ∃ a : Wasm.TagType, Core.TagType bs a ∧ v = tagTypeToValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_btagtype h hl).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_btagtype h hl).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Blimits` (5.2:83-87) denotes exactly `Core.Limits Forms.all`. -/
theorem gramRel_blimits {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Blimits" []) bs v ↔
      ∃ a : Wasm.AddrType × Wasm.Limits,
        Core.Limits Core.Forms.all bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_blimits h hl).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_blimits h hl).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bmemtype` (5.2:95-96) denotes exactly `Core.MemType Forms.all`. -/
theorem gramRel_bmemtype {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bmemtype" []) bs v ↔
      ∃ a : Wasm.MemoryType, Core.MemType Core.Forms.all bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bmemtype h hl).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bmemtype h hl).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- **`Bheaptype` (5.2:30-32) denotes only the abstract heap types.**  See
`symDerives_bheaptype` and `bheaptype_misses_typeIdx`. -/
theorem gramRel_bheaptype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bheaptype" []) bs v ↔
      ∃ a : Wasm.AbsHeapType, Core.AbsHeapType bs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bheaptype h).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bheaptype h).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Breftype` (5.2:34-37) denotes `Core.RefType Forms.all` restricted to
abstract heap types. -/
theorem gramRel_breftype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Breftype" []) bs v ↔
      ∃ a : Wasm.RefType, Core.RefType Core.Forms.all bs a ∧ RefAbs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hab, hres⟩ := (symDerives_breftype' h).mp hd
    exact ⟨a, ha, hab, by simpa using hres⟩
  · rintro ⟨a, ha, hab, rfl⟩
    exact ⟨ρ, (symDerives_breftype' h).mpr ⟨rfl, a, ha, hab, rfl⟩⟩

/-- `Bvaltype` (5.2:39-42) denotes `Core.ValType Forms.all` restricted to
`ValAbs`. -/
theorem gramRel_bvaltype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bvaltype" []) bs v ↔
      ∃ a : Wasm.ValType, Core.ValType Core.Forms.all bs a ∧ ValAbs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hab, hres⟩ := (symDerives_bvaltype h).mp hd
    exact ⟨a, ha, hab, by simpa using hres⟩
  · rintro ⟨a, ha, hab, rfl⟩
    exact ⟨ρ, (symDerives_bvaltype h).mpr ⟨rfl, a, ha, hab, rfl⟩⟩

/-- `Bstoragetype` (5.2:59-61) denotes `Core.StorageType Forms.all` restricted
to `StorageAbs`. -/
theorem gramRel_bstoragetype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bstoragetype" []) bs v ↔
      ∃ a : Wasm.StorageType,
        Core.StorageType Core.Forms.all bs a ∧ StorageAbs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hab, hres⟩ := (symDerives_bstoragetype h).mp hd
    exact ⟨a, ha, hab, by simpa using hres⟩
  · rintro ⟨a, ha, hab, rfl⟩
    exact ⟨ρ, (symDerives_bstoragetype h).mpr ⟨rfl, a, ha, hab, rfl⟩⟩

/-- `Bfieldtype` (5.2:63-64) denotes `Core.FieldType Forms.all` restricted to
`FieldAbs`. -/
theorem gramRel_bfieldtype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bfieldtype" []) bs v ↔
      ∃ a : Wasm.FieldType,
        Core.FieldType Core.Forms.all bs a ∧ FieldAbs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hab, hres⟩ := (symDerives_bfieldtype h).mp hd
    exact ⟨a, ha, hab, by simpa using hres⟩
  · rintro ⟨a, ha, hab, rfl⟩
    exact ⟨ρ, (symDerives_bfieldtype h).mpr ⟨rfl, a, ha, hab, rfl⟩⟩

/-- `Bglobaltype` (5.2:92-93) denotes `Core.GlobalType Forms.all` restricted to
`GlobalAbs`. -/
theorem gramRel_bglobaltype {env : Env} (h : HasBinTypes env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bglobaltype" []) bs v ↔
      ∃ a : Wasm.GlobalType,
        Core.GlobalType Core.Forms.all bs a ∧ GlobalAbs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hab, hres⟩ := (symDerives_bglobaltype h).mp hd
    exact ⟨a, ha, hab, by simpa using hres⟩
  · rintro ⟨a, ha, hab, rfl⟩
    exact ⟨ρ, (symDerives_bglobaltype h).mpr ⟨rfl, a, ha, hab, rfl⟩⟩

/-- `Btabletype` (5.2:98-99) denotes `Core.TableType Forms.all` restricted to
`TableAbs`. -/
theorem gramRel_btabletype {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Btabletype" []) bs v ↔
      ∃ a : Wasm.TableType,
        Core.TableType Core.Forms.all bs a ∧ TableAbs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hab, hres⟩ := (symDerives_btabletype h hl).mp hd
    exact ⟨a, ha, hab, by simpa using hres⟩
  · rintro ⟨a, ha, hab, rfl⟩
    exact ⟨ρ, (symDerives_btabletype h hl).mpr ⟨rfl, a, ha, hab, rfl⟩⟩

/-- `Bexterntype` (5.2:102-107) denotes `Core.ExternType Forms.all` restricted
to `ExternAbs`. -/
theorem gramRel_bexterntype {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bexterntype" []) bs v ↔
      ∃ a : Wasm.ExternType,
        Core.ExternType Core.Forms.all bs a ∧ ExternAbs a ∧ v = Encode.toValue a := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hab, hres⟩ := (symDerives_bexterntype h hl).mp hd
    exact ⟨a, ha, hab, by simpa using hres⟩
  · rintro ⟨a, ha, hab, rfl⟩
    exact ⟨ρ, (symDerives_bexterntype h hl).mpr ⟨rfl, a, ha, hab, rfl⟩⟩

/-- `Bu32` (`5.1-binary.values.spectec:26`) denotes
`Silmaril.Wasm.Binary.U32`. -/
theorem gramRel_bu32 {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bu32" []) bs v ↔ ∃ m, U32 bs m ∧ v = numCase m := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, m, hm, hres⟩ := (symDerives_bu32 h hl).mp hd
    exact ⟨m, hm, by simpa using hres⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨ρ, (symDerives_bu32 h hl).mpr ⟨rfl, m, hm, rfl⟩⟩

/-- `Bu64` (`5.1-binary.values.spectec:27`) denotes
`Silmaril.Wasm.Binary.U64`. -/
theorem gramRel_bu64 {env : Env} (h : HasBinTypes env) (hl : HasLeb env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bu64" []) bs v ↔ ∃ m, U64 bs m ∧ v = numCase m := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, m, hm, hres⟩ := (symDerives_bu64 h hl).mp hd
    exact ⟨m, hm, by simpa using hres⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨ρ, (symDerives_bu64 h hl).mpr ⟨rfl, m, hm, rfl⟩⟩

end Silmaril.SpecTec.Equiv
