module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.V1Binary
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryInstr
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Agreement.Sections
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
-- `spectec_import` and `spectec_erratum` add their constants with
-- `Lean.addDecl`, which bypasses the `@[expose]` of the section they sit in,
-- so the *values* of `Specs.wasm20`, `Specs.wasm30`, `Wasm20.wasm20corrected`
-- and `Wasm10.wasm10corrected` are not visible to an importing module without
-- these lines; they are what makes the census below `rfl`s the kernel can do.
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10

/-!
# The corrected wasm-2.0 specification: a version census, and Silmaril's binary layer

`Silmaril/SpecTec/Equiv/V1Binary.lean` does this for wasm-1.0 and
`Silmaril/SpecTec/Equiv/BinaryValues.lean`, `Equiv/BinaryTypes.lean` for
wasm-3.0.  This file is the wasm-2.0 counterpart.  It relates
`Silmaril.SpecTec.IL.Wasm20.wasm20corrected` — the pinned wasm-2.0 stream with
the four errata of `#660` that are expressible as AST patches
applied (`Silmaril/SpecTec/Errata/Wasm20.lean`) — to wasm-3.0, to wasm-1.0,
and to `Silmaril/Wasm/Binary/`.

Everything is relative to the pin `608711107b7f1edb13efd57b7d79b49477462d36`.
Bare line citations `A-binary.spectec:n` are line `n` of
`specification/wasm-2.0/A-binary.spectec`; `1-syntax.spectec` is its sibling;
`wasm-3.0/…` and `wasm-1.0/…` name the other two directories, and
`interpreter/…` the reference interpreter.

## There is no wasm-2.0 Lean semantics in this checkout

`#660` describes a wasm-2.0 layer at `Silmaril/Wasm/V2/**` on
branch `wasm2`.  **That branch has not merged here**: `Silmaril/Wasm/`
contains `V1/`, `Lime1/`, `Scalar/`, `Validation/`, `Execution/` and the
shared `Binary/`, and no `V2/` directory at all.  So the
statements below cannot be "the corrected wasm-2.0 specification agrees with
Silmaril's wasm-2.0 semantics"; what they can be, and are, is

* a **version census** — which of wasm-2.0's definitions SpecTec elaborates to
  byte-identical IL with wasm-3.0's, and which with wasm-1.0's — so that a
  future wasm-2.0 layer knows exactly which existing theorems transport; and
* agreement of wasm-2.0's **values and types sections** with
  `Silmaril/Wasm/Binary/`, the version-independent binary layer, which needs
  no wasm-2.0 abstract syntax to state.

## The census

`sharedGramsV3_agree`, `changedGramsV3_differ` and `v2OnlyGrams_absent`
partition wasm-2.0's **71 grammars** into 49 that are byte-identical to
wasm-3.0's, 21 that differ, and one (`Bfunctype`) that wasm-3.0 does not
declare; `sharedGramsV1_agree` finds 50 byte-identical to the corrected
wasm-1.0's.  Each is one `IL.defEq`, i.e. one comparison of the two
definitions' `--ast` renderings, reduced by the kernel.

The picture that comes out is that **wasm-2.0 is not "between" 1.0 and 3.0 in
one piece**.  Its LEB128, float, list, section and index machinery is
wasm-3.0's verbatim; its `Bmut`, `Blimits`, `Bglobaltype`, `Bexternidx`,
`Bexterntype`, `Bmemarg`, `Bi32` and `Bi64` are wasm-1.0's verbatim; and
`Bnumtype`, `Breftype`, `Btabletype`, `Bmemtype`, `Bblocktype` and `Binstr`
match neither neighbour.  `Bvaltype`, `Bvectype` and `Bresulttype` are
wasm-3.0's *text*, which is a trap: `Bvaltype` reads a `Breftype`, and
wasm-2.0's `Breftype` is two nullary injections where wasm-3.0's is a heap
type.  Byte-identity of a definition transports a theorem only when the whole
dependency closure is byte-identical, which is why every result below is
stated against an explicit `HasLeb`/`HasSignedLeb`/`HasV2Types` hypothesis
rather than against "wasm-2.0 = wasm-3.0 here".

Only the **grammar** namespace is checked by the kernel.  Computed outside
Lean, from the same `--ast` streams, the other namespaces come out as: of
wasm-2.0's 144 `syntax` declarations 98 are byte-identical to wasm-3.0's, 36
differ and 10 are wasm-2.0's alone; of its 213 `def`s, 126/67/20; of its 40
`relation`s, only two — `Expr_const` and `Expr_ok_const` — survive unchanged,
36 differ and 2 (`Functype_ok`, `Functype_sub`) are wasm-2.0's alone.
wasm-2.0 declares no text-format grammar at all: of the 162 grammars wasm-3.0
has and wasm-2.0 does not, 142 are the `T…` text grammars and the remaining
20 are the heap-type, recursive-type, tag and `Bmagic`/`Bversion` machinery
wasm-2.0 lacks.  These counts are **not** kernel
checked, because `IL.namedDefs` keys on the identifier alone and wasm-2.0
reuses 32 identifiers across two namespaces (`func` is a `syntax` and a
`def`, and so on), which `defsAgree` reports as "not declared exactly once".

## What this says about `#803`

`#803` is SpecTec's elaborator narrowing `int` to `nat`, so that the
elaborated `BsN` derives no multi-byte negative LEB128.  `sharedGramsV3_agree`
puts `BsN`, `BiN` and `Bbyte` in the byte-identical set, and their dependency
closure is `{Bbyte, BuN, BsN}`, which is byte-identical too; `hasLeb_v2` and
`hasSignedLeb_v2` are the two `rfl`s that make
`Equiv/BinaryValues.lean`'s results wasm-2.0's results.  So **`#803` applies
to wasm-2.0 unchanged**, and in the sharp form wasm-1.0 has rather than the
wasm-3.0 one: `A-binary.spectec:42` already reads `grammar Bi32 : i32 =
BiN(32)`, so `#654` has nothing to correct here (`hasCorrectedBi_v2`) and
`BsN` is the sole cause of `bi32_v2_disagrees_with_in`.  wasm-2.0 has no text
format, so `#803`'s `Tfloat`/`Thexfloat` half does not arise.

## Erratum `#672` and the module header

`bmodule_header_v2` is the verdict asked for: after `#672` every byte string
the corrected `Bmodule` derives begins with the eight bytes
`Wasm.Binary.magic ++ Wasm.Binary.version`, which is exactly the prefix
`Silmaril/Wasm/Binary/Core/Modules.lean`'s `Module` and
`Silmaril/Wasm/V1/Binary/Modules.lean`'s `Module` require.  Before the patch
(`bmodule_header_pinned_v2`) the header is the four magic bytes followed by
whatever `Bu32` derives for 1 — and `u32_one_ambiguous` is the sharp form of
the defect: that is `0x01`, but also the non-minimal `0x81 0x00`, so the
pinned grammar accepts headers our Lean rejects *and* is ambiguous about the
one it does accept.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.Wasm20

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Binary

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-- The corrected wasm-2.0 specification. -/
noncomputable abbrev wasm20corrected : Script := IL.Wasm20.wasm20corrected

/-- The environment of the corrected wasm-2.0 specification. -/
noncomputable abbrev envV2 : Env := envOfScript wasm20corrected

/-- The environment of the pinned wasm-3.0 specification. -/
noncomputable abbrev envV3 : Env := envOfScript Specs.wasm30

/-- The environment of the corrected wasm-1.0 specification. -/
noncomputable abbrev envV1c : Env := envOfScript IL.Wasm10.wasm10corrected

/-! ## The census, as a kernel-checked comparison of top-level definitions

`IL.defEq` (`Silmaril/SpecTec/Errata.lean`) decides equality of two
`IL.Def`s through `IL.defS`, their `--ast` rendering, and `IL.defEq_iff` turns
that `Bool` back into an equation.  `IL.namedDefs x s` is the list of
definitions of `s` that declare `x`, reaching inside `recD` groups.  Putting
the two together gives a decidable "`x` is declared exactly once in each
script, and the two declarations are the same bytes". -/

/-- `x` is declared exactly once in each of `s` and `t`, and by the same
definition — hence by the same `--ast` text. -/
def defsAgree (s t : Script) (x : IL.Id) : Bool :=
  match namedDefs x s, namedDefs x t with
  | [d₁], [d₂] => defEq d₁ d₂
  | _, _ => false

/-- `x` is declared exactly once in each of `s` and `t`, and the two
declarations differ. -/
def defsDiffer (s t : Script) (x : IL.Id) : Bool :=
  match namedDefs x s, namedDefs x t with
  | [d₁], [d₂] => !defEq d₁ d₂
  | _, _ => false

/-- `x` is declared exactly once in `s` and not at all in `t`. -/
def defsAbsent (s t : Script) (x : IL.Id) : Bool :=
  match namedDefs x s, namedDefs x t with
  | [_], [] => true
  | _, _ => false

/-- What `defsAgree` says: one declaration on each side, and it is literally
the same `IL.Def`. -/
theorem eq_of_defsAgree {s t : Script} {x : IL.Id} (h : defsAgree s t x = true) :
    ∃ d, namedDefs x s = [d] ∧ namedDefs x t = [d] := by
  unfold defsAgree at h
  split at h
  · rename_i d₁ d₂ h₁ h₂
    exact ⟨d₁, h₁, (defEq_iff.mp h) ▸ h₂⟩
  · exact absurd h (by simp)

/-- What `defsDiffer` says: one declaration on each side, and they are not
equal. -/
theorem ne_of_defsDiffer {s t : Script} {x : IL.Id} (h : defsDiffer s t x = true) :
    ∃ d₁ d₂, namedDefs x s = [d₁] ∧ namedDefs x t = [d₂] ∧ d₁ ≠ d₂ := by
  unfold defsDiffer at h
  split at h
  · rename_i d₁ d₂ h₁ h₂
    refine ⟨d₁, d₂, h₁, h₂, fun hd => ?_⟩
    subst hd
    simp [defEq] at h
  · exact absurd h (by simp)

/-- What `defsAbsent` says: `x` is declared in `s` and not in `t`. -/
theorem absent_of_defsAbsent {s t : Script} {x : IL.Id} (h : defsAbsent s t x = true) :
    namedDefs x t = [] := by
  unfold defsAbsent at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-! ### The grammars wasm-2.0 and wasm-3.0 share -/

/-- The 49 `grammar` identifiers that the corrected wasm-2.0 script and the
pinned wasm-3.0 script declare with **byte-identical** definitions. -/
def sharedGramsV3 : List IL.Id :=
  [
    "Bbyte", "Bcode", "Bcodesec", "Bcustom", "Bcustomsec",
    "Bdata", "Bdatacnt", "Bdatacntsec", "Bdataidx", "Bdatasec",
    "Belemidx", "Belemsec", "Bexport", "Bexportsec", "Bexpr",
    "Bf32", "Bf64", "BfN", "Bfuncidx", "Bfuncsec",
    "Bglobal", "Bglobalidx", "Bglobalsec", "BiN", "Bimport",
    "Bimportsec", "Blaneidx", "Blist", "Blocalidx", "Blocals",
    "Bmem", "Bmemidx", "Bmemsec", "Bname", "Bresulttype",
    "Bs33", "BsN", "Bsection_", "Bstart", "Bstartsec",
    "Btableidx", "Btablesec", "Btypeidx", "Btypesec", "Bu32",
    "Bu64", "BuN", "Bvaltype", "Bvectype" ]

/-- **The census, upward.**  Every name in `sharedGramsV3` is declared exactly
once in each script and by the same `IL.Def`.  One `rfl`, 49 string
comparisons of `--ast` renderings, checked by the kernel. -/
theorem sharedGramsV3_agree :
    sharedGramsV3.all (defsAgree wasm20corrected Specs.wasm30) = true := by rfl

/-- The 21 `grammar` identifiers both scripts declare with **different**
definitions. -/
def changedGramsV3 : List IL.Id :=
  [
    "Bblocktype", "Belem", "Belemkind", "Bexternidx", "Bexterntype",
    "Bfunc", "Bglobaltype", "Bi32", "Bi64", "Binstr",
    "Blabelidx", "Blimits", "Bmemarg", "Bmemtype", "Bmodule",
    "Bmut", "Bnumtype", "Breftype", "Btable", "Btabletype",
    "Btype" ]

/-- **The census, the other way.**  Every name in `changedGramsV3` is declared
in both scripts, and the two declarations are different `--ast` text. -/
theorem changedGramsV3_differ :
    changedGramsV3.all (defsDiffer wasm20corrected Specs.wasm30) = true := by rfl

/-- The one `grammar` the corrected wasm-2.0 script declares and the pinned
wasm-3.0 script does not. -/
def v2OnlyGrams : List IL.Id :=
  [
    "Bfunctype" ]

/-- `Bfunctype` is wasm-2.0's and wasm-1.0's; wasm-3.0 folds function types
into `Bcomptype` (`wasm-3.0/5.2-binary.types.spectec:66-69`). -/
theorem v2OnlyGrams_absent :
    v2OnlyGrams.all (defsAbsent wasm20corrected Specs.wasm30) = true := by rfl

/-! ### The grammars corrected wasm-2.0 and corrected wasm-1.0 share -/

/-- The 50 `grammar` identifiers that the corrected wasm-2.0 script and the
corrected wasm-1.0 script declare with **byte-identical** definitions. -/
def sharedGramsV1 : List IL.Id :=
  [
    "Bbyte", "Bcode", "Bcodesec", "Bcustom", "Bcustomsec",
    "Bdatasec", "Belemsec", "Bexport", "Bexportsec", "Bexpr",
    "Bexternidx", "Bexterntype", "Bf32", "Bf64", "BfN",
    "Bfuncidx", "Bfuncsec", "Bglobal", "Bglobalidx", "Bglobalsec",
    "Bglobaltype", "Bi32", "Bi64", "BiN", "Bimport",
    "Bimportsec", "Blabelidx", "Blimits", "Blist", "Blocalidx",
    "Blocals", "Bmem", "Bmemarg", "Bmemidx", "Bmemsec",
    "Bmut", "Bname", "BsN", "Bsection_", "Bstart",
    "Bstartsec", "Btable", "Btableidx", "Btablesec", "Btype",
    "Btypeidx", "Btypesec", "Bu32", "Bu64", "BuN" ]

/-- **wasm-2.0 sits between the two.**  Every name in `sharedGramsV1` is
declared exactly once in each of the corrected wasm-2.0 and corrected
wasm-1.0 scripts, by the same `IL.Def`. -/
theorem sharedGramsV1_agree :
    sharedGramsV1.all (defsAgree wasm20corrected IL.Wasm10.wasm10corrected) = true := by rfl

/-! ## The values section at the corrected wasm-2.0 environment

`A-binary.spectec:18-46`.  The census above already says that `Bbyte`, `BuN`,
`BsN`, `BiN`, `BfN`, `Bu32`, `Bu64`, `Bs33`, `Bf32`, `Bf64` and `Blist` are
byte-identical to wasm-3.0's; the `rfl`s below read them off `envV2` in the
shape `Sem/Grammar.lean` and `Equiv/BinaryValues.lean` state their theorems
in, so every one of those theorems applies to wasm-2.0 verbatim. -/

private theorem findGram_bbyte_v2 :
    envV2.findGram? "Bbyte" = some ([], .varT "byte" [], bbyteProds) := rfl

private theorem findGram_bun_v2 :
    envV2.findGram? "BuN" = some (bunParams, bunTyp, bunProds) := rfl

private theorem findGram_bsn_v2 :
    envV2.findGram? "BsN" = some (bsnParams, bsnTyp, bsnProds) := rfl

private theorem findGram_bin_v2 :
    envV2.findGram? "BiN"
      = some (bsnParams, .varT "iN" [.expA (.varE "N")], binProds) := rfl

private theorem findGram_bu32_v2 :
    envV2.findGram? "Bu32"
      = some ([], .varT "u32" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 32))]) "BuN" (.numE (.natN 32))) := rfl

private theorem findGram_bu64_v2 :
    envV2.findGram? "Bu64"
      = some ([], .varT "u64" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 64))]) "BuN" (.numE (.natN 64))) := rfl

private theorem findGram_bs33_v2 :
    envV2.findGram? "Bs33"
      = some ([], .varT "s33" [],
          wrapProds (.varT "sN" [.expA (.numE (.natN 33))]) "BsN" (.numE (.natN 33))) := rfl

private theorem findGram_bi32_v2 :
    envV2.findGram? "Bi32"
      = some ([], .varT "i32" [],
          wrapProds (.varT "iN" [.expA (.numE (.natN 32))]) "BiN" (.numE (.natN 32))) := rfl

private theorem findGram_bi64_v2 :
    envV2.findGram? "Bi64"
      = some ([], .varT "i64" [],
          wrapProds (.varT "iN" [.expA (.numE (.natN 64))]) "BiN" (.numE (.natN 64))) := rfl

/-- **`Bbyte` and `BuN` are wasm-3.0's**, so `Sem/Grammar.lean`'s LEB128
theorems are theorems about wasm-2.0. -/
theorem hasLeb_v2 : HasLeb envV2 := ⟨findGram_bbyte_v2, findGram_bun_v2⟩

/-- **`BsN` and `BiN` are wasm-3.0's**, so `Equiv/BinaryValues.lean`'s signed
LEB128 theorems — and its defect — are theorems about wasm-2.0. -/
theorem hasSignedLeb_v2 : HasSignedLeb envV2 := ⟨findGram_bsn_v2, findGram_bin_v2⟩

/-- **`Bu32` and `Bs33` are wasm-3.0's.** -/
theorem hasWrappers_v2 : HasWrappers envV2 := ⟨findGram_bu32_v2, findGram_bs33_v2⟩

/-- **wasm-2.0 does not have `#654`.**  `A-binary.spectec:42-43` already reads
`grammar Bi32 : i32 = BiN(32)`, the signed grammar; wasm-3.0's
`5.1-binary.values.spectec:31` writes `BuN(32)` and needs the patch of
`Errata/Binary51.lean`.  So the corrected wasm-2.0 script satisfies
`Equiv.HasCorrectedBi` with no patch at all — exactly as wasm-1.0 does. -/
theorem hasCorrectedBi_v2 : HasCorrectedBi envV2 := ⟨findGram_bi32_v2, findGram_bi64_v2⟩

/-- **`Bbyte` is `Silmaril.Wasm.Binary.Byte`** (`A-binary.spectec:18`). -/
theorem bbyte_iff_byte_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bbyte" []) bs v ↔
      ∃ b : UInt8, Byte bs b ∧ v = Encode.toValue b :=
  bbyte_iff_byte hasLeb_v2 ρ bs v

/-- **`BuN(N)` is `Silmaril.Wasm.Binary.UN N`** (`A-binary.spectec:20-22`). -/
theorem bun_iff_un_v2 (W : Nat) (bs : Grammar.Bytes) (v : Value) (ρ : VarEnv) :
    gramRelSup envV2 ρ (.varG "BuN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ m, UN W bs m ∧ v = uNV m :=
  bun_iff_un hasLeb_v2 W bs v ρ

/-- **`Bu32` is `Silmaril.Wasm.Binary.U32`** (`A-binary.spectec:37`). -/
theorem bu32_iff_u32_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bu32" []) bs v ↔ ∃ m, U32 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff findGram_bu32_v2 hasLeb_v2.bun ρ bs v]
  exact bun_iff_un_v2 32 bs v VarEnv.empty

/-- **`Bu64` is `Silmaril.Wasm.Binary.U64`** (`A-binary.spectec:38`). -/
theorem bu64_iff_u64_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bu64" []) bs v ↔ ∃ m, U64 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff findGram_bu64_v2 hasLeb_v2.bun ρ bs v]
  exact bun_iff_un_v2 64 bs v VarEnv.empty

/-! ### `BsN`: the verdict for wasm-2.0 (`#803`)

`A-binary.spectec:24-27` is the same three productions as
`wasm-3.0/5.1-binary.values.spectec:13-16`, and `sharedGramsV3_agree` says
SpecTec elaborates them to the same IL, character for character.  So the
narrowing `#803` reports — the third production infers its arithmetic at
`nat`, narrows the recursive `sN` value with `cvt int nat` before multiplying,
and `Xl.Num.cvt` (`spectec/src/xl/num.ml:86`) is undefined on a negative
integer — is present in wasm-2.0 **unchanged**, and
`Equiv/BinaryValues.lean`'s `bsn_iff_sn` is already the exact
characterisation of wasm-2.0's `BsN`. -/

/-- **The corrected wasm-2.0 `BsN(N)` is `Silmaril.Wasm.Binary.SN N`
restricted to single-byte encodings and non-negative values, exactly.** -/
theorem bsn_iff_sn_v2 (W : Nat) (hW : 0 < W) (bs : Grammar.Bytes) (v : Value) (ρ : VarEnv) :
    gramRelSup envV2 ρ (.varG "BsN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ i, SN W bs i ∧ (0 ≤ i ∨ bs.length = 1) ∧ v = sNV i :=
  bsn_iff_sn hasLeb_v2 hasSignedLeb_v2 W hW bs v ρ

/-- **`Bs33` is `Silmaril.Wasm.Binary.S33`, under the same restriction**
(`A-binary.spectec:40`).  This is the grammar wasm-2.0's multi-value block
type goes through: `A-binary.spectec:154` reads
`| i:Bs33 => _IDX x  -- if i >= 0 /\ i = x`. -/
theorem bs33_iff_s33_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bs33" []) bs v ↔
      ∃ j, S33 bs j ∧ (0 ≤ j ∨ bs.length = 1) ∧ v = sNV j :=
  bs33_iff_s33_gen hasLeb_v2 hasSignedLeb_v2 hasWrappers_v2 ρ bs v

/-- **The corrected wasm-2.0 `BsN(32)` derives nothing from `FF 7E`**, the
two-byte signed LEB128 encoding of `-129`. -/
theorem not_bsn_FF7E_v2 (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envV2 ρ (.varG "BsN" [.expA (.numE (.natN 32))]) [0xFF, 0x7E] v :=
  not_bsn_FF7E hasLeb_v2 hasSignedLeb_v2 ρ v

/-- **The corrected wasm-2.0 `Bi32` derives nothing from `FF 7E`** either:
`Bi32 = BiN(32)` and `BiN`'s byte language is `BsN`'s. -/
theorem not_bi32_FF7E_v2 (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envV2 ρ (.varG "Bi32" []) [0xFF, 0x7E] v := by
  intro hd
  rw [wrap_rel_iff hasCorrectedBi_v2.bi32 hasSignedLeb_v2.bin ρ _ v] at hd
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
  exact not_bin_FF7E hasLeb_v2 hasSignedLeb_v2 VarEnv.empty ρ' v hd

/-- The same for `Bi64`: `FF 7E` is `i64.const -129`. -/
theorem not_bi64_FF7E_v2 (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envV2 ρ (.varG "Bi64" []) [0xFF, 0x7E] v := by
  intro hd
  rw [wrap_rel_iff hasCorrectedBi_v2.bi64 hasSignedLeb_v2.bin ρ _ v] at hd
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
  obtain ⟨w, ρa, hinner⟩ := bsn_of_bin hasSignedLeb_v2 hd
  obtain ⟨i, hi, hcond, -⟩ := sn_of_bsn hasLeb_v2 hasSignedLeb_v2 64 (by omega)
    (evalExp_varE_iff.mpr (findVal_bunScope_N 64)) hinner
  have hieq : i = -129 := SN.functional 64 hi (SN.mono (by omega) sn32_FF7E)
  rcases hcond with hc | hc
  · rw [hieq] at hc; exact absurd hc (by decide)
  · exact absurd hc (by decide)

/-- **The `BsN` verdict for wasm-2.0.**  wasm-2.0 has no `#654` to apply and
its `Bi32` is already the signed grammar, yet the corrected wasm-2.0
specification still disagrees with `Silmaril.Wasm.Binary.IN 32`: `FF 7E`, the
encoding of `i32.const -129`, has no derivation at all.  As in wasm-1.0, and
unlike wasm-3.0, there is no patch in flight and `#803`'s `BsN` is the sole
cause. -/
theorem bi32_v2_disagrees_with_in (ρ : VarEnv) :
    ¬ ∀ (bs : Grammar.Bytes) (v : Value),
        gramRelSup envV2 ρ (.varG "Bi32" []) bs v ↔
          ∃ bv : BitVec 32, IN 32 bs bv ∧ v = iNV bv := by
  intro h
  exact not_bi32_FF7E_v2 ρ (iNV (BitVec.ofInt 32 (-129)))
    ((h [0xFF, 0x7E] _).mpr ⟨BitVec.ofInt 32 (-129), in32_FF7E, rfl⟩)

/-! ## The types section: the productions wasm-2.0 has

`A-binary.spectec:66-142`.  wasm-2.0 is the version that *adds* reference and
vector types to wasm-1.0 and *predates* wasm-3.0's heap types, so its type
grammars are the ones that match neither neighbour: `sharedGramsV3_agree`
places `Bvaltype`, `Bvectype` and `Bresulttype` on the wasm-3.0 side and
`sharedGramsV1_agree` places `Bmut`, `Blimits`, `Bglobaltype`, `Bexternidx`,
`Bexterntype` and `Bmemarg` on the wasm-1.0 side, while `Bnumtype`, `Breftype`,
`Btabletype` and `Bmemtype` match neither. -/

/-- The four productions of `grammar Bnumtype : numtype`
(`A-binary.spectec:89-93`).  These are the four productions wasm-1.0 gives
`Bvaltype` (`Equiv.V1Binary.bvaltypeV1Prods`), in the same order; wasm-3.0
lists the same four bytes in the opposite order, which is why `Bnumtype` is in
`changedGramsV3`. -/
def bnumtypeV2Prods : List IL.Prod :=
  [ .prodD [] (.numG 0x7F) (.caseE "I32" (.tupE [])) [],
    .prodD [] (.numG 0x7E) (.caseE "I64" (.tupE [])) [],
    .prodD [] (.numG 0x7D) (.caseE "F32" (.tupE [])) [],
    .prodD [] (.numG 0x7C) (.caseE "F64" (.tupE [])) [] ]

/-- wasm-2.0's `Bnumtype` is, production for production, wasm-1.0's
`Bvaltype`. -/
theorem bnumtypeV2Prods_eq : bnumtypeV2Prods = V1Binary.bvaltypeV1Prods := rfl

/-- The two productions of `grammar Breftype : reftype`
(`A-binary.spectec:98-100`).  wasm-2.0 has exactly two reference types and
spells them as nullary injections; wasm-3.0's `Breftype`
(`wasm-3.0/5.2-binary.types.spectec:34-37`) reads a whole `Bheaptype` under
`0x63`/`0x64` and twelve abstract heap types bare. -/
def breftypeV2Prods : List IL.Prod :=
  [ .prodD [] (.numG 0x70) (.caseE "FUNCREF" (.tupE [])) [],
    .prodD [] (.numG 0x6F) (.caseE "EXTERNREF" (.tupE [])) [] ]

/-! ## Provenance for the types section -/

private theorem findGram_bu32_prods_v2 :
    envV2.findGram? "Bu32" = some ([], .varT "u32" [], bu32Prods) := findGram_bu32_v2

private theorem findGram_bu64_prods_v2 :
    envV2.findGram? "Bu64" = some ([], .varT "u64" [], bu64Prods) := findGram_bu64_v2

private theorem findGram_btypeidx_v2 :
    envV2.findGram? "Btypeidx" = some ([], .varT "typeidx" [], btypeidxProds) := rfl

private theorem findGram_bfuncidx_v2 :
    envV2.findGram? "Bfuncidx" = some ([], .varT "funcidx" [], btypeidxProds) := rfl

private theorem findGram_bglobalidx_v2 :
    envV2.findGram? "Bglobalidx" = some ([], .varT "globalidx" [], btypeidxProds) := rfl

private theorem findGram_btableidx_v2 :
    envV2.findGram? "Btableidx" = some ([], .varT "tableidx" [], btypeidxProds) := rfl

private theorem findGram_bmemidx_v2 :
    envV2.findGram? "Bmemidx" = some ([], .varT "memidx" [], btypeidxProds) := rfl

private theorem findGram_belemidx_v2 :
    envV2.findGram? "Belemidx" = some ([], .varT "elemidx" [], btypeidxProds) := rfl

private theorem findGram_bdataidx_v2 :
    envV2.findGram? "Bdataidx" = some ([], .varT "dataidx" [], btypeidxProds) := rfl

private theorem findGram_blocalidx_v2 :
    envV2.findGram? "Blocalidx" = some ([], .varT "localidx" [], btypeidxProds) := rfl

private theorem findGram_blabelidx_v2 :
    envV2.findGram? "Blabelidx" = some ([], .varT "labelidx" [], btypeidxProds) := rfl

private theorem findGram_bnumtype_v2 :
    envV2.findGram? "Bnumtype" = some ([], .varT "numtype" [], bnumtypeV2Prods) := rfl

private theorem findGram_bvectype_v2 :
    envV2.findGram? "Bvectype" = some ([], .varT "vectype" [], bvectypeProds) := rfl

private theorem findGram_breftype_v2 :
    envV2.findGram? "Breftype" = some ([], .varT "reftype" [], breftypeV2Prods) := rfl

private theorem findGram_bmut_v2 :
    envV2.findGram? "Bmut" = some ([], .varT "mut" [], V1Binary.bmutV1Prods) := rfl

private theorem findGram_blimits_v2 :
    envV2.findGram? "Blimits" = some ([], .varT "limits" [], V1Binary.blimitsV1Prods) := rfl

private theorem findGram_bexternidx_v2 :
    envV2.findGram? "Bexternidx"
      = some ([], .varT "externidx" [], V1Binary.bexternidxV1Prods) := rfl

/-! ## The hypotheses on an environment

As in `Equiv/BinaryTypes.lean` and `Equiv/V1Binary.lean`, every result below is
stated for an arbitrary environment that defines the nonterminals it uses
exactly as the corrected wasm-2.0 stream does. -/

/-- An environment whose wasm-2.0 index and type nonterminals are the
corrected wasm-2.0 stream's. -/
structure HasV2Types (env : Env) : Prop where
  /-- `Bu32 = BuN(32)` (`A-binary.spectec:37`). -/
  bu32 : env.findGram? "Bu32" = some ([], .varT "u32" [], bu32Prods)
  /-- `Bu64 = BuN(64)` (`A-binary.spectec:38`). -/
  bu64 : env.findGram? "Bu64" = some ([], .varT "u64" [], bu64Prods)
  /-- `Btypeidx` (`A-binary.spectec:66`). -/
  btypeidx : env.findGram? "Btypeidx" = some ([], .varT "typeidx" [], btypeidxProds)
  /-- `Bfuncidx` (`A-binary.spectec:67`). -/
  bfuncidx : env.findGram? "Bfuncidx" = some ([], .varT "funcidx" [], btypeidxProds)
  /-- `Bglobalidx` (`A-binary.spectec:68`). -/
  bglobalidx : env.findGram? "Bglobalidx" = some ([], .varT "globalidx" [], btypeidxProds)
  /-- `Btableidx` (`A-binary.spectec:69`). -/
  btableidx : env.findGram? "Btableidx" = some ([], .varT "tableidx" [], btypeidxProds)
  /-- `Bmemidx` (`A-binary.spectec:70`). -/
  bmemidx : env.findGram? "Bmemidx" = some ([], .varT "memidx" [], btypeidxProds)
  /-- `Belemidx` (`A-binary.spectec:71`), which wasm-1.0 does not have. -/
  belemidx : env.findGram? "Belemidx" = some ([], .varT "elemidx" [], btypeidxProds)
  /-- `Bdataidx` (`A-binary.spectec:72`), which wasm-1.0 does not have. -/
  bdataidx : env.findGram? "Bdataidx" = some ([], .varT "dataidx" [], btypeidxProds)
  /-- `Blocalidx` (`A-binary.spectec:73`). -/
  blocalidx : env.findGram? "Blocalidx" = some ([], .varT "localidx" [], btypeidxProds)
  /-- `Blabelidx` (`A-binary.spectec:74`).  wasm-3.0 writes this one production
  with the metavariable `l` instead of `x`, which is the whole of its entry in
  `changedGramsV3`. -/
  blabelidx : env.findGram? "Blabelidx" = some ([], .varT "labelidx" [], btypeidxProds)
  /-- `Bnumtype` (`A-binary.spectec:89-93`). -/
  bnumtype : env.findGram? "Bnumtype" = some ([], .varT "numtype" [], bnumtypeV2Prods)
  /-- `Bvectype` (`A-binary.spectec:95-96`). -/
  bvectype : env.findGram? "Bvectype" = some ([], .varT "vectype" [], bvectypeProds)
  /-- `Breftype` (`A-binary.spectec:98-100`). -/
  breftype : env.findGram? "Breftype" = some ([], .varT "reftype" [], breftypeV2Prods)
  /-- `Bmut` (`A-binary.spectec:120-122`). -/
  bmut : env.findGram? "Bmut" = some ([], .varT "mut" [], V1Binary.bmutV1Prods)
  /-- `Blimits` (`A-binary.spectec:124-126`). -/
  blimits : env.findGram? "Blimits" = some ([], .varT "limits" [], V1Binary.blimitsV1Prods)
  /-- `Bexternidx` (`A-binary.spectec:76-80`). -/
  bexternidx : env.findGram? "Bexternidx"
    = some ([], .varT "externidx" [], V1Binary.bexternidxV1Prods)

/-- The corrected wasm-2.0 environment satisfies it, by `rfl` against the
stream. -/
theorem hasV2Types_v2 : HasV2Types envV2 :=
  ⟨findGram_bu32_prods_v2, findGram_bu64_prods_v2, findGram_btypeidx_v2,
    findGram_bfuncidx_v2, findGram_bglobalidx_v2, findGram_btableidx_v2,
    findGram_bmemidx_v2, findGram_belemidx_v2, findGram_bdataidx_v2,
    findGram_blocalidx_v2, findGram_blabelidx_v2, findGram_bnumtype_v2,
    findGram_bvectype_v2, findGram_breftype_v2, findGram_bmut_v2,
    findGram_blimits_v2, findGram_bexternidx_v2⟩

/-! ## The `u32` wrappers and the nine index grammars -/

/-- `grammar Bu32 : u32 = BuN(32)` is `Silmaril.Wasm.Binary.U32`, as a
`SymDerives`. -/
theorem symDerives_bu32_v2 {env : Env} (h : HasV2Types env) (hl : HasLeb env)
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
theorem symDerives_bu64_v2 {env : Env} (h : HasV2Types env) (hl : HasLeb env)
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

/-- **All nine index grammars are `Silmaril.Wasm.Binary.Index`.**
`A-binary.spectec:66-74` writes them with one and the same production
`x:Bu32 => x`, so the elaborated production list is literally shared and one
lemma covers `Btypeidx`, `Bfuncidx`, `Bglobalidx`, `Btableidx`, `Bmemidx`,
`Belemidx`, `Bdataidx`, `Blocalidx` and `Blabelidx`. -/
theorem symDerives_idxGram_v2 {env : Env} {x : IL.Id} {t : Typ} (h : HasV2Types env)
    (hl : HasLeb env) (hg : env.findGram? x = some ([], t, btypeidxProds))
    {k : Wasm.IndexKind} {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG x []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ y : Wasm.Idx k, Index bs y ∧ l = [Encode.toValue y] := by
  rw [symDerives_wrapper rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hd => ((symDerives_varG h.bu32).mp hd).1) hg]
  constructor
  · rintro ⟨rfl, w, hw, rfl⟩
    obtain ⟨-, m, hm, hl'⟩ := (symDerives_bu32_v2 h hl).mp hw
    exact ⟨rfl, ⟨⟨m, UN.lt_two_pow hm⟩⟩, hm, hl'⟩
  · rintro ⟨rfl, y, hy, rfl⟩
    exact ⟨rfl, _, (symDerives_bu32_v2 h hl).mpr ⟨rfl, y.toNat, hy, rfl⟩, rfl⟩

/-! ## The types section: agreement with `Silmaril/Wasm/Binary/` -/

/-- **`Bnumtype` is `Silmaril.Wasm.Binary.Core.NumType`** (`A-binary.spectec:89-93`):
the four numeric types, which wasm-2.0 lists in the opposite order to
wasm-3.0's `5.2-binary.types.spectec:7-11` and in the same order as
wasm-1.0's `Bvaltype`. -/
theorem symDerives_bnumtype_v2 {env : Env} (h : HasV2Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bnumtype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ t : Wasm.NumType, Core.NumType bs t ∧ l = [Encode.toValue t] := by
  rw [symDerives_varG h.bnumtype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bnumtypeV2Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
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
      exact ⟨_, by simp [bnumtypeV2Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩

/-- **`Bvectype` is `Silmaril.Wasm.Binary.Core.VecType`** (`A-binary.spectec:95-96`),
and this production is byte-identical to wasm-3.0's. -/
theorem symDerives_bvectype_v2 {env : Env} (h : HasV2Types env) {ρ ρ' : VarEnv}
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

/-- **`Bmut` is `Silmaril.Wasm.Binary.Core.Mut`** (`A-binary.spectec:120-122`).
`1-syntax.spectec:162` makes wasm-2.0's `mut` the *option* `MUT?`, as
wasm-1.0 does, so the grammar's value is an `opt`; wasm-3.0 spells the same
thing by giving `Bmut` the type `mut?`. -/
theorem symDerives_bmut_v2 {env : Env} (h : HasV2Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bmut" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ m : Wasm.Mutability, Core.Mut bs m ∧ l = [Encode.toValue m] := by
  rw [symDerives_varG h.bmut]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [V1Binary.bmutV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
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
    · exact ⟨_, by simp [V1Binary.bmutV1Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_optE_none_iff.mpr rfl, rfl⟩⟩
    · exact ⟨_, by simp [V1Binary.bmutV1Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_optE_some_iff.mpr ⟨_, evalExp_nullaryCase.mpr rfl, rfl⟩, rfl⟩⟩

/-! ### `Breftype`: where wasm-2.0 and the shared Lean layer part company

`A-binary.spectec:98-100` is two nullary injections, `FUNCREF` and
`EXTERNREF`.  `Silmaril/Wasm/Binary/Core/Types.lean`'s `RefType` is wasm-3.0's
`REF NULL? heaptype`, and `Forms.v1` — the gate that turns off every form
wasm-1.0 does not have — still admits all twelve `Babsheaptype` bytes bare.
So there is no `Encode` bridge here (the *abstract syntax* differs, not just
the grammar), and what can be compared is the byte language.  It is a strict
inclusion in one direction. -/

/-- **`Breftype` derives exactly `0x70` and `0x6F`**, with the nullary
injections wasm-2.0's `syntax reftype` gives them. -/
theorem symDerives_breftype_v2 {env : Env} (h : HasV2Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Breftype" []) bs l ρ' ↔
      ρ' = ρ ∧ ((bs = [0x70] ∧ l = [.case "FUNCREF" (.tuple [])]) ∨
                (bs = [0x6F] ∧ l = [.case "EXTERNREF" (.tuple [])])) := by
  rw [symDerives_varG h.breftype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [breftypeV2Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [evalExp_nullaryCase] at hv
      exact Or.inl ⟨rfl, by rw [hv]⟩
    · obtain ⟨rfl, v, hv, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [evalExp_nullaryCase] at hv
      exact Or.inr ⟨rfl, by rw [hv]⟩
  · rintro ⟨rfl, hc | hc⟩ <;> obtain ⟨rfl, rfl⟩ := hc
    · exact ⟨rfl, _, by simp [breftypeV2Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩
    · exact ⟨rfl, _, by simp [breftypeV2Prods], (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, evalExp_nullaryCase.mpr rfl, rfl⟩⟩

/-- **Every byte string `Breftype` derives is one the shared Lean
`Core.RefType` derives too**, at the `Forms.v1` gate, as a nullable abstract
reference. -/
theorem breftype_v2_le_core {env : Env} (h : HasV2Types env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value}
    (hd : SymDerives env ρ (.varG "Breftype" []) bs l ρ') :
    ∃ ht : Wasm.AbsHeapType, Core.AbsHeapType bs ht ∧
      Core.RefType Core.Forms.v1 bs ⟨true, .abstract ht⟩ := by
  obtain ⟨-, hc | hc⟩ := (symDerives_breftype_v2 h).mp hd <;> obtain ⟨rfl, -⟩ := hc
  · exact ⟨.func, .func, .abs .func⟩
  · exact ⟨.extern, .extern, .abs .extern⟩

/-- **The inclusion is strict.**  `0x6E` is `anyref` to the shared Lean layer
even at `Forms.v1`, and nothing at all to wasm-2.0, which has no `anyref`. -/
theorem not_breftype_v2_6E {env : Env} (h : HasV2Types env) (ρ ρ' : VarEnv)
    (l : List Value) : ¬ SymDerives env ρ (.varG "Breftype" []) [0x6E] l ρ' := by
  intro hd
  obtain ⟨-, hc | hc⟩ := (symDerives_breftype_v2 h).mp hd <;> exact absurd hc.1 (by decide)

/-- …while the shared layer's `RefType` does derive `anyref` from it. -/
theorem refType_v1_6E : Core.RefType Core.Forms.v1 [0x6E] ⟨true, .abstract .any⟩ := .abs .any

/-! ### Limits -/

/-- A `(attr (case "%" (tup (var y))) Bu32)` factor: it derives a `u32` and
binds `y` to the bare numeral. -/
theorem symDerives_bu32Factor_v2 {env : Env} (h : HasV2Types env) (hl : HasLeb env)
    {σ σ' : VarEnv} {y : IL.Id} {b : Grammar.Bytes} {ls : List Value}
    (hy : σ.findVal? y = none) :
    SymDerives env σ (.seqG [.attrG (.caseE "%" (.tupE [.varE y])) (.varG "Bu32" [])]) b ls σ'
      ↔ ∃ k, U32 b k ∧ ls = [numCase k] ∧ σ' = σ.bindVal y (.num (.natN k)) := by
  rw [symDerives_attrNT (fun _ _ _ _ hd => ((symDerives_varG h.bu32).mp hd).1)]
  constructor
  · rintro ⟨w, hw, rfl, hm⟩
    obtain ⟨-, k, hk, hlw⟩ := (symDerives_bu32_v2 h hl).mp hw
    have hw' : w = numCase k := by simpa using hlw
    subst hw'
    obtain ⟨u, hu, hmv⟩ := matchExp_case_var_elim hm
    have hu' : u = .num (.natN k) := by simpa [numCase] using hu.symm
    subst hu'
    rw [matchExp_varE_of_none_iff hy] at hmv
    exact ⟨k, hk, rfl, hmv⟩
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨numCase k, (symDerives_bu32_v2 h hl).mpr ⟨rfl, k, hk, rfl⟩, rfl,
      matchExp_case_var hy⟩

/-- **`Blimits` is `Silmaril.Wasm.V1.Binary.Limits`** (`A-binary.spectec:124-126`):
both bounds are `u32`, and wasm-2.0 — like wasm-1.0 and unlike wasm-3.0 — has
no address type to carry.  The production list is byte-identical to wasm-1.0's,
which is what `sharedGramsV1_agree` records. -/
theorem symDerives_blimits_v2 {env : Env} (h : HasV2Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Blimits" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ q : Wasm.V1.Limits, Wasm.V1.Binary.Limits bs q ∧ l = [Encode.toValue q] := by
  rw [symDerives_varG h.blimits]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [V1Binary.blimitsV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu32Factor_v2 h hl rfl).mp h₂
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_case_var rfl,
          evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩)
      exact ⟨⟨⟨k, UN.lt_two_pow hk⟩, none⟩, .min hk, rfl⟩
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, rfl, rfl⟩ :=
        symDerives_seqG_triple.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨k, hk, rfl, rfl⟩ := (symDerives_bu32Factor_v2 h hl rfl).mp h₂
      obtain ⟨m, hm, rfl, rfl⟩ := (symDerives_bu32Factor_v2 h hl rfl).mp h₃
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
            (symDerives_bu32Factor_v2 h hl rfl).mpr ⟨_, hb, rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
          evalExp_case_var rfl, evalExp_optE_none_iff.mpr rfl, rfl⟩, rfl⟩
    | minMax hb hb' =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_triple.mpr ⟨_, _, VarEnv.empty, _, _, _, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_bu32Factor_v2 h hl rfl).mpr ⟨_, hb, rfl, rfl⟩,
            (symDerives_bu32Factor_v2 h hl rfl).mpr ⟨_, hb', rfl, rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr ⟨_, _,
          evalExp_case_var rfl,
          evalExp_optE_some_iff.mpr ⟨_, evalExp_case_var rfl, rfl⟩, rfl⟩, rfl⟩

/-- **`Blimits` lands in the shared Lean `Limits` at the `Forms.v1` gate**, as
the `I32` address type with `u32` bounds — which is exactly what the shared
layer's `Limits.of_v1`/`Limits.to_v1` (`Silmaril/Wasm/Binary/Agreement/Sections.lean`)
say about the wasm-1.0 relation. -/
theorem symDerives_blimits_v2_core {env : Env} (h : HasV2Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Blimits" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ q : Wasm.V1.Limits, Core.Limits Core.Forms.v1 bs (.i32, q.toCore) ∧
        l = [Encode.toValue q] := by
  rw [symDerives_blimits_v2 h hl]
  constructor
  · rintro ⟨rfl, q, hq, rfl⟩
    exact ⟨rfl, q, Core.Limits.of_v1 hq, rfl⟩
  · rintro ⟨rfl, q, hq, rfl⟩
    exact ⟨rfl, q, Core.Limits.to_v1 Core.Forms.v1_le_lime1 hq, rfl⟩

/-! ### External indices -/

/-- **`Bexternidx` is `Silmaril.Wasm.Scalar.Binary.ExportDesc`**
(`A-binary.spectec:76-80`), the four tagged indices an export description is.
The production list is byte-identical to wasm-1.0's; wasm-3.0 adds a fifth
production for tags. -/
theorem symDerives_bexternidx_v2 {env : Env} (h : HasV2Types env) (hl : HasLeb env)
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
    simp only [V1Binary.bexternidxV1Prods, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · obtain ⟨l₀, σ, v, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hmt⟩ := (symDerives_attrNT hf).mp h₂
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v2 (k := .func) h hl h.bfuncidx).mp hw
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
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v2 (k := .table) h hl h.btableidx).mp hw
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
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v2 (k := .memory) h hl h.bmemidx).mp hw
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
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxGram_v2 (k := .global) h hl h.bglobalidx).mp hw
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
              (symDerives_idxGram_v2 h hl h.bfuncidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩
    | table hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT ht).mpr ⟨Encode.toValue (_ : Wasm.TableIdx),
              (symDerives_idxGram_v2 h hl h.btableidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩
    | memory hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT hm).mpr ⟨Encode.toValue (_ : Wasm.MemIdx),
              (symDerives_idxGram_v2 h hl h.bmemidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩
    | global hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          (prodDerives_simple rfl).mpr ⟨_, _, _,
          symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT hg).mpr ⟨Encode.toValue (_ : Wasm.GlobalIdx),
              (symDerives_idxGram_v2 h hl h.bglobalidx).mpr ⟨rfl, _, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩

/-- **`Bexternidx` lands in the shared Lean `Core.ExternIdx`**, through
`ExternIdx.of_v1` and `ExternIdx.to_v1` of
`Silmaril/Wasm/Binary/Agreement/Sections.lean`. -/
theorem symDerives_bexternidx_v2_core {env : Env} (h : HasV2Types env) (hl : HasLeb env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bexternidx" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ x : Wasm.V1.ExternIdx, Core.ExternIdx bs x.toCore ∧ l = [Encode.toValue x] := by
  rw [symDerives_bexternidx_v2 h hl]
  constructor
  · rintro ⟨rfl, x, hx, rfl⟩
    exact ⟨rfl, x, Core.ExternIdx.of_v1 hx, rfl⟩
  · rintro ⟨rfl, x, hx, rfl⟩
    exact ⟨rfl, x, Core.ExternIdx.to_v1 hx, rfl⟩

/-! ## The denotations, as `gramRelSup`, at the corrected wasm-2.0 script -/

/-- `Btypeidx` (`A-binary.spectec:66`) denotes `Silmaril.Wasm.Binary.Index`. -/
theorem gramRel_btypeidx_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Btypeidx" []) bs v ↔
      ∃ x : Wasm.TypeIdx, Index bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ :=
      (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2 hasV2Types_v2.btypeidx).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2
      hasV2Types_v2.btypeidx).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bdataidx` (`A-binary.spectec:72`) denotes `Silmaril.Wasm.Binary.Index`;
wasm-1.0 has no data index at all. -/
theorem gramRel_bdataidx_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bdataidx" []) bs v ↔
      ∃ x : Wasm.DataIdx, Index bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ :=
      (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2 hasV2Types_v2.bdataidx).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2
      hasV2Types_v2.bdataidx).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Belemidx` (`A-binary.spectec:71`) denotes `Silmaril.Wasm.Binary.Index`. -/
theorem gramRel_belemidx_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Belemidx" []) bs v ↔
      ∃ x : Wasm.ElemIdx, Index bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ :=
      (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2 hasV2Types_v2.belemidx).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2
      hasV2Types_v2.belemidx).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Blabelidx` (`A-binary.spectec:74`) denotes `Silmaril.Wasm.Binary.Index`.
This is the one index grammar that is *not* byte-identical to wasm-3.0's, and
the difference is the metavariable's name. -/
theorem gramRel_blabelidx_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Blabelidx" []) bs v ↔
      ∃ x : Wasm.LabelIdx, Index bs x ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ :=
      (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2 hasV2Types_v2.blabelidx).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_idxGram_v2 hasV2Types_v2 hasLeb_v2
      hasV2Types_v2.blabelidx).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bnumtype` (`A-binary.spectec:89-93`) denotes exactly
`Silmaril.Wasm.Binary.Core.NumType`. -/
theorem gramRel_bnumtype_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bnumtype" []) bs v ↔
      ∃ t : Wasm.NumType, Core.NumType bs t ∧ v = Encode.toValue t := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bnumtype_v2 hasV2Types_v2).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bnumtype_v2 hasV2Types_v2).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bvectype` (`A-binary.spectec:95-96`) denotes exactly
`Silmaril.Wasm.Binary.Core.VecType`. -/
theorem gramRel_bvectype_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bvectype" []) bs v ↔
      ∃ t : Wasm.VecType, Core.VecType bs t ∧ v = Encode.toValue t := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bvectype_v2 hasV2Types_v2).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bvectype_v2 hasV2Types_v2).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bmut` (`A-binary.spectec:120-122`) denotes exactly
`Silmaril.Wasm.Binary.Core.Mut`. -/
theorem gramRel_bmut_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bmut" []) bs v ↔
      ∃ m : Wasm.Mutability, Core.Mut bs m ∧ v = Encode.toValue m := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bmut_v2 hasV2Types_v2).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bmut_v2 hasV2Types_v2).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Blimits` (`A-binary.spectec:124-126`) denotes exactly
`Silmaril.Wasm.V1.Binary.Limits`, hence `Limits Forms.v1` at the `I32` address
type. -/
theorem gramRel_blimits_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Blimits" []) bs v ↔
      ∃ q : Wasm.V1.Limits, Core.Limits Core.Forms.v1 bs (.i32, q.toCore) ∧
        v = Encode.toValue q := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_blimits_v2_core hasV2Types_v2 hasLeb_v2).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_blimits_v2_core hasV2Types_v2 hasLeb_v2).mpr ⟨rfl, a, ha, rfl⟩⟩

/-- `Bexternidx` (`A-binary.spectec:76-80`) denotes exactly
`Silmaril.Wasm.Binary.Core.ExternIdx` on the image of wasm-1.0's
`ExternIdx`. -/
theorem gramRel_bexternidx_v2 (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envV2 ρ (.varG "Bexternidx" []) bs v ↔
      ∃ x : Wasm.V1.ExternIdx, Core.ExternIdx bs x.toCore ∧ v = Encode.toValue x := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, a, ha, hres⟩ := (symDerives_bexternidx_v2_core hasV2Types_v2 hasLeb_v2).mp hd
    exact ⟨a, ha, by simpa using hres⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ρ, (symDerives_bexternidx_v2_core hasV2Types_v2 hasLeb_v2).mpr ⟨rfl, a, ha, rfl⟩⟩

/-! ## `Bmodule` and erratum `#672`: the module header

`A-binary.spectec:923-924` writes the wasm-2.0 module header as

```
grammar Bmodule : module =
  | 0x00 0x61 0x73 0x6D 1:Bu32 ...
```

`Bu32` is `BuN(32)` (`A-binary.spectec:37`, `:20-22`), so `1:Bu32` derives
*any* LEB128 encoding of the number 1 — the single byte `0x01`, but also
`0x81 0x00` and `0x81 0x80 0x80 0x80 0x00` — where the format, the reference
interpreter (`interpreter/binary/decode.ml:1262-1266`) and
`Silmaril/Wasm/Binary/Core/Modules.lean` all demand the four raw bytes
`0x01 0x00 0x00 0x00`.  `Errata/Wasm20.lean`'s `erratum672` replaces the one
`Bu32` factor with four byte terminals.  This section is the verdict: after
the patch the grammar's header is exactly `Wasm.Binary.magic ++
Wasm.Binary.version`, which is the prefix `Core.Module` and `V1.Binary.Module`
require. -/

/-- A byte-terminal factor of a `Bmodule`-style sequence, `(seq (num 0xNN))`. -/
def byteFactor (b : UInt8) : IL.Sym := .seqG [.numG b.toNat]

/-- `Subst.subst_list Subst.subst_sym` distributes over an append. -/
theorem substSyms_append (σ : List (IL.Id × IL.Sym)) :
    ∀ gs hs : List IL.Sym, substSyms σ (gs ++ hs) = substSyms σ gs ++ substSyms σ hs
  | [], _ => rfl
  | g :: gs, hs => by
    rw [List.cons_append, substSyms_cons, substSyms_cons, substSyms_append σ gs hs,
      List.cons_append]

/-- A byte terminal has no grammar variables, so substitution leaves a run of
them alone. -/
theorem substSyms_map_byteFactor (σ : List (IL.Id × IL.Sym)) :
    ∀ ns : Grammar.Bytes, substSyms σ (ns.map byteFactor) = ns.map byteFactor
  | [] => rfl
  | n :: ns => by
    rw [List.map_cons, substSyms_cons, substSyms_map_byteFactor σ ns, byteFactor,
      substSym_seqG, substSyms_cons, substSym_numG]
    rfl

/-- **A run of byte terminals derives exactly its own bytes.**  Peeling the
leading byte terminals off a sequence, one `symDerives_seqG_cons` at a time. -/
theorem symDerives_leadBytes {env : Env} :
    ∀ (ns : Grammar.Bytes) (rest : List IL.Sym) {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
      {l : List Value},
      SymDerives env ρ (.seqG (ns.map byteFactor ++ rest)) bs l ρ' →
      ∃ (b₂ : Grammar.Bytes) (l₂ : List Value) (ρ₁ : VarEnv),
        bs = ns ++ b₂ ∧ SymDerives env ρ₁ (.seqG rest) b₂ l₂ ρ'
  | [], rest, _, _, bs, l => fun h => ⟨bs, l, _, rfl, by simpa using h⟩
  | n :: ns, rest, ρ, ρ', bs, l => by
    intro h
    rw [List.map_cons, List.cons_append, symDerives_seqG_cons] at h
    obtain ⟨b₁, l₁, ρ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := h
    rw [byteFactor, symDerives_byteFactor n.toNat_lt_size] at h₁
    obtain ⟨rfl, -, -⟩ := h₁
    obtain ⟨b₃, l₃, ρ₂, rfl, h₃⟩ := symDerives_leadBytes ns rest h₂
    exact ⟨b₃, l₃, ρ₂, by simp, h₃⟩

/-- The eight byte terminals the corrected `Bmodule` begins with: the magic
number and the four-byte version. -/
def headerSyms : List IL.Sym :=
  [byteFactor 0x00, byteFactor 0x61, byteFactor 0x73, byteFactor 0x6D,
    byteFactor 0x01, byteFactor 0x00, byteFactor 0x00, byteFactor 0x00]

/-- They are exactly `Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version`,
read as factors. -/
theorem headerSyms_eq : headerSyms = (magic ++ version).map byteFactor := rfl

/-- The four byte terminals the *pinned* `Bmodule` begins with: the magic
number alone. -/
def magicSyms : List IL.Sym := (magic : Grammar.Bytes).map byteFactor

/-- The pinned version factor, `1:Bu32` (`A-binary.spectec:924`). -/
def pinnedVersionSym : IL.Sym :=
  .seqG [.attrG (.caseE "%" (.tupE [.numE (.natN 1)])) (.varG "Bu32" [])]

/-- **The corrected `Bmodule`, read off the stream.**  One production, whose
body is a sequence beginning with the eight byte terminals of `headerSyms`. -/
private theorem findGram_bmodule_v2 :
    ∃ (q : List Param) (gs : List IL.Sym) (e : Exp) (prems : List Prem),
      envV2.findGram? "Bmodule"
        = some ([], .varT "module" [], [.prodD q (.seqG (headerSyms ++ gs)) e prems]) :=
  ⟨_, _, _, _, rfl⟩

/-- **The pinned `Bmodule`, read off the stream.**  The same production, with
the four magic bytes followed by the single `1:Bu32` factor. -/
private theorem findGram_bmodule_pinned :
    ∃ (q : List Param) (gs : List IL.Sym) (e : Exp) (prems : List Prem),
      (envOfScript Specs.wasm20).findGram? "Bmodule"
        = some ([], .varT "module" [],
            [.prodD q (.seqG (magicSyms ++ pinnedVersionSym :: gs)) e prems]) :=
  ⟨_, _, _, _, rfl⟩

/-- `Bu32`, `BuN` and `Bbyte` are the same in the pinned and the corrected
wasm-2.0 scripts: `erratum672` touches only `Bmodule`. -/
private theorem findGram_bu32_pinned_v2 :
    (envOfScript Specs.wasm20).findGram? "Bu32" = some ([], .varT "u32" [], bu32Prods) := rfl

/-- The pinned wasm-2.0 environment has the same LEB128 grammars. -/
theorem hasLeb_pinned_v2 : HasLeb (envOfScript Specs.wasm20) := ⟨rfl, rfl⟩

/-- …and the same index and type grammars: `erratum672` touches only
`Bmodule`, `erratum670` only `Binstr`, `erratum671` only `Belem` and
`erratum673` only `dataidx_instrs`. -/
theorem hasV2Types_pinned_v2 : HasV2Types (envOfScript Specs.wasm20) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The verdict on `#672`.**  Every byte string the *corrected* wasm-2.0
`Bmodule` derives begins with `magic ++ version`, the eight bytes
`Silmaril/Wasm/Binary/Core/Modules.lean`'s `Module` and
`Silmaril/Wasm/V1/Binary/Modules.lean`'s `Module` both require.  So the
erratum does make the header agree with our Lean. -/
theorem bmodule_header_v2 {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value}
    (hd : SymDerives envV2 ρ (.varG "Bmodule" []) bs l ρ') :
    ∃ r : Grammar.Bytes, bs = magic ++ version ++ r := by
  obtain ⟨q, gs, e, prems, hg⟩ := findGram_bmodule_v2
  rw [symDerives_varG hg] at hd
  obtain ⟨-, p, hp, hdd⟩ := hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩ := hdd
  rw [substSym_seqG, substSyms_append, headerSyms_eq, substSyms_map_byteFactor] at hs
  obtain ⟨b₂, l₂, ρ₃, rfl, -⟩ := symDerives_leadBytes _ _ hs
  exact ⟨b₂, by simp⟩

/-- **And the pinned `Bmodule` does not.**  Its header is the four magic bytes
followed by whatever `Bu32` derives for the value 1 — a LEB128 numeral, not a
fixed byte string. -/
theorem bmodule_header_pinned_v2 {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value}
    (hd : SymDerives (envOfScript Specs.wasm20) ρ (.varG "Bmodule" []) bs l ρ') :
    ∃ (b r : Grammar.Bytes) (m : Nat), U32 b m ∧ bs = magic ++ b ++ r := by
  obtain ⟨q, gs, e, prems, hg⟩ := findGram_bmodule_pinned
  rw [symDerives_varG hg] at hd
  obtain ⟨-, p, hp, hdd⟩ := hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩ := hdd
  rw [substSym_seqG, substSyms_append, magicSyms, substSyms_map_byteFactor,
    substSyms_cons] at hs
  obtain ⟨b₂, l₂, ρ₃, rfl, hrest⟩ := symDerives_leadBytes _ _ hs
  rw [symDerives_seqG_cons] at hrest
  obtain ⟨b₄, l₄, ρ₄, b₅, l₅, h₄, -, rfl, -⟩ := hrest
  rw [show substSym (gramArgSubst [] ([] : List IL.Arg)) pinnedVersionSym
      = pinnedVersionSym from rfl, pinnedVersionSym,
    symDerives_attrNT (z := "Bu32")
      (fun _ _ _ _ hdv => ((symDerives_varG findGram_bu32_pinned_v2).mp hdv).1)] at h₄
  obtain ⟨w, hw, -, -⟩ := h₄
  obtain ⟨-, m, hm, -⟩ := (symDerives_bu32_v2 hasV2Types_pinned_v2 hasLeb_pinned_v2).mp hw
  exact ⟨b₄, b₅, m, hm, by simp⟩

/-- **The pinned version field is ambiguous**, which is the sharper form of
`#672`: `Bu32` derives both `0x01` and the non-minimal `0x81 0x00`, and both
denote 1, so the pinned wasm-2.0 `Bmodule` accepts `00 61 73 6D 81 00 …` as a
module header.  `Silmaril.Wasm.Binary.Core.Module` accepts neither five-byte
header. -/
theorem u32_one_ambiguous : U32 [0x01] 1 ∧ U32 [0x81, 0x00] 1 := by
  refine ⟨.byte 0x01 (by decide) (by decide), ?_⟩
  have h : U32 [0x81, 0x00] (2 ^ 7 * 0 + ((0x81 : UInt8).toNat - 2 ^ 7)) :=
    .cont 0x81 (by decide) (by decide) (.byte 0x00 (by decide) (by decide))
  simpa using h

/-! ## What is proved, and what is not

### Proved

**No wasm-2.0 Lean semantics exists in this checkout.**  The module docstring
records the evidence; everything below is therefore stated against wasm-3.0,
against wasm-1.0, or against the version-independent `Silmaril/Wasm/Binary/`.

**The version census**, four `rfl`s, one `IL.defEq` per name:

* `sharedGramsV3_agree` — 49 of wasm-2.0's 71 grammars are byte-identical to
  wasm-3.0's;
* `changedGramsV3_differ` — 21 are declared in both and differ;
* `v2OnlyGrams_absent` — `Bfunctype` is wasm-2.0's and not wasm-3.0's;
* `sharedGramsV1_agree` — 50 are byte-identical to the corrected wasm-1.0's.

`eq_of_defsAgree`, `ne_of_defsDiffer` and `absent_of_defsAbsent` are what the
three `Bool`s mean: "declared exactly once in each, by the same `IL.Def`",
"declared in both and different", "declared here and not there".

**The values section** (`A-binary.spectec:18-46`), at the corrected wasm-2.0
script:

* `hasLeb_v2`, `hasSignedLeb_v2`, `hasWrappers_v2` — `Bbyte`, `BuN`, `BsN`,
  `BiN`, `Bu32`, `Bs33` are wasm-3.0's, so every theorem of
  `Sem/Grammar.lean` and `Equiv/BinaryValues.lean` about them is a theorem
  about wasm-2.0;
* `bbyte_iff_byte_v2`, `bun_iff_un_v2`, `bu32_iff_u32_v2`, `bu64_iff_u64_v2` —
  `Bbyte` is `Byte`, `BuN(N)` is `UN N`, `Bu32` is `U32`, `Bu64` is `U64`;
* `bsn_iff_sn_v2`, `bs33_iff_s33_v2` — `BsN(N)` is `SN N` restricted to
  single-byte encodings and non-negative values, **exactly**, and `Bs33` is
  `S33` under the same restriction;
* `hasCorrectedBi_v2` — wasm-2.0 has no `#654`: `A-binary.spectec:42-43`
  already reads `Bi32 = BiN(32)`.

**The `BsN` verdict for wasm-2.0** (`#803`): the defect is
present, unchanged, and in the sharper wasm-1.0 form.  `not_bsn_FF7E_v2`,
`not_bi32_FF7E_v2`, `not_bi64_FF7E_v2` — `FF 7E`, the signed LEB128 of `-129`,
has no derivation; `bi32_v2_disagrees_with_in` — the corrected wasm-2.0 `Bi32`
disagrees with `Silmaril.Wasm.Binary.IN 32`, with nothing left to patch at the
`Bi32` level.

**The types section** (`A-binary.spectec:66-126`), each an equality of
relations proved in both directions and transported along `Encode.toValue`:

| SpecTec | Lean | statement |
| --- | --- | --- |
| `Btypeidx` … `Blabelidx` (nine) | `Wasm.Binary.Index` | `symDerives_idxGram_v2` |
| `Bnumtype` | `Wasm.Binary.Core.NumType` | `gramRel_bnumtype_v2` |
| `Bvectype` | `Wasm.Binary.Core.VecType` | `gramRel_bvectype_v2` |
| `Bmut` | `Wasm.Binary.Core.Mut` | `gramRel_bmut_v2` |
| `Blimits` | `Wasm.Binary.Core.Limits Forms.v1` | `gramRel_blimits_v2` |
| `Bexternidx` | `Wasm.Binary.Core.ExternIdx` | `gramRel_bexternidx_v2` |

`Blimits` and `Bexternidx` go through `Silmaril.Wasm.V1.Binary.Limits` and
`Silmaril.Wasm.Scalar.Binary.ExportDesc` — the relations whose `Encode`
bridges `Equiv/V1Binary.lean` supplies — and then through `Limits.of_v1`,
`Limits.to_v1`, `ExternIdx.of_v1`, `ExternIdx.to_v1` of
`Silmaril/Wasm/Binary/Agreement/Sections.lean`.  That those two 2.0 grammars
are byte-identical to wasm-1.0's is `sharedGramsV1_agree`; the proofs are
re-run here rather than imported, because `Equiv/V1Binary.lean` bundles its
hypotheses into a `HasV1Types` that wasm-2.0 does **not** satisfy (its
`Bvaltype`, `Btabletype`, `Bmemtype` and `Bblocktype` differ from wasm-1.0's).

**`Breftype`, and where wasm-2.0 leaves the shared Lean layer.**
`symDerives_breftype_v2` is exact: `0x70 => FUNCREF` and `0x6F => EXTERNREF`,
and nothing else.  `breftype_v2_le_core` sends each of those two derivations
into `Core.RefType Forms.v1` as a nullable abstract reference, and
`not_breftype_v2_6E` with `refType_v1_6E` shows the inclusion is **strict**:
`0x6E` is `anyref` to the shared layer even at the `Forms.v1` gate and is
nothing at all to wasm-2.0.  There is no `Encode` bridge in this case, because
wasm-2.0's `syntax reftype` is two nullary injections where wasm-3.0's — which
is what `Silmaril.Wasm.RefType` transcribes — is `REF NULL? heaptype`; what
agrees is the byte language, not the values.

**Erratum `#672`.**  `bmodule_header_v2`: every byte string the corrected
`Bmodule` derives begins with `Wasm.Binary.magic ++ Wasm.Binary.version`, the
eight bytes both of Silmaril's module decoders require — so **yes**, `#672`
makes the header agree with our Lean.  `bmodule_header_pinned_v2`: the pinned
header is the four magic bytes followed by whatever `Bu32` derives for 1, and
`u32_one_ambiguous` is that this is `0x01` *and* `0x81 0x00`, so the pinned
grammar is ambiguous about a header our Lean fixes to four bytes.
`symDerives_leadBytes` is the reusable part: a run of byte terminals at the
head of a production derives exactly its own bytes.

### Not proved

* **Everything above `Blist`.**  `Blist(BX) = n:Bu32 (el:BX)^n`
  (`A-binary.spectec:7-8`) is byte-identical to wasm-3.0's and denotes an
  `IterG` with a `ListN` counter; the generic bridge "`Blist(BX)` denotes
  `Silmaril.Wasm.Binary.Vec R` whenever `BX` denotes `R`" is still not proved
  anywhere in this tree, and without it `Bresulttype`
  (`A-binary.spectec:108-109`), `Bfunctype` (`:114-115`), `Bexterntype`
  (`:138-142`), `Bname` (`:60-61`) and the whole module section are out of
  reach.  This is the same gap `Equiv/BinaryTypes.lean` and
  `Equiv/V1Binary.lean` record, and it is the single lemma that would unlock
  the most here.
* **`Bvaltype`.**  Its production list *is* wasm-3.0's, byte for byte
  (`sharedGramsV3_agree`), but it reads a `Breftype`, and wasm-2.0's
  `Breftype` is not wasm-3.0's — so neither `Equiv/BinaryTypes.lean`'s
  `symDerives_bvaltype` nor `Equiv/V1Binary.lean`'s `symDerives_bvaltype_v1`
  applies, and no wasm-2.0 `Bvaltype` theorem is proved here.  The same goes
  for `Bglobaltype` and `Btabletype`, whose production lists are wasm-1.0's
  but whose value types are not.
* **`Bmemtype`** (`A-binary.spectec:134-135`) is `lim:Blimits => lim PAGE`,
  which matches neither wasm-1.0's bare `lim` nor wasm-3.0's `at lim PAGE`;
  its agreement with `Core.MemType` is not proved.  **`Bblocktype`**
  (`A-binary.spectec:151-154`) has the `Bs33` production whose `#803`
  consequence `bs33_iff_s33_v2` already bounds, but its agreement with
  `Silmaril.Wasm.BlockType` is not proved.  **`Bmemarg`** is byte-identical to
  wasm-1.0's and `Equiv/V1Binary.lean` does not prove its agreement either
  (the production's value is a `struct`, and `Sem/Bridge.lean`'s
  `Encode.ofStruct` has no instance in this tree yet).
* **The instruction section.**  `Binstr` is one 79 701-character grammar; the
  census records only that it differs from wasm-3.0's and from wasm-1.0's.
  `#670` — `0xFD 92` given twice — is patched in `Errata/Wasm20.lean` and its
  effect on the derivation relation is not proved here.
* **The census outside the `grammar` namespace** is computed from the `--ast`
  streams and not kernel checked; see the module docstring for why
  (`IL.namedDefs` keys on the identifier alone, and wasm-2.0 reuses 32
  identifiers across two namespaces).
* **`bmodule_header_v2` is one-directional.**  It says every derivation of the
  corrected `Bmodule` starts with the eight header bytes.  It does **not** say
  that the corrected `Bmodule` derives anything at all: that needs `Blist`,
  every section grammar and `Binstr`.  The same holds of
  `bmodule_header_pinned_v2`; `u32_one_ambiguous` is a statement about `Bu32`,
  not about a complete pinned module derivation.
* **`$utf8`, `BfN`, `$inv_signed_`, `$inv_fbytes_`.**  wasm-2.0's `$utf8`
  (`A-binary.spectec:54-58`) has the same shape as wasm-1.0's — four clauses
  whose result expressions mention byte variables the clause's scope does not
  bind — and `Equiv/V1Binary.lean`'s analysis of it was not re-run here.
  `BfN` is byte-identical to wasm-3.0's and untouched, as in both neighbours.
* **The four unpatched sub-issues of `#660`** (`#674`, `#675`, `#676`, `#678`)
  and four later ones are typing and reduction
  defects; `Errata/Wasm20.lean` triages them and nothing here touches them.
-/

end Silmaril.SpecTec.Equiv.Wasm20
