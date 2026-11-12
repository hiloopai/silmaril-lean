module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Bridge
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Grammar
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The values section of the binary format, two ways

`specification/wasm-3.0/5.1-binary.values.spectec` and
`Silmaril/Wasm/Binary/Basic.lean` are two independent readings of the same
thing: bytes, LEB128 integers, lists and names.  This file compares them — not
the `.spectec` source against the Lean text, but the **denotation of the
elaborated grammar** (`Sem/Grammar.lean`'s `gramRelSup`, an
`EncRel (List UInt8) Value`) against the hand-written inductive `Encodes`
relations, with `Sem/Bridge.lean`'s `Encode` class supplying the
correspondence between the two notions of value.

Everything is relative to the pin `608711107b7f1edb13efd57b7d79b49477462d36`.

## Which script

Two, and the difference matters.  `Silmaril.SpecTec.Specs.wasm30` is the
pinned stream; `Silmaril.SpecTec.IL.Binary51.wasm30binary51` is it with
`#650`'s four patches applied (`docs/projects/spectec-divergences.md`).
`#654` changes `Bi32` and `Bi64` and nothing else in this section, so `Bbyte`,
`BuN`, `BsN`, `BiN`, `Bu32`, `Bu64` and `Bs33` are literally the same
definitions in both — which is what `hasLeb_corrected`,
`hasSignedLeb_corrected` and `hasWrappers_corrected` record, each by a `rfl`
against the script itself.

Every statement is made for an arbitrary environment satisfying a `Has…`
hypothesis, so that it does not depend on the other 970 definitions, and then
discharged at the two scripts.

## The values, through the bridge

`Sem/Bridge.lean` fixes the conventions.  The three this file needs:

| SpecTec type | elaborated as | value | Lean |
| --- | --- | --- | --- |
| `byte` | `(case "%" (tup (bind "i" nat)) …)` | `percentV (num (natN b))` | `UInt8` |
| `uN(N)` | `(case "%" (tup (bind "i" nat)) …)` | `uNV m` = `Sem.numCase m` | `Nat` |
| `sN(N)` | `(case "%" (tup (bind "i" int)) …)` | `sNV i` | `Int` |

`iN(N)` is an *alias* of `uN(N)` (`1.1-syntax.values.spectec:14-15`), so the
value of a `BitVec N` is `iNV`, the `uN(N)` value of its natural number.  That
aliasing is exactly why the type checker cannot catch `#654`.

## The headline

`#654` says the pinned `Bi32`/`Bi64` use the *unsigned* grammar.  Here that is
`bi32_pinned_iff_un` (the pinned `Bi32` **is** `U32`) and
`bi32_pinned_disagrees_with_in` (so it is not `Silmaril.Wasm.Binary.IN 32`:
`7F` reads as `127`, not `-1`).

The expected companion — "and after the patch they agree" — is **false**, and
that is this file's main result.  `bsn_iff_sn` characterises the pinned
`BsN(N)` exactly: it is `SN N` restricted to single-byte encodings and
non-negative values.  The restriction is forced by the *elaborated* third
production, which narrows the recursive `sN` value from `int` to `nat` before
multiplying, and `Xl.Num.cvt` is partial there (`spectec/src/xl/num.ml:86`).
So the corrected `Bi32 = BiN(32)` still cannot read `FF 7E`, the encoding of
`i32.const -129`: `bi32_corrected_disagrees_with_in`.  The closing section of
this file states that finding with its scope and its caveats.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Binary

set_option maxRecDepth 4000000

/-! ## The values of the numeral types, through the bridge -/

/-- The `uN(N)` value of a natural number.  `uN(N)` is the one-case variant
`(case "%" (tup (bind "i" nat)) …)`, so this is `Sem.percentV` of the bridge's
`nat`, and it is `Sem.numCase` by definition. -/
def uNV (m : Nat) : Value := percentV (Encode.toValue m)

/-- `uNV` is `Sem/Grammar.lean`'s `numCase`. -/
@[simp] theorem uNV_eq_numCase (m : Nat) : uNV m = numCase m := rfl

/-- The `sN(N)` value of an integer.  `sN(N)` is `(case "%" (tup (bind "i" int)) …)`,
so the payload is the bridge's `int`. -/
def sNV (i : Int) : Value := percentV (Encode.toValue i)

/-- `sNV` unfolded. -/
theorem sNV_eq (i : Int) : sNV i = .case "%" (.tuple [.num (.intN i)]) := rfl

/-- The `byte` value of a byte is the bridge's `UInt8` encoding, and it is
`numCase` of the byte's natural number. -/
theorem toValue_uint8_eq_numCase (b : UInt8) :
    Encode.toValue b = numCase b.toNat := rfl

/-! ## The productions, read out of the pinned and the corrected scripts

Every definition below is checked against the actual script by a `rfl`: the
`private` theorems are the provenance, and nothing else in this file reads the
stream.  They are `private` because `Specs.wasm30` is added with
`Lean.addDecl` and is therefore not exposed to importers — the same reason
`Sem/Grammar.lean`'s `findGram_bbyte_wasm30` is private. -/

/-- `cvt nat int e`: the widening coercion, total. -/
def n2i (e : Exp) : Exp := .cvtE e .natT .intT

/-- `cvt int nat e`: the narrowing coercion, **partial** — `Xl.Num.cvt`
(`spectec/src/xl/num.ml:86`) is `None` on a negative integer. -/
def i2n (e : Exp) : Exp := .cvtE e .intT .natT

/-- `$(N - k)` as the elaborated stream spells it: subtract at `int`, then
narrow back to `nat`. -/
def nSubE (k : Nat) : Exp :=
  i2n (.binE .subOp (.numT .intT) (n2i (.varE "N")) (n2i (.numE (.natN k))))

/-- The parameter list of `grammar BsN(N)`
(`specification/wasm-3.0/5.1-binary.values.spectec:13`). -/
def bsnParams : List Param := [.expP "N" (.varT "N" [])]

/-- The type of `grammar BsN(N) : sN(N)`. -/
def bsnTyp : Typ := .varT "sN" [.expA (.varE "N")]

/-- The value expression of `BsN`'s third production, `$(2^7 * i + (n - 2^7))`
as SpecTec elaborates it.

**Read the coercions.**  `i` has type `sN(N-7)`, whose payload is an `int`;
the arithmetic was inferred at `nat`, so the elaborated form narrows the
recursive value with `cvt int nat` before multiplying and widens the sum back
with `cvt nat int`.  That narrowing is the subject of `bsn_rec_undef_of_neg`
below. -/
def bsnRecValue : Exp :=
  .caseE "%" (.tupE [ n2i (.binE .addOp (.numT .natT)
    (.binE .mulOp (.numT .natT) (twoPowE (.numE (.natN 7)))
      (i2n (.projE (.uncaseE (.varE "i") "%") 0)))
    (i2n (.binE .subOp (.numT .intT) (n2i (.varE "n"))
      (n2i (twoPowE (.numE (.natN 7))))))) ])

/-- The three productions of `grammar BsN(N)`
(`specification/wasm-3.0/5.1-binary.values.spectec:14-16`), as elaborated. -/
def bsnProds : List IL.Prod :=
  [ .prodD [.expP "n" (.varT "n" [])]
      (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" []))
      (.caseE "%" (.tupE [n2i (.varE "n")]))
      [ .ifPr (.binE .andOp .boolT
          (.cmpE .ltOp (.numT .natT) (.varE "n") (twoPowE (.numE (.natN 6))))
          (.cmpE .ltOp (.numT .natT) (.varE "n") (twoPowE (nSubE 1)))) ],
    .prodD [.expP "n" (.varT "n" [])]
      (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" []))
      (.caseE "%" (.tupE [.binE .subOp (.numT .intT) (n2i (.varE "n"))
          (n2i (twoPowE (.numE (.natN 7))))]))
      [ .ifPr (.binE .andOp .boolT
          (.binE .andOp .boolT
            (.cmpE .leOp (.numT .natT) (twoPowE (.numE (.natN 6))) (.varE "n"))
            (.cmpE .ltOp (.numT .natT) (.varE "n") (twoPowE (.numE (.natN 7)))))
          (.cmpE .geOp (.numT .intT) (n2i (.varE "n"))
            (.binE .subOp (.numT .intT) (n2i (twoPowE (.numE (.natN 7))))
              (n2i (twoPowE (nSubE 1)))))) ],
    .prodD [ .expP "i" (.varT "sN" [.expA (nSubE 7)]), .expP "n" (.varT "n" []) ]
      (.seqG [ .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])],
               .seqG [.attrG (.varE "i") (.varG "BsN" [.expA (nSubE 7)])] ])
      bsnRecValue
      [ .ifPr (.binE .andOp .boolT
          (.cmpE .geOp (.numT .natT) (.varE "n") (twoPowE (.numE (.natN 7))))
          (.cmpE .gtOp (.numT .natT) (.varE "N") (.numE (.natN 7)))) ] ]

/-- The sole production of `grammar BiN(N) : iN(N) = i:BsN(N) => $inv_signed_(N, i)`
(`specification/wasm-3.0/5.1-binary.values.spectec:18-19`), as elaborated. -/
def binProds : List IL.Prod :=
  [ .prodD [.expP "i" (.varT "sN" [.expA (.varE "N")])]
      (.attrG (.varE "i") (.varG "BsN" [.expA (.varE "N")]))
      (.caseE "%" (.tupE [.callE "inv_signed_"
        [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i") "%") 0)]])) [] ]

/-- The shape every one-line wrapper grammar of §5.1 elaborates to:
`grammar BX : t = BY(k)` becomes a single production binding an implicit
result. -/
def wrapProds (t : Typ) (g : IL.Id) (arg : Exp) : List IL.Prod :=
  [ .prodD [.expP "<implicit-prod-result>" t]
      (.attrG (.varE "<implicit-prod-result>") (.varG g [.expA arg]))
      (.varE "<implicit-prod-result>") [] ]

private theorem findGram_bsn_pinned :
    (envOfScript Specs.wasm30).findGram? "BsN" = some (bsnParams, bsnTyp, bsnProds) := rfl

private theorem findGram_bin_pinned :
    (envOfScript Specs.wasm30).findGram? "BiN"
      = some (bsnParams, .varT "iN" [.expA (.varE "N")], binProds) := rfl

private theorem findGram_bu32_pinned :
    (envOfScript Specs.wasm30).findGram? "Bu32"
      = some ([], .varT "u32" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 32))]) "BuN" (.numE (.natN 32))) := rfl

private theorem findGram_bu64_pinned :
    (envOfScript Specs.wasm30).findGram? "Bu64"
      = some ([], .varT "u64" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 64))]) "BuN" (.numE (.natN 64))) := rfl

private theorem findGram_bs33_pinned :
    (envOfScript Specs.wasm30).findGram? "Bs33"
      = some ([], .varT "s33" [],
          wrapProds (.varT "sN" [.expA (.numE (.natN 33))]) "BsN" (.numE (.natN 33))) := rfl

private theorem findGram_bi32_pinned :
    (envOfScript Specs.wasm30).findGram? "Bi32"
      = some ([], .varT "i32" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 32))]) "BuN" (.numE (.natN 32))) := rfl

private theorem findGram_bi64_pinned :
    (envOfScript Specs.wasm30).findGram? "Bi64"
      = some ([], .varT "i64" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 64))]) "BuN" (.numE (.natN 64))) := rfl

/-- The corrected wasm-3.0 script of `#650`. -/
noncomputable abbrev wasm30corrected : Script := IL.Binary51.wasm30binary51

/-- Its environment, which every theorem below about the *corrected*
specification is stated at. -/
noncomputable abbrev envCorrected : Env := envOfScript wasm30corrected

private theorem findGram_bbyte_corrected :
    envCorrected.findGram? "Bbyte" = some ([], .varT "byte" [], bbyteProds) := rfl

private theorem findGram_bun_corrected :
    envCorrected.findGram? "BuN" = some (bunParams, bunTyp, bunProds) := rfl

private theorem findGram_bsn_corrected :
    envCorrected.findGram? "BsN" = some (bsnParams, bsnTyp, bsnProds) := rfl

private theorem findGram_bin_corrected :
    envCorrected.findGram? "BiN"
      = some (bsnParams, .varT "iN" [.expA (.varE "N")], binProds) := rfl

private theorem findGram_bu32_corrected :
    envCorrected.findGram? "Bu32"
      = some ([], .varT "u32" [],
          wrapProds (.varT "uN" [.expA (.numE (.natN 32))]) "BuN" (.numE (.natN 32))) := rfl

private theorem findGram_bs33_corrected :
    envCorrected.findGram? "Bs33"
      = some ([], .varT "s33" [],
          wrapProds (.varT "sN" [.expA (.numE (.natN 33))]) "BsN" (.numE (.natN 33))) := rfl

private theorem findGram_bi32_corrected :
    envCorrected.findGram? "Bi32"
      = some ([], .varT "i32" [],
          wrapProds (.varT "iN" [.expA (.numE (.natN 32))]) "BiN" (.numE (.natN 32))) := rfl

private theorem findGram_bi64_corrected :
    envCorrected.findGram? "Bi64"
      = some ([], .varT "i64" [],
          wrapProds (.varT "iN" [.expA (.numE (.natN 64))]) "BiN" (.numE (.natN 64))) := rfl

/-! ## The hypotheses on an environment

Each result below is stated for any environment that defines the grammars it
uses exactly as the stream does, so that the proofs do not depend on the other
970-odd definitions.  `Sem/Grammar.lean`'s `HasLeb` covers `Bbyte` and `BuN`;
`HasSignedLeb` adds `BsN` and `BiN`. -/

/-- An environment whose `BsN` and `BiN` are the pinned ones — which the
corrected script's also are, since `#654` changes only `Bi32` and `Bi64`. -/
structure HasSignedLeb (env : Env) : Prop where
  /-- `BsN` is the pinned one. -/
  bsn : env.findGram? "BsN" = some (bsnParams, bsnTyp, bsnProds)
  /-- `BiN` is the pinned one. -/
  bin : env.findGram? "BiN" = some (bsnParams, .varT "iN" [.expA (.varE "N")], binProds)

/-- An environment whose one-line wrappers are the pinned ones. -/
structure HasWrappers (env : Env) : Prop where
  /-- `Bu32 = BuN(32)`. -/
  bu32 : env.findGram? "Bu32" = some ([], .varT "u32" [],
    wrapProds (.varT "uN" [.expA (.numE (.natN 32))]) "BuN" (.numE (.natN 32)))
  /-- `Bs33 = BsN(33)`. -/
  bs33 : env.findGram? "Bs33" = some ([], .varT "s33" [],
    wrapProds (.varT "sN" [.expA (.numE (.natN 33))]) "BsN" (.numE (.natN 33)))

/-- The pinned environment. -/
theorem hasSignedLeb_wasm30 : HasSignedLeb (envOfScript Specs.wasm30) :=
  ⟨findGram_bsn_pinned, findGram_bin_pinned⟩

/-- The corrected environment: `#654` leaves `BsN` and `BiN` alone. -/
theorem hasSignedLeb_corrected : HasSignedLeb envCorrected :=
  ⟨findGram_bsn_corrected, findGram_bin_corrected⟩

/-- `Bbyte` and `BuN` survive the patches unchanged, so every theorem of
`Sem/Grammar.lean` about them applies verbatim to the corrected script. -/
theorem hasLeb_corrected : HasLeb envCorrected :=
  ⟨findGram_bbyte_corrected, findGram_bun_corrected⟩

/-- The pinned environment. -/
theorem hasWrappers_wasm30 : HasWrappers (envOfScript Specs.wasm30) :=
  ⟨findGram_bu32_pinned, findGram_bs33_pinned⟩

/-- The corrected environment: `#654` leaves `Bu32` and `Bs33` alone. -/
theorem hasWrappers_corrected : HasWrappers envCorrected :=
  ⟨findGram_bu32_corrected, findGram_bs33_corrected⟩

/-! ## `Bbyte`: a single byte

`Sem/Grammar.lean` already proves that the pinned `Bbyte` derives exactly the
one-byte strings, with the `byte` value of the byte.  Through the bridge, that
is the statement that it is `Silmaril.Wasm.Binary.Byte`. -/

/-- **`Bbyte` is `Silmaril.Wasm.Binary.Byte`.**  Both directions, with the
value given by the bridge's `Encode UInt8` instance — which is the SpecTec
type `byte`, `(case "%" (tup (bind "i" nat)) (if 0 <= i <= 255))`. -/
theorem bbyte_iff_byte {env : Env} (h : HasLeb env) (ρ : VarEnv) (bs : Grammar.Bytes)
    (v : Value) :
    gramRelSup env ρ (.varG "Bbyte" []) bs v ↔ ∃ b : UInt8, Byte bs b ∧ v = Encode.toValue b := by
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    obtain ⟨b, rfl, hv, -⟩ := bbyte_elim h hd
    refine ⟨b, .mk b, ?_⟩
    show v = numCase b.toNat
    simpa using hv
  · rintro ⟨b, hb, rfl⟩
    cases hb
    exact gramRelSup_iff.mpr ⟨ρ, bbyte_derives h ρ b⟩

/-- `Bbyte` at the corrected wasm-3.0 script. -/
theorem bbyte_iff_byte_corrected (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envCorrected ρ (.varG "Bbyte" []) bs v ↔
      ∃ b : UInt8, Byte bs b ∧ v = Encode.toValue b :=
  bbyte_iff_byte hasLeb_corrected ρ bs v

/-! ## `BuN`: unsigned LEB128

`Sem/Grammar.lean`'s `bun_iff_un` is the agreement with
`Silmaril.Wasm.Binary.UN`, proved at the pinned script.  `#654` does not touch
`Bbyte` or `BuN`, so `hasLeb_corrected` transports it to the corrected one. -/

/-- **The corrected `BuN(N)` is `Silmaril.Wasm.Binary.UN N`.** -/
theorem bun_iff_un_corrected (W : Nat) (bs : Grammar.Bytes) (v : Value) (ρ : VarEnv) :
    gramRelSup envCorrected ρ (.varG "BuN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ m, UN W bs m ∧ v = uNV m :=
  bun_iff_un hasLeb_corrected W bs v ρ

/-! ## The one-line wrappers

`grammar Bu32 : u32 = BuN(32)` elaborates to a single production that binds an
implicit result to `BuN(32)` and returns it; the same shape carries `Bu64`,
`Bs33`, `Bi32` and `Bi64`.  One lemma covers them all. -/

/-- A wrapper grammar denotes exactly what it wraps, at the empty scope: the
production's fresh scope binds nothing but the implicit result, so neither the
caller's scope nor the wrapper's own bindings are visible to the wrapped
nonterminal. -/
theorem wrap_rel_iff {env : Env} {x gx : IL.Id} {tw t : Typ} {arg : Exp} {dgx : GramDef}
    (h : env.findGram? x = some ([], tw, wrapProds t gx arg))
    (hg : env.findGram? gx = some dgx) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG x []) bs v ↔
      gramRelSup env VarEnv.empty (.varG gx [.expA arg]) bs v := by
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    rw [symDerives_varG h] at hd
    obtain ⟨-, p, hp, hpd⟩ := hd
    simp only [wrapProds, List.mem_singleton] at hp
    subst hp
    obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, heval, hl⟩ := hpd
    rw [evalArgs_nil_iff] at hargs
    subst hargs
    have hρ₀ : ρ₀ = VarEnv.empty := by
      have hb : (some VarEnv.empty : Option VarEnv) = some ρ₀ := hbp
      exact (Option.some_inj.mp hb).symm
    subst hρ₀
    replace hbody : SymDerives env VarEnv.empty
        (.attrG (.varE "<implicit-prod-result>") (.varG gx [.expA arg])) bs l₀ ρ₁ := hbody
    rw [symDerives_attrG] at hbody
    obtain ⟨w, ρa, hinner, -, hm⟩ := hbody
    have hρa : ρa = VarEnv.empty := ((symDerives_varG hg).mp hinner).1
    subst hρa
    have hρ₁ : ρ₁ = VarEnv.empty.bindVal "<implicit-prod-result>" w :=
      MatchExp.unique hm (matchExp_varE_of_none rfl)
    subst hρ₁
    rw [premsHold_nil_iff] at hprems
    subst hprems
    have hvv : v' = w := EvalExp.unique heval (evalExp_varE_iff.mpr rfl)
    have : v = w := by simpa [hvv] using hl
    exact this ▸ gramRelSup_iff.mpr ⟨VarEnv.empty, hinner⟩
  · intro hd
    obtain ⟨ρa, hinner⟩ := gramRelSup_iff.mp hd
    have hρa : ρa = VarEnv.empty := ((symDerives_varG hg).mp hinner).1
    subst hρa
    refine gramRelSup_iff.mpr ⟨ρ, (symDerives_varG h).mpr ⟨rfl, _, List.mem_singleton.mpr rfl, ?_⟩⟩
    refine ⟨[], VarEnv.empty, [v], VarEnv.empty.bindVal "<implicit-prod-result>" v,
      VarEnv.empty.bindVal "<implicit-prod-result>" v, v,
      evalArgs_nil env ρ, rfl, ?_, premsHold_nil .., evalExp_varE_iff.mpr rfl, rfl⟩
    exact symDerives_attrG.mpr ⟨v, VarEnv.empty, hinner, rfl, matchExp_varE_of_none rfl⟩

/-- **`Bu32` is `Silmaril.Wasm.Binary.U32`**, at the corrected script. -/
theorem bu32_iff_u32_corrected (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envCorrected ρ (.varG "Bu32" []) bs v ↔ ∃ m, U32 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff hasWrappers_corrected.bu32 hasLeb_corrected.bun ρ bs v]
  exact bun_iff_un_corrected 32 bs v VarEnv.empty

/-! ## `#654`: `Bi32`/`Bi64` and the hand-written `IN`

`5.1-binary.values.spectec:31-32` reads `grammar Bi32 : i32 = BuN(32)`, the
*unsigned* LEB128 grammar.  `1.1-syntax.values.spectec:14-15` makes `iN(N)` an
alias of `uN(N)`, so the type checker cannot catch it, and the consequence is
that an `i32.const` immediate decodes as unsigned: `41 7F` reads as
`i32.const 127` rather than `i32.const -1`.

The hand-written side is `Silmaril.Wasm.Binary.IN`
(`Silmaril/Wasm/Binary/Basic.lean:124`), which is `SN` followed by the
two's-complement reading, and `Silmaril/Wasm/Binary/Examples.lean:368` already
records `41 7F = i32.const -1`.  The two theorems below are the formal
statement of the disagreement. -/

/-- The `iN(N)` value of a bit pattern.  `iN(N)` is an *alias* of `uN(N)`
(`specs/spectec/wasm-3.0.ast`, `(typ "iN" … (alias (var "uN" …)))`), so there
is no extra injection: the value of a `BitVec N` is the `uN(N)` value of its
natural number, which is what `$inv_signed_` computes. -/
def iNV {N : Nat} (bv : BitVec N) : Value := uNV bv.toNat

/-- An environment whose `Bi32`/`Bi64` are the **pinned**, unsigned ones. -/
structure HasPinnedBi (env : Env) : Prop where
  /-- `Bi32 = BuN(32)`, the defect of `#654`. -/
  bi32 : env.findGram? "Bi32" = some ([], .varT "i32" [],
    wrapProds (.varT "uN" [.expA (.numE (.natN 32))]) "BuN" (.numE (.natN 32)))
  /-- `Bi64 = BuN(64)`. -/
  bi64 : env.findGram? "Bi64" = some ([], .varT "i64" [],
    wrapProds (.varT "uN" [.expA (.numE (.natN 64))]) "BuN" (.numE (.natN 64)))

/-- An environment whose `Bi32`/`Bi64` are the **corrected**, signed ones. -/
structure HasCorrectedBi (env : Env) : Prop where
  /-- `Bi32 = BiN(32)`, as `#654` asks. -/
  bi32 : env.findGram? "Bi32" = some ([], .varT "i32" [],
    wrapProds (.varT "iN" [.expA (.numE (.natN 32))]) "BiN" (.numE (.natN 32)))
  /-- `Bi64 = BiN(64)`. -/
  bi64 : env.findGram? "Bi64" = some ([], .varT "i64" [],
    wrapProds (.varT "iN" [.expA (.numE (.natN 64))]) "BiN" (.numE (.natN 64)))

/-- The pinned script has the defect. -/
theorem hasPinnedBi_wasm30 : HasPinnedBi (envOfScript Specs.wasm30) :=
  ⟨findGram_bi32_pinned, findGram_bi64_pinned⟩

/-- The corrected script does not. -/
theorem hasCorrectedBi_corrected : HasCorrectedBi envCorrected :=
  ⟨findGram_bi32_corrected, findGram_bi64_corrected⟩

/-- **The pinned `Bi32` is the unsigned grammar.**  Exactly `Bu32`: the same
production, the same wrapped nonterminal, the same values. -/
theorem bi32_pinned_iff_un {env : Env} (hl : HasLeb env) (hb : HasPinnedBi env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bi32" []) bs v ↔ ∃ m, U32 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff hb.bi32 hl.bun ρ bs v]
  exact bun_iff_un hl 32 bs v VarEnv.empty

/-- The same for `Bi64`. -/
theorem bi64_pinned_iff_un {env : Env} (hl : HasLeb env) (hb : HasPinnedBi env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bi64" []) bs v ↔ ∃ m, U64 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff hb.bi64 hl.bun ρ bs v]
  exact bun_iff_un hl 64 bs v VarEnv.empty

/-- The hand-written reading of `7F` as an `i32` immediate: `-1`
(`Silmaril/Wasm/Binary/Examples.lean:368-372`). -/
theorem in32_7F : IN 32 [0x7F] (-1 : BitVec 32) := by
  have h : IN 32 [0x7F] (BitVec.ofInt 32 (((0x7F : UInt8).toNat : Int) - 2 ^ 7)) :=
    .mk (.neg 0x7F (by decide) (by decide) (by decide))
  have e : BitVec.ofInt 32 (((0x7F : UInt8).toNat : Int) - 2 ^ 7) = (-1 : BitVec 32) := by decide
  exact e ▸ h

/-- The pinned `Bi32`'s reading of `7F`: the unsigned `127`. -/
theorem bi32_pinned_7F {env : Env} (hl : HasLeb env) (hb : HasPinnedBi env) (ρ : VarEnv) :
    gramRelSup env ρ (.varG "Bi32" []) [0x7F] (uNV 127) :=
  (bi32_pinned_iff_un hl hb ρ _ _).mpr ⟨127, .byte 0x7F (by decide) (by decide), rfl⟩

/-- …and `127` is the *only* value it gives `7F`. -/
theorem bi32_pinned_7F_unique {env : Env} (hl : HasLeb env) (hb : HasPinnedBi env)
    (ρ : VarEnv) (v : Value) (h : gramRelSup env ρ (.varG "Bi32" []) [0x7F] v) :
    v = uNV 127 := by
  obtain ⟨m, hm, rfl⟩ := (bi32_pinned_iff_un hl hb ρ _ _).mp h
  have : m = 127 := UN.functional 32 hm (.byte 0x7F (by decide) (by decide))
  rw [this]

/-- **The disagreement `#654` reports, as a theorem.**  No `ρ` makes the
pinned `Bi32` agree with `Silmaril.Wasm.Binary.IN 32` through the bridge: the
byte string `7F` is given the value of `127` by the one and of `-1` — bit
pattern `0xFFFFFFFF`, hence the `uN(32)` value `4294967295` — by the other. -/
theorem bi32_pinned_disagrees_with_in {env : Env} (hl : HasLeb env) (hb : HasPinnedBi env)
    (ρ : VarEnv) :
    ¬ ∀ (bs : Grammar.Bytes) (v : Value),
        gramRelSup env ρ (.varG "Bi32" []) bs v ↔ ∃ bv : BitVec 32, IN 32 bs bv ∧ v = iNV bv := by
  intro h
  obtain ⟨bv, hbv, hv⟩ := (h [0x7F] (uNV 127)).mp (bi32_pinned_7F hl hb ρ)
  have hbv' : bv = (-1 : BitVec 32) := IN.prefixFree 32 (r := []) (r' := []) hbv in32_7F rfl |>.2
  subst hbv'
  simp only [uNV, iNV, percentV, Sem.caseV, Value.case.injEq, Value.tuple.injEq,
    Encode.toValue, List.cons.injEq, Value.num.injEq, Num.natN.injEq] at hv
  exact absurd hv.2.1 (by decide)

/-! ## `BsN`: signed LEB128

`specification/wasm-3.0/5.1-binary.values.spectec:13-16` is three productions:
one byte below `2^6`, one byte in `[2^6, 2^7)` read as negative, and a
continuation byte followed by `BsN(N-7)`.  The hand-written
`Silmaril.Wasm.Binary.SN` (`Silmaril/Wasm/Binary/Basic.lean:111`) is the same
three clauses.

**They are not the same relation**, and the reason is in the elaboration, not
in the source: see `bsn_iff_sn` and the closing section "A new finding: the
elaborated `BsN` loses negative multi-byte values" at the end of this file.
The defect is filed as `#803`.

Everything here is stated for `0 < W`, because `$(N-1)` is elaborated as
a subtraction at `int` followed by a narrowing back to `nat`
(`spectec/src/xl/num.ml:86`), which is undefined at `N = 0`, whereas Lean's
`2 ^ (N - 1)` truncates. -/

section Signed

variable {env : Env}

/-- The scope `BsN`'s third production reaches after its second factor has
bound the recursive `sN` value to `i`. -/
def bsnScopeI (W k : Nat) (w : Value) : VarEnv := (bunScopeN W k).bindVal "i" w

/-- `i` is fresh when the second factor runs. -/
theorem findVal_bunScopeN_i (W k : Nat) : (bunScopeN W k).findVal? "i" = none := rfl

/-- `N` survives the binding of `i`. -/
theorem findVal_bsnScopeI_N (W k : Nat) (w : Value) :
    (bsnScopeI W k w).findVal? "N" = some (.num (.natN W)) := rfl

/-- `n` survives the binding of `i`. -/
theorem findVal_bsnScopeI_n (W k : Nat) (w : Value) :
    (bsnScopeI W k w).findVal? "n" = some (.num (.natN k)) := rfl

/-- `i` is in scope after the second factor. -/
theorem findVal_bsnScopeI_i (W k : Nat) (w : Value) :
    (bsnScopeI W k w).findVal? "i" = some w := rfl

/-- `$(N-k)` denotes `W - k`, provided `k ≤ W`: the elaborated form subtracts
at `int` and narrows back, so it is undefined when `W < k`. -/
theorem evalExp_nSubE {ρ : VarEnv} {W k : Nat} (hW : k ≤ W)
    (hN : ρ.findVal? "N" = some (.num (.natN W))) :
    EvalExp env ρ (nSubE k) (.num (.natN (W - k))) :=
  evalExp_cvtE_num (evalExp_binE_num
    (evalExp_cvtE_num (evalExp_varE_iff.mpr hN) rfl)
    (evalExp_cvtE_num (evalExp_numE_iff.mpr rfl) rfl) rfl)
    (cvt_natT_intN (by omega) (by omega))

/-- The projection `i!%.0` of the recursive `sN` value in scope. -/
theorem evalExp_bsnProj {ρ : VarEnv} {j : Int} (hi : ρ.findVal? "i" = some (sNV j)) :
    EvalExp env ρ (.projE (.uncaseE (.varE "i") "%") 0) (.num (.intN j)) :=
  evalExp_projE_iff.mpr ⟨[.num (.intN j)],
    evalExp_uncaseE_iff.mpr (evalExp_varE_iff.mpr hi), le_refl 0, rfl⟩

/-- `boolShort` (`spectec/src/il/eval.ml:240-255`) never short-circuits an
arithmetic operator. -/
theorem boolShort_addOp (u : Value) : boolShort .addOp u = none := by cases u <;> rfl

/-- `boolShort` never short-circuits a multiplication. -/
theorem boolShort_mulOp (u : Value) : boolShort .mulOp u = none := by cases u <;> rfl

/-- `BsN`'s third production computes its value at `nat`, so a **non-negative**
recursive value gives the expected result. -/
theorem evalExp_bsnRecValue {ρ : VarEnv} {k : Nat} {j : Int}
    (hn : ρ.findVal? "n" = some (.num (.natN k))) (hi : ρ.findVal? "i" = some (sNV j))
    (hk : 2 ^ 7 ≤ k) (hj : 0 ≤ j) :
    EvalExp env ρ bsnRecValue (sNV (2 ^ 7 * j + ((k : Int) - 2 ^ 7))) := by
  have hmul : EvalExp env ρ (.binE .mulOp (.numT .natT) (twoPowE (.numE (.natN 7)))
      (i2n (.projE (.uncaseE (.varE "i") "%") 0))) (.num (.natN (2 ^ 7 * j.toNat))) :=
    evalExp_binE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl))
      (evalExp_cvtE_num (evalExp_bsnProj hi) (cvt_natT_intN hj rfl)) rfl
  have hsub : EvalExp env ρ (i2n (.binE .subOp (.numT .intT) (n2i (.varE "n"))
      (n2i (twoPowE (.numE (.natN 7)))))) (.num (.natN (k - 2 ^ 7))) :=
    evalExp_cvtE_num (evalExp_binE_num
      (evalExp_cvtE_num (evalExp_varE_iff.mpr hn) rfl)
      (evalExp_cvtE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl) rfl)
      (cvt_natT_intN (by omega) (by omega))
  refine evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_singleton ?_, rfl⟩, rfl⟩
  refine evalExp_cvtE_num (evalExp_binE_num hmul hsub rfl) ?_
  have he : Num.cvt .intT (.natN (2 ^ 7 * j.toNat + (k - 2 ^ 7)))
      = some (.intN ((2 ^ 7 * j.toNat + (k - 2 ^ 7) : Nat) : Int)) := rfl
  rw [he, Option.some.injEq, Num.intN.injEq]
  omega

/-- **The narrowing that breaks the recursion.**  `BsN`'s third production
narrows the recursive value from `int` to `nat` before multiplying, and
`Xl.Num.cvt` (`spectec/src/xl/num.ml:86`) is undefined on a negative integer,
so the production has *no* value when the recursive `sN` is negative.  This is
`#803`. -/
theorem not_evalExp_bsnRecValue {ρ : VarEnv} {j : Int} {v : Value}
    (hi : ρ.findVal? "i" = some (sNV j)) (hj : j < 0) :
    ¬ EvalExp env ρ bsnRecValue v := by
  intro h
  rw [bsnRecValue, evalExp_caseE_iff] at h
  obtain ⟨w, hw, -⟩ := h
  rw [evalExp_tupE_iff] at hw
  obtain ⟨vs, hvs, -⟩ := hw
  obtain ⟨u, -, hu, -, -⟩ := evalExps_cons_iff.mp hvs
  obtain ⟨m, m', hm, -, -⟩ := evalExp_cvtE_iff.mp hu
  obtain ⟨v₁, h₁, hcase⟩ := evalExp_binE_iff.mp hm
  rcases hcase with hs | ⟨-, -, -, -⟩
  · rw [boolShort_addOp] at hs; exact absurd hs (by simp)
  obtain ⟨v₂, h₂, hcase₂⟩ := evalExp_binE_iff.mp h₁
  rcases hcase₂ with hs | ⟨-, v₃, h₃, -⟩
  · rw [boolShort_mulOp] at hs; exact absurd hs (by simp)
  obtain ⟨m₃, m₄, hm₃, hcvt, -⟩ := evalExp_cvtE_iff.mp h₃
  have hmj : (Value.num m₃) = .num (.intN j) := EvalExp.unique hm₃ (evalExp_bsnProj hi)
  have hmj' : m₃ = .intN j := by injection hmj
  rw [hmj'] at hcvt
  have hc : Num.cvt .natT (.intN j) = none := by
    simp only [Num.cvt]
    exact ite_eq_right (fun hle => absurd hle (by omega))
  rw [hc] at hcvt
  exact absurd hcvt (by simp)

/-- `Xl.Num.bin` at `int` for subtraction. -/
theorem num_bin_sub_int (a b : Int) :
    Num.bin .subOp (.intN a) (.intN b) = some (.intN (a - b)) := rfl

/-- A power of two, cast from `nat` to `int`. -/
theorem cast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = 2 ^ k := by push_cast; rfl

/-- `cmpValues` at `geOp` on two integers (`spectec/src/il/eval.ml:256-270`). -/
theorem cmpValues_geOp_intN {a b : Int} (hab : b ≤ a) :
    cmpValues .geOp (.num (.intN a)) (.num (.intN b)) = .ok (.bool true) := by
  simp [cmpValues, Num.cmp, hab]

/-- Every `SN` encoding is non-empty. -/
theorem sn_ne_nil {W : Nat} {bs : Grammar.Bytes} {i : Int} (h : SN W bs i) : bs ≠ [] := by
  cases h <;> simp

/-- **Introduction.**  The pinned `BsN(N)` derives every `SN N` encoding whose
value is non-negative, and every single-byte one.  The side condition is
exactly what `not_evalExp_bsnRecValue` forces: a multi-byte encoding of a
negative number would need the third production to narrow a negative recursive
value to `nat`. -/
theorem bsn_of_sn {env : Env} (hl : HasLeb env) (h : HasSignedLeb env) :
    ∀ {W : Nat} {bs : Grammar.Bytes} {i : Int}, SN W bs i → 0 < W →
      (0 ≤ i ∨ bs.length = 1) →
      ∀ (ρ : VarEnv) (eN : Exp), EvalExp env ρ eN (.num (.natN W)) →
        SymDerives env ρ (.varG "BsN" [.expA eN]) bs [sNV i] ρ := by
  intro W bs i hsn
  induction hsn with
  | @pos W n h₁ h₂ =>
      intro hW _ ρ eN heN
      rw [symDerives_varG h.bsn]
      refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
      refine ⟨[.val (.num (.natN W))], bunScope W, [numCase n.toNat], bunScopeN W n.toNat,
        bunScopeN W n.toNat, sNV (n.toNat : Int), evalArgs_expA heN, rfl, ?_, ?_, ?_, rfl⟩
      · show SymDerives env (bunScope W)
          (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])) _ _ _
        rw [symDerives_attrG]
        exact ⟨numCase n.toNat, bunScope W, bbyte_derives hl _ n, rfl,
          matchExp_case_var (findVal_bunScope_n W)⟩
      · refine premsHold_ifPr (evalExp_and_true ?_ ?_)
        · exact evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat))
            (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) (by simp [cmpValues, Num.cmp, h₁])
        · exact evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat))
            (evalExp_twoPowE (evalExp_nSubE (by omega) (findVal_bunScopeN_N W n.toNat)))
            (by simp [cmpValues, Num.cmp, h₂])
      · exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_singleton
          (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat)) rfl),
          rfl⟩, rfl⟩
  | @neg W n h₁ h₂ h₃ =>
      intro hW _ ρ eN heN
      rw [symDerives_varG h.bsn]
      refine ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
      refine ⟨[.val (.num (.natN W))], bunScope W, [numCase n.toNat], bunScopeN W n.toNat,
        bunScopeN W n.toNat, sNV ((n.toNat : Int) - 2 ^ 7), evalArgs_expA heN, rfl,
        ?_, ?_, ?_, rfl⟩
      · show SymDerives env (bunScope W)
          (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])) _ _ _
        rw [symDerives_attrG]
        exact ⟨numCase n.toNat, bunScope W, bbyte_derives hl _ n, rfl,
          matchExp_case_var (findVal_bunScope_n W)⟩
      · refine premsHold_ifPr (evalExp_and_true (evalExp_and_true ?_ ?_) ?_)
        · exact evalExp_cmpE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl))
            (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat))
            (by simp [cmpValues, Num.cmp, h₁])
        · exact evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat))
            (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) (by simp [cmpValues, Num.cmp, h₂])
        · refine evalExp_cmpE_num
            (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat)) rfl)
            (evalExp_binE_num
              (evalExp_cvtE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl)
              (evalExp_cvtE_num (evalExp_twoPowE
                (evalExp_nSubE (by omega) (findVal_bunScopeN_N W n.toNat))) rfl)
              (num_bin_sub_int _ _)) ?_
          exact cmpValues_geOp_intN (by rw [cast_two_pow, cast_two_pow]; exact h₃)
      · refine evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_singleton ?_,
          rfl⟩, rfl⟩
        refine evalExp_binE_num
          (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat)) rfl)
          (evalExp_cvtE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl) ?_
        rw [num_bin_sub_int, cast_two_pow]
  | @cont W n b j h₁ h₂ rest ih =>
      intro hW hcond ρ eN heN
      have hbne : b ≠ [] := sn_ne_nil rest
      have hlen : (n :: b).length ≠ 1 := by
        cases b with
        | nil => exact absurd rfl hbne
        | cons _ _ => simp
      have hnlt : n.toNat < 256 := n.toNat_lt_size
      have hi0 : 0 ≤ (2 : Int) ^ 7 * j + ((n.toNat : Int) - 2 ^ 7) := by
        rcases hcond with hc | hc
        · exact hc
        · exact absurd hc hlen
      have hj0 : 0 ≤ j := by
        have h128 : (2 : Int) ^ 7 = 128 := by decide
        rw [h128] at hi0
        omega
      have hrec : SymDerives env (bunScopeN W n.toNat) (.varG "BsN" [.expA (nSubE 7)]) b
          [sNV j] (bunScopeN W n.toNat) :=
        ih (by omega) (Or.inl hj0) (bunScopeN W n.toNat) (nSubE 7)
          (evalExp_nSubE (by omega) (findVal_bunScopeN_N W n.toNat))
      rw [symDerives_varG h.bsn]
      refine ⟨rfl, _,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
      refine ⟨[.val (.num (.natN W))], bunScope W, [numCase n.toNat, sNV j],
        bsnScopeI W n.toNat (sNV j), bsnScopeI W n.toNat (sNV j),
        sNV (2 ^ 7 * j + ((n.toNat : Int) - 2 ^ 7)), evalArgs_expA heN, rfl, ?_, ?_, ?_, rfl⟩
      · show SymDerives env (bunScope W)
          (.seqG [ .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])],
                   .seqG [.attrG (.varE "i") (.varG "BsN" [.expA (nSubE 7)])] ]) _ _ _
        rw [symDerives_seqG_cons]
        refine ⟨[n], [numCase n.toNat], bunScopeN W n.toNat, b, [sNV j], ?_, ?_, rfl, rfl⟩
        · rw [symDerives_seqG_cons]
          refine ⟨[n], [numCase n.toNat], bunScopeN W n.toNat, [], [], ?_,
            symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
          rw [symDerives_attrG]
          exact ⟨numCase n.toNat, bunScope W, bbyte_derives hl _ n, rfl,
            matchExp_case_var (findVal_bunScope_n W)⟩
        · refine symDerives_seqG_cons.mpr ⟨b, [sNV j], bsnScopeI W n.toNat (sNV j), [], [], ?_,
            symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil b).symm,
            (List.append_nil _).symm⟩
          refine symDerives_seqG_cons.mpr ⟨b, [sNV j], bsnScopeI W n.toNat (sNV j), [], [], ?_,
            symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil b).symm,
            (List.append_nil _).symm⟩
          exact symDerives_attrG.mpr ⟨sNV j, bunScopeN W n.toNat, hrec, rfl,
            matchExp_varE_of_none (findVal_bunScopeN_i W n.toNat)⟩
      · refine premsHold_ifPr (evalExp_and_true ?_ ?_)
        · exact evalExp_cmpE_num
            (evalExp_varE_iff.mpr (findVal_bsnScopeI_n W n.toNat (sNV j)))
            (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) (by simp [cmpValues, Num.cmp, h₁])
        · exact evalExp_cmpE_num
            (evalExp_varE_iff.mpr (findVal_bsnScopeI_N W n.toNat (sNV j)))
            (evalExp_numE_iff.mpr rfl) (by simp [cmpValues, Num.cmp, h₂])
      · exact evalExp_bsnRecValue (findVal_bsnScopeI_n W n.toNat (sNV j))
          (findVal_bsnScopeI_i W n.toNat (sNV j)) h₁ hj0

/-- **Elimination.**  Every derivation of the pinned `BsN(N)` is an `SN N`
encoding, and its value is non-negative unless the encoding is a single byte. -/
theorem sn_of_bsn {env : Env} (hl : HasLeb env) (h : HasSignedLeb env) :
    ∀ (W : Nat), 0 < W → ∀ {bs : Grammar.Bytes} {v : Value} {ρ ρ' : VarEnv} {eN : Exp},
      EvalExp env ρ eN (.num (.natN W)) →
      SymDerives env ρ (.varG "BsN" [.expA eN]) bs [v] ρ' →
      ∃ i, SN W bs i ∧ (0 ≤ i ∨ bs.length = 1) ∧ v = sNV i := by
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
    intro hW bs v ρ ρ' eN heN hd
    rw [symDerives_varG h.bsn] at hd
    obtain ⟨-, p, hp, hpd⟩ := hd
    simp only [bsnProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, heval, hl'⟩ := hpd
      rw [evalArgs_expA_iff] at hargs
      obtain ⟨vA, hvA, rfl⟩ := hargs
      have hvAW : vA = Value.num (.natN W) := EvalExp.unique hvA heN
      subst hvAW
      have hρ₀ : ρ₀ = bunScope W := by
        have hb : (some (bunScope W) : Option VarEnv) = some ρ₀ := hbp
        exact (Option.some_inj.mp hb).symm
      subst hρ₀
      replace hbody : SymDerives env (bunScope W)
          (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])) bs l₀ ρ₁ := hbody
      rw [symDerives_attrG] at hbody
      obtain ⟨v₁, ρa, hbb, -, hm⟩ := hbody
      obtain ⟨b, rfl, hv₁, rfl⟩ := bbyte_elim hl hbb
      have hv₁' : v₁ = numCase b.toNat := by simpa using hv₁
      subst hv₁'
      have hρ₁ : ρ₁ = bunScopeN W b.toNat :=
        MatchExp.unique hm (matchExp_case_var (findVal_bunScope_n W))
      subst hρ₁
      rw [premsHold_ifPr_iff] at hprems
      obtain ⟨hcond, rfl⟩ := hprems
      have hc := (EvalExp.unique hcond (evalExp_and
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat))
          (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl)
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat))
          (evalExp_twoPowE (evalExp_nSubE (by omega) (findVal_bunScopeN_N W b.toNat)))
          rfl))).symm
      simp only [Value.bool.injEq, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hvv : v' = sNV (b.toNat : Int) :=
        EvalExp.unique heval (evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_,
          evalExps_singleton (evalExp_cvtE_num
            (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat)) rfl), rfl⟩, rfl⟩)
      exact ⟨(b.toNat : Int), SN.pos b hc.1 hc.2, Or.inr rfl, by simpa [hvv] using hl'⟩
    · obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, heval, hl'⟩ := hpd
      rw [evalArgs_expA_iff] at hargs
      obtain ⟨vA, hvA, rfl⟩ := hargs
      have hvAW : vA = Value.num (.natN W) := EvalExp.unique hvA heN
      subst hvAW
      have hρ₀ : ρ₀ = bunScope W := by
        have hb : (some (bunScope W) : Option VarEnv) = some ρ₀ := hbp
        exact (Option.some_inj.mp hb).symm
      subst hρ₀
      replace hbody : SymDerives env (bunScope W)
          (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])) bs l₀ ρ₁ := hbody
      rw [symDerives_attrG] at hbody
      obtain ⟨v₁, ρa, hbb, -, hm⟩ := hbody
      obtain ⟨b, rfl, hv₁, rfl⟩ := bbyte_elim hl hbb
      have hv₁' : v₁ = numCase b.toNat := by simpa using hv₁
      subst hv₁'
      have hρ₁ : ρ₁ = bunScopeN W b.toNat :=
        MatchExp.unique hm (matchExp_case_var (findVal_bunScope_n W))
      subst hρ₁
      rw [premsHold_ifPr_iff] at hprems
      obtain ⟨hcond, rfl⟩ := hprems
      have hc := (EvalExp.unique hcond (evalExp_and
        (evalExp_and
          (evalExp_cmpE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl))
            (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat)) rfl)
          (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat))
            (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl))
        (evalExp_cmpE_num
          (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat)) rfl)
          (evalExp_binE_num
            (evalExp_cvtE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl)
            (evalExp_cvtE_num (evalExp_twoPowE
              (evalExp_nSubE (by omega) (findVal_bunScopeN_N W b.toNat))) rfl)
            (num_bin_sub_int _ _)) rfl))).symm
      simp only [Value.bool.injEq, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hvv : v' = sNV ((b.toNat : Int) - 2 ^ 7) :=
        EvalExp.unique heval (evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_,
          evalExps_singleton (evalExp_binE_num
            (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat)) rfl)
            (evalExp_cvtE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl)
            (by rw [num_bin_sub_int, cast_two_pow])), rfl⟩, rfl⟩)
      refine ⟨(b.toNat : Int) - 2 ^ 7,
        SN.neg b hc.1.1 hc.1.2 ?_, Or.inr rfl, by simpa [hvv] using hl'⟩
      have h3 := hc.2
      rw [cast_two_pow, cast_two_pow] at h3
      exact h3
    · obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, heval, hl'⟩ := hpd
      rw [evalArgs_expA_iff] at hargs
      obtain ⟨vA, hvA, rfl⟩ := hargs
      have hvAW : vA = Value.num (.natN W) := EvalExp.unique hvA heN
      subst hvAW
      have hρ₀ : ρ₀ = bunScope W := by
        have hb : (some (bunScope W) : Option VarEnv) = some ρ₀ := hbp
        exact (Option.some_inj.mp hb).symm
      subst hρ₀
      replace hbody : SymDerives env (bunScope W)
          (.seqG [ .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])],
                   .seqG [.attrG (.varE "i") (.varG "BsN" [.expA (nSubE 7)])] ])
          bs l₀ ρ₁ := hbody
      rw [symDerives_seqG_cons] at hbody
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, hA, hB, rfl, rfl⟩ := hbody
      rw [symDerives_seqG_cons] at hA
      obtain ⟨b₁', l₁', σ₁', b₁'', l₁'', hA1, hA2, rfl, rfl⟩ := hA
      rw [symDerives_seqG_nil] at hA2
      obtain ⟨rfl, rfl, rfl⟩ := hA2
      rw [symDerives_attrG] at hA1
      obtain ⟨vn, ρa, hbb, -, hmn⟩ := hA1
      obtain ⟨b, rfl, hvn, rfl⟩ := bbyte_elim hl hbb
      have hvn' : vn = numCase b.toNat := by simpa using hvn
      subst hvn'
      have hσ₁ : σ₁ = bunScopeN W b.toNat :=
        MatchExp.unique hmn (matchExp_case_var (findVal_bunScope_n W))
      subst hσ₁
      rw [symDerives_seqG_cons] at hB
      obtain ⟨b₃, l₃, σ₂, b₄, l₄, hB1, hB2, rfl, rfl⟩ := hB
      rw [symDerives_seqG_nil] at hB2
      obtain ⟨rfl, rfl, rfl⟩ := hB2
      rw [symDerives_seqG_cons] at hB1
      obtain ⟨b₅, l₅, σ₃, b₆, l₆, hC1, hC2, rfl, rfl⟩ := hB1
      rw [symDerives_seqG_nil] at hC2
      obtain ⟨rfl, rfl, rfl⟩ := hC2
      rw [symDerives_attrG] at hC1
      obtain ⟨w, ρb, hrec, -, hmw⟩ := hC1
      have hρb : ρb = bunScopeN W b.toNat := ((symDerives_varG h.bsn).mp hrec).1
      subst hρb
      have hρ₁ : ρ₁ = bsnScopeI W b.toNat w :=
        MatchExp.unique hmw (matchExp_varE_of_none (findVal_bunScopeN_i W b.toNat))
      subst hρ₁
      rw [premsHold_ifPr_iff] at hprems
      obtain ⟨hcond, rfl⟩ := hprems
      have hc := (EvalExp.unique hcond (evalExp_and
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bsnScopeI_n W b.toNat w))
          (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl)
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bsnScopeI_N W b.toNat w))
          (evalExp_numE_iff.mpr rfl) rfl))).symm
      simp only [Value.bool.injEq, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hcvt : EvalExp env (bunScopeN W b.toNat) (nSubE 7) (.num (.natN (W - 7))) :=
        evalExp_nSubE (by omega) (findVal_bunScopeN_N W b.toNat)
      obtain ⟨j, hsn, -, hvm⟩ := ih (W - 7) (by omega) (by omega) hcvt hrec
      subst hvm
      have hj0 : 0 ≤ j := by
        by_contra hneg
        exact not_evalExp_bsnRecValue (findVal_bsnScopeI_i W b.toNat (sNV j))
          (by omega) heval
      have hvv : v' = sNV (2 ^ 7 * j + ((b.toNat : Int) - 2 ^ 7)) :=
        EvalExp.unique heval (evalExp_bsnRecValue (findVal_bsnScopeI_n W b.toNat (sNV j))
          (findVal_bsnScopeI_i W b.toNat (sNV j)) hc.1 hj0)
      refine ⟨2 ^ 7 * j + ((b.toNat : Int) - 2 ^ 7), ?_, Or.inl ?_, by simpa [hvv] using hl'⟩
      · simpa using SN.cont b hc.1 hc.2 hsn
      · have h128 : (2 : Int) ^ 7 = 128 := by decide
        rw [h128]
        omega

/-- **The pinned `BsN(N)` and the hand-written `SN N`, exactly.**  They agree
on single-byte encodings and on non-negative values, and *only* there: the
side condition is not an artefact of the proof but the content of
`not_evalExp_bsnRecValue`, i.e. of `#803`. -/
theorem bsn_iff_sn {env : Env} (hl : HasLeb env) (h : HasSignedLeb env) (W : Nat) (hW : 0 < W)
    (bs : Grammar.Bytes) (v : Value) (ρ : VarEnv) :
    gramRelSup env ρ (.varG "BsN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ i, SN W bs i ∧ (0 ≤ i ∨ bs.length = 1) ∧ v = sNV i := by
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    exact sn_of_bsn hl h W hW (evalExp_numE_iff.mpr rfl) hd
  · rintro ⟨i, hi, hcond, rfl⟩
    exact gramRelSup_iff.mpr ⟨ρ, bsn_of_sn hl h hi hW hcond ρ _ (evalExp_numE_iff.mpr rfl)⟩

/-- **`Bs33` is `Silmaril.Wasm.Binary.S33`, up to the same side condition.**
`Bs33 = BsN(33)` (`5.1-binary.values.spectec:29`) is what block types and heap
types are encoded with (`Silmaril/Wasm/Binary/Core/Types.lean:140`). -/
theorem bs33_iff_s33_corrected (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envCorrected ρ (.varG "Bs33" []) bs v ↔
      ∃ i, S33 bs i ∧ (0 ≤ i ∨ bs.length = 1) ∧ v = sNV i := by
  rw [wrap_rel_iff hasWrappers_corrected.bs33 hasSignedLeb_corrected.bsn ρ bs v]
  exact bsn_iff_sn hasLeb_corrected hasSignedLeb_corrected 33 (by omega) bs v VarEnv.empty

/-! ### The side condition is real: a new finding

`FF 7E` is the two-byte signed LEB128 encoding of `-129`.  The hand-written
`SN 32` accepts it; the pinned — and, since `#654` does not touch `BsN`, the
*corrected* — `BsN(32)` derives nothing from it at all, because its third
production narrows the recursive `sN` value from `int` to `nat` before using
it.  This is not in `docs/projects/spectec-divergences.md`; see the closing section. -/

/-- `FF 7E` encodes `-129` in signed LEB128. -/
theorem sn32_FF7E : SN 32 [0xFF, 0x7E] (-129) := by
  have hrest : SN 25 [0x7E] (-2) := by
    have h := SN.neg (N := 25) 0x7E (by decide) (by decide) (by decide)
    simpa using h
  have h := SN.cont (N := 32) 0xFF (by decide) (by decide) hrest
  simpa using h

/-- **The pinned and corrected `BsN(32)` derive nothing from `FF 7E`.**  This
is `#803`. -/
theorem not_bsn_FF7E {env : Env} (hl : HasLeb env) (h : HasSignedLeb env) (ρ : VarEnv)
    (v : Value) : ¬ gramRelSup env ρ (.varG "BsN" [.expA (.numE (.natN 32))]) [0xFF, 0x7E] v := by
  intro hd
  obtain ⟨i, hi, hcond, -⟩ := (bsn_iff_sn hl h 32 (by omega) _ v ρ).mp hd
  have hieq : i = -129 := SN.functional 32 hi sn32_FF7E
  rcases hcond with hc | hc
  · rw [hieq] at hc; exact absurd hc (by decide)
  · exact absurd hc (by decide)

/-- The same at the corrected wasm-3.0 script: `#654` does not fix this. -/
theorem not_bsn_FF7E_corrected (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envCorrected ρ (.varG "BsN" [.expA (.numE (.natN 32))]) [0xFF, 0x7E] v :=
  not_bsn_FF7E hasLeb_corrected hasSignedLeb_corrected ρ v

/-! ## `BiN` and the corrected `Bi32`

`grammar BiN(N) : iN(N) = i:BsN(N) => $inv_signed_(N, i)`
(`5.1-binary.values.spectec:18-19`) is the signed grammar `#654` asks `Bi32`
and `Bi64` to use.  Its *byte language* is `BsN(N)`'s, so everything
`bsn_iff_sn` says carries over — including the gap. -/

/-- A `BiN(N)` derivation contains a `BsN(N)` derivation of the same bytes. -/
theorem bsn_of_bin {env : Env} (h : HasSignedLeb env) {W : Nat} {bs : Grammar.Bytes}
    {v : Value} {ρ ρ' : VarEnv}
    (hd : SymDerives env ρ (.varG "BiN" [.expA (.numE (.natN W))]) bs [v] ρ') :
    ∃ w ρa, SymDerives env (bunScope W) (.varG "BsN" [.expA (.varE "N")]) bs [w] ρa := by
  rw [symDerives_varG h.bin] at hd
  obtain ⟨-, p, hp, hpd⟩ := hd
  simp only [binProds, List.mem_singleton] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, -, -, -⟩ := hpd
  rw [evalArgs_expA_iff] at hargs
  obtain ⟨vA, hvA, rfl⟩ := hargs
  have hvAW : vA = Value.num (.natN W) := EvalExp.unique hvA (evalExp_numE_iff.mpr rfl)
  subst hvAW
  have hρ₀ : ρ₀ = bunScope W := by
    have hb : (some (bunScope W) : Option VarEnv) = some ρ₀ := hbp
    exact (Option.some_inj.mp hb).symm
  subst hρ₀
  replace hbody : SymDerives env (bunScope W)
      (.attrG (.varE "i") (.varG "BsN" [.expA (.varE "N")])) bs l₀ ρ₁ := hbody
  rw [symDerives_attrG] at hbody
  obtain ⟨w, ρa, hinner, -, -⟩ := hbody
  exact ⟨w, ρa, hinner⟩

/-- **The corrected `BiN(32)` cannot read `FF 7E` either.**  `#654` replaces
the unsigned grammar by the signed one, but the signed one is itself incomplete
(`not_bsn_FF7E`), so the two-byte encoding of `i32.const -129` still has no
derivation. -/
theorem not_bin_FF7E {env : Env} (hl : HasLeb env) (h : HasSignedLeb env)
    (ρ ρ' : VarEnv) (v : Value) :
    ¬ SymDerives env ρ (.varG "BiN" [.expA (.numE (.natN 32))]) [0xFF, 0x7E] [v] ρ' := by
  intro hd
  obtain ⟨w, ρa, hinner⟩ := bsn_of_bin h hd
  obtain ⟨i, hi, hcond, -⟩ := sn_of_bsn hl h 32 (by omega)
    (evalExp_varE_iff.mpr (findVal_bunScope_N 32)) hinner
  have hieq : i = -129 := SN.functional 32 hi sn32_FF7E
  rcases hcond with hc | hc
  · rw [hieq] at hc; exact absurd hc (by decide)
  · exact absurd hc (by decide)

/-- The corrected `Bi32` is `BiN(32)` at the empty scope, so it cannot read
`FF 7E` either. -/
theorem not_bi32_corrected_FF7E (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envCorrected ρ (.varG "Bi32" []) [0xFF, 0x7E] v := by
  intro hd
  rw [wrap_rel_iff hasCorrectedBi_corrected.bi32 hasSignedLeb_corrected.bin ρ _ v] at hd
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
  exact not_bin_FF7E hasLeb_corrected hasSignedLeb_corrected VarEnv.empty ρ' v hd

/-- `FF 7E` is `i32.const -129` on the hand-written side. -/
theorem in32_FF7E : IN 32 [0xFF, 0x7E] (BitVec.ofInt 32 (-129)) := .mk sn32_FF7E

/-- **The correction is necessary but not sufficient.**  `#654` removes the
`127`-versus-`-1` disagreement of `bi32_pinned_disagrees_with_in`, but the
*corrected* `Bi32` still does not agree with `Silmaril.Wasm.Binary.IN 32`:
`FF 7E`, the encoding of `i32.const -129`, has no derivation at all.  The cause
is `BsN`'s elaborated third production — `#803`; see the
closing section. -/
theorem bi32_corrected_disagrees_with_in (ρ : VarEnv) :
    ¬ ∀ (bs : Grammar.Bytes) (v : Value),
        gramRelSup envCorrected ρ (.varG "Bi32" []) bs v ↔
          ∃ bv : BitVec 32, IN 32 bs bv ∧ v = iNV bv := by
  intro h
  exact not_bi32_corrected_FF7E ρ (iNV (BitVec.ofInt 32 (-129)))
    ((h [0xFF, 0x7E] _).mpr ⟨BitVec.ofInt 32 (-129), in32_FF7E, rfl⟩)

/-! ## The bridge is well typed: `Encode UInt8` lands in SpecTec's `byte`

`Sem/Bridge.lean` states the conventions and proves the closure lemmas; this
is one instance of them discharged against the pinned script, which is what
makes the convention a claim about the specification rather than a choice of
notation. -/

/-- The sole `typcase` of `syntax byte = 0x00 | ... | 0xFF`
(`specification/wasm-3.0/1.1-syntax.values.spectec:8`), as elaborated: a `%`
injection of a one-component tuple of a `nat`, with the range as a premise. -/
def byteCases : List TypCase :=
  [ .mk "%" (.tupT [.mk "i" (.numT .natT)]) []
      [ .ifPr (.binE .andOp .boolT
          (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0)))
          (.cmpE .leOp (.numT .natT) (.varE "i") (.numE (.natN 255)))) ] ]

private theorem findTyp_byte_pinned :
    (envOfScript Specs.wasm30).findTyp? "byte"
      = some ([], [.instD [] [] (.variantT byteCases)]) := rfl

private theorem findTyp_byte_corrected :
    envCorrected.findTyp? "byte" = some ([], [.instD [] [] (.variantT byteCases)]) := rfl

/-- An environment whose `byte` is the pinned one. -/
structure HasByteTyp (env : Env) : Prop where
  /-- `byte` is the pinned one. -/
  byteTyp : env.findTyp? "byte" = some ([], [.instD [] [] (.variantT byteCases)])

/-- The pinned environment. -/
theorem hasByteTyp_wasm30 : HasByteTyp (envOfScript Specs.wasm30) := ⟨findTyp_byte_pinned⟩

/-- The corrected environment: no patch touches `byte`. -/
theorem hasByteTyp_corrected : HasByteTyp envCorrected := ⟨findTyp_byte_corrected⟩

/-- A list of premises that *holds* is a list of premises that `hasTyp`
accepts (`Sem/Type.lean`'s `premsOk`, which only turns a *definite* failure
into `false`). -/
theorem premsOk_of_premsHold {env : Env} {ρ ρ' : VarEnv} {prems : List Prem}
    (h : PremsHold env ρ prems ρ') : PremsOk env ρ prems := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [premsOk, hn, Res.elimUndef_ok]⟩

/-- **The bridge's `byte` convention is sound against `Sem/Type.lean`.**  Every
`UInt8` encodes to a value of the SpecTec type `byte` — the range premise
included, which is where `UInt8`'s own bound is used. -/
theorem denotes_byte {env : Env} (h : HasByteTyp env) :
    Denotes env VarEnv.empty (.varT "byte" []) UInt8 := by
  intro b
  have hb : b.toNat ≤ 255 := by
    have h1 : b.toNat < 256 := b.toNat_lt_size
    omega
  show HasTyp env VarEnv.empty (.varT "byte" []) (.case "%" (.tuple [.num (.natN b.toNat)]))
  refine hasTyp_varT_case (σ := VarEnv.empty) rfl h.byteTyp (evalArgs_nil env VarEnv.empty)
    ⟨1, by simp [matchArgs]⟩ ?_
  refine (hasTypCase_cons_hit_iff rfl).mpr ⟨?_, ?_⟩
  · exact hasTyp_tupT_iff.mpr ⟨_, rfl, hasTypTup_cons_iff.mpr
      ⟨_, _, rfl, denotes_natT b.toNat, hasTypTup_nil_iff.mpr rfl⟩⟩
  · refine premsOk_of_premsHold (ρ' := _) (premsHold_ifPr (evalExp_and_true ?_ ?_))
    · exact evalExp_cmpE_num (evalExp_varE_iff.mpr rfl) (evalExp_numE_iff.mpr rfl)
        (by simp [cmpValues, Num.cmp])
    · exact evalExp_cmpE_num (evalExp_varE_iff.mpr rfl) (evalExp_numE_iff.mpr rfl)
        (by simp [cmpValues, Num.cmp, hb])

/-- The same at the corrected script: `Encode UInt8` is the SpecTec type
`byte` there too. -/
theorem denotes_byte_corrected : Denotes envCorrected VarEnv.empty (.varT "byte" []) UInt8 :=
  denotes_byte hasByteTyp_corrected

/-! ## What is proved, and what is not

### Proved

* `Bbyte` is `Silmaril.Wasm.Binary.Byte`, at the pinned and at the corrected
  script (`bbyte_iff_byte`, `bbyte_iff_byte_corrected`).
* `BuN(N)` is `Silmaril.Wasm.Binary.UN N` at the corrected script
  (`bun_iff_un_corrected`), and `Bu32` is `U32` (`bu32_iff_u32_corrected`),
  through the generic wrapper lemma `wrap_rel_iff`.
* `BsN(N)` is `SN N` restricted to single-byte encodings and non-negative
  values, *exactly* (`bsn_iff_sn`), hence `Bs33` and `S33`
  (`bs33_iff_s33_corrected`).
* `#654`'s disagreement, before the patch: `bi32_pinned_iff_un`,
  `bi32_pinned_disagrees_with_in`.
* `#654` is **necessary but not sufficient**: `bi32_corrected_disagrees_with_in`.
* The bridge's `byte` convention is sound against `Sem/Type.lean`: every
  `UInt8` encodes to a value of the SpecTec type `byte`, range premise
  included (`denotes_byte`, `denotes_byte_corrected`).

### Not proved

* **`$inv_signed_` is not evaluated.**  `BiN(N)`'s value expression is
  `$inv_signed_(N, i)` (`3.1-numerics.scalar.spectec:56-58`), and evaluating a
  `CallE` means unfolding `Sem/Eval.lean`'s `tryClauses`, for which there are
  no inversion lemmas yet.  So the results about `BiN` and the corrected
  `Bi32` are about their **byte language** (`bsn_of_bin`, `not_bin_FF7E`), not
  about the values they attach.  The positive statement "the corrected `Bi32`
  agrees with `IN 32` on the strings it does derive" is therefore *not* proved
  here; `bi32_corrected_disagrees_with_in` shows it could at best hold on a
  proper subset of `IN 32`.
* **`Bu64`, `Bi64` are only covered generically.**  `bun_iff_un` and
  `wrap_rel_iff` give them for free, and `bi64_pinned_iff_un` is stated, but no
  `Bu64`-specific corollary is spelled out.
* **`Bname` is not reached.**  `Bname : name = b*:Blist(Bbyte) => name -- if
  $utf8(name) = b*` (`5.1:66-67`) needs three things this file does not have:
  the `Blist` grammar (whose `IterG` with a `ListN` counter is the
  L-attributed case `Sem/Grammar.lean` handles but no worked instance
  exercises), the `$utf8` function (another `CallE`, and the one `#655`/`#656`
  patch), and `Silmaril/SpecTec/Grammar/Utf8.lean`'s headline pair.  The
  `Encode Char` instance that the statement would be phrased over is in
  `Sem/Bridge.lean` and is unused here.
* **`BfN`, `Blist` and the index grammars** are untouched.
* **Width `0`.**  Every statement about `BsN` assumes `0 < W`, because the
  elaborated `$(N-1)` narrows `-1` to `nat` and so is undefined at `N = 0`,
  whereas Lean's `2 ^ (N - 1)` truncates.  `BsN(0)` is not called by anything.

### A new finding: the elaborated `BsN` loses negative multi-byte values

`not_bsn_FF7E` is not a restatement of a known erratum.  The `.spectec`
**source** is correct: `5.1-binary.values.spectec:16` reads

```
| n:Bbyte i:BsN(($(N-7))) => $(2^7 * i + (n - 2^7))  -- if $(n >= 2^7 /\ N > 7)
```

and `2^7 * i + (n - 2^7)` is the right arithmetic.  What the *elaboration*
produces (`findGram_bsn_pinned`, checked by `rfl` against
`specs/spectec/wasm-3.0.ast`) infers that arithmetic at `nat` and therefore
narrows the recursive value first:

```
(bin mul nat (bin pow nat (num (nat 2)) (num (nat 7)))
             (cvt int nat (proj (uncase (var "i") "%") 0)))
```

`Xl.Num.cvt` is `None` on a negative integer (`spectec/src/xl/num.ml:86`, read
at the pin), and `Eval.reduce_exp`'s `CvtE` clause turns that into `Error`
(`spectec/src/il/eval.ml:484-492`), so the production has **no value** when
`i < 0` — which is `not_evalExp_bsnRecValue`, and `bsn_iff_sn` is the exact
consequence.  Every two-or-more-byte encoding of a negative number is affected:
`FF 7E` (`-129`), `80 7F` (`-128`), and so on.

Three things to be careful about before this is filed anywhere.

1. **The scope is the IL, not the prose.**  The claim is about the elaborated
   stream and about `Sem/Eval.lean`, which transcribes `il/eval.ml`.  The
   rendered specification text is generated from the EL, not from this IL, and
   is not claimed to be wrong.
2. **`BuN` is unaffected**, because its recursive value has type `uN(N-7)`,
   already a `nat`; only the signed grammar crosses the sign boundary.  That is
   presumably why `#650`'s executable transcription — which was written against
   the *source* lines `5.1:9-19` — did not see it.
3. **SpecTec's own backends were not checked.**  Whether
   `backend-interpreter` or the prose backend ever reduce this expression is
   not something this file establishes.

`#654` does not fix it: `bi32_corrected_disagrees_with_in` is the corrected
script still disagreeing with `Silmaril.Wasm.Binary.IN 32`.  The finding is
filed as `#803`, which also covers the negative float
exponents `Tfloat`/`Thexfloat` lose for the same reason. -/

end Signed

end Silmaril.SpecTec.Equiv
