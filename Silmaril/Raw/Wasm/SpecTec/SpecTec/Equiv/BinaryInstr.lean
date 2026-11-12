module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.InstrEncoding
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryValues
public import Silmaril.Wasm.Binary.Core.Instructions
-- `spectec_import` and `spectec_erratum` add their constants with `Lean.addDecl`,
-- which bypasses the `@[expose]` of the section they sit in, so the *values* of
-- `Specs.wasm30` and `Binary51.wasm30binary51` are not visible to an importing
-- module without these two lines; they are what makes the provenance `rfl`s
-- below kernel computations the kernel can actually do.
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51

/-!
# The corrected wasm-3.0 binary grammar for instructions

Phase 4, the instruction section.  `Silmaril/SpecTec/Errata/Binary51.lean`
builds the *corrected* wasm-3.0 specification as a Lean value,
`Silmaril/SpecTec/Sem/Grammar.lean` gives every `GramD` a denotation as an
`EncRel Bytes Value`, and `Silmaril/Wasm/Binary/Core/Instructions.lean` is
Silmaril's hand-written `Instr` relation for the same section.  This file
compares the two, through the `Encode` bridge of
`Silmaril/SpecTec/Sem/Bridge.lean`, following `Equiv/BinaryValues.lean` and
`Equiv/BinaryTypes.lean`.

Every citation `5.3:n` is line `n` of
`specification/wasm-3.0/5.3-binary.instructions.spectec` at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`.

## Why this file does not transcribe `Binstr`

`5.3` declares fourteen `grammar Binstr/<fragment>` pieces; the elaborator
merges them into **one** `grammar Binstr : instr` with 498 productions
(`specs/spectec/wasm-3.0.ast`).  Writing all 498 out, as `Equiv/BinaryTypes.lean`
writes out the twenty §5.2 nonterminals, is neither readable nor cheap, and a
498-way case analysis is worse.

Every one of the 498 begins with a *byte terminal*: either `(prod (num 0xNN) …)`
or `(prod … (seq (seq (num 0xNN)) …) …)`, and nothing else.  `prodLead` reads
that byte off a production, `HasBinstr.lead` is the machine-checked statement
that every production of `Binstr` has one, and `symDerives_binstr_cons` is the
consequence: a derivation from `c :: r` can only use a production in

```
binstrOps env c = (binstrProds env).filter (fun p => prodLead p == some c.toNat)
```

Each statement below therefore names an opcode, and its provenance is one
kernel `rfl` computing that filter out of the corrected script.  The filter is
*exhaustive*, so each such `rfl` certifies both that the production is there
and that there is no other one for that byte — which is what makes the results
below `iff`s and not just derivability.

## The correspondence

Every row is an **equality of relations**, proved in both directions: the byte
strings the corrected specification derives from a string beginning with that
opcode, with the values it assigns, are exactly those of the hand-written
relation, transported along `Encode.toValue`.

| opcode | SpecTec | Lean | statement |
| --- | --- | --- | --- |
| the 137 opcodes with no immediates | `Binstr` | `Core.PlainOp` | `binstr_plain` |
| `0x08` `THROW` | `0x08 x:Btagidx` | `Core.Instr` | `binstr_throw` |
| `0x0C` `BR` | `0x0C l:Blabelidx` | `Core.Instr` | `binstr_br` |
| `0x0D` `BR_IF` | `0x0D l:Blabelidx` | `Core.Instr` | `binstr_brIf` |
| `0x10` `CALL` | `0x10 x:Bfuncidx` | `Core.Instr` | `binstr_call` |
| `0x12` `RETURN_CALL` | `0x12 x:Bfuncidx` | `Core.Instr` | `binstr_returnCall` |
| `0x14` `CALL_REF` | `0x14 x:Btypeidx` | `Core.Instr` | `binstr_callRef` |
| `0x15` `RETURN_CALL_REF` | `0x15 x:Btypeidx` | `Core.Instr` | `binstr_returnCallRef` |
| `0x20` `LOCAL.GET` | `0x20 x:Blocalidx` | `Core.Instr` | `binstr_localGet` |
| `0x21` `LOCAL.SET` | `0x21 x:Blocalidx` | `Core.Instr` | `binstr_localSet` |
| `0x22` `LOCAL.TEE` | `0x22 x:Blocalidx` | `Core.Instr` | `binstr_localTee` |
| `0x23` `GLOBAL.GET` | `0x23 x:Bglobalidx` | `Core.Instr` | `binstr_globalGet` |
| `0x24` `GLOBAL.SET` | `0x24 x:Bglobalidx` | `Core.Instr` | `binstr_globalSet` |
| `0x25` `TABLE.GET` | `0x25 x:Btableidx` | `Core.Instr` | `binstr_tableGet` |
| `0x26` `TABLE.SET` | `0x26 x:Btableidx` | `Core.Instr` | `binstr_tableSet` |
| `0x3F` `MEMORY.SIZE` | `0x3F x:Bmemidx` | `Core.Instr` | `binstr_memorySize` |
| `0x40` `MEMORY.GROW` | `0x40 x:Bmemidx` | `Core.Instr` | `binstr_memoryGrow` |
| `0xD0` `REF.NULL` | `0xD0 ht:Bheaptype` | `Core.AbsHeapType` | `binstr_refNull` |
| `0xD2` `REF.FUNC` | `0xD2 x:Bfuncidx` | `Core.Instr` | `binstr_refFunc` |
| `0xD5` `BR_ON_NULL` | `0xD5 l:Blabelidx` | `Core.Instr` | `binstr_brOnNull` |
| `0xD6` `BR_ON_NON_NULL` | `0xD6 l:Blabelidx` | `Core.Instr` | `binstr_brOnNonNull` |
| — | `Bblocktype` (5.3:26-29) | `Core.BlockType` ∩ `BlockAbs` | `gramRel_bblocktype` |
| — | `Bcastop` (5.3:20-24) | `Core.CastOp` | `gramRel_bcastop_corrected` |
| — | `Bcatch` (5.3:61-65) | `Core.Catch` | `gramRel_bcatch_corrected` |
| — | `Bxidx` (5.1:72-82) | `Index` | `symDerives_idxNT` |

Two further statements are about the *language* rather than a single opcode:
`not_binstr_nil` (`Binstr` derives no empty string) and `binstrProds_length`
(it has 498 productions).

## Provenance

`HasBinstr`, `HasIdxNTs`, `HasBlocktype`, `HasCastop` and `HasCatch` list, one
field per nonterminal, what the stream contains, and
`hasBinstr_corrected`, `hasIdxNTs_corrected`, `hasBlocktype_corrected`,
`hasCastop_corrected` and `hasCatch_corrected` discharge them by `rfl` against
`Silmaril.SpecTec.IL.Binary51.wasm30binary51`.  Each opcode row adds one more
`rfl`, computing `binstrOps envC c` out of the script.  `#650` corrects
`Bi32`, `Bi64`, `$cont` and `$utf8`; of those §5.3 mentions only `Bi32` and
`Bi64`, in the four `CONST` productions, which are out of scope except for the
finding below — so every row here reads the same in the pinned script as in the
corrected one.

## Two findings carried into the instruction section

Neither is new to this file; both are consequences, at an opcode, of a defect
`Equiv/BinaryValues.lean` and `Equiv/BinaryTypes.lean` already located, and
both are stated as theorems with the hand-written encoding beside them.

* `binstr_refNull_misses_typeIdx` — `D0 00` is `ref.null (type 0)` and the
  corrected specification derives nothing from it, because `Bheaptype`'s `s33`
  production calls `$s33_to_u32`, which `3.1-numerics.scalar.spectec:7`
  declares and no clause defines.
* `binstr_i32Const_misses_FF7E` — `41 FF 7E` is `i32.const -129` and the
  corrected specification derives nothing from it, because `BsN`'s recursive
  production narrows the recursive `sN` value from `int` to `nat`
  (`spectec/src/xl/num.ml:86`) before using it, so it reads no multi-byte
  encoding of a negative number.  `#654` does not touch `BsN`.

-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv

open Silmaril.SpecTec.IL Silmaril.SpecTec.Sem Silmaril.Wasm.Binary

set_option maxRecDepth 4000000

/-! ## Reading a production's leading byte -/

/-- The leading byte terminal of a grammar symbol, in the two shapes
`print.ml` gives the right-hand side of a `Binstr` production: a bare terminal
`(num 0xNN)`, and a sequence whose first factor is `(seq (num 0xNN) …)`. -/
def symLead : IL.Sym → Option Nat
  | .numG n => some n
  | .seqG (.seqG (.numG n :: _) :: _) => some n
  | _ => none

/-- The leading byte terminal of a production. -/
def prodLead : IL.Prod → Option Nat
  | .prodD _ g _ _ => symLead g

/-- The `Binstr` productions of an environment, or `[]` if it has no `Binstr`. -/
def binstrProds (env : Env) : List IL.Prod :=
  match env.findGram? "Binstr" with
  | some (_, _, ps) => ps
  | none => []

/-- The leading byte terminal of a production, as a `UInt8`. -/
def prodLeadByte (p : IL.Prod) : Option UInt8 := (prodLead p).map UInt8.ofNat

/-- The `Binstr` productions whose leading byte terminal is `c`. -/
def binstrOps (env : Env) (c : UInt8) : List IL.Prod :=
  (binstrProds env).filter (fun p => prodLeadByte p == some c)

/-- The hypotheses every statement below is made under: `env` has a
parameterless `grammar Binstr : instr`, and every one of its productions begins
with a byte terminal.  Both are discharged by `rfl` against the corrected
script in `hasBinstr_corrected`. -/
structure HasBinstr (env : Env) : Prop where
  /-- `Binstr` is a parameterless grammar of type `instr`. -/
  find : env.findGram? "Binstr" = some ([], .varT "instr" [], binstrProds env)
  /-- Every production of `Binstr` starts with a byte terminal. -/
  lead : (binstrProds env).all (fun p => (prodLead p).any (· < 256)) = true

/-- `Subst.subst_sym` leaves a byte terminal alone. -/
theorem substSym_numG (σ : List (IL.Id × IL.Sym)) (k : Nat) :
    substSym σ (.numG k) = .numG k := rfl

/-- `Subst.subst_sym` traverses a sequence. -/
theorem substSym_seqG (σ : List (IL.Id × IL.Sym)) (gs : List IL.Sym) :
    substSym σ (.seqG gs) = .seqG (substSyms σ gs) := rfl

/-- `Subst.subst_list Subst.subst_sym`, unfolded one step. -/
theorem substSyms_cons (σ : List (IL.Id × IL.Sym)) (g : IL.Sym) (gs : List IL.Sym) :
    substSyms σ (g :: gs) = substSym σ g :: substSyms σ gs := rfl

/-- A production whose leading terminal is `n` derives only byte strings that
start with `n`. -/
theorem prodDerives_lead {env : Env} {ρ : VarEnv} {p : IL.Prod} {bs : Grammar.Bytes}
    {l : List Value} {n : Nat} (hn : prodLead p = some n) (hlt : n < 256)
    (h : ProdDerives env ρ [] [] p bs l) :
    ∃ r, bs = UInt8.ofNat n :: r := by
  obtain ⟨q, g, e, prems⟩ := p
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hs, hpr, hev, hl⟩ := h
  rw [prodLead] at hn
  unfold symLead at hn
  split at hn <;>
    first
      | · obtain rfl := Option.some.inj hn
          rw [substSym_numG, symDerives_numG hlt] at hs
          exact ⟨[], hs.1⟩
      | · obtain rfl := Option.some.inj hn
          rw [substSym_seqG, substSyms_cons, substSym_seqG, substSyms_cons, substSym_numG,
            symDerives_seqG_cons] at hs
          obtain ⟨b₁, l₁, σ, b₂, l₂, h₁, -, rfl, -⟩ := hs
          rw [symDerives_seqG_cons] at h₁
          obtain ⟨b₃, l₃, τ, b₄, l₄, h₃, -, rfl, -⟩ := h₁
          rw [symDerives_numG hlt] at h₃
          obtain ⟨rfl, -, -⟩ := h₃
          exact ⟨b₄ ++ b₂, rfl⟩
      | · simp at hn

/-- **The lead-byte filter.**  A derivation of `Binstr` from a byte string
beginning with `c` uses one of the productions whose leading terminal is `c`,
and conversely.  This is the inversion principle every row below is proved
with, and the reason each row is an `iff`. -/
theorem symDerives_binstr_cons {env : Env} (hb : HasBinstr env) {ρ ρ' : VarEnv}
    {c : UInt8} {r : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Binstr" []) (c :: r) l ρ' ↔
      ρ' = ρ ∧ ∃ p ∈ binstrOps env c, ProdDerives env ρ [] [] p (c :: r) l := by
  rw [symDerives_varG hb.find]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, p, ?_, hd⟩
    have hall := List.all_eq_true.mp hb.lead p hp
    obtain ⟨n, hn⟩ : ∃ n, prodLead p = some n := by
      cases hq : prodLead p with
      | none => rw [hq] at hall; exact absurd hall (by simp)
      | some n => exact ⟨n, rfl⟩
    rw [hn] at hall
    have hlt : n < 256 := by simpa using hall
    obtain ⟨r', hr'⟩ := prodDerives_lead hn hlt hd
    have hc : c = UInt8.ofNat n := (List.cons.inj hr').1
    refine List.mem_filter.mpr ⟨hp, ?_⟩
    simp only [prodLeadByte, hn, Option.map_some, beq_iff_eq, Option.some.injEq]
    exact hc.symm
  · rintro ⟨rfl, p, hp, hd⟩
    exact ⟨rfl, p, List.mem_of_mem_filter hp, hd⟩

/-- **`Binstr` derives no empty byte string.**  Every production begins with a
byte terminal, so the empty string is not in the language. -/
theorem not_binstr_nil {env : Env} (hb : HasBinstr env) (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup env ρ (.varG "Binstr" []) [] v := by
  intro h
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
  rw [symDerives_varG hb.find] at hd
  obtain ⟨-, p, hp, hdd⟩ := hd
  have hall := List.all_eq_true.mp hb.lead p hp
  obtain ⟨n, hn⟩ : ∃ n, prodLead p = some n := by
    cases hq : prodLead p with
    | none => rw [hq] at hall; exact absurd hall (by simp)
    | some n => exact ⟨n, rfl⟩
  rw [hn] at hall
  obtain ⟨r, hr⟩ := prodDerives_lead hn (by simpa using hall) hdd
  exact absurd hr (by simp)

/-! ## Closed value expressions

Every production of §5.3 whose opcode carries no immediate has a *closed*
value expression: a nest of `caseE`, `tupE`, `optE` and numerals.  `DenotesConst`
says such an expression denotes one value in every scope, and the combinators
below build the witness structurally. -/

/-- `e` denotes the constant `v`, in every scope. -/
def DenotesConst (env : Env) (e : Exp) (v : Value) : Prop :=
  ∀ (ρ : VarEnv) (u : Value), EvalExp env ρ e u ↔ u = v

/-- A list of expressions denotes a list of constants, in every scope. -/
def DenotesConsts (env : Env) (es : List Exp) (vs : List Value) : Prop :=
  ∀ (ρ : VarEnv) (us : List Value), EvalExps env ρ es us ↔ us = vs

/-- The empty list. -/
theorem dcsNil {env : Env} : DenotesConsts env [] [] :=
  fun _ _ => evalExps_nil_iff

/-- Cons. -/
theorem dcsCons {env : Env} {e : Exp} {v : Value} {es : List Exp} {vs : List Value}
    (h : DenotesConst env e v) (hs : DenotesConsts env es vs) :
    DenotesConsts env (e :: es) (v :: vs) := by
  intro ρ us
  rw [evalExps_cons_iff]
  constructor
  · rintro ⟨w, ws, hw, hws, rfl⟩
    rw [(h ρ w).mp hw, (hs ρ ws).mp hws]
  · rintro rfl
    exact ⟨v, vs, (h ρ v).mpr rfl, (hs ρ vs).mpr rfl, rfl⟩

/-- A tuple of constants. -/
theorem dcTup {env : Env} {es : List Exp} {vs : List Value} (h : DenotesConsts env es vs) :
    DenotesConst env (.tupE es) (.tuple vs) := by
  intro ρ u
  rw [evalExp_tupE_iff]
  constructor
  · rintro ⟨ws, hws, rfl⟩
    rw [(h ρ ws).mp hws]
  · rintro rfl
    exact ⟨vs, (h ρ vs).mpr rfl, rfl⟩

/-- The empty tuple. -/
theorem dcTup0 {env : Env} : DenotesConst env (.tupE []) (.tuple []) := dcTup dcsNil

/-- A one-component tuple. -/
theorem dcTup1 {env : Env} {e : Exp} {v : Value} (h : DenotesConst env e v) :
    DenotesConst env (.tupE [e]) (.tuple [v]) := dcTup (dcsCons h dcsNil)

/-- A two-component tuple. -/
theorem dcTup2 {env : Env} {e₁ e₂ : Exp} {v₁ v₂ : Value} (h₁ : DenotesConst env e₁ v₁)
    (h₂ : DenotesConst env e₂ v₂) :
    DenotesConst env (.tupE [e₁, e₂]) (.tuple [v₁, v₂]) :=
  dcTup (dcsCons h₁ (dcsCons h₂ dcsNil))

/-- A three-component tuple. -/
theorem dcTup3 {env : Env} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value} (h₁ : DenotesConst env e₁ v₁)
    (h₂ : DenotesConst env e₂ v₂) (h₃ : DenotesConst env e₃ v₃) :
    DenotesConst env (.tupE [e₁, e₂, e₃]) (.tuple [v₁, v₂, v₃]) :=
  dcTup (dcsCons h₁ (dcsCons h₂ (dcsCons h₃ dcsNil)))

/-- A variant case. -/
theorem dcCase {env : Env} {op : MixopS} {e : Exp} {v : Value} (h : DenotesConst env e v) :
    DenotesConst env (.caseE op e) (.case op v) := by
  intro ρ u
  rw [evalExp_caseE_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [(h ρ w).mp hw]
  · rintro rfl
    exact ⟨v, (h ρ v).mpr rfl, rfl⟩

/-- The absent option. -/
theorem dcOptNone {env : Env} : DenotesConst env (.optE none) (.opt none) :=
  fun _ _ => evalExp_optE_none_iff

/-- A present option. -/
theorem dcOptSome {env : Env} {e : Exp} {v : Value} (h : DenotesConst env e v) :
    DenotesConst env (.optE (some e)) (.opt (some v)) := by
  intro ρ u
  rw [evalExp_optE_some_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [(h ρ w).mp hw]
  · rintro rfl
    exact ⟨v, (h ρ v).mpr rfl, rfl⟩

/-- A nullary variant case, the commonest closed value expression of §5.3. -/
theorem dcNullary {env : Env} {op : MixopS} :
    DenotesConst env (.caseE op (.tupE [])) (.case op (.tuple [])) := dcCase dcTup0

/-- A natural numeral. -/
theorem dcNat {env : Env} {k : Nat} : DenotesConst env (.numE (.natN k)) (.num (.natN k)) :=
  fun _ _ => evalExp_numE_iff

/-! ## The provenance -/

/-- The corrected wasm-3.0 script of `#650`, as an
environment.  It is `Equiv.envCorrected` of `Equiv/BinaryValues.lean`. -/
noncomputable abbrev envC : Env := envCorrected

/-- **Provenance.**  The corrected wasm-3.0 script has a parameterless
`grammar Binstr : instr` and every one of its 498 productions begins with a
byte terminal; the kernel checks both against
`Silmaril.SpecTec.IL.Binary51.wasm30binary51`. -/
theorem hasBinstr_corrected : HasBinstr envC := ⟨rfl, rfl⟩

/-- **Provenance.**  `Binstr` has 498 productions.  `private` because
`Binary51.wasm30binary51` is added with `Lean.addDecl` and is therefore not
exposed to importers, exactly as in `Equiv/BinaryValues.lean`. -/
private theorem binstrProds_length : (binstrProds envC).length = 498 := by decide

/-! ## The opcodes with no immediates

`Core/Opcodes.lean`'s `PlainOp` is the hand-written table of the §5.3 rules of
the form `| 0xNN => instr`; the corrected specification has exactly 137 such
productions, and `PlainOp` has exactly 137 constructors. -/

/-- `instrV` is a variant case on every instruction `Core.PlainOp` names, so
the junk value of its default clause is never reached by `binstr_plain`. -/
theorem instrV_case {c : UInt8} {i : Wasm.Instr} (h : Core.PlainOp c i) :
    ∃ op w, instrV i = .case op w := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- A `Binstr` production consisting of a byte terminal and a closed value
expression, with no premises: the shape of all 137 plain opcodes. -/
theorem binstrByte {env : Env} (hb : HasBinstr env) {c : UInt8} {e : Exp} {w : Value}
    (hv : DenotesConst env e w)
    (hp : binstrOps env c = [.prodD [] (.numG c.toNat) e []])
    (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Binstr" []) (c :: r) v ↔ r = [] ∧ v = w := by
  have hc : UInt8.ofNat c.toNat = c := by simp
  constructor
  · intro h
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
    obtain ⟨-, p, hp', hdd⟩ := (symDerives_binstr_cons hb).mp hd
    rw [hp, List.mem_singleton] at hp'
    subst hp'
    obtain ⟨hbs, u, hu, hl⟩ := (prodDerives_byte (by simpa using c.toNat_lt)).mp hdd
    rw [hc] at hbs
    refine ⟨(List.cons.inj hbs).2, ?_⟩
    rw [(hv VarEnv.empty u).mp hu] at hl
    exact (List.cons.inj hl).1
  · rintro ⟨rfl, rfl⟩
    refine gramRelSup_iff.mpr ⟨ρ, (symDerives_binstr_cons hb).mpr ⟨rfl,
      .prodD [] (.numG c.toNat) e [], ?_, ?_⟩⟩
    · rw [hp]; exact List.mem_singleton.mpr rfl
    · refine (prodDerives_byte (by simpa using c.toNat_lt)).mpr ⟨by rw [hc], v, ?_, rfl⟩
      exact (hv VarEnv.empty v).mpr rfl

set_option maxHeartbeats 4000000 in
/-- **The 137 opcodes with no immediates.**  For every `(c, i)` in
`Core.PlainOp`, the corrected specification's `Binstr` derives from a byte
string beginning with `c` exactly when that string is `[c]`, and the value it
gives it is `instrV i`.  Each case is certified against the stream by a kernel
`rfl` computing `binstrOps envC c`, which is exhaustive, so this is an `iff`
and not merely derivability. -/
theorem binstr_plain {c : UInt8} {i : Wasm.Instr} (hop : Core.PlainOp c i) (ρ : VarEnv)
    (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (c :: r) v ↔ r = [] ∧ v = instrV i := by
  have hb := hasBinstr_corrected
  cases hop
  case rx00 => exact binstrByte hb dcNullary rfl ρ r v
  case rx01 => exact binstrByte hb dcNullary rfl ρ r v
  case rx1A => exact binstrByte hb dcNullary rfl ρ r v
  case rx1B => exact binstrByte hb (dcCase (dcOptNone)) rfl ρ r v
  case rx0A => exact binstrByte hb dcNullary rfl ρ r v
  case rx0F => exact binstrByte hb dcNullary rfl ρ r v
  case rxD1 => exact binstrByte hb dcNullary rfl ρ r v
  case rxD3 => exact binstrByte hb dcNullary rfl ρ r v
  case rxD4 => exact binstrByte hb dcNullary rfl ρ r v
  case rx45 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx46 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx47 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx48 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx49 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx4A => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx4B => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx4C => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx4D => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx4E => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx4F => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx50 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx51 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx52 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx53 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx54 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx55 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx56 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx57 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx58 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx59 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx5A => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx5B => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx5C => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx5D => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx5E => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx5F => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx60 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx61 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx62 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx63 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx64 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx65 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx66 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx67 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx68 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx69 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx6A => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx6B => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx6C => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx6D => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx6E => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx6F => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx70 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx71 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx72 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx73 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx74 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx75 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx76 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx77 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx78 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx79 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx7A => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx7B => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxC0 =>
      exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcTup1 (dcCase (dcTup1 dcNat))))))
        rfl ρ r v
  case rxC1 =>
      exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcTup1 (dcCase (dcTup1 dcNat))))))
        rfl ρ r v
  case rxC2 =>
      exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcTup1 (dcCase (dcTup1 dcNat))))))
        rfl ρ r v
  case rxC3 =>
      exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcTup1 (dcCase (dcTup1 dcNat))))))
        rfl ρ r v
  case rxC4 =>
      exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcTup1 (dcCase (dcTup1 dcNat))))))
        rfl ρ r v
  case rx7C => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx7D => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx7E => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx7F => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx80 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx81 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx82 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx83 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx84 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx85 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx86 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx87 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx88 => exact binstrByte hb (dcCase (dcTup2 dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rx89 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx8A => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx8B => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx8C => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx8D => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx8E => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx8F => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx90 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx91 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx92 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx93 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx94 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx95 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx96 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx97 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx98 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx99 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx9A => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx9B => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx9C => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx9D => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx9E => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rx9F => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA0 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA1 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA2 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA3 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA4 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA5 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA6 => exact binstrByte hb (dcCase (dcTup2 dcNullary dcNullary)) rfl ρ r v
  case rxA7 => exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary dcNullary)) rfl ρ r v
  case rxA8 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxA9 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxAA =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxAB =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxAC =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxAD =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxAE =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxAF =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB0 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB1 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB2 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB3 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB4 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB5 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB6 => exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary dcNullary)) rfl ρ r v
  case rxB7 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB8 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxB9 =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxBA =>
      exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary (dcCase (dcNullary)))) rfl ρ r v
  case rxBB => exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary dcNullary)) rfl ρ r v
  case rxBC => exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary dcNullary)) rfl ρ r v
  case rxBD => exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary dcNullary)) rfl ρ r v
  case rxBE => exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary dcNullary)) rfl ρ r v
  case rxBF => exact binstrByte hb (dcCase (dcTup3 dcNullary dcNullary dcNullary)) rfl ρ r v


/-! ## The opcodes with one index immediate

`5.1-binary.values.spectec:72-82` declares eleven index nonterminals, all of
the shape `grammar BX : t = y:Bu32 => y`.  `Btypeidx` (`:72`) belongs to
`HasBinTypes`, so `HasIdxNTs` below carries the remaining ten.  §5.3 uses them
for the opcodes
`0x08`, `0x0C`, `0x0D`, `0x10`, `0x12`, `0x14`, `0x15`, `0x20`-`0x26`, `0x3F`,
`0x40`, `0xD2`, `0xD5` and `0xD6`. -/

/-- Looking a binding up right after making it. -/
theorem findVal_bindVal_self {ρ : VarEnv} {y : IL.Id} (hy : y ≠ "_") (w : Value) :
    (ρ.bindVal y w).findVal? y = some w := Map.find?_bind_self _ hy w

/-- The sole production of an index nonterminal `grammar BX : t = y:Bu32 => y`
(`5.1-binary.values.spectec:72-82`), as elaborated. -/
def idxProds (y : IL.Id) (t : Typ) : List IL.Prod :=
  [.prodD [.expP y t] (.attrG (.varE y) (.varG "Bu32" [])) (.varE y) []]

/-- **An index nonterminal is `Silmaril.Wasm.Binary.Index`.**  The generic form
of `Equiv/BinaryTypes.lean`'s `symDerives_btypeidx`. -/
theorem symDerives_idxNT {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    {x y : IL.Id} {t t' : Typ} (hy : y ≠ "_")
    (hg : env.findGram? x = some ([], t, idxProds y t'))
    {k : Wasm.IndexKind} {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG x []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ z : Wasm.Idx k, Index bs z ∧ l = [Encode.toValue z] := by
  rw [symDerives_wrapper rfl rfl (findVal_bindVal_self hy)
    (fun _ _ _ _ hd => ((symDerives_varG h.bu32).mp hd).1) hg]
  constructor
  · rintro ⟨rfl, w, hw, rfl⟩
    obtain ⟨-, m, hm, hl'⟩ := (symDerives_bu32 h hl).mp hw
    exact ⟨rfl, ⟨⟨m, UN.lt_two_pow hm⟩⟩, hm, hl'⟩
  · rintro ⟨rfl, z, hz, rfl⟩
    exact ⟨rfl, _, (symDerives_bu32 h hl).mpr ⟨rfl, z.toNat, hz, rfl⟩, rfl⟩

/-- The ten index nonterminals of `5.1-binary.values.spectec:73-82`, as the
corrected script has them — the eleventh, `Btypeidx` (`:72`), is a field of
`HasBinTypes` instead.  One structure, so that the kernel computes
`envC.findGram?` once for all ten. -/
structure HasIdxNTs (env : Env) : Prop where
  /-- `grammar Btagidx : tagidx = x:Bu32 => x` (`5.1:73`). -/
  btagidx : env.findGram? "Btagidx" = some ([], .varT "tagidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Bglobalidx : globalidx = x:Bu32 => x` (`5.1:74`). -/
  bglobalidx : env.findGram? "Bglobalidx"
    = some ([], .varT "globalidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Bmemidx : memidx = x:Bu32 => x` (`5.1:75`). -/
  bmemidx : env.findGram? "Bmemidx" = some ([], .varT "memidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Btableidx : tableidx = x:Bu32 => x` (`5.1:76`). -/
  btableidx : env.findGram? "Btableidx"
    = some ([], .varT "tableidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Bfuncidx : funcidx = x:Bu32 => x` (`5.1:77`). -/
  bfuncidx : env.findGram? "Bfuncidx" = some ([], .varT "funcidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Bdataidx : dataidx = x:Bu32 => x` (`5.1:78`). -/
  bdataidx : env.findGram? "Bdataidx" = some ([], .varT "dataidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Belemidx : elemidx = x:Bu32 => x` (`5.1:79`). -/
  belemidx : env.findGram? "Belemidx" = some ([], .varT "elemidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Blocalidx : localidx = x:Bu32 => x` (`5.1:80`). -/
  blocalidx : env.findGram? "Blocalidx"
    = some ([], .varT "localidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Bfieldidx : fieldidx = x:Bu32 => x` (`5.1:81`). -/
  bfieldidx : env.findGram? "Bfieldidx"
    = some ([], .varT "fieldidx" [], idxProds "x" (.varT "idx" []))
  /-- `grammar Blabelidx : labelidx = l:Bu32 => l` (`5.1:82`), the one that
  binds `l` rather than `x`. -/
  blabelidx : env.findGram? "Blabelidx"
    = some ([], .varT "labelidx" [], idxProds "l" (.varT "labelidx" []))

/-- **Provenance.**  The corrected wasm-3.0 script's index nonterminals. -/
theorem hasIdxNTs_corrected : HasIdxNTs envC :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `HasBinTypes` at the corrected script, under this file's abbreviation. -/
theorem hasBinTypes_corrected : HasBinTypes envC := hasBinTypes_wasm30binary51

/-- `HasLeb` at the corrected script, under this file's abbreviation. -/
theorem hasLebC : HasLeb envC := hasLeb_wasm30binary51

/-- **A `Binstr` production `0xNN y:BX => ve`.**  The byte string is the opcode
followed by whatever `BX` derives; the value expression `ve` is closed but for
`y`, and `wrap` is what it makes of `y`'s value.  `hchar` is the
characterisation of `BX` the row is relative to: one of
`Equiv/BinaryTypes.lean`'s `symDerives_*` lemmas, or `symDerives_idxNT`. -/
theorem binstrWrap {env : Env} (hb : HasBinstr env) {c : UInt8} {g y : IL.Id}
    {q : List Param} {ve : Exp} {wrap : Value → Value} {α : Type} [Encode α]
    {P : Grammar.Bytes → α → Prop} (hy : y ≠ "_")
    (hve : ∀ (τ : VarEnv) (w u : Value), τ.findVal? y = some w →
      (EvalExp env τ ve u ↔ u = wrap w))
    (hchar : ∀ (τ τ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG g []) b ws τ' ↔
        τ' = τ ∧ ∃ a : α, P b a ∧ ws = [Encode.toValue a])
    (hp : binstrOps env c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]]) ve []])
    (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ a : α, P r a ∧ v = wrap (Encode.toValue a) := by
  have hc : UInt8.ofNat c.toNat = c := by simp
  have hnt : ∀ (τ τ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG g []) b ws τ' → τ' = τ :=
    fun τ τ' b ws hd => ((hchar τ τ' b ws).mp hd).1
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    obtain ⟨-, p, hp', hdd⟩ := (symDerives_binstr_cons hb).mp hd
    rw [hp, List.mem_singleton] at hp'
    subst hp'
    obtain ⟨l₀, σ, u, hs, hev, hlv⟩ := (prodDerives_simple rfl).mp hdd
    obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, hbs, rfl⟩ := symDerives_seqG_pair.mp hs
    obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by simpa using c.toNat_lt)).mp h₁
    obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hnt).mp h₂
    obtain ⟨-, a, ha, hlw⟩ := (hchar _ _ _ _).mp hw
    have hw' : w = Encode.toValue a := by simpa using hlw
    subst hw'
    rw [matchExp_varE_of_none_iff rfl] at hm
    subst hm
    rw [hve _ _ _ (findVal_bindVal_self hy _)] at hev
    subst hev
    rw [hc] at hbs
    obtain rfl : r = b₂ := (List.cons.inj hbs).2
    exact ⟨a, ha, (List.cons.inj hlv).1⟩
  · rintro ⟨a, ha, rfl⟩
    refine gramRelSup_iff.mpr ⟨ρ, (symDerives_binstr_cons hb).mpr ⟨rfl,
      .prodD q (.seqG [.seqG [.numG c.toNat],
        .seqG [.attrG (.varE y) (.varG g [])]]) ve [], ?_, ?_⟩⟩
    · rw [hp]; exact List.mem_singleton.mpr rfl
    · refine (prodDerives_simple rfl).mpr ⟨_, _, _, symDerives_seqG_pair.mpr
        ⟨_, _, VarEnv.empty, _, _,
          (symDerives_byteFactor (by simpa using c.toNat_lt)).mpr ⟨rfl, rfl, rfl⟩,
          (symDerives_attrNT hnt).mpr ⟨Encode.toValue a,
            (hchar _ _ _ _).mpr ⟨rfl, a, ha, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩, by rw [hc]; rfl, rfl⟩, ?_, rfl⟩
      exact (hve _ _ _ (findVal_bindVal_self hy _)).mpr rfl

/-- The value expression `OP y` denotes the mixop applied to `y`'s value. -/
theorem evalExp_caseVar {env : Env} {op : MixopS} {y : IL.Id} (τ : VarEnv) (w u : Value)
    (h : τ.findVal? y = some w) : EvalExp env τ (.caseE op (.varE y)) u ↔ u = .case op w := by
  rw [evalExp_caseE_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [evalExp_varE_iff, h, Option.some.injEq] at hz
    rw [hz]
  · rintro rfl
    exact ⟨w, evalExp_varE_iff.mpr h, rfl⟩

/-- The value expression `OP (OP' y)`, which is how `5.3:50-51` injects a
`typeidx` into a `typeuse`. -/
theorem evalExp_caseCaseVar {env : Env} {op op' : MixopS} {y : IL.Id} (τ : VarEnv)
    (w u : Value) (h : τ.findVal? y = some w) :
    EvalExp env τ (.caseE op (.caseE op' (.varE y))) u ↔ u = .case op (.case op' w) := by
  rw [evalExp_caseE_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [evalExp_caseVar τ w z h] at hz
    rw [hz]
  · rintro rfl
    exact ⟨_, (evalExp_caseVar τ w _ h).mpr rfl, rfl⟩

/-- **A `Binstr` production `0xNN y:BX => OP y`.** -/
theorem binstrOne {env : Env} (hb : HasBinstr env) {c : UInt8} {op : MixopS} {g y : IL.Id}
    {q : List Param} {α : Type} [Encode α] {P : Grammar.Bytes → α → Prop}
    (hy : y ≠ "_")
    (hchar : ∀ (τ τ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG g []) b ws τ' ↔
        τ' = τ ∧ ∃ a : α, P b a ∧ ws = [Encode.toValue a])
    (hp : binstrOps env c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]])
      (.caseE op (.varE y)) []])
    (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ a : α, P r a ∧ v = .case op (Encode.toValue a) :=
  binstrWrap hb hy evalExp_caseVar hchar hp ρ r v

/-- **A `Binstr` production `0xNN y:BX => OP (OP' y)`.** -/
theorem binstrOneCase {env : Env} (hb : HasBinstr env) {c : UInt8} {op op' : MixopS}
    {g y : IL.Id} {q : List Param} {α : Type} [Encode α] {P : Grammar.Bytes → α → Prop}
    (hy : y ≠ "_")
    (hchar : ∀ (τ τ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG g []) b ws τ' ↔
        τ' = τ ∧ ∃ a : α, P b a ∧ ws = [Encode.toValue a])
    (hp : binstrOps env c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]])
      (.caseE op (.caseE op' (.varE y))) []])
    (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ a : α, P r a ∧ v = .case op (.case op' (Encode.toValue a)) :=
  binstrWrap hb hy evalExp_caseCaseVar hchar hp ρ r v

/-- **A `Binstr` production `0xNN y:BX => OP y` for an index nonterminal.** -/
theorem binstrIdx {env : Env} (hb : HasBinstr env) (h : HasBinTypes env) (hl : HasLeb env)
    {c : UInt8} {op : MixopS} {g y : IL.Id} {t t' : Typ} {q : List Param}
    (hy : y ≠ "_") (hg : env.findGram? g = some ([], t, idxProds y t'))
    (hp : binstrOps env c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]])
      (.caseE op (.varE y)) []])
    {k : Wasm.IndexKind} (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ z : Wasm.Idx k, Index r z ∧ v = .case op (Encode.toValue z) :=
  binstrOne hb hy (fun _ _ _ _ => symDerives_idxNT h hl hy hg) hp ρ r v


/-! ### The rows

`Core/Instructions.lean`'s `Instr.inv` inverts the hand-written relation on its
first byte through `Core.Dispatch.KSpec`, and for every opcode here that
`KSpec` is literally `Core.One Index f`.  `instr_one` is the two-line bridge,
and `binstrIdxRow` puts the two halves together. -/

/-- An opcode whose hand-written shape is one immediate: `Core.Instr` at that
opcode is exactly `G` followed by the constructor. -/
theorem instr_one {F : Core.Forms} {c : UInt8} {α : Type} {G : Grammar.Bytes → α → Prop}
    {f : α → Wasm.Instr}
    (hk : Core.Dispatch.KSpec F (Core.Dispatch.kind c) c = Core.Dispatch.One G f)
    (hmk : ∀ {b : Grammar.Bytes} {z : α}, G b z → Core.Instr F (c :: b) (f z))
    (b : Grammar.Bytes) (j : Wasm.Instr) :
    Core.Instr F (c :: b) j ↔ ∃ z, G b z ∧ j = f z := by
  constructor
  · intro hj
    have h := hj.inv (c := c) (rest := b) rfl
    rw [hk] at h
    exact h
  · rintro ⟨z, hz, rfl⟩
    exact hmk hz

/-- **One row of the index table.**  The corrected specification and the
hand-written `Core.Instr` agree, as relations, on every byte string starting
with the opcode `c`. -/
theorem binstrIdxRow {env : Env} (hb : HasBinstr env) (h : HasBinTypes env) (hl : HasLeb env)
    {c : UInt8} {op : MixopS} {g y : IL.Id} {t t' : Typ} {q : List Param}
    (hy : y ≠ "_") (hg : env.findGram? g = some ([], t, idxProds y t'))
    (hp : binstrOps env c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]])
      (.caseE op (.varE y)) []])
    {k : Wasm.IndexKind} {f : Wasm.Idx k → Wasm.Instr}
    (hinv : ∀ (b : Grammar.Bytes) (j : Wasm.Instr),
      Core.Instr Core.Forms.all (c :: b) j ↔ ∃ z, Index b z ∧ j = f z)
    (hval : ∀ z : Wasm.Idx k, instrV (f z) = .case op (Encode.toValue z))
    (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (c :: r) i ∧ v = instrV i := by
  rw [binstrIdx hb h hl hy hg hp (k := k) ρ r v]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨f z, (hinv r (f z)).mpr ⟨z, hz, rfl⟩, (hval z).symm⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (hinv r j).mp hj
    exact ⟨z, hz, hval z⟩

/-- An index row at the corrected script, with the three environment
hypotheses already supplied. -/
theorem binstrIdxRowC {c : UInt8} {op : MixopS} {g y : IL.Id} {t t' : Typ} {q : List Param}
    (hy : y ≠ "_") (hg : envC.findGram? g = some ([], t, idxProds y t'))
    (hp : binstrOps envC c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]])
      (.caseE op (.varE y)) []])
    {k : Wasm.IndexKind} {f : Wasm.Idx k → Wasm.Instr}
    (hinv : ∀ (b : Grammar.Bytes) (j : Wasm.Instr),
      Core.Instr Core.Forms.all (c :: b) j ↔ ∃ z, Index b z ∧ j = f z)
    (hval : ∀ z : Wasm.Idx k, instrV (f z) = .case op (Encode.toValue z))
    (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (c :: r) i ∧ v = instrV i :=
  binstrIdxRow hasBinstr_corrected hasBinTypes_corrected hasLebC hy hg hp hinv hval ρ r v

/-- `0x08 x:Btagidx => THROW x` (5.3:40). -/
theorem binstr_throw (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x08 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x08 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.btagidx rfl
    (instr_one rfl fun hz => .throw hz) (fun _ => rfl) ρ r v

/-- `0x0C l:Blabelidx => BR l` (5.3:42). -/
theorem binstr_br (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x0C :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x0C :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.blabelidx rfl
    (instr_one rfl fun hz => .br hz) (fun _ => rfl) ρ r v

/-- `0x0D l:Blabelidx => BR_IF l` (5.3:43). -/
theorem binstr_brIf (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x0D :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x0D :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.blabelidx rfl
    (instr_one rfl fun hz => .brIf hz) (fun _ => rfl) ρ r v

/-- `0x10 x:Bfuncidx => CALL x` (5.3:46). -/
theorem binstr_call (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x10 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x10 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.bfuncidx rfl
    (instr_one rfl fun hz => .call hz) (fun _ => rfl) ρ r v

/-- `0x12 x:Bfuncidx => RETURN_CALL x` (5.3:48). -/
theorem binstr_returnCall (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x12 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x12 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.bfuncidx rfl
    (instr_one rfl fun hz => .returnCall hz) (fun _ => rfl) ρ r v

/-- `0x20 x:Blocalidx => LOCAL.GET x` (5.3:71). -/
theorem binstr_localGet (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x20 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x20 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.blocalidx rfl
    (instr_one rfl fun hz => .localGet hz) (fun _ => rfl) ρ r v

/-- `0x21 x:Blocalidx => LOCAL.SET x` (5.3:72). -/
theorem binstr_localSet (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x21 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x21 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.blocalidx rfl
    (instr_one rfl fun hz => .localSet hz) (fun _ => rfl) ρ r v

/-- `0x22 x:Blocalidx => LOCAL.TEE x` (5.3:73). -/
theorem binstr_localTee (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x22 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x22 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.blocalidx rfl
    (instr_one rfl fun hz => .localTee hz) (fun _ => rfl) ρ r v

/-- `0x23 x:Bglobalidx => GLOBAL.GET x` (5.3:77). -/
theorem binstr_globalGet (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x23 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x23 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.bglobalidx rfl
    (instr_one rfl fun hz => .globalGet hz) (fun _ => rfl) ρ r v

/-- `0x24 x:Bglobalidx => GLOBAL.SET x` (5.3:78). -/
theorem binstr_globalSet (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x24 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x24 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.bglobalidx rfl
    (instr_one rfl fun hz => .globalSet hz) (fun _ => rfl) ρ r v

/-- `0x25 x:Btableidx => TABLE.GET x` (5.3:85). -/
theorem binstr_tableGet (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x25 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x25 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.btableidx rfl
    (instr_one rfl fun hz => .tableGet hz) (fun _ => rfl) ρ r v

/-- `0x26 x:Btableidx => TABLE.SET x` (5.3:86). -/
theorem binstr_tableSet (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x26 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x26 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.btableidx rfl
    (instr_one rfl fun hz => .tableSet hz) (fun _ => rfl) ρ r v

/-- `0xD2 x:Bfuncidx => REF.FUNC x` (5.3:142). -/
theorem binstr_refFunc (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0xD2 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0xD2 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.bfuncidx rfl
    (instr_one rfl fun hz => .refFunc hz) (fun _ => rfl) ρ r v

/-- `0xD5 l:Blabelidx => BR_ON_NULL l` (5.3:53). -/
theorem binstr_brOnNull (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0xD5 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0xD5 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.blabelidx rfl
    (instr_one rfl fun hz => .brOnNull hz) (fun _ => rfl) ρ r v

/-- `0xD6 l:Blabelidx => BR_ON_NON_NULL l` (5.3:54). -/
theorem binstr_brOnNonNull (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0xD6 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0xD6 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.blabelidx rfl
    (instr_one rfl fun hz => .brOnNonNull hz) (fun _ => rfl) ρ r v

/-- The memory index of `memory.size` and `memory.grow` is `Bu32` in Core 3.0,
and `Core.ReservedIdx true` is `Index` (`Core/Instructions.lean`'s
`ReservedIdx.true_iff`), so the two sides still line up at `Forms.all`. -/
theorem instr_reservedIdx {c : UInt8} {k : Wasm.IndexKind} {f : Wasm.Idx k → Wasm.Instr}
    (hk : Core.Dispatch.KSpec Core.Forms.all (Core.Dispatch.kind c) c
      = Core.Dispatch.One (Core.ReservedIdx true) f)
    (hmk : ∀ {b : Grammar.Bytes} {z : Wasm.Idx k}, Core.ReservedIdx true b z →
      Core.Instr Core.Forms.all (c :: b) (f z))
    (b : Grammar.Bytes) (j : Wasm.Instr) :
    Core.Instr Core.Forms.all (c :: b) j ↔ ∃ z, Index b z ∧ j = f z := by
  rw [instr_one hk hmk b j]
  exact exists_congr fun z => and_congr_left' (Core.ReservedIdx.true_iff b z)

/-- `0x3F x:Bmemidx => MEMORY.SIZE x` (5.3:128). -/
theorem binstr_memorySize (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x3F :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x3F :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.bmemidx rfl
    (instr_reservedIdx rfl fun hz => .memorySize hz) (fun _ => rfl) ρ r v

/-- `0x40 x:Bmemidx => MEMORY.GROW x` (5.3:129). -/
theorem binstr_memoryGrow (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x40 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x40 :: r) i ∧ v = instrV i :=
  binstrIdxRowC (by decide) hasIdxNTs_corrected.bmemidx rfl
    (instr_reservedIdx rfl fun hz => .memoryGrow hz) (fun _ => rfl) ρ r v


/-! ### `call_ref` and `return_call_ref`

`5.3:50-51` inject the `typeidx` into a `typeuse` with `_IDX`, so the value is
one `case` deeper than the rows above. -/

/-- An index row whose value expression wraps the index in `_IDX`. -/
theorem binstrIdxCaseRowC {c : UInt8} {op op' : MixopS} {g y : IL.Id} {t t' : Typ}
    {q : List Param}
    (hy : y ≠ "_") (hg : envC.findGram? g = some ([], t, idxProds y t'))
    (hp : binstrOps envC c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]])
      (.caseE op (.caseE op' (.varE y))) []])
    {k : Wasm.IndexKind} {f : Wasm.Idx k → Wasm.Instr}
    (hinv : ∀ (b : Grammar.Bytes) (j : Wasm.Instr),
      Core.Instr Core.Forms.all (c :: b) j ↔ ∃ z, Index b z ∧ j = f z)
    (hval : ∀ z : Wasm.Idx k, instrV (f z) = .case op (.case op' (Encode.toValue z)))
    (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (c :: r) i ∧ v = instrV i := by
  rw [binstrOneCase hasBinstr_corrected hy
    (fun _ _ _ _ => symDerives_idxNT hasBinTypes_corrected hasLebC hy hg (k := k)) hp ρ r v]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨f z, (hinv r (f z)).mpr ⟨z, hz, rfl⟩, (hval z).symm⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (hinv r j).mp hj
    exact ⟨z, hz, hval z⟩

/-- `0x14 x:Btypeidx => CALL_REF (_IDX x)` (5.3:50). -/
theorem binstr_callRef (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x14 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x14 :: r) i ∧ v = instrV i :=
  binstrIdxCaseRowC (by decide) hasBinTypes_corrected.btypeidx rfl
    (instr_one rfl fun hz => .callRef hz) (fun _ => rfl) ρ r v

/-- `0x15 x:Btypeidx => RETURN_CALL_REF (_IDX x)` (5.3:51). -/
theorem binstr_returnCallRef (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x15 :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (0x15 :: r) i ∧ v = instrV i :=
  binstrIdxCaseRowC (by decide) hasBinTypes_corrected.btypeidx rfl
    (instr_one rfl fun hz => .returnCallRef hz) (fun _ => rfl) ρ r v

/-! ### `ref.null`, and the `$s33_to_u32` finding in the instruction section

`Equiv/BinaryTypes.lean` shows that the corrected `Bheaptype` derives exactly
the twelve *abstract* heap types, because its second production calls the
clause-less `$s33_to_u32`.  `0xD0 ht:Bheaptype => REF.NULL ht` (5.3:140)
inherits the restriction. -/

/-- **`0xD0 ht:Bheaptype => REF.NULL ht` (5.3:140).**  The corrected
specification derives exactly the *abstract* heap types here. -/
theorem binstr_refNull (ρ : VarEnv) (r : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Binstr" []) (0xD0 :: r) v ↔
      ∃ ht : Wasm.AbsHeapType, Core.AbsHeapType r ht ∧
        v = instrV (.refNull (.abstract ht)) := by
  rw [binstrOne hasBinstr_corrected (by decide)
    (fun _ _ _ _ => symDerives_bheaptype hasBinTypes_corrected) rfl ρ r v]
  refine exists_congr fun ht => and_congr_right' ?_
  rw [show instrV (.refNull (.abstract ht))
    = .case "REF.NULL" (Encode.toValue (Wasm.HeapType.abstract ht)) from rfl, toValue_abstract]

/-- **The finding, in the instruction section.**  `D0 00` is
`ref.null (type 0)` for the hand-written relation and is derived by nothing in
the corrected specification: `Bheaptype`'s `s33` production calls
`$s33_to_u32`, which `3.1-numerics.scalar.spectec:7` declares and no clause
defines (`Equiv/BinaryTypes.lean`, `bheaptype_misses_typeIdx`). -/
theorem binstr_refNull_misses_typeIdx (ρ : VarEnv) :
    Core.Instr Core.Forms.all [0xD0, 0x00]
        (.refNull (.typeIdx ⟨⟨0, Nat.two_pow_pos 32⟩⟩)) ∧
      ∀ v : Value, ¬ gramRelSup envC ρ (.varG "Binstr" []) [0xD0, 0x00] v := by
  refine ⟨.refNull (.idx _ (SN.pos 0 (by decide) (by decide))), fun v hv => ?_⟩
  obtain ⟨ht, hht, -⟩ := (binstr_refNull ρ [0x00] v).mp hv
  cases hht

/-! ### `i32.const`, and the `BsN` narrowing in the instruction section

`Equiv/BinaryValues.lean` shows that the pinned — and, since `#654` does not
touch `BsN`, the corrected — `BsN(N)` derives nothing from a multi-byte
encoding of a negative number, because its third production narrows the
recursive `sN` value from `int` to `nat` before using it
(`spectec/src/xl/num.ml:86`).  `0x41 i:Bi32 => CONST I32 i` (5.3:192) inherits
that, so the corrected specification cannot decode `i32.const -129`. -/

/-- A `0xNN y:BX` production derives nothing when `BX` derives nothing. -/
theorem not_binstrOne {env : Env} (hb : HasBinstr env) {c : UInt8} {g y : IL.Id}
    {q : List Param} {ve : Exp}
    (hp : binstrOps env c = [.prodD q
      (.seqG [.seqG [.numG c.toNat], .seqG [.attrG (.varE y) (.varG g [])]]) ve []])
    {r : Grammar.Bytes}
    (hno : ∀ (τ : VarEnv) (w : Value), ¬ gramRelSup env τ (.varG g []) r w)
    (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup env ρ (.varG "Binstr" []) (c :: r) v := by
  have hc : UInt8.ofNat c.toNat = c := by simp
  intro hd
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
  obtain ⟨-, p, hp', hdd⟩ := (symDerives_binstr_cons hb).mp hd
  rw [hp, List.mem_singleton] at hp'
  subst hp'
  obtain ⟨l₀, σ, u, hs, hev, hlv⟩ := (prodDerives_simple rfl).mp hdd
  obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, hbs, rfl⟩ := symDerives_seqG_pair.mp hs
  obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by simpa using c.toNat_lt)).mp h₁
  obtain ⟨w, τ, hw, rfl, -⟩ := symDerives_attrG.mp (symDerives_seq1.mp h₂)
  rw [hc] at hbs
  obtain rfl : r = b₂ := (List.cons.inj hbs).2
  exact hno _ w (gramRelSup_iff.mpr ⟨τ, hw⟩)

/-- **The corrected specification cannot decode `i32.const -129`.**  `FF 7E`
is the two-byte signed LEB128 encoding of `-129`; `Silmaril.Wasm.Binary.IN 32`
reads it, and the corrected `Bi32 = BiN(32) = BsN(32)` derives nothing from it
(`Equiv/BinaryValues.lean`, `not_bi32_corrected_FF7E`). -/
theorem binstr_i32Const_misses_FF7E (ρ : VarEnv) :
    Core.Instr Core.Forms.all [0x41, 0xFF, 0x7E]
        (.intConst .i32 (BitVec.ofInt 32 (-129))) ∧
      ∀ v : Value, ¬ gramRelSup envC ρ (.varG "Binstr" []) [0x41, 0xFF, 0x7E] v :=
  ⟨.i32Const in32_FF7E,
    not_binstrOne hasBinstr_corrected rfl (fun τ w => not_bi32_corrected_FF7E τ w) ρ⟩


/-! ## Block types

`grammar Bblocktype : blocktype` (5.3:26-29) is three productions: the empty
result `0x40`, a single `valtype`, and a non-negative `s33` read as a type
index.  The third one is where `Equiv/BinaryValues.lean`'s `BsN` analysis and
`Equiv/BinaryTypes.lean`'s `ValAbs` restriction meet. -/

/-- A production of a parameterless grammar with a single `if` premise. -/
theorem prodDerives_ifPr {env : Env} {ρ : VarEnv} {q : List Param} {g : IL.Sym}
    {e pe : Exp} {bs : Grammar.Bytes} {l : List Value}
    (hsub : substSym (gramArgSubst [] ([] : List IL.Arg)) g = g) :
    ProdDerives env ρ [] [] (.prodD q g e [.ifPr pe]) bs l ↔
      ∃ l₀ σ v, SymDerives env VarEnv.empty g bs l₀ σ ∧ EvalExp env σ pe (.bool true) ∧
        EvalExp env σ e v ∧ l = [v] := by
  constructor
  · rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hsy, hpr, hev, hl⟩
    rw [evalArgs_nil_iff] at hw
    subst hw
    rw [bindParams] at hbp
    obtain rfl := (Option.some.inj hbp).symm
    rw [hsub] at hsy
    obtain ⟨hp, rfl⟩ := premsHold_ifPr_iff.mp hpr
    exact ⟨l₀, _, v, hsy, hp, hev, hl⟩
  · rintro ⟨l₀, σ, v, hsy, hp, hev, rfl⟩
    refine ⟨[], VarEnv.empty, l₀, σ, σ, v, evalArgs_nil env _, rfl, ?_,
      premsHold_ifPr_iff.mpr ⟨hp, rfl⟩, hev, rfl⟩
    rw [hsub]
    exact hsy

/-- `Bs33` for an arbitrary environment: the generic form of
`Equiv/BinaryValues.lean`'s `bs33_iff_s33_corrected`. -/
theorem bs33_iff_s33_gen {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env)
    (hw : HasWrappers env) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bs33" []) bs v ↔
      ∃ j, S33 bs j ∧ (0 ≤ j ∨ bs.length = 1) ∧ v = sNV j := by
  rw [wrap_rel_iff hw.bs33 hs.bsn ρ bs v]
  exact bsn_iff_sn hl hs 33 (by omega) bs v VarEnv.empty

/-- `Bs33` as a `SymDerives`, which is the form a factor of a production needs. -/
theorem symDerives_bs33 {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env)
    (hw : HasWrappers env) {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bs33" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ j, S33 bs j ∧ (0 ≤ j ∨ bs.length = 1) ∧ l = [sNV j] := by
  constructor
  · intro hd
    obtain ⟨hρ, p, -, hdd⟩ := (symDerives_varG hw.bs33).mp hd
    subst hρ
    obtain ⟨q, g, e, prems⟩ := p
    obtain ⟨-, -, -, -, -, w, -, -, -, -, -, rfl⟩ := hdd
    obtain ⟨j, hj, hc, rfl⟩ :=
      (bs33_iff_s33_gen hl hs hw _ bs w).mp (gramRelSup_iff.mpr ⟨_, hd⟩)
    exact ⟨rfl, j, hj, hc, rfl⟩
  · rintro ⟨rfl, j, hj, hc, rfl⟩
    obtain ⟨σ, hσ⟩ := gramRelSup_iff.mp
      ((bs33_iff_s33_gen hl hs hw _ bs (sNV j)).mpr ⟨j, hj, hc, rfl⟩)
    obtain rfl := ((symDerives_varG hw.bs33).mp hσ).1
    exact hσ

/-- A block type the corrected wasm-3.0 binary grammar can reach: the `valtype`
case is restricted exactly as `Equiv/BinaryTypes.lean`'s `Bvaltype` is. -/
def BlockAbs : Wasm.BlockType → Prop
  | .value t => ValAbs t
  | .empty | .typeIdx _ => True

/-- The three productions of `grammar Bblocktype : blocktype` (5.3:26-29), as
elaborated.  The third one's value expression narrows the `s33` back to a `nat`
with `cvt int nat`, which is total exactly under its own premise `i >= 0`. -/
def bblocktypeProds : List IL.Prod :=
  [ .prodD [] (.numG 0x40) (.caseE "_RESULT" (.optE none)) [],
    .prodD [.expP "t" (.varT "valtype" [])] (.attrG (.varE "t") (.varG "Bvaltype" []))
      (.caseE "_RESULT" (.optE (some (.varE "t")))) [],
    .prodD [.expP "i" (.varT "s33" [])] (.attrG (.varE "i") (.varG "Bs33" []))
      (.caseE "_IDX" (.caseE "%" (.tupE
        [.cvtE (.projE (.uncaseE (.varE "i") "%") 0) .intT .natT])))
      [.ifPr (.cmpE .geOp (.numT .intT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.cvtE (.numE (.natN 0)) .natT .intT))] ]

/-- `Bblocktype` is the pinned one. -/
structure HasBlocktype (env : Env) : Prop where
  /-- `grammar Bblocktype : blocktype` (5.3:26-29). -/
  bblocktype : env.findGram? "Bblocktype" = some ([], .varT "blocktype" [], bblocktypeProds)

/-- **Provenance.**  The corrected wasm-3.0 script's `Bblocktype`. -/
theorem hasBlocktype_corrected : HasBlocktype envC := ⟨rfl⟩

/-- `HasSignedLeb` at the corrected script, under this file's abbreviation. -/
theorem hasSignedLebC : HasSignedLeb envC := hasSignedLeb_corrected

/-- `HasWrappers` at the corrected script, under this file's abbreviation. -/
theorem hasWrappersC : HasWrappers envC := hasWrappers_corrected

/-- `cmpValues` at `>=` on two integers (`spectec/src/il/eval.ml:256-270`), as
an equation rather than an implication. -/
theorem cmpValues_geOp_int (a b : Int) :
    cmpValues .geOp (.num (.intN a)) (.num (.intN b)) = .ok (.bool (decide (b ≤ a))) := by
  simp [cmpValues, Num.cmp]

/-- `0` at `int`, as the elaborated premise spells it. -/
theorem evalExp_zeroIntCvt {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.cvtE (.numE (.natN 0)) .natT .intT) (.num (.intN 0)) :=
  evalExp_cvtE_num (evalExp_numE_iff.mpr rfl) rfl

/-- The scope `Bblocktype`'s third production reaches after its only factor. -/
def bblocktypeScope (j : Int) : VarEnv := VarEnv.empty.bindVal "i" (sNV j)

/-- `i` is in scope there. -/
theorem findVal_bblocktypeScope (j : Int) :
    (bblocktypeScope j).findVal? "i" = some (sNV j) := rfl

/-- The premise `i >= 0` holds exactly when the `s33` is non-negative. -/
theorem premise_bblocktype {env : Env} {j : Int} :
    EvalExp env (bblocktypeScope j) (.cmpE .geOp (.numT .intT)
      (.projE (.uncaseE (.varE "i") "%") 0) (.cvtE (.numE (.natN 0)) .natT .intT))
      (.bool true) ↔ 0 ≤ j := by
  constructor
  · intro hev
    have h := EvalExp.unique hev (evalExp_cmpE_num
      (evalExp_bsnProj (findVal_bblocktypeScope j)) evalExp_zeroIntCvt (cmpValues_geOp_int j 0))
    by_contra hj
    rw [show decide ((0 : Int) ≤ j) = false from by simp [hj]] at h
    exact absurd h (by simp)
  · intro hj
    exact evalExp_cmpE_num (evalExp_bsnProj (findVal_bblocktypeScope j)) evalExp_zeroIntCvt
      (by rw [cmpValues_geOp_int, show decide ((0 : Int) ≤ j) = true from by simp [hj]])

/-- The value expression of the third production, under its premise. -/
theorem value_bblocktype {env : Env} {j : Int} (hj : 0 ≤ j) :
    EvalExp env (bblocktypeScope j) (.caseE "_IDX" (.caseE "%" (.tupE
      [.cvtE (.projE (.uncaseE (.varE "i") "%") 0) .intT .natT])))
      (.case "_IDX" (numCase j.toNat)) :=
  evalExp_caseE_iff.mpr ⟨_, evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_,
    evalExps_singleton (evalExp_cvtE_num (evalExp_bsnProj (findVal_bblocktypeScope j))
      (cvt_natT_intN hj rfl)), rfl⟩, rfl⟩, rfl⟩

/-- **`Bblocktype` (5.3:26-29) is `Core.BlockType Forms.all`, restricted to
`BlockAbs`.**  The `_IDX` production is *exact*: its premise `i >= 0` is both
what makes the `cvt int nat` in its value expression total and what discharges
`Equiv/BinaryValues.lean`'s `BsN` side condition `0 ≤ i ∨ |bs| = 1`.  Only the
`valtype` production is narrowed, and only by the `$s33_to_u32` finding of
`Equiv/BinaryTypes.lean`. -/
theorem symDerives_bblocktype {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    (hs : HasSignedLeb env) (hw : HasWrappers env) (hb : HasBlocktype env)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bblocktype" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ bt : Wasm.BlockType, Core.BlockType Core.Forms.all bs bt ∧ BlockAbs bt ∧
        l = [Encode.toValue bt] := by
  have hvt : ∀ (τ τ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Bvaltype" []) b ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG h.bvaltype).mp hd).1
  rw [symDerives_varG hb.bblocktype]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bblocktypeProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · obtain ⟨rfl, u, hu, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [(dcCase dcOptNone VarEnv.empty u).mp hu]
      exact ⟨.empty, .empty, trivial, rfl⟩
    · obtain ⟨l₀, σ, u, hsy, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨w, τ, hw', rfl, hm⟩ := symDerives_attrG.mp hsy
      obtain ⟨-, t, ht, hta, hlw⟩ := (symDerives_bvaltype h).mp hw'
      have hw'' : w = Encode.toValue t := by simpa using hlw
      subst hw''
      obtain rfl := hvt _ _ _ _ hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_optE_some_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩)
      exact ⟨.value t, .value ht, hta, rfl⟩
    · obtain ⟨l₀, σ, u, hsy, hpr, hev, rfl⟩ := (prodDerives_ifPr rfl).mp hd
      obtain ⟨w, τ, hw', rfl, hm⟩ := symDerives_attrG.mp hsy
      obtain ⟨rfl, j, hj, -, hlw⟩ := (symDerives_bs33 hl hs hw).mp hw'
      have hw'' : w = sNV j := by simpa using hlw
      subst hw''
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      have hnn : 0 ≤ j := premise_bblocktype.mp hpr
      obtain rfl := EvalExp.unique hev (value_bblocktype hnn)
      have hlt : j < 2 ^ 32 := by
        have := (SN.bounds hj).2
        simpa using this
      refine ⟨.typeIdx ⟨⟨j.toNat, by omega⟩⟩, .idx _ ?_, trivial, rfl⟩
      have : ((⟨⟨j.toNat, by omega⟩⟩ : Wasm.TypeIdx).toNat : Int) = j := by
        show ((j.toNat : Nat) : Int) = j
        omega
      rw [this]
      exact hj
  · rintro ⟨rfl, bt, hbt, hta, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hbt with
    | empty =>
        exact ⟨_, List.mem_cons_self .., (prodDerives_byte (by decide)).mpr
          ⟨rfl, _, (dcCase dcOptNone VarEnv.empty _).mpr rfl, rfl⟩⟩
    | @value b t ht =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (prodDerives_simple rfl).mpr
          ⟨_, _, _, symDerives_attrG.mpr ⟨Encode.toValue t, VarEnv.empty,
            (symDerives_bvaltype h).mpr ⟨rfl, t, ht, hta, rfl⟩, rfl,
            matchExp_varE_of_none rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_optE_some_iff.mpr
          ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩
    | @idx b x hx =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_ifPr rfl).mpr
          ⟨_, _, _, symDerives_attrG.mpr ⟨sNV (x.toNat : Int), VarEnv.empty,
            (symDerives_bs33 hl hs hw).mpr ⟨rfl, (x.toNat : Int), hx, .inl (by omega), rfl⟩,
            rfl, matchExp_varE_of_none rfl⟩, premise_bblocktype.mpr (by omega), ?_, rfl⟩⟩
        have hv := value_bblocktype (env := env) (j := (x.toNat : Int)) (by omega)
        rw [show ((x.toNat : Int)).toNat = x.toNat from by omega] at hv
        exact hv

/-- **`Bblocktype` as an `EncRel`.** -/
theorem gramRel_bblocktype {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    (hs : HasSignedLeb env) (hw : HasWrappers env) (hb : HasBlocktype env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bblocktype" []) bs v ↔
      ∃ bt : Wasm.BlockType, Core.BlockType Core.Forms.all bs bt ∧ BlockAbs bt ∧
        v = Encode.toValue bt := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, bt, hbt, hta, hlw⟩ := (symDerives_bblocktype h hl hs hw hb).mp hd
    exact ⟨bt, hbt, hta, by simpa using hlw⟩
  · rintro ⟨bt, hbt, hta, rfl⟩
    exact ⟨ρ, (symDerives_bblocktype h hl hs hw hb).mpr ⟨rfl, bt, hbt, hta, rfl⟩⟩

/-- **`Bblocktype` at the corrected wasm-3.0 script.** -/
theorem gramRel_bblocktype_corrected (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Bblocktype" []) bs v ↔
      ∃ bt : Wasm.BlockType, Core.BlockType Core.Forms.all bs bt ∧ BlockAbs bt ∧
        v = Encode.toValue bt :=
  gramRel_bblocktype hasBinTypes_corrected hasLebC hasSignedLebC hasWrappersC
    hasBlocktype_corrected ρ bs v


/-! ## `Bcastop`

`syntax castop = (null?, null?)` and `grammar Bcastop : castop` (5.3:18-24) is
a four-entry byte table; `Silmaril/Wasm/Binary/Core/Instructions.lean`'s
`Core.CastOp` is the same four rules.  `br_on_cast` and `br_on_cast_fail`, the
only users, are `0xFB`-prefixed and out of scope here, so this is the
nonterminal on its own. -/

/-- The value of a `castop`: a pair of `null?` options, which
`Equiv/BinaryTypes.lean`'s `nullToValue` already encodes. -/
def castOpV (p : Bool × Bool) : Value := .tuple [nullToValue p.1, nullToValue p.2]

/-- The four productions of `grammar Bcastop : castop` (5.3:20-24). -/
def bcastopProds : List IL.Prod :=
  [ .prodD [] (.numG 0x00) (.tupE [.optE none, .optE none]) [],
    .prodD [] (.numG 0x01)
      (.tupE [.optE (some (.caseE "NULL" (.tupE []))), .optE none]) [],
    .prodD [] (.numG 0x02)
      (.tupE [.optE none, .optE (some (.caseE "NULL" (.tupE [])))]) [],
    .prodD [] (.numG 0x03)
      (.tupE [.optE (some (.caseE "NULL" (.tupE []))),
              .optE (some (.caseE "NULL" (.tupE [])))]) [] ]

/-- `Bcastop` is the pinned one. -/
structure HasCastop (env : Env) : Prop where
  /-- `grammar Bcastop : castop` (5.3:20-24). -/
  bcastop : env.findGram? "Bcastop" = some ([], .varT "castop" [], bcastopProds)

/-- **Provenance.**  The corrected wasm-3.0 script's `Bcastop`. -/
theorem hasCastop_corrected : HasCastop envC := ⟨rfl⟩

/-- **`Bcastop` (5.3:20-24) is `Silmaril.Wasm.Binary.Core.CastOp`.** -/
theorem symDerives_bcastop {env : Env} (hb : HasCastop env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bcastop" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ p : Bool × Bool, Core.CastOp bs p ∧ l = [castOpV p] := by
  rw [symDerives_varG hb.bcastop]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bcastopProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · obtain ⟨rfl, u, hu, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [(dcTup2 dcOptNone dcOptNone VarEnv.empty u).mp hu]
      exact ⟨(false, false), .r00, rfl⟩
    · obtain ⟨rfl, u, hu, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [(dcTup2 (dcOptSome dcNullary) dcOptNone VarEnv.empty u).mp hu]
      exact ⟨(true, false), .r01, rfl⟩
    · obtain ⟨rfl, u, hu, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [(dcTup2 dcOptNone (dcOptSome dcNullary) VarEnv.empty u).mp hu]
      exact ⟨(false, true), .r02, rfl⟩
    · obtain ⟨rfl, u, hu, rfl⟩ := (prodDerives_byte (by decide)).mp hd
      rw [(dcTup2 (dcOptSome dcNullary) (dcOptSome dcNullary) VarEnv.empty u).mp hu]
      exact ⟨(true, true), .r03, rfl⟩
  · rintro ⟨rfl, p, hcp, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hcp with
    | r00 => exact ⟨_, List.mem_cons_self .., (prodDerives_byte (by decide)).mpr
        ⟨rfl, _, (dcTup2 dcOptNone dcOptNone VarEnv.empty _).mpr rfl, rfl⟩⟩
    | r01 => exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        (prodDerives_byte (by decide)).mpr ⟨rfl, _,
          (dcTup2 (dcOptSome dcNullary) dcOptNone VarEnv.empty _).mpr rfl, rfl⟩⟩
    | r02 => exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        (prodDerives_byte (by decide)).mpr ⟨rfl, _,
          (dcTup2 dcOptNone (dcOptSome dcNullary) VarEnv.empty _).mpr rfl, rfl⟩⟩
    | r03 => exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        (prodDerives_byte (by decide)).mpr ⟨rfl, _,
          (dcTup2 (dcOptSome dcNullary) (dcOptSome dcNullary) VarEnv.empty _).mpr rfl, rfl⟩⟩

/-- **`Bcastop` as an `EncRel`, at the corrected wasm-3.0 script.** -/
theorem gramRel_bcastop_corrected (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Bcastop" []) bs v ↔
      ∃ p : Bool × Bool, Core.CastOp bs p ∧ v = castOpV p := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, p, hcp, hlw⟩ := (symDerives_bcastop hasCastop_corrected).mp hd
    exact ⟨p, hcp, by simpa using hlw⟩
  · rintro ⟨p, hcp, rfl⟩
    exact ⟨ρ, (symDerives_bcastop hasCastop_corrected).mpr ⟨rfl, p, hcp, rfl⟩⟩


/-! ## `Bcatch`

`grammar Bcatch : catch` (5.3:61-65) is four productions, two of them an
opcode followed by a `tagidx` and a `labelidx`.  `try_table`, its only user, is
out of scope here (it needs `Blist` and the `(in:Binstr)*` iteration), so this
is the nonterminal on its own. -/

/-- The four productions of `grammar Bcatch : catch` (5.3:61-65). -/
def bcatchProds : List IL.Prod :=
  [ .prodD [.expP "x" (.varT "idx" []), .expP "l" (.varT "labelidx" [])]
      (.seqG [.seqG [.numG 0x00], .seqG [.attrG (.varE "x") (.varG "Btagidx" [])],
              .seqG [.attrG (.varE "l") (.varG "Blabelidx" [])]])
      (.caseE "CATCH" (.tupE [.varE "x", .varE "l"])) [],
    .prodD [.expP "x" (.varT "idx" []), .expP "l" (.varT "labelidx" [])]
      (.seqG [.seqG [.numG 0x01], .seqG [.attrG (.varE "x") (.varG "Btagidx" [])],
              .seqG [.attrG (.varE "l") (.varG "Blabelidx" [])]])
      (.caseE "CATCH_REF" (.tupE [.varE "x", .varE "l"])) [],
    .prodD [.expP "l" (.varT "labelidx" [])]
      (.seqG [.seqG [.numG 0x02], .seqG [.attrG (.varE "l") (.varG "Blabelidx" [])]])
      (.caseE "CATCH_ALL" (.varE "l")) [],
    .prodD [.expP "l" (.varT "labelidx" [])]
      (.seqG [.seqG [.numG 0x03], .seqG [.attrG (.varE "l") (.varG "Blabelidx" [])]])
      (.caseE "CATCH_ALL_REF" (.varE "l")) [] ]

/-- `Bcatch` is the pinned one. -/
structure HasCatch (env : Env) : Prop where
  /-- `grammar Bcatch : catch` (5.3:61-65). -/
  bcatch : env.findGram? "Bcatch" = some ([], .varT "catch" [], bcatchProds)

/-- **Provenance.**  The corrected wasm-3.0 script's `Bcatch`. -/
theorem hasCatch_corrected : HasCatch envC := ⟨rfl⟩

/-- **`Bcatch` (5.3:61-65) is `Silmaril.Wasm.Binary.Core.Catch`.** -/
theorem symDerives_bcatch {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    (hi : HasIdxNTs env) (hc : HasCatch env) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Bcatch" []) bs l ρ' ↔
      ρ' = ρ ∧ ∃ c : Wasm.Catch, Core.Catch bs c ∧ l = [Encode.toValue c] := by
  have htag : ∀ (τ τ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Btagidx" []) b ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG hi.btagidx).mp hd).1
  have hlab : ∀ (τ τ' : VarEnv) (b : Grammar.Bytes) (ws : List Value),
      SymDerives env τ (.varG "Blabelidx" []) b ws τ' → τ' = τ :=
    fun _ _ _ _ hd => ((symDerives_varG hi.blabelidx).mp hd).1
  rw [symDerives_varG hc.bcatch]
  constructor
  · rintro ⟨rfl, p, hp, hd⟩
    refine ⟨rfl, ?_⟩
    simp only [bcatchProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · obtain ⟨l₀, σ, u, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, rfl, rfl⟩ :=
        symDerives_seqG_triple.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT htag).mp h₂
      obtain ⟨-, x, hx, hlw⟩ := (symDerives_idxNT h hl (by decide) hi.btagidx
        (k := .tag)).mp hw
      have hw' : w = Encode.toValue x := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain ⟨w', hw'', rfl, hm'⟩ := (symDerives_attrNT hlab).mp h₃
      obtain ⟨-, y, hy, hlw'⟩ := (symDerives_idxNT h hl (by decide) hi.blabelidx
        (k := .label)).mp hw''
      have hw2 : w' = Encode.toValue y := by simpa using hlw'
      subst hw2
      rw [matchExp_varE_of_none_iff rfl] at hm'
      subst hm'
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_varE_iff.mpr rfl,
          evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩)
      exact ⟨.catch_ x y, .catch_ hx hy, rfl⟩
    · obtain ⟨l₀, σ, u, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, σ₂, b₃, l₃, h₁, h₂, h₃, rfl, rfl⟩ :=
        symDerives_seqG_triple.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT htag).mp h₂
      obtain ⟨-, x, hx, hlw⟩ := (symDerives_idxNT h hl (by decide) hi.btagidx
        (k := .tag)).mp hw
      have hw' : w = Encode.toValue x := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain ⟨w', hw'', rfl, hm'⟩ := (symDerives_attrNT hlab).mp h₃
      obtain ⟨-, y, hy, hlw'⟩ := (symDerives_idxNT h hl (by decide) hi.blabelidx
        (k := .label)).mp hw''
      have hw2 : w' = Encode.toValue y := by simpa using hlw'
      subst hw2
      rw [matchExp_varE_of_none_iff rfl] at hm'
      subst hm'
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr ⟨_,
        evalExp_tupE_pair_iff.mpr ⟨_, _, evalExp_varE_iff.mpr rfl,
          evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩)
      exact ⟨.catchRef x y, .catchRef hx hy, rfl⟩
    · obtain ⟨l₀, σ, u, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hlab).mp h₂
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxNT h hl (by decide) hi.blabelidx
        (k := .label)).mp hw
      have hw' : w = Encode.toValue y := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr
        ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩)
      exact ⟨.catchAll y, .catchAll hy, rfl⟩
    · obtain ⟨l₀, σ, u, hs, hev, rfl⟩ := (prodDerives_simple rfl).mp hd
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩ := symDerives_seqG_pair.mp hs
      obtain ⟨rfl, rfl, rfl⟩ := (symDerives_byteFactor (by decide)).mp h₁
      obtain ⟨w, hw, rfl, hm⟩ := (symDerives_attrNT hlab).mp h₂
      obtain ⟨-, y, hy, hlw⟩ := (symDerives_idxNT h hl (by decide) hi.blabelidx
        (k := .label)).mp hw
      have hw' : w = Encode.toValue y := by simpa using hlw
      subst hw'
      rw [matchExp_varE_of_none_iff rfl] at hm
      subst hm
      obtain rfl := EvalExp.unique hev (evalExp_caseE_iff.mpr
        ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩)
      exact ⟨.catchAllRef y, .catchAllRef hy, rfl⟩
  · rintro ⟨rfl, c, hcc, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hcc with
    | @catch_ b b' x y hx hy =>
        refine ⟨_, List.mem_cons_self .., (prodDerives_simple rfl).mpr
          ⟨_, _, _, symDerives_seqG_triple.mpr ⟨_, _, VarEnv.empty, _, _, _, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT htag).mpr ⟨Encode.toValue x,
              (symDerives_idxNT h hl (by decide) hi.btagidx).mpr ⟨rfl, x, hx, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩,
            (symDerives_attrNT hlab).mpr ⟨Encode.toValue y,
              (symDerives_idxNT h hl (by decide) hi.blabelidx).mpr ⟨rfl, y, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr
          ⟨_, _, evalExp_varE_iff.mpr rfl, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩
    | @catchRef b b' x y hx hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (prodDerives_simple rfl).mpr
          ⟨_, _, _, symDerives_seqG_triple.mpr ⟨_, _, VarEnv.empty, _, _, _, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT htag).mpr ⟨Encode.toValue x,
              (symDerives_idxNT h hl (by decide) hi.btagidx).mpr ⟨rfl, x, hx, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩,
            (symDerives_attrNT hlab).mpr ⟨Encode.toValue y,
              (symDerives_idxNT h hl (by decide) hi.blabelidx).mpr ⟨rfl, y, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_pair_iff.mpr
          ⟨_, _, evalExp_varE_iff.mpr rfl, evalExp_varE_iff.mpr rfl, rfl⟩, rfl⟩
    | @catchAll b y hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          (prodDerives_simple rfl).mpr
          ⟨_, _, _, symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT hlab).mpr ⟨Encode.toValue y,
              (symDerives_idxNT h hl (by decide) hi.blabelidx).mpr ⟨rfl, y, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩
    | @catchAllRef b y hy =>
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          (prodDerives_simple rfl).mpr
          ⟨_, _, _, symDerives_seqG_pair.mpr ⟨_, _, VarEnv.empty, _, _,
            (symDerives_byteFactor (by decide)).mpr ⟨rfl, rfl, rfl⟩,
            (symDerives_attrNT hlab).mpr ⟨Encode.toValue y,
              (symDerives_idxNT h hl (by decide) hi.blabelidx).mpr ⟨rfl, y, hy, rfl⟩, rfl,
              matchExp_varE_of_none rfl⟩, rfl, rfl⟩, ?_, rfl⟩⟩
        exact evalExp_caseE_iff.mpr ⟨_, evalExp_varE_iff.mpr rfl, rfl⟩

/-- **`Bcatch` as an `EncRel`, at the corrected wasm-3.0 script.** -/
theorem gramRel_bcatch_corrected (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup envC ρ (.varG "Bcatch" []) bs v ↔
      ∃ c : Wasm.Catch, Core.Catch bs c ∧ v = Encode.toValue c := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨σ, hd⟩
    obtain ⟨-, c, hcc, hlw⟩ := (symDerives_bcatch hasBinTypes_corrected hasLebC
      hasIdxNTs_corrected hasCatch_corrected).mp hd
    exact ⟨c, hcc, by simpa using hlw⟩
  · rintro ⟨c, hcc, rfl⟩
    exact ⟨ρ, (symDerives_bcatch hasBinTypes_corrected hasLebC hasIdxNTs_corrected
      hasCatch_corrected).mpr ⟨rfl, c, hcc, rfl⟩⟩


/-! ## What this file does not prove

Stated precisely, because the lead-byte filter makes it easy to say exactly
which opcodes are covered and which are not.

* **The structured instructions.**  `0x02` `BLOCK`, `0x03` `LOOP`, `0x04` `IF`
  (two productions) and `0x1F` `TRY_TABLE` all contain
  `(iter (attr (var "in") (var "Binstr")) list (dom "in" (var "in*")))`, the
  list iteration of the *recursive* nonterminal.  `Sem/Grammar.lean`'s
  `iterAct`/`IterCount` give it a denotation, but nothing here reasons about
  it, and the matching `Core.Instrs`/`Core.Blk` induction is not done.
  `Bblocktype`, the other half of those four productions, *is* done
  (`gramRel_bblocktype`), and so is `Bcatch` (`gramRel_bcatch_corrected`).
* **Everything that goes through `Blist`.**  `0x0E` `BR_TABLE`, `0x1C`
  `SELECT t*`, and the `Blist(Bcatch)` of `TRY_TABLE`.  `Equiv/BinaryTypes.lean`
  says the same about `Bresulttype`, `Bcomptype`, `Bsubtype` and `Brectype`:
  the generic bridge "`Blist(BX)` denotes `Silmaril.Wasm.Binary.Vec R` whenever
  `BX` denotes `R`" is not proved anywhere yet.
* **The two-immediate opcodes.**  `0x11` `CALL_INDIRECT` and `0x13`
  `RETURN_CALL_INDIRECT` are `0xNN y:Btypeidx x:Btableidx`; the shape is a
  three-factor sequence and `binstrWrap` handles only two.  Nothing stands in
  the way, it is simply not written.
* **The memory instructions.**  `0x28`-`0x3E` are `0xNN (x,ao):Bmemarg`, and
  `grammar Bmemarg : memidxop` (5.3:100-102) is two productions with
  arithmetic premises (`n < 2^6`, `2^6 <= n < 2^7`) and a value expression that
  subtracts `2^6` from the alignment through `cvt int nat`.  Neither `Bmemarg`
  nor any of the 23 load/store rows is proved here.  The corresponding
  hand-written relation is `Core.Memarg` and `Core.MemOp`.  Note that a bridge
  for it needs an `Encode (Fin (2 ^ 32))` instance, which
  `Equiv/V1Binary.lean` also defines; whoever writes it should reuse that one
  rather than add a second.
* **The `0xFB`, `0xFC` and `0xFD` families.**  31, 18 and 256 productions
  respectively, each `0xNN k:Bu32 …` with a *non-minimal-LEB128-tolerant*
  sub-opcode, so `binstrOps envC 0xFB` is a 31-element list and the inversion
  has to discriminate on the `Bu32` value rather than on a byte.  The lead-byte
  filter of this file is the right starting point but does not do it.
* **The constants.**  `0x41`-`0x44`.  `0x43`/`0x44` need `Bf32`/`Bf64`;
  `0x41`/`0x42` are the subject of `binstr_i32Const_misses_FF7E`, which shows
  the corrected specification is *not* `Core.Instr` there, so there is no
  equality to prove — characterising what it is instead would mean exporting
  `Equiv/BinaryValues.lean`'s `bsn_iff_sn` through the opcode, which is not
  done.
* **Unambiguity.**  `Core/Instructions.lean` proves `Instr.prefixFree`;
  transporting it along the rows above would give unambiguity of `Binstr` at
  those opcodes, and is not written down.
* **`Bexpr`** (`5.3:812-813`) and everything in `5.4-binary.modules.spectec`.

`instrV` is a *total* function with a junk default, so a statement that applies
it to an instruction outside the rows above says nothing.  `instrV_case` is the
machine-checked guarantee that `binstr_plain` never reaches the default clause;
the index rows name their constructor explicitly, so they cannot either.
-/

end Silmaril.SpecTec.Equiv
