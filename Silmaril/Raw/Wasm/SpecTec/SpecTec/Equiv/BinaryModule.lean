module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryTypes
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryValues
public import Silmaril.Wasm.Binary.Core.Modules
-- As in `Equiv/BinaryInstr.lean`: `spectec_import` and `spectec_erratum` add their
-- constants with `Lean.addDecl`, so the *values* of `Specs.wasm30` and
-- `Binary51.wasm30binary51` are invisible to an importing module without these.
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51

/-!
# The corrected wasm-3.0 binary grammar for modules

Phase 4, the module section.  `Equiv/BinaryValues.lean`, `Equiv/BinaryTypes.lean`
and `Equiv/BinaryInstr.lean` have done §5.1, §5.2 and §5.3; this file does
`specification/wasm-3.0/5.4-binary.modules.spectec`, cited `5.4:n`, against
`Silmaril/Wasm/Binary/Basic.lean` and `Silmaril/Wasm/Binary/Core/Modules.lean`.
`5.1:n` is `specification/wasm-3.0/5.1-binary.values.spectec`.

## The L-attributed iteration: it works

`Sem/Grammar.lean`'s module docstring names `Blist` (`5.1:40-41`)

```
grammar Blist(grammar BX : el) : el* =
  | n:Bu32 (el:BX)^n => el^n
```

as the witness that SpecTec grammars are genuinely L-attributed: the
repetition count of the second factor is the value the first factor bound.
Its framework attribute is an *environment transformer* `Act`, and no file in
this tree had exercised that — `Equiv/BinaryTypes.lean`, `Equiv/BinaryInstr.lean`
and `Equiv/V1Binary.lean` all record "everything that goes through `Blist`" as
the gap that blocks the most.

`blist_iff_vec` closes it, in both directions:

```
gramRelSup env ρ Blist(el, BY) bs v ↔ ∃ ws, Vec (NtRel env BY) bs ws ∧ v = .list ws
```

where `Vec` is `Silmaril.Wasm.Binary.Vec`, the hand-written "a `Bu32` count
followed by that many encodings".  Nothing had to be added to
`Sem/Grammar.lean` or to `Grammar/Basic.lean`: the framework carries the
dependency exactly as designed.  The supporting machinery, all new and all
generic, is

* `Rounds` and `rounds_iff` — the Kleene closure of one round of an `IterG`,
  applied at a scope, read as an inductive list of rounds;
* `symDerives_iterG` — `IterG (g, (it, ds))` as a derivation: `Rounds` many
  rounds, `IterCount` many of them, `BindDoms` binding the columns outwards;
* `gramRelSup_varG_nil_scope` — a parameterless nonterminal's derivations do
  not depend on the caller's scope, which is what lets `Blist`'s elements be
  compared against a scope-free relation (`NtRel`);
* `matchExp_iterList_var` / `evalExp_iterList_var` / `evalExp_blistResult` —
  the `eval.ml` side of a one-domain iteration, in both directions.

## The finding: `||BX||` elaborates to `0`

`Bsection_` (`5.4:9-11`) is

```
grammar Bsection_(N, grammar BX : en*) : en* =
  | N:Bbyte len:Bu32 en*:BX => en*  -- if len = ||BX||
  | eps => eps
```

and `spectec/src/frontend/elab.ml:1284-1286` is

```ocaml
| SizeE id ->
  let _ = find "grammar" env.grams id in
  Ok (Il.NumE (`Nat Z.zero), Il.NumT `NatT)
```

`SizeE` is `` `|` `|` `` doubled, `spectec/src/el/ast.ml:102`.  The elaborator
checks that the named grammar exists and then returns the **literal `0`**.  So
the elaborated side condition is `len = 0`, which is what
`specs/spectec/wasm-3.0.ast` contains; `bsectionProds` transcribes it and
`hasSecs_corrected`/`hasSecs_wasm30` are the kernel-checked `rfl`s that this is
the pinned text, corrected and uncorrected.

The consequence is stated as an equality of relations.  `SectionZero` is
`Silmaril.Wasm.Binary.Section` with `len = c.length` replaced by `len = 0`,
and `bsection_iff` is

```
Bsection_(N, BX)  =  SectionZero N R          (R = what BX denotes)
```

both directions.  Two witnesses make the gap concrete, at the type section:

| byte string | what it is | `Btypesec` | `Core.TypeSec` |
| --- | --- | --- | --- |
| `01 01 00` | the empty type section | derives **nothing** | derives `[]` |
| `01 00 00` | size 0, one byte of contents | derives `[]` | derives **nothing** |

(`btypesec_misses_empty_type_section`, `typeSec_empty_type_section`,
`btypesec_derives_ill_formed`, `not_typeSec_ill_formed`.)  Since every section
of a non-trivial module has a non-zero declared size, **the elaborated
wasm-3.0 binary grammar derives no module with a non-empty section**, and it
accepts byte strings whose declared sizes are all wrong.  The same notation
occurs once more, at `Bcode` (`5.4:133-134`, `-- if len = ||Bfunc||`), with
the same elaboration: `bcode_size_is_zero` proves that every byte string
`Bcode` derives begins with a `Bu32` encoding of zero.

This is a defect of the *frontend*, not of the specification text, and it is
not any of the 33 errata in `docs/projects/spectec-divergences.md`; a `spectec_erratum` patch
cannot fix it, because the IL has no expression form for "the number of bytes
this grammar derives" at all — `SizeE` lives only in the EL.

## `Bmagic` and `Bversion`

The brief asks whether errata #672 (wasm-2.0) and #687 (wasm-1.0), "the
version field is written as a LEB128 `1:Bu32` instead of four raw bytes",
apply to 3.0.  They do not: `specification/wasm-3.0/5.4-binary.modules.spectec:174`
reads `grammar Bversion : () = 0x01 0x00 0x00 0x00 => ()`, against
`specification/wasm-1.0/A-binary.spectec:527` and
`specification/wasm-2.0/A-binary.spectec:924`, which both read
`0x00 0x61 0x73 0x6D 1:Bu32`.  `bmagic_iff_magic` and `bversion_iff_version`
prove, in both directions, that the two grammars derive exactly
`Silmaril.Wasm.Binary.magic` and `Silmaril.Wasm.Binary.version`.

## The correspondence

Every row is an **equality of relations**, proved in both directions.

| SpecTec | Lean | statement |
| --- | --- | --- |
| `Blist(el, BY)` (`5.1:40-41`) | `Vec` | `blist_iff_vec` |
| `Bmagic` (`5.4:173`) | `magic` | `bmagic_iff_magic` |
| `Bversion` (`5.4:174`) | `version` | `bversion_iff_version` |
| `Bsection_(N, BX)` (`5.4:9-11`) | `SectionZero N` | `bsection_iff` |
| `Btypesec` (`5.4:28-29`) | `SectionZero 1 (Vec …)` | `btypesec_iff` |
| `Bimportsec` (`5.4:37-38`) | `SectionZero 2 (Vec …)` | `bimportsec_iff` |
| `Bfuncsec` (`5.4:43-44`) | `SectionZero 3 (Vec Index)` | `bfuncsec_iff_sectionZero` |
| `Btablesec` (`5.4:53-54`) | `SectionZero 4 (Vec …)` | `btablesec_iff` |
| `Bmemsec` (`5.4:62-63`) | `SectionZero 5 (Vec …)` | `bmemsec_iff` |
| `Bglobalsec` (`5.4:71-72`) | `SectionZero 6 (Vec …)` | `bglobalsec_iff` |
| `Bexportsec` (`5.4:80-81`) | `SectionZero 7 (Vec …)` | `bexportsec_iff` |
| `Belemsec` (`5.4:118-119`) | `SectionZero 9 (Vec …)` | `belemsec_iff` |
| `Bcodesec` (`5.4:136-137`) | `SectionZero 10 (Vec …)` | `bcodesec_iff` |
| `Bdatasec` (`5.4:147-148`) | `SectionZero 11 (Vec …)` | `bdatasec_iff` |
| `Btagsec` (`5.4:167-168`) | `SectionZero 13 (Vec …)` | `btagsec_iff` |
| `Bcode` (`5.4:133-134`) | — | `bcode_size_is_zero` (one direction) |

The eleven section rows are instances of one lemma, `sec_iff`, which composes
`secWrap_iff` (the one-line `v*:Bsection_(N, Blist(Bxxx)) => v*` wrapper) with
`bsectionBlist_iff` (`bsection_iff` at a `Blist` argument).  They are stated
over `NtRel env "Bxxx"`, the denotation of the element grammar, because §5.2
and §5.3 do not yet reach `Btype`, `Bimport`, `Btable`, `Bglobal`, `Belem`,
`Bcode` or `Bdata`; **the framing is proved, the elements are parameters**.

One section is taken all the way to Silmaril's own relation:
`bfuncsec_iff_sectionZero` reads `Bfuncsec` as `SectionZero 3 (Vec Index)`
over `Silmaril.Wasm.Binary.Index`, transported along the `Encode` bridge
(`ntRel_btypeidx`, `seq_toValue_iff`, `vec_toValue_iff`,
`sectionZero_toValue_iff`), and `funcSec_eq_section` records that
`Core.FuncSec` is `Section 3 (Vec Index)` — the *same* contents relation.  The
two differ in exactly one place, the size premise.

## Provenance

`HasSecs` lists, one field per nonterminal, what the stream contains;
`hasSecs_corrected` and `hasSecs_wasm30` discharge all fifteen by `rfl`
against `Silmaril.SpecTec.IL.Binary51.wasm30binary51` and
`Silmaril.SpecTec.Specs.wasm30`.  `HasBlist` does the same for `Blist`, `Bu32`
and the LEB128 grammar, through `Equiv/BinaryTypes.lean`'s `HasBinTypes` and
`Equiv/BinaryValues.lean`'s `HasWrappers`.  `#650` corrects `Bi32`, `Bi64`,
`$cont` and `$utf8`, none of which §5.4 mentions, so every statement here
reads the same in the pinned script as in the corrected one.

## What this file does **not** prove

* **`Bmodule` (`5.4:175-195`).**  Three things are missing, and none of them
  is a matter of effort.  (i) Its value expression mentions `func*`, which no
  factor of the sequence binds: `func*` is a production *quantifier*
  constrained only by the trailing premise
  `-- (if func = FUNC typeidx local* expr)*`.  `Sem/Grammar.lean`'s
  `prodActFn` evaluates the value expression in the scope the premises leave,
  and `Sem/Eval.lean`'s `premsHold` *checks* an `IfPr`, it does not solve for
  an unbound variable, so the production as elaborated has no derivation at
  all unless `func*` is bound elsewhere — `Sem/Eval.lean`'s `premIter` starts
  by evaluating its domains, and `var "func*"` has no value.  That is a
  second, independent finding about the elaborated `Bmodule`, and it is
  **not** proved here: proving it means characterising the scope the whole
  thirteen-factor body leaves, which needs every element grammar below.
  (ii) `Bcustomsec*` needs `Bname`, hence `$utf8`, whose last clause calls
  itself on its own argument (`Equiv/V1Binary.lean`,
  `utf8_charArg_only_last_clause_v1`).  (iii) `Bstartsec` and `Bdatacntsec`
  apply `$opt_`, a `DecD` call, so they need `callDef`.
* **The element grammars** `Btype`, `Bimport`, `Btable`, `Bmem`, `Bglobal`,
  `Bexport`, `Belem`, `Bcode`, `Bdata`, `Btag`.  Each needs §5.2 or §5.3 one
  level higher than `Equiv/BinaryTypes.lean` and `Equiv/BinaryInstr.lean`
  reach — `Brectype`, `Bexterntype`, `Bexpr` — and `Bexpr` needs all 498
  productions of `Binstr`.  The section rows above are stated over `NtRel` so
  that they compose with those results when they exist.
* **`Bcustomsec`, `Bstartsec`, `Bdatacntsec`**, for the reasons above.  Their
  `Bsection_` framing is covered by `bsection_iff`, which is stated for an
  arbitrary content grammar; only the content side is missing.
* **The converse of `bcode_size_is_zero`**, which would need `Bfunc`.
* **Unambiguity.**  `Core/Modules.lean` proves `PrefixFree` for the section
  relations; transporting it along the equalities here is immediate but is
  not written down.

## #803

`#803` — the elaborator narrows `int` to `nat`, so `BsN` derives no
multi-byte negative LEB128 — does not bite in §5.4: the only numerals in the
module section are `Bu32` section ids, sizes, vector counts and indices, all
unsigned.  It does bite one level down, inside `Belem`, `Bdata` and `Bcode`,
through `Bexpr`'s `CONST` immediates; that is `Equiv/BinaryValues.lean`'s
`not_bi32_corrected_FF7E` and `Equiv/BinaryInstr.lean`'s
`binstr_i32Const_misses_FF7E`, and nothing here re-states it.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.BinaryModule

open Silmaril.SpecTec.IL Silmaril.SpecTec.Sem Silmaril.SpecTec.Equiv
open Silmaril.Wasm.Binary Silmaril.SpecTec.Grammar

set_option maxRecDepth 4000000

/-! ## Iteration, elementwise -/

/-- The rounds of an `IterG` (`spectec/src/il/ast.ml:109`), read off the
framework's Kleene closure: each round derives a byte string from `g`
*starting in the same scope* `ρ` (`roundActFn` restores it), contributes one
value, and reports the value each `iterexp` domain variable
(`ast.ml:95`) was bound to in that round. -/
inductive Rounds (env : Env) (ρ : VarEnv) (g : IL.Sym) (ds : List Dom) :
    Grammar.Bytes → List (Value × List Value) → Prop where
  /-- No rounds: no bytes. -/
  | nil : Rounds env ρ g ds [] []
  /-- One more round, prepended. -/
  | cons {b bs : Grammar.Bytes} {v : Value} {vs : List Value}
      {rows : List (Value × List Value)} {ρ₁ : VarEnv}
      (hd : SymDerives env ρ g b [v] ρ₁)
      (hv : ds.mapM (fun d => ρ₁.findVal? (domVar d)) = some vs)
      (ht : Rounds env ρ g ds bs rows) :
      Rounds env ρ g ds (b ++ bs) ((v, vs) :: rows)

/-- The Kleene closure of one round, applied at a scope, is exactly `Rounds`.
This is the step that makes `Sem/Grammar.lean`'s environment-transformer
attribute usable: the framework chooses each factor's byte string
independently, and `actApp` threads the scope through them. -/
theorem rounds_iff {env : Env} {ρ ρ' : VarEnv} {g : IL.Sym} {ds : List Dom}
    {bs : Grammar.Bytes} {l : List Value} :
    (∃ a : Act, kleene actAlg (EncRel.mapPartial (roundAct ds) (symDen env g)) bs a ∧
        a ρ l ρ') ↔
      ∃ rows, Rounds env ρ g ds bs rows ∧
        l = rows.map (fun r => Value.tuple (r.1 :: r.2)) ∧ ρ' = ρ := by
  have key : ∀ (k : Nat) (cs : Grammar.Bytes) (a : Act) (m : List Value) (σ : VarEnv),
      powRel actAlg (EncRel.mapPartial (roundAct ds) (symDen env g)) k cs a → a ρ m σ →
      ∃ rows, Rounds env ρ g ds cs rows ∧
        m = rows.map (fun r => Value.tuple (r.1 :: r.2)) ∧ σ = ρ := by
    intro k
    induction k with
    | zero =>
        rintro cs a m σ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        exact ⟨[], .nil, rfl, rfl⟩
    | succ k ih =>
        rintro cs a m σ ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ hv
        obtain ⟨m₁, σ₁, m₂, k₁, k₂, rfl⟩ := hv
        obtain ⟨a₀, h₀, hf⟩ := h₁
        rw [roundAct, Option.some_inj] at hf
        subst hf
        obtain ⟨rfl, v, σx, vs, hvd, hm, rfl⟩ := k₁
        obtain ⟨rows, hrows, rfl, rfl⟩ := ih b₂ a₂ m₂ σ h₂ k₂
        exact ⟨(v, vs) :: rows, .cons ⟨a₀, h₀, hvd⟩ hm hrows, rfl, rfl⟩
  constructor
  · rintro ⟨a, ha, hv⟩
    obtain ⟨k, hk⟩ := kleene_apply.mp ha
    exact key k bs a l ρ' hk hv
  · rintro ⟨rows, hrows, rfl, rfl⟩
    induction hrows with
    | nil => exact ⟨actNil, kleene_apply.mpr ⟨0, rfl, rfl⟩, rfl, rfl⟩
    | @cons b bs v vs rows σ₁ hd hv ht ih =>
        obtain ⟨a₀, h₀, hvd⟩ := hd
        obtain ⟨a, ha, hva⟩ := ih
        obtain ⟨k, hk⟩ := kleene_apply.mp ha
        refine ⟨actApp (roundActFn ds a₀) a, kleene_apply.mpr ⟨k + 1, ?_⟩, ?_⟩
        · exact ⟨b, roundActFn ds a₀, bs, a, ⟨a₀, h₀, rfl⟩, hk, rfl, rfl⟩
        · exact ⟨[.tuple (v :: vs)], _, _, ⟨rfl, v, σ₁, vs, hvd, hv, rfl⟩, hva, rfl⟩

/-- The row encoding `roundActFn` uses — a round's own value consed onto its
domain column — is injective. -/
theorem tupleRow_injective :
    Function.Injective (fun r : Value × List Value => Value.tuple (r.1 :: r.2)) := by
  rintro ⟨v, vs⟩ ⟨w, ws⟩ h
  simp only [Value.tuple.injEq, List.cons.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- `IterG (g, (it, ds))` as a derivation: `Rounds` many rounds, as many as
the iterator admits, contributing the list (or option) of their values and
binding each domain's column outwards. -/
theorem symDerives_iterG {env : Env} {ρ ρ' : VarEnv} {g : IL.Sym} {it : Iter}
    {ds : List Dom} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.iterG g (.mk it ds)) bs l ρ' ↔
      ∃ rows, Rounds env ρ g ds bs rows ∧ IterCount env ρ it rows.length ∧
        l = [iterValue it (rows.map Prod.fst)] ∧
        BindDoms env it ds (rows.map Prod.snd) ρ ρ' := by
  rw [SymDerives, symDen_iterG]
  constructor
  · rintro ⟨a, ⟨a₀, h₀, hf⟩, hv⟩
    rw [iterAct, Option.some_inj] at hf
    subst hf
    obtain ⟨rows, hk, hc, hl, hb⟩ := hv
    obtain ⟨rows', hrows, hlm, -⟩ := rounds_iff.mp ⟨a₀, h₀, hk⟩
    have hrr : rows = rows' := List.map_injective_iff.mpr tupleRow_injective hlm
    subst hrr
    exact ⟨rows, hrows, hc, hl, hb⟩
  · rintro ⟨rows, hrows, hc, rfl, hb⟩
    obtain ⟨a₀, h₀, hk⟩ := rounds_iff.mpr ⟨rows, hrows, rfl, rfl⟩
    exact ⟨iterActFn env it ds a₀, ⟨a₀, h₀, rfl⟩, rows, hk, hc, rfl, hb⟩


/-! ## `Blist`: the L-attributed iteration -/

/-- Reading every index of a list off it, in order.  This is the pure list
fact behind `iterRows_single`. -/
theorem map_range_getElem? {α : Type} (l : List α) :
    (List.range l.length).map (fun i => l[i]?) = l.map some := by
  have key : ∀ (post pre : List α),
      (List.range' pre.length post.length).map (fun i => (pre ++ post)[i]?)
        = post.map some := by
    intro post
    induction post with
    | nil => intro pre; simp
    | cons w ws ih =>
        intro pre
        have hw : (pre ++ w :: ws)[pre.length]? = some w := by
          simp
        have hsplit : pre ++ w :: ws = (pre ++ [w]) ++ ws := by simp
        have hlen : (pre ++ [w]).length = pre.length + 1 := by simp
        rw [List.length_cons, List.range'_succ, List.map_cons, hw, List.map_cons]
        congr 1
        rw [hsplit, ← hlen]
        exact ih (pre ++ [w])
  have := key l []
  simpa [List.range_eq_range'] using this


/-- `iterRows` (`Sem/Eval.lean`, `eval.ml:406-415`) for a single domain, run
for exactly as many rounds as the domain has elements: round `i` binds the
domain variable to the `i`-th element and nothing else. -/
theorem iterRows_single (x : IL.Id) (ws : List Value) :
    iterRows [(x, ws)] none ws.length = ws.map (fun w => [(x, w)]) := by
  have h : ∀ i, iterRow [(x, ws)] none i
      = ((ws[i]?).map (fun v => (x, v))).toList := by
    intro i
    rw [iterRow]
    rcases hi : ws[i]? with _ | v <;> simp [hi]
  have hmap : (List.range ws.length).map (iterRow [(x, ws)] none)
      = ((List.range ws.length).map (fun i => ws[i]?)).map
        (fun o => (o.map (fun v => (x, v))).toList) := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ => h i
  rw [iterRows, hmap, map_range_getElem?, List.map_map]
  simp

/-- One round per element, with the body the domain variable itself. -/
theorem evalRounds_single (env : Env) (ρ : VarEnv) (x : IL.Id) (hx : x ≠ "_")
    (ws : List Value) (n : Nat) :
    evalRounds (n + 2) env ρ (.varE x) (ws.map (fun w => [(x, w)])) = .ok ws := by
  rw [evalRounds]
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      have hv : evalExp (n + 1) env (ρ.bindVals [(x, w)]) (.varE x) = .ok w := by
        simp [evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, hx]
      simp [List.mapM_cons, hv, ih]


/-- The `Blist` production's value expression `el^n`
(`5.1-binary.values.spectec:41`): with `n` the count and `el*` the column of
the iteration, it denotes the list of elements. -/
theorem evalExp_blistResult {env : Env} {ρ : VarEnv} {ws : List Value} {m : Nat}
    (hn : ρ.findVal? "n" = some (.num (.natN m)))
    (hel : ρ.findVal? "el*" = some (.list ws)) (hm : ws.length = m) :
    EvalExp env ρ (.iterE (.varE "el")
      (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])) (.list ws) := by
  subst hm
  refine evalExp_iterE_iff.mpr ⟨4, ?_⟩
  have hdoms : evalDoms 3 env ρ [.mk "el" (.varE "el*")]
      = .ok [("el", Value.list ws)] := by
    simp [evalDoms, domVar, domSrc, evalExp, hel]
  have hcount : evalExp 3 env ρ (.varE "n") = .ok (.num (.natN ws.length)) := by
    simp [evalExp, hn]
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hcount]
  refine ⟨_, rfl, _, rfl, ws.length, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok]
  refine ⟨[("el", ws)], by simp [Value.asList?], by simp, ws, ?_, rfl⟩
  rw [iterRows_single]
  exact evalRounds_single env ρ "el" (by decide) ws 0


/-- A nonterminal leaves the caller's scope untouched, whether or not the
script defines it (`prodActFn`'s `ρ' = ρ`). -/
theorem symDerives_varG_scope {env : Env} {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} {x : IL.Id} {args : List IL.Arg}
    (h : SymDerives env ρ (.varG x args) bs l ρ') : ρ' = ρ := by
  cases hf : env.findGram? x with
  | none =>
      obtain ⟨a, ha, -⟩ := h
      rw [symDen_varG_of_none env x args hf] at ha
      exact ha.elim
  | some d =>
      obtain ⟨ps, t, prods⟩ := d
      exact ((symDerives_varG hf).mp h).1

/-- A **parameterless** nonterminal's derivations do not depend on the
caller's scope at all: `prodActFn` evaluates the (empty) argument list in it
and then starts the production in the fresh scope `VarEnv.empty`.  This is
what lets the elements of a `Blist` be compared against a scope-free
hand-written relation. -/
theorem gramRelSup_varG_nil_scope {env : Env} {y : IL.Id} (ρ σ : VarEnv)
    {bs : Grammar.Bytes} {v : Value} :
    gramRelSup env ρ (.varG y []) bs v ↔ gramRelSup env σ (.varG y []) bs v := by
  have key : ∀ ρ σ : VarEnv, gramRelSup env ρ (.varG y []) bs v →
      gramRelSup env σ (.varG y []) bs v := by
    intro ρ σ h
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
    cases hf : env.findGram? y with
    | none =>
        obtain ⟨a, ha, -⟩ := hd
        rw [symDen_varG_of_none env y [] hf] at ha
        exact ha.elim
    | some d =>
        obtain ⟨ps, t, prods⟩ := d
        rw [symDerives_varG hf] at hd
        obtain ⟨-, p, hp, hpd⟩ := hd
        refine gramRelSup_iff.mpr ⟨σ, (symDerives_varG hf).mpr ⟨rfl, p, hp, ?_⟩⟩
        obtain ⟨q, g, e, prems⟩ := p
        obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, hev, hl⟩ := hpd
        rw [evalArgs_nil_iff] at hargs
        subst hargs
        exact ⟨[], ρ₀, l₀, ρ₁, ρ₂, v', evalArgs_nil env σ, hbp, hbody, hprems, hev, hl⟩
  exact ⟨key ρ σ, key σ ρ⟩

/-- The relation a parameterless nonterminal denotes, as a scope-free
`Bytes → Value → Prop`; `gramRelSup_varG_nil_scope` says the choice of scope
is immaterial. -/
def NtRel (env : Env) (y : IL.Id) : Grammar.Bytes → Value → Prop :=
  fun bs v => gramRelSup env VarEnv.empty (.varG y []) bs v

/-- The rounds of `Blist`'s `(el:BX)^n`
(`5.1-binary.values.spectec:41`): one derivation of the wrapped nonterminal
apiece, each exporting exactly the binding of `el`.  The `Seq` on the right is
`Silmaril.Wasm.Binary.Seq`, the hand-written "concatenation, one encoding per
element". -/
theorem rounds_blist {env : Env} {ρ : VarEnv} {y : IL.Id} {bs : Grammar.Bytes}
    {rows : List (Value × List Value)} (hel : ρ.findVal? "el" = none) :
    Rounds env ρ (.attrG (.varE "el") (.varG y [])) [.mk "el" (.varE "el*")] bs rows ↔
      ∃ ws, rows = ws.map (fun w => (w, [w])) ∧ Seq (NtRel env y) bs ws := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl, .nil⟩
    | @cons b bs v vs rows ρ₁ hd hv ht ih =>
        obtain ⟨ws, hrows, hseq⟩ := ih
        rw [symDerives_attrG] at hd
        obtain ⟨w, ρx, hnt, hvw, hm⟩ := hd
        have hv' : v = w := by simpa using hvw
        have hx : ρx = ρ := symDerives_varG_scope hnt
        rw [hx] at hm
        have hρ₁ : ρ₁ = VarEnv.bindVal ρ "el" w :=
          MatchExp.unique hm (matchExp_varE_of_none hel)
        have hfind : (VarEnv.bindVal ρ "el" w).findVal? "el" = some w := by
          simp [VarEnv.findVal?, VarEnv.bindVal]
        have hvs : vs = [w] := by
          rw [hρ₁] at hv
          exact (by simpa [domVar, hfind] using hv : [w] = vs).symm
        refine ⟨w :: ws, ?_, .cons ?_ hseq⟩
        · rw [hrows, hv', hvs]
          rfl
        · exact (gramRelSup_varG_nil_scope ρ VarEnv.empty).mp (gramRelSup_iff.mpr ⟨ρx, hnt⟩)
  · rintro ⟨ws, rfl, hseq⟩
    induction hseq with
    | nil => exact .nil
    | @cons b bs w us hw hus ih =>
        have hnt : SymDerives env ρ (.varG y []) b [w] ρ := by
          obtain ⟨ρ', hρ⟩ :=
            gramRelSup_iff.mp ((gramRelSup_varG_nil_scope VarEnv.empty ρ).mp hw)
          rwa [symDerives_varG_scope hρ] at hρ
        have hfind : (VarEnv.bindVal ρ "el" w).findVal? "el" = some w := by
          simp [VarEnv.findVal?, VarEnv.bindVal]
        exact .cons (symDerives_attrG.mpr ⟨w, ρ, hnt, rfl, matchExp_varE_of_none hel⟩)
          (by simp [domVar, hfind]) ih


/-- A type argument and a grammar argument evaluate to themselves, resolved
through the caller's scope (`evalArg`, `spectec/src/il/eval.ml:363`). -/
theorem evalArgs_typA_gramA_iff {env : Env} {ρ : VarEnv} {t : Typ} {g : IL.Sym}
    {ws : List ArgV} :
    EvalArgs env ρ [.typA t, .gramA g] ws ↔
      ws = [.typ (resolveTyp ρ t), .gram (resolveSym ρ g)] := by
  constructor
  · rintro ⟨n, h⟩
    match n, h with
    | 0, h => simp [evalArgs] at h
    | 1, h => simp [evalArgs, evalArg] at h
    | n + 2, h =>
        have : (Except.ok ws : Res (List ArgV))
            = .ok [ArgV.typ (resolveTyp ρ t), ArgV.gram (resolveSym ρ g)] := by
          rw [← h]
          simp [evalArgs, evalArg, List.mapM_cons]
        exact Except.ok.inj this
  · rintro rfl
    exact ⟨2, by simp [evalArgs, evalArg, List.mapM_cons]⟩

/-- `Bu32` is `Silmaril.Wasm.Binary.U32`, at any environment with the pinned
LEB128 grammar and the pinned wrapper. -/
theorem bu32_iff_u32 {env : Env} (hl : HasLeb env) (hw : HasWrappers env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bu32" []) bs v ↔ ∃ m, U32 bs m ∧ v = uNV m := by
  rw [wrap_rel_iff hw.bu32 hl.bun ρ bs v]
  exact bun_iff_un hl 32 bs v VarEnv.empty

/-- The hypotheses the `Blist` bridge is stated under: the environment has the
pinned LEB128 grammar, the pinned `Bu32` wrapper and the pinned `Blist`. -/
structure HasBlist (env : Env) : Prop where
  /-- `Bbyte`/`BuN` are the pinned ones. -/
  leb : HasLeb env
  /-- `Bu32 = BuN(32)`. -/
  wrappers : HasWrappers env
  /-- `grammar Blist(syntax el, grammar BX : el) : el*` is the pinned one
  (`5.1-binary.values.spectec:40-41`). -/
  blist : env.findGram? "Blist"
    = some (blistParams, .iterT (.varT "el" []) .list, blistProds)

/-- The fresh scope a `Blist(el, BY)` call starts its production in
(`prodActFn`, `spectec/src/il/valid.ml:754`): the type parameter and the
grammar parameter, bound in `VarEnv.empty`. -/
def blistScope (ρ : VarEnv) (t : Typ) (y : IL.Id) : VarEnv :=
  (VarEnv.empty.bindTyp "el" (resolveTyp ρ t)).bindGram "BX" (resolveSym ρ (.varG y []))

/-- `n` is fresh in `blistScope`. -/
theorem blistScope_n (ρ : VarEnv) (t : Typ) (y : IL.Id) :
    (blistScope ρ t y).findVal? "n" = none := rfl

/-- `el` is fresh in `blistScope`: the type parameter lives in a different
namespace from the term variables. -/
theorem blistScope_el (ρ : VarEnv) (t : Typ) (y : IL.Id) :
    (blistScope ρ t y).findVal? "el" = none := rfl

/-- `el*` is fresh in `blistScope`. -/
theorem blistScope_els (ρ : VarEnv) (t : Typ) (y : IL.Id) :
    (blistScope ρ t y).findVal? "el*" = none := rfl

/-- The body of `Blist`'s sole production, with the grammar argument `BY`
already substituted for the parameter `BX` — which is how `prodsOf` resolves a
grammar-valued parameter (`spectec/src/il/subst.ml:210-228`). -/
def blistBody (y : IL.Id) : IL.Sym :=
  .seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
    .seqG [.iterG (.attrG (.varE "el") (.varG y []))
      (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])]]

/-- `substSym` really does turn `Blist`'s body into `blistBody y`; checked by
the kernel. -/
theorem substSym_blistBody (t : Typ) (y : IL.Id) :
    substSym (gramArgSubst blistParams [IL.Arg.typA t, .gramA (.varG y [])])
        (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
          .seqG [.iterG (.attrG (.varE "el") (.varG "BX" []))
            (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])]])
      = blistBody y := rfl

/-- The column a `Blist` round contributes: every round binds `el` once, so
the `el` column of the rounds is the list of values. -/
theorem filterMap_head?_rounds (ws : List Value) :
    (List.map Prod.snd (ws.map (fun w => (w, [w])))).filterMap List.head? = ws := by
  induction ws with
  | nil => rfl
  | cons w us ih => simpa using ih

/-- The values a `Blist` round contributes, read off the rounds. -/
theorem map_fst_rounds (ws : List Value) :
    List.map (Prod.fst ∘ fun w : Value => (w, [w])) ws = ws := by
  induction ws with
  | nil => rfl
  | cons w us ih => simpa using ih

/-- The body of `Blist`, as a derivation.  Stated at any scope in which the
production's three pattern variables are fresh, which is what
`bindParams … VarEnv.empty` guarantees. -/
theorem symDerives_blistBody {env : Env} (h : HasBlist env) {y : IL.Id} {σ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value}
    (hn : σ.findVal? "n" = none) (hel : σ.findVal? "el" = none)
    (hels : σ.findVal? "el*" = none) :
    SymDerives env σ (blistBody y) bs l ρ' ↔
      ∃ ws cb db, U32 cb ws.length ∧ Seq (NtRel env y) db ws ∧ bs = cb ++ db ∧
        l = [uNV ws.length, .list ws] ∧
        ρ' = (σ.bindVal "n" (Encode.toValue ws.length)).bindVal "el*" (.list ws) := by
  have hnel : ∀ (w : Value), (σ.bindVal "n" w).findVal? "el" = none := by
    intro w
    simpa [VarEnv.findVal?, VarEnv.bindVal, Map.find?_bind] using hel
  have hnels : ∀ (w : Value), (σ.bindVal "n" w).findVal? "el*" = none := by
    intro w
    simpa [VarEnv.findVal?, VarEnv.bindVal, Map.find?_bind] using hels
  have hnn : ∀ (w : Value), (σ.bindVal "n" w).findVal? "n" = some w := by
    intro w
    simp [VarEnv.findVal?, VarEnv.bindVal]
  constructor
  · intro hbody
    rw [blistBody, symDerives_seqG_cons] at hbody
    obtain ⟨b₁, l₁, ρa, b₂, l₂, hA, hB, rfl, rfl⟩ := hbody
    rw [symDerives_seqG_cons] at hA
    obtain ⟨c₁, m₁, ρc, c₂, m₂, hA1, hA2, rfl, rfl⟩ := hA
    rw [symDerives_seqG_nil] at hA2
    obtain ⟨rfl, rfl, rfl⟩ := hA2
    rw [symDerives_attrG] at hA1
    obtain ⟨u, ρu, hbu, hm1, hmu⟩ := hA1
    rw [symDerives_varG_scope hbu] at hmu
    obtain ⟨m, hU, rfl⟩ :=
      (bu32_iff_u32 h.leb h.wrappers _ c₁ u).mp (gramRelSup_iff.mpr ⟨ρu, hbu⟩)
    have hρa : ρa = σ.bindVal "n" (Encode.toValue m) :=
      MatchExp.unique hmu (matchExp_case_var hn)
    subst hρa
    rw [symDerives_seqG_cons] at hB
    obtain ⟨d₁, n₁, ρd, d₂, n₂, hB1, hB2, rfl, rfl⟩ := hB
    rw [symDerives_seqG_nil] at hB2
    obtain ⟨rfl, rfl, rfl⟩ := hB2
    rw [symDerives_seqG_cons] at hB1
    obtain ⟨e₁, p₁, ρe, e₂, p₂, hI, hIn, rfl, rfl⟩ := hB1
    rw [symDerives_seqG_nil] at hIn
    obtain ⟨rfl, rfl, rfl⟩ := hIn
    rw [symDerives_iterG] at hI
    obtain ⟨rows, hrows, hcount, hvals, hbind⟩ := hI
    rw [rounds_blist (hnel _)] at hrows
    obtain ⟨ws, rfl, hseq⟩ := hrows
    obtain ⟨-, cv, hcv, hcnat⟩ := hcount
    rw [evalExp_varE_iff, hnn] at hcv
    obtain rfl : cv = Encode.toValue m := (Option.some_inj.mp hcv).symm
    have hlen : ws.length = m := (by simpa using hcnat : m = ws.length).symm
    obtain ⟨ρb, hmatch, hnil⟩ := hbind
    have hρ' : ρ' = ρb := hnil
    rw [show domSrc (Dom.mk "el" (Exp.varE "el*")) = Exp.varE "el*" from rfl,
      filterMap_head?_rounds] at hmatch
    obtain rfl : ρb = (σ.bindVal "n" (Encode.toValue m)).bindVal "el*" (.list ws) :=
      MatchExp.unique hmatch (matchExp_varE_of_none (hnels _))
    refine ⟨ws, c₁, e₁, hlen ▸ hU, hseq, by simp, ?_, ?_⟩
    · rw [hm1, hvals, hlen]
      simp [iterValue, List.map_map, map_fst_rounds]
    · rw [hρ', hlen]
  · rintro ⟨ws, cb, db, hU, hseq, rfl, rfl, rfl⟩
    rw [blistBody]
    refine symDerives_seqG_cons.mpr ⟨cb, [uNV ws.length], σ.bindVal "n"
      (Encode.toValue ws.length), db, [Value.list ws], ?_, ?_, rfl, rfl⟩
    · refine symDerives_seqG_cons.mpr ⟨cb, [uNV ws.length], _, [], [], ?_,
        symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil cb).symm,
        (List.append_nil _).symm⟩
      have hbu : SymDerives env σ (.varG "Bu32" []) cb [uNV ws.length] σ := by
        obtain ⟨ρ'', hd⟩ := gramRelSup_iff.mp
          ((bu32_iff_u32 h.leb h.wrappers σ cb (uNV ws.length)).mpr ⟨ws.length, hU, rfl⟩)
        rwa [symDerives_varG_scope hd] at hd
      exact symDerives_attrG.mpr ⟨uNV ws.length, σ, hbu, rfl, matchExp_case_var hn⟩
    · refine symDerives_seqG_cons.mpr ⟨db, [Value.list ws], _, [], [], ?_,
        symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil db).symm,
        (List.append_nil _).symm⟩
      refine symDerives_seqG_cons.mpr ⟨db, [Value.list ws], _, [], [], ?_,
        symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil db).symm,
        (List.append_nil _).symm⟩
      refine symDerives_iterG.mpr ⟨ws.map (fun w => (w, [w])), ?_, ?_, ?_, ?_⟩
      · exact (rounds_blist (hnel _)).mpr ⟨ws, rfl, hseq⟩
      · exact ⟨rfl, Encode.toValue ws.length, evalExp_varE_iff.mpr (hnn _), by simp⟩
      · simp [iterValue, List.map_map, map_fst_rounds]
      · refine ⟨_, ?_, rfl⟩
        rw [show domSrc (Dom.mk "el" (Exp.varE "el*")) = Exp.varE "el*" from rfl,
          filterMap_head?_rounds]
        exact matchExp_varE_of_none (v := Value.list ws) (hnels _)

/-- **`Blist(el, BY)` is `Silmaril.Wasm.Binary.Vec`.**  Both directions: the
byte strings the pinned `Blist` derives from a parameterless nonterminal `BY`,
with the values it assigns, are exactly a `Bu32` count followed by that many
derivations of `BY`, carrying the list of their values.

This is the L-attributed instance `Sem/Grammar.lean`'s module docstring
promises and that no file in this tree had exercised: the repetition count of
the second factor is the value the first factor bound, which is expressible
only because the framework's attribute is an environment transformer. -/
theorem blist_iff_vec {env : Env} (h : HasBlist env) (t : Typ) (y : IL.Id)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Blist" [.typA t, .gramA (.varG y [])]) bs v ↔
      ∃ ws, Vec (NtRel env y) bs ws ∧ v = .list ws := by
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    rw [symDerives_varG h.blist] at hd
    obtain ⟨-, p, hp, hpd⟩ := hd
    simp only [blistProds, List.mem_singleton] at hp
    subst hp
    obtain ⟨wargs, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, hev, hl⟩ := hpd
    rw [evalArgs_typA_gramA_iff] at hargs
    subst hargs
    rw [premsHold_nil_iff] at hprems
    subst hprems
    have hρ₀ : ρ₀ = blistScope ρ t y := (Option.some_inj.mp hbp).symm
    have hn : ρ₀.findVal? "n" = none := by rw [hρ₀]; rfl
    have hel : ρ₀.findVal? "el" = none := by rw [hρ₀]; rfl
    have hels : ρ₀.findVal? "el*" = none := by rw [hρ₀]; rfl
    rw [substSym_blistBody, symDerives_blistBody h hn hel hels] at hbody
    obtain ⟨ws, cb, db, hU, hseq, rfl, rfl, rfl⟩ := hbody
    refine ⟨ws, ⟨hU, hseq⟩, ?_⟩
    have : v' = .list ws := EvalExp.unique hev
      (evalExp_blistResult (by simp [VarEnv.findVal?, VarEnv.bindVal])
        (by simp [VarEnv.findVal?, VarEnv.bindVal]) rfl)
    simpa [this] using hl
  · rintro ⟨ws, hvec, rfl⟩
    obtain ⟨cb, db, hU, hseq, rfl⟩ :
        ∃ cb db, U32 cb ws.length ∧ Seq (NtRel env y) db ws ∧ bs = cb ++ db := by
      cases hvec with | mk hc hs => exact ⟨_, _, hc, hs, rfl⟩
    refine gramRelSup_iff.mpr ⟨ρ, (symDerives_varG h.blist).mpr
      ⟨rfl, _, List.mem_singleton.mpr rfl, ?_⟩⟩
    refine ⟨[.typ (resolveTyp ρ t), .gram (resolveSym ρ (.varG y []))], blistScope ρ t y,
      [uNV ws.length, .list ws],
      ((blistScope ρ t y).bindVal "n" (Encode.toValue ws.length)).bindVal "el*" (.list ws),
      ((blistScope ρ t y).bindVal "n" (Encode.toValue ws.length)).bindVal "el*" (.list ws),
      .list ws, evalArgs_typA_gramA_iff.mpr rfl, rfl, ?_, premsHold_nil, ?_, rfl⟩
    · rw [substSym_blistBody]
      exact (symDerives_blistBody h (blistScope_n ρ t y) (blistScope_el ρ t y)
        (blistScope_els ρ t y)).mpr ⟨ws, cb, db, hU, hseq, rfl, rfl, rfl⟩
    · exact evalExp_blistResult (by simp [VarEnv.findVal?, VarEnv.bindVal])
        (by simp [VarEnv.findVal?, VarEnv.bindVal]) rfl


/-! ## The section framing -/

/-- The two parameters and the grammar parameter of
`grammar Bsection_(N, grammar BX : en*) : en*`
(`5.4-binary.modules.spectec:9`).  The elaborator adds the *type* parameter
`en` that the surface syntax leaves implicit. -/
def bsectionParams : List Param :=
  [.expP "N" (.varT "N" []), .typP "en", .gramP "BX" [] (.iterT (.varT "en" []) .list)]

/-- The two productions of `grammar Bsection_`
(`5.4-binary.modules.spectec:10-11`), as elaborated.

**The side condition is not what was written.**  The source reads
`-- if len = ||BX||` — the declared size equals the number of bytes `BX`
derives — and the elaborated premise is `len = 0`.  See
`bsection_premise_is_len_zero` and the module docstring. -/
def bsectionProds : List IL.Prod :=
  [ .prodD [.expP "en*" (.iterT (.varT "en" []) .list), .expP "len" (.numT .natT)]
      (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "N"])) (.varG "Bbyte" [])],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "len"])) (.varG "Bu32" [])],
              .seqG [.attrG (.iterE (.varE "en") (.mk .list [.mk "en" (.varE "en*")]))
                (.varG "BX" [])]])
      (.iterE (.varE "en") (.mk .list [.mk "en" (.varE "en*")]))
      [.ifPr (.cmpE .eqOp .boolT (.varE "len") (.numE (.natN 0)))],
    .prodD [] .epsG (.listE []) [] ]

/-- The sole production of `grammar Bmagic : () = 0x00 0x61 0x73 0x6D => ()`
(`5.4-binary.modules.spectec:173`).  Four *raw bytes*. -/
def bmagicProds : List IL.Prod :=
  [ .prodD [] (.seqG [.seqG [.numG 0x00], .seqG [.numG 0x61], .seqG [.numG 0x73],
      .seqG [.numG 0x6D]]) (.projE (.tupE [.tupE [], .tupE []]) 1) [] ]

/-- The sole production of `grammar Bversion : () = 0x01 0x00 0x00 0x00 => ()`
(`5.4-binary.modules.spectec:174`).

**Errata #672 and #687 do not apply here.**  wasm-1.0 and wasm-2.0 write the
version field as a LEB128 `1:Bu32` (`specification/wasm-1.0/A-binary.spectec:527`
and `specification/wasm-2.0/A-binary.spectec:924`), which encodes it in one
byte; wasm-3.0 already writes the four little-endian bytes the format
prescribes, and `bversion_iff_version` is the proof that the elaborated
grammar derives exactly them. -/
def bversionProds : List IL.Prod :=
  [ .prodD [] (.seqG [.seqG [.numG 0x01], .seqG [.numG 0x00], .seqG [.numG 0x00],
      .seqG [.numG 0x00]]) (.projE (.tupE [.tupE [], .tupE []]) 1) [] ]

/-- The shape every one-line section grammar of §5.4 elaborates to:
`grammar Bxxxsec : t* = v*:Bsection_(N, Blist(Bxxx)) => v*`.  `x` is the
elaborated bound variable, `tv` the type it was given, `t` the element type
and `inner` the per-element grammar. -/
def secProds (x : IL.Id) (tv : Typ) (n : Nat) (t : Typ) (inner : IL.Id) : List IL.Prod :=
  [ .prodD [.expP (x ++ "*") (.iterT tv .list)]
      (.attrG (.iterE (.varE x) (.mk .list [.mk x (.varE (x ++ "*"))]))
        (.varG "Bsection_" [.expA (.numE (.natN n)), .typA t,
          .gramA (.varG "Blist" [.typA t, .gramA (.varG inner [])])]))
      (.iterE (.varE x) (.mk .list [.mk x (.varE (x ++ "*"))])) [] ]

/-- The sole production of `grammar Bcode : code = len:Bu32 code:Bfunc => code`
(`5.4-binary.modules.spectec:133-134`), as elaborated.  Its side condition is
written `-- if len = ||Bfunc||` and elaborates, like `Bsection_`'s, to
`len = 0`. -/
def bcodeProds : List IL.Prod :=
  [ .prodD [.expP "code" (.varT "code" []), .expP "len" (.numT .natT)]
      (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "len"])) (.varG "Bu32" [])],
              .seqG [.attrG (.varE "code") (.varG "Bfunc" [])]])
      (.varE "code")
      [.ifPr (.cmpE .eqOp .boolT (.varE "len") (.numE (.natN 0)))] ]

/-- The corrected wasm-3.0 script, as `Equiv/BinaryInstr.lean` abbreviates it. -/
noncomputable abbrev envM : Env := envOfScript IL.Binary51.wasm30binary51

/-- The §5.4 nonterminals this file reads, as the corrected script has them.
`#650` corrects `Bi32`, `Bi64`, `$cont` and `$utf8`, none of which §5.4
mentions, so every field below reads the same in the pinned script. -/
structure HasSecs (env : Env) : Prop where
  /-- `Bsection_` is the pinned one. -/
  bsection : env.findGram? "Bsection_"
    = some (bsectionParams, .iterT (.varT "en" []) .list, bsectionProds)
  /-- `Bmagic` is the pinned one. -/
  bmagic : env.findGram? "Bmagic" = some ([], .tupT [], bmagicProds)
  /-- `Bversion` is the pinned one. -/
  bversion : env.findGram? "Bversion" = some ([], .tupT [], bversionProds)
  /-- `Btypesec` (`5.4:28-29`). -/
  btypesec : env.findGram? "Btypesec"
    = some ([], .iterT (.varT "type" []) .list,
        secProds "ty" (.varT "type" []) 1 (.varT "type" []) "Btype")
  /-- `Bimportsec` (`5.4:37-38`). -/
  bimportsec : env.findGram? "Bimportsec"
    = some ([], .iterT (.varT "import" []) .list,
        secProds "im" (.varT "import" []) 2 (.varT "import" []) "Bimport")
  /-- `Bfuncsec` (`5.4:43-44`); the elaborator gives the bound variable the
  type `idx`, not `typeidx`. -/
  bfuncsec : env.findGram? "Bfuncsec"
    = some ([], .iterT (.varT "typeidx" []) .list,
        secProds "x" (.varT "idx" []) 3 (.varT "typeidx" []) "Btypeidx")
  /-- `Btablesec` (`5.4:53-54`). -/
  btablesec : env.findGram? "Btablesec"
    = some ([], .iterT (.varT "table" []) .list,
        secProds "tab" (.varT "table" []) 4 (.varT "table" []) "Btable")
  /-- `Bmemsec` (`5.4:62-63`). -/
  bmemsec : env.findGram? "Bmemsec"
    = some ([], .iterT (.varT "mem" []) .list,
        secProds "mem" (.varT "mem" []) 5 (.varT "mem" []) "Bmem")
  /-- `Bglobalsec` (`5.4:71-72`). -/
  bglobalsec : env.findGram? "Bglobalsec"
    = some ([], .iterT (.varT "global" []) .list,
        secProds "glob" (.varT "global" []) 6 (.varT "global" []) "Bglobal")
  /-- `Bexportsec` (`5.4:80-81`). -/
  bexportsec : env.findGram? "Bexportsec"
    = some ([], .iterT (.varT "export" []) .list,
        secProds "ex" (.varT "export" []) 7 (.varT "export" []) "Bexport")
  /-- `Belemsec` (`5.4:118-119`). -/
  belemsec : env.findGram? "Belemsec"
    = some ([], .iterT (.varT "elem" []) .list,
        secProds "elem" (.varT "elem" []) 9 (.varT "elem" []) "Belem")
  /-- `Bcodesec` (`5.4:136-137`). -/
  bcodesec : env.findGram? "Bcodesec"
    = some ([], .iterT (.varT "code" []) .list,
        secProds "code" (.varT "code" []) 10 (.varT "code" []) "Bcode")
  /-- `Bdatasec` (`5.4:147-148`). -/
  bdatasec : env.findGram? "Bdatasec"
    = some ([], .iterT (.varT "data" []) .list,
        secProds "data" (.varT "data" []) 11 (.varT "data" []) "Bdata")
  /-- `Bcode` (`5.4:133-134`), the second place the section-size notation
  `||…||` occurs. -/
  bcode : env.findGram? "Bcode" = some ([], .varT "code" [], bcodeProds)
  /-- `Btagsec` (`5.4:167-168`). -/
  btagsec : env.findGram? "Btagsec"
    = some ([], .iterT (.varT "tag" []) .list,
        secProds "tag" (.varT "tag" []) 13 (.varT "tag" []) "Btag")

/-- **Provenance.**  The corrected wasm-3.0 script defines §5.4's framing and
its twelve one-line section grammars exactly as transcribed above; the `rfl`
is checked by the kernel against
`Silmaril.SpecTec.IL.Binary51.wasm30binary51`. -/
theorem hasSecs_corrected : HasSecs envM :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Provenance.**  The pinned script reads the same. -/
theorem hasSecs_wasm30 : HasSecs (envOfScript Specs.wasm30) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- A sequence of singleton byte terminals derives exactly that byte string.
This is the shape `print.ml` gives a literal byte run such as `Bmagic`'s. -/
theorem symDerives_byteSeq {env : Env} {ρ ρ' : VarEnv} (ns : List Nat)
    (hns : ∀ n ∈ ns, n < 256) {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.seqG (ns.map (fun n => IL.Sym.seqG [.numG n]))) bs l ρ' ↔
      bs = ns.map UInt8.ofNat ∧
        l = ns.map (fun n => Value.num (.natN (UInt8.ofNat n).toNat)) ∧ ρ' = ρ := by
  induction ns generalizing bs l with
  | nil =>
      simp only [List.map_nil]
      exact symDerives_seqG_nil
  | cons n ns ih =>
      obtain ⟨hn, hns'⟩ := List.forall_mem_cons.mp hns
      rw [List.map_cons, symDerives_seqG_cons]
      constructor
      · rintro ⟨b₁, l₁, ρ₁, b₂, l₂, h₁, h₂, rfl, rfl⟩
        rw [symDerives_seqG_cons] at h₁
        obtain ⟨c₁, m₁, ρc, c₂, m₂, hb, hnil, rfl, rfl⟩ := h₁
        rw [symDerives_seqG_nil] at hnil
        obtain ⟨rfl, rfl, rfl⟩ := hnil
        rw [symDerives_numG hn] at hb
        obtain ⟨rfl, rfl, rfl⟩ := hb
        obtain ⟨rfl, rfl, rfl⟩ := (ih hns').mp h₂
        simp
      · rintro ⟨rfl, rfl, rfl⟩
        refine ⟨[UInt8.ofNat n], [.num (.natN (UInt8.ofNat n).toNat)], _, _, _, ?_,
          (ih hns').mpr ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
        exact symDerives_seqG_cons.mpr ⟨_, _, _, [], [],
          (symDerives_numG hn).mpr ⟨rfl, rfl, rfl⟩,
          symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm,
          (List.append_nil _).symm⟩

/-- A literal byte run has no grammar identifiers to substitute. -/
theorem substSyms_byteRun (σ : List (IL.Id × IL.Sym)) (ns : List Nat) :
    substSyms σ (ns.map (fun n => IL.Sym.seqG [.numG n]))
      = ns.map (fun n => IL.Sym.seqG [.numG n]) := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [substSyms, substSym, List.map_cons, ih]

/-- The value expression `()` that `print.ml` emits for the unit result of
`Bmagic` and `Bversion`: `proj (tup (tup) (tup)) 1`. -/
theorem evalExp_unitProj {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.projE (.tupE [.tupE [], .tupE []]) 1) (.tuple []) := by
  refine evalExp_projE_iff.mpr ⟨[.tuple [], .tuple []], ?_, by decide, rfl⟩
  refine evalExp_tupE_iff.mpr ⟨[.tuple [], .tuple []], ?_, rfl⟩
  refine evalExps_cons_iff.mpr ⟨_, _, evalExp_tupE_iff.mpr ⟨[], evalExps_nil_iff.mpr rfl, rfl⟩,
    evalExps_cons_iff.mpr ⟨_, _, evalExp_tupE_iff.mpr ⟨[], evalExps_nil_iff.mpr rfl, rfl⟩,
      evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩

/-- A parameterless, premise-free grammar with a single literal-byte-run
production derives exactly that byte string. -/
theorem symDerives_litRun {env : Env} {x : IL.Id} {t : Typ} {ns : List Nat}
    {e : Exp} {w : Value} (hns : ∀ n ∈ ns, n < 256)
    (hg : env.findGram? x = some ([], t,
      [.prodD [] (.seqG (ns.map (fun n => IL.Sym.seqG [.numG n]))) e []]))
    (he : EvalExp env VarEnv.empty e w) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG x []) bs v ↔ bs = ns.map UInt8.ofNat ∧ v = w := by
  have hsub : substSym (gramArgSubst [] ([] : List IL.Arg))
      (IL.Sym.seqG (ns.map (fun n => IL.Sym.seqG [.numG n])))
      = .seqG (ns.map (fun n => IL.Sym.seqG [.numG n])) := by
    rw [substSym, substSyms_byteRun]
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    rw [symDerives_varG hg] at hd
    obtain ⟨-, p, hp, hpd⟩ := hd
    simp only [List.mem_singleton] at hp
    subst hp
    obtain ⟨wargs, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, hev, hl⟩ := hpd
    rw [evalArgs_nil_iff] at hargs
    subst hargs
    obtain rfl : ρ₀ = VarEnv.empty := (Option.some_inj.mp hbp).symm
    rw [premsHold_nil_iff] at hprems
    subst hprems
    rw [hsub, symDerives_byteSeq ns hns] at hbody
    obtain ⟨rfl, -, rfl⟩ := hbody
    refine ⟨rfl, ?_⟩
    have hvw : v' = w := EvalExp.unique hev he
    simpa [hvw] using hl
  · rintro ⟨rfl, rfl⟩
    refine gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hg).mpr
      ⟨rfl, _, List.mem_singleton.mpr rfl, ?_⟩⟩
    refine ⟨[], VarEnv.empty, ns.map (fun n => Value.num (.natN (UInt8.ofNat n).toNat)),
      VarEnv.empty, VarEnv.empty, v, evalArgs_nil env ρ, rfl, ?_, premsHold_nil, he, rfl⟩
    rw [hsub]
    exact (symDerives_byteSeq ns hns).mpr ⟨rfl, rfl, rfl⟩

/-- **`Bmagic` is `Silmaril.Wasm.Binary.magic`**, both directions: it derives
the four bytes `00 61 73 6D` and nothing else, with the unit value. -/
theorem bmagic_iff_magic {env : Env} (h : HasSecs env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bmagic" []) bs v ↔ bs = magic ∧ v = .tuple [] :=
  symDerives_litRun (ns := [0x00, 0x61, 0x73, 0x6D]) (by decide) h.bmagic
    evalExp_unitProj ρ bs v

/-- **`Bversion` is `Silmaril.Wasm.Binary.version`**, both directions: it
derives the four raw bytes `01 00 00 00`.

This is the check the brief asks for: errata #672 (wasm-2.0) and #687
(wasm-1.0) report the version field written as a LEB128 `1:Bu32`, which
derives the single byte `01`.  wasm-3.0 does not have that defect. -/
theorem bversion_iff_version {env : Env} (h : HasSecs env) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bversion" []) bs v ↔ bs = version ∧ v = .tuple [] :=
  symDerives_litRun (ns := [0x01, 0x00, 0x00, 0x00]) (by decide) h.bversion
    evalExp_unitProj ρ bs v


/-! ## The `en*:BX` pattern and value expression of a section -/

/-- Matching a variable that is already bound is a *check*, not a binding
(`spectec/src/il/eval.ml:887-890`). -/
theorem matchExp_varE_of_some_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v w : Value}
    (h : ρ.findVal? x = some w) :
    MatchExp env ρ (.varE x) v ρ' ↔ v = w ∧ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        by_cases hw : w = v
        · refine ⟨hw.symm, ?_⟩
          have hok : (Except.ok ρ : Res VarEnv) = .ok ρ' := by
            simpa [matchExp, h, hw] using hn
          simpa using hok.symm
        · exact absurd hn (by simp [matchExp, h, hw])
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, by simp [matchExp, h]⟩

/-- Matching `%(x)` against `%(w)` with `x` already bound to `w`. -/
theorem matchExp_case_var_check {env : Env} {ρ : VarEnv} {op : MixopS} {x : IL.Id}
    {w : Value} (h : ρ.findVal? x = some w) :
    MatchExp env ρ (.caseE op (.tupE [.varE x])) (.case op (.tuple [w])) ρ :=
  ⟨4, by simp [matchExp, matchExps, Value.asCase?, Value.asTuple?, h]⟩

/-- One column of the rounds of a one-domain `.list` match. -/
theorem iterCol_singletons (vs : List Value) :
    iterCol (vs.map (fun v => [v])) 0 = vs := by
  induction vs with
  | nil => rfl
  | cons v us ih => simp [iterCol]

/-- Matching the body `x` of a one-domain `.list` iteration, once per element
(`spectec/src/il/eval.ml:1008-1017`). -/
theorem matchRounds_var {env : Env} {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "_")
    (hfresh : ρ.findVal? x = none) :
    ∀ (vs : List Value) (i k : Nat),
      matchRounds (vs.length + k + 2) env ρ (.varE x) [x] none i vs
        = .ok (vs.map (fun v => [v])) := by
  intro vs
  induction vs with
  | nil => intro i k; simp [matchRounds]
  | cons v vs ih =>
      intro i k
      have hfuel : (v :: vs).length + k + 2 = (vs.length + k + 2) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hfuel, matchRounds]
      have hme : matchExp (vs.length + k + 2) env ρ (.varE x) v = .ok (ρ.bindVal x v) := by
        rw [show vs.length + k + 2 = (vs.length + k + 1) + 1 from rfl, matchExp, hfresh]
      have hrow : (ρ.bindVal x v).findVals? [x] = some [v] := by
        simp [VarEnv.findVals?, VarEnv.findVal?, VarEnv.bindVal, hx]
      simp [hme, hrow, ih (i + 1) k]

/-- Matching the `.list` iteration pattern `(x)*` whose single domain is the
pattern variable `xs`: the whole list is bound to `xs`. -/
theorem matchExp_iterList_var {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_")
    (hfx : ρ.findVal? x = none) (hfxs : ρ.findVal? xs = none)
    (vs : List Value) :
    MatchExp env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) (.list vs)
      (ρ.bindVal xs (.list vs)) := by
  refine ⟨vs.length + 6, ?_⟩
  rw [matchExp, matchIterE]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?]
  refine ⟨vs, rfl, ?_⟩
  rw [matchIterList]
  simp only [Res.bind_eq_ok]
  refine ⟨vs.map (fun v => [v]), ?_, ?_⟩
  · exact matchRounds_var hx hfx vs 0 1
  · have hcols : iterCols (vs.map (fun v => [v])) [Dom.mk x (Exp.varE xs)].length
        = [Value.list vs] := by
      simp [iterCols, iterCol_singletons]
    rw [hcols, show List.map domSrc [Dom.mk x (Exp.varE xs)] = [Exp.varE xs] from rfl,
      matchExps]
    simp only [Res.bind_eq_ok]
    exact ⟨ρ.bindVal xs (.list vs), by simp [matchExp, hfxs], by simp [matchExps]⟩

/-- The value of a one-domain `.list` iteration whose body is the domain
variable: the list the domain is bound to. -/
theorem evalExp_iterList_var {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? xs = some (.list vs)) :
    EvalExp env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) (.list vs) := by
  refine evalExp_iterE_iff.mpr ⟨4, ?_⟩
  have hdoms : evalDoms 3 env ρ [.mk x (.varE xs)] = .ok [(x, Value.list vs)] := by
    simp [evalDoms, domVar, domSrc, evalExp, h]
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, Value.asList?,
    List.isEmpty_cons]
  refine ⟨[(x, Value.list vs)], rfl, trivial, vs.length, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
    List.mapM_nil]
  refine ⟨[(x, vs)], by simp [Value.asList?], by simp, vs, ?_, rfl⟩
  rw [iterRows_single]
  exact evalRounds_single env ρ x hx vs 0


/-! ## `Bsection_`, as the elaborator emits it -/

/-- The relation the **elaborated** `Bsection_(N, BX)` denotes: the id byte,
the declared size, the contents, or nothing at all.

This is `Silmaril.Wasm.Binary.Section` with the side condition
`len = ||BX||` replaced by `len = 0`, which is what
`specs/spectec/wasm-3.0.ast` actually contains — see `bsectionProds` and the
module docstring. -/
inductive SectionZero (N : UInt8) {α : Type} (G : Grammar.Bytes → List α → Prop) :
    Grammar.Bytes → List α → Prop where
  /-- Id byte, a `Bu32` that must be **zero**, contents. -/
  | mk {lb c : Grammar.Bytes} {vs : List α} (hl : U32 lb 0) (hc : G c vs) :
      SectionZero N G (N :: (lb ++ c)) vs
  /-- The section is absent. -/
  | empty : SectionZero N G [] []

/-- The body of `Bsection_`'s first production, with the grammar argument
substituted for `BX`. -/
def bsectionBody (g : IL.Sym) : IL.Sym :=
  .seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "N"])) (.varG "Bbyte" [])],
         .seqG [.attrG (.caseE "%" (.tupE [.varE "len"])) (.varG "Bu32" [])],
         .seqG [.attrG (.iterE (.varE "en") (.mk .list [.mk "en" (.varE "en*")])) g]]

/-- `substSym` turns the printed body into `bsectionBody`; checked by the
kernel. -/
theorem substSym_bsectionBody (N : Nat) (t : Typ) (g : IL.Sym) :
    substSym (gramArgSubst bsectionParams
        [IL.Arg.expA (.numE (.natN N)), .typA t, .gramA g])
      (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "N"])) (.varG "Bbyte" [])],
              .seqG [.attrG (.caseE "%" (.tupE [.varE "len"])) (.varG "Bu32" [])],
              .seqG [.attrG (.iterE (.varE "en") (.mk .list [.mk "en" (.varE "en*")]))
                (.varG "BX" [])]])
      = bsectionBody g := rfl

/-- The fresh scope `Bsection_`'s first production starts in: the id `N`, the
element type and the content grammar, bound in `VarEnv.empty`. -/
def bsectionScope (ρ : VarEnv) (N : Nat) (t : Typ) (g : IL.Sym) : VarEnv :=
  ((VarEnv.empty.bindVal "N" (.num (.natN N))).bindTyp "en" (resolveTyp ρ t)).bindGram "BX"
    (resolveSym ρ g)

/-- `N` is bound to the section id in `bsectionScope`. -/
theorem bsectionScope_N (ρ : VarEnv) (N : Nat) (t : Typ) (g : IL.Sym) :
    (bsectionScope ρ N t g).findVal? "N" = some (.num (.natN N)) := rfl

/-- `len` is fresh in `bsectionScope`. -/
theorem bsectionScope_len (ρ : VarEnv) (N : Nat) (t : Typ) (g : IL.Sym) :
    (bsectionScope ρ N t g).findVal? "len" = none := rfl

/-- An argument list of the shape `Bsection_`'s calls have. -/
theorem evalArgs_expA_typA_gramA_iff {env : Env} {ρ : VarEnv} {e : Exp} {t : Typ}
    {g : IL.Sym} {ws : List ArgV} :
    EvalArgs env ρ [.expA e, .typA t, .gramA g] ws ↔
      ∃ u, EvalExp env ρ e u ∧
        ws = [.val u, .typ (resolveTyp ρ t), .gram (resolveSym ρ g)] := by
  constructor
  · rintro ⟨n, h⟩
    match n, h with
    | 0, h => simp [evalArgs] at h
    | 1, h => simp [evalArgs, evalArg] at h
    | n + 2, h =>
        cases hu : evalExp n env ρ e with
        | error er => rw [evalArgs] at h; simp [evalArg, List.mapM_cons, hu] at h
        | ok u =>
            refine ⟨u, ⟨n, hu⟩, ?_⟩
            have hok : (Except.ok ws : Res (List ArgV))
                = .ok [ArgV.val u, .typ (resolveTyp ρ t), .gram (resolveSym ρ g)] := by
              rw [← h, evalArgs]
              simp [evalArg, List.mapM_cons, hu]
            simpa using hok
  · rintro ⟨u, ⟨n, hu⟩, rfl⟩
    refine ⟨n + 2, ?_⟩
    simp [evalArgs, evalArg, List.mapM_cons, hu]

/-- A `.list` iteration pattern only matches a list value. -/
theorem matchExp_iterE_list_asList {env : Env} {ρ ρ' : VarEnv} {e : Exp} {ds : List Dom}
    {v : Value} (h : MatchExp env ρ (.iterE e (.mk .list ds)) v ρ') :
    ∃ vs, v = .list vs := by
  obtain ⟨n, hn⟩ := h
  match n, hn with
  | 0, hn => simp [matchExp] at hn
  | 1, hn => simp [matchExp, matchIterE] at hn
  | n + 2, hn =>
      rw [matchExp, matchIterE] at hn
      obtain ⟨vs, hvs, -⟩ := Res.bind_eq_ok.mp hn
      refine ⟨vs, ?_⟩
      cases v <;> simp [Value.asList?] at hvs ⊢
      exact hvs

/-- The premise `len = 0`, evaluated. -/
theorem evalExp_len_eq_zero_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {m : Nat}
    (h : ρ.findVal? x = some (.num (.natN m))) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.varE x) (.numE (.natN 0))) (.bool true) ↔ m = 0 := by
  rw [evalExp_cmpE_iff]
  constructor
  · rintro ⟨v₁, v₂, h₁, h₂, hc⟩
    rw [evalExp_varE_iff, h, Option.some_inj] at h₁
    rw [evalExp_numE_iff] at h₂
    subst h₁
    subst h₂
    simp only [cmpValues, Except.ok.injEq, Value.bool.injEq, beq_iff_eq, Value.num.injEq] at hc
    simpa using hc
  · rintro rfl
    exact ⟨.num (.natN 0), .num (.natN 0), evalExp_varE_iff.mpr h, evalExp_numE_iff.mpr rfl,
      by simp [cmpValues]⟩


/-- **`Bsection_(N, BX)` is `SectionZero N R`** whenever `BX` denotes the
list-valued relation `R`.  Both directions.

This is the generic section framing of §5.4, and the one place where the
L-attributed machinery of `Sem/Grammar.lean` has to carry a *value* from one
factor of a sequence to a later one: `len:Bu32` binds `len`, and the premise
reads it.  It does carry it — and what the premise then says is `len = 0`. -/
theorem bsection_iff {env : Env} (hs : HasSecs env) (hl : HasLeb env) (hw : HasWrappers env)
    {N : Nat} (hN : N < 256) {t : Typ} {gname : IL.Id} {gargs : List IL.Arg}
    {R : Grammar.Bytes → List Value → Prop}
    (hgy : ∀ (σ : VarEnv) (c : Grammar.Bytes) (u : Value),
      gramRelSup env σ (.varG gname gargs) c u ↔ ∃ l, R c l ∧ u = .list l)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bsection_"
        [.expA (.numE (.natN N)), .typA t, .gramA (.varG gname gargs)]) bs v ↔
      ∃ ws, SectionZero (UInt8.ofNat N) R bs ws ∧ v = .list ws := by
  have hNback : (UInt8.ofNat N).toNat = N := by
    simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt hN
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    rw [symDerives_varG hs.bsection] at hd
    obtain ⟨-, p, hp, hpd⟩ := hd
    simp only [bsectionProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · -- the framed production
      obtain ⟨wargs, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, hev, hlv⟩ := hpd
      rw [evalArgs_expA_typA_gramA_iff] at hargs
      obtain ⟨u0, hu0, rfl⟩ := hargs
      obtain rfl : u0 = .num (.natN N) := evalExp_numE_iff.mp hu0
      obtain rfl : ρ₀ = bsectionScope ρ N t (.varG gname gargs) :=
        (Option.some_inj.mp hbp).symm
      rw [substSym_bsectionBody, bsectionBody, symDerives_seqG_cons] at hbody
      obtain ⟨b₁, l₁, ρa, r₁, m₁, hA, hR, rfl, rfl⟩ := hbody
      -- the id byte
      rw [symDerives_seqG_cons] at hA
      obtain ⟨c₁, n₁, ρc, c₂, n₂, hA1, hA2, rfl, rfl⟩ := hA
      rw [symDerives_seqG_nil] at hA2
      obtain ⟨rfl, rfl, rfl⟩ := hA2
      rw [symDerives_attrG] at hA1
      obtain ⟨uid, ρu, hbb, -, hmid⟩ := hA1
      rw [symDerives_varG_scope hbb] at hmid
      obtain ⟨cb, hcb, rfl⟩ := (bbyte_iff_byte hl _ c₁ uid).mp (gramRelSup_iff.mpr ⟨ρu, hbb⟩)
      cases hcb
      obtain ⟨wid, hwid, hmid'⟩ := matchExp_case_var_elim hmid
      rw [matchExp_varE_of_some_iff (bsectionScope_N ρ N t _)] at hmid'
      obtain ⟨hwN, rfl⟩ := hmid'
      obtain rfl : cb = UInt8.ofNat N := by
        have hcn : cb.toNat = N := by
          have hx := hwid
          simp only [toValue_uint8, percentV_eq, Value.case.injEq, Value.tuple.injEq,
            List.cons.injEq] at hx
          rw [hwN] at hx
          simpa using hx.2.1
        exact UInt8.toNat_inj.1 (by rw [hcn, hNback])
      -- the declared size
      rw [symDerives_seqG_cons] at hR
      obtain ⟨b₂, l₂, ρb, r₂, m₂, hB, hC, rfl, rfl⟩ := hR
      rw [symDerives_seqG_cons] at hB
      obtain ⟨d₁, p₁, ρd, d₂, p₂, hB1, hB2, rfl, rfl⟩ := hB
      rw [symDerives_seqG_nil] at hB2
      obtain ⟨rfl, rfl, rfl⟩ := hB2
      rw [symDerives_attrG] at hB1
      obtain ⟨ulen, ρw, hbu, -, hmlen⟩ := hB1
      rw [symDerives_varG_scope hbu] at hmlen
      obtain ⟨m, hm, rfl⟩ := (bu32_iff_u32 hl hw _ d₁ ulen).mp (gramRelSup_iff.mpr ⟨ρw, hbu⟩)
      obtain rfl : ρb = (bsectionScope ρ N t (.varG gname gargs)).bindVal "len"
          (Encode.toValue m) :=
        MatchExp.unique hmlen (matchExp_case_var (bsectionScope_len ρ N t _))
      -- the contents
      rw [symDerives_seqG_cons] at hC
      obtain ⟨e₁, q₁, ρe, e₂, q₂, hC1, hC2, rfl, rfl⟩ := hC
      rw [symDerives_seqG_nil] at hC2
      obtain ⟨rfl, rfl, rfl⟩ := hC2
      rw [symDerives_seqG_cons] at hC1
      obtain ⟨f₁, s₁, ρf, f₂, s₂, hC1, hC1n, rfl, rfl⟩ := hC1
      rw [symDerives_seqG_nil] at hC1n
      obtain ⟨rfl, rfl, rfl⟩ := hC1n
      rw [symDerives_attrG] at hC1
      obtain ⟨ucon, ρx, hinner, -, hmcon⟩ := hC1
      rw [symDerives_varG_scope hinner] at hmcon
      obtain ⟨ws, hws, rfl⟩ := (hgy _ f₁ ucon).mp (gramRelSup_iff.mpr ⟨ρx, hinner⟩)
      obtain rfl : ρ₁ = _ :=
        MatchExp.unique hmcon (matchExp_iterList_var (by decide) rfl rfl ws)
      -- the premise, and the value
      rw [premsHold_ifPr_iff, evalExp_len_eq_zero_iff (by rfl)] at hprems
      obtain ⟨rfl, rfl⟩ := hprems
      have hv' : v' = .list ws := EvalExp.unique hev (evalExp_iterList_var (by decide) rfl)
      refine ⟨ws, ?_, ?_⟩
      · simpa using SectionZero.mk (N := UInt8.ofNat N) hm hws
      · simpa [hv'] using hlv
    · -- the `eps` production
      obtain ⟨wargs, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, hev, hlv⟩ := hpd
      rw [show substSym (gramArgSubst bsectionParams
          [IL.Arg.expA (.numE (.natN N)), .typA t, .gramA (.varG gname gargs)]) IL.Sym.epsG
        = IL.Sym.epsG from rfl] at hbody
      rw [symDerives_epsG] at hbody
      obtain ⟨rfl, -, rfl⟩ := hbody
      rw [premsHold_nil_iff] at hprems
      subst hprems
      have hv' : v' = .list [] :=
        EvalExp.unique hev (evalExp_listE_iff.mpr ⟨[], evalExps_nil_iff.mpr rfl, rfl⟩)
      exact ⟨[], .empty, by simpa [hv'] using hlv⟩
  · rintro ⟨ws, hsec, rfl⟩
    cases hsec with
    | @mk lb c _ hlb hc =>
        refine gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hs.bsection).mpr
          ⟨rfl, _, List.mem_cons_self .., ?_⟩⟩
        refine ⟨[.val (.num (.natN N)), .typ (resolveTyp ρ t),
            .gram (resolveSym ρ (.varG gname gargs))],
          bsectionScope ρ N t (.varG gname gargs),
          [Encode.toValue (UInt8.ofNat N)] ++ ([uNV 0] ++ [Value.list ws]),
          ((bsectionScope ρ N t (.varG gname gargs)).bindVal "len" (Encode.toValue 0)).bindVal
            "en*" (Value.list ws),
          ((bsectionScope ρ N t (.varG gname gargs)).bindVal "len" (Encode.toValue 0)).bindVal
            "en*" (Value.list ws), Value.list ws,
          evalArgs_expA_typA_gramA_iff.mpr ⟨_, evalExp_numE_iff.mpr rfl, rfl⟩, rfl, ?_, ?_, ?_,
          rfl⟩
        · rw [substSym_bsectionBody, bsectionBody]
          refine symDerives_seqG_cons.mpr ⟨[UInt8.ofNat N], [Encode.toValue (UInt8.ofNat N)],
            bsectionScope ρ N t (.varG gname gargs), lb ++ c,
            [uNV 0] ++ [Value.list ws], ?_, ?_, rfl, rfl⟩
          · refine symDerives_seqG_cons.mpr ⟨[UInt8.ofNat N], [Encode.toValue (UInt8.ofNat N)],
              bsectionScope ρ N t (.varG gname gargs), [], [], ?_,
              symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm,
              (List.append_nil _).symm⟩
            refine symDerives_attrG.mpr ⟨Encode.toValue (UInt8.ofNat N),
              bsectionScope ρ N t (.varG gname gargs), ?_, rfl, ?_⟩
            · obtain ⟨ρ'', hd⟩ := gramRelSup_iff.mp
                ((bbyte_iff_byte hl (bsectionScope ρ N t (.varG gname gargs)) [UInt8.ofNat N]
                  (Encode.toValue (UInt8.ofNat N))).mpr ⟨UInt8.ofNat N, .mk _, rfl⟩)
              rwa [symDerives_varG_scope hd] at hd
            · rw [show Encode.toValue (UInt8.ofNat N)
                  = Value.case "%" (.tuple [.num (.natN N)]) by
                simp [toValue_uint8, percentV_eq, hNback]]
              exact matchExp_case_var_check (bsectionScope_N ρ N t _)
          · refine symDerives_seqG_cons.mpr ⟨lb, [uNV 0],
              (bsectionScope ρ N t (.varG gname gargs)).bindVal "len" (Encode.toValue 0),
              c, [Value.list ws], ?_, ?_, rfl, rfl⟩
            · refine symDerives_seqG_cons.mpr ⟨lb, [uNV 0],
                (bsectionScope ρ N t (.varG gname gargs)).bindVal "len" (Encode.toValue 0),
                [], [], ?_, symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm,
                (List.append_nil _).symm⟩
              refine symDerives_attrG.mpr ⟨uNV 0, bsectionScope ρ N t (.varG gname gargs), ?_,
                rfl, matchExp_case_var (bsectionScope_len ρ N t _)⟩
              obtain ⟨ρ'', hd⟩ := gramRelSup_iff.mp
                ((bu32_iff_u32 hl hw (bsectionScope ρ N t (.varG gname gargs)) lb (uNV 0)).mpr
                  ⟨0, hlb, rfl⟩)
              rwa [symDerives_varG_scope hd] at hd
            · refine symDerives_seqG_cons.mpr ⟨c, [Value.list ws], _, [], [], ?_,
                symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm,
                (List.append_nil _).symm⟩
              refine symDerives_seqG_cons.mpr ⟨c, [Value.list ws], _, [], [], ?_,
                symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm,
                (List.append_nil _).symm⟩
              refine symDerives_attrG.mpr ⟨Value.list ws,
                (bsectionScope ρ N t (.varG gname gargs)).bindVal "len" (Encode.toValue 0), ?_,
                rfl, matchExp_iterList_var (by decide) rfl rfl ws⟩
              obtain ⟨ρ'', hd⟩ := gramRelSup_iff.mp
                ((hgy ((bsectionScope ρ N t (.varG gname gargs)).bindVal "len"
                  (Encode.toValue 0)) c (Value.list ws)).mpr ⟨ws, hc, rfl⟩)
              rwa [symDerives_varG_scope hd] at hd
        · exact premsHold_ifPr_iff.mpr ⟨(evalExp_len_eq_zero_iff (by rfl)).mpr rfl, rfl⟩
        · exact evalExp_iterList_var (by decide) rfl
    | empty =>
        refine gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hs.bsection).mpr
          ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩⟩
        refine ⟨[.val (.num (.natN N)), .typ (resolveTyp ρ t),
            .gram (resolveSym ρ (.varG gname gargs))],
          bsectionScope ρ N t (.varG gname gargs), [],
          bsectionScope ρ N t (.varG gname gargs),
          bsectionScope ρ N t (.varG gname gargs), .list [],
          evalArgs_expA_typA_gramA_iff.mpr ⟨_, evalExp_numE_iff.mpr rfl, rfl⟩, rfl,
          symDerives_epsG.mpr ⟨rfl, rfl, rfl⟩, premsHold_nil,
          evalExp_listE_iff.mpr ⟨[], evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩


/-! ## The individual sections -/

/-- A one-line section grammar `Bxxxsec : t* = v*:Bsection_(N, Blist(Bxxx)) => v*`
denotes exactly what its `Bsection_` call does. -/
theorem secWrap_iff {env : Env} {sec x : IL.Id} (hx : x ≠ "_") (hxs : (x ++ "*") ≠ "_")
    {tv tsec t : Typ}
    {n : Nat} {inner : IL.Id} {S : Grammar.Bytes → List Value → Prop}
    (hg : env.findGram? sec = some ([], tsec, secProds x tv n t inner))
    (hfx : (VarEnv.empty.findVal? x) = none)
    (hfxs : (VarEnv.empty.findVal? (x ++ "*")) = none)
    (hsec : ∀ (σ : VarEnv) (c : Grammar.Bytes) (u : Value),
      gramRelSup env σ (.varG "Bsection_" [.expA (.numE (.natN n)), .typA t,
        .gramA (.varG "Blist" [.typA t, .gramA (.varG inner [])])]) c u ↔
        ∃ l, S c l ∧ u = .list l)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG sec []) bs v ↔ ∃ ws, S bs ws ∧ v = .list ws := by
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    rw [symDerives_varG hg] at hd
    obtain ⟨-, p, hp, hpd⟩ := hd
    simp only [secProds, List.mem_singleton] at hp
    subst hp
    obtain ⟨wargs, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, hev, hlv⟩ := hpd
    rw [evalArgs_nil_iff] at hargs
    subst hargs
    obtain rfl : ρ₀ = VarEnv.empty := (Option.some_inj.mp hbp).symm
    rw [premsHold_nil_iff] at hprems
    rw [hprems] at hev
    rw [show substSym (gramArgSubst ([] : List Param) ([] : List IL.Arg))
        (IL.Sym.attrG (.iterE (.varE x) (.mk .list [.mk x (.varE (x ++ "*"))]))
          (.varG "Bsection_" [.expA (.numE (.natN n)), .typA t,
            .gramA (.varG "Blist" [.typA t, .gramA (.varG inner [])])]))
      = IL.Sym.attrG (.iterE (.varE x) (.mk .list [.mk x (.varE (x ++ "*"))]))
          (.varG "Bsection_" [.expA (.numE (.natN n)), .typA t,
            .gramA (.varG "Blist" [.typA t, .gramA (.varG inner [])])]) from rfl,
      symDerives_attrG] at hbody
    obtain ⟨u, ρu, hinner, -, hmu⟩ := hbody
    rw [symDerives_varG_scope hinner] at hmu
    obtain ⟨ws, hws, rfl⟩ := (hsec _ bs u).mp (gramRelSup_iff.mpr ⟨ρu, hinner⟩)
    obtain rfl : ρ₁ = VarEnv.empty.bindVal (x ++ "*") (.list ws) :=
      MatchExp.unique hmu (matchExp_iterList_var hx hfx hfxs ws)
    have hv' : v' = .list ws := EvalExp.unique hev
      (evalExp_iterList_var hx (by simp [VarEnv.findVal?, VarEnv.bindVal, hxs]))
    exact ⟨ws, hws, by simpa [hv'] using hlv⟩
  · rintro ⟨ws, hws, rfl⟩
    refine gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hg).mpr
      ⟨rfl, _, List.mem_singleton.mpr rfl, ?_⟩⟩
    refine ⟨[], VarEnv.empty, [Value.list ws],
      VarEnv.empty.bindVal (x ++ "*") (.list ws), VarEnv.empty.bindVal (x ++ "*") (.list ws),
      .list ws, evalArgs_nil env ρ, rfl, ?_, premsHold_nil,
      evalExp_iterList_var hx (by simp [VarEnv.findVal?, VarEnv.bindVal, hxs]), rfl⟩
    refine symDerives_attrG.mpr ⟨.list ws, VarEnv.empty, ?_, rfl,
      matchExp_iterList_var hx hfx hfxs ws⟩
    obtain ⟨ρ'', hd⟩ := gramRelSup_iff.mp ((hsec VarEnv.empty bs (.list ws)).mpr ⟨ws, hws, rfl⟩)
    rwa [symDerives_varG_scope hd] at hd

/-- `Bsection_(N, Blist(BY))`, composed: the elaborated section framing around
a vector of `BY`s. -/
theorem bsectionBlist_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    {N : Nat} (hN : N < 256) (t : Typ) (y : IL.Id) (ρ : VarEnv)
    (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bsection_" [.expA (.numE (.natN N)), .typA t,
        .gramA (.varG "Blist" [.typA t, .gramA (.varG y [])])]) bs v ↔
      ∃ ws, SectionZero (UInt8.ofNat N) (Vec (NtRel env y)) bs ws ∧ v = .list ws :=
  bsection_iff hs hb.leb hb.wrappers hN (fun σ c u => blist_iff_vec hb t y σ c u) ρ bs v

/-- The eleven `Bsection_(N, Blist(BX))` section grammars of §5.4, each read
as a `SectionZero` over a `Vec` of its element grammar.  One statement per
section; the only thing that varies is the id byte and the element
nonterminal. -/
theorem sec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    {sec x : IL.Id} (hx : x ≠ "_") (hxs : (x ++ "*") ≠ "_")
    {tv tsec t : Typ} {n : Nat} (hn : n < 256)
    {inner : IL.Id}
    (hg : env.findGram? sec = some ([], tsec, secProds x tv n t inner))
    (hfx : (VarEnv.empty.findVal? x) = none)
    (hfxs : (VarEnv.empty.findVal? (x ++ "*")) = none)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG sec []) bs v ↔
      ∃ ws, SectionZero (UInt8.ofNat n) (Vec (NtRel env inner)) bs ws ∧ v = .list ws :=
  secWrap_iff hx hxs hg hfx hfxs (fun σ c u => bsectionBlist_iff hs hb hn t inner σ c u) ρ bs v

/-- `Btypesec` (`5.4:28-29`). -/
theorem btypesec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Btypesec" []) bs v ↔
      ∃ ws, SectionZero 1 (Vec (NtRel env "Btype")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.btypesec rfl rfl ρ bs v

/-- `Bimportsec` (`5.4:37-38`). -/
theorem bimportsec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bimportsec" []) bs v ↔
      ∃ ws, SectionZero 2 (Vec (NtRel env "Bimport")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.bimportsec rfl rfl ρ bs v

/-- `Bfuncsec` (`5.4:43-44`). -/
theorem bfuncsec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bfuncsec" []) bs v ↔
      ∃ ws, SectionZero 3 (Vec (NtRel env "Btypeidx")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.bfuncsec rfl rfl ρ bs v

/-- `Btablesec` (`5.4:53-54`). -/
theorem btablesec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Btablesec" []) bs v ↔
      ∃ ws, SectionZero 4 (Vec (NtRel env "Btable")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.btablesec rfl rfl ρ bs v

/-- `Bmemsec` (`5.4:62-63`). -/
theorem bmemsec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bmemsec" []) bs v ↔
      ∃ ws, SectionZero 5 (Vec (NtRel env "Bmem")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.bmemsec rfl rfl ρ bs v

/-- `Bglobalsec` (`5.4:71-72`). -/
theorem bglobalsec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bglobalsec" []) bs v ↔
      ∃ ws, SectionZero 6 (Vec (NtRel env "Bglobal")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.bglobalsec rfl rfl ρ bs v

/-- `Bexportsec` (`5.4:80-81`). -/
theorem bexportsec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bexportsec" []) bs v ↔
      ∃ ws, SectionZero 7 (Vec (NtRel env "Bexport")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.bexportsec rfl rfl ρ bs v

/-- `Belemsec` (`5.4:118-119`). -/
theorem belemsec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Belemsec" []) bs v ↔
      ∃ ws, SectionZero 9 (Vec (NtRel env "Belem")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.belemsec rfl rfl ρ bs v

/-- `Bcodesec` (`5.4:136-137`). -/
theorem bcodesec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bcodesec" []) bs v ↔
      ∃ ws, SectionZero 10 (Vec (NtRel env "Bcode")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.bcodesec rfl rfl ρ bs v

/-- `Bdatasec` (`5.4:147-148`). -/
theorem bdatasec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bdatasec" []) bs v ↔
      ∃ ws, SectionZero 11 (Vec (NtRel env "Bdata")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.bdatasec rfl rfl ρ bs v

/-- `Btagsec` (`5.4:167-168`). -/
theorem btagsec_iff {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Btagsec" []) bs v ↔
      ∃ ws, SectionZero 13 (Vec (NtRel env "Btag")) bs ws ∧ v = .list ws :=
  sec_iff hs hb (by decide) (by decide) (by decide) hs.btagsec rfl rfl ρ bs v


/-! ## The finding: the section size is elaborated away -/

/-- A `Bu32` whose first byte is below `0x80` is that one byte
(`Silmaril/Wasm/Binary/Basic.lean`'s `UN.byte`). -/
theorem u32_cons_small {b : UInt8} {r : Grammar.Bytes} {m : Nat} (hb : b.toNat < 2 ^ 7)
    (h : U32 (b :: r) m) : r = [] ∧ m = b.toNat := by
  cases h with
  | byte n h₁ h₂ => exact ⟨rfl, rfl⟩
  | cont n h₁ h₂ rest => omega

/-- `01 01 00` — a type section of declared size 1 holding the empty vector —
is derived by **no** `SectionZero`, whatever its contents grammar, because the
declared size is not zero. -/
theorem not_sectionZero_01_01_00 {α : Type} {G : Grammar.Bytes → List α → Prop}
    {ws : List α} {bs : Grammar.Bytes} (hbs : bs = [0x01, 0x01, 0x00]) :
    ¬ SectionZero 1 G bs ws := by
  intro h
  cases h with
  | empty => simp at hbs
  | @mk lb c _ hl hc =>
      obtain ⟨b, lb', rfl⟩ : ∃ b lb', lb = b :: lb' := by
        cases lb with
        | nil => cases hl
        | cons b lb' => exact ⟨b, lb', rfl⟩
      obtain ⟨rfl, -⟩ : b = 0x01 ∧ lb' ++ c = [0x00] := by simpa using hbs
      obtain ⟨-, hm⟩ := u32_cons_small (b := 0x01) (by decide) hl
      exact absurd hm (by decide)

/-- `01 00 00` is derived by **no** `Silmaril.Wasm.Binary.Section`, whatever
its contents grammar, because the declared size `0` forces empty contents. -/
theorem not_section_01_00_00 {α : Type} {G : Grammar.Bytes → List α → Prop}
    {ws : List α} {bs : Grammar.Bytes} (hbs : bs = [0x01, 0x00, 0x00]) :
    ¬ Section 1 G bs ws := by
  intro h
  cases h with
  | empty => simp at hbs
  | @mk lb c _ _ hl hlen hc =>
      obtain ⟨b, lb', rfl⟩ : ∃ b lb', lb = b :: lb' := by
        cases lb with
        | nil => cases hl
        | cons b lb' => exact ⟨b, lb', rfl⟩
      obtain ⟨rfl, hrest⟩ : b = 0x00 ∧ lb' ++ c = [0x00] := by simpa using hbs
      obtain ⟨rfl, hm⟩ := u32_cons_small (b := 0x00) (by decide) hl
      simp only [List.nil_append] at hrest
      subst hrest
      simp [hm] at hlen

/-- `HasBlist` at the corrected wasm-3.0 script. -/
theorem hasBlist_corrected : HasBlist envM :=
  ⟨hasLeb_corrected, hasWrappers_corrected, hasBinTypes_wasm30binary51.blist⟩

/-- **The format's empty type section is not derivable.**  `01 01 00` is the
encoding of a module's empty type section — id `1`, declared size `1`,
contents the one-byte vector `00` — and the corrected wasm-3.0 specification
derives nothing at all from it.

The cause is `spectec/src/frontend/elab.ml:1284-1286`: the surface expression
`||BX||`, `SizeE` of `src/el/ast.ml:102`, elaborates to the literal `0`.  So
`Bsection_`'s side condition `-- if len = ||BX||`
(`specification/wasm-3.0/5.4-binary.modules.spectec:10`) becomes `len = 0` in
`specs/spectec/wasm-3.0.ast` — see `bsectionProds` and `hasSecs_corrected`. -/
theorem btypesec_misses_empty_type_section (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envM ρ (.varG "Btypesec" []) [0x01, 0x01, 0x00] v := by
  intro h
  obtain ⟨ws, hsec, -⟩ := (btypesec_iff hasSecs_corrected hasBlist_corrected ρ _ v).mp h
  exact not_sectionZero_01_01_00 rfl hsec

/-- …while the hand-written relation derives it, with the empty list of
types. -/
theorem typeSec_empty_type_section :
    Silmaril.Wasm.Binary.Core.TypeSec Silmaril.Wasm.Binary.Core.Forms.all [0x01, 0x01, 0x00] [] :=
  Section.mk (lb := [0x01]) (c := [0x00]) (UN.byte 0x01 (by decide) (by decide)) (by decide)
    (Vec.mk (UN.byte 0x00 (by decide) (by decide)) Seq.nil)

/-- **And the elaborated grammar derives a byte string the format rejects.**
`01 00 00` declares a type section of size `0` whose contents are one byte
long; the corrected specification accepts it, with the empty list of types. -/
theorem btypesec_derives_ill_formed (ρ : VarEnv) :
    gramRelSup envM ρ (.varG "Btypesec" []) [0x01, 0x00, 0x00] (.list []) :=
  (btypesec_iff hasSecs_corrected hasBlist_corrected ρ _ _).mpr
    ⟨[], SectionZero.mk (c := [0x00]) (UN.byte 0x00 (by decide) (by decide))
      (Vec.mk (UN.byte 0x00 (by decide) (by decide)) Seq.nil), rfl⟩

/-- …while the hand-written relation rejects it. -/
theorem not_typeSec_ill_formed :
    ¬ Silmaril.Wasm.Binary.Core.TypeSec Silmaril.Wasm.Binary.Core.Forms.all [0x01, 0x00, 0x00] [] :=
  not_section_01_00_00 rfl


/-! ## One section end to end: the function section -/

/-- `Seq`, transported along the `Encode` bridge. -/
theorem seq_toValue_iff {α : Type} [Encode α] {G : Grammar.Bytes → α → Prop}
    {bs : Grammar.Bytes} {us : List Value} :
    Seq (fun b u => ∃ a, G b a ∧ u = Encode.toValue a) bs us ↔
      ∃ ys : List α, Seq G bs ys ∧ us = ys.map Encode.toValue := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], .nil, rfl⟩
    | @cons b bs u us hu hus ih =>
        obtain ⟨ys, hys, rfl⟩ := ih
        obtain ⟨a, ha, rfl⟩ := hu
        exact ⟨a :: ys, .cons ha hys, rfl⟩
  · rintro ⟨ys, hys, rfl⟩
    induction hys with
    | nil => exact .nil
    | @cons b bs a ys ha hys ih => exact .cons ⟨a, ha, rfl⟩ ih

/-- `Vec`, transported along the `Encode` bridge. -/
theorem vec_toValue_iff {α : Type} [Encode α] {G : Grammar.Bytes → α → Prop}
    {bs : Grammar.Bytes} {us : List Value} :
    Vec (fun b u => ∃ a, G b a ∧ u = Encode.toValue a) bs us ↔
      ∃ ys : List α, Vec G bs ys ∧ us = ys.map Encode.toValue := by
  constructor
  · intro h
    cases h with
    | @mk n b xs hn hs =>
        obtain ⟨ys, hys, rfl⟩ := seq_toValue_iff.mp hs
        exact ⟨ys, .mk (by simpa using hn) hys, rfl⟩
  · rintro ⟨ys, hys, rfl⟩
    cases hys with
    | @mk n b _ hn hs =>
        exact .mk (by simpa using hn) (seq_toValue_iff.mpr ⟨ys, hs, rfl⟩)

/-- `SectionZero`, transported along the `Encode` bridge. -/
theorem sectionZero_toValue_iff {α : Type} [Encode α] {N : UInt8}
    {G : Grammar.Bytes → List α → Prop} {bs : Grammar.Bytes} {us : List Value} :
    SectionZero N (fun c l => ∃ ys, G c ys ∧ l = ys.map Encode.toValue) bs us ↔
      ∃ ys : List α, SectionZero N G bs ys ∧ us = ys.map Encode.toValue := by
  constructor
  · intro h
    cases h with
    | @mk lb c _ hl hc =>
        obtain ⟨ys, hys, rfl⟩ := hc
        exact ⟨ys, .mk hl hys, rfl⟩
    | empty => exact ⟨[], .empty, rfl⟩
  · rintro ⟨ys, hys, rfl⟩
    cases hys with
    | @mk lb c _ hl hc => exact .mk hl ⟨_, hc, rfl⟩
    | empty => exact .empty

/-- **`Btypeidx` is `Silmaril.Wasm.Binary.Index`**, ys a scope-free relation. -/
theorem ntRel_btypeidx {env : Env} (h : HasBinTypes env) (hl : HasLeb env)
    (bs : Grammar.Bytes) (u : Value) :
    NtRel env "Btypeidx" bs u ↔
      ∃ x : Wasm.TypeIdx, Index bs x ∧ u = Encode.toValue x := by
  rw [NtRel, gramRelSup_iff]
  constructor
  · rintro ⟨ρ', hd⟩
    obtain ⟨-, x, hx, hu⟩ := (symDerives_btypeidx h hl).mp hd
    exact ⟨x, hx, by simpa using hu⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨VarEnv.empty, (symDerives_btypeidx h hl).mpr ⟨rfl, x, hx, rfl⟩⟩

/-- **The function section, end to end.**  The corrected wasm-3.0 `Bfuncsec`
derives exactly the byte strings `SectionZero 3 (Vec Index)` does, with the
list of type indices transported along `Encode.toValue`.

`Silmaril.Wasm.Binary.Core.FuncSec` is `Section 3 (Vec Index)`
(`funcSec_eq_section`), so the two sides have the *same* contents relation
and differ in exactly one place: `Section` requires the declared size to be
the length of the contents, `SectionZero` requires it to be zero. -/
theorem bfuncsec_iff_sectionZero {env : Env} (hs : HasSecs env) (hb : HasBlist env)
    (ht : HasBinTypes env) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    gramRelSup env ρ (.varG "Bfuncsec" []) bs v ↔
      ∃ xs : List Wasm.TypeIdx, SectionZero 3 (Vec Index) bs xs ∧
        v = .list (xs.map Encode.toValue) := by
  have hnt : NtRel env "Btypeidx"
      = fun b u => ∃ x : Wasm.TypeIdx, Index b x ∧ u = Encode.toValue x := by
    funext b u
    exact propext (ntRel_btypeidx ht hb.leb b u)
  have hvec : (Vec (NtRel env "Btypeidx") : Grammar.Bytes → List Value → Prop)
      = fun c l => ∃ ys : List Wasm.TypeIdx, Vec Index c ys ∧ l = ys.map Encode.toValue := by
    funext c l
    rw [hnt]
    exact propext vec_toValue_iff
  rw [bfuncsec_iff hs hb ρ bs v, hvec]
  constructor
  · rintro ⟨ws, hsec, rfl⟩
    obtain ⟨xs, hxs, rfl⟩ := sectionZero_toValue_iff.mp hsec
    exact ⟨xs, hxs, rfl⟩
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs.map Encode.toValue, sectionZero_toValue_iff.mpr ⟨xs, hxs, rfl⟩, rfl⟩

/-- Silmaril's function section is the *same* framing with the *right* size
premise. -/
theorem funcSec_eq_section :
    Silmaril.Wasm.Binary.Core.FuncSec = Section 3 (Vec (Index (k := .type_))) := rfl


/-- **The same defect at `Bcode`.**  Every byte string the corrected
specification derives from `Bcode` begins with a `Bu32` encoding of **zero** —
the declared size of a function body, which the format says is the length of
that body.

This is the second occurrence of `||…||` in §5.4
(`specification/wasm-3.0/5.4-binary.modules.spectec:134`), and it elaborates
the same way.  Only this direction is proved: the converse would need
`Bfunc`, which goes through `Bexpr` and so through all 498 productions of
`Binstr`. -/
theorem bcode_size_is_zero {env : Env} (hs : HasSecs env) (hl : HasLeb env)
    (hw : HasWrappers env) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value)
    (h : gramRelSup env ρ (.varG "Bcode" []) bs v) :
    ∃ lb c, U32 lb 0 ∧ bs = lb ++ c := by
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
  rw [symDerives_varG hs.bcode] at hd
  obtain ⟨-, p, hp, hpd⟩ := hd
  simp only [bcodeProds, List.mem_singleton] at hp
  subst hp
  obtain ⟨wargs, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, hev, hlv⟩ := hpd
  rw [evalArgs_nil_iff] at hargs
  subst hargs
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some_inj.mp hbp).symm
  rw [show substSym (gramArgSubst ([] : List Param) ([] : List IL.Arg))
      (IL.Sym.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "len"])) (.varG "Bu32" [])],
        .seqG [.attrG (.varE "code") (.varG "Bfunc" [])]])
    = IL.Sym.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "len"])) (.varG "Bu32" [])],
        .seqG [.attrG (.varE "code") (.varG "Bfunc" [])]] from rfl,
    symDerives_seqG_cons] at hbody
  obtain ⟨b₁, l₁, ρa, b₂, l₂, hA, hB, rfl, -⟩ := hbody
  rw [symDerives_seqG_cons] at hA
  obtain ⟨c₁, m₁, ρc, c₂, m₂, hA1, hA2, rfl, rfl⟩ := hA
  rw [symDerives_seqG_nil] at hA2
  obtain ⟨rfl, rfl, rfl⟩ := hA2
  rw [symDerives_attrG] at hA1
  obtain ⟨ulen, ρu, hbu, -, hmlen⟩ := hA1
  rw [symDerives_varG_scope hbu] at hmlen
  obtain ⟨m, hm, rfl⟩ := (bu32_iff_u32 hl hw _ c₁ ulen).mp (gramRelSup_iff.mpr ⟨ρu, hbu⟩)
  obtain rfl : ρa = VarEnv.empty.bindVal "len" (Encode.toValue m) :=
    MatchExp.unique hmlen (matchExp_case_var rfl)
  rw [symDerives_seqG_cons] at hB
  obtain ⟨d₁, p₁, ρd, d₂, p₂, hB1, hB2, rfl, rfl⟩ := hB
  rw [symDerives_seqG_nil] at hB2
  obtain ⟨rfl, rfl, rfl⟩ := hB2
  rw [symDerives_seqG_cons] at hB1
  obtain ⟨f₁, s₁, ρf, f₂, s₂, hB1, hB1n, rfl, rfl⟩ := hB1
  rw [symDerives_seqG_nil] at hB1n
  obtain ⟨rfl, rfl, rfl⟩ := hB1n
  rw [symDerives_attrG] at hB1
  obtain ⟨ucode, ρx, hfn, -, hmcode⟩ := hB1
  rw [symDerives_varG_scope hfn] at hmcode
  obtain rfl : ρ₁ = (VarEnv.empty.bindVal "len" (Encode.toValue m)).bindVal "code" ucode :=
    MatchExp.unique hmcode (matchExp_varE_of_none rfl)
  rw [premsHold_ifPr_iff, evalExp_len_eq_zero_iff (by rfl)] at hprems
  obtain ⟨rfl, -⟩ := hprems
  exact ⟨c₁, f₁, hm, by simp⟩

end Silmaril.SpecTec.Equiv.BinaryModule
