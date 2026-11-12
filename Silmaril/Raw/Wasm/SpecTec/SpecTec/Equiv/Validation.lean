module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Bridge
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
public import Silmaril.Wasm.Validation.Context
public import Silmaril.Wasm.Validation.Instr.Parametric
public import Silmaril.Wasm.Validation.Instr.Numeric
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# SpecTec's typing relations against Silmaril's Wasm validation

Phase 4, the validation area.  `Silmaril/SpecTec/Sem/Eval.lean` gives every
`RelD` of the internal language a denotation — `derives`, the step-indexed
least fixpoint of its rules — and `Silmaril/Wasm/Validation/` is Silmaril's
hand-written transcription of §2.1–§2.3 of the WebAssembly 3.0 specification.
This file relates the two.

Every citation `2.1:n` is line `n` of
`specification/wasm-3.0/2.1-validation.types.spectec`, and likewise `2.0:n`,
`2.2:n` and `2.3:n`, all at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`.

## The correspondence

`tyV : {k : TKind} → Ty k → Value` encodes `Silmaril/Wasm/Validation/
DefTypes.lean`'s kind-indexed semantic types into `Sem/Value.lean`'s domain,
following `Sem/Bridge.lean`'s conventions.  The one thing worth stating
twice: SpecTec's *elaborated* `heaptype`, `valtype` and `storagetype` are
**flat** variants — `valtype` is `I32 | I64 | F32 | F64 | V128 | REF | BOT`
with no `numtype` wrapper (`1.2-syntax.types.spectec:49-52`, as the pinned
stream records it) — so the Lean subsorting constructors `Ty.dt`, `Ty.use`,
`Ty.refv` and `Ty.val` are **erased** by `tyV`.  `tyV_inj` is the statement
that nothing else is lost.

| SpecTec | Lean | encoding |
| --- | --- | --- |
| `numtype`, `vectype`, `packtype` | `NumType`, `VecType`, `PackType` | `numtypeV`, … |
| `absheaptype` | `AbsHeapType` | `absV` |
| `heaptype`, `typeuse`, `deftype` | `Ty .heap/.use/.def` | `tyV` |
| `reftype`, `valtype`, `storagetype`, `fieldtype` | `Ty .ref/.val/.storage/.field` | `tyV` |
| `comptype`, `subtype`, `rectype` | `Ty .comp/.sub/.group` | `tyV` |
| `resulttype = list(valtype)` | `List CValType` | `resulttypeV` |
| `context` | `Context` | `ctxV` |
| `instrtype` | `InstrType` | `instrtypeV` |
| `idx`, `u32`, `u64` | `Nat` | `idxV` |

A `context` is a thirteen-field record, and `Sem/Eval.lean`'s `matchExpFields`
pairs a record's fields *positionally* (`Sem/Bridge.lean`, "The record
convention"), so `ctxV` lists them in declaration order
(`2.0-validation.contexts.spectec:24-41`).  `ctxV_types_inj`,
`ctxV_recs_inj` and `ctxV_typeCtx_inj` say the encoding determines the two
fields the subtyping rules read.

## What is proved

**Machinery that belongs upstream.**  `Sem/Eval.lean` defines `derives` and
`anyRule` but supplies no inversion principle, and no `matchExp_*_iff` to go
with its `evalExp_*_iff`.  Both are built here and should move:

* `derives_iff` — `v` is derivable by `x` exactly when one rule of `x` fires;
* `matchExp_var_iff`, `matchExp_tup_iff`, `matchExp_case_iff`,
  `matchExp_list_iff`, `matchExp_sub_iff`, `matchExp_optNone_iff`,
  `matchExp_optSome_iff`, `matchExp_iterOptNil_iff`, `matchExps_nil_iff`,
  `matchExps_cons_iff`;
* `premsHold_nil_iff`, `premsHold_cons_iff`, `premHolds_rule_iff`,
  `premHolds_if_iff`, `evalExps_nil_iff`, `evalExps_cons_iff`,
  `evalArgs_nil_iff`.

**Provenance.**  `HasTyping` lists, one field per relation, the
`(params, mixop, type, rules)` quadruple the pinned stream contains for the
eighteen `RelD`s this file reaches; `hasTyping_wasm30` discharges it by `rfl`
against `Silmaril.SpecTec.Specs.wasm30`.  `HasInstrRules` does the same for
six individual rules of `Instr_ok`, by index.

**Subtyping, exactly, in both directions.**

| SpecTec | theorem | reads |
| --- | --- | --- |
| `Numtype_sub` (2.2:13) | `derives_numtypeSub_iff` | `v₁ = v₂` |
| `Vectype_sub` (2.2:16) | `derives_vectypeSub_iff` | `v₁ = v₂` |
| `Packtype_sub` (2.2:158) | `derives_packtypeSub_iff` | `v₁ = v₂` |
| `Reftype_sub` (2.2:105) | `derives_reftypeSub_ref_iff`, `…_shape` | nullability + `Heaptype_sub` |
| `Valtype_sub` (2.2:114) | `derives_valtypeSub_iff` | equal, or `Reftype_sub`, or `BOT` |
| `Storagetype_sub` (2.2:162) | `derives_storagetypeSub_iff` | `Valtype_sub`, or equal |
| `Fieldtype_sub` (2.2:171) | `derives_fieldtypeSub_iff` | co/invariance by mutability |

and, against Silmaril's `Sub`, modulo the single hypothesis `HeapSubAgree`
(agreement at the heap sort, which this file does not reach):

* `reftypeSub_agree` — `Reftype_sub` **is** `Sub` at the reference sort;
* `valtypeSub_agree` — `Valtype_sub` **is** `Sub` at the value sort;
* `storagetypeSub_agree` — `Storagetype_sub` is `Sub` **plus `StorageGap`**,
  exactly (see the finding below);
* `fieldtypeSub_agree` — `Fieldtype_sub` is `Sub` at the field sort away from
  that gap.

The Lean-side inversion principles those rest on (`sub_ref_iff`,
`sub_val_iff`, `sub_storage_iff`, `sub_field_iff`) are proved here too; they
belong in `Validation/Subtyping.lean`.

**Instruction typing.**  `ruleFires_instrOk_nop_iff`,
`…_drop_iff`, `…_const_iff`, `…_binop_iff`, `…_relop_iff` and
`…_localGet_iff` characterise, in both directions, exactly when each of six
`Instr_ok` rules fires; `derives_instrOk_nop`, `…_drop`, `…_intConst`,
`…_intBinOp`, `…_intRelOp` and `…_localGet` then turn a Silmaril derivation
into a SpecTec one.

## The finding: `derives` drops a rule's quantifiers

`RuleD` (`spectec/src/il/ast.ml:146`) carries a `quant list`
(`ast.ml:129`, `= param list`), and an `ExpP` quantifier (`ast.ml:124`)
carries the *declared type* of the variable it binds.  `Sem/Eval.lean`'s
`anyRule` ignores that list — a rule's binders are `_` in its pattern — and it
never consults `Sem/Type.lean`'s `HasTyp`.  Every §2.1 well-formedness rule
binds its subject with a bare `VarE` under a `SubE`, both of which `matchExp`
treats transparently (`eval.ml:1035-1068`), so the sort constraint is the
*only* thing standing between those rules and triviality.  Consequence, proved
rather than asserted:

* `derives_numtypeOk`, `derives_vectypeOk`, `derives_packtypeOk`,
  `derives_heaptypeOk`, `derives_valtypeOk`, `derives_storagetypeOk` hold of
  **every** pair of values;
* `valtypeOk_not_agree` — so `Valtype_ok` and Silmaril's `TyOk` do not agree,
  with `not_tyOk_refIdx` and `derives_valtypeOk_refIdx` the witness: the
  well-sorted value type `REF NULL (_IDX 0)` in the *empty* context;
* `derives_storagetypeSub_botv_pack` and `not_sub_botv_pack` — the same
  erasure makes `C ⊢ BOT <: I8` derivable at the storage sort, which
  `storagetypeSub_agree` measures as exactly `StorageGap`;
* `ruleFires_instrOk_localGet_iff` — `Instr_ok/local.get` reads its immediate
  with `x!%.0` and never checks that `x` is a one-component `%` injection.

The counterexamples are not ill-sorted values, so this is not repaired by
conjoining a top-level `HasTyp`: the fix belongs inside `anyRule`, which
should bind a rule's quantifiers and require each bound value to inhabit its
declared type.  Until then `derives` is an *over-approximation* of the
relation a `RelD` denotes, and every theorem here that goes from `derives` to
Silmaril is correspondingly conditional or restricted; every theorem that goes
the other way is unconditional.

## What is not reached

See the final section of this file.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.Validation

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Inversion for `derives` -/

/-- A definite answer is exactly an `Except.ok`. -/
theorem isOk_iff {α : Type} {r : Res α} : r.isOk = true ↔ ∃ a, r = .ok a := by
  cases r <;> simp [Except.isOk, Except.toBool]

/-- One rule of a relation fires at the given arguments and value. -/
def RuleFires (env : Env) (op : MixopS) (ps : List Param) (args : List ArgV)
    (v : Value) (r : Rule) : Prop :=
  ∃ (x : IL.Id) (q : List Param) (e : Exp) (prems : List Prem) (ρ₀ ρ₁ ρ₂ : VarEnv),
    r = .ruleD x q op e prems ∧
    bindParams VarEnv.empty ps args = some ρ₀ ∧
    MatchExp env ρ₀ e v ρ₁ ∧ PremsHold env ρ₁ prems ρ₂

/-- A rule at the head of the list that fires makes `anyRule` true. -/
theorem anyRule_head {env : Env} {op : MixopS} {ps : List Param} {args : List ArgV}
    {v : Value} {r : Rule} {rs : List Rule} (h : RuleFires env op ps args v r) :
    ∃ n, anyRule n env op ps args v (r :: rs) = true := by
  obtain ⟨x, q, e, prems, ρ₀, ρ₁, ρ₂, rfl, hb, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩ := h
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e1 := matchExp_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) h₁
  have e2 := premsHold_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) h₂
  simp only [anyRule, hb, Res.ofOption, e1, e2, Bind.bind, Except.bind, beq_self_eq_true,
    Bool.true_and, Except.isOk, Except.toBool, Bool.true_or]

/-- `anyRule` is monotone in the tail of the rule list. -/
theorem anyRule_tail {n : Nat} {env : Env} {op : MixopS} {ps : List Param}
    {args : List ArgV} {v : Value} {r : Rule} {rs : List Rule}
    (h : anyRule n env op ps args v rs = true) :
    anyRule (n + 1) env op ps args v (r :: rs) = true := by
  cases r with
  | ruleD x q op' e prems => simp only [anyRule, h, Bool.or_true]

/-- **Introduction**: any rule of the list that fires makes `anyRule` true. -/
theorem anyRule_of_mem {env : Env} {op : MixopS} {ps : List Param} {args : List ArgV}
    {v : Value} {rules : List Rule} {r : Rule} (hmem : r ∈ rules)
    (h : RuleFires env op ps args v r) :
    ∃ n, anyRule n env op ps args v rules = true := by
  induction rules with
  | nil => cases hmem
  | cons r' rs ih =>
      rcases List.mem_cons.1 hmem with rfl | hmem'
      · exact anyRule_head h
      · obtain ⟨n, hn⟩ := ih hmem'
        exact ⟨n + 1, anyRule_tail hn⟩

/-- **Elimination**: if `anyRule` is true then some rule of the list fires. -/
theorem ruleFires_of_anyRule : ∀ (n : Nat) (env : Env) (op : MixopS) (ps : List Param)
    (args : List ArgV) (v : Value) (rules : List Rule),
    anyRule n env op ps args v rules = true → ∃ r ∈ rules, RuleFires env op ps args v r
  | 0, _, _, _, _, _, _, h => by simp [anyRule] at h
  | _+1, _, _, _, _, _, [], h => by simp [anyRule] at h
  | n+1, env, op, ps, args, v, .ruleD x q op' e prems :: rs, h => by
      simp only [anyRule, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨rfl, hok⟩ | h
      · refine ⟨_, List.mem_cons_self .., ?_⟩
        rw [isOk_iff] at hok
        obtain ⟨ρ₂, hok⟩ := hok
        simp only [Bind.bind, Except.bind, Res.ofOption] at hok
        cases hb : bindParams VarEnv.empty ps args with
        | none => rw [hb] at hok; simp at hok
        | some ρ₀ =>
            rw [hb] at hok
            simp only at hok
            cases hm : matchExp n env ρ₀ e v with
            | error _ => rw [hm] at hok; simp at hok
            | ok ρ₁ =>
                rw [hm] at hok
                exact ⟨x, q, e, prems, ρ₀, ρ₁, ρ₂, rfl, hb, ⟨n, hm⟩, ⟨n, hok⟩⟩
      · obtain ⟨r, hr, hf⟩ := ruleFires_of_anyRule n env op ps args v rs h
        exact ⟨r, List.mem_cons_of_mem _ hr, hf⟩

/-- **The characterisation of `Derives`**: a value is derivable by a relation
exactly when one of the relation's rules fires at it.

This is the inversion principle `Silmaril/SpecTec/Sem/Eval.lean` does not
supply; it belongs there, next to `derives`. -/
theorem derives_iff {env : Env} {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} :
    Derives env x op args v ↔
      ∃ ps t rules, env.findRel? x = some (ps, op, t, rules) ∧
        ∃ r ∈ rules, RuleFires env op ps args v r := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [derives] at hn
    | succ n =>
        simp only [derives] at hn
        obtain ⟨d, hd⟩ : ∃ d, env.findRel? x = some d := by
          rcases h : env.findRel? x with _ | d
          · rw [h] at hn; simp at hn
          · exact ⟨d, rfl⟩
        obtain ⟨ps, op', t, rules⟩ := d
        rw [hd] at hn
        simp only [Bool.and_eq_true, beq_iff_eq] at hn
        obtain ⟨hop, hn⟩ := hn
        rw [hop] at hd
        exact ⟨ps, t, rules, hd, ruleFires_of_anyRule n env op ps args v rules hn⟩
  · rintro ⟨ps, t, rules, hr, r, hmem, hf⟩
    obtain ⟨n, hn⟩ := anyRule_of_mem hmem hf
    exact ⟨n + 1, by simp only [derives, hr, hn, beq_self_eq_true, Bool.true_and]⟩

/-! ## The value bridge for semantic types -/

open Silmaril.Wasm.Validation (TKind Ty TypeCtx Context LocalType Init CGlobalType
  CTableType CValType CHeapType CRefType CStorageType CFieldType CSubType DefType
  Sub TyOk ResultSub InstrType ParametricInstrOk NumericInstrOk)

/-- A natural number as an IL value (SpecTec `nat`). -/
def natV (n : Nat) : Value := .num (.natN n)

/-- `u32`, and hence every `idx`: a numeral in the one-case variant `%`. -/
def idxV (n : Nat) : Value := percentV (natV n)

/-- Prepend a value to a list value. -/
def consV (hd : Value) : Value → Value
  | .list vs => .list (hd :: vs)
  | _ => .list [hd]

/-- `null?`. -/
def nullV (b : Bool) : Value :=
  .opt (if b then some (.case "NULL" (.tuple [])) else none)

/-- `mut?`. -/
def mutV : Wasm.Mutability → Value
  | .const => .opt none
  | .var => .opt (some (.case "MUT" (.tuple [])))

/-- `final?`. -/
def finalV (b : Bool) : Value :=
  .opt (if b then some (.case "FINAL" (.tuple [])) else none)

/-- `absheaptype`. -/
def absV : Wasm.AbsHeapType → Value
  | .any => .case "ANY" (.tuple [])
  | .eq => .case "EQ" (.tuple [])
  | .i31 => .case "I31" (.tuple [])
  | .struct => .case "STRUCT" (.tuple [])
  | .array => .case "ARRAY" (.tuple [])
  | .none => .case "NONE" (.tuple [])
  | .func => .case "FUNC" (.tuple [])
  | .nofunc => .case "NOFUNC" (.tuple [])
  | .exn => .case "EXN" (.tuple [])
  | .noexn => .case "NOEXN" (.tuple [])
  | .extern => .case "EXTERN" (.tuple [])
  | .noextern => .case "NOEXTERN" (.tuple [])

/-- `numtype`. -/
def numtypeV : Wasm.NumType → Value
  | .int .i32 => .case "I32" (.tuple [])
  | .int .i64 => .case "I64" (.tuple [])
  | .float .f32 => .case "F32" (.tuple [])
  | .float .f64 => .case "F64" (.tuple [])

/-- `vectype`. -/
def vectypeV : Wasm.VecType → Value
  | .v128 => .case "V128" (.tuple [])

/-- `packtype`. -/
def packtypeV : Wasm.PackType → Value
  | .i8 => .case "I8" (.tuple [])
  | .i16 => .case "I16" (.tuple [])

/-- `addrtype`. -/
def addrV : Wasm.AddrType → Value
  | .i32 => .case "I32" (.tuple [])
  | .i64 => .case "I64" (.tuple [])

/-- Every semantic type of `Silmaril/Wasm/Validation/DefTypes.lean` as a value
of the corresponding SpecTec sort. -/
def tyV : {k : TKind} → Ty k → Value
  | _, .nil => .list []
  | _, .cons a l => consV (tyV a) (tyV l)
  | _, .idx x => .case "_IDX" (idxV x)
  | _, .recv i => .case "REC" (natV i)
  | _, .dt d => tyV d
  | _, .defn g i => .case "_DEF" (.tuple [tyV g, natV i])
  | _, .abs a => absV a
  | _, .bot => .case "BOT" (.tuple [])
  | _, .use u => tyV u
  | _, .ref n h => .case "REF" (.tuple [nullV n, tyV h])
  | _, .num t => numtypeV t
  | _, .vec t => vectypeV t
  | _, .refv r => tyV r
  | _, .botv => .case "BOT" (.tuple [])
  | _, .val t => tyV t
  | _, .pack p => packtypeV p
  | _, .field m s => .case "%%" (.tuple [mutV m, tyV s])
  | _, .struct fs => .case "STRUCT" (percentV (tyV fs))
  | _, .array f => .case "ARRAY" (tyV f)
  | _, .func ps rs => .case "FUNC%->%" (.tuple [percentV (tyV ps), percentV (tyV rs)])
  | _, .sub fin sups ct => .case "SUB" (.tuple [finalV fin, tyV sups, tyV ct])
  | _, .group subs => .case "REC" (percentV (tyV subs))

/-- A sequence encodes as the list of its elements' encodings. -/
theorem tyV_list : {k : TKind} → (t : Ty (.list k)) → tyV t = .list (t.toList.map tyV)
  | _, .nil => rfl
  | _, .cons a l => by
      simp only [tyV, Ty.toList_cons, List.map_cons, tyV_list l, consV]

/-- `resulttype = list(valtype)`. -/
def resulttypeV (ts : List (Ty .val)) : Value := percentV (.list (ts.map tyV))

/-! ### The encoding is injective

Every theorem below reads a SpecTec value back as a Lean type, so the encoding
has to determine its argument.  The subsorting constructors `Ty.dt`, `Ty.use`,
`Ty.refv` and `Ty.val` are *erased* by `tyV` — SpecTec's elaborator flattens
`heaptype = absheaptype | typeuse` into one variant — so injectivity is a
statement about the flattened variants, and it needs the head mixop of each
sort. -/

/-- The mixop at the head of an injection. -/
def headV : Value → Option MixopS
  | .case op _ => some op
  | _ => none

/-- `absheaptype` is injective. -/
theorem absV_inj {a b : Wasm.AbsHeapType} (h : absV a = absV b) : a = b := by
  cases a <;> cases b <;> simp_all [absV]

/-- `numtype` is injective. -/
theorem numtypeV_inj {a b : Wasm.NumType} (h : numtypeV a = numtypeV b) : a = b := by
  cases a <;> cases b <;> rename_i x y <;> cases x <;> cases y <;> simp_all [numtypeV]

/-- `packtype` is injective. -/
theorem packtypeV_inj {a b : Wasm.PackType} (h : packtypeV a = packtypeV b) : a = b := by
  cases a <;> cases b <;> simp_all [packtypeV]

/-- `null?` is injective. -/
theorem nullV_inj {a b : Bool} (h : nullV a = nullV b) : a = b := by
  cases a <;> cases b <;> simp_all [nullV]

/-- `final?` is injective. -/
theorem finalV_inj {a b : Bool} (h : finalV a = finalV b) : a = b := by
  cases a <;> cases b <;> simp_all [finalV]

/-- `mut?` is injective. -/
theorem mutV_inj {a b : Wasm.Mutability} (h : mutV a = mutV b) : a = b := by
  cases a <;> cases b <;> simp_all [mutV]

/-- A `deftype` always encodes as a `_DEF` injection. -/
theorem headV_dt (d : Ty .def) : headV (tyV d) = some "_DEF" := by cases d; rfl

/-- A `reftype` always encodes as a `REF` injection. -/
theorem headV_ref (r : Ty .ref) : headV (tyV r) = some "REF" := by cases r; rfl

/-- A `typeuse` encodes as one of three injections. -/
theorem headV_use (u : Ty .use) :
    headV (tyV u) = some "_IDX" ∨ headV (tyV u) = some "_DEF" ∨
      headV (tyV u) = some "REC" := by
  cases u with
  | idx => exact Or.inl rfl
  | recv => exact Or.inr (Or.inr rfl)
  | dt d => exact Or.inr (Or.inl (headV_dt d))

/-- No abstract heap type encodes as a type use. -/
theorem absV_ne_use (a : Wasm.AbsHeapType) (u : Ty .use) : absV a ≠ tyV u := by
  intro h
  rcases headV_use u with hu | hu | hu <;> rw [← h] at hu <;>
    cases a <;> simp [headV, absV] at hu

/-- The heap-type `BOT` does not encode as a type use. -/
theorem botV_ne_use (u : Ty .use) : Value.case "BOT" (.tuple []) ≠ tyV u := by
  intro h
  rcases headV_use u with hu | hu | hu <;> rw [← h] at hu <;> simp [headV] at hu

/-- No value type encodes as a packed type. -/
theorem tyVal_ne_pack (t : Ty .val) (p : Wasm.PackType) : tyV t ≠ packtypeV p := by
  cases t with
  | num nt => cases nt <;> rename_i x <;> cases x <;> cases p <;> simp [tyV, numtypeV, packtypeV]
  | vec vt => cases vt; cases p <;> simp [tyV, vectypeV, packtypeV]
  | refv r =>
      intro h
      have hr := headV_ref r
      simp only [tyV] at h
      rw [h] at hr
      cases p <;> simp [headV, packtypeV] at hr
  | botv => cases p <;> simp [tyV, packtypeV]

/-- **The encoding of a semantic type determines the type.**

The proof is one induction over `Ty`, with the subsorting constructors handled
by the head-mixop lemmas above. -/
theorem tyV_inj : ∀ {k : TKind} (a b : Ty k), tyV a = tyV b → a = b := by
  intro k a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons y m => rw [tyV_list, tyV_list] at h; simp at h
  | cons x l ihx ihl =>
      intro b h
      cases b with
      | nil => rw [tyV_list, tyV_list] at h; simp at h
      | cons y m =>
          rw [tyV_list, tyV_list] at h
          simp only [Ty.toList_cons, List.map_cons, Value.list.injEq, List.cons.injEq] at h
          have hl : tyV l = tyV m := by rw [tyV_list, tyV_list, h.2]
          rw [ihx y h.1, ihl m hl]
  | idx x =>
      intro b h
      cases b with
      | idx y =>
          simp only [tyV, idxV, percentV, caseV, natV] at h
          injection h with _ h; injection h with _ h; injection h with h
          injection h with h _; injection h with h; injection h with h
          rw [h]
      | recv j => simp [tyV] at h
      | dt d =>
          simp only [tyV] at h
          have hd := headV_dt d; rw [← h] at hd; simp [headV] at hd
  | recv i =>
      intro b h
      cases b with
      | idx y => simp [tyV] at h
      | recv j =>
          simp only [tyV, natV] at h
          injection h with _ h; injection h with h; injection h with h
          rw [h]
      | dt d =>
          simp only [tyV] at h
          have hd := headV_dt d; rw [← h] at hd; simp [headV] at hd
  | dt d ihd =>
      intro b h
      cases b with
      | idx y =>
          simp only [tyV] at h
          have hd := headV_dt d; rw [h] at hd; simp [headV] at hd
      | recv j =>
          simp only [tyV] at h
          have hd := headV_dt d; rw [h] at hd; simp [headV] at hd
      | dt d' => rw [ihd d' h]
  | defn g i ihg =>
      intro b h
      cases b with
      | defn g' i' =>
          simp only [tyV, natV] at h
          injection h with _ h; injection h with h
          injection h with hg h; injection h with hi _
          injection hi with hi; injection hi with hi
          rw [ihg g' hg, hi]
  | abs a =>
      intro b h
      cases b with
      | abs b' => rw [absV_inj h]
      | bot => simp only [tyV] at h; cases a <;> simp [absV] at h
      | use u => simp only [tyV] at h; exact absurd h (absV_ne_use a u)
  | bot =>
      intro b h
      cases b with
      | abs b' => simp only [tyV] at h; cases b' <;> simp [absV] at h
      | bot => rfl
      | use u => simp only [tyV] at h; exact absurd h (botV_ne_use u)
  | use u ihu =>
      intro b h
      cases b with
      | abs b' => simp only [tyV] at h; exact absurd h.symm (absV_ne_use b' u)
      | bot => simp only [tyV] at h; exact absurd h.symm (botV_ne_use u)
      | use u' => rw [ihu u' h]
  | ref n ht iht =>
      intro b h
      cases b with
      | ref n' ht' =>
          simp only [tyV] at h
          injection h with _ h; injection h with h
          injection h with hn h; injection h with hh _
          rw [nullV_inj hn, iht ht' hh]
  | num t =>
      intro b h
      cases b with
      | num t' => rw [numtypeV_inj h]
      | vec t' =>
          simp only [tyV] at h
          cases t <;> rename_i x <;> cases x <;> cases t' <;> simp [numtypeV, vectypeV] at h
      | refv r =>
          simp only [tyV] at h
          have hr := headV_ref r
          rw [← h] at hr
          cases t <;> rename_i x <;> cases x <;> simp [headV, numtypeV] at hr
      | botv =>
          simp only [tyV] at h
          cases t <;> rename_i x <;> cases x <;> simp [numtypeV] at h
  | vec t =>
      intro b h
      cases b with
      | num t' =>
          simp only [tyV] at h
          cases t; cases t' <;> rename_i x <;> cases x <;> simp [numtypeV, vectypeV] at h
      | vec t' => cases t; cases t'; rfl
      | refv r =>
          simp only [tyV] at h
          have hr := headV_ref r
          rw [← h] at hr
          cases t; simp [headV, vectypeV] at hr
      | botv => simp only [tyV] at h; cases t; simp [vectypeV] at h
  | refv r ihr =>
      intro b h
      cases b with
      | num t' =>
          simp only [tyV] at h
          have hr := headV_ref r
          rw [h] at hr
          cases t' <;> rename_i x <;> cases x <;> simp [headV, numtypeV] at hr
      | vec t' =>
          simp only [tyV] at h
          have hr := headV_ref r
          rw [h] at hr
          cases t'; simp [headV, vectypeV] at hr
      | refv r' => rw [ihr r' h]
      | botv =>
          simp only [tyV] at h
          have hr := headV_ref r
          rw [h] at hr
          simp [headV] at hr
  | botv =>
      intro b h
      cases b with
      | num t' => simp only [tyV] at h; cases t' <;> rename_i x <;> cases x <;> simp [numtypeV] at h
      | vec t' => simp only [tyV] at h; cases t'; simp [vectypeV] at h
      | refv r' =>
          simp only [tyV] at h
          have hr := headV_ref r'
          rw [← h] at hr
          simp [headV] at hr
      | botv => rfl
  | val t iht =>
      intro b h
      cases b with
      | val t' => rw [iht t' h]
      | pack p => simp only [tyV] at h; exact absurd h (tyVal_ne_pack t p)
  | pack p =>
      intro b h
      cases b with
      | val t' => simp only [tyV] at h; exact absurd h.symm (tyVal_ne_pack t' p)
      | pack p' => rw [packtypeV_inj h]
  | field m s ihs =>
      intro b h
      cases b with
      | field m' s' =>
          simp only [tyV] at h
          injection h with _ h; injection h with h
          injection h with hm h; injection h with hs _
          rw [mutV_inj hm, ihs s' hs]
  | struct fs ihf =>
      intro b h
      cases b with
      | struct fs' =>
          simp only [tyV, percentV, caseV] at h
          injection h with _ h; injection h with _ h; injection h with h
          injection h with hf _
          rw [ihf fs' hf]
      | array f => simp [tyV] at h
      | func ps rs => simp [tyV] at h
  | array f ihf =>
      intro b h
      cases b with
      | struct fs' => simp [tyV] at h
      | array f' => simp only [tyV] at h; injection h with _ h; rw [ihf f' h]
      | func ps rs => simp [tyV] at h
  | func ps rs ihp ihr =>
      intro b h
      cases b with
      | struct fs' => simp [tyV] at h
      | array f' => simp [tyV] at h
      | func ps' rs' =>
          simp only [tyV, percentV, caseV] at h
          injection h with _ h; injection h with h
          injection h with hp h; injection h with hr _
          injection hp with _ hp; injection hp with hp; injection hp with hp _
          injection hr with _ hr; injection hr with hr; injection hr with hr _
          rw [ihp ps' hp, ihr rs' hr]
  | sub fin sups ct ihs ihc =>
      intro b h
      cases b with
      | sub fin' sups' ct' =>
          simp only [tyV] at h
          injection h with _ h; injection h with h
          injection h with hf h; injection h with hs h; injection h with hc _
          rw [finalV_inj hf, ihs sups' hs, ihc ct' hc]
  | group subs ihs =>
      intro b h
      cases b with
      | group subs' =>
          simp only [tyV, percentV, caseV] at h
          injection h with _ h; injection h with _ h; injection h with h
          injection h with hs _
          rw [ihs subs' hs]


/-! ## The typing group of the pinned specification

Each constant is the `(params, mixop, type, rules)` quadruple that
`Silmaril/SpecTec/Sem/Env.lean`'s `envOfScript` builds for one `RelD` of the
pinned stream.  `hasTyping_wasm30` checks all eighteen in a single `rfl`. -/

/-- `Numtype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:7,13-14`),
as `envOfScript` records it. -/
def numtypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "numtype" [])), (.mk
   "_" (.varT "numtype" []))]), [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "numtype"
   (.varT "numtype" []))] "%|-%<:%" (.tupE [(.varE "C"), (.varE "numtype"), (.varE "numtype")])
   [])])

/-- `Vectype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:8,16-17`),
as `envOfScript` records it. -/
def vectypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "vectype" [])), (.mk
   "_" (.varT "vectype" []))]), [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "vectype"
   (.varT "vectype" []))] "%|-%<:%" (.tupE [(.varE "C"), (.varE "vectype"), (.varE "vectype")])
   [])])

/-- `Packtype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:149,158-159`),
as `envOfScript` records it. -/
def packtypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "packtype" [])), (.mk
   "_" (.varT "packtype" []))]), [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP
   "packtype" (.varT "packtype" []))] "%|-%<:%" (.tupE [(.varE "C"), (.varE "packtype"), (.varE
   "packtype")]) [])])

/-- `Reftype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:10,105-111`),
as `envOfScript` records it. -/
def reftypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "reftype" [])), (.mk
   "_" (.varT "reftype" []))]), [(.ruleD "nonnull" [(.expP "C" (.varT "context" [])), (.expP
   "ht_1" (.varT "heaptype" [])), (.expP "ht_2" (.varT "heaptype" []))] "%|-%<:%" (.tupE [(.varE
   "C"), (.caseE "REF" (.tupE [(.optE none), (.varE "ht_1")])), (.caseE "REF" (.tupE [(.optE
   none), (.varE "ht_2")]))]) [(.rulePr "Heaptype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE
   "ht_1"), (.varE "ht_2")]))]), (.ruleD "null" [(.expP "C" (.varT "context" [])), (.expP "ht_1"
   (.varT "heaptype" [])), (.expP "ht_2" (.varT "heaptype" []))] "%|-%<:%" (.tupE [(.varE "C"),
   (.caseE "REF" (.tupE [(.iterE (.caseE "NULL" (.tupE [])) (.mk .opt [])), (.varE "ht_1")])),
   (.caseE "REF" (.tupE [(.optE (some (.caseE "NULL" (.tupE [])))), (.varE "ht_2")]))])
   [(.rulePr "Heaptype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE "ht_1"), (.varE
   "ht_2")]))])])

/-- `Valtype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:11,114-127`),
as `envOfScript` records it. -/
def valtypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "valtype" [])), (.mk
   "_" (.varT "valtype" []))]), [(.ruleD "num" [(.expP "C" (.varT "context" [])), (.expP
   "numtype_1" (.varT "numtype" [])), (.expP "numtype_2" (.varT "numtype" []))] "%|-%<:%" (.tupE
   [(.varE "C"), (.subE (.varE "numtype_1") (.varT "numtype" []) (.varT "valtype" [])), (.subE
   (.varE "numtype_2") (.varT "numtype" []) (.varT "valtype" []))]) [(.rulePr "Numtype_sub" []
   "%|-%<:%" (.tupE [(.varE "C"), (.varE "numtype_1"), (.varE "numtype_2")]))]), (.ruleD "vec"
   [(.expP "C" (.varT "context" [])), (.expP "vectype_1" (.varT "vectype" [])), (.expP
   "vectype_2" (.varT "vectype" []))] "%|-%<:%" (.tupE [(.varE "C"), (.subE (.varE "vectype_1")
   (.varT "vectype" []) (.varT "valtype" [])), (.subE (.varE "vectype_2") (.varT "vectype" [])
   (.varT "valtype" []))]) [(.rulePr "Vectype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE
   "vectype_1"), (.varE "vectype_2")]))]), (.ruleD "ref" [(.expP "C" (.varT "context" [])),
   (.expP "reftype_1" (.varT "reftype" [])), (.expP "reftype_2" (.varT "reftype" []))] "%|-%<:%"
   (.tupE [(.varE "C"), (.subE (.varE "reftype_1") (.varT "reftype" []) (.varT "valtype" [])),
   (.subE (.varE "reftype_2") (.varT "reftype" []) (.varT "valtype" []))]) [(.rulePr
   "Reftype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE "reftype_1"), (.varE
   "reftype_2")]))]), (.ruleD "bot" [(.expP "C" (.varT "context" [])), (.expP "valtype" (.varT
   "valtype" []))] "%|-%<:%" (.tupE [(.varE "C"), (.caseE "BOT" (.tupE [])), (.varE "valtype")])
   [])])

/-- `Storagetype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:150,162-168`),
as `envOfScript` records it. -/
def storagetypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "storagetype" [])),
   (.mk "_" (.varT "storagetype" []))]), [(.ruleD "val" [(.expP "C" (.varT "context" [])),
   (.expP "valtype_1" (.varT "valtype" [])), (.expP "valtype_2" (.varT "valtype" []))] "%|-%<:%"
   (.tupE [(.varE "C"), (.subE (.varE "valtype_1") (.varT "valtype" []) (.varT "storagetype"
   [])), (.subE (.varE "valtype_2") (.varT "valtype" []) (.varT "storagetype" []))]) [(.rulePr
   "Valtype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE "valtype_1"), (.varE
   "valtype_2")]))]), (.ruleD "pack" [(.expP "C" (.varT "context" [])), (.expP "packtype_1"
   (.varT "packtype" [])), (.expP "packtype_2" (.varT "packtype" []))] "%|-%<:%" (.tupE [(.varE
   "C"), (.subE (.varE "packtype_1") (.varT "packtype" []) (.varT "storagetype" [])), (.subE
   (.varE "packtype_2") (.varT "packtype" []) (.varT "storagetype" []))]) [(.rulePr
   "Packtype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE "packtype_1"), (.varE
   "packtype_2")]))])])

/-- `Fieldtype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:151,171-178`),
as `envOfScript` records it. -/
def fieldtypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "fieldtype" [])),
   (.mk "_" (.varT "fieldtype" []))]), [(.ruleD "const" [(.expP "C" (.varT "context" [])),
   (.expP "zt_1" (.varT "storagetype" [])), (.expP "zt_2" (.varT "storagetype" []))] "%|-%<:%"
   (.tupE [(.varE "C"), (.caseE "%%" (.tupE [(.optE none), (.varE "zt_1")])), (.caseE "%%"
   (.tupE [(.optE none), (.varE "zt_2")]))]) [(.rulePr "Storagetype_sub" [] "%|-%<:%" (.tupE
   [(.varE "C"), (.varE "zt_1"), (.varE "zt_2")]))]), (.ruleD "var" [(.expP "C" (.varT "context"
   [])), (.expP "zt_1" (.varT "storagetype" [])), (.expP "zt_2" (.varT "storagetype" []))]
   "%|-%<:%" (.tupE [(.varE "C"), (.caseE "%%" (.tupE [(.optE (some (.caseE "MUT" (.tupE [])))),
   (.varE "zt_1")])), (.caseE "%%" (.tupE [(.optE (some (.caseE "MUT" (.tupE [])))), (.varE
   "zt_2")]))]) [(.rulePr "Storagetype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE "zt_1"),
   (.varE "zt_2")])), (.rulePr "Storagetype_sub" [] "%|-%<:%" (.tupE [(.varE "C"), (.varE
   "zt_2"), (.varE "zt_1")]))])])

/-- `Resulttype_sub` (`specification/wasm-3.0/2.2-validation.subtyping.spectec:132,135-137`),
as `envOfScript` records it. -/
def resulttypeSubRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%<:%", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "resulttype" [])),
   (.mk "_" (.varT "resulttype" []))]), [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP
   "t_1*" (.iterT (.varT "valtype" []) .list)), (.expP "t_2*" (.iterT (.varT "valtype" [])
   .list))] "%|-%<:%" (.tupE [(.varE "C"), (.caseE "%" (.tupE [(.iterE (.varE "t_1") (.mk .list
   [(.mk "t_1" (.varE "t_1*"))]))])), (.caseE "%" (.tupE [(.iterE (.varE "t_2") (.mk .list [(.mk
   "t_2" (.varE "t_2*"))]))]))]) [(.iterPr (.rulePr "Valtype_sub" [] "%|-%<:%" (.tupE [(.varE
   "C"), (.varE "t_1"), (.varE "t_2")])) (.mk .list [(.mk "t_1" (.varE "t_1*")), (.mk "t_2"
   (.varE "t_2*"))]))])])

/-- `Numtype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:7,14-15`),
as `envOfScript` records it. -/
def numtypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "numtype" []))]),
   [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "numtype" (.varT "numtype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.varE "numtype")]) [])])

/-- `Vectype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:8,17-18`),
as `envOfScript` records it. -/
def vectypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "vectype" []))]),
   [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "vectype" (.varT "vectype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.varE "vectype")]) [])])

/-- `Packtype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:91,119-120`),
as `envOfScript` records it. -/
def packtypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "packtype" []))]),
   [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "packtype" (.varT "packtype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.varE "packtype")]) [])])

/-- `Heaptype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:9,20-28`),
as `envOfScript` records it. -/
def heaptypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "heaptype" []))]),
   [(.ruleD "abs" [(.expP "C" (.varT "context" [])), (.expP "absheaptype" (.varT "absheaptype"
   []))] "%|-%:OK" (.tupE [(.varE "C"), (.subE (.varE "absheaptype") (.varT "absheaptype" [])
   (.varT "heaptype" []))]) []), (.ruleD "typeuse" [(.expP "C" (.varT "context" [])), (.expP
   "typeuse" (.varT "typeuse" []))] "%|-%:OK" (.tupE [(.varE "C"), (.subE (.varE "typeuse")
   (.varT "typeuse" []) (.varT "heaptype" []))]) [(.rulePr "Typeuse_ok" [] "%|-%:OK" (.tupE
   [(.varE "C"), (.varE "typeuse")]))]), (.ruleD "bot" [(.expP "C" (.varT "context" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.caseE "BOT" (.tupE []))]) [])])

/-- `Reftype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:10,30-32`),
as `envOfScript` records it. -/
def reftypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "reftype" []))]),
   [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "heaptype" (.varT "heaptype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.caseE "REF" (.tupE [(.iterE (.caseE "NULL" (.tupE [])) (.mk
   .opt [])), (.varE "heaptype")]))]) [(.rulePr "Heaptype_ok" [] "%|-%:OK" (.tupE [(.varE "C"),
   (.varE "heaptype")]))])])

/-- `Valtype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:11,34-47`),
as `envOfScript` records it. -/
def valtypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "valtype" []))]),
   [(.ruleD "num" [(.expP "C" (.varT "context" [])), (.expP "numtype" (.varT "numtype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.subE (.varE "numtype") (.varT "numtype" []) (.varT "valtype"
   []))]) [(.rulePr "Numtype_ok" [] "%|-%:OK" (.tupE [(.varE "C"), (.varE "numtype")]))]),
   (.ruleD "vec" [(.expP "C" (.varT "context" [])), (.expP "vectype" (.varT "vectype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.subE (.varE "vectype") (.varT "vectype" []) (.varT "valtype"
   []))]) [(.rulePr "Vectype_ok" [] "%|-%:OK" (.tupE [(.varE "C"), (.varE "vectype")]))]),
   (.ruleD "ref" [(.expP "C" (.varT "context" [])), (.expP "reftype" (.varT "reftype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.subE (.varE "reftype") (.varT "reftype" []) (.varT "valtype"
   []))]) [(.rulePr "Reftype_ok" [] "%|-%:OK" (.tupE [(.varE "C"), (.varE "reftype")]))]),
   (.ruleD "bot" [(.expP "C" (.varT "context" []))] "%|-%:OK" (.tupE [(.varE "C"), (.caseE "BOT"
   (.tupE []))]) [])])

/-- `Storagetype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:93,122-128`),
as `envOfScript` records it. -/
def storagetypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "storagetype" []))]),
   [(.ruleD "val" [(.expP "C" (.varT "context" [])), (.expP "valtype" (.varT "valtype" []))]
   "%|-%:OK" (.tupE [(.varE "C"), (.subE (.varE "valtype") (.varT "valtype" []) (.varT
   "storagetype" []))]) [(.rulePr "Valtype_ok" [] "%|-%:OK" (.tupE [(.varE "C"), (.varE
   "valtype")]))]), (.ruleD "pack" [(.expP "C" (.varT "context" [])), (.expP "packtype" (.varT
   "packtype" []))] "%|-%:OK" (.tupE [(.varE "C"), (.subE (.varE "packtype") (.varT "packtype"
   []) (.varT "storagetype" []))]) [(.rulePr "Packtype_ok" [] "%|-%:OK" (.tupE [(.varE "C"),
   (.varE "packtype")]))])])

/-- `Fieldtype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:92,130-132`),
as `envOfScript` records it. -/
def fieldtypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "fieldtype" []))]),
   [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "storagetype" (.varT "storagetype"
   []))] "%|-%:OK" (.tupE [(.varE "C"), (.caseE "%%" (.tupE [(.iterE (.caseE "MUT" (.tupE []))
   (.mk .opt [])), (.varE "storagetype")]))]) [(.rulePr "Storagetype_ok" [] "%|-%:OK" (.tupE
   [(.varE "C"), (.varE "storagetype")]))])])

/-- `Resulttype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:53,60-62`),
as `envOfScript` records it. -/
def resulttypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "resulttype" []))]),
   [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "t*" (.iterT (.varT "valtype" [])
   .list))] "%|-%:OK" (.tupE [(.varE "C"), (.caseE "%" (.tupE [(.iterE (.varE "t") (.mk .list
   [(.mk "t" (.varE "t*"))]))]))]) [(.iterPr (.rulePr "Valtype_ok" [] "%|-%:OK" (.tupE [(.varE
   "C"), (.varE "t")])) (.mk .list [(.mk "t" (.varE "t*"))]))])])

/-- `Localtype_ok` (`specification/wasm-3.0/2.1-validation.types.spectec:52,56-58`),
as `envOfScript` records it. -/
def localtypeOkRel : List Param × MixopS × Typ × List Rule :=
  ([], "%|-%:OK", (.tupT [(.mk "_" (.varT "context" [])), (.mk "_" (.varT "localtype" []))]),
   [(.ruleD "" [(.expP "C" (.varT "context" [])), (.expP "init" (.varT "init" [])), (.expP "t"
   (.varT "valtype" []))] "%|-%:OK" (.tupE [(.varE "C"), (.caseE "%%" (.tupE [(.varE "init"),
   (.varE "t")]))]) [(.rulePr "Valtype_ok" [] "%|-%:OK" (.tupE [(.varE "C"), (.varE "t")]))])])

/-- An environment that interprets the typing group of the pinned wasm-3.0
specification — the `RelD`s of `2.1-validation.types.spectec` and
`2.2-validation.subtyping.spectec` this file reaches — exactly as the
specification does. -/
structure HasTyping (env : Env) : Prop where
  /-- `Numtype_sub`. -/
  numtypeSubD : env.findRel? "Numtype_sub" = some numtypeSubRel
  /-- `Vectype_sub`. -/
  vectypeSubD : env.findRel? "Vectype_sub" = some vectypeSubRel
  /-- `Packtype_sub`. -/
  packtypeSubD : env.findRel? "Packtype_sub" = some packtypeSubRel
  /-- `Reftype_sub`. -/
  reftypeSubD : env.findRel? "Reftype_sub" = some reftypeSubRel
  /-- `Valtype_sub`. -/
  valtypeSubD : env.findRel? "Valtype_sub" = some valtypeSubRel
  /-- `Storagetype_sub`. -/
  storagetypeSubD : env.findRel? "Storagetype_sub" = some storagetypeSubRel
  /-- `Fieldtype_sub`. -/
  fieldtypeSubD : env.findRel? "Fieldtype_sub" = some fieldtypeSubRel
  /-- `Resulttype_sub`. -/
  resulttypeSubD : env.findRel? "Resulttype_sub" = some resulttypeSubRel
  /-- `Numtype_ok`. -/
  numtypeOkD : env.findRel? "Numtype_ok" = some numtypeOkRel
  /-- `Vectype_ok`. -/
  vectypeOkD : env.findRel? "Vectype_ok" = some vectypeOkRel
  /-- `Packtype_ok`. -/
  packtypeOkD : env.findRel? "Packtype_ok" = some packtypeOkRel
  /-- `Heaptype_ok`. -/
  heaptypeOkD : env.findRel? "Heaptype_ok" = some heaptypeOkRel
  /-- `Reftype_ok`. -/
  reftypeOkD : env.findRel? "Reftype_ok" = some reftypeOkRel
  /-- `Valtype_ok`. -/
  valtypeOkD : env.findRel? "Valtype_ok" = some valtypeOkRel
  /-- `Storagetype_ok`. -/
  storagetypeOkD : env.findRel? "Storagetype_ok" = some storagetypeOkRel
  /-- `Fieldtype_ok`. -/
  fieldtypeOkD : env.findRel? "Fieldtype_ok" = some fieldtypeOkRel
  /-- `Resulttype_ok`. -/
  resulttypeOkD : env.findRel? "Resulttype_ok" = some resulttypeOkRel
  /-- `Localtype_ok`. -/
  localtypeOkD : env.findRel? "Localtype_ok" = some localtypeOkRel

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- The pinned wasm-3.0 specification is such an environment: the one
statement here the kernel has to *compute*, unfolding all 976 top-level
definitions of `Specs.wasm30` into `envOfScript`'s declaration maps. -/
theorem hasTyping_wasm30 : HasTyping (envOfScript Specs.wasm30) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Inversion for matching and for premises

`Silmaril/SpecTec/Sem/Eval.lean` has an `evalExp_*_iff` for every expression
former, but no counterpart for `matchExp`, `matchExps`, `premHolds` or
`premsHold`.  The conclusion of a `RuleD` is a *pattern*, so every theorem
below needs them.  Like `derives_iff`, they belong upstream, beside the
functions they invert. -/

/-- `Except.ok` is injective. -/
theorem okInj {α : Type} {a b : α} (h : (.ok a : Res α) = .ok b) : a = b := by
  injection h

/-- A list of patterns matches a list of values, extending `ρ` to `ρ'`. -/
def MatchExps (env : Env) (ρ : VarEnv) (es : List Exp) (vs : List Value)
    (ρ' : VarEnv) : Prop := ∃ n, matchExps n env ρ es vs = .ok ρ'

/-- More fuel preserves a scope `matchExps` has committed to. -/
theorem matchExps_ok_of_le {m n : Nat} {env ρ es vs ρ'} (h : m ≤ n)
    (hv : matchExps m env ρ es vs = .ok ρ') : matchExps n env ρ es vs = .ok ρ' :=
  ((monoAt_of_le h).matchExps env ρ es vs).ok hv

/-- More fuel preserves a scope `matchExp` has committed to. -/
theorem matchExp_ok_mono {m n : Nat} {env ρ e v ρ'} (h : m ≤ n)
    (hv : matchExp m env ρ e v = .ok ρ') : matchExp n env ρ e v = .ok ρ' :=
  ((monoAt_of_le h).matchExp env ρ e v).ok hv

/-- A variable pattern binds an unbound variable and tests a bound one. -/
theorem matchExp_var_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v : Value} :
    MatchExp env ρ (.varE x) v ρ' ↔
      (ρ.findVal? x = none ∧ ρ' = ρ.bindVal x v) ∨ (ρ.findVal? x = some v ∧ ρ' = ρ) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp] at hn
        cases hx : ρ.findVal? x with
        | none => rw [hx] at hn; exact Or.inl ⟨rfl, (okInj hn).symm⟩
        | some w =>
            rw [hx] at hn
            by_cases hw : w = v
            · subst hw; simp only [reduceIte] at hn; exact Or.inr ⟨rfl, (okInj hn).symm⟩
            · simp [hw] at hn
  · rintro (⟨hx, rfl⟩ | ⟨hx, rfl⟩)
    · exact ⟨1, by simp only [matchExp, hx]⟩
    · exact ⟨1, by simp only [matchExp, hx, reduceIte]⟩

/-- The empty pattern list matches only the empty value list. -/
theorem matchExps_nil_iff {env : Env} {ρ ρ' : VarEnv} {vs : List Value} :
    MatchExps env ρ [] vs ρ' ↔ vs = [] ∧ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExps] at hn
    | succ n =>
        cases vs with
        | nil => exact ⟨rfl, (okInj (by simpa only [matchExps] using hn)).symm⟩
        | cons w ws => simp [matchExps] at hn
  · rintro ⟨rfl, rfl⟩; exact ⟨1, by simp only [matchExps]⟩

/-- Pattern lists match head first, threading the scope. -/
theorem matchExps_cons_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {es : List Exp}
    {vs : List Value} :
    MatchExps env ρ (e :: es) vs ρ' ↔
      ∃ w ws σ, vs = w :: ws ∧ MatchExp env ρ e w σ ∧ MatchExps env σ es ws ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExps] at hn
    | succ n =>
        cases vs with
        | nil => simp [matchExps] at hn
        | cons w ws =>
            simp only [matchExps, Res.bind_eq_ok] at hn
            obtain ⟨σ, h₁, h₂⟩ := hn
            exact ⟨w, ws, σ, rfl, ⟨n, h₁⟩, ⟨n, h₂⟩⟩
  · rintro ⟨w, ws, σ, rfl, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    have e1 := matchExp_ok_mono (m := n₁) (n := max n₁ n₂) (by omega) h₁
    have e2 := matchExps_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) h₂
    simp only [matchExps, e1, Bind.bind, Except.bind, e2]

/-- A tuple pattern matches a tuple, component by component. -/
theorem matchExp_tup_iff {env : Env} {ρ ρ' : VarEnv} {es : List Exp} {v : Value} :
    MatchExp env ρ (.tupE es) v ρ' ↔ ∃ vs, v = .tuple vs ∧ MatchExps env ρ es vs ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok,
          Value.asTuple?_eq_some] at hn
        obtain ⟨vs, hv, hm⟩ := hn
        exact ⟨vs, hv, n, hm⟩
  · rintro ⟨vs, rfl, n, hn⟩
    exact ⟨n + 1, by
      simp only [matchExp, Value.asTuple?_tuple, Res.ofOption, Bind.bind, Except.bind, hn]⟩

/-- An injection pattern matches an injection with the same mixop. -/
theorem matchExp_case_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {e : Exp} {v : Value} :
    MatchExp env ρ (.caseE op e) v ρ' ↔ ∃ w, v = .case op w ∧ MatchExp env ρ e w ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
        obtain ⟨⟨op', w⟩, hv, hm⟩ := hn
        rw [Value.asCase?_eq_some] at hv
        rw [Res.assert_eq_ok] at hm
        obtain ⟨rfl, hm⟩ := hm
        exact ⟨w, hv, n, hm⟩
  · rintro ⟨w, rfl, n, hn⟩
    exact ⟨n + 1, by
      simp only [matchExp, Value.asCase?_case, Res.ofOption, Bind.bind, Except.bind,
        Res.assert, reduceIte, hn]⟩

/-- A subtype coercion is transparent to matching (`eval.ml:1035-1068`). -/
theorem matchExp_sub_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {t₁ t₂ : Typ} {v : Value} :
    MatchExp env ρ (.subE e t₁ t₂) v ρ' ↔ MatchExp env ρ e v ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n => exact ⟨n, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- The empty-option pattern matches only the empty option. -/
theorem matchExp_optNone_iff {env : Env} {ρ ρ' : VarEnv} {v : Value} :
    MatchExp env ρ (.optE none) v ρ' ↔ v = .opt none ∧ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        rw [matchExp, Res.assert_eq_ok] at hn
        exact ⟨hn.1, (okInj hn.2).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, by simp only [matchExp, Res.assert, reduceIte]⟩

/-- A non-empty-option pattern matches a non-empty option. -/
theorem matchExp_optSome_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} :
    MatchExp env ρ (.optE (some e)) v ρ' ↔
      ∃ w, v = .opt (some w) ∧ MatchExp env ρ e w ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asOpt?_eq_some] at hn
        obtain ⟨o, hv, w, hw, hm⟩ := hn
        exact ⟨w, by rw [hv, hw], n, hm⟩
  · rintro ⟨w, rfl, n, hn⟩
    exact ⟨n + 1, by
      simp only [matchExp, Value.asOpt?_opt, Res.ofOption, Bind.bind, Except.bind, hn]⟩

/-- `(e)?` with no iteration domain: an optional occurrence of `e`, binding
nothing.  This is the shape the elaborator gives `NULL?` on the left of
`Reftype_sub/null` (`2.2-validation.subtyping.spectec:110`) and `MUT?` on the
left of `Fieldtype_ok` (`2.1-validation.types.spectec:131`). -/
theorem matchExp_iterOptNil_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} :
    MatchExp env ρ (.iterE e (.mk .opt [])) v ρ' ↔
      ρ' = ρ ∧ (v = .opt none ∨ ∃ w σ, v = .opt (some w) ∧ MatchExp env ρ e w σ) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp] at hn
        cases n with
        | zero => simp [matchIterE] at hn
        | succ n =>
            simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok,
              Value.asOpt?_eq_some] at hn
            obtain ⟨o, hv, hm⟩ := hn
            cases o with
            | none =>
                simp only [List.map_nil] at hm
                exact ⟨((matchExps_nil_iff (env := env)).1 ⟨n, hm⟩).2, Or.inl hv⟩
            | some w =>
                simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, List.map_nil,
                  VarEnv.findVals?_nil, Option.some.injEq] at hm
                obtain ⟨σ, hσ, ws, hws, hm⟩ := hm
                subst hws
                simp only [List.map_nil] at hm
                exact ⟨((matchExps_nil_iff (env := env)).1 ⟨n, hm⟩).2,
                  Or.inr ⟨w, σ, hv, n, hσ⟩⟩
  · rintro ⟨rfl, hv | ⟨w, σ, rfl, n, hn⟩⟩
    · subst hv
      exact ⟨3, by
        simp only [matchExp, matchIterE, Value.asOpt?_opt, Res.ofOption, Bind.bind,
          Except.bind, List.map_nil, matchExps]⟩
    · refine ⟨n + 3, ?_⟩
      have hn' := matchExp_ok_mono (m := n) (n := n + 1) (by omega) hn
      simp only [matchExp, matchIterE, Value.asOpt?_opt, Res.ofOption, Bind.bind,
        Except.bind, List.map_nil, hn', VarEnv.findVals?_nil, matchExps]

/-- A list pattern matches a list, component by component. -/
theorem matchExp_list_iff {env : Env} {ρ ρ' : VarEnv} {es : List Exp} {v : Value} :
    MatchExp env ρ (.listE es) v ρ' ↔ ∃ vs, v = .list vs ∧ MatchExps env ρ es vs ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok,
          Value.asList?_eq_some] at hn
        obtain ⟨vs, hv, hm⟩ := hn
        exact ⟨vs, hv, n, hm⟩
  · rintro ⟨vs, rfl, n, hn⟩
    exact ⟨n + 1, by
      simp only [matchExp, Value.asList?_list, Res.ofOption, Bind.bind, Except.bind, hn]⟩

/-! ### Premises -/


/-- No premises hold vacuously and bind nothing. -/
theorem premsHold_nil_iff {env : Env} {ρ ρ' : VarEnv} :
    PremsHold env ρ [] ρ' ↔ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [premsHold] at hn
    | succ n => rw [premsHold_nil_eq] at hn; exact (okInj hn).symm
  · rintro rfl; exact premsHold_nil

/-- Premises are checked left to right, each seeing the previous scope. -/
theorem premsHold_cons_iff {env : Env} {ρ ρ' : VarEnv} {pr : Prem} {prs : List Prem} :
    PremsHold env ρ (pr :: prs) ρ' ↔ ∃ σ, PremHolds env ρ pr σ ∧ PremsHold env σ prs ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [premsHold] at hn
    | succ n =>
        simp only [premsHold, List.foldlM_cons, Res.bind_eq_ok] at hn
        obtain ⟨σ, h₁, h₂⟩ := hn
        exact ⟨σ, ⟨n, h₁⟩, ⟨n + 1, by simpa only [premsHold] using h₂⟩⟩
  · rintro ⟨σ, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨max n₁ (n₂ + 1) + 1, ?_⟩
    have e1 := premHolds_ok_of_le (m := n₁) (n := max n₁ (n₂ + 1)) (by omega) h₁
    have e2 := premsHold_ok_of_le (m := n₂) (n := max n₁ (n₂ + 1) + 1) (by omega) h₂
    simp only [premsHold, List.foldlM_cons, e1, Bind.bind, Except.bind]
    simpa only [premsHold] using e2

/-- A relational premise holds exactly when the asserted instance is
derivable; it binds nothing. -/
theorem premHolds_rule_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {args : List Arg}
    {op : MixopS} {e : Exp} :
    PremHolds env ρ (.rulePr x args op e) ρ' ↔
      ρ' = ρ ∧ ∃ ws v, EvalArgs env ρ args ws ∧ EvalExp env ρ e v ∧
        Derives env x op ws v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [premHolds] at hn
    | succ n =>
        simp only [premHolds, Res.bind_eq_ok] at hn
        obtain ⟨ws, ha, v, he, hd⟩ := hn
        cases hb : derives n env x op ws v with
        | true =>
            rw [hb] at hd
            simp only [reduceIte] at hd
            exact ⟨(okInj hd).symm, ws, v, ⟨n, ha⟩, ⟨n, he⟩, ⟨n, hb⟩⟩
        | false => rw [hb] at hd; simp at hd
  · rintro ⟨rfl, ws, v, ⟨n₁, ha⟩, ⟨n₂, he⟩, ⟨n₃, hd⟩⟩
    refine ⟨max (max n₁ n₂) n₃ + 1, ?_⟩
    have e1 := evalArgs_ok_of_le (m := n₁) (n := max (max n₁ n₂) n₃) (by omega) ha
    have e2 := evalExp_ok_of_le (m := n₂) (n := max (max n₁ n₂) n₃) (by omega) he
    have e3 := derives_of_le (m := n₃) (n := max (max n₁ n₂) n₃) (by omega) hd
    simp only [premHolds, e1, Bind.bind, Except.bind, e2, e3, reduceIte]

/-- The empty argument list denotes the empty value list. -/
theorem evalArgs_nil {env : Env} {ρ : VarEnv} : EvalArgs env ρ [] [] :=
  ⟨1, by simp only [evalArgs, List.mapM_nil]; rfl⟩

/-- Specialise `derives_iff` to a relation whose declaration is known. -/
theorem derives_of_rel_iff {env : Env} {x : IL.Id} {op : MixopS} {ps : List Param}
    {t : Typ} {rules : List Rule} (hr : env.findRel? x = some (ps, op, t, rules))
    {args : List ArgV} {v : Value} :
    Derives env x op args v ↔ ∃ r ∈ rules, RuleFires env op ps args v r := by
  rw [derives_iff]
  constructor
  · rintro ⟨ps', t', rules', hr', hf⟩
    rw [hr] at hr'
    injection hr' with hr'
    injection hr' with h1 hr'
    injection hr' with _ hr'
    injection hr' with _ h4
    subst h1; subst h4
    exact hf
  · intro hf; exact ⟨ps, t, rules, hr, hf⟩

/-- A rule of a parameterless relation fires exactly when its conclusion
matches the value and its premises hold in the scope the match built. -/
theorem ruleFires_nil_iff {env : Env} {op : MixopS} {v : Value} {nm : IL.Id}
    {q : List Param} {e : Exp} {prems : List Prem} :
    RuleFires env op [] [] v (.ruleD nm q op e prems) ↔
      ∃ ρ₁ ρ₂, MatchExp env VarEnv.empty e v ρ₁ ∧ PremsHold env ρ₁ prems ρ₂ := by
  constructor
  · rintro ⟨x, q', e', prems', ρ₀, ρ₁, ρ₂, hrule, hb, hm, hp⟩
    injection hrule with _ _ _ he hpr
    subst he; subst hpr
    simp only [bindParams, Option.some.injEq] at hb
    subst hb
    exact ⟨ρ₁, ρ₂, hm, hp⟩
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    exact ⟨nm, q, e, prems, VarEnv.empty, ρ₁, ρ₂, rfl, rfl, hm, hp⟩

/-! ### Evaluating the expressions a premise asserts -/

/-- The empty expression list denotes the empty value list. -/
theorem evalExps_nil_iff {env : Env} {ρ : VarEnv} {vs : List Value} :
    EvalExps env ρ [] vs ↔ vs = [] := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [evalExps] at hn
    | succ n =>
        exact (okInj (by simpa only [evalExps, List.mapM_nil, pure, Except.pure] using hn)).symm
  · rintro rfl; exact ⟨1, by simp only [evalExps, List.mapM_nil]; rfl⟩

/-- An expression list denotes the list of its components' denotations. -/
theorem evalExps_cons_iff {env : Env} {ρ : VarEnv} {e : Exp} {es : List Exp}
    {vs : List Value} :
    EvalExps env ρ (e :: es) vs ↔
      ∃ w ws, vs = w :: ws ∧ EvalExp env ρ e w ∧ EvalExps env ρ es ws := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [evalExps] at hn
    | succ n =>
        simp only [evalExps, List.mapM_cons, Res.bind_eq_ok] at hn
        obtain ⟨w, hw, ws, hws, hv⟩ := hn
        exact ⟨w, ws, (okInj hv).symm, ⟨n, hw⟩, ⟨n + 1, by simpa only [evalExps] using hws⟩⟩
  · rintro ⟨w, ws, rfl, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    have e1 := evalExp_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) h₁
    have e2 : es.mapM (evalExp (max n₁ n₂) env ρ) = .ok ws := by
      have := evalExps_ok_of_le (m := n₂) (n := max n₁ n₂ + 1) (by omega) h₂
      simpa only [evalExps] using this
    simp only [evalExps, List.mapM_cons, e1, e2, Bind.bind, Except.bind]
    rfl

/-- A side condition holds exactly when its expression is `true`; it binds
nothing (`spectec/src/il/eval.ml:688-693`). -/
theorem premHolds_if_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} :
    PremHolds env ρ (.ifPr e) ρ' ↔ ρ' = ρ ∧ EvalExp env ρ e (.bool true) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [premHolds] at hn
    | succ n =>
        simp only [premHolds, Res.bind_eq_ok, Res.assert_eq_ok] at hn
        obtain ⟨v, hv, rfl, hr⟩ := hn
        exact ⟨(okInj hr).symm, ⟨n, hv⟩⟩
  · rintro ⟨rfl, ⟨n, hn⟩⟩
    exact ⟨n + 1, by simp only [premHolds, hn, Bind.bind, Except.bind, Res.assert, reduceIte]⟩

/-- The empty argument list denotes the empty value list, and nothing else. -/
theorem evalArgs_nil_iff {env : Env} {ρ : VarEnv} {ws : List ArgV} :
    EvalArgs env ρ [] ws ↔ ws = [] := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [evalArgs] at hn
    | succ n =>
        exact (okInj (by simpa only [evalArgs, List.mapM_nil, pure, Except.pure] using hn)).symm
  · rintro rfl; exact evalArgs_nil

/-! ## The subtyping relations

Every theorem in this section is proved by the same four steps:
`derives_of_rel_iff` replaces `Derives` by "some rule of the pinned
declaration fires", `ruleFires_nil_iff` splits a rule into "the conclusion
matches" and "the premises hold", and the `matchExp_*_iff` and `premHolds_*`
lemmas above reduce those to the shape of the value and to `Derives` of the
premises.  The result is an *equality of relations*, not an implication: both
directions come out of the same chain of `iff`s. -/

/-- The `simp` set that turns "some rule of a parameterless relation fires"
into a condition on the value and on the premises' own `Derives`.  Every
theorem in this section and the next is proved by `rw [derives_of_rel_iff …]`
followed by this. -/
local macro "rule_simp" : tactic =>
  `(tactic|
    simp +contextual [ruleFires_nil_iff, matchExp_tup_iff, matchExps_cons_iff,
      matchExps_nil_iff, matchExp_var_iff, matchExp_case_iff, matchExp_sub_iff,
      matchExp_list_iff, matchExp_optNone_iff, matchExp_optSome_iff,
      matchExp_iterOptNil_iff, premsHold_nil_iff, premsHold_cons_iff,
      premHolds_rule_iff, premHolds_if_iff, evalArgs_nil_iff,
      evalExp_tupE_iff, evalExps_nil_iff, evalExps_cons_iff, evalExp_varE_iff,
      VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.empty, Map.bind, Map.find?])

/-- `rule_simp`, applied to a hypothesis. -/
local macro "rule_simp_at" h:ident : tactic =>
  `(tactic|
    simp +contextual [ruleFires_nil_iff, matchExp_tup_iff, matchExps_cons_iff,
      matchExps_nil_iff, matchExp_var_iff, matchExp_case_iff, matchExp_sub_iff,
      matchExp_list_iff, matchExp_optNone_iff, matchExp_optSome_iff,
      matchExp_iterOptNil_iff, premsHold_nil_iff, premsHold_cons_iff,
      premHolds_rule_iff, premHolds_if_iff, evalArgs_nil_iff,
      evalExp_tupE_iff, evalExps_nil_iff, evalExps_cons_iff, evalExp_varE_iff,
      VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.empty, Map.bind,
      Map.find?] at $h:ident)

/-- `Numtype_sub` (`2.2:13-14`) relates a value to itself and to nothing
else: its single rule's conclusion `C |- numtype <: numtype` repeats one
pattern variable, and `matchExp` tests a *bound* variable for equality. -/
theorem derives_numtypeSub_iff {env : Env} (h : HasTyping env) {c v₁ v₂ : Value} :
    Derives env "Numtype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂]) ↔ v₁ = v₂ := by
  rw [derives_of_rel_iff h.numtypeSubD]
  rule_simp
  exact eq_comm

/-- `Vectype_sub` (`2.2:16-17`), likewise. -/
theorem derives_vectypeSub_iff {env : Env} (h : HasTyping env) {c v₁ v₂ : Value} :
    Derives env "Vectype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂]) ↔ v₁ = v₂ := by
  rw [derives_of_rel_iff h.vectypeSubD]
  rule_simp
  exact eq_comm

/-- `Packtype_sub` (`2.2:158-159`), likewise. -/
theorem derives_packtypeSub_iff {env : Env} (h : HasTyping env) {c v₁ v₂ : Value} :
    Derives env "Packtype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂]) ↔ v₁ = v₂ := by
  rw [derives_of_rel_iff h.packtypeSubD]
  rule_simp
  exact eq_comm

/-- `Reftype_sub` (`2.2:105-111`) on two reference types: nullability must be
preserved, and the heap types must be related. -/
theorem derives_reftypeSub_ref_iff {env : Env} (h : HasTyping env) {c : Value}
    {n₁ n₂ : Bool} {hv₁ hv₂ : Value} :
    Derives env "Reftype_sub" "%|-%<:%" []
        (.tuple [c, .case "REF" (.tuple [nullV n₁, hv₁]),
          .case "REF" (.tuple [nullV n₂, hv₂])]) ↔
      (n₁ = true → n₂ = true) ∧
        Derives env "Heaptype_sub" "%|-%<:%" [] (.tuple [c, hv₁, hv₂]) := by
  rw [derives_of_rel_iff h.reftypeSubD]
  cases n₁ <;> cases n₂ <;> simp only [nullV] <;> rule_simp

/-- The two rules of `Reftype_sub` are the only way to derive it, so a
derivation forces both sides to be reference types. -/
theorem derives_reftypeSub_shape {env : Env} (h : HasTyping env) {c v₁ v₂ : Value}
    (hd : Derives env "Reftype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂])) :
    ∃ (n₁ n₂ : Bool) (w₁ w₂ : Value),
      v₁ = .case "REF" (.tuple [nullV n₁, w₁]) ∧
        v₂ = .case "REF" (.tuple [nullV n₂, w₂]) ∧ (n₁ = true → n₂ = true) ∧
          Derives env "Heaptype_sub" "%|-%<:%" [] (.tuple [c, w₁, w₂]) := by
  rw [derives_of_rel_iff h.reftypeSubD] at hd
  rule_simp_at hd
  rcases hd with ⟨a, b, ⟨hv₁, hv₂⟩, hh⟩ | ⟨a, o, b, ⟨⟨hv₁, hv₂⟩, ho⟩, hh⟩
  · exact ⟨false, false, b, a, by simpa [nullV] using hv₁, by simpa [nullV] using hv₂,
      by simp, hh⟩
  · rcases ho with rfl | rfl
    · exact ⟨false, true, b, a, by simpa [nullV] using hv₁, by simpa [nullV] using hv₂,
        by simp, hh⟩
    · exact ⟨true, true, b, a, by simpa [nullV] using hv₁, by simpa [nullV] using hv₂,
        fun _ => rfl, hh⟩

/-- `Valtype_sub` (`2.2:114-127`): the `num` and `vec` rules both reduce to
equality, so the relation is "equal, or a reference subtyping, or `BOT` on the
left". -/
theorem derives_valtypeSub_iff {env : Env} (h : HasTyping env) {c v₁ v₂ : Value} :
    Derives env "Valtype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂]) ↔
      v₁ = v₂ ∨ Derives env "Reftype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂]) ∨
        v₁ = .case "BOT" (.tuple []) := by
  rw [derives_of_rel_iff h.valtypeSubD]
  rule_simp
  rw [derives_numtypeSub_iff h, derives_vectypeSub_iff h]
  tauto

/-- `Storagetype_sub` (`2.2:162-168`). -/
theorem derives_storagetypeSub_iff {env : Env} (h : HasTyping env) {c v₁ v₂ : Value} :
    Derives env "Storagetype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂]) ↔
      Derives env "Valtype_sub" "%|-%<:%" [] (.tuple [c, v₁, v₂]) ∨ v₁ = v₂ := by
  rw [derives_of_rel_iff h.storagetypeSubD]
  rule_simp
  rw [derives_packtypeSub_iff h]

/-- `Fieldtype_sub` (`2.2:171-178`): immutable fields are covariant, mutable
fields invariant. -/
theorem derives_fieldtypeSub_iff {env : Env} (h : HasTyping env) {c : Value}
    {m₁ m₂ : Wasm.Mutability} {z₁ z₂ : Value} :
    Derives env "Fieldtype_sub" "%|-%<:%" []
        (.tuple [c, .case "%%" (.tuple [mutV m₁, z₁]),
          .case "%%" (.tuple [mutV m₂, z₂])]) ↔
      m₁ = m₂ ∧ Derives env "Storagetype_sub" "%|-%<:%" [] (.tuple [c, z₁, z₂]) ∧
        (m₁ = .var → Derives env "Storagetype_sub" "%|-%<:%" [] (.tuple [c, z₂, z₁])) := by
  rw [derives_of_rel_iff h.fieldtypeSubD]
  cases m₁ <;> cases m₂ <;> simp only [mutV] <;> rule_simp

/-! ## The well-formedness judgments, and what they do *not* say

Each `*_ok` rule below binds its subject with a bare pattern variable — a
`VarE` under a `SubE`, both of which `matchExp` treats transparently — and the
only thing that would restrict that variable to the right *sort* is the rule's
own quantifier list (`exp "absheaptype" (var "absheaptype")` and friends).
`Sem/Eval.lean`'s `anyRule` discards a `RuleD`'s quantifiers
(`spectec/src/il/ast.ml:145` has no argument list for a rule, so `derives`
binds the *relation*'s parameters positionally and ignores the rule's), and it
never consults `Sem/Type.lean`'s `HasTyp`.  The consequence is proved rather
than asserted: `Numtype_ok`, `Vectype_ok`, `Packtype_ok`, `Heaptype_ok`,
`Valtype_ok` and `Storagetype_ok` hold of **every** pair of values. -/

/-- `Numtype_ok` (`2.1:14-15`) holds of every value. -/
theorem derives_numtypeOk {env : Env} (h : HasTyping env) (c v : Value) :
    Derives env "Numtype_ok" "%|-%:OK" [] (.tuple [c, v]) := by
  rw [derives_of_rel_iff h.numtypeOkD]; rule_simp

/-- `Vectype_ok` (`2.1:17-18`) holds of every value. -/
theorem derives_vectypeOk {env : Env} (h : HasTyping env) (c v : Value) :
    Derives env "Vectype_ok" "%|-%:OK" [] (.tuple [c, v]) := by
  rw [derives_of_rel_iff h.vectypeOkD]; rule_simp

/-- `Packtype_ok` (`2.1:119-120`) holds of every value. -/
theorem derives_packtypeOk {env : Env} (h : HasTyping env) (c v : Value) :
    Derives env "Packtype_ok" "%|-%:OK" [] (.tuple [c, v]) := by
  rw [derives_of_rel_iff h.packtypeOkD]; rule_simp

/-- `Heaptype_ok` (`2.1:20-28`) holds of every value: the `abs` rule's
conclusion is `C |- absheaptype : OK` with `absheaptype` a free pattern
variable under a `SubE`. -/
theorem derives_heaptypeOk {env : Env} (h : HasTyping env) (c v : Value) :
    Derives env "Heaptype_ok" "%|-%:OK" [] (.tuple [c, v]) := by
  rw [derives_of_rel_iff h.heaptypeOkD]; rule_simp

/-- `Valtype_ok` (`2.1:34-47`) holds of every value, through its `num` rule
and `derives_numtypeOk`. -/
theorem derives_valtypeOk {env : Env} (h : HasTyping env) (c v : Value) :
    Derives env "Valtype_ok" "%|-%:OK" [] (.tuple [c, v]) := by
  rw [derives_of_rel_iff h.valtypeOkD]
  rule_simp
  exact Or.inl (derives_numtypeOk h c v)

/-- `Storagetype_ok` (`2.1:122-128`) holds of every value. -/
theorem derives_storagetypeOk {env : Env} (h : HasTyping env) (c v : Value) :
    Derives env "Storagetype_ok" "%|-%:OK" [] (.tuple [c, v]) := by
  rw [derives_of_rel_iff h.storagetypeOkD]
  rule_simp
  exact Or.inl (derives_valtypeOk h c v)

/-- `Reftype_ok` (`2.1:30-32`) holds of every reference-shaped value. -/
theorem derives_reftypeOk {env : Env} (h : HasTyping env) (c : Value) (n : Bool)
    (w : Value) :
    Derives env "Reftype_ok" "%|-%:OK" [] (.tuple [c, .case "REF" (.tuple [nullV n, w])]) := by
  rw [derives_of_rel_iff h.reftypeOkD]
  cases n <;> simp only [nullV] <;> rule_simp <;> exact derives_heaptypeOk h c w

/-- `Fieldtype_ok` (`2.1:130-132`) holds of every field-shaped value. -/
theorem derives_fieldtypeOk {env : Env} (h : HasTyping env) (c : Value)
    (m : Wasm.Mutability) (z : Value) :
    Derives env "Fieldtype_ok" "%|-%:OK" [] (.tuple [c, .case "%%" (.tuple [mutV m, z])]) := by
  rw [derives_of_rel_iff h.fieldtypeOkD]
  cases m <;> simp only [mutV] <;> rule_simp <;> exact derives_storagetypeOk h c z

/-- `Localtype_ok` (`2.1:56-58`) holds of every `%%`-shaped value, with no
constraint at all on the initialisation status or the value type. -/
theorem derives_localtypeOk {env : Env} (h : HasTyping env) (c i t : Value) :
    Derives env "Localtype_ok" "%|-%:OK" [] (.tuple [c, .case "%%" (.tuple [i, t])]) := by
  rw [derives_of_rel_iff h.localtypeOkD]
  rule_simp
  exact derives_valtypeOk h c t

/-! ## The validation context

`context` (`2.0-validation.contexts.spectec:24-41`) is a thirteen-field
record, and `Sem/Eval.lean`'s `matchExpFields` pairs a record's fields
*positionally*, so `ctxV` lists them in declaration order.
`Silmaril/Wasm/Validation/Context.lean`'s `Context` has exactly these fields
(`RECS` through `TypeCtx`), with every stored type already closed. -/

/-- `init` (`2.0-validation.contexts.spectec:8-9`). -/
def initV : Init → Value
  | .set => .case "SET" (.tuple [])
  | .unset => .case "UNSET" (.tuple [])

/-- `localtype = init valtype` (`2.0-validation.contexts.spectec:11-12`). -/
def localtypeV (l : LocalType) : Value :=
  .case "%%" (.tuple [initV l.init, tyV l.type])

/-- `limits = `[u64 .. u64?]` (`1.2-syntax.types.spectec:128`). -/
def limitsV (l : Wasm.Limits) : Value :=
  .case "[%..%]" (.tuple [idxV l.min.val, .opt (l.max.map fun m => idxV m.val)])

/-- `memtype = addrtype limits PAGE` (`1.2-syntax.types.spectec:131`). -/
def memtypeV (m : Wasm.MemoryType) : Value :=
  .case "%%PAGE" (.tuple [addrV m.address, limitsV m.limits])

/-- `tabletype = addrtype limits reftype` (`1.2-syntax.types.spectec:132`). -/
def tabletypeV (t : CTableType) : Value :=
  .case "%%%" (.tuple [addrV t.address, limitsV t.limits, tyV t.element])

/-- `globaltype = mut? valtype` (`1.2-syntax.types.spectec:130`). -/
def globaltypeV (g : CGlobalType) : Value :=
  .case "%%" (.tuple [mutV g.mutability, tyV g.type])

/-- `datatype = OK` (`1.2-syntax.types.spectec:133`). -/
def datatypeV : Value := .case "OK" (.tuple [])

/-- A validation context as a `Value.struct`, fields in declaration order. -/
def ctxV (C : Context) : Value :=
  .struct
    [("TYPES", .list (C.types.map tyV)),
     ("TAGS", .list (C.tags.map tyV)),
     ("GLOBALS", .list (C.globals.map globaltypeV)),
     ("MEMS", .list (C.mems.map memtypeV)),
     ("TABLES", .list (C.tables.map tabletypeV)),
     ("FUNCS", .list (C.funcs.map tyV)),
     ("DATAS", .list (C.datas.map fun _ => datatypeV)),
     ("ELEMS", .list (C.elems.map tyV)),
     ("LOCALS", .list (C.locals.map localtypeV)),
     ("LABELS", .list (C.labels.map resulttypeV)),
     ("RETURN", .opt (C.return_.map resulttypeV)),
     ("REFS", .list (C.refs.map idxV)),
     ("RECS", .list (C.recs.map tyV))]

/-! ### What an encoded context determines -/

/-- The `TYPES` field of an encoded context. -/
theorem ctxV_types (C : Context) :
    (ctxV C).field? "TYPES" = some (.list (C.types.map tyV)) := by
  simp [ctxV, Value.field?]

/-- The `RECS` field of an encoded context. -/
theorem ctxV_recs (C : Context) :
    (ctxV C).field? "RECS" = some (.list (C.recs.map tyV)) := by
  simp [ctxV, Value.field?]

/-- The `LABELS` field of an encoded context. -/
theorem ctxV_labels (C : Context) :
    (ctxV C).field? "LABELS" = some (.list (C.labels.map resulttypeV)) := by
  simp [ctxV, Value.field?]

/-- An encoded context determines its `TYPES`, which is the field every
subtyping rule above the heap sort reads. -/
theorem ctxV_types_inj {C D : Context} (h : ctxV C = ctxV D) : C.types = D.types := by
  have h₁ := ctxV_types C
  rw [h, ctxV_types D] at h₁
  have h₂ : C.types.map tyV = D.types.map tyV := by
    simpa only [Option.some.injEq, Value.list.injEq] using h₁.symm
  exact List.map_injective_iff.2 (fun a b hab => tyV_inj a b hab) h₂

/-- An encoded context determines its `RECS`. -/
theorem ctxV_recs_inj {C D : Context} (h : ctxV C = ctxV D) : C.recs = D.recs := by
  have h₁ := ctxV_recs C
  rw [h, ctxV_recs D] at h₁
  have h₂ : C.recs.map tyV = D.recs.map tyV := by
    simpa only [Option.some.injEq, Value.list.injEq] using h₁.symm
  exact List.map_injective_iff.2 (fun a b hab => tyV_inj a b hab) h₂

/-- Hence an encoded context determines the `TypeCtx` the subtyping judgments
are relative to. -/
theorem ctxV_typeCtx_inj {C D : Context} (h : ctxV C = ctxV D) :
    C.toTypeCtx = D.toTypeCtx := by
  show (⟨C.types, C.recs⟩ : TypeCtx) = ⟨D.types, D.recs⟩
  rw [ctxV_types_inj h, ctxV_recs_inj h]

/-! ## Silmaril's subtyping, inverted

`Silmaril/Wasm/Validation/Subtyping.lean`'s `Sub` is one kind-indexed
inductive covering every sort at once.  At the reference, value, storage and
field sorts only a handful of its constructors apply, and these are the
inversion lemmas that say so. -/

/-- Reflexivity of `Sub` at the heap sort (`Heaptype_sub/refl`). -/
theorem sub_refl_heap (Δ : TypeCtx) (ht : CHeapType) : Sub Δ ht ht := .heapRefl

/-- Reflexivity of `Sub` at the reference sort. -/
theorem sub_refl_ref (Δ : TypeCtx) (r : CRefType) : Sub Δ r r := by
  cases r with
  | ref n ht => cases n with
    | false => exact .refNonNull .heapRefl
    | true => exact .refNull .heapRefl

/-- Reflexivity of `Sub` at the value sort. -/
theorem sub_refl_val (Δ : TypeCtx) (t : CValType) : Sub Δ t t := by
  cases t with
  | num => exact .num
  | vec => exact .vec
  | refv r => exact .refv (sub_refl_ref Δ r)
  | botv => exact .botv

/-- Reflexivity of `Sub` at the storage sort. -/
theorem sub_refl_storage (Δ : TypeCtx) (z : CStorageType) : Sub Δ z z := by
  cases z with
  | val t => exact .val (sub_refl_val Δ t)
  | pack => exact .pack

/-- Inversion of `Sub` at the reference sort: `Reftype_sub/nonnull` and
`Reftype_sub/null` are its only constructors there. -/
theorem sub_ref_iff {Δ : TypeCtx} {n₁ n₂ : Bool} {h₁ h₂ : CHeapType} :
    Sub Δ (.ref n₁ h₁) (.ref n₂ h₂) ↔ (n₁ = true → n₂ = true) ∧ Sub Δ h₁ h₂ := by
  constructor
  · intro hs
    cases hs with
    | refNonNull hh => exact ⟨by simp, hh⟩
    | refNull hh => exact ⟨fun _ => rfl, hh⟩
  · rintro ⟨hn, hh⟩
    cases n₂ with
    | true => exact .refNull hh
    | false =>
        cases n₁ with
        | false => exact .refNonNull hh
        | true => simp at hn

/-- Inversion of `Sub` at the value sort. -/
theorem sub_val_iff {Δ : TypeCtx} {t₁ t₂ : CValType} :
    Sub Δ t₁ t₂ ↔
      t₁ = t₂ ∨ (∃ r₁ r₂, t₁ = .refv r₁ ∧ t₂ = .refv r₂ ∧ Sub Δ r₁ r₂) ∨ t₁ = .botv := by
  constructor
  · intro hs
    cases hs with
    | num => exact Or.inl rfl
    | vec => exact Or.inl rfl
    | refv hr => exact Or.inr (Or.inl ⟨_, _, rfl, rfl, hr⟩)
    | botv => exact Or.inr (Or.inr rfl)
  · rintro (rfl | ⟨r₁, r₂, rfl, rfl, hr⟩ | rfl)
    · exact sub_refl_val Δ t₁
    · exact .refv hr
    · exact .botv

/-- Inversion of `Sub` at the storage sort. -/
theorem sub_storage_iff {Δ : TypeCtx} {z₁ z₂ : CStorageType} :
    Sub Δ z₁ z₂ ↔
      (∃ t₁ t₂, z₁ = .val t₁ ∧ z₂ = .val t₂ ∧ Sub Δ t₁ t₂) ∨
        (∃ p, z₁ = .pack p ∧ z₂ = .pack p) := by
  constructor
  · intro hs
    cases hs with
    | val ht => exact Or.inl ⟨_, _, rfl, rfl, ht⟩
    | pack => exact Or.inr ⟨_, rfl, rfl⟩
  · rintro (⟨t₁, t₂, rfl, rfl, ht⟩ | ⟨p, rfl, rfl⟩)
    · exact .val ht
    · exact .pack

/-- Inversion of `Sub` at the field sort. -/
theorem sub_field_iff {Δ : TypeCtx} {m₁ m₂ : Wasm.Mutability} {z₁ z₂ : CStorageType} :
    Sub Δ (.field m₁ z₁) (.field m₂ z₂) ↔
      m₁ = m₂ ∧ Sub Δ z₁ z₂ ∧ (m₁ = .var → Sub Δ z₂ z₁) := by
  constructor
  · intro hs
    cases hs with
    | fieldConst hz => exact ⟨rfl, hz, by simp⟩
    | fieldVar h₁ h₂ => exact ⟨rfl, h₁, fun _ => h₂⟩
  · rintro ⟨rfl, hz, hv⟩
    cases m₁ with
    | const => exact .fieldConst hz
    | var => exact .fieldVar hz (hv rfl)

/-! ## Agreement with Silmaril's subtyping

Every statement below is relative to one named hypothesis, `HeapSubAgree`:
that the two developments agree at the *heap* sort.  That is the one sort this
file does not reach (see "What is not reached"), and `Reftype_sub` — hence
everything above it — recurses into it. -/

/-- A value type whose encoding is a `REF` injection is a reference type. -/
theorem tyVal_isRef {t : CValType} {w : Value} (hv : tyV t = .case "REF" w) :
    ∃ r : CRefType, t = .refv r := by
  cases t with
  | num nt => cases nt <;> rename_i x <;> cases x <;> simp [tyV, numtypeV] at hv
  | vec vt => cases vt; simp [tyV, vectypeV] at hv
  | refv r => exact ⟨r, rfl⟩
  | botv => simp [tyV] at hv

/-- A value type whose encoding is `BOT` is `BOT`. -/
theorem tyVal_isBot {t : CValType} (hv : tyV t = .case "BOT" (.tuple [])) : t = .botv := by
  cases t with
  | num nt => cases nt <;> rename_i x <;> cases x <;> simp [tyV, numtypeV] at hv
  | vec vt => cases vt; simp [tyV, vectypeV] at hv
  | refv r => cases r; simp [tyV] at hv
  | botv => rfl

/-- `Reftype_sub` never holds with a packed type on the right. -/
theorem not_derives_reftypeSub_packR {env : Env} (h : HasTyping env) {c v : Value}
    {p : Wasm.PackType} :
    ¬ Derives env "Reftype_sub" "%|-%<:%" [] (.tuple [c, v, packtypeV p]) := by
  intro hd
  obtain ⟨m₁, m₂, u₁, u₂, hv₁, hv₂, hn, hh⟩ := derives_reftypeSub_shape h hd
  cases p <;> simp [packtypeV] at hv₂

/-- `Reftype_sub` never holds with a packed type on the left. -/
theorem not_derives_reftypeSub_packL {env : Env} (h : HasTyping env) {c v : Value}
    {p : Wasm.PackType} :
    ¬ Derives env "Reftype_sub" "%|-%<:%" [] (.tuple [c, packtypeV p, v]) := by
  intro hd
  obtain ⟨m₁, m₂, u₁, u₂, hv₁, hv₂, hn, hh⟩ := derives_reftypeSub_shape h hd
  cases p <;> simp [packtypeV] at hv₁

/-- SpecTec's `Heaptype_sub` and Silmaril's `Sub` agree at the heap sort. -/
def HeapSubAgree (env : Env) (C : Context) : Prop :=
  ∀ h₁ h₂ : CHeapType,
    Derives env "Heaptype_sub" "%|-%<:%" [] (.tuple [ctxV C, tyV h₁, tyV h₂]) ↔
      Sub C.toTypeCtx h₁ h₂

/-- **`Reftype_sub` agrees with `Sub` at the reference sort**, in both
directions. -/
theorem reftypeSub_agree {env : Env} {C : Context} (h : HasTyping env)
    (ha : HeapSubAgree env C) (r₁ r₂ : CRefType) :
    Derives env "Reftype_sub" "%|-%<:%" [] (.tuple [ctxV C, tyV r₁, tyV r₂]) ↔
      Sub C.toTypeCtx r₁ r₂ := by
  cases r₁ with
  | ref n₁ h₁ =>
      cases r₂ with
      | ref n₂ h₂ =>
          simp only [tyV]
          rw [derives_reftypeSub_ref_iff h, ha, sub_ref_iff]

/-- **`Valtype_sub` agrees with `Sub` at the value sort**, in both
directions. -/
theorem valtypeSub_agree {env : Env} {C : Context} (h : HasTyping env)
    (ha : HeapSubAgree env C) (t₁ t₂ : CValType) :
    Derives env "Valtype_sub" "%|-%<:%" [] (.tuple [ctxV C, tyV t₁, tyV t₂]) ↔
      Sub C.toTypeCtx t₁ t₂ := by
  rw [derives_valtypeSub_iff h, sub_val_iff]
  constructor
  · rintro (he | hr | hb)
    · exact Or.inl (tyV_inj _ _ he)
    · obtain ⟨m₁, m₂, u₁, u₂, hv₁, hv₂, hn, hh⟩ := derives_reftypeSub_shape h hr
      obtain ⟨s₁, rfl⟩ := tyVal_isRef hv₁
      obtain ⟨s₂, rfl⟩ := tyVal_isRef hv₂
      exact Or.inr (Or.inl ⟨s₁, s₂, rfl, rfl,
        (reftypeSub_agree h ha s₁ s₂).1 (by simpa only [tyV] using hr)⟩)
    · exact Or.inr (Or.inr (tyVal_isBot hb))
  · rintro (rfl | ⟨s₁, s₂, rfl, rfl, hs⟩ | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by
        simpa only [tyV] using (reftypeSub_agree h ha s₁ s₂).2 hs))
    · exact Or.inr (Or.inr rfl)

/-! ### The storage sort, and the gap -/

/-- `Sub` at the storage sort, on two unpacked types. -/
theorem sub_val_val_iff {Δ : TypeCtx} {t₁ t₂ : CValType} :
    Sub Δ (.val t₁) (.val t₂) ↔ Sub Δ t₁ t₂ := by
  constructor
  · intro hs; cases hs with | val hh => exact hh
  · exact Sub.val

/-- `Sub` at the storage sort, on two packed types. -/
theorem sub_pack_pack_iff {Δ : TypeCtx} {p₁ p₂ : Wasm.PackType} :
    Sub Δ (.pack p₁ : CStorageType) (.pack p₂) ↔ p₁ = p₂ := by
  constructor
  · intro hs; cases hs; rfl
  · rintro rfl; exact .pack

/-- A value type is never a subtype of a packed type. -/
theorem not_sub_val_pack {Δ : TypeCtx} {t : CValType} {p : Wasm.PackType} :
    ¬ Sub Δ (.val t) (.pack p) := by intro hs; cases hs

/-- A packed type is never a subtype of a value type. -/
theorem not_sub_pack_val {Δ : TypeCtx} {t : CValType} {p : Wasm.PackType} :
    ¬ Sub Δ (.pack p : CStorageType) (.val t) := by intro hs; cases hs

/-- The one place sort erasure makes `Storagetype_sub` strictly larger than
`Sub`: the value type `BOT` on the left of a *packed* type.
`Valtype_sub/bot` (`2.2:126-127`) concludes `C |- BOT <: valtype` with
`valtype` a free pattern variable, and `Storagetype_sub/val` (`2.2:162-164`)
feeds a `storagetype` straight into it. -/
def StorageGap (z₁ z₂ : CStorageType) : Prop := z₁ = .val .botv ∧ ∃ p, z₂ = .pack p

/-- **`Storagetype_sub` is exactly `Sub` plus `StorageGap`.** -/
theorem storagetypeSub_agree {env : Env} {C : Context} (h : HasTyping env)
    (ha : HeapSubAgree env C) (z₁ z₂ : CStorageType) :
    Derives env "Storagetype_sub" "%|-%<:%" [] (.tuple [ctxV C, tyV z₁, tyV z₂]) ↔
      Sub C.toTypeCtx z₁ z₂ ∨ StorageGap z₁ z₂ := by
  rw [derives_storagetypeSub_iff h]
  cases z₁ with
  | val t₁ =>
      cases z₂ with
      | val t₂ =>
          simp only [tyV, StorageGap, sub_val_val_iff, reduceCtorEq, exists_false,
            and_false, or_false]
          rw [valtypeSub_agree h ha]
          constructor
          · rintro (hs | he)
            · exact hs
            · exact (tyV_inj _ _ he) ▸ sub_refl_val _ t₁
          · exact Or.inl
      | pack p =>
          simp only [tyV, StorageGap, Ty.val.injEq, Ty.pack.injEq, exists_eq',
            and_true]
          rw [derives_valtypeSub_iff h]
          constructor
          · rintro ((hp | hr | hb) | hp)
            · exact absurd hp (tyVal_ne_pack t₁ p)
            · exact absurd hr (not_derives_reftypeSub_packR h)
            · exact Or.inr (tyVal_isBot hb)
            · exact absurd hp (tyVal_ne_pack t₁ p)
          · rintro (hs | rfl)
            · exact absurd hs not_sub_val_pack
            · exact Or.inl (Or.inr (Or.inr rfl))
  | pack p =>
      cases z₂ with
      | val t₂ =>
          simp only [tyV, StorageGap, reduceCtorEq, false_and, or_false]
          rw [derives_valtypeSub_iff h]
          constructor
          · rintro ((he | hr | hb) | he)
            · exact absurd he.symm (tyVal_ne_pack t₂ p)
            · exact absurd hr (not_derives_reftypeSub_packL h)
            · exact absurd hb (by cases p <;> simp [packtypeV])
            · exact absurd he.symm (tyVal_ne_pack t₂ p)
          · intro hs; exact absurd hs not_sub_pack_val
      | pack p₂ =>
          simp only [tyV, StorageGap, sub_pack_pack_iff, reduceCtorEq, false_and,
            or_false]
          rw [derives_valtypeSub_iff h]
          constructor
          · rintro ((he | hr | hb) | he)
            · exact packtypeV_inj he
            · exact absurd hr (not_derives_reftypeSub_packL h)
            · exact absurd hb (by cases p <;> simp [packtypeV])
            · exact packtypeV_inj he
          · rintro rfl; exact Or.inr rfl

/-- **`Fieldtype_sub` agrees with `Sub` at the field sort**, away from the
`StorageGap`. -/
theorem fieldtypeSub_agree {env : Env} {C : Context} (h : HasTyping env)
    (ha : HeapSubAgree env C) (m₁ m₂ : Wasm.Mutability) (z₁ z₂ : CStorageType)
    (hg : ¬ StorageGap z₁ z₂) (hg' : ¬ StorageGap z₂ z₁) :
    Derives env "Fieldtype_sub" "%|-%<:%" []
        (.tuple [ctxV C, tyV (Ty.field m₁ z₁), tyV (Ty.field m₂ z₂)]) ↔
      Sub C.toTypeCtx (Ty.field m₁ z₁) (Ty.field m₂ z₂) := by
  simp only [tyV]
  rw [derives_fieldtypeSub_iff h, sub_field_iff, storagetypeSub_agree h ha,
    storagetypeSub_agree h ha]
  constructor
  · rintro ⟨rfl, hs, hv⟩
    refine ⟨rfl, hs.resolve_right hg, fun hm => ?_⟩
    exact (hv hm).resolve_right hg'
  · rintro ⟨rfl, hs, hv⟩
    exact ⟨rfl, Or.inl hs, fun hm => Or.inl (hv hm)⟩

/-! ## The finding, as theorems

`Silmaril/Wasm/Validation/Subtyping.lean`'s `TyOk` is the real §2.1 judgment:
it reads `C.TYPES` and `C.RECS`.  The SpecTec side, interpreted by
`Sem/Eval.lean`'s `derives`, is not — and the gap is not repairable by adding
a top-level `HasTyp` side condition, because the subject of the offending
rules is a well-sorted value in the first place. -/

/-- Silmaril's `TyOk` rejects a reference to a type index the context does not
have. -/
theorem not_tyOk_refIdx (x : Nat) :
    ¬ TyOk (⟨[], []⟩ : TypeCtx) (Ty.refv (.ref true (.use (.idx x)))) := by
  intro hs
  cases hs with
  | refv hr =>
      cases hr with
      | ref hh =>
          cases hh with
          | use hu =>
              cases hu with
              | idx hd => simp at hd

/-- SpecTec's `Valtype_ok`, as `derives` interprets it, accepts that same
value type in the empty context. -/
theorem derives_valtypeOk_refIdx {env : Env} (h : HasTyping env) (x : Nat) :
    Derives env "Valtype_ok" "%|-%:OK" []
      (.tuple [ctxV {}, tyV (Ty.refv (.ref true (.use (.idx x))))]) :=
  derives_valtypeOk h _ _

/-- **So the two do not agree at `Valtype_ok`.**  Note that the counterexample
is a perfectly well-sorted `valtype`: the gap is `anyRule` ignoring a
`RuleD`'s quantifiers, not a missing top-level typing side condition. -/
theorem valtypeOk_not_agree {env : Env} (h : HasTyping env) :
    ¬ ∀ (C : Context) (t : CValType),
        Derives env "Valtype_ok" "%|-%:OK" [] (.tuple [ctxV C, tyV t]) ↔
          TyOk C.toTypeCtx t := by
  intro hall
  exact not_tyOk_refIdx 0
    ((hall {} (Ty.refv (.ref true (.use (.idx 0))))).1 (derives_valtypeOk h _ _))

/-- The direction that does hold, and holds trivially: a Silmaril derivation
of well-formedness gives a SpecTec one. -/
theorem derives_valtypeOk_of_tyOk {env : Env} (h : HasTyping env) (C : Context)
    (t : CValType) (_ : TyOk C.toTypeCtx t) :
    Derives env "Valtype_ok" "%|-%:OK" [] (.tuple [ctxV C, tyV t]) :=
  derives_valtypeOk h _ _

/-- The same gap at the storage sort, in the form `storagetypeSub_agree`
measures it: `BOT <: I8` is derivable in SpecTec and false in Silmaril. -/
theorem derives_storagetypeSub_botv_pack {env : Env} (h : HasTyping env)
    (C : Context) (p : Wasm.PackType) :
    Derives env "Storagetype_sub" "%|-%<:%" []
      (.tuple [ctxV C, tyV (Ty.val .botv), tyV (Ty.pack p)]) := by
  rw [derives_storagetypeSub_iff h, derives_valtypeSub_iff h]
  exact Or.inl (Or.inr (Or.inr rfl))

/-- …and Silmaril rejects it. -/
theorem not_sub_botv_pack (Δ : TypeCtx) (p : Wasm.PackType) :
    ¬ Sub Δ (Ty.val .botv) (Ty.pack p) := not_sub_val_pack

/-- The gap is exactly `StorageGap`, by `storagetypeSub_agree`. -/
theorem storageGap_botv_pack (p : Wasm.PackType) :
    StorageGap (Ty.val .botv) (Ty.pack p) := ⟨rfl, p, rfl⟩

/-! ## Instruction typing -/

/-- `Instr_ok/nop`, rule 0 of the relation. -/
def instrOkNopRule : Rule :=
  (.ruleD "nop" [(.expP "C" (.varT "context" []))] "%|-%:%" (.tupE [(.varE "C"), (.caseE "NOP"
   (.tupE [])), (.caseE "%->_%%" (.tupE [(.caseE "%" (.tupE [(.listE [])])), (.listE []),
   (.caseE "%" (.tupE [(.listE [])]))]))]) [])

/-- `Instr_ok/drop`, rule 2 of the relation. -/
def instrOkDropRule : Rule :=
  (.ruleD "drop" [(.expP "C" (.varT "context" [])), (.expP "t" (.varT "valtype" []))] "%|-%:%"
   (.tupE [(.varE "C"), (.caseE "DROP" (.tupE [])), (.caseE "%->_%%" (.tupE [(.caseE "%" (.tupE
   [(.listE [(.varE "t")])])), (.listE []), (.caseE "%" (.tupE [(.listE [])]))]))]) [(.rulePr
   "Valtype_ok" [] "%|-%:OK" (.tupE [(.varE "C"), (.varE "t")]))])

/-- `Instr_ok/local.get`, rule 52 of the relation. -/
def instrOkLocalGetRule : Rule :=
  (.ruleD "local.get" [(.expP "C" (.varT "context" [])), (.expP "x" (.varT "idx" [])), (.expP
   "t" (.varT "valtype" []))] "%|-%:%" (.tupE [(.varE "C"), (.caseE "LOCAL.GET" (.varE "x")),
   (.caseE "%->_%%" (.tupE [(.caseE "%" (.tupE [(.listE [])])), (.listE []), (.caseE "%" (.tupE
   [(.listE [(.varE "t")])]))]))]) [(.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C")
   "LOCALS") (.projE (.uncaseE (.varE "x") "%") (0))) (.caseE "%%" (.tupE [(.caseE "SET" (.tupE
   [])), (.varE "t")]))))])

/-- `Instr_ok/const`, rule 82 of the relation. -/
def instrOkConstRule : Rule :=
  (.ruleD "const" [(.expP "C" (.varT "context" [])), (.expP "nt" (.varT "numtype" [])), (.expP
   "c_nt" (.varT "num_" [(.expA (.varE "nt"))]))] "%|-%:%" (.tupE [(.varE "C"), (.caseE "CONST"
   (.tupE [(.varE "nt"), (.varE "c_nt")])), (.caseE "%->_%%" (.tupE [(.caseE "%" (.tupE [(.listE
   [])])), (.listE []), (.caseE "%" (.tupE [(.listE [(.subE (.varE "nt") (.varT "numtype" [])
   (.varT "valtype" []))])]))]))]) [])

/-- `Instr_ok/binop`, rule 84 of the relation. -/
def instrOkBinopRule : Rule :=
  (.ruleD "binop" [(.expP "C" (.varT "context" [])), (.expP "nt" (.varT "numtype" [])), (.expP
   "binop_nt" (.varT "binop_" [(.expA (.varE "nt"))]))] "%|-%:%" (.tupE [(.varE "C"), (.caseE
   "BINOP" (.tupE [(.varE "nt"), (.varE "binop_nt")])), (.caseE "%->_%%" (.tupE [(.caseE "%"
   (.tupE [(.listE [(.subE (.varE "nt") (.varT "numtype" []) (.varT "valtype" [])), (.subE
   (.varE "nt") (.varT "numtype" []) (.varT "valtype" []))])])), (.listE []), (.caseE "%" (.tupE
   [(.listE [(.subE (.varE "nt") (.varT "numtype" []) (.varT "valtype" []))])]))]))]) [])

/-- `Instr_ok/relop`, rule 86 of the relation. -/
def instrOkRelopRule : Rule :=
  (.ruleD "relop" [(.expP "C" (.varT "context" [])), (.expP "nt" (.varT "numtype" [])), (.expP
   "relop_nt" (.varT "relop_" [(.expA (.varE "nt"))]))] "%|-%:%" (.tupE [(.varE "C"), (.caseE
   "RELOP" (.tupE [(.varE "nt"), (.varE "relop_nt")])), (.caseE "%->_%%" (.tupE [(.caseE "%"
   (.tupE [(.listE [(.subE (.varE "nt") (.varT "numtype" []) (.varT "valtype" [])), (.subE
   (.varE "nt") (.varT "numtype" []) (.varT "valtype" []))])])), (.listE []), (.caseE "%" (.tupE
   [(.listE [(.caseE "I32" (.tupE []))])]))]))]) [])
/-- The `k`-th rule of a parameterless relation, as the pinned stream records
it.  `Instr_ok` has 110 rules and its `RelD` prints to 88 000 characters, so
its provenance is recorded one rule at a time, by index, rather than by
spelling the whole list out as `HasTyping` does. -/
def HasRuleAt (env : Env) (x : IL.Id) (op : MixopS) (k : Nat) (r : Rule) : Prop :=
  ∃ ps t rules, env.findRel? x = some (ps, op, t, rules) ∧ ps = [] ∧ rules[k]? = some r

/-- A rule that is in the relation and fires gives a derivation. -/
theorem derives_of_ruleAt {env : Env} {x : IL.Id} {op : MixopS} {k : Nat} {r : Rule}
    (h : HasRuleAt env x op k r) {v : Value} (hf : RuleFires env op [] [] v r) :
    Derives env x op [] v := by
  obtain ⟨ps, t, rules, hr, rfl, hk⟩ := h
  exact derives_iff.2 ⟨[], t, rules, hr, r, List.mem_of_getElem? hk, hf⟩

/-- The six `Instr_ok` rules this file reaches, at their indices in the
pinned stream. -/
structure HasInstrRules (env : Env) : Prop where
  /-- `Instr_ok/nop`. -/
  nop : HasRuleAt env "Instr_ok" "%|-%:%" 0 instrOkNopRule
  /-- `Instr_ok/drop`. -/
  drop : HasRuleAt env "Instr_ok" "%|-%:%" 2 instrOkDropRule
  /-- `Instr_ok/local.get`. -/
  localGet : HasRuleAt env "Instr_ok" "%|-%:%" 52 instrOkLocalGetRule
  /-- `Instr_ok/const`. -/
  const : HasRuleAt env "Instr_ok" "%|-%:%" 82 instrOkConstRule
  /-- `Instr_ok/binop`. -/
  binop : HasRuleAt env "Instr_ok" "%|-%:%" 84 instrOkBinopRule
  /-- `Instr_ok/relop`. -/
  relop : HasRuleAt env "Instr_ok" "%|-%:%" 86 instrOkRelopRule

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- The pinned wasm-3.0 specification has those six rules at those indices. -/
theorem hasInstrRules_wasm30 : HasInstrRules (envOfScript Specs.wasm30) :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-! ### The instruction types, and six rules of `Instr_ok`

`Instr_ok` (`2.3-validation.instructions.spectec:5`) has 110 rules and its
`RelD` prints to 88 000 characters, far too wide to transcribe.  `HasRuleAt`
records the provenance of a *single* rule, by index, and `derives_of_ruleAt`
turns "that rule fires" into `Derives`.  Each theorem below is an exact
characterisation of when one rule fires — both directions — but **not** a
characterisation of `Derives`, which would need all 110 rules; see "What is
not reached". -/

/-- `instrtype = resulttype ->_(localidx*) resulttype`
(`2.0-validation.contexts.spectec:14-15`). -/
def instrtypeV (it : InstrType) : Value :=
  .case "%->_%%"
    (.tuple [resulttypeV it.params, .list (it.inits.map idxV), resulttypeV it.results])

/-- `Instr_ok/nop` (`2.3-validation.instructions.spectec:18-19`) fires at
exactly one instruction and one instruction type. -/
theorem ruleFires_instrOk_nop_iff {env : Env} {c i t : Value} :
    RuleFires env "%|-%:%" [] [] (.tuple [c, i, t]) instrOkNopRule ↔
      i = .case "NOP" (.tuple []) ∧ t = instrtypeV (.plain [] []) := by
  simp only [instrOkNopRule, instrtypeV, resulttypeV, percentV, caseV, List.map_nil]
  rule_simp

/-- `Instr_ok/drop` (`2.3:25-27`).  Its premise `Valtype_ok: C |- t : OK` is
vacuous — `derives_valtypeOk` — so the rule fires at *every* one-element
parameter stack, whatever the context says. -/
theorem ruleFires_instrOk_drop_iff {env : Env} (h : HasTyping env) {c i t : Value} :
    RuleFires env "%|-%:%" [] [] (.tuple [c, i, t]) instrOkDropRule ↔
      i = .case "DROP" (.tuple []) ∧
        ∃ u : Value, t = .case "%->_%%"
          (.tuple [percentV (.list [u]), .list [], percentV (.list [])]) := by
  simp only [instrOkDropRule, percentV, caseV]
  rule_simp
  constructor
  · rintro ⟨u, ⟨hi, ht⟩, -⟩; exact ⟨hi, u, ht⟩
  · rintro ⟨hi, u, ht⟩; exact ⟨u, ⟨hi, ht⟩, derives_valtypeOk h c u⟩

/-- `Instr_ok/const` (`2.3:520-521`): the constant's *value* is unconstrained
(it is a bare pattern variable), and the result type is the number type. -/
theorem ruleFires_instrOk_const_iff {env : Env} {c i t : Value} :
    RuleFires env "%|-%:%" [] [] (.tuple [c, i, t]) instrOkConstRule ↔
      ∃ nt u : Value, i = .case "CONST" (.tuple [nt, u]) ∧
        t = .case "%->_%%"
          (.tuple [percentV (.list []), .list [], percentV (.list [nt])]) := by
  simp only [instrOkConstRule, percentV, caseV]
  rule_simp

/-- `Instr_ok/binop` (`2.3:526-527`). -/
theorem ruleFires_instrOk_binop_iff {env : Env} {c i t : Value} :
    RuleFires env "%|-%:%" [] [] (.tuple [c, i, t]) instrOkBinopRule ↔
      ∃ nt u : Value, i = .case "BINOP" (.tuple [nt, u]) ∧
        t = .case "%->_%%"
          (.tuple [percentV (.list [nt, nt]), .list [], percentV (.list [nt])]) := by
  simp only [instrOkBinopRule, percentV, caseV]
  rule_simp

/-- `Instr_ok/relop` (`2.3:532-533`). -/
theorem ruleFires_instrOk_relop_iff {env : Env} {c i t : Value} :
    RuleFires env "%|-%:%" [] [] (.tuple [c, i, t]) instrOkRelopRule ↔
      ∃ nt u : Value, i = .case "RELOP" (.tuple [nt, u]) ∧
        t = .case "%->_%%"
          (.tuple [percentV (.list [nt, nt]), .list [],
            percentV (.list [.case "I32" (.tuple [])])]) := by
  simp only [instrOkRelopRule, percentV, caseV]
  rule_simp

/-- An equality test is settled by structural equality of the operands
(`spectec/src/il/eval.ml:260-263`). -/
theorem cmpValues_eq_ok_true {v₁ v₂ : Value} :
    cmpValues .eqOp v₁ v₂ = .ok (.bool true) ↔ v₁ = v₂ := by
  simp [cmpValues]

/-- `Instr_ok/local.get` (`2.3:343-345`): `C.LOCALS[x]` must be `SET t`.

The index `x` is read with `x!%.0`, a projection out of the one-case variant
`idx = u32 = %(nat)`, and `evalExp` only asks for component `0`: a `LOCAL.GET`
payload with *extra* components still fires the rule.  That is the same sort
erasure the `*_ok` relations exhibit; `ruleFires_instrOk_localGet` below is
the well-sorted instance. -/
theorem ruleFires_instrOk_localGet_iff {env : Env} {c i t : Value} :
    RuleFires env "%|-%:%" [] [] (.tuple [c, i, t]) instrOkLocalGetRule ↔
      ∃ (u ls : Value) (n : Nat) (vs : List Value),
        (i = .case "LOCAL.GET" (.case "%" (.tuple vs)) ∧
          t = .case "%->_%%"
            (.tuple [percentV (.list []), .list [], percentV (.list [u])])) ∧
        c.field? "LOCALS" = some ls ∧ vs[0]? = some (natV n) ∧
        ls.idx? n = some (.case "%%" (.tuple [.case "SET" (.tuple []), u])) := by
  simp only [instrOkLocalGetRule, percentV, caseV, natV]
  simp +contextual [ruleFires_nil_iff, matchExp_tup_iff, matchExps_cons_iff,
    matchExps_nil_iff, matchExp_var_iff, matchExp_case_iff, matchExp_list_iff,
    premsHold_nil_iff, premsHold_cons_iff, premHolds_if_iff, evalExp_tupE_iff,
    evalExps_nil_iff, evalExps_cons_iff, evalExp_varE_iff, evalExp_cmpE_iff,
    evalExp_dotE_iff, evalExp_idxE_iff, evalExp_uncaseE_iff, evalExp_projE_iff,
    evalExp_caseE_iff, cmpValues_eq_ok_true,
    VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.empty, Map.bind, Map.find?]

/-- The well-sorted instance of `ruleFires_instrOk_localGet_iff`. -/
theorem ruleFires_instrOk_localGet {env : Env} {c ls u : Value} (n : Nat)
    (hls : c.field? "LOCALS" = some ls)
    (hl : ls.idx? n = some (.case "%%" (.tuple [.case "SET" (.tuple []), u]))) :
    RuleFires env "%|-%:%" [] []
      (.tuple [c, .case "LOCAL.GET" (idxV n),
        .case "%->_%%" (.tuple [percentV (.list []), .list [], percentV (.list [u])])])
      instrOkLocalGetRule :=
  ruleFires_instrOk_localGet_iff.2 ⟨u, ls, n, [natV n], ⟨rfl, rfl⟩, hls, rfl, hl⟩

/-! ### Six instructions, bridged to Silmaril

Each theorem reads: whenever Silmaril's typing family assigns `it` to the
instruction, the pinned `Instr_ok` rule derives the *encoded* judgment with
the *encoded* instruction type.  Only this direction is available here; the
converse would have to rule out the other 109 rules of `Instr_ok`. -/

/-- `Instr_ok/nop` against `ParametricInstrOk.nop`. -/
theorem derives_instrOk_nop {env : Env} (hr : HasInstrRules env) (C : Context)
    (it : InstrType) (hs : ParametricInstrOk C .nop it) :
    Derives env "Instr_ok" "%|-%:%" []
      (.tuple [ctxV C, .case "NOP" (.tuple []), instrtypeV it]) := by
  cases hs
  exact derives_of_ruleAt hr.nop (ruleFires_instrOk_nop_iff.2 ⟨rfl, rfl⟩)

/-- `Instr_ok/drop` against `ParametricInstrOk.drop`. -/
theorem derives_instrOk_drop {env : Env} (h : HasTyping env) (hr : HasInstrRules env)
    (C : Context) (it : InstrType) (hs : ParametricInstrOk C .drop it) :
    Derives env "Instr_ok" "%|-%:%" []
      (.tuple [ctxV C, .case "DROP" (.tuple []), instrtypeV it]) := by
  cases hs with
  | @drop t _ =>
      exact derives_of_ruleAt hr.drop ((ruleFires_instrOk_drop_iff h).2 ⟨rfl, tyV t, rfl⟩)

/-- `Instr_ok/const` against `NumericInstrOk.intConst`.  The rule binds the
constant with a bare pattern variable, so any encoding `u` of the immediate
works; the *type* is the one Silmaril assigns. -/
theorem derives_instrOk_intConst {env : Env} (hr : HasInstrRules env) (C : Context)
    (t : Wasm.IntType) (b : BitVec t.width) (u : Value) (it : InstrType)
    (hs : NumericInstrOk C (.intConst t b) it) :
    Derives env "Instr_ok" "%|-%:%" []
      (.tuple [ctxV C, .case "CONST" (.tuple [numtypeV (.int t), u]), instrtypeV it]) := by
  cases hs
  refine derives_of_ruleAt hr.const (ruleFires_instrOk_const_iff.2 ⟨_, u, rfl, ?_⟩)
  cases t <;> rfl

/-- `Instr_ok/binop` against `NumericInstrOk.intBinOp`. -/
theorem derives_instrOk_intBinOp {env : Env} (hr : HasInstrRules env) (C : Context)
    (t : Wasm.IntType) (op : Wasm.IntBinOp) (u : Value) (it : InstrType)
    (hs : NumericInstrOk C (.intBinOp t op) it) :
    Derives env "Instr_ok" "%|-%:%" []
      (.tuple [ctxV C, .case "BINOP" (.tuple [numtypeV (.int t), u]), instrtypeV it]) := by
  cases hs
  refine derives_of_ruleAt hr.binop (ruleFires_instrOk_binop_iff.2 ⟨_, u, rfl, ?_⟩)
  cases t <;> rfl

/-- `Instr_ok/relop` against `NumericInstrOk.intRelOp`. -/
theorem derives_instrOk_intRelOp {env : Env} (hr : HasInstrRules env) (C : Context)
    (t : Wasm.IntType) (op : Wasm.IntRelOp) (u : Value) (it : InstrType)
    (hs : NumericInstrOk C (.intRelOp t op) it) :
    Derives env "Instr_ok" "%|-%:%" []
      (.tuple [ctxV C, .case "RELOP" (.tuple [numtypeV (.int t), u]), instrtypeV it]) := by
  cases hs
  refine derives_of_ruleAt hr.relop (ruleFires_instrOk_relop_iff.2 ⟨_, u, rfl, ?_⟩)
  cases t <;> rfl

/-- The `LOCALS` field of an encoded context. -/
theorem ctxV_locals (C : Context) :
    (ctxV C).field? "LOCALS" = some (.list (C.locals.map localtypeV)) := by
  simp [ctxV, Value.field?]

/-- `Instr_ok/local.get` against `Silmaril/Wasm/Validation/Context.lean`'s
`LOCALS`.  `VariableInstrOk` is not imported here, so the Silmaril side is
stated as the context lookup the rule needs. -/
theorem derives_instrOk_localGet {env : Env} (hr : HasInstrRules env) (C : Context)
    (n : Nat) (u : CValType) (hl : C.locals[n]? = some ⟨.set, u⟩) :
    Derives env "Instr_ok" "%|-%:%" []
      (.tuple [ctxV C, .case "LOCAL.GET" (idxV n), instrtypeV (.plain [] [u])]) := by
  refine derives_of_ruleAt hr.localGet ?_
  have hidx : Value.idx? (.list (C.locals.map localtypeV)) n
      = some (.case "%%" (.tuple [.case "SET" (.tuple []), tyV u])) := by
    simp only [Value.idx?, List.getElem?_map, hl, Option.map_some]
    rfl
  have := ruleFires_instrOk_localGet (env := env) (c := ctxV C) n (ctxV_locals C) hidx
  simpa only [instrtypeV, resulttypeV, InstrType.plain, List.map_nil, List.map_cons] using this

/-! ## What is not reached

Stated precisely, because the theorems above are deliberately narrow.

* **`Heaptype_sub` (`2.2:9,20-102`).**  Not proved, in either direction.  Its
  twenty rules include `trans` (an arbitrary intermediate heap type),
  `typeidx-l`/`typeidx-r` (a lookup in `C.TYPES` on either side) and the four
  `none`/`nofunc`/`noexn`/`noextern` rules, whose premises point *back* into
  `Heaptype_sub`; and `Silmaril/Wasm/Validation/Subtyping.lean`'s `Sub` is one
  mutual inductive with `TyOk`, `SubOk2` and `GroupOk2`, so the soundness
  direction is a mutual induction over all four.  `HeapSubAgree` names the
  statement; every agreement theorem above takes it as a hypothesis and
  nothing in this file discharges it.  Note also the audit note on
  `Sub.recStruct` in `Validation/Subtyping.lean`: the Lean side is
  deliberately *larger* than the literal spec rule there, so `HeapSubAgree`
  is not obviously true and should be investigated before it is assumed.

* **`Heaptype_ok`'s `typeuse` rule, `Typeuse_ok`, `Deftype_ok`,
  `Subtype_ok`, `Subtype_ok2`, `Rectype_ok`, `Rectype_ok2`, `Comptype_ok`,
  `Comptype_sub`, `Deftype_sub`, `Expand`, `Expand_use`.**  Transcribed by
  nothing here.  `derives_heaptypeOk` makes them unnecessary for the `*_ok`
  results, because the `abs` rule already fires everywhere — which is the
  finding, not a proof about them.

* **`Resulttype_sub` (`2.2:132,135-137`) and `Resulttype_ok` (`2.1:53,60-62`).**
  Their provenance is checked (`HasTyping.resulttypeSubD`,
  `HasTyping.resulttypeOkD`) but nothing is claimed about what they derive.
  Both conclusions match a `%`-wrapped list with an `IterE` over a `List`
  domain and both premises are an `IterPr`, so they need `matchIterE`/
  `matchIterList`/`matchRounds` and `premIter`/`premRounds` inversion lemmas
  that this file does not build.  `Silmaril/Wasm/Validation/Subtyping.lean`'s
  `ResultSub` is the Lean side they would be compared against.

* **`Instrtype_ok`, `Instrtype_sub`, `Localtype_ok` against `LocalType`.**
  `derives_localtypeOk` is proved but only as another instance of the
  finding; `InstrTypeOk` and `InstrTypeSub` are not related to anything.

* **`Instr_ok` as a relation.**  Only *six of its 110 rules* are reached, and
  only as `RuleFires` characterisations plus the Silmaril-to-SpecTec
  direction.  "`Derives env "Instr_ok" … v` implies the Silmaril judgment"
  would have to rule out the other 109 rules at every value, which needs the
  whole 88 000-character `RelD` as a Lean term.  `unreachable`, `block`,
  `loop`, `if`, `br` and `br_table` additionally need the `IterE`/`CatE`
  machinery above.  `Instrs_ok`, `Expr_ok` and everything in
  `2.4-validation.modules.spectec` are untouched.

* **The immediates of `CONST`, `BINOP` and `RELOP`.**  The rules bind them
  with bare pattern variables, so `derives_instrOk_intConst` and friends are
  stated for an *arbitrary* value in that position.  A bridge for
  `num_(nt)`, `binop_(nt)` and `relop_(nt)` against Silmaril's `BitVec`,
  `IntBinOp` and `IntRelOp` is not built.

* **`ctxV` is not proved injective.**  `ctxV_typeCtx_inj` recovers `TYPES`
  and `RECS` — the two fields the subtyping judgments read — and
  `ctxV_locals`/`ctxV_labels` read two more; the remaining nine fields need
  injectivity of `globaltypeV`, `memtypeV`, `tabletypeV` and `limitsV`, which
  is not proved.

* **Nothing here is a statement about `Sem/Type.lean`'s `HasTyp`.**  The
  finding above says that is exactly what is missing from `anyRule`, and
  repairing it is upstream work, not work this file can do.
-/

end Silmaril.SpecTec.Equiv.Validation
