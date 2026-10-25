module

public import Silmaril.Wasm.V2.Validation.Context

/-!
# WebAssembly 2.0 instruction typing

Transcribed from the official SpecTec source
`specification/wasm-2.0/6-typing.spectec`, sections `Instructions`
(`6-typing:138-532`) and `Expressions` (`6-typing:147-151`), at WebAssembly/spec
revision `608711107b7f1edb13efd57b7d79b49477462d36` (see
`specs/wasm/core-2.0.json`). Line references of the form `6-typing:NN` point
into that file; `1-syntax:NN` into `specification/wasm-2.0/1-syntax.spectec`.

Every `rule Instr_ok/<name>` of `6-typing` has exactly one constructor of
`InstrOk`, except where the 2.0 instruction syntax was flattened (see below).
`InstrsOk` has exactly the five rules `Instrs_ok/{empty,instr,seq,sub,frame}`
(`6-typing:156-177`); `InstrsOk.cons` is a *derived lemma*, not a constructor,
because `seq` is kept.

## Flattened constructors

`Silmaril.Wasm.V2.Instr` splits SpecTec's type-indexed instruction families into
one constructor per index family, because `unop_(numtype)` and friends are
dependent syntax that Lean's plain inductives cannot express. Each such SpecTec
rule therefore has several constructors here, with identical premises:

| SpecTec rule | constructors |
|---|---|
| `Instr_ok/const` (`6-typing:264`) | `intConst`, `floatConst` |
| `Instr_ok/unop` (`6-typing:267`) | `intUnOp`, `floatUnOp` |
| `Instr_ok/binop` (`6-typing:270`) | `intBinOp`, `floatBinOp` |
| `Instr_ok/testop` (`6-typing:273`) | `intTestOp` (`testop_(Fnn)` is uninhabited, `1-syntax:295`) |
| `Instr_ok/relop` (`6-typing:276`) | `intRelOp`, `floatRelOp` |
| `Instr_ok/vunop` (`6-typing:319`) | `vecIntUnOp`, `vecFloatUnOp` |
| `Instr_ok/vbinop` (`6-typing:322`) | `vecIntBinOp`, `vecFloatBinOp` |
| `Instr_ok/vtestop` (`6-typing:325`) | `vecAllTrue` (`vtestop_(Fnn X M)` is uninhabited, `1-syntax:354`) |
| `Instr_ok/vrelop` (`6-typing:328`) | `vecIntRelOp`, `vecFloatRelOp` |
| `Instr_ok/load-val` (`6-typing:468`) | `intLoadVal`, `floatLoadVal` |
| `Instr_ok/store-val` (`6-typing:487`) | `intStoreVal`, `floatStoreVal` |

Conversely, SpecTec's `VLOAD V128 vloadop? memarg` is one Lean constructor
`Instr.vecLoad` whose `vloadop?` immediate `Silmaril.Wasm.V2.VecLoadOp` is
already flattened, so the four rules `/vload-val`, `/vload-pack`,
`/vload-splat`, `/vload-zero` select on it; `VecLoadOp.packShape` and
`VecLoadOp.zeroWidth` recover SpecTec's `SHAPE M X N _ sx` and `ZERO n`
decompositions.

## Syntactic side conditions are typing premises here

SpecTec attaches side conditions to the *syntax* productions: `vbinop_(Jnn X M)`
admits `MUL` only `-- if $lsizenn(Jnn) >= 16` (`1-syntax:345`), `VEXTRACT_LANE`
carries `-- if $lanetype(shape) = numtype <=> sx? = eps` (`1-syntax:460`), and so
on. A SpecTec `instr` that violates them is not a term of the syntax at all, so
`Instr_ok` never sees it. Our flattened `Instr` *can* represent such a term, and
`Silmaril.Wasm.V2.Instr.immediatesValid` is where those conditions were
collected. The typing rules below re-impose them clause by clause, using exactly
the predicates of `Silmaril/Wasm/V2/Ops.lean` that `immediatesValid` uses;
`InstrOk.immediatesValid` states that the two agree.

This matters for soundness, not only for faithfulness: without the premises,
`VBINOP (I8 X 16) MUL` or `VCVTOP (I8 X 16) (F64 X 2) (EXTEND LOW S)` would be
well typed while no `Step_pure/*` rule applies to them, and progress would fail.
Carrying the `vcvtop` conditions is decided deviation 3 of this development
(`1-syntax:472` says `;; TODO: missing constraints` and `Instr_ok/vcvtop`
(`6-typing:365`) is correspondingly unconditional); see `Silmaril.Wasm.V2.Validation`.

**Deviation (`C.REFS`).** `Instr_ok/ref.func` (`6-typing:294`) has the single
premise `C.FUNCS[x] = ft`; the `6-typing` context (`6-typing:5-9`) has no `REFS`
field and `Module_ok` records `;; TODO: refs` (`6-typing:681`). The W3C 2.0 prose
and the reference interpreter both require in addition that `x` be *declared*:
`interpreter/valid/valid.ml:720-723` reads

```
| RefFunc x ->
  let dt = func c x in
  refer_func c x;
  [] --> [RefT (NoNull, UseHT (Def dt))], []
```

The pinned interpreter is the 3.0 one, so the result type is 3.0's; the 2.0-era
text (`git show wg-2.0:interpreter/valid/valid.ml`, lines 419-422) is
`let _ft = func c x in refer_func c x; [] --> [RefType FuncRefType]`. What
matters here is the `refer_func c x` call — the declaredness check — which both
revisions make. And `test/core/ref_func.wast` has `assert_invalid` modules whose
only fault is an undeclared `ref.func`. Core 3.0 has the field
(`Silmaril/Wasm/Validation/Context.lean`). We follow the reference interpreter:
`InstrOk.refFunc` carries `x ∈ C.refs` in addition to `C.FUNCS[x] = ft`. This is
decided deviation 6; see `Silmaril.Wasm.V2.Validation`.

**Observation (`Instr_ok/cvtop-convert`).** `6-typing:280` carries the author's
note `;; TODO: move side conditions to syntax`, and the two rules that follow are
`/cvtop-reinterpret`, which requires `$size(nt_1) = $size(nt_2)`, and
`/cvtop-convert`, whose operator is the *unrestricted* metavariable `cvtop`
(`1-syntax:305`). Read literally, `/cvtop-convert` subsumes `/cvtop-reinterpret`
and types combinations such as `CVTOP I32 F32 WRAP` for which `$cvtop__`
(`3-numerics:310-318`) has no equation, so no `Step_pure/cvtop-*` rule applies.
Core 3.0 repaired this by indexing the syntax, `cvtop__(numtype_1, numtype_2)`
(`wasm-3.0/1.3-syntax.instructions.spectec:55-68`), after which its single
`Instr_ok/cvtop` is sound; the reference interpreter never had the problem,
because its `cvtop` constructors fix both types (`exec/eval_num.ml:111-182`,
`valid/valid.ml:304-336`). We transcribe both 2.0 rules **as written**, so
`cvtOpConvert` has no premise beyond the syntactic `nt_1 =/= nt_2` of
`1-syntax:438`. Anyone proving progress for the scalar conversions must either
add the `cvtop__` definedness premise here or handle the gap in the reduction
relation; `Silmaril.Wasm.V2.CvtOp.toShared` is the predicate to use. This is
*not* a deviation — it is SpecTec 2.0's literal content — but it is recorded
here because it is the one place in `6-typing:182-532` where the 2.0 rules are
strictly more liberal than both the 3.0 rules and the reference interpreter.

**Observation (`VNARROW`).** `1-syntax:468-469` constrains `VNARROW ishape_1
ishape_2 sx` by the *chained* comparison
`$($lsize($lanetype(ishape_2)) = 2*$lsize($lanetype(ishape_1)) <= 32)`, i.e. the
operand lane is twice the result lane **and** at most `32`, so the result lane is
at most `16`. The surviving pairs are `(I8 X 16) (I16 X 8)` and
`(I16 X 8) (I32 X 4)`, which are exactly the four opcodes `0xFD 101`, `0xFD 102`,
`0xFD 133`, `0xFD 134` of `A-binary:604-605` and `A-binary:630-631`, and exactly
the four `i8x16.narrow_i16x8_{s,u}` / `i16x8.narrow_i32x4_{s,u}` of
`interpreter/binary/decode.ml:795-796` and `:827-828`. Both sides of this
development impose that chained reading, on the *operand* lane: the `.vecNarrow`
clause of `Silmaril.Wasm.V2.Instr.immediatesValid` is
`source.laneWidth == 2 * target.laneWidth && source.laneWidth ≤ 32`, and
`InstrOk.vecNarrow` below carries `hwidth : sh₂.laneWidth = 2 * sh₁.laneWidth`
together with `hmax : sh₂.laneWidth ≤ 32`. The two therefore agree exactly —
neither is weaker than the other, both reject `VNARROW (I32 X 4) (I64 X 2)`, and
this is not a deviation.

## Points of care

* `select-expl` (`6-typing:192`) is `SELECT t`, i.e. the optional immediate is
  *present* and holds exactly one value type; `valid.ml:443-447` requires
  `List.length ts = 1`. `select-impl` (`6-typing:195`) is the absent immediate,
  and its operand type may be `BOT`: the premise is `|- t <: t'` with
  `t' = numtype \/ t' = vectype` (`NumOrVec`), so `t` is a number type, a vector
  type, or `BOT`.
* `br`, `br_table`, `return` and `unreachable` are stack polymorphic through the
  free `t_1*`/`t_2*` of their conclusions.
* `br_table` (`6-typing:240`) compares the *same* `t*` against every
  `C.LABELS[l]` and against `C.LABELS[l']`, by `Resulttype_sub`, not equality.
* `call_indirect` (`6-typing:252`) requires `C.TABLES[x] = lim FUNCREF`: the
  element type must be exactly `FUNCREF`, there is no subtyping in 2.0.
* `global.get` (`6-typing:386`) matches `mut t` and so accepts either
  mutability; `global.set` (`6-typing:390`) matches `MUT t`, i.e.
  `Mutability.var`.
* `table.copy` (`6-typing:417`) names the element type `rt` *once*, so the two
  tables must have the same element type; `table.init` (`6-typing:422`) shares
  `rt` between the table and the element segment.
* every memory instruction and every load and store uses `C.MEMS[0]`
  (`6-typing:434-532`); 2.0 has no memory index immediate.
* the alignment conditions differ by rule: `load-val` bounds `2^align` by
  `$size(nt)/8`, `load-pack` by `M/8`, `vload-pack` by `M/8 * N` (SpecTec
  divides before multiplying, `6-typing:505`). They are `MemArgOk` and
  `MemArgOkPack` of `Validation/Context.lean`.
* `vshuffle` (`6-typing:340`) bounds every lane by `2*$dim(sh)`; the shape is
  fixed to `I8 X 16` by `1-syntax:457`, so the bound is `32`.
* `vextract_lane`/`vreplace_lane` (`6-typing:348`, `6-typing:352`) bound the lane
  by `$dim(sh)`, and `vload_lane`/`vstore_lane` (`6-typing:517`, `6-typing:528`)
  by `128 / n`.

No deviation from the pinned SpecTec source is taken in this file beyond the
`C.REFS` premise and the `vcvtop` side condition described above.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Validation

/-! ## Auxiliary side conditions -/

/-- `t' = numtype \/ t' = vectype`, the second premise of `Instr_ok/select-impl`
(`6-typing:198`). It excludes reference types (and `BOT`, which is not a
`ValType` here). -/
def NumOrVec (t : ValType) : Prop :=
  (∃ nt : NumType, t = .num nt) ∨ (∃ vt : VecType, t = .vec vt)

instance (t : ValType) : Decidable (NumOrVec t) :=
  match t with
  | .num nt => isTrue (Or.inl ⟨nt, rfl⟩)
  | .vec vt => isTrue (Or.inr ⟨vt, rfl⟩)
  | .ref _ => isFalse (by rintro (⟨_, h⟩ | ⟨_, h⟩) <;> cases h)

/-- The `M` and `N` of `VLOAD V128 (SHAPE M X N _ sx) memarg`, the premise shape
of `Instr_ok/vload-pack` (`6-typing:502`). The three packed vector loads of
`vloadop` (`1-syntax:390`) are `SHAPE 8 X 8`, `SHAPE 16 X 4` and `SHAPE 32 X 2`;
every other `vloadop` is handled by a different rule. -/
def VecLoadOp.packShape : VecLoadOp → Option (Nat × Nat)
  | .shape8x8 _ => some (8, 8)
  | .shape16x4 _ => some (16, 4)
  | .shape32x2 _ => some (32, 2)
  | .splat _ | .zero32 | .zero64 => none

/-- The `n` of `VLOAD V128 (ZERO n) memarg`, the premise shape of
`Instr_ok/vload-zero` (`6-typing:512`). -/
def VecLoadOp.zeroWidth : VecLoadOp → Option Nat
  | .zero32 => some 32
  | .zero64 => some 64
  | .shape8x8 _ | .shape16x4 _ | .shape32x2 _ | .splat _ => none

/-! ## Instruction typing -/

mutual

/-- `Instr_ok: context |- instr : functype` (`6-typing:142`), every rule of
`6-typing:182-532`. The `InstrType` is SpecTec's `t_1* -> t_2*` at the
validation value type, bottom of the stack first. -/
inductive InstrOk : Context → Instr → InstrType → Prop where
  -- Parametric instructions (`6-typing:180-198`).
  /-- `Instr_ok/nop` (`6-typing:182`). -/
  | nop {C : Context} : InstrOk C .nop ⟨[], []⟩
  /-- `Instr_ok/unreachable` (`6-typing:185`): stack polymorphic in both
  directions. -/
  | unreachable {C : Context} {t₁ t₂ : CResultType} : InstrOk C .unreachable ⟨t₁, t₂⟩
  /-- `Instr_ok/drop` (`6-typing:188`): any single operand, including `BOT`. -/
  | drop {C : Context} {t : CValType} : InstrOk C .drop ⟨[t], []⟩
  /-- `Instr_ok/select-expl` (`6-typing:192`). The immediate is present and holds
  exactly one value type, matching `valid.ml:443-447`; there is no subtyping
  premise, so the operands have that type on the nose. -/
  | selectExpl {C : Context} {t : ValType} :
      InstrOk C (.select (some [t])) ⟨[.val t, .val t, .val .i32], [.val t]⟩
  /-- `Instr_ok/select-impl` (`6-typing:195`), with the premises
  `Valtype_sub: |- t <: t'` and `if t' = numtype \/ t' = vectype`. The operand
  type `t` may therefore be `BOT`. -/
  | selectImpl {C : Context} {t : CValType} {t' : ValType}
      (hsub : CValType.Sub t (.val t')) (hnv : NumOrVec t') :
      InstrOk C (.select none) ⟨[t, t, .val .i32], [t]⟩
  -- Block instructions (`6-typing:213-227`).
  /-- `Instr_ok/block` (`6-typing:213`): the body is checked under
  `{LABELS (t_2*)} ++ C`, so a branch out of a block targets its *results*. -/
  | block {C : Context} {bt : BlockType} {body : List Instr} {t₁ t₂ : CResultType}
      (hbt : BlockTypeOk C bt ⟨t₁, t₂⟩)
      (hbody : InstrsOk (C.withLabel t₂) body ⟨t₁, t₂⟩) :
      InstrOk C (.block bt body) ⟨t₁, t₂⟩
  /-- `Instr_ok/loop` (`6-typing:218`): the label is `t_1*`, the *parameters*, so
  a branch to a loop re-enters it. -/
  | loop {C : Context} {bt : BlockType} {body : List Instr} {t₁ t₂ : CResultType}
      (hbt : BlockTypeOk C bt ⟨t₁, t₂⟩)
      (hbody : InstrsOk (C.withLabel t₁) body ⟨t₁, t₂⟩) :
      InstrOk C (.loop bt body) ⟨t₁, t₂⟩
  /-- `Instr_ok/if` (`6-typing:223`): the condition is the topmost operand, so it
  is appended at the *end* of the parameter list. -/
  | if_ {C : Context} {bt : BlockType} {thenBody elseBody : List Instr}
      {t₁ t₂ : CResultType}
      (hbt : BlockTypeOk C bt ⟨t₁, t₂⟩)
      (hthen : InstrsOk (C.withLabel t₂) thenBody ⟨t₁, t₂⟩)
      (helse : InstrsOk (C.withLabel t₂) elseBody ⟨t₁, t₂⟩) :
      InstrOk C (.if_ bt thenBody elseBody) ⟨t₁ ++ [.val .i32], t₂⟩
  -- Branch instructions (`6-typing:230-243`).
  /-- `Instr_ok/br` (`6-typing:232`): stack polymorphic below the label's operands
  and in the results. -/
  | br {C : Context} {l : LabelIdx} {ts t₁ t₂ : CResultType}
      (hl : C.labels[l.toNat]? = some ts) :
      InstrOk C (.br l) ⟨t₁ ++ ts, t₂⟩
  /-- `Instr_ok/br_if` (`6-typing:236`): *not* stack polymorphic, the label's
  operands are passed through. -/
  | brIf {C : Context} {l : LabelIdx} {ts : CResultType}
      (hl : C.labels[l.toNat]? = some ts) :
      InstrOk C (.brIf l) ⟨ts ++ [.val .i32], ts⟩
  /-- `Instr_ok/br_table` (`6-typing:240`): one `Resulttype_sub` premise per
  table entry and one for the default, all against the *same* `t*`. -/
  | brTable {C : Context} {ls : List LabelIdx} {l' : LabelIdx} {ts t₁ t₂ : CResultType}
      (hls : ∀ l ∈ ls, ∃ lt, C.labels[l.toNat]? = some lt ∧ CResultType.Sub ts lt)
      (hl' : ∃ lt, C.labels[l'.toNat]? = some lt ∧ CResultType.Sub ts lt) :
      InstrOk C (.brTable ls l') ⟨t₁ ++ ts ++ [.val .i32], t₂⟩
  -- Function instructions (`6-typing:246-259`).
  /-- `Instr_ok/call` (`6-typing:248`). -/
  | call {C : Context} {x : FuncIdx} {ft : FuncType} (hx : C.funcs[x.toNat]? = some ft) :
      InstrOk C (.call x) (InstrType.lift ft.params ft.results)
  /-- `Instr_ok/call_indirect` (`6-typing:252`): the table's element type must be
  exactly `FUNCREF`, and the type index selects the signature. -/
  | callIndirect {C : Context} {x : TableIdx} {y : TypeIdx} {tt : TableType} {ft : FuncType}
      (hx : C.tables[x.toNat]? = some tt) (hrt : tt.element = .funcref)
      (hy : C.types[y.toNat]? = some ft) :
      InstrOk C (.callIndirect x y)
        ⟨liftResult ft.params ++ [.val .i32], liftResult ft.results⟩
  /-- `Instr_ok/return` (`6-typing:257`): stack polymorphic, like `br`. -/
  | return_ {C : Context} {ts t₁ t₂ : CResultType} (hr : C.return_ = some ts) :
      InstrOk C .return_ ⟨t₁ ++ ts, t₂⟩
  -- Numeric instructions (`6-typing:262-286`).
  /-- `Instr_ok/const` (`6-typing:264`), integer case. -/
  | intConst {C : Context} {t : IntType} {c : BitVec t.width} :
      InstrOk C (.intConst t c) ⟨[], [.val (.num (.int t))]⟩
  /-- `Instr_ok/const` (`6-typing:264`), floating-point case. -/
  | floatConst {C : Context} {t : FloatType} {c : BitVec t.width} :
      InstrOk C (.floatConst t c) ⟨[], [.val (.num (.float t))]⟩
  /-- `Instr_ok/unop` (`6-typing:267`), integer case.

  **Deviation (`EXTEND n` is bounded).** The premise `IntUnOp.valid t op`, i.e.
  `size.width < t.width` for `EXTEND size`, is **not** in SpecTec 2.0.
  `1-syntax:283` reads

  ```
  syntax unop_(Inn) = CLZ | CTZ | POPCNT | EXTEND n
  ```

  with no side condition of any kind — `n` is an unconstrained `nat` — and
  `rule Instr_ok/unop` (`6-typing:267`), `C |- UNOP nt unop_nt : nt -> nt`, is
  premise-free. Read literally, 2.0 therefore types `UNOP I32 (EXTEND 32)` and
  even `UNOP I32 (EXTEND 64)`, and `3-numerics:278`,
  `$unop_(Inn, EXTEND N', iN) = $extend__(N', $sizenn(Inn), S, $wrap__($sizenn(Inn), N', iN))`,
  gives the first of them a meaning (the identity on `i32`), while we reject
  both. We keep the premise:

  1. **`$wrap__` needs it.** `$wrap__(N, N', iN(N)) : iN(N')` (`3-numerics:55`)
     is a *truncation*; for `N' > N`, as in `EXTEND 64` on `I32`, the 2.0
     reduction has no meaning to give `UNOP`.
  2. **The W3C 2.0 prose has no such instruction.** Its concrete syntax
     enumerates exactly `inn.extend8_s`, `inn.extend16_s` and `i64.extend32_s`
     (`document/core/syntax/instructions.rst`, *Numeric Instructions*); there is
     no `i32.extend32_s` and no `extend64_s`.
  3. **The reference interpreter has exactly our side condition**:
     `valid/valid.ml:365-372` is
     `check_pack sz t_sz = require (Pack.packed_size sz < t_sz) "invalid sign extension"`,
     applied to every `ExtendS`; `binary/encode.ml:505,514` reject
     `i32.extend32_s`/`i32.extend64_s`/`i64.extend64_s` as "illegal instruction".
  4. **Wasm 3.0 repaired the syntax**:
     `specification/wasm-3.0/1.3-syntax.instructions.spectec:32` is
     `syntax unop_(Inn) = CLZ | CTZ | POPCNT | EXTEND sz -- if $(sz < $sizenn(Inn))`.
  5. **No opcode reaches the excluded cases**: `A-binary:446-450` encode only
     `UNOP I32 (EXTEND 8|16)` and `UNOP I64 (EXTEND 8|16|32)`, so the premise
     costs nothing on decoded modules.

  Note also that `EXTEND n` ranges over all of `nat` in 2.0, whereas
  `IntUnOp.extend` (`Silmaril/Wasm/Ops.lean`) carries a `PackSize`, i.e. one of
  `8, 16, 32, 64` — the interpreter's `packsize` (`syntax/ast.ml:33`,
  `unop = Clz | Ctz | Popcnt | ExtendS of packsize`) and 3.0's `sz`. The two
  restrictions together make `intUnOp` accept exactly the five encodable
  sign-extension instructions. -/
  | intUnOp {C : Context} {t : IntType} {op : IntUnOp} (hop : IntUnOp.valid t op = true) :
      InstrOk C (.intUnOp t op) ⟨[.val (.num (.int t))], [.val (.num (.int t))]⟩
  /-- `Instr_ok/unop` (`6-typing:267`), floating-point case. -/
  | floatUnOp {C : Context} {t : FloatType} {op : FloatUnOp} :
      InstrOk C (.floatUnOp t op) ⟨[.val (.num (.float t))], [.val (.num (.float t))]⟩
  /-- `Instr_ok/binop` (`6-typing:270`), integer case. -/
  | intBinOp {C : Context} {t : IntType} {op : IntBinOp} :
      InstrOk C (.intBinOp t op)
        ⟨[.val (.num (.int t)), .val (.num (.int t))], [.val (.num (.int t))]⟩
  /-- `Instr_ok/binop` (`6-typing:270`), floating-point case. -/
  | floatBinOp {C : Context} {t : FloatType} {op : FloatBinOp} :
      InstrOk C (.floatBinOp t op)
        ⟨[.val (.num (.float t)), .val (.num (.float t))], [.val (.num (.float t))]⟩
  /-- `Instr_ok/testop` (`6-typing:273`). Only the integer case exists:
  `testop_(Fnn)` is uninhabited (`1-syntax:295`). -/
  | intTestOp {C : Context} {t : IntType} {op : IntTestOp} :
      InstrOk C (.intTestOp t op) ⟨[.val (.num (.int t))], [.val .i32]⟩
  /-- `Instr_ok/relop` (`6-typing:276`), integer case. -/
  | intRelOp {C : Context} {t : IntType} {op : IntRelOp} :
      InstrOk C (.intRelOp t op)
        ⟨[.val (.num (.int t)), .val (.num (.int t))], [.val .i32]⟩
  /-- `Instr_ok/relop` (`6-typing:276`), floating-point case. -/
  | floatRelOp {C : Context} {t : FloatType} {op : FloatRelOp} :
      InstrOk C (.floatRelOp t op)
        ⟨[.val (.num (.float t)), .val (.num (.float t))], [.val .i32]⟩
  /-- `Instr_ok/cvtop-reinterpret` (`6-typing:281`), whose premise is
  `$size(nt_1) = $size(nt_2)`; `nt_1 =/= nt_2` is the syntactic side condition of
  `1-syntax:438`. -/
  | cvtOpReinterpret {C : Context} {t₁ t₂ : NumType}
      (hne : t₁ ≠ t₂) (hsize : t₁.width = t₂.width) :
      InstrOk C (.cvtOp t₁ t₂ .reinterpret) ⟨[.val (.num t₂)], [.val (.num t₁)]⟩
  /-- `Instr_ok/cvtop-convert` (`6-typing:285`), plus the definedness premise of
  **deviation 16**; see the module docstring. SpecTec gives this rule no premise
  and lets `cvtop` range over the whole flat operator syntax, so read literally it
  types `CVTOP I64 I32 WRAP`, for which `$cvtop__` (`3-numerics:310-318`) has no
  equation and no `Step_pure/cvtop-*` rule applies — progress fails. The premise
  `(op.toShared t₁ t₂).isSome` is exactly "`$cvtop__(t₂, t₁, op, ·)` is defined",
  and it is also the `.cvtOp` clause of `Instr.immediatesValid`. -/
  | cvtOpConvert {C : Context} {t₁ t₂ : NumType} {op : CvtOp} (hne : t₁ ≠ t₂)
      (hdef : (op.toShared t₁ t₂).isSome) :
      InstrOk C (.cvtOp t₁ t₂ op) ⟨[.val (.num t₂)], [.val (.num t₁)]⟩
  -- Reference instructions (`6-typing:289-299`).
  /-- `Instr_ok/ref.null` (`6-typing:291`). -/
  | refNull {C : Context} {rt : RefType} : InstrOk C (.refNull rt) ⟨[], [.val (.ref rt)]⟩
  /-- `Instr_ok/ref.func` (`6-typing:294`), plus the `C.REFS` premise of decided
  deviation 6; see the module docstring. -/
  | refFunc {C : Context} {x : FuncIdx} {ft : FuncType}
      (hx : C.funcs[x.toNat]? = some ft) (hrefs : x ∈ C.refs) :
      InstrOk C (.refFunc x) ⟨[], [.val .funcref]⟩
  /-- `Instr_ok/ref.is_null` (`6-typing:298`): any *syntactic* reference type. -/
  | refIsNull {C : Context} {rt : RefType} :
      InstrOk C .refIsNull ⟨[.val (.ref rt)], [.val .i32]⟩
  -- Vector instructions (`6-typing:302-366`).
  /-- `Instr_ok/vconst` (`6-typing:304`). -/
  | vecConst {C : Context} {c : BitVec 128} : InstrOk C (.vecConst c) ⟨[], [.val .v128]⟩
  /-- `Instr_ok/vvunop` (`6-typing:307`). -/
  | vvUnOp {C : Context} {op : VecUnOp} :
      InstrOk C (.vvUnOp op) ⟨[.val .v128], [.val .v128]⟩
  /-- `Instr_ok/vvbinop` (`6-typing:310`). -/
  | vvBinOp {C : Context} {op : VecBinOp} :
      InstrOk C (.vvBinOp op) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vvternop` (`6-typing:313`). -/
  | vvTernOp {C : Context} {op : VecTernOp} :
      InstrOk C (.vvTernOp op) ⟨[.val .v128, .val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vvtestop` (`6-typing:316`). -/
  | vvTestOp {C : Context} {op : VecTestOp} :
      InstrOk C (.vvTestOp op) ⟨[.val .v128], [.val .i32]⟩
  /-- `Instr_ok/vunop` (`6-typing:319`), integer shapes. The premise is the
  syntactic side condition of `vunop_(Jnn X M)` (`1-syntax:335`): `POPCNT` needs
  `Jnn = I8`. -/
  | vecIntUnOp {C : Context} {sh : IntShape} {op : VecIntUnOp}
      (hop : VecIntUnOp.valid sh op = true) :
      InstrOk C (.vecIntUnOp sh op) ⟨[.val .v128], [.val .v128]⟩
  /-- `Instr_ok/vunop` (`6-typing:319`), floating-point shapes. -/
  | vecFloatUnOp {C : Context} {sh : FloatShape} {op : FloatUnOp} :
      InstrOk C (.vecFloatUnOp sh op) ⟨[.val .v128], [.val .v128]⟩
  /-- `Instr_ok/vbinop` (`6-typing:322`), integer shapes, with the lane-width
  side conditions of `vbinop_(Jnn X M)` (`1-syntax:340-349`). -/
  | vecIntBinOp {C : Context} {sh : IntShape} {op : V2.VecIntBinOp}
      (hop : V2.VecIntBinOp.valid sh op = true) :
      InstrOk C (.vecIntBinOp sh op) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vbinop` (`6-typing:322`), floating-point shapes. -/
  | vecFloatBinOp {C : Context} {sh : FloatShape} {op : V2.VecFloatBinOp} :
      InstrOk C (.vecFloatBinOp sh op) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vtestop` (`6-typing:325`). The only inhabitant of
  `vtestop_(Jnn X M)` is `ALL_TRUE` (`1-syntax:353`) and `vtestop_(Fnn X M)` is
  uninhabited (`1-syntax:354`), so `Instr.vecAllTrue` is the whole rule. -/
  | vecAllTrue {C : Context} {sh : IntShape} :
      InstrOk C (.vecAllTrue sh) ⟨[.val .v128], [.val .i32]⟩
  /-- `Instr_ok/vrelop` (`6-typing:328`), integer shapes, with the side condition
  of `vrelop_(Jnn X M)` (`1-syntax:357-361`): a 64-bit lane has only signed
  orderings. -/
  | vecIntRelOp {C : Context} {sh : IntShape} {op : IntRelOp}
      (hop : IntRelOp.validShape sh op = true) :
      InstrOk C (.vecIntRelOp sh op) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vrelop` (`6-typing:328`), floating-point shapes. -/
  | vecFloatRelOp {C : Context} {sh : FloatShape} {op : FloatRelOp} :
      InstrOk C (.vecFloatRelOp sh op) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vshiftop` (`6-typing:331`): the shift amount is an `I32`. -/
  | vecShiftOp {C : Context} {sh : IntShape} {op : VecShiftOp} :
      InstrOk C (.vecShiftOp sh op) ⟨[.val .v128, .val .i32], [.val .v128]⟩
  /-- `Instr_ok/vbitmask` (`6-typing:334`). -/
  | vecBitmask {C : Context} {sh : IntShape} :
      InstrOk C (.vecBitmask sh) ⟨[.val .v128], [.val .i32]⟩
  /-- `Instr_ok/vswizzle` (`6-typing:337`). The shape is fixed to `I8 X 16` by
  `1-syntax:455`, so `Instr.vecSwizzle` carries none. -/
  | vecSwizzle {C : Context} : InstrOk C .vecSwizzle ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vshuffle` (`6-typing:340`): every lane index satisfies
  `i < 2*$dim(sh)`. The shape is `I8 X 16` (`1-syntax:457`), so `$dim(sh) = 16`
  and the bound is `32`; the same production fixes the number of lanes at
  `16`. -/
  | vecShuffle {C : Context} {lanes : List LaneIdx}
      (hlen : lanes.length = 16) (hlanes : ∀ i ∈ lanes, i.val < 32) :
      InstrOk C (.vecShuffle lanes) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vsplat` (`6-typing:344`): the operand is `$shunpack(sh)`
  (`2-syntax-aux:44`), i.e. `Shape.unpacked`, which maps `I8` and `I16` lanes to
  `I32`. -/
  | vecSplat {C : Context} {sh : Shape} :
      InstrOk C (.vecSplat sh) ⟨[.val (.num sh.unpacked)], [.val .v128]⟩
  /-- `Instr_ok/vextract_lane` (`6-typing:348`): `i < $dim(sh)`. The signedness
  immediate is present exactly for packed lanes, by `1-syntax:460`. -/
  | vecExtractLane {C : Context} {sh : Shape} {sx : Option Signedness} {i : LaneIdx}
      (hsx : sx.isSome = decide (sh.laneWidth < 32)) (hi : i.val < sh.lanes) :
      InstrOk C (.vecExtractLane sh sx i) ⟨[.val .v128], [.val (.num sh.unpacked)]⟩
  /-- `Instr_ok/vreplace_lane` (`6-typing:352`): `i < $dim(sh)`. -/
  | vecReplaceLane {C : Context} {sh : Shape} {i : LaneIdx} (hi : i.val < sh.lanes) :
      InstrOk C (.vecReplaceLane sh i)
        ⟨[.val .v128, .val (.num sh.unpacked)], [.val .v128]⟩
  /-- `Instr_ok/vextunop` (`6-typing:356`), with the side conditions of
  `1-syntax:462-464` and `1-syntax:374`: the result lane doubles the operand lane
  and lies in `[16, 32]`. -/
  | vecExtUnOp {C : Context} {sh₁ sh₂ : IntShape} {op : VecExtUnOp}
      (hop : VecExtUnOp.valid2 sh₁ sh₂ op = true) :
      InstrOk C (.vecExtUnOp sh₁ sh₂ op) ⟨[.val .v128], [.val .v128]⟩
  /-- `Instr_ok/vextbinop` (`6-typing:359`), with the side conditions of
  `1-syntax:465-467` and `1-syntax:376-378`. -/
  | vecExtBinOp {C : Context} {sh₁ sh₂ : IntShape} {op : V2.VecExtBinOp}
      (hop : V2.VecExtBinOp.valid sh₁ sh₂ op = true) :
      InstrOk C (.vecExtBinOp sh₁ sh₂ op) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vnarrow` (`6-typing:362`), with the side condition of
  `1-syntax:468-469`,
  `$($lsize($lanetype(ishape_2)) = 2*$lsize($lanetype(ishape_1)) <= 32)`. That is
  a *chained* comparison: the operand lane is twice the result lane **and** is
  itself at most `32`, so the result lane is at most `16`. The two surviving
  combinations are `(I8 X 16) (I16 X 8)` and `(I16 X 8) (I32 X 4)`, which are
  exactly the two pairs of `A-binary:604-605` and `A-binary:630-631`, and it is
  exactly the `.vecNarrow` clause of `Silmaril.Wasm.V2.Instr.immediatesValid`. -/
  | vecNarrow {C : Context} {sh₁ sh₂ : IntShape} {sx : Signedness}
      (hwidth : sh₂.laneWidth = 2 * sh₁.laneWidth) (hmax : sh₂.laneWidth ≤ 32) :
      InstrOk C (.vecNarrow sh₁ sh₂ sx) ⟨[.val .v128, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vcvtop` (`6-typing:365`), plus the shape constraint of decided
  deviation 3: `1-syntax:472` says `;; TODO: missing constraints` and the typing
  rule is unconditional, so we require the combination to be one the reduction
  rules `Step_pure/vcvtop-*` define. See the module docstring. -/
  | vecCvtOp {C : Context} {sh₁ sh₂ : Shape} {op : VecCvtOp}
      (hop : VecCvtOp.valid sh₁ sh₂ op = true) :
      InstrOk C (.vecCvtOp sh₁ sh₂ op) ⟨[.val .v128], [.val .v128]⟩
  -- Local instructions (`6-typing:369-381`).
  /-- `Instr_ok/local.get` (`6-typing:371`). -/
  | localGet {C : Context} {x : LocalIdx} {t : ValType} (hx : C.locals[x.toNat]? = some t) :
      InstrOk C (.localGet x) ⟨[], [.val t]⟩
  /-- `Instr_ok/local.set` (`6-typing:375`). -/
  | localSet {C : Context} {x : LocalIdx} {t : ValType} (hx : C.locals[x.toNat]? = some t) :
      InstrOk C (.localSet x) ⟨[.val t], []⟩
  /-- `Instr_ok/local.tee` (`6-typing:379`). -/
  | localTee {C : Context} {x : LocalIdx} {t : ValType} (hx : C.locals[x.toNat]? = some t) :
      InstrOk C (.localTee x) ⟨[.val t], [.val t]⟩
  -- Global instructions (`6-typing:384-392`).
  /-- `Instr_ok/global.get` (`6-typing:386`): the premise is `C.GLOBALS[x] = mut t`
  with `mut = MUT?`, so either mutability is accepted. -/
  | globalGet {C : Context} {x : GlobalIdx} {gt : GlobalType}
      (hx : C.globals[x.toNat]? = some gt) :
      InstrOk C (.globalGet x) ⟨[], [.val gt.value]⟩
  /-- `Instr_ok/global.set` (`6-typing:390`): the premise is `C.GLOBALS[x] = MUT t`,
  so the global must be mutable. -/
  | globalSet {C : Context} {x : GlobalIdx} {gt : GlobalType}
      (hx : C.globals[x.toNat]? = some gt) (hmut : gt.mutability = .var) :
      InstrOk C (.globalSet x) ⟨[.val gt.value], []⟩
  -- Table instructions (`6-typing:395-429`).
  /-- `Instr_ok/table.get` (`6-typing:397`). -/
  | tableGet {C : Context} {x : TableIdx} {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
      InstrOk C (.tableGet x) ⟨[.val .i32], [.val (.ref tt.element)]⟩
  /-- `Instr_ok/table.set` (`6-typing:401`). -/
  | tableSet {C : Context} {x : TableIdx} {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
      InstrOk C (.tableSet x) ⟨[.val .i32, .val (.ref tt.element)], []⟩
  /-- `Instr_ok/table.size` (`6-typing:405`). -/
  | tableSize {C : Context} {x : TableIdx} {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
      InstrOk C (.tableSize x) ⟨[], [.val .i32]⟩
  /-- `Instr_ok/table.grow` (`6-typing:409`): the initialiser is below the
  delta. -/
  | tableGrow {C : Context} {x : TableIdx} {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
      InstrOk C (.tableGrow x) ⟨[.val (.ref tt.element), .val .i32], [.val .i32]⟩
  /-- `Instr_ok/table.fill` (`6-typing:413`). -/
  | tableFill {C : Context} {x : TableIdx} {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
      InstrOk C (.tableFill x) ⟨[.val .i32, .val (.ref tt.element), .val .i32], []⟩
  /-- `Instr_ok/table.copy` (`6-typing:417`): SpecTec names the element type `rt`
  once, so the two tables must agree on it. -/
  | tableCopy {C : Context} {x₁ x₂ : TableIdx} {tt₁ tt₂ : TableType}
      (hx₁ : C.tables[x₁.toNat]? = some tt₁) (hx₂ : C.tables[x₂.toNat]? = some tt₂)
      (hrt : tt₁.element = tt₂.element) :
      InstrOk C (.tableCopy x₁ x₂) ⟨[.val .i32, .val .i32, .val .i32], []⟩
  /-- `Instr_ok/table.init` (`6-typing:422`): the table's element type is the
  segment's. -/
  | tableInit {C : Context} {x₁ : TableIdx} {x₂ : ElemIdx} {tt : TableType} {rt : ElemType}
      (hx₁ : C.tables[x₁.toNat]? = some tt) (hx₂ : C.elems[x₂.toNat]? = some rt)
      (hrt : tt.element = rt) :
      InstrOk C (.tableInit x₁ x₂) ⟨[.val .i32, .val .i32, .val .i32], []⟩
  /-- `Instr_ok/elem.drop` (`6-typing:427`). -/
  | elemDrop {C : Context} {x : ElemIdx} {rt : ElemType} (hx : C.elems[x.toNat]? = some rt) :
      InstrOk C (.elemDrop x) ⟨[], []⟩
  -- Memory instructions (`6-typing:432-532`).
  /-- `Instr_ok/memory.size` (`6-typing:434`): 2.0 has no memory index, the
  premise is always `C.MEMS[0] = mt`. -/
  | memorySize {C : Context} {mt : MemoryType} (hm : C.mems[0]? = some mt) :
      InstrOk C .memorySize ⟨[], [.val .i32]⟩
  /-- `Instr_ok/memory.grow` (`6-typing:438`). -/
  | memoryGrow {C : Context} {mt : MemoryType} (hm : C.mems[0]? = some mt) :
      InstrOk C .memoryGrow ⟨[.val .i32], [.val .i32]⟩
  /-- `Instr_ok/memory.fill` (`6-typing:442`). -/
  | memoryFill {C : Context} {mt : MemoryType} (hm : C.mems[0]? = some mt) :
      InstrOk C .memoryFill ⟨[.val .i32, .val .i32, .val .i32], []⟩
  /-- `Instr_ok/memory.copy` (`6-typing:446`). -/
  | memoryCopy {C : Context} {mt : MemoryType} (hm : C.mems[0]? = some mt) :
      InstrOk C .memoryCopy ⟨[.val .i32, .val .i32, .val .i32], []⟩
  /-- `Instr_ok/memory.init` (`6-typing:450`): `C.DATAS[x] = OK`, and `datatype`
  carries no information (`1-syntax:176-177`). -/
  | memoryInit {C : Context} {x : DataIdx} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (hx : C.datas[x.toNat]? = some ()) :
      InstrOk C (.memoryInit x) ⟨[.val .i32, .val .i32, .val .i32], []⟩
  /-- `Instr_ok/data.drop` (`6-typing:455`). -/
  | dataDrop {C : Context} {x : DataIdx} (hx : C.datas[x.toNat]? = some ()) :
      InstrOk C (.dataDrop x) ⟨[], []⟩
  /-- `Instr_ok/load-val` (`6-typing:468`), integer case: alignment is bounded by
  `$size(nt)/8`. -/
  | intLoadVal {C : Context} {t : IntType} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg t.width) :
      InstrOk C (.intLoad t none arg) ⟨[.val .i32], [.val (.num (.int t))]⟩
  /-- `Instr_ok/load-val` (`6-typing:468`), floating-point case. `loadop_(Fnn)` is
  undeclared (`1-syntax:387-388` declares only `loadop_(Inn)`), so a float load
  never packs. -/
  | floatLoadVal {C : Context} {t : FloatType} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg t.width) :
      InstrOk C (.floatLoad t arg) ⟨[.val .i32], [.val (.num (.float t))]⟩
  /-- `Instr_ok/load-pack` (`6-typing:473`): alignment is bounded by `M/8`, the
  *packed* width, and `1-syntax:388` requires `sz < $sizenn(Inn)`. -/
  | intLoadPack {C : Context} {t : IntType} {sz : PackSize} {sx : Signedness}
      {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (hsz : sz.width < t.width) (ha : MemArgOk arg sz.width) :
      InstrOk C (.intLoad t (some (sz, sx)) arg) ⟨[.val .i32], [.val (.num (.int t))]⟩
  /-- `Instr_ok/store-val` (`6-typing:487`), integer case. -/
  | intStoreVal {C : Context} {t : IntType} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg t.width) :
      InstrOk C (.intStore t none arg) ⟨[.val .i32, .val (.num (.int t))], []⟩
  /-- `Instr_ok/store-val` (`6-typing:487`), floating-point case. -/
  | floatStoreVal {C : Context} {t : FloatType} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg t.width) :
      InstrOk C (.floatStore t arg) ⟨[.val .i32, .val (.num (.float t))], []⟩
  /-- `Instr_ok/store-pack` (`6-typing:492`), with the side condition of
  `1-syntax:509`. -/
  | intStorePack {C : Context} {t : IntType} {sz : PackSize} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (hsz : sz.width < t.width) (ha : MemArgOk arg sz.width) :
      InstrOk C (.intStore t (some sz) arg) ⟨[.val .i32, .val (.num (.int t))], []⟩
  /-- `Instr_ok/vload-val` (`6-typing:497`): `$size(V128)/8 = 16`. -/
  | vloadVal {C : Context} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg 128) :
      InstrOk C (.vecLoad none arg) ⟨[.val .i32], [.val .v128]⟩
  /-- `Instr_ok/vload-pack` (`6-typing:502`): `2^align <= M/8 * N`, with `M` the
  lane width and `N` the lane count of `SHAPE M X N _ sx`. SpecTec divides before
  multiplying; `MemArgOkPack` reproduces that. -/
  | vloadPack {C : Context} {op : VecLoadOp} {m n : Nat} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (hop : VecLoadOp.packShape op = some (m, n))
      (ha : MemArgOkPack arg m n) :
      InstrOk C (.vecLoad (some op) arg) ⟨[.val .i32], [.val .v128]⟩
  /-- `Instr_ok/vload-splat` (`6-typing:507`): `2^align <= n/8`. -/
  | vloadSplat {C : Context} {sz : PackSize} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg sz.width) :
      InstrOk C (.vecLoad (some (.splat sz)) arg) ⟨[.val .i32], [.val .v128]⟩
  /-- `Instr_ok/vload-zero` (`6-typing:512`): `2^align <= n/8` with `n` the width
  of `ZERO n`. -/
  | vloadZero {C : Context} {op : VecLoadOp} {n : Nat} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (hop : VecLoadOp.zeroWidth op = some n)
      (ha : MemArgOk arg n) :
      InstrOk C (.vecLoad (some op) arg) ⟨[.val .i32], [.val .v128]⟩
  /-- `Instr_ok/vload_lane` (`6-typing:517`): `2^align <= n/8` and
  `laneidx < 128/n`. -/
  | vloadLane {C : Context} {sz : PackSize} {arg : MemArg} {i : LaneIdx} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg sz.width) (hi : i.val < 128 / sz.width) :
      InstrOk C (.vecLoadLane sz arg i) ⟨[.val .i32, .val .v128], [.val .v128]⟩
  /-- `Instr_ok/vstore` (`6-typing:523`). -/
  | vstore {C : Context} {arg : MemArg} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg 128) :
      InstrOk C (.vecStore arg) ⟨[.val .i32, .val .v128], []⟩
  /-- `Instr_ok/vstore_lane` (`6-typing:528`). -/
  | vstoreLane {C : Context} {sz : PackSize} {arg : MemArg} {i : LaneIdx} {mt : MemoryType}
      (hm : C.mems[0]? = some mt) (ha : MemArgOk arg sz.width) (hi : i.val < 128 / sz.width) :
      InstrOk C (.vecStoreLane sz arg i) ⟨[.val .i32, .val .v128], []⟩

/-- `Instrs_ok: context |- instr* : functype` (`6-typing:143`), with exactly the
five rules of `6-typing:156-177`. The derived one-instruction-then-rest form is
the lemma `InstrsOk.cons`, not a constructor, because `seq` is kept. -/
inductive InstrsOk : Context → List Instr → InstrType → Prop where
  /-- `Instrs_ok/empty` (`6-typing:156`). -/
  | empty {C : Context} : InstrsOk C [] ⟨[], []⟩
  /-- `Instrs_ok/instr` (`6-typing:159`). -/
  | instr {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it) : InstrsOk C [i] it
  /-- `Instrs_ok/seq` (`6-typing:163`). -/
  | seq {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : CResultType}
      (h₁ : InstrsOk C is₁ ⟨t₁, t₂⟩) (h₂ : InstrsOk C is₂ ⟨t₂, t₃⟩) :
      InstrsOk C (is₁ ++ is₂) ⟨t₁, t₃⟩
  /-- `Instrs_ok/sub` (`6-typing:168`): the conclusion `t'_1* -> t'_2*` is the
  *weaker* type, with `t'_1* <: t_1*` and `t_2* <: t'_2*`. That orientation is
  `InstrType.Sub it it'`. -/
  | sub {C : Context} {is : List Instr} {it it' : InstrType}
      (h : InstrsOk C is it) (hs : InstrType.Sub it it') : InstrsOk C is it'
  /-- `Instrs_ok/frame` (`6-typing:175`): an untouched prefix of the stack. -/
  | frame {C : Context} {is : List Instr} {ts t₁ t₂ : CResultType}
      (h : InstrsOk C is ⟨t₁, t₂⟩) : InstrsOk C is ⟨ts ++ t₁, ts ++ t₂⟩

end

/-! ## Expressions -/

/-- `Expr_ok: context |- expr : resulttype` (`6-typing:144`), whose single rule
(`6-typing:149`) is `Instrs_ok: C |- instr* : eps -> t*`. -/
def ExprOk (C : Context) (e : Expr) (ts : CResultType) : Prop := InstrsOk C e ⟨[], ts⟩

/-! ## Structural lemmas

The derived forms the rest of the development uses. `singleton`, `append`,
`cons`, `mono` and `frame'` are immediate repackagings of the constructors;
`nil_iff` is a genuine inversion result. -/

namespace InstrsOk

/-- `Instrs_ok/instr` (`6-typing:159`) under its usual name. -/
theorem singleton {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it) :
    InstrsOk C [i] it := .instr h

/-- `Instrs_ok/seq` (`6-typing:163`) under its usual name. -/
theorem append {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : CResultType}
    (h₁ : InstrsOk C is₁ ⟨t₁, t₂⟩) (h₂ : InstrsOk C is₂ ⟨t₂, t₃⟩) :
    InstrsOk C (is₁ ++ is₂) ⟨t₁, t₃⟩ := .seq h₁ h₂

/-- `Instrs_ok/seq` with an `Instrs_ok/instr` left operand. This is the derived
`cons` form; it is a lemma rather than a constructor because `seq` is kept. -/
theorem cons {C : Context} {i : Instr} {is : List Instr} {t₁ t₂ t₃ : CResultType}
    (hi : InstrOk C i ⟨t₁, t₂⟩) (hs : InstrsOk C is ⟨t₂, t₃⟩) :
    InstrsOk C (i :: is) ⟨t₁, t₃⟩ := .seq (.instr hi) hs

/-- `Instrs_ok/sub` (`6-typing:168`): weakening along `InstrType.Sub`. -/
theorem mono {C : Context} {is : List Instr} {it it' : InstrType}
    (h : InstrsOk C is it) (hs : InstrType.Sub it it') : InstrsOk C is it' := .sub h hs

/-- `Instrs_ok/frame` (`6-typing:175`) stated on a packaged `InstrType`, so that
it applies without destructuring the type. -/
theorem frame' {C : Context} {is : List Instr} {ts : CResultType} {it : InstrType}
    (h : InstrsOk C is it) : InstrsOk C is ⟨ts ++ it.params, ts ++ it.results⟩ := by
  obtain ⟨t₁, t₂⟩ := it
  exact .frame h

/-- The empty instruction sequence has exactly the coercion types: `empty` gives
`eps -> eps`, `frame` makes it `t* -> t*`, and `sub` weakens that to any
`t_1* -> t_2*` with `t_1* <: t_2*`. Nothing else is derivable, because `instr`
needs a non-empty sequence and `seq` splits `eps` into two empty sequences. -/
theorem nil_iff {C : Context} {t₁ t₂ : CResultType} :
    InstrsOk C [] ⟨t₁, t₂⟩ ↔ CResultType.Sub t₁ t₂ := by
  constructor
  · intro h
    have aux : ∀ {C' : Context} {is : List Instr} {it : InstrType},
        InstrsOk C' is it → is = [] → CResultType.Sub it.params it.results := by
      intro C' is it h'
      induction h' using InstrsOk.rec (motive_1 := fun _ _ _ _ => True) with
      | empty => intro _; exact CResultType.sub_nil_nil
      | instr _ => intro hnil; exact absurd hnil (by simp)
      | seq _ _ ih₁ ih₂ =>
          intro hnil
          simp only [List.append_eq_nil_iff] at hnil
          exact CResultType.sub_trans (ih₁ hnil.1) (ih₂ hnil.2)
      | sub _ hs ih =>
          intro hnil
          exact CResultType.sub_trans hs.1 (CResultType.sub_trans (ih hnil) hs.2)
      | frame _ ih =>
          intro hnil
          exact CResultType.sub_append (CResultType.sub_refl _) (ih hnil)
      | _ => trivial
    exact aux h rfl
  · intro h
    have h₀ : InstrsOk C [] ⟨t₁ ++ [], t₁ ++ []⟩ := InstrsOk.frame InstrsOk.empty
    rw [List.append_nil] at h₀
    exact h₀.sub ⟨CResultType.sub_refl _, h⟩

end InstrsOk

/-! ## Agreement with the syntactic side conditions

The per-constructor premises above are exactly the clauses of
`Silmaril.Wasm.V2.Instr.immediatesValid`, which collects the `-- if` conditions of
the `syntax instr/…` productions (`1-syntax:406-522`). -/

/-- A well-typed instruction satisfies every syntactic side condition of its
production. -/
theorem InstrOk.immediatesValid {C : Context} {i : Instr} {it : InstrType}
    (h : InstrOk C i it) : i.immediatesValid = true := by
  induction h using InstrOk.rec
    (motive_2 := fun _ is _ _ => is.all Instr.immediatesValid = true) with
  | cvtOpConvert hne hdef =>
      simp only [Instr.immediatesValid, Bool.and_eq_true, bne_iff_ne, ne_eq, hdef, and_true]
      exact hne
  | cvtOpReinterpret hne hsize =>
      simp only [Instr.immediatesValid, Bool.and_eq_true, bne_iff_ne, ne_eq,
        CvtOp.toShared_reinterpret_isSome hne hsize, and_true]
      exact hne
  | _ => simp_all [Instr.immediatesValid]

/-- A well-typed instruction sequence consists of syntactically well-formed
instructions. -/
theorem InstrsOk.immediatesValid {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : is.all Instr.immediatesValid = true := by
  induction h using InstrsOk.rec
    (motive_1 := fun _ i _ _ => i.immediatesValid = true) with
  | cvtOpConvert hne hdef =>
      simp only [Instr.immediatesValid, Bool.and_eq_true, bne_iff_ne, ne_eq, hdef, and_true]
      exact hne
  | cvtOpReinterpret hne hsize =>
      simp only [Instr.immediatesValid, Bool.and_eq_true, bne_iff_ne, ne_eq,
        CvtOp.toShared_reinterpret_isSome hne hsize, and_true]
      exact hne
  | _ => simp_all [Instr.immediatesValid]

end Silmaril.Wasm.V2.Validation
