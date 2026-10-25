module

public import Silmaril.Wasm.V2.Execution.Basic
public import Silmaril.Wasm.V2.Execution.Numerics
public import Silmaril.Foundations.InfiniteTrace

/-!
# WebAssembly 2.0 reduction

Transcribed from the official SpecTec source
`specification/wasm-2.0/8-reduction.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (see `specs/wasm/core-2.0.json`).
Line references of the form `8-reduction:NN` point into that file.

`8-reduction:5-8` declares four relations; all four are transcribed here, one
constructor per `rule`, in SpecTec's order:

| SpecTec | Lean |
| --- | --- |
| `relation Step_pure: admininstr* ~> admininstr*` | `PureStep` |
| `relation Step_read: config ~> admininstr*` | `ReadStep` |
| `relation Step: config ~> config` | `Step` |
| `relation Steps: config ~>* config` | `Steps` |
| `relation Eval_expr` (`8-reduction:29`) | `EvalExpr` |

The layout follows `Silmaril.Wasm.Execution.Core.Step` and its `Core/Step/*`
family, which do the same job for Core 3.0, adapted down: 2.0 has no concrete-type subtyping,
no `Expand`, no GC, no exceptions, no handlers, no tail calls, no 64-bit or
multiple memories, no relaxed SIMD and no local-initialisation tracking, so the
reduction is considerably smaller and every operand is a plain `Val`.

## Where the state is read and where it is written

`ReadStep` takes the store and the frame as *parameters* — it never changes
them, exactly as `Step_read: config ~> admininstr*` says. `Step` lifts both
`PureStep` and `ReadStep` (`Step/pure`, `Step/read`, `8-reduction:10-16`) and
adds every rule that writes the state.

Rules that only *read* the state use the `Option`-valued accessors of
`Silmaril.Wasm.V2.Execution.Basic` (`State.table?`, `State.mem?`, …), so an
out-of-range module-instance index leaves the machine *stuck*, not trapped; that
is the policy fixed in `Basic.lean`'s module docstring. Rules that *write* the
state resolve the address first (`ModuleInst.tableAddr?` and friends) and then
use the address-indexed `Store.setXInst`; this is `$with_table`, `$with_global`,
`$with_mem`, … unfolded, and is written this way because `Step/table.grow-*` and
`Step/memory.grow-*` need the address for the `Numerics.Profile` grow policy
anyway. `$with_local` is the one *total* update (`8-reduction:380-381` guards
nothing, `List.set` is the identity out of range), so `Step/local.set` carries no
bound premise — again the decision recorded in `Basic.lean`.

## `-- otherwise`

SpecTec's `-- otherwise` means "none of the earlier rules of this rule group
applies". It is transcribed as an explicit negative premise, never as rule
order. The negations used, in full:

* `Step_read/call_indirect-trap` (`8-reduction:127`) negates the two premises of
  `call_indirect-call`: `¬ ∃ a fi, ti.refs[i] = some (REF.FUNC_ADDR a) ∧
  s.FUNCS[a] = some fi ∧ $type(z, y) = some fi.TYPE`. The table lookup
  `$table(z, x) = some ti` is a premise of *both* rules, so a module instance
  without that table is stuck rather than trapping.
* `Step_pure/ref.is_null-false` (`8-reduction:220`) negates `ref = REF.NULL rt`:
  `∀ t, r ≠ REF.NULL t`, i.e. `r` is a `REF.FUNC_ADDR` or a `REF.HOST_ADDR`.
* `Step_pure/vtestop-false` (`8-reduction:272`) negates `(ci_1 =/= 0)*` over
  `ci_1* = $lanes_(Jnn X N, c)`: `∃ l ∈ sh.lanesOf c, l = 0`.
* every `table.*` and `memory.*` rule named `-zero`, `-succ`, `-le` or `-gt`
  negates the preceding `-trap` rule's bound, which is a disjunction of `>`s,
  giving a conjunction of `≤`s; `-zero` then adds `n = 0` and the others add
  `n ≠ 0`; `-gt` further negates `-le`'s `j ≤ i`, giving `i < j`.

## Bulk operations

`table.fill`/`table.copy`/`table.init` and `memory.fill`/`memory.copy`/
`memory.init` reduce **one element (byte) at a time** by emitting further
instructions (`8-reduction:428-480, 608-660`), transcribed literally except
that the loop indices are `BitVec 32` sums (Deviation 5); there is no
atomic bulk operation here. The `-le`/`-gt` split of `copy` chooses the copy
direction. This matches Core 3.0 and differs from the `Lime1` machine, whose
bulk operations are atomic.

## Growing

`Step/memory.grow` and `Step/table.grow` each have a `-succeed` rule and an
unconditional `-fail` rule returning `$inv_signed_(32, -1)` (`8-reduction:420-425,
600-605`). Both are present. As in Core 3.0 the nondeterminism is parameterised
by `Numerics.Profile`'s `grow` policy: `-succeed` additionally requires
`P.growMaySucceed`, and `-fail` requires `P.growMayFail ∨ the growth is
impossible`. Under `Profile.spec` (policy `.nondet`) both side conditions are
`True`, so the pair of growth rules agrees with SpecTec's; an `.oracle` policy
selects growth outcomes. It does not make the entire reduction relation
deterministic: NaN choices and trap propagation are separate concerns. `$inv_signed_(32, -1)` is `BitVec.allOnes 32`.

## Deviations

**Deviation 1: `Step/ctxt-instrs` is missing from SpecTec 2.0.** `8-reduction`
has only `Step/ctxt-label` (`:163`) and `Step/ctxt-frame` (`:167`). Both
`specification/wasm-1.0/8-reduction.spectec:165-168` and
`specification/wasm-3.0/4.3-execution.instructions.spectec:32-35` additionally
have

    rule Step/ctxt-instrs:
      z; val* instr* instr_1*  ~>  z'; val* instr'* instr_1*
      -- Step: z; instr* ~> z'; instr'*
      -- if val* =/= eps \/ instr_1* =/= eps

Without it no instruction sequence of length greater than one can reduce at all:
`Step_pure/nop` (`8-reduction:45`) rewrites the sequence `NOP`, not a `NOP`
inside a sequence, so already `NOP NOP` is stuck, and `Eval_expr` is empty on
every non-trivial expression. The reference interpreter of course evaluates
instruction sequences left to right
(`interpreter/exec/eval.ml`, `step`/`instr` over the value and instruction
stacks), and the whole test suite depends on it. We include the rule, verbatim
from wasm-1.0, as `Step.ctxtInstrs`.

**Deviation 2: `Step/ctxt-frame` freezes the inner frame.** `8-reduction:167`
reads

    rule Step/ctxt-frame:
      s; f; (FRAME_ n `{f'} instr*)  ~>  s'; f; (FRAME_ n `{f'} instr'*)
      -- Step: s; f'; instr* ~> s'; f'; instr'*

with the *same* `f'` in the premise's source and target. `Step/local.set`
(`8-reduction:380`) changes the frame, so under the literal reading
`local.set` — and hence every function that writes a local — is stuck inside
`FRAME_`. wasm-1.0 `8-reduction:161-163` and wasm-3.0
`4.3-execution.instructions.spectec:45-47` both use a fresh `f''`:

    s; f; (FRAME_ n `{f'} instr*)  ~>  s'; f; (FRAME_ n `{f''} instr'*)
    -- Step: s; f'; instr* ~> s'; f''; instr'*

as does the W3C 2.0 prose (`S; F; frame_n{F'} instr* end ↪ S'; F; frame_n{F''}
instr'* end`). We follow wasm-1.0/3.0 and the interpreter: `Step.ctxtFrame`
lets the inner frame change, restores the outer frame `f`, and propagates the
new store. (The outer configuration therefore changes only in its store, which
is what `8-reduction:168` says about `f`.)

**Deviation 3: host functions.** SpecTec 2.0 has no host functions at all; the
runtime of `Basic.lean` adds `FuncCode.host`, as described in
`docs/projects/wasm-semantics.md`. `Step.callAddrHost` and `Step.callAddrHostDiv` mirror Core
3.0's `Step/call_ref-hostfunc-res` and `-hostfunc-div`: a host call consumes the
same `val^k` as `Step_read/call_addr`, may return any `(store, result)` the
`HostSemantics` admits, and may diverge, in which case the configuration steps
to itself (so that `Diverges` sees an infinite trace). With `H = Empty` these
two constructors are vacuous; the other deviations listed here still apply.

**Deviation 4: `PureStep` is indexed by a `Numerics.Profile`.** `Step_pure`
contains `unop`/`binop`/`cvtop` on floats and the float-shaped vector operators,
whose SpecTec result *sets* are NaN-nondeterministic (`3-numerics:215-230`); the
repo packages that choice as `Numerics.Profile`. `ReadStep` needs no profile.

**Deviation 5: the bulk loops' index arithmetic wraps.** The `-succ`, `-le` and
`-gt` rules of `table.fill`/`table.copy`/`table.init` and `memory.fill`/
`memory.copy`/`memory.init` (`8-reduction:437,453,460,476,617,633,640,656`)
continue at `CONST I32 $(i+1)`, `$(j+1)`, `$(i+n-1)`, `$(j+n-1)` and `$(n-1)`.
SpecTec computes these in `nat`, and `CONST I32` takes a `num_(I32) = iN(32) =
uN(32)`, i.e. `0 | ... | 2^32-1` (`1-syntax:18-23,260,432`). Where a result is
`2^32` or more the right-hand side is not a term, so the rule has no instance
there. Here they are computed in `BitVec 32` (`constI32 (j + 1)` etc.), which
wraps. `$(n-1)` never wraps (`n ≠ 0`), and `$(i+n-1)`/`$(j+n-1)` only beyond a
table or memory of `2^32` entries. `$(i+1)`/`$(j+1)` do wrap on a valid store. A
memory of `2^16` pages (`Memtype_ok`, `6-typing:42`, allows it) holds exactly
`2^32` bytes. A `memory.fill` or `memory.init` whose destination range ends at
`2^32`, or a forward (`-le`) `memory.copy` whose source range does, reaches its
last byte at index `2^32-1` with `n = 1`. No SpecTec rule applies there (`-trap`
needs a range past `2^32`, `-zero` needs `n = 0`, and `-succ`/`-le` have no
instance), so SpecTec is stuck; here the last byte is written, the index wraps
to `0`, and the loop ends through `-zero`. Tables have at most `2^32-1` entries
(`Tabletype_ok`, `6-typing:38`), so on a valid store the table loops do not
wrap.

Three rules of `8-reduction` are wholly vacuous but transcribed anyway, with
their exact premises, because they are rules:

* `Step_pure/unop-trap` (`8-reduction:178`), for both integers (`$unop_(Inn, ..)`
  is always a singleton) and floats (`FloatUnOpResult_nonempty`);
* `Step_pure/vunop-trap` (`8-reduction:252`), for integer shapes
  (`VecIntUnOpResult_nonempty`) *and* float shapes
  (`VecFloatUnOpResult_nonempty`);
* `Step_pure/vbinop-trap` (`8-reduction:261`), again for both shapes
  (`VecIntBinOpResult_nonempty`, `VecFloatBinOpResult_nonempty`).

`Step_pure/binop-trap` (`8-reduction:187`) is vacuous on its float half too
(`FloatBinOpResult_nonempty`); only the integer half, where `$idiv_`/`$irem_`
by zero give `eps`, has instances. None of this is an infidelity: SpecTec's
`$vunop_`/`$vbinop_` on `Jnn X M` (`3-numerics:386-431`) return a single
`v128`, and on `Fnn X M` (`3-numerics:464-532`) a `$setproduct_` of per-lane
float result sets, each of which is nonempty, so neither result set can be
`eps`.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (V128 Profile)
open Silmaril.Wasm.Execution.Memory (Bytes readBytes pageSize)

variable {H : Type}

/-! ## Notation and auxiliary functions -/

/-- `(CONST I32 c)`. -/
abbrev constI32 (c : BitVec 32) : Admin := .plain (.intConst .i32 c)

/-- `(VCONST V128 c)`. -/
abbrev vconst (c : V128) : Admin := .plain (.vecConst c)

/-- `ref` as an administrative instruction. -/
abbrev aref (r : Ref) : Admin := (Val.ref r).toAdmin

/-- `$memarg0 = {ALIGN 0, OFFSET 0}` (`2-syntax-aux:106`). -/
def memarg0 : MemArg := ⟨⟨0, Nat.two_pow_pos 32⟩, ⟨0, Nat.two_pow_pos 32⟩⟩

/-- `(STORE I32 8 $memarg0)`, emitted by the `memory.fill`/`copy`/`init` loops. -/
def store8 : Admin := .plain (.intStore .i32 (some .i8) memarg0)

/-- `(LOAD I32 (8 _ U) $memarg0)`, emitted by the `memory.copy` loop. -/
def load8u : Admin := .plain (.intLoad .i32 (some (.i8, .unsigned)) memarg0)

/-- The effective address `i + ao.OFFSET`, computed in `Nat` so that it never
wraps; every bound of `8-reduction:489-593` is `i + ao.OFFSET + W/8 > |bytes|`. -/
def effAddr (i : Nat) (arg : MemArg) : Nat := i + arg.offset.val

/-- `l - 1` for the label index of `Step_pure/br-succ` (`8-reduction:95`, where
the matched index is written `$(l+1)`). -/
def labelPred (l : LabelIdx) : LabelIdx :=
  ⟨⟨l.toNat - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) l.value.isLt⟩⟩

/-- `$blocktype(z, bt)` (`8-reduction:63-66`). `_IDX x` is resolved against the
frame's module types, so the function lives on `ModuleInst`. -/
def ModuleInst.blockType? (m : ModuleInst) : BlockType → Option FuncType
  | .result none => some ⟨[], []⟩
  | .result (some t) => some ⟨[], [t]⟩
  | .typeIdx x => m.type? x

/-- The widening half of `Step_read/vload-shape-val` (`8-reduction:518`): the
`N` chunks of `K` bits read from memory, each `$extend__(K, 2*K, sx, ·)`, laid
out as `2*K`-bit lanes. -/
def extendLanes (K N : Nat) (sx : Signedness) {n : Nat} (c : BitVec n) : V128 :=
  Numerics.invLanes (2 * K) ((List.range N).map fun k =>
    let l := c.extractLsb' (k * K) K
    match sx with
    | .signed => l.signExtend (2 * K)
    | .unsigned => l.setWidth (2 * K))

/-- The vector produced by a vector load from the `$ibytes_`-decoded bits, for
all four shapes at once: `Step_read/vload-val` (`8-reduction:509`, `op = eps`),
`vload-shape-val` (`:518`), `vload-splat-val` (`:529`) and `vload-zero-val`
(`:541`). -/
def vecLoadResult : (op : Option VecLoadOp) → BitVec (VecLoadOp.accessWidth op) → V128
  | none, c => c.setWidth 128
  | some (.shape8x8 sx), c => extendLanes 8 8 sx c
  | some (.shape16x4 sx), c => extendLanes 16 4 sx c
  | some (.shape32x2 sx), c => extendLanes 32 2 sx c
  | some (.splat sz), c =>
      Numerics.invLanes sz.width (List.replicate (128 / sz.width) (c.setWidth sz.width))
  | some .zero32, c => c.setWidth 128
  | some .zero64, c => c.setWidth 128

/-! ## `Step_pure` (`8-reduction:6`)

The rules that look at neither the store nor the frame. -/

inductive PureStep (P : Profile) : List Admin → List Admin → Prop where
  -- Polymorphic instructions (`8-reduction:40-58`)
  /-- `Step_pure/unreachable` (`8-reduction:42`). -/
  | unreachable : PureStep P [.plain .unreachable] [.trap]
  /-- `Step_pure/nop` (`8-reduction:45`). -/
  | nop : PureStep P [.plain .nop] []
  /-- `Step_pure/drop` (`8-reduction:48`). -/
  | drop (v : Val) : PureStep P [v.toAdmin, .plain .drop] []
  /-- `Step_pure/select-true` (`8-reduction:52`). -/
  | selectTrue {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List ValType)} (hc : c ≠ 0) :
      PureStep P [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] [v₁.toAdmin]
  /-- `Step_pure/select-false` (`8-reduction:56`). -/
  | selectFalse (v₁ v₂ : Val) (ts : Option (List ValType)) :
      PureStep P [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)] [v₂.toAdmin]
  -- Block instructions (`8-reduction:61-86`)
  /-- `Step_pure/if-true` (`8-reduction:76`). -/
  | ifTrue {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr} (hc : c ≠ 0) :
      PureStep P [constI32 c, .plain (.if_ bt b₁ b₂)] [.plain (.block bt b₁)]
  /-- `Step_pure/if-false` (`8-reduction:80`). -/
  | ifFalse {bt : BlockType} {b₁ b₂ : List Instr} :
      PureStep P [constI32 0, .plain (.if_ bt b₁ b₂)] [.plain (.block bt b₂)]
  /-- `Step_pure/label-vals` (`8-reduction:85`). -/
  | labelVals {n : Nat} {cont : List Instr} {vs : List Val} :
      PureStep P [.label n cont (vals vs)] (vals vs)
  -- Branch instructions (`8-reduction:89-114`)
  /-- `Step_pure/br-zero` (`8-reduction:92`): the `val'*` prefix below the `val^n`
  is **discarded**, the `val^n` kept, and the label's continuation `instr'*` run. -/
  | brZero {n : Nat} {cont : List Instr} {vs' vs : List Val} {l : LabelIdx}
      {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = n) :
      PureStep P [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]
        (vals vs ++ expression cont)
  /-- `Step_pure/br-succ` (`8-reduction:95`): the whole `val*` prefix is kept and
  the branch bubbles out with its index decremented. -/
  | brSucc {n : Nat} {cont : List Instr} {vs : List Val} {l : LabelIdx}
      {rest : List Admin} (hl : 0 < l.toNat) :
      PureStep P [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]
        (vals vs ++ [.plain (.br (labelPred l))])
  /-- `Step_pure/br_if-true` (`8-reduction:99`). -/
  | brIfTrue {c : BitVec 32} {l : LabelIdx} (hc : c ≠ 0) :
      PureStep P [constI32 c, .plain (.brIf l)] [.plain (.br l)]
  /-- `Step_pure/br_if-false` (`8-reduction:103`). -/
  | brIfFalse {l : LabelIdx} : PureStep P [constI32 0, .plain (.brIf l)] []
  /-- `Step_pure/br_table-lt` (`8-reduction:108`). -/
  | brTableLt {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
      (hi : ls[i.toNat]? = some l) :
      PureStep P [constI32 i, .plain (.brTable ls l')] [.plain (.br l)]
  /-- `Step_pure/br_table-ge` (`8-reduction:112`). -/
  | brTableGe {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
      (hi : ls.length ≤ i.toNat) :
      PureStep P [constI32 i, .plain (.brTable ls l')] [.plain (.br l')]
  -- Function instructions (`8-reduction:117-145`)
  /-- `Step_pure/frame-vals` (`8-reduction:138`). -/
  | frameVals {n : Nat} {fr : Frame} {vs : List Val} (hn : vs.length = n) :
      PureStep P [.frame n fr (vals vs)] (vals vs)
  /-- `Step_pure/return-frame` (`8-reduction:141`). -/
  | returnFrame {n : Nat} {fr : Frame} {vs' vs : List Val} {rest : List Admin}
      (hn : vs.length = n) :
      PureStep P [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] (vals vs)
  /-- `Step_pure/return-label` (`8-reduction:144`). -/
  | returnLabel {n : Nat} {cont : List Instr} {vs : List Val} {rest : List Admin} :
      PureStep P [.label n cont (vals vs ++ [.plain .return_] ++ rest)]
        (vals vs ++ [.plain .return_])
  -- Traps (`8-reduction:148-158`)
  /-- `Step_pure/trap-vals` (`8-reduction:150`). The side condition
  `val* =/= eps \/ instr* =/= eps` (`8-reduction:152`) is essential: without it
  `TRAP ~> TRAP` and the rule loops. -/
  | trapVals {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ []) :
      PureStep P (vals vs ++ [.trap] ++ rest) [.trap]
  /-- `Step_pure/trap-label` (`8-reduction:154`). -/
  | trapLabel {n : Nat} {cont : List Instr} : PureStep P [.label n cont [.trap]] [.trap]
  /-- `Step_pure/trap-frame` (`8-reduction:157`). -/
  | trapFrame {n : Nat} {fr : Frame} : PureStep P [.frame n fr [.trap]] [.trap]
  -- Numeric instructions (`8-reduction:172-207`)
  /-- `Step_pure/unop-val` (`8-reduction:174`), integer operators. -/
  | intUnOp {t : IntType} {op : IntUnOp} {x z : BitVec t.width} (h : IntUnOpResult t op x z) :
      PureStep P [.plain (.intConst t x), .plain (.intUnOp t op)] [.plain (.intConst t z)]
  /-- `Step_pure/unop-val` (`8-reduction:174`), floating-point operators. -/
  | floatUnOp {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
      (h : FloatUnOpResult P t op x z) :
      PureStep P [.plain (.floatConst t x), .plain (.floatUnOp t op)] [.plain (.floatConst t z)]
  /-- `Step_pure/unop-trap` (`8-reduction:178`), integer operators. Vacuous:
  `$unop_(Inn, ..)` is a singleton for every argument. -/
  | intUnOpTrap {t : IntType} {op : IntUnOp} {x : BitVec t.width}
      (h : ∀ z, ¬ IntUnOpResult t op x z) :
      PureStep P [.plain (.intConst t x), .plain (.intUnOp t op)] [.trap]
  /-- `Step_pure/unop-trap` (`8-reduction:178`), floating-point operators.
  Vacuous: the result set is never empty (`FloatUnOpResult_nonempty`). -/
  | floatUnOpTrap {t : FloatType} {op : FloatUnOp} {x : BitVec t.width}
      (h : ∀ z, ¬ FloatUnOpResult P t op x z) :
      PureStep P [.plain (.floatConst t x), .plain (.floatUnOp t op)] [.trap]
  /-- `Step_pure/binop-val` (`8-reduction:183`), integer operators. -/
  | intBinOp {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
      (h : IntBinOpResult t op x y z) :
      PureStep P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)]
        [.plain (.intConst t z)]
  /-- `Step_pure/binop-val` (`8-reduction:183`), floating-point operators. -/
  | floatBinOp {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
      (h : FloatBinOpResult P t op x y z) :
      PureStep P [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatBinOp t op)]
        [.plain (.floatConst t z)]
  /-- `Step_pure/binop-trap` (`8-reduction:187`), integer operators: division by
  zero and signed division overflow. -/
  | intBinOpTrap {t : IntType} {op : IntBinOp} {x y : BitVec t.width}
      (h : IntBinOpTraps t op x y) :
      PureStep P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)] [.trap]
  /-- `Step_pure/binop-trap` (`8-reduction:187`), floating-point operators.
  Vacuous (`FloatBinOpResult_nonempty`). -/
  | floatBinOpTrap {t : FloatType} {op : FloatBinOp} {x y : BitVec t.width}
      (h : ∀ z, ¬ FloatBinOpResult P t op x y z) :
      PureStep P [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatBinOp t op)]
        [.trap]
  /-- `Step_pure/testop` (`8-reduction:192`). -/
  | testOp {t : IntType} {op : IntTestOp} {x : BitVec t.width} :
      PureStep P [.plain (.intConst t x), .plain (.intTestOp t op)] [constI32 (testOp t op x)]
  /-- `Step_pure/relop` (`8-reduction:196`), integer operators. -/
  | intRelOp {t : IntType} {op : IntRelOp} {x y : BitVec t.width} :
      PureStep P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intRelOp t op)]
        [constI32 (intRelOp t op x y)]
  /-- `Step_pure/relop` (`8-reduction:196`), floating-point operators. -/
  | floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} :
      PureStep P [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatRelOp t op)]
        [constI32 (floatRelOp t op x y)]
  /-- `Step_pure/cvtop-val` (`8-reduction:201`). The instruction is
  `CVTOP nt_2 nt_1 cvtop` with `nt_2` the target and `nt_1` the source. -/
  | cvtOp {target source : NumType} {op : CvtOp} {x : BitVec source.width}
      {z : BitVec target.width} (h : CvtOpResult P target source op x z) :
      PureStep P [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)]
        [(Val.num ⟨target, z⟩).toAdmin]
  /-- `Step_pure/cvtop-trap` (`8-reduction:205`). -/
  | cvtOpTrap {target source : NumType} {op : CvtOp} {x : BitVec source.width}
      (h : CvtOpTraps P target source op x) :
      PureStep P [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)] [.trap]
  -- Reference instructions (`8-reduction:210-222`)
  /-- `Step_pure/ref.is_null-true` (`8-reduction:216`). -/
  | refIsNullTrue {t : RefType} :
      PureStep P [aref (.null t), .plain .refIsNull] [constI32 1]
  /-- `Step_pure/ref.is_null-false` (`8-reduction:220`). `-- otherwise` negates
  `ref = REF.NULL rt`. -/
  | refIsNullFalse {r : Ref} (h : ∀ t, r ≠ .null t) :
      PureStep P [aref r, .plain .refIsNull] [constI32 0]
  -- Vector instructions (`8-reduction:225-372`)
  /-- `Step_pure/vvunop` (`8-reduction:227`). -/
  | vvUnOp (op : VecUnOp) (c : V128) :
      PureStep P [vconst c, .plain (.vvUnOp op)] [vconst (VVUnOp op c)]
  /-- `Step_pure/vvbinop` (`8-reduction:232`). -/
  | vvBinOp (op : VecBinOp) (c₁ c₂ : V128) :
      PureStep P [vconst c₁, vconst c₂, .plain (.vvBinOp op)] [vconst (VVBinOp op c₁ c₂)]
  /-- `Step_pure/vvternop` (`8-reduction:237`). -/
  | vvTernOp (op : VecTernOp) (c₁ c₂ c₃ : V128) :
      PureStep P [vconst c₁, vconst c₂, vconst c₃, .plain (.vvTernOp op)]
        [vconst (VVTernOp op c₁ c₂ c₃)]
  /-- `Step_pure/vvtestop` (`8-reduction:243`): `ANY_TRUE` is `$ine_(128, c, 0)`. -/
  | vvTestOp (op : VecTestOp) (c : V128) :
      PureStep P [vconst c, .plain (.vvTestOp op)] [constI32 (VVTestOp op c)]
  /-- `Step_pure/vunop` (`8-reduction:248`), integer shapes. -/
  | vecIntUnOp {sh : IntShape} {op : VecIntUnOp} {c r : V128} (h : VecIntUnOpResult sh op c r) :
      PureStep P [vconst c, .plain (.vecIntUnOp sh op)] [vconst r]
  /-- `Step_pure/vunop` (`8-reduction:248`), floating-point shapes. -/
  | vecFloatUnOp {sh : FloatShape} {op : FloatUnOp} {c r : V128}
      (h : VecFloatUnOpResult P sh op c r) :
      PureStep P [vconst c, .plain (.vecFloatUnOp sh op)] [vconst r]
  /-- `Step_pure/vunop-trap` (`8-reduction:252`), integer shapes. Vacuous:
  `$vunop_(Jnn X M, ..)` is a singleton (`VecIntUnOpResult_nonempty`). -/
  | vecIntUnOpTrap {sh : IntShape} {op : VecIntUnOp} {c : V128}
      (h : ∀ r, ¬ VecIntUnOpResult sh op c r) :
      PureStep P [vconst c, .plain (.vecIntUnOp sh op)] [.trap]
  /-- `Step_pure/vunop-trap` (`8-reduction:252`), floating-point shapes.
  Vacuous: the per-lane float result sets are nonempty, so the `$setproduct_`
  is too (`VecFloatUnOpResult_nonempty`). -/
  | vecFloatUnOpTrap {sh : FloatShape} {op : FloatUnOp} {c : V128}
      (h : ∀ r, ¬ VecFloatUnOpResult P sh op c r) :
      PureStep P [vconst c, .plain (.vecFloatUnOp sh op)] [.trap]
  /-- `Step_pure/vbinop-val` (`8-reduction:257`), integer shapes. -/
  | vecIntBinOp {sh : IntShape} {op : V2.VecIntBinOp} {c₁ c₂ r : V128}
      (h : VecIntBinOpResult P sh op c₁ c₂ r) :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp sh op)] [vconst r]
  /-- `Step_pure/vbinop-val` (`8-reduction:257`), floating-point shapes. -/
  | vecFloatBinOp {sh : FloatShape} {op : V2.VecFloatBinOp} {c₁ c₂ r : V128}
      (h : VecFloatBinOpResult P sh op c₁ c₂ r) :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp sh op)] [vconst r]
  /-- `Step_pure/vbinop-trap` (`8-reduction:261`), integer shapes. Vacuous:
  `$vbinop_(Jnn X M, ..)` is a singleton (`VecIntBinOpResult_nonempty`). -/
  | vecIntBinOpTrap {sh : IntShape} {op : V2.VecIntBinOp} {c₁ c₂ : V128}
      (h : ∀ r, ¬ VecIntBinOpResult P sh op c₁ c₂ r) :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp sh op)] [.trap]
  /-- `Step_pure/vbinop-trap` (`8-reduction:261`), floating-point shapes.
  Vacuous: the per-lane float result sets are nonempty, so the `$setproduct_`
  is too (`VecFloatBinOpResult_nonempty`). -/
  | vecFloatBinOpTrap {sh : FloatShape} {op : V2.VecFloatBinOp} {c₁ c₂ : V128}
      (h : ∀ r, ¬ VecFloatBinOpResult P sh op c₁ c₂ r) :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp sh op)] [.trap]
  /-- `Step_pure/vtestop-true` (`8-reduction:267`): every lane is non-zero. -/
  | vecAllTrueTrue {sh : IntShape} {c : V128} (h : ∀ l ∈ sh.lanesOf c, l ≠ 0) :
      PureStep P [vconst c, .plain (.vecAllTrue sh)] [constI32 1]
  /-- `Step_pure/vtestop-false` (`8-reduction:272`). `-- otherwise` negates
  `(ci_1 =/= 0)*` over `ci_1* = $lanes_(Jnn X N, c)`: some lane is zero. -/
  | vecAllTrueFalse {sh : IntShape} {c : V128} (h : ∃ l ∈ sh.lanesOf c, l = 0) :
      PureStep P [vconst c, .plain (.vecAllTrue sh)] [constI32 0]
  /-- `Step_pure/vrelop` (`8-reduction:277`), integer shapes. -/
  | vecIntRelOp {sh : IntShape} {op : IntRelOp} {c₁ c₂ : V128} :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecIntRelOp sh op)]
        [vconst (VecIntRelOp sh op c₁ c₂)]
  /-- `Step_pure/vrelop` (`8-reduction:277`), floating-point shapes. -/
  | vecFloatRelOp {sh : FloatShape} {op : FloatRelOp} {c₁ c₂ : V128} :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatRelOp sh op)]
        [vconst (VecFloatRelOp sh op c₁ c₂)]
  /-- `Step_pure/vshiftop` (`8-reduction:287`). -/
  | vecShiftOp {sh : IntShape} {op : Wasm.VecShiftOp} {c : V128} {n : BitVec 32} :
      PureStep P [vconst c, constI32 n, .plain (.vecShiftOp sh op)]
        [vconst (VecShiftOp sh op c n)]
  /-- `Step_pure/vbitmask` (`8-reduction:293`). -/
  | vecBitmask {sh : IntShape} {c : V128} :
      PureStep P [vconst c, .plain (.vecBitmask sh)] [constI32 (VecBitmask sh c)]
  /-- `Step_pure/vswizzle` (`8-reduction:299`): `c_1` is the table, `c_2` the
  index vector; SpecTec pads the table with `0^(256-M)`, so an out-of-range
  index selects `0`. -/
  | vecSwizzle {c₁ c₂ : V128} :
      PureStep P [vconst c₁, vconst c₂, .plain .vecSwizzle] [vconst (VecSwizzle c₁ c₂)]
  /-- `Step_pure/vshuffle` (`8-reduction:307`). `c'*[$(i*[k])]` indexes the
  32-lane concatenation partially, so an index `≥ 32` is *stuck*; the bound is a
  typing premise (`Instr_ok/vshuffle`, `6-typing:340-342`). -/
  | vecShuffle {idx : List LaneIdx} {c₁ c₂ : V128} (hidx : ∀ j ∈ idx, j.val < 32) :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecShuffle idx)]
        [vconst (VecShuffle idx c₁ c₂)]
  /-- `Step_pure/vsplat` (`8-reduction:314`). -/
  | vecSplat {sh : Shape} {x : BitVec sh.unpacked.width} :
      PureStep P [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)]
        [vconst (VecSplat sh x)]
  /-- `Step_pure/vextract_lane-num` (`8-reduction:319`) and `-pack` (`:324`):
  one constructor, the sign `sx?` deciding. `$lanes_(sh, c)[i]` is partial, so an
  out-of-range lane index is stuck. -/
  | vecExtractLane {sh : Shape} {sx : Option Signedness} {i : LaneIdx} {c : V128}
      (hi : i.val < sh.lanes) :
      PureStep P [vconst c, .plain (.vecExtractLane sh sx i)]
        [(Val.num ⟨sh.unpacked, VecExtractLane sh sx i.val c⟩).toAdmin]
  /-- `Step_pure/vreplace_lane` (`8-reduction:329`). The update
  `$lanes_(sh, c)[[i] = ..]` is partial, so an out-of-range lane is stuck. -/
  | vecReplaceLane {sh : Shape} {i : LaneIdx} {c : V128} {x : BitVec sh.unpacked.width}
      (hi : i.val < sh.lanes) :
      PureStep P [vconst c, (Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecReplaceLane sh i)]
        [vconst (VecReplaceLane sh i.val c x)]
  /-- `Step_pure/vextunop` (`8-reduction:334`). -/
  | vecExtUnOp {target source : IntShape} {op : VecExtUnOp} {c r : V128}
      (h : VecExtUnOpResult target source op c r) :
      PureStep P [vconst c, .plain (.vecExtUnOp target source op)] [vconst r]
  /-- `Step_pure/vextbinop` (`8-reduction:339`). -/
  | vecExtBinOp {target source : IntShape} {op : V2.VecExtBinOp} {c₁ c₂ r : V128}
      (h : VecExtBinOpResult P target source op c₁ c₂ r) :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecExtBinOp target source op)] [vconst r]
  /-- `Step_pure/vnarrow` (`8-reduction:344`). -/
  | vecNarrow {target source : IntShape} {sx : Signedness} {c₁ c₂ : V128} :
      PureStep P [vconst c₁, vconst c₂, .plain (.vecNarrow target source sx)]
        [vconst (VecNarrow target source sx c₁ c₂)]
  /-- `Step_pure/vcvtop-full` (`8-reduction:353`), `-half` (`:360`) and `-zero`
  (`:367`) at once: the `$halfop` slicing and the `$zeroop` padding are built
  into `VecCvtOpResult`'s shape-indexed cases (see `Numerics.lean`). -/
  | vecCvtOp {target source : Shape} {op : VecCvtOp} {c r : V128}
      (h : VecCvtOpResult P target source op c r) :
      PureStep P [vconst c, .plain (.vecCvtOp target source op)] [vconst r]
  -- Local instructions (`8-reduction:375-384`)
  /-- `Step_pure/local.tee` (`8-reduction:383`). -/
  | localTee {x : LocalIdx} {v : Val} :
      PureStep P [v.toAdmin, .plain (.localTee x)] [v.toAdmin, v.toAdmin, .plain (.localSet x)]

/-! ## `Step_read` (`8-reduction:7`)

`z; instr* ~> instr'*`: the rules that read the state but do not change it. The
store and the frame are parameters. -/

inductive ReadStep : Store H → Frame → List Admin → List Admin → Prop where
  -- Block instructions (`8-reduction:61-74`)
  /-- `Step_read/block` (`8-reduction:68`): the label arity is `n`, the number of
  **results** of `$blocktype(z, bt) = t_1^k -> t_2^n`, the continuation is empty,
  and the `val^k` operands move *inside* the label. -/
  | block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {ft : FuncType} (hbt : f.module.blockType? bt = some ft)
      (hk : vs.length = ft.params.length) :
      ReadStep s f (vals vs ++ [.plain (.block bt body)])
        [.label ft.results.length [] (vals vs ++ expression body)]
  /-- `Step_read/loop` (`8-reduction:72`): the label arity is `k`, the number of
  **parameters**, and the continuation is the `LOOP` itself. -/
  | loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {ft : FuncType} (hbt : f.module.blockType? bt = some ft)
      (hk : vs.length = ft.params.length) :
      ReadStep s f (vals vs ++ [.plain (.loop bt body)])
        [.label ft.params.length [.loop bt body] (vals vs ++ expression body)]
  -- Function instructions (`8-reduction:117-135`)
  /-- `Step_read/call` (`8-reduction:119`). -/
  | call {s : Store H} {f : Frame} {x : FuncIdx} {a : FuncAddr}
      (hx : f.module.funcAddr? x = some a) :
      ReadStep s f [.plain (.call x)] [.callAddr a]
  /-- `Step_read/call_indirect-call` (`8-reduction:122`). -/
  | callIndirectCall {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {i : BitVec 32}
      {ti : TableInst} {a : FuncAddr} {fi : FuncInst H}
      (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (hr : ti.refs[i.toNat]? = some (.funcAddr a))
      (hf : s.funcInst? a = some fi)
      (hy : (⟨s, f⟩ : State H).type? y = some fi.type) :
      ReadStep s f [constI32 i, .plain (.callIndirect x y)] [.callAddr a]
  /-- `Step_read/call_indirect-trap` (`8-reduction:127`). `-- otherwise` negates
  the conjunction of `call_indirect-call`'s two premises; the table lookup is
  kept as a premise of both rules, so a missing table is stuck, not a trap. -/
  | callIndirectTrap {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {i : BitVec 32}
      {ti : TableInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
        s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) :
      ReadStep s f [constI32 i, .plain (.callIndirect x y)] [.trap]
  /-- `Step_read/call_addr` (`8-reduction:131`), Wasm code: the new frame holds
  `val^k` followed by `$default_(t)*` for the declared locals, and the body is
  wrapped in `FRAME_ n {f} (LABEL_ n {eps} instr*)`. -/
  | callAddr {s : Store H} {f : Frame} {a : FuncAddr} {vs : List Val} {fi : FuncInst H}
      {fn : Func} (hf : s.funcInst? a = some fi) (hcode : fi.code = .wasm fn)
      (hk : vs.length = fi.type.params.length) :
      ReadStep s f (vals vs ++ [.callAddr a])
        [.frame fi.type.results.length (Frame.forCall fi.module vs fn.locals)
          [.label fi.type.results.length [] (expression fn.body)]]
  -- Reference instructions (`8-reduction:210-213`)
  /-- `Step_read/ref.func` (`8-reduction:212`). -/
  | refFunc {s : Store H} {f : Frame} {x : FuncIdx} {a : FuncAddr}
      (hx : f.module.funcAddr? x = some a) :
      ReadStep s f [.plain (.refFunc x)] [.refFuncAddr a]
  -- Local instructions (`8-reduction:375-378`)
  /-- `Step_read/local.get` (`8-reduction:377`). -/
  | localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
      (h : (⟨s, f⟩ : State H).local? x = some v) :
      ReadStep s f [.plain (.localGet x)] [v.toAdmin]
  -- Global instructions (`8-reduction:387-390`)
  /-- `Step_read/global.get` (`8-reduction:389`). -/
  | globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {gi : GlobalInst}
      (h : (⟨s, f⟩ : State H).global? x = some gi) :
      ReadStep s f [.plain (.globalGet x)] [gi.value.toAdmin]
  -- Table instructions (`8-reduction:396-480`)
  /-- `Step_read/table.get-trap` (`8-reduction:398`). -/
  | tableGetTrap {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {ti : TableInst}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : ti.refs.length ≤ i.toNat) :
      ReadStep s f [constI32 i, .plain (.tableGet x)] [.trap]
  /-- `Step_read/table.get-val` (`8-reduction:402`). -/
  | tableGetVal {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {ti : TableInst}
      {r : Ref} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (hr : ti.refs[i.toNat]? = some r) :
      ReadStep s f [constI32 i, .plain (.tableGet x)] [aref r]
  /-- `Step_read/table.size` (`8-reduction:415`). -/
  | tableSize {s : Store H} {f : Frame} {x : TableIdx} {ti : TableInst} {n : BitVec 32}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (hn : ti.refs.length = n.toNat) :
      ReadStep s f [.plain (.tableSize x)] [constI32 n]
  /-- `Step_read/table.fill-trap` (`8-reduction:428`). -/
  | tableFillTrap {s : Store H} {f : Frame} {x : TableIdx} {i n : BitVec 32} {v : Val}
      {ti : TableInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (h : ti.refs.length < i.toNat + n.toNat) :
      ReadStep s f [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)] [.trap]
  /-- `Step_read/table.fill-zero` (`8-reduction:432`): `-- otherwise` (the bound
  of `-trap` fails) together with `n = 0`. -/
  | tableFillZero {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {v : Val}
      {ti : TableInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (h : i.toNat ≤ ti.refs.length) :
      ReadStep s f [constI32 i, v.toAdmin, constI32 0, .plain (.tableFill x)] []
  /-- `Step_read/table.fill-succ` (`8-reduction:437`): `-- otherwise` of both
  `-trap` and `-zero`, i.e. the bound holds and `n ≠ 0`. One element per step. -/
  | tableFillSucc {s : Store H} {f : Frame} {x : TableIdx} {i n : BitVec 32} {v : Val}
      {ti : TableInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (h : i.toNat + n.toNat ≤ ti.refs.length) (hn : n ≠ 0) :
      ReadStep s f [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)]
        [constI32 i, v.toAdmin, .plain (.tableSet x),
         constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.tableFill x)]
  /-- `Step_read/table.copy-trap` (`8-reduction:444`): `j` is the destination in
  table `x`, `i` the source in table `y`. -/
  | tableCopyTrap {s : Store H} {f : Frame} {x y : TableIdx} {j i n : BitVec 32}
      {tx ty : TableInst} (hx : (⟨s, f⟩ : State H).table? x = some tx)
      (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : ty.refs.length < i.toNat + n.toNat ∨ tx.refs.length < j.toNat + n.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)] [.trap]
  /-- `Step_read/table.copy-zero` (`8-reduction:448`). -/
  | tableCopyZero {s : Store H} {f : Frame} {x y : TableIdx} {j i : BitVec 32}
      {tx ty : TableInst} (hx : (⟨s, f⟩ : State H).table? x = some tx)
      (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : i.toNat ≤ ty.refs.length ∧ j.toNat ≤ tx.refs.length) :
      ReadStep s f [constI32 j, constI32 i, constI32 0, .plain (.tableCopy x y)] []
  /-- `Step_read/table.copy-le` (`8-reduction:453`): `j ≤ i`, so copy forwards. -/
  | tableCopyLe {s : Store H} {f : Frame} {x y : TableIdx} {j i n : BitVec 32}
      {tx ty : TableInst} (hx : (⟨s, f⟩ : State H).table? x = some tx)
      (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length)
      (hn : n ≠ 0) (hle : j.toNat ≤ i.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]
        [constI32 j, constI32 i, .plain (.tableGet y), .plain (.tableSet x),
         constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableCopy x y)]
  /-- `Step_read/table.copy-gt` (`8-reduction:460`): `-- otherwise` of `-le`,
  i.e. `i < j`, so copy backwards. -/
  | tableCopyGt {s : Store H} {f : Frame} {x y : TableIdx} {j i n : BitVec 32}
      {tx ty : TableInst} (hx : (⟨s, f⟩ : State H).table? x = some tx)
      (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length)
      (hn : n ≠ 0) (hgt : i.toNat < j.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]
        [constI32 (j + n - 1), constI32 (i + n - 1), .plain (.tableGet y), .plain (.tableSet x),
         constI32 j, constI32 i, constI32 (n - 1), .plain (.tableCopy x y)]
  /-- `Step_read/table.init-trap` (`8-reduction:467`): `j` is the destination in
  table `x`, `i` the source in element segment `y`. -/
  | tableInitTrap {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {j i n : BitVec 32}
      {ti : TableInst} {ei : ElemInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (he : (⟨s, f⟩ : State H).elem? y = some ei)
      (h : ei.refs.length < i.toNat + n.toNat ∨ ti.refs.length < j.toNat + n.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)] [.trap]
  /-- `Step_read/table.init-zero` (`8-reduction:471`). -/
  | tableInitZero {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {j i : BitVec 32}
      {ti : TableInst} {ei : ElemInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (he : (⟨s, f⟩ : State H).elem? y = some ei)
      (h : i.toNat ≤ ei.refs.length ∧ j.toNat ≤ ti.refs.length) :
      ReadStep s f [constI32 j, constI32 i, constI32 0, .plain (.tableInit x y)] []
  /-- `Step_read/table.init-succ` (`8-reduction:476`). -/
  | tableInitSucc {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {j i n : BitVec 32}
      {ti : TableInst} {ei : ElemInst} {r : Ref}
      (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (he : (⟨s, f⟩ : State H).elem? y = some ei)
      (h : i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length)
      (hn : n ≠ 0) (hr : ei.refs[i.toNat]? = some r) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)]
        [constI32 j, aref r, .plain (.tableSet x),
         constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableInit x y)]
  -- Memory instructions (`8-reduction:487-660`)
  /-- `Step_read/load-num-trap` (`8-reduction:489`), integers. -/
  | loadIntTrap {s : Store H} {f : Frame} {t : IntType} {ao : MemArg} {i : BitVec 32}
      {mi : MemInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      ReadStep s f [constI32 i, .plain (.intLoad t none ao)] [.trap]
  /-- `Step_read/load-num-val` (`8-reduction:493`), integers. -/
  | loadIntVal {s : Store H} {f : Frame} {t : IntType} {ao : MemArg} {i : BitVec 32}
      {mi : MemInst} {c : BitVec t.width} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hb : readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) = some (nbytes (.int t) c)) :
      ReadStep s f [constI32 i, .plain (.intLoad t none ao)] [.plain (.intConst t c)]
  /-- `Step_read/load-num-trap` (`8-reduction:489`), floats. -/
  | loadFloatTrap {s : Store H} {f : Frame} {t : FloatType} {ao : MemArg} {i : BitVec 32}
      {mi : MemInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      ReadStep s f [constI32 i, .plain (.floatLoad t ao)] [.trap]
  /-- `Step_read/load-num-val` (`8-reduction:493`), floats. -/
  | loadFloatVal {s : Store H} {f : Frame} {t : FloatType} {ao : MemArg} {i : BitVec 32}
      {mi : MemInst} {c : BitVec t.width} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hb : readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) = some (fbytes t c)) :
      ReadStep s f [constI32 i, .plain (.floatLoad t ao)] [.plain (.floatConst t c)]
  /-- `Step_read/load-pack-trap` (`8-reduction:497`). -/
  | loadPackTrap {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness}
      {ao : MemArg} {i : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
      ReadStep s f [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)] [.trap]
  /-- `Step_read/load-pack-val` (`8-reduction:501`): the loaded `n` bits are
  `$extend__(n, $size(Inn), sx, c)`. -/
  | loadPackVal {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness}
      {ao : MemArg} {i : BitVec 32} {mi : MemInst} {c : BitVec sz.width}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hb : readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8) = some (ibytes sz.width c)) :
      ReadStep s f [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]
        [.plain (.intConst t (match sx with
          | .signed => c.signExtend t.width
          | .unsigned => c.setWidth t.width))]
  /-- `Step_read/vload-oob` (`8-reduction:505`), `vload-shape-oob` (`:514`),
  `vload-splat-oob` (`:525`) and `vload-zero-oob` (`:537`): one constructor, the
  access width read off `$vloadop` by `VecLoadOp.accessWidth`. -/
  | vecLoadOob {s : Store H} {f : Frame} {op : Option VecLoadOp} {ao : MemArg} {i : BitVec 32}
      {mi : MemInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + VecLoadOp.accessWidth op / 8) :
      ReadStep s f [constI32 i, .plain (.vecLoad op ao)] [.trap]
  /-- `Step_read/vload-val` (`8-reduction:509`), `vload-shape-val` (`:518`),
  `vload-splat-val` (`:529`) and `vload-zero-val` (`:541`): one constructor, the
  lane assembly performed by `vecLoadResult`. -/
  | vecLoadVal {s : Store H} {f : Frame} {op : Option VecLoadOp} {ao : MemArg} {i : BitVec 32}
      {mi : MemInst} {c : BitVec (VecLoadOp.accessWidth op)}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hb : readBytes mi.bytes (effAddr i.toNat ao) (VecLoadOp.accessWidth op / 8)
        = some (ibytes (VecLoadOp.accessWidth op) c)) :
      ReadStep s f [constI32 i, .plain (.vecLoad op ao)] [vconst (vecLoadResult op c)]
  /-- `Step_read/vload_lane-oob` (`8-reduction:547`). -/
  | vecLoadLaneOob {s : Store H} {f : Frame} {sz : PackSize} {ao : MemArg} {j : LaneIdx}
      {i : BitVec 32} {c₁ : V128} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
      ReadStep s f [constI32 i, vconst c₁, .plain (.vecLoadLane sz ao j)] [.trap]
  /-- `Step_read/vload_lane-val` (`8-reduction:551`). The lane update
  `$lanes_(Jnn X M, c_1)[[j] = k]` is partial, so an out-of-range lane is stuck;
  the bound is a typing premise (`Instr_ok/vload_lane`, `6-typing:517-521`). -/
  | vecLoadLaneVal {s : Store H} {f : Frame} {sz : PackSize} {ao : MemArg} {j : LaneIdx}
      {i : BitVec 32} {c₁ : V128} {mi : MemInst} {k : BitVec sz.width}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hj : j.val < 128 / sz.width)
      (hb : readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8)
        = some (ibytes sz.width k)) :
      ReadStep s f [constI32 i, vconst c₁, .plain (.vecLoadLane sz ao j)]
        [vconst (Numerics.invLanes sz.width
          ((Numerics.lanes sz.width (128 / sz.width) c₁).set j.val k))]
  /-- `Step_read/memory.size` (`8-reduction:595`): `$(n * 64 * $Ki)` is the
  memory's byte size, so the premise also forces the size to be a whole number of
  pages. -/
  | memorySize {s : Store H} {f : Frame} {mi : MemInst} {n : BitVec 32}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hn : n.toNat * pageSize = mi.bytes.size) :
      ReadStep s f [.plain .memorySize] [constI32 n]
  /-- `Step_read/memory.fill-trap` (`8-reduction:608`). -/
  | memoryFillTrap {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < i.toNat + n.toNat) :
      ReadStep s f [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill] [.trap]
  /-- `Step_read/memory.fill-zero` (`8-reduction:612`). -/
  | memoryFillZero {s : Store H} {f : Frame} {i : BitVec 32} {v : Val} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (h : i.toNat ≤ mi.bytes.size) :
      ReadStep s f [constI32 i, v.toAdmin, constI32 0, .plain .memoryFill] []
  /-- `Step_read/memory.fill-succ` (`8-reduction:617`): one byte per step. -/
  | memoryFillSucc {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : i.toNat + n.toNat ≤ mi.bytes.size) (hn : n ≠ 0) :
      ReadStep s f [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]
        [constI32 i, v.toAdmin, store8,
         constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain .memoryFill]
  /-- `Step_read/memory.copy-trap` (`8-reduction:624`): `j` is the destination,
  `i` the source, both in the single memory. -/
  | memoryCopyTrap {s : Store H} {f : Frame} {j i n : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain .memoryCopy] [.trap]
  /-- `Step_read/memory.copy-zero` (`8-reduction:628`). -/
  | memoryCopyZero {s : Store H} {f : Frame} {j i : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ mi.bytes.size) :
      ReadStep s f [constI32 j, constI32 i, constI32 0, .plain .memoryCopy] []
  /-- `Step_read/memory.copy-le` (`8-reduction:633`): `j ≤ i`, copy forwards. -/
  | memoryCopyLe {s : Store H} {f : Frame} {j i n : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
      (hn : n ≠ 0) (hle : j.toNat ≤ i.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]
        [constI32 j, constI32 i, load8u, store8,
         constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain .memoryCopy]
  /-- `Step_read/memory.copy-gt` (`8-reduction:640`): `-- otherwise` of `-le`,
  i.e. `i < j`, copy backwards. -/
  | memoryCopyGt {s : Store H} {f : Frame} {j i n : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
      (hn : n ≠ 0) (hgt : i.toNat < j.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]
        [constI32 (j + n - 1), constI32 (i + n - 1), load8u, store8,
         constI32 j, constI32 i, constI32 (n - 1), .plain .memoryCopy]
  /-- `Step_read/memory.init-trap` (`8-reduction:647`): `j` is the destination in
  memory, `i` the source in data segment `x`. -/
  | memoryInitTrap {s : Store H} {f : Frame} {x : DataIdx} {j i n : BitVec 32} {mi : MemInst}
      {di : DataInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hd : (⟨s, f⟩ : State H).data? x = some di)
      (h : di.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)] [.trap]
  /-- `Step_read/memory.init-zero` (`8-reduction:651`). -/
  | memoryInitZero {s : Store H} {f : Frame} {x : DataIdx} {j i : BitVec 32} {mi : MemInst}
      {di : DataInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hd : (⟨s, f⟩ : State H).data? x = some di)
      (h : i.toNat ≤ di.bytes.size ∧ j.toNat ≤ mi.bytes.size) :
      ReadStep s f [constI32 j, constI32 i, constI32 0, .plain (.memoryInit x)] []
  /-- `Step_read/memory.init-succ` (`8-reduction:656`). -/
  | memoryInitSucc {s : Store H} {f : Frame} {x : DataIdx} {j i n : BitVec 32} {mi : MemInst}
      {di : DataInst} {b : UInt8} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hd : (⟨s, f⟩ : State H).data? x = some di)
      (h : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
      (hn : n ≠ 0) (hb : di.bytes.data[i.toNat]? = some b) :
      ReadStep s f [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)]
        [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8,
         constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)]

/-! ## `Step` (`8-reduction:5`)

The lifting rules, the context rules, and every rule that writes the state. -/

inductive Step (P : Profile) (host : HostSemantics H) : Config H → Config H → Prop where
  -- Structural (`8-reduction:10-16`)
  /-- `Step/pure` (`8-reduction:10`). -/
  | pure {s : Store H} {f : Frame} {is is' : List Admin} (h : PureStep P is is') :
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step/read` (`8-reduction:14`). -/
  | read {s : Store H} {f : Frame} {is is' : List Admin} (h : ReadStep s f is is') :
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  -- Context (`8-reduction:161-169`)
  /-- `Step/ctxt-instrs`. **Deviation 1**: absent from SpecTec 2.0, taken
  verbatim from wasm-1.0 `8-reduction:165` (= wasm-3.0
  `4.3-execution.instructions.spectec:32`). Without it no sequence of more than
  one instruction reduces. See the module docstring. -/
  | ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
      (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hne : vs ≠ [] ∨ rest ≠ []) :
      Step P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
  /-- `Step/ctxt-label` (`8-reduction:163`). The whole state, frame included,
  may change. -/
  | ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
      {is is' : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Step P host ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩
  /-- `Step/ctxt-frame` (`8-reduction:167`): the inner step runs under the inner
  frame, the outer frame `f` is restored, and the outer configuration changes
  only in its store. **Deviation 2**: SpecTec 2.0 writes the *same* `f'` on both
  sides of the premise, which would make `local.set` stuck inside any frame; we
  follow wasm-1.0 `8-reduction:161` and wasm-3.0
  `4.3-execution.instructions.spectec:45`, which use a fresh `f''`. -/
  | ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : Step P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
      Step P host ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩
  -- Host functions (**Deviation 3**; SpecTec 2.0 has none)
  /-- `CALL_ADDR a` on a host function that returns: the counterpart of Core
  3.0's `Step/call_ref-hostfunc-res`. -/
  | callAddrHost {s s' : Store H} {f : Frame} {a : FuncAddr} {vs : List Val} {fi : FuncInst H}
      {h : H} {r : Result} (hf : s.funcInst? a = some fi) (hcode : fi.code = .host h)
      (hk : vs.length = fi.type.params.length) (hhost : host h s vs (.returned s' r)) :
      Step P host ⟨s, f, vals vs ++ [.callAddr a]⟩ ⟨s', f, r.toAdmin⟩
  /-- `CALL_ADDR a` on a host function that diverges: the configuration steps to
  itself, so `Diverges` holds. Counterpart of Core 3.0's
  `Step/call_ref-hostfunc-div`. -/
  | callAddrHostDiv {s : Store H} {f : Frame} {a : FuncAddr} {vs : List Val} {fi : FuncInst H}
      {h : H} (hf : s.funcInst? a = some fi) (hcode : fi.code = .host h)
      (hk : vs.length = fi.type.params.length) (hhost : host h s vs .diverged) :
      Step P host ⟨s, f, vals vs ++ [.callAddr a]⟩ ⟨s, f, vals vs ++ [.callAddr a]⟩
  -- Local instructions (`8-reduction:380`)
  /-- `Step/local.set` (`8-reduction:380`): `$with_local(z, x, val)`.

  The bound `hx` is SpecTec's, not an addition: `$with_local((s; f), x, v)` is
  `s; f[.LOCALS[x] = v]` (`5-runtime-aux:104`), and SpecTec's array update is
  **partial** — it has no value when `x >= |f.LOCALS|`, so the rule does not fire.
  Lean's `List.set` is total (the identity out of range), so the bound has to be
  written out. Without it the rule is strictly more permissive than both SpecTec
  and Core 3.0 (`Core.VariableStep.localSet` carries the same premise), and the
  `2.0 ⊆ 3.0` step simulation would be false; `Instr_ok/local.set`
  (`6-typing:375-377`) supplies it in every well-typed configuration. -/
  | localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
      (hx : x.toNat < f.locals.length) :
      Step P host ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩
  -- Global instructions (`8-reduction:392`)
  /-- `Step/global.set` (`8-reduction:392`): `$with_global(z, x, val)`. -/
  | globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : GlobalAddr}
      {gi : GlobalInst} (ha : f.module.globalAddr? x = some a) (hg : s.globalInst? a = some gi) :
      Step P host ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩
        ⟨s.setGlobalInst a { gi with value := v }, f, []⟩
  -- Table instructions (`8-reduction:406-425, 483`)
  /-- `Step/table.set-trap` (`8-reduction:406`). -/
  | tableSetTrap {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref}
      {a : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti) (h : ti.refs.length ≤ i.toNat) :
      Step P host ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/table.set-val` (`8-reduction:410`): `$with_table(z, x, i, ref)`. -/
  | tableSetVal {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref}
      {a : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti) (h : i.toNat < ti.refs.length) :
      Step P host ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩
        ⟨s.setTableInst a (ti.setRef i.toNat r), f, []⟩
  /-- `Step/table.grow-succeed` (`8-reduction:420`): the result is the **old**
  size. `P.growMaySucceed` is the profile's grow policy (`True` for
  `Profile.spec`). -/
  | tableGrowSucceed {s : Store H} {f : Frame} {x : TableIdx} {n : BitVec 32} {r : Ref}
      {a : TableAddr} {ti ti' : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti) (hg : ti.grow? n.toNat r = some ti')
      (hp : P.growMaySucceed .table a ti.refs.length n.toNat) :
      Step P host ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩
        ⟨s.setTableInst a ti', f, [constI32 (BitVec.ofNat 32 ti.refs.length)]⟩
  /-- `Step/table.grow-fail` (`8-reduction:424`): `$inv_signed_(32, -1)`.
  SpecTec's rule is unconditional; `P.growMayFail` is `True` for `Profile.spec`,
  and growth that is impossible always fails. -/
  | tableGrowFail {s : Store H} {f : Frame} {x : TableIdx} {n : BitVec 32} {r : Ref}
      {a : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti)
      (hp : P.growMayFail .table a ti.refs.length n.toNat ∨ ti.grow? n.toNat r = none) :
      Step P host ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩
        ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩
  /-- `Step/elem.drop` (`8-reduction:483`): `$with_elem(z, x, eps)`. -/
  | elemDrop {s : Store H} {f : Frame} {x : ElemIdx} {a : ElemAddr} {ei : ElemInst}
      (ha : f.module.elemAddr? x = some a) (he : s.elemInst? a = some ei) :
      Step P host ⟨s, f, [.plain (.elemDrop x)]⟩
        ⟨s.setElemInst a { ei with refs := [] }, f, []⟩
  -- Memory instructions (`8-reduction:559-605, 663`)
  /-- `Step/store-num-trap` (`8-reduction:559`), integers. -/
  | storeIntTrap {s : Store H} {f : Frame} {t : IntType} {ao : MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      Step P host ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t none ao)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/store-num-val` (`8-reduction:563`), integers:
  `$with_mem(z, 0, i + ao.OFFSET, $size(nt)/8, $nbytes_(nt, c))`. -/
  | storeIntVal {s : Store H} {f : Frame} {t : IntType} {ao : MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (nbytes (.int t) c) = some mi') :
      Step P host ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t none ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩
  /-- `Step/store-num-trap` (`8-reduction:559`), floats. -/
  | storeFloatTrap {s : Store H} {f : Frame} {t : FloatType} {ao : MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      Step P host ⟨s, f, [constI32 i, .plain (.floatConst t c), .plain (.floatStore t ao)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/store-num-val` (`8-reduction:563`), floats. -/
  | storeFloatVal {s : Store H} {f : Frame} {t : FloatType} {ao : MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (fbytes t c) = some mi') :
      Step P host ⟨s, f, [constI32 i, .plain (.floatConst t c), .plain (.floatStore t ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩
  /-- `Step/store-pack-trap` (`8-reduction:567`). -/
  | storePackTrap {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {ao : MemArg}
      {i : BitVec 32} {c : BitVec t.width} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
      Step P host ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t (some sz) ao)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/store-pack-val` (`8-reduction:571`): the stored bytes are
  `$ibytes_(n, $wrap__($size(Inn), n, c))`. -/
  | storePackVal {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {ao : MemArg}
      {i : BitVec 32} {c : BitVec t.width} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
        (ibytes sz.width (c.setWidth sz.width)) = some mi') :
      Step P host ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t (some sz) ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩
  /-- `Step/vstore-oob` (`8-reduction:575`). -/
  | vecStoreOob {s : Store H} {f : Frame} {ao : MemArg} {i : BitVec 32} {c : V128}
      {a : MemAddr} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
      (hm : s.memInst? a = some mi) (h : mi.bytes.size < effAddr i.toNat ao + 16) :
      Step P host ⟨s, f, [constI32 i, vconst c, .plain (.vecStore ao)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/vstore-val` (`8-reduction:579`). -/
  | vecStoreVal {s : Store H} {f : Frame} {ao : MemArg} {i : BitVec 32} {c : V128}
      {a : MemAddr} {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
      (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) 16 (vbytes c) = some mi') :
      Step P host ⟨s, f, [constI32 i, vconst c, .plain (.vecStore ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩
  /-- `Step/vstore_lane-oob` (`8-reduction:584`). -/
  | vecStoreLaneOob {s : Store H} {f : Frame} {sz : PackSize} {ao : MemArg} {j : LaneIdx}
      {i : BitVec 32} {c : V128} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
      Step P host ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/vstore_lane-val` (`8-reduction:588`): the stored bytes are
  `$ibytes_(N, $lanes_(Jnn X M, c)[j])` with `M = 128/N`. The lane indexing is
  partial, so an out-of-range lane is stuck. -/
  | vecStoreLaneVal {s : Store H} {f : Frame} {sz : PackSize} {ao : MemArg} {j : LaneIdx}
      {i : BitVec 32} {c : V128} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hj : j.val < 128 / sz.width)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
        (ibytes sz.width ((Numerics.lanes sz.width (128 / sz.width) c).getD j.val 0))
          = some mi') :
      Step P host ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩
        ⟨s.setMemInst a mi', f, []⟩
  /-- `Step/memory.grow-succeed` (`8-reduction:600`): the result is the **old**
  size in pages. -/
  | memoryGrowSucceed {s : Store H} {f : Frame} {n : BitVec 32} {a : MemAddr}
      {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
      (hm : s.memInst? a = some mi) (hg : mi.grow? n.toNat = some mi')
      (hp : P.growMaySucceed .memory a mi.pages n.toNat) :
      Step P host ⟨s, f, [constI32 n, .plain .memoryGrow]⟩
        ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩
  /-- `Step/memory.grow-fail` (`8-reduction:604`): `$inv_signed_(32, -1)`. -/
  | memoryGrowFail {s : Store H} {f : Frame} {n : BitVec 32} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hp : P.growMayFail .memory a mi.pages n.toNat ∨ mi.grow? n.toNat = none) :
      Step P host ⟨s, f, [constI32 n, .plain .memoryGrow]⟩
        ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩
  /-- `Step/data.drop` (`8-reduction:663`): `$with_data(z, x, eps)`. -/
  | dataDrop {s : Store H} {f : Frame} {x : DataIdx} {a : DataAddr} {di : DataInst}
      (ha : f.module.dataAddr? x = some a) (hd : s.dataInst? a = some di) :
      Step P host ⟨s, f, [.plain (.dataDrop x)]⟩ ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩

/-! ## `Steps`, divergence and `Eval_expr` -/

/-- `Steps: config ~>* config` (`8-reduction:8`, rules `Steps/refl` and
`Steps/trans`, `8-reduction:18-24`). -/
abbrev Steps (P : Profile) (host : HostSemantics H) := Relation.ReflTransGen (Step P host)

/-- An infinite reduction sequence. Not in SpecTec (which has no coinductive
relation); it is what makes a divergent host call observable. -/
def Diverges (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  InfiniteTrace (Step P host) c

/-- `Eval_expr: z; expr ~>* z'; val*` (`8-reduction:29-33`). -/
def EvalExpr (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (e : Expr)
    (s' : Store H) (f' : Frame) (vs : List Val) : Prop :=
  Steps P host ⟨s, f, expression e⟩ ⟨s', f', vals vs⟩

/-! ## Properties -/

variable {P : Profile} {host : HostSemantics H}

/-- A single step is a reduction sequence (`Steps/trans` with `Steps/refl`). -/
theorem Step.steps {c c' : Config H} (h : Step P host c c') : Steps P host c c' :=
  Relation.ReflTransGen.single h

/-- `Step/ctxt-label` for whole reduction sequences. -/
theorem Steps.ctxtLabel (n : Nat) (cont : List Instr) {s s' : Store H} {f f' : Frame}
    {is is' : List Admin} (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  have key : ∀ c c' : Config H, Steps P host c c' →
      Steps P host ⟨c.store, c.frame, [.label n cont c.code]⟩
        ⟨c'.store, c'.frame, [.label n cont c'.code]⟩ := by
    intro c c' hc
    induction hc with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail (Step.ctxtLabel hstep)
  exact key _ _ h

/-- `Step/ctxt-frame` for whole reduction sequences: the inner frame evolves and
the outer frame is restored at every step. -/
theorem Steps.ctxtFrame (n : Nat) (f : Frame) {s s' : Store H} {fi fi' : Frame}
    {is is' : List Admin} (h : Steps P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Steps P host ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  have key : ∀ c c' : Config H, Steps P host c c' →
      Steps P host ⟨c.store, f, [.frame n c.frame c.code]⟩
        ⟨c'.store, f, [.frame n c'.frame c'.code]⟩ := by
    intro c c' hc
    induction hc with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail (Step.ctxtFrame hstep)
  exact key _ _ h

/-- Framing by a value prefix and an instruction suffix, for whole reduction
sequences.

This holds for **every** rule, not only the lifted ones, because `Step` contains
the closure rule `Step.ctxtInstrs` (deviation 1 of the module docstring). The
side condition `val* =/= eps \/ instr_1* =/= eps` of that rule is not needed
here: when both lists are empty the statement is the hypothesis itself. Were
`Step.ctxtInstrs` dropped — i.e. were SpecTec 2.0's rule set taken literally —
this statement would be *false*, already for `Step/pure` with
`PureStep.nop`. -/
theorem Steps.ctxtInstrs (vs : List Val) (rest : List Admin) {s s' : Store H} {f f' : Frame}
    {is is' : List Admin} (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  rcases Classical.em (vs = [] ∧ rest = []) with ⟨rfl, rfl⟩ | hne
  · simpa using h
  · have hne' : vs ≠ [] ∨ rest ≠ [] := by
      by_contra hc
      exact hne ⟨by simpa using (not_or.mp hc).1, by simpa using (not_or.mp hc).2⟩
    have key : ∀ c c' : Config H, Steps P host c c' →
        Steps P host ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
          ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩ := by
      intro c c' hc
      induction hc with
      | refl => exact .refl
      | tail _ hstep ih => exact ih.tail (Step.ctxtInstrs hstep hne')
    exact key _ _ h

/-- Divergence inside a label diverges. -/
theorem Diverges.label (n : Nat) (cont : List Instr) {s : Store H} {f : Frame}
    {is : List Admin} (h : Diverges P host ⟨s, f, is⟩) :
    Diverges P host ⟨s, f, [.label n cont is]⟩ :=
  InfiniteTrace.map
    (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun _ _ hs => Step.ctxtLabel hs) h

/-- Divergence inside a frame diverges. -/
theorem Diverges.frame (n : Nat) (f : Frame) {s : Store H} {fi : Frame} {is : List Admin}
    (h : Diverges P host ⟨s, fi, is⟩) : Diverges P host ⟨s, f, [.frame n fi is]⟩ :=
  InfiniteTrace.map
    (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun _ _ hs => Step.ctxtFrame hs) h

/-- Every element of `val*` is a value. -/
theorem isVal_of_mem_vals {vs : List Val} {a : Admin} (h : a ∈ vals vs) : a.isVal := by
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp h
  simp

@[simp] theorem all_isVal_vals (vs : List Val) : (vals vs).all Admin.isVal = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

/-- No `Step_pure` rule applies to a sequence of values: every left-hand side of
`8-reduction` contains an instruction, a `LABEL_`, a `FRAME_` or a `TRAP`. -/
theorem PureStep.not_allVals {is is' : List Admin} (h : PureStep P is is') :
    is.all Admin.isVal = false := by
  cases h <;> simp [Admin.isVal, Admin.val?]

/-- No `Step_read` rule applies to a sequence of values. -/
theorem ReadStep.not_allVals {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') : is.all Admin.isVal = false := by
  cases h <;> simp [Admin.isVal, Admin.val?]

/-- No `Step` rule applies to a sequence of values. -/
theorem Step.not_allVals {c c' : Config H} (h : Step P host c c') :
    c.code.all Admin.isVal = false := by
  induction h with
  | pure hp => exact hp.not_allVals
  | read hr => exact hr.not_allVals
  | ctxtInstrs _ _ ih =>
      simp only [List.all_append, ih, Bool.and_false, Bool.false_and]
  | _ => simp [Admin.isVal, Admin.val?]

/-- A configuration whose code is a sequence of values does not step: values are
the normal forms of `Step` other than `TRAP`. -/
theorem Step.not_vals {s : Store H} {f : Frame} {vs : List Val} {c' : Config H} :
    ¬ Step P host ⟨s, f, vals vs⟩ c' := fun h => by
  have h1 : (vals vs).all Admin.isVal = false := h.not_allVals
  rw [all_isVal_vals] at h1
  exact Bool.noConfusion h1

end Silmaril.Wasm.V2.Execution
