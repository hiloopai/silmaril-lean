module

public import Silmaril.Wasm.Det.Core.Defs

/-!
# The memory-free, float-free subset of Wasm 3.0

A syntactic subset of Core 3.0 code, used to prove determinism modulo traps and imports
(`Silmaril.Wasm.Det.Core.DetCfg`) at **every** profile (`Silmaril.Wasm.Det.NoMem.Thms`).

## The subset

`flatOk` lists the flat instructions of the subset: control (`nop`, `unreachable`, `drop`,
`select`, branches including `br_on_null`/`br_on_cast`, `return`), exceptions (`throw`,
`throw_ref`; `try_table` through `instrB`), locals and globals, the table instructions other
than `table.grow` (`table.get/set/size/fill/copy/init`, `elem.drop`), references and GC (`ref.*`,
`i31`, `struct.*`, `array.*`, `extern.convert_any`, `any.convert_extern`), integer constants and
operators, and the integer conversions `i32.wrap_i64`, `i64.extend_i32_s/u`.

Excluded: every memory instruction (loads, stores, `memory.*`, `data.drop`), every float
instruction (constants, operators, comparisons, conversions involving floats), every vector
instruction, and `table.grow` (whose failure is a profile choice that does not trap).

Not a restriction: silmaril-lean's Core 3.0 `Step` has no allocation-failure rule for GC
(`struct.new`, `array.new*`): the aggregate rules do not mention the profile. Hence in this
subset no profile choice is left at all; "modulo traps" refers to the semantics' own traps
(division by zero, failing casts, out-of-bounds table and array accesses, `unreachable`).

## Two modes

`instrB q ind fs i` checks an instruction (recursively through `block`, `loop`, `if` and
`try_table` bodies) in a module instance with function address list `fs`:

* `q : Nat → Bool` is the set of function addresses that may be **entered**: a direct `call x`
  or `return_call x` must resolve (through `fs`) into `q`;
* `ind : Bool` allows the indirect calls `call_ref`, `call_indirect`, `return_call_ref` and
  `return_call_indirect`; the invariant needs `q` to be everything then (`Mode`).

**Full mode** (`q = fun _ => true`, `ind = true`): every Wasm function of the store is in the
subset (`storeB`); this is the per-module/instance criterion. **Direct mode** (`q` a list `A` of
addresses, `ind = false`): only the functions of `A` are checked, and their direct calls stay in
`A` (`closB`); this is the per-function criterion, which holds inside modules that are not in the
subset (another function may use floats or memory: it is never entered).

## The invariant on configurations

* `IsCRT a`: `a` is an administrative `call_ref`/`return_call_ref` with a runtime type (the code
  a `call` reduces to: `ref.func a; call_ref`);
* `InS q a`: `a` may stand right before such an administrative call: a reference whose function
  address is in `q`, a `trap` or a `throw_ref` (the last two only bubble);
* `AOk q ind fs a`, `Seq q ind fs p l`: administrative code whose source instructions pass
  `instrB` (constants of every type are allowed, since parameters and fields may hold floats),
  where every administrative call is preceded by an `InS` element (`p`: whether the element
  before the list is `InS`); frames switch to their own module instance;
* `FunOk q ind F`: every Wasm function at an address in `q` has a body passing `instrB` in its own
  module instance;
* `Inv q ind c`: `Mode q ind`, `Seq` of the code in the frame's module instance, `FunOk` of the
  store's functions.

## Executable checks

* `funcB q ind fi`, `storeB s` (full mode, every function), `closB s A` (direct mode on `A`);
* `callees s a`, `clos s a`: the direct-call successors of a function and a fuelled closure;
  `detFnB s a := (clos s a).contains a && closB s (clos s a)`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## Instructions -/

/-- Flat instructions of the subset (structured instructions and calls are handled by
`instrB`). -/
def flatOk : Instr → Bool
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .brOnNull _
  | .brOnNonNull _ | .brOnCast _ _ _ | .brOnCastFail _ _ _ | .return_ | .throw _ | .throwRef
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _
  | .tableGet _ | .tableSet _ | .tableSize _ | .tableFill _ | .tableCopy _ _ | .tableInit _ _
  | .elemDrop _
  | .refNull _ | .refIsNull | .refAsNonNull | .refEq | .refTest _ | .refCast _ | .refFunc _
  | .refI31 | .i31Get _ | .structNew _ | .structNewDefault _ | .structGet _ _ _ | .structSet _ _
  | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _ | .arrayNewData _ _
  | .arrayNewElem _ _ | .arrayGet _ _ | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy _ _
  | .arrayInitData _ _ | .arrayInitElem _ _ | .externConvertAny | .anyConvertExtern
  | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ => true
  | .convert .wrap | .convert (.extend _) => true
  | _ => false

/-- A direct call of function index `x` in a module instance with function addresses `fs` may
be entered: it resolves into `q` (or does not resolve, and gets stuck). -/
def callOk (q : Nat → Bool) (fs : List Nat) (x : FuncIdx) : Bool :=
  match fs[x.toNat]? with
  | some b => q b
  | none => true

mutual
/-- An instruction of the subset, in a module instance with function addresses `fs`: direct
calls resolve into `q`, indirect calls need `ind`. -/
def instrB (q : Nat → Bool) (ind : Bool) (fs : List Nat) : Instr → Bool
  | .block _ b => instrsB q ind fs b
  | .loop _ b => instrsB q ind fs b
  | .if_ _ b₁ b₂ => instrsB q ind fs b₁ && instrsB q ind fs b₂
  | .tryTable _ _ b => instrsB q ind fs b
  | .call x => callOk q fs x
  | .returnCall x => callOk q fs x
  | .callRef _ => ind
  | .callIndirect _ _ => ind
  | .returnCallRef _ => ind
  | .returnCallIndirect _ _ => ind
  | i => flatOk i

/-- `instrB` on a sequence. -/
def instrsB (q : Nat → Bool) (ind : Bool) (fs : List Nat) : List Instr → Bool
  | [] => true
  | i :: is => instrB q ind fs i && instrsB q ind fs is
end

/-! ## Administrative code -/

/-- An administrative `call_ref`/`return_call_ref` with a runtime type. -/
def IsCRT : Admin → Prop
  | .callRefType _ => True
  | .returnCallRefType _ => True
  | _ => False

/-- An element that may precede an administrative call: a reference whose function address is
in `q`, a `trap` or a `throw_ref`. -/
def InS (q : Nat → Bool) : Admin → Prop
  | .trap => True
  | .plain .throwRef => True
  | .ref r => ∀ b, r = .func b → q b = true
  | _ => False

/-- A plain instruction of administrative code: an instruction of the subset, or a constant of
any type (values of every type may be passed around). -/
def PlainOk (q : Nat → Bool) (ind : Bool) (fs : List Nat) (i : Instr) : Prop :=
  instrB q ind fs i = true ∨ (∃ t b, i = .floatConst t b) ∨ (∃ b, i = .vecConst b)

mutual
/-- An administrative instruction of the subset, in a module instance with function addresses
`fs` (frames switch to their own instance). -/
def AOk (q : Nat → Bool) (ind : Bool) (fs : List Nat) : Admin → Prop
  | .plain i => PlainOk q ind fs i
  | .label _ cont body => (∀ i ∈ cont, instrB q ind fs i = true) ∧ Seq q ind fs False body
  | .handler _ _ body => Seq q ind fs False body
  | .frame _ f body => Seq q ind f.module.funcs False body
  | .ref _ => True
  | .callRefType _ => True
  | .returnCallRefType _ => True
  | .trap => True

/-- Administrative code of the subset; `p` says whether the element before the code may precede
an administrative call (`InS`). -/
def Seq (q : Nat → Bool) (ind : Bool) (fs : List Nat) : Prop → List Admin → Prop
  | _, [] => True
  | p, a :: as => (IsCRT a → p) ∧ AOk q ind fs a ∧ Seq q ind fs (InS q a) as
end

/-- Whether the last element of `l` (or, for `l = []`, the element before it, `p`) is `InS`. -/
def lastS (q : Nat → Bool) : Prop → List Admin → Prop
  | p, [] => p
  | _, a :: as => lastS q (InS q a) as

/-! ## Stores and configurations -/

/-- Every Wasm function at an address in `q` has a body of the subset, in its own module
instance. -/
def FunOk {H : Type} (q : Nat → Bool) (ind : Bool) (F : List (FuncInst H)) : Prop :=
  ∀ b fi fn, q b = true → F[b]? = some fi → fi.code = .wasm fn →
    instrsB q ind fi.module.funcs fn.body = true

/-- Indirect calls are only allowed when every function may be entered. -/
def Mode (q : Nat → Bool) (ind : Bool) : Prop := ind = true → ∀ b, q b = true

/-- **The invariant**: the code is of the subset (in the frame's module instance) and so is
every function that may be entered. -/
def Inv (q : Nat → Bool) (ind : Bool) (c : Config Nat) : Prop :=
  Mode q ind ∧ Seq q ind c.frame.module.funcs False c.code ∧ FunOk q ind c.store.funcs

/-! ## Executable checks -/

/-- A function instance passes the check (host functions pass: they are imports). -/
def funcB {H : Type} (q : Nat → Bool) (ind : Bool) (fi : FuncInst H) : Bool :=
  match fi.code with
  | .wasm fn => instrsB q ind fi.module.funcs fn.body
  | .host _ => true

/-- **Full mode**: every function of the store is in the subset (indirect calls allowed). -/
def storeB (s : Store Nat) : Bool := s.funcs.all (funcB (fun _ => true) true)

/-- **Direct mode** on the addresses `A`: every function of `A` is in the subset without indirect
calls, and its direct calls resolve into `A`. -/
def closB (s : Store Nat) (A : List Nat) : Bool :=
  A.all fun b => match s.funcs[b]? with
    | some fi => funcB (fun x => A.contains x) false fi
    | none => true

mutual
/-- The function indices named by direct calls (`call`, `return_call`), through nested
bodies. -/
def instrCalls : Instr → List Nat
  | .call x => [x.toNat]
  | .returnCall x => [x.toNat]
  | .block _ b => instrsCalls b
  | .loop _ b => instrsCalls b
  | .tryTable _ _ b => instrsCalls b
  | .if_ _ b₁ b₂ => instrsCalls b₁ ++ instrsCalls b₂
  | _ => []

/-- `instrCalls` on a sequence. -/
def instrsCalls : List Instr → List Nat
  | [] => []
  | i :: is => instrCalls i ++ instrsCalls is
end

/-- The direct-call successors of the function at `b`. -/
def callees (s : Store Nat) (b : Nat) : List Nat :=
  match s.funcs[b]? with
  | some fi => match fi.code with
    | .wasm fn => (instrsCalls fn.body).filterMap (fi.module.funcs[·]?)
    | .host _ => []
  | none => []

/-- One round of closure under direct calls. -/
def growB (s : Store Nat) (A : List Nat) : List Nat :=
  (A.flatMap (callees s)).foldl (fun B b => if B.contains b then B else B ++ [b]) A

/-- The direct-call closure of `a`, with as many rounds as the store has functions. -/
def clos (s : Store Nat) (a : Nat) : List Nat :=
  (List.range s.funcs.length).foldl (fun A _ => growB s A) [a]

/-- **The per-function check**: the direct-call closure of `a` passes `closB`. -/
def detFnB (s : Store Nat) (a : Nat) : Bool :=
  (clos s a).contains a && closB s (clos s a)

end Silmaril.Wasm.Det.NoMem
