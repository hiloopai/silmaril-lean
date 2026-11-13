module

public import Silmaril.Wasm.Auto2.Valid.Defs

@[expose] public section

/-!
# The structural validator, extended: control flow, calls, globals, memory

`Silmaril.Wasm.Auto2.Valid` checks straight-line numeric code by
structural recursion and leaves every function with a block, a branch, a call, a global or a
memory access to silmaril-lean's generic checker. This module extends the fast path, still by
structural recursion over the decoded instructions (`seqN`: on the nesting depth, then on the
list; recursion over the nested `Instr`/`List Instr` costs about twice as much in the kernel), to

* `block`, `loop` and `if` with block types over number types (the label stack is the context's,
  as in silmaril-lean: `C.withLabel`), nested up to `depthBound`;
* `br`, `br_if`, `br_table` and `return` to labels of number types, and `unreachable`, as the
  last instruction of their sequence (a stack-polymorphic instruction followed by dead code takes
  the default path);
* `call` of a function whose type has number parameters and results;
* `global.get`/`global.set` of numeric globals, untyped `select` on equal number types, and the
  memory instructions whose operands and results are number types (`memorySig?`: loads, stores,
  `memory.size`, `memory.grow`, `memory.fill`, `memory.copy`, `memory.init`, `data.drop`).

It also removes the module-level costs measured for `Valid` (`docs/projects/wasm-binaryen-tooling.md`): the comparison `C.type? f.type = some d` of `funcCheck` (always true for the
types `checkModule?` itself looked up, so `checkModuleG?` does not decide it), the `expand?` of
every function's type (computed once per type, `ets`), and the distinctness of export names
(compared as natural numbers, `encB`, instead of byte lists).

`validG? m` is **equal to `validate? m`** (`validG?_eq`, `Silmaril.Wasm.Auto2.Valid2.Thms`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto2.Valid2

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.Valid

/-! ## Atoms beyond `sigF`: globals, `select`, memory -/

/-- The instruction type of a global, `select` or memory instruction against the stack `t`
(top first), when all its operands and results are number types; `none` otherwise. -/
def sigM (C : Context) (t : List CValType) : Instr → Option InstrType
  | .globalGet x =>
    match C.globals[x.toNat]? with
    | some ⟨_, .num a⟩ => some (.plain [] [.num a])
    | _ => none
  | .globalSet x =>
    match C.globals[x.toNat]? with
    | some ⟨.var, .num a⟩ => some (.plain [.num a] [])
    | _ => none
  | .select none =>
    match t with
    | _ :: .num b :: .num a :: _ =>
      if ntEq a b then some (.plain [.num a, .num a, .i32] [.num a]) else none
    | _ => none
  | .intLoad ty p x arg => memorySig? C (.intLoad ty p x arg)
  | .floatLoad ty x arg => memorySig? C (.floatLoad ty x arg)
  | .intStore ty p x arg => memorySig? C (.intStore ty p x arg)
  | .floatStore ty x arg => memorySig? C (.floatStore ty x arg)
  | .memorySize x => memorySig? C (.memorySize x)
  | .memoryGrow x => memorySig? C (.memoryGrow x)
  | .memoryFill x => memorySig? C (.memoryFill x)
  | .memoryCopy x y => memorySig? C (.memoryCopy x y)
  | .memoryInit x y => memorySig? C (.memoryInit x y)
  | .dataDrop y => memorySig? C (.dataDrop y)
  | _ => none

/-- One step through `sigM`: pop the parameters, push the results (stacks top first). -/
def stepM (C : Context) (t : List CValType) (i : Instr) : Option (List CValType) :=
  match sigM C t i with
  | some it =>
    if popsF it.params.reverse t && allNum it.results then
      some (it.results.reverse ++ t.drop it.params.length)
    else none
  | none => none

/-- A non-control instruction: the straight-line fragment of `Valid` (`stepF`), else `stepM`. -/
def atomG (C : Context) (t : List CValType) (i : Instr) : Option (List CValType) :=
  match stepF C.locals t i with
  | some t' => some t'
  | none => stepM C t i

/-! ## Control flow -/

/-- The result of one instruction: the next stack, a stack-polymorphic instruction (a branch,
`return`, `unreachable`), or failure. -/
inductive StepG where
  | next (t : List CValType)
  | poly
  | fail

/-- The instructions the checker treats directly, with their immediates; `other` for the rest.
Dispatching on an instruction of silmaril-lean's `Instr` (about 150 constructors) is the main
kernel cost of a step, so `classify` does it once per instruction and the checker then matches
on this small type. -/
inductive Cls where
  | lget (x : LocalIdx)
  | lset (x : LocalIdx)
  | ltee (x : LocalIdx)
  | iconst (ty : IntType) (bits : BitVec ty.width)
  | ibin (ty : IntType) (op : IntBinOp)
  | irel (ty : IntType) (op : IntRelOp)
  | itest (ty : IntType) (op : IntTestOp)
  | drop
  | gget (x : GlobalIdx)
  | gset (x : GlobalIdx)
  | block (bt : BlockType) (body : List Instr)
  | loop (bt : BlockType) (body : List Instr)
  | if_ (bt : BlockType) (b₁ b₂ : List Instr)
  | br (l : LabelIdx)
  | brIf (l : LabelIdx)
  | brTable (ls : List LabelIdx) (l : LabelIdx)
  | ret
  | unreach
  | call (x : FuncIdx)
  | other

/-- The class of an instruction (one match on `Instr`). -/
def classify : Instr → Cls
  | .localGet x => .lget x
  | .localSet x => .lset x
  | .localTee x => .ltee x
  | .intConst ty b => .iconst ty b
  | .intBinOp ty op => .ibin ty op
  | .intRelOp ty op => .irel ty op
  | .intTestOp ty op => .itest ty op
  | .drop => .drop
  | .globalGet x => .gget x
  | .globalSet x => .gset x
  | .block bt body => .block bt body
  | .loop bt body => .loop bt body
  | .if_ bt b₁ b₂ => .if_ bt b₁ b₂
  | .br l => .br l
  | .brIf l => .brIf l
  | .brTable ls l => .brTable ls l
  | .return_ => .ret
  | .unreachable => .unreach
  | .call x => .call x
  | _ => .other

/-- The instruction of a class (`other` has none; `back_classify`). -/
def Cls.back : Cls → Instr
  | .lget x => .localGet x
  | .lset x => .localSet x
  | .ltee x => .localTee x
  | .iconst ty b => .intConst ty b
  | .ibin ty op => .intBinOp ty op
  | .irel ty op => .intRelOp ty op
  | .itest ty op => .intTestOp ty op
  | .drop => .drop
  | .gget x => .globalGet x
  | .gset x => .globalSet x
  | .block bt body => .block bt body
  | .loop bt body => .loop bt body
  | .if_ bt b₁ b₂ => .if_ bt b₁ b₂
  | .br l => .br l
  | .brIf l => .brIf l
  | .brTable ls l => .brTable ls l
  | .ret => .return_
  | .unreach => .unreachable
  | .call x => .call x
  | .other => .nop

/-- Every label of `ls` has the label type `lt` (number types). -/
def labelsEq (C : Context) (lt : List CValType) : List LabelIdx → Bool
  | [] => true
  | l :: ls =>
    (match C.labels[l.toNat]? with
     | some lt' => numsEq lt lt'
     | none => false) && labelsEq C lt ls

/-- Wrap an optional stack as a step result. -/
def ofOpt : Option (List CValType) → StepG
  | some t => .next t
  | none => .fail

/-- **One instruction** `i` of class `c` (`classify i`) against the stack `t` (top first), the
bodies of blocks checked by `rec` (a sequence checker: context, stack, goal, body). The direct
cases agree with `atomG` (`Silmaril.Proofs.Wasm.Auto2.Valid2`); `other` is `atomG`. Not
recursive. -/
def instrC (rec : Context → List CValType → List CValType → List Instr → Bool) (C : Context)
    (t : List CValType) (i : Instr) : Cls → StepG
  | .lget x =>
    match C.locals[x.toNat]? with
    | some ⟨.set, .num a⟩ => .next (.num a :: t)
    | _ => .fail
  | .lset x =>
    match t, C.locals[x.toNat]? with
    | .num a :: t, some ⟨.set, .num b⟩ => if ntEq a b then .next t else .fail
    | _, _ => .fail
  | .ltee x =>
    match t, C.locals[x.toNat]? with
    | .num a :: t, some ⟨.set, .num b⟩ => if ntEq a b then .next (.num a :: t) else .fail
    | _, _ => .fail
  | .iconst ty _ => .next (.num (.int ty) :: t)
  | .ibin ty _ =>
    match t with
    | .num a :: .num b :: t =>
      if ntEq a (.int ty) && ntEq b (.int ty) then .next (.num (.int ty) :: t) else .fail
    | _ => .fail
  | .irel ty _ =>
    match t with
    | .num a :: .num b :: t =>
      if ntEq a (.int ty) && ntEq b (.int ty) then .next (.num (.int .i32) :: t) else .fail
    | _ => .fail
  | .itest ty _ =>
    match t with
    | .num a :: t => if ntEq a (.int ty) then .next (.num (.int .i32) :: t) else .fail
    | _ => .fail
  | .drop =>
    match t with
    | .num _ :: t => .next t
    | _ => .fail
  | .gget x =>
    match C.globals[x.toNat]? with
    | some ⟨_, .num a⟩ => .next (.num a :: t)
    | _ => .fail
  | .gset x =>
    match t, C.globals[x.toNat]? with
    | .num a :: t, some ⟨.var, .num b⟩ => if ntEq a b then .next t else .fail
    | _, _ => .fail
  | .block bt body =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if allNum t₁ && allNum t₂ && popsF t₁.reverse t &&
          rec (C.withLabel t₂) t₁.reverse t₂ body then
        .next (t₂.reverse ++ t.drop t₁.length)
      else .fail
    | none => .fail
  | .loop bt body =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if allNum t₁ && allNum t₂ && popsF t₁.reverse t &&
          rec (C.withLabel t₁) t₁.reverse t₂ body then
        .next (t₂.reverse ++ t.drop t₁.length)
      else .fail
    | none => .fail
  | .if_ bt b₁ b₂ =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if allNum t₁ && allNum t₂ && popsF (t₁ ++ [Ty.i32]).reverse t &&
          rec (C.withLabel t₂) t₁.reverse t₂ b₁ && rec (C.withLabel t₂) t₁.reverse t₂ b₂ then
        .next (t₂.reverse ++ t.drop (t₁ ++ [Ty.i32]).length)
      else .fail
    | none => .fail
  | .br l =>
    match C.labels[l.toNat]? with
    | some ts => if allNum ts && popsF ts.reverse t then .poly else .fail
    | none => .fail
  | .brIf l =>
    match C.labels[l.toNat]? with
    | some ts =>
      if allNum ts && popsF (ts ++ [Ty.i32]).reverse t then
        .next (ts.reverse ++ t.drop (ts ++ [Ty.i32]).length)
      else .fail
    | none => .fail
  | .brTable ls l' =>
    match C.labels[l'.toNat]? with
    | some lt =>
      if allNum lt && popsF (lt ++ [Ty.i32]).reverse t && labelsEq C lt ls then .poly else .fail
    | none => .fail
  | .ret =>
    match C.return_ with
    | some ts => if allNum ts && popsF ts.reverse t then .poly else .fail
    | none => .fail
  | .unreach => .poly
  | .call x =>
    match C.funcs[x.toNat]? with
    | some d =>
      match funcOfDef? d with
      | some (ps, rs) =>
        if allNum ps.toList && allNum rs.toList && popsF ps.toList.reverse t then
          .next (rs.toList.reverse ++ t.drop ps.toList.length)
        else .fail
      | none => .fail
    | none => .fail
  | .other => ofOpt (atomG C t i)

/-- One instruction: `instrC` on its class. -/
def instrN (rec : Context → List CValType → List CValType → List Instr → Bool) (C : Context)
    (t : List CValType) (i : Instr) : StepG :=
  instrC rec C t i (classify i)

/-- A sequence from the stack `t` (top first) to the goal `g` (bottom first), each instruction
checked by `step`, by structural recursion on the list; a stack-polymorphic instruction must end
it. -/
def runL (step : Context → List CValType → Instr → StepG) (C : Context) (g : List CValType) :
    List CValType → List Instr → Bool
  | t, [] => numsEq t.reverse g
  | t, i :: is =>
    match step C t i with
    | .next t' => runL step C g t' is
    | .poly => is.isEmpty
    | .fail => false

/-- **A sequence**, nested blocks up to depth `n` (structural recursion on `n`, then on the
list: cheaper in the kernel than recursion over the nested `Instr`). -/
def seqN : Nat → Context → List CValType → List CValType → List Instr → Bool
  | 0, _, _, _, _ => false
  | n + 1, C, t, g, is => runL (instrN (seqN n)) C g t is

/-- The nesting depth the expression checker allows (deeper bodies take the default path). -/
def depthBound : Nat := 64

/-! ## Functions -/

/-- The expression checker: from the empty stack to the results `ts` (number types). -/
def exprG (C : Context) (e : Expr) (ts : List CValType) : Bool :=
  allNum ts && seqN depthBound C [] ts e

/-- The function checker given the expansion `x` of the function's type (computed once per
type): `funcCheck` with `exprG`, without the comparison of the looked-up type. -/
def funcBodyG (C : Context) (f : Func) (x : Option CCompType) : Bool :=
  match x with
  | some (.func ps rs) =>
    match localsCheck? tyOkC C f.locals with
    | some lts => exprG (C.funcBody ps.toList rs.toList lts) f.body rs.toList
    | none => false
  | _ => false

/-- The check of function `f`: the fast path with the precomputed expansions `ets` (one per
type of the module), otherwise silmaril-lean's checker. -/
def funcG (ets : List (Option CCompType)) (C : Context) (f : Func) (d : DefType) : Bool :=
  funcBodyG C f (ets[f.type.toNat]?).join || defaultCheckers.func C f d

/-! ## Export names -/

/-- A byte list as a natural number in base 257 with digits `b + 1` (injective, `encB_inj`). -/
def encB : List UInt8 → Nat
  | [] => 0
  | b :: l => (b.toNat + 1) + 257 * encB l

/-- The export names are distinct, compared as numbers (`encB` of their UTF-8 encodings). -/
def nodupNamesN (es : List Export) : Bool :=
  pwB (fun a b => !Nat.beq a b) (es.map fun e => encB e.name.toByteArray.data.toList)

/-! ## The module -/

/-- The part checkers `checkModuleG?` is proved against: the default ones, with a function accepted
by the fast path (when its type is the one looked up) or by the default checker. -/
def checkersX : ModuleCheckers :=
  { defaultCheckers with
    func := fun C f d =>
      (decide (C.type? f.type = some d) && funcBodyG C f d.expand?) || defaultCheckers.func C f d }

/-- `checkModule? checkersX` with `funcG` (without the type comparison, with the expansions
computed once) and `nodupNamesN`. -/
def checkModuleG? (m : Module) : Option CModuleType := do
  let K := checkersX
  let dts ← K.types? {} m.types
  let xtI ← m.imports.mapM (K.import? { types := dts })
  let fdts ← m.funcs.mapM (fun f => ({ types := dts } : Context).type? f.type)
  let C' := moduleCtx' m dts xtI fdts
  let jts ← m.tags.mapM (K.tag? C')
  let gts ← K.globals? C' m.globals
  let tts ← m.tables.mapM (K.table? C')
  let rts := m.elems.map fun e => C'.closeRef e.type
  let C := moduleCtx m C' xtI jts gts tts rts
  let ets := dts.map DefType.expand?
  if m.memories.all K.mem && allPairs (funcG ets C) m.funcs fdts && m.data.all (K.data C) &&
      allPairs (fun e rt => K.elem? C e == some rt) m.elems rts && m.start.all (K.start C) then
    let xtE ← m.exports.mapM (K.export? C)
    if nodupNamesN m.exports then some ⟨xtI, xtE⟩ else none
  else none

/-- **The validator**: `checkModuleG?` when it succeeds, otherwise `validate?` (equal to
`validate?`: `validG?_eq`). -/
def validG? (m : Module) : Option CModuleType :=
  match checkModuleG? m with
  | some mt => some mt
  | none => validate? m

end Silmaril.Wasm.Auto2.Valid2
