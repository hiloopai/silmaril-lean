module

public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-!
# A structurally recursive validator for kernel evaluation

`Silmaril.Wasm.Validation.validate?` is silmaril-lean's module validator. It is generic (GC
types, subtyping, stack polymorphism, every instruction family) and costs about 5 s of kernel
time on a 60-function module of straight-line integer code (`docs/projects/wasm-binaryen-tooling.md`): each instruction goes through the oracle dispatch
(`atomicA?`/`atomicB?`), `Sub.check` on every operand and `TyOk.check` on every result, and the
distinctness of export names is decided on UTF-8 encodings through `String.decEq`.

`validK? m` is **equal to `validate? m`** (`validK?_eq`, `Silmaril.Wasm.Auto2.Valid.Thms`) and
cheap in the kernel on the modules the certificates state:

* `seqF`: a structurally recursive checker for straight-line code over numeric types (operand
  stack top first, `local.get`/`local.set`/`local.tee` of initialised numeric locals, `drop`,
  `nop` and every instruction of the numeric family), comparing number types by a direct match;
* `funcF`: silmaril-lean's `funcCheck` with `exprF` (`seqF` from the empty stack, compared to
  the declared results) as the expression checker; the module checkers `checkersK` accept a
  function when `funcF` or the default checker does;
* `checkModuleK?`: `checkModule?` with export names compared as byte lists (`nodupNames`);
* `validK? m`: `checkModuleK? checkersK m` when it succeeds, otherwise `validate? m`.

Equality: a result of `checkModuleK? checkersK` is sound (`checkModule?_sound`, through the
soundness of `funcF` against the default function checker), and `validate?` is complete
(`validate?_complete`), so both give the same module type; otherwise `validK?` is `validate?`.
Control flow (`block`, `loop`, `if`, branches, calls), memory and reference instructions take the
default path.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto2.Valid

open Silmaril.Wasm Silmaril.Wasm.Validation

/-! ## Number types and stacks -/

/-- Equality of integer types by a direct match. -/
def itEq : IntType → IntType → Bool
  | .i32, .i32 => true
  | .i64, .i64 => true
  | _, _ => false

/-- Equality of number types by a direct match. -/
def ntEq : NumType → NumType → Bool
  | .int a, .int b => itEq a b
  | .float .f32, .float .f32 => true
  | .float .f64, .float .f64 => true
  | _, _ => false

/-- `a` is the number type `b` (`false` unless both are number types). -/
def numIs : CValType → CValType → Bool
  | .num a, .num b => ntEq a b
  | _, _ => false

/-- Every entry is a number type. -/
def allNum : List CValType → Bool
  | [] => true
  | .num _ :: l => allNum l
  | _ :: _ => false

/-- `popsF ps t`: the operand stack `t` (top first) starts with `ps` (top first), all number
types. -/
def popsF : List CValType → List CValType → Bool
  | [], _ => true
  | p :: ps, a :: t => numIs a p && popsF ps t
  | _ :: _, [] => false

/-- Two lists of number types are equal. -/
def numsEq : List CValType → List CValType → Bool
  | [], [] => true
  | a :: l, b :: r => numIs a b && numsEq l r
  | _, _ => false

/-! ## Straight-line code -/

/-- The instruction type of `i` against locals `L` and the stack `t` (top first), in the
fragment; `none` outside it. -/
def sigF (L : List LocalType) (t : List CValType) : Instr → Option InstrType
  | .localGet x =>
    match L[x.toNat]? with
    | some ⟨.set, .num a⟩ => some (.plain [] [.num a])
    | _ => none
  | .localSet x =>
    match L[x.toNat]? with
    | some ⟨.set, .num a⟩ => some ⟨[.num a], [x.toNat], []⟩
    | _ => none
  | .localTee x =>
    match L[x.toNat]? with
    | some ⟨.set, .num a⟩ => some ⟨[.num a], [x.toNat], [.num a]⟩
    | _ => none
  | .drop =>
    match t with
    | .num a :: _ => some (.plain [.num a] [])
    | _ => none
  | .nop => some (.plain [] [])
  | i => numericType? i

/-- One step: pop the parameters, push the results (stacks top first). -/
def stepF (L : List LocalType) (t : List CValType) (i : Instr) : Option (List CValType) :=
  match sigF L t i with
  | some it =>
    if popsF it.params.reverse t && allNum it.results then
      some (it.results.reverse ++ t.drop it.params.length)
    else none
  | none => none

/-- **A sequence of fragment instructions**, by structural recursion on the list. -/
def seqF (L : List LocalType) : List CValType → List Instr → Option (List CValType)
  | t, [] => some t
  | t, i :: is =>
    match stepF L t i with
    | some t' => seqF L t' is
    | none => none

/-- The expression checker of the fragment: from the empty stack to the results `ts`. -/
def exprF (C : Context) (e : Expr) (ts : List CValType) : Bool :=
  allNum ts &&
    match seqF C.locals [] e with
    | some t => numsEq t.reverse ts
    | none => false

/-- The function checker of the fragment: `funcCheck` with `exprF`. -/
def funcF (C : Context) (f : Func) (d : DefType) : Bool := funcCheck tyOkC exprF C f d

/-- The default part checkers, with a function accepted by `funcF` or the default checker. -/
def checkersK : ModuleCheckers :=
  { defaultCheckers with func := fun C f d => funcF C f d || defaultCheckers.func C f d }

/-! ## Export names -/

/-- Two byte lists differ (structural recursion). -/
def bytesNe : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | a :: l, b :: r => !Nat.beq a.toNat b.toNat || bytesNe l r
  | _, _ => true

/-- Pairwise `ne` (structural recursion). -/
def pwB {α : Type} (ne : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (ne a) && pwB ne l

/-- The export names are distinct, compared as UTF-8 byte lists. -/
def nodupNames (es : List Export) : Bool :=
  pwB bytesNe (es.map fun e => e.name.toByteArray.data.toList)

/-! ## The module -/

/-- `checkModule?` with `nodupNames`. -/
def checkModuleK? (K : ModuleCheckers) (m : Module) : Option CModuleType := do
  let dts ← K.types? {} m.types
  let xtI ← m.imports.mapM (K.import? { types := dts })
  let fdts ← m.funcs.mapM (fun f => ({ types := dts } : Context).type? f.type)
  let C' := moduleCtx' m dts xtI fdts
  let jts ← m.tags.mapM (K.tag? C')
  let gts ← K.globals? C' m.globals
  let tts ← m.tables.mapM (K.table? C')
  let rts := m.elems.map fun e => C'.closeRef e.type
  let C := moduleCtx m C' xtI jts gts tts rts
  if m.memories.all K.mem && allPairs (K.func C) m.funcs fdts && m.data.all (K.data C) &&
      allPairs (fun e rt => K.elem? C e == some rt) m.elems rts && m.start.all (K.start C) then
    let xtE ← m.exports.mapM (K.export? C)
    if nodupNames m.exports then some ⟨xtI, xtE⟩ else none
  else none

/-- **The validator**: `checkModuleK? checkersK` when it succeeds, otherwise `validate?`
(equal to `validate?`: `validK?_eq`). -/
def validK? (m : Module) : Option CModuleType :=
  match checkModuleK? checkersK m with
  | some mt => some mt
  | none => validate? m

end Silmaril.Wasm.Auto2.Valid
