module

public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Silmaril's Core validator with function lookups in an array

`Silmaril.Wasm.Validation.validate?` (run by the reference component validator
`Reference.check?` on every core module) keeps the module's functions in a list
(`Context.funcs`) and looks a function up by walking it, at every `call` and `return_call`
(`directStep`), every export (`externIdxCheck?`) and, in dead code, every padded `call`
(`funcArity`), and every `ref.func` (also a walk of `C.refs`: an element segment of `n`
functions costs `n²`). On a module with `F` functions and `c` calls that is `c · F / 2` steps: 1.8 s
on a 0.7 MB module of 5000 functions with 100 000 calls, and minutes on a real program of tens
of thousands of functions. The export names are checked distinct by `List.Nodup`
(quadratic as well).

Here those lookups read an `Array` of the same functions (`fa`, with `fa.toList = C.funcs`,
built once per module), `ref.func`'s membership test reads a hash set of `C.refs` (`rs`), and
the export names are checked with a hash set:

* `directStepF fa rs`: `directStep` with `call`, `return_call` and `ref.func` reading `fa` and
  `rs` (`refFuncSig`);
* `checkInstrF`, `checkSeqF` (mutual), `checkExprF`: `checkInstr`, `checkSeq`, `checkExpr?`
  (copied verbatim, with `atomC` and `tyOkC`) calling `directStepF fa rs` and `padForF fa`;
* `exportCheckF fa`, `nodupF`; `checkModuleF`: `checkModule? defaultCheckers` with the function
  bodies checked by `funcCheck tyOkC (checkExprF fa rs)`, the element segments by `elemCheck?`
  over `checkExprF fa rs`, the exports by `exportCheckF fa` and `nodupF`; `validateF`.

Depends on silmaril only; the component validator over `validateF` (`checkCore3F`) is
`Perf.ValidateComp`.

`Thms.lean`: `validateF_eq : validateF = validate?`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.ValidateF

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs

/-- `refSig?` at `ref.func x`, with the function looked up in `fa` and the membership of `x` in
`C.refs` read from the hash set `rs`. -/
def refFuncSig (fa : Array DefType) (rs : Std.HashSet Nat) (x : FuncIdx) : Option InstrType :=
  match fa[x.toNat]? with
  | some d => if rs.contains x.toNat then some (.plain [] [.refT false (.defHeap d)]) else none
  | none => none

/-- `variableType?` at the local instructions, with the locals read from `la`. -/
def localType (la : Array LocalType) : Instr → Option InstrType
  | .localGet x =>
    match la[x.toNat]? with
    | some ⟨.set, t⟩ => some (.plain [] [t])
    | _ => none
  | .localSet x =>
    match la[x.toNat]? with
    | some ⟨_, t⟩ => some ⟨[t], [x.toNat], []⟩
    | none => none
  | .localTee x =>
    match la[x.toNat]? with
    | some ⟨_, t⟩ => some ⟨[t], [x.toNat], [t]⟩
    | none => none
  | _ => none

/-- `localsOk` with the locals read from `la`. -/
def localsOkL (la : Array LocalType) (xs : List Nat) : Bool := xs.all fun x => (la[x]?).isSome

/-- `Context.withLocals` on the array of locals (`setIfInBounds` is `List.set`). -/
def withLocalsL : Array LocalType → List Nat → List LocalType → Array LocalType
  | la, x :: xs, lt :: lts => withLocalsL (la.setIfInBounds x lt) xs lts
  | la, _, _ => la

/-- `Context.initLocals` on the array of locals. -/
def initLocalsL (la : Array LocalType) (xs : List Nat) : Array LocalType :=
  withLocalsL la xs (xs.map fun x => ⟨.set, ((la[x]?).map LocalType.type).getD default⟩)

/-- `directStep atomC tyOkC` with the function looked up in `fa` at `call`, `return_call` and
`ref.func`, `ref.func`'s membership in `C.refs` read from `rs`, and the locals of `local.get`,
`local.set` and `local.tee` read from `la` (the context's own locals are not read). -/
def directStepF (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context)
    (S : List CValType) (i : Instr) : Option StepRes :=
  match i with
  | .localGet x =>
    match (localType la (.localGet x)).bind (finishCheck C S) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | .localSet x =>
    match (localType la (.localSet x)).bind (finishCheck C S) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | .localTee x =>
    match (localType la (.localTee x)).bind (finishCheck C S) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | .call x =>
    match fa[x.toNat]? with
    | some d =>
      match funcOfDef? d with
      | some (ps, rs) => stepA C.toTypeCtx S ps.toList [] rs.toList
      | none => none
    | none => none
  | .returnCall x =>
    match fa[x.toNat]?, C.return_ with
    | some d, some rs' =>
      match funcOfDef? d with
      | some (ps, rs) =>
        if resSub C.toTypeCtx rs.toList rs' then stepB C.toTypeCtx S ps.toList else none
      | none => none
    | _, _ => none
  | .refFunc x =>
    match checkBySig C.toTypeCtx (refFuncSig fa rs x) S with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | i => directStep atomC tyOkC C S i

/-- `padFor` with the function looked up in `fa` at `call` and `return_call`. -/
def padForF (fa : Array DefType) (C : Context) (poly : Bool) (i : Instr) : Nat :=
  if poly then
    match i with
    | .call x | .returnCall x => 8 + ((fa[x.toNat]?).map defArity).getD 0
    | i => arityBound C i
  else 0

mutual

/-- Check one instruction against the (padded) stack `S`. -/
def checkInstrF (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context) (S : List CValType) : Instr → Option StepRes
  | .block bt body =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ then
        match checkSeqF fa rs la (C.withLabel t₂) t₁ false (some t₂) body with
        | some (_, xsb, _) =>
          if localsOkL la xsb then stepA C.toTypeCtx S t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .loop bt body =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ then
        match checkSeqF fa rs la (C.withLabel t₁) t₁ false (some t₂) body with
        | some (_, xsb, _) =>
          if localsOkL la xsb then stepA C.toTypeCtx S t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .if_ bt b₁ b₂ =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ then
        match checkSeqF fa rs la (C.withLabel t₂) t₁ false (some t₂) b₁,
            checkSeqF fa rs la (C.withLabel t₂) t₁ false (some t₂) b₂ with
        | some (_, xs₁, _), some (_, xs₂, _) =>
          if localsOkL la xs₁ && localsOkL la xs₂ then
            stepA C.toTypeCtx S (t₁ ++ [.i32]) [] t₂
          else none
        | _, _ => none
      else none
    | none => none
  | .tryTable bt cs body =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ && cs.all (catchOk? C) then
        match checkSeqF fa rs la (C.withLabel t₂) t₁ false (some t₂) body with
        | some (_, xsb, _) =>
          if localsOkL la xsb then stepA C.toTypeCtx S t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .select none =>
    -- Implicit `select` on two `BOT` operands (dead code): the principal result is `BOT`.
    match stepA C.toTypeCtx S [.botv, .botv, .i32] [] [.botv] with
    | some r => some r
    | none => directStep atomC tyOkC C S (.select none)
  | i => directStepF fa rs la C S i

/-- Check a sequence against the concrete stack `s` (in polymorphic mode when
`poly`), ending at the stack `goal` when one is given. Returns the final stack
(`goal` itself when given), the initialised locals and the number of `BOT`s
consumed below `s`. -/
def checkSeqF (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context) (s : List CValType) (poly : Bool) (goal : Option (List CValType)) :
    List Instr → Option (List CValType × List Nat × Nat)
  | [] =>
    match goal with
    | none => some (s, [], 0)
    | some g =>
      if resSub C.toTypeCtx (List.replicate (endPad poly s g) .botv ++ s) g
          && resOk tyOkC C.toTypeCtx g then
        some (g, [], endPad poly s g)
      else none
  | i :: is =>
    match checkInstrF fa rs la C (padStack (padForF fa C poly i) s) i with
    | some (.normal n xs out) =>
      if localsOkL la xs && resOk tyOkC C.toTypeCtx out then
        match checkSeqF fa rs (initLocalsL la xs) C (s.take (s.length - n) ++ out) poly goal is with
        | some (out', xs', k') => some (out', xs ++ xs', k' + (n - s.length))
        | none => none
      else none
    | some (.poly t₁) =>
      match checkSeqF fa rs la C [] true goal is with
      | some (out', xs', _) => some (out', xs', t₁.length - s.length)
      | none => none
    | none => none

end


/-- `checkExpr? atomC tyOkC` with `checkSeqF`: the context's locals moved into an array (and the
context's own list emptied, as nothing reads it). -/
def checkExprF (fa : Array DefType) (rs : Std.HashSet Nat) (C : Context) (e : Expr)
    (ts : List CValType) : Bool :=
  resOk tyOkC C.toTypeCtx ts &&
    match checkSeqF fa rs C.locals.toArray { C with locals := [] } [] false (some ts) e with
    | some _ => true
    | none => false

/-- `exportCheck?` with the function looked up in `fa`. -/
def exportCheckF (fa : Array DefType) (C : Context) (e : Export) : Option CExternType :=
  match e.index with
  | .func x => fa[x.toNat]?.map .func
  | idx => externIdxCheck? C idx

/-- `l.Nodup`, with a hash set of the elements seen (`nodupF_eq`). -/
def nodupGo (seen : Std.HashSet String) : List String → Bool
  | [] => true
  | x :: xs => if seen.contains x then false else nodupGo (seen.insert x) xs

/-- `decide l.Nodup` in linear time (`nodupF_eq`). -/
def nodupF (l : List String) : Bool := nodupGo {} l

/-- `checkModule? defaultCheckers` with the function bodies and the exports checked against the
array of the module's functions, and the export names by `nodupF` (copied verbatim otherwise). -/
def checkModuleF (m : Module) : Option CModuleType := do
  let K := defaultCheckers
  let dts ← K.types? {} m.types
  let xtI ← m.imports.mapM (K.import? { types := dts })
  let fdts ← m.funcs.mapM (fun f => ({ types := dts } : Context).type? f.type)
  let C' := moduleCtx' m dts xtI fdts
  let jts ← m.tags.mapM (K.tag? C')
  let gts ← K.globals? C' m.globals
  let tts ← m.tables.mapM (K.table? C')
  let rts := m.elems.map fun e => C'.closeRef e.type
  let C := moduleCtx m C' xtI jts gts tts rts
  let fa := C.funcs.toArray
  let rs := Std.HashSet.ofList C.refs
  if m.memories.all K.mem && allPairs (funcCheck tyOkC (checkExprF fa rs) C) m.funcs fdts &&
      m.data.all (K.data C) &&
      allPairs (fun e rt => elemCheck? tyOkC (constOk (checkExprF fa rs)) C e == some rt) m.elems
        rts && m.start.all (K.start C) then
    let xtE ← m.exports.mapM (exportCheckF fa C)
    if nodupF (m.exports.map Export.name) then some ⟨xtI, xtE⟩ else none
  else none

/-- **`validate?` with array lookups** (`validateF_eq`). -/
def validateF (m : Module) : Option CModuleType := checkModuleF m

end Silmaril.Wasm.Perf.ValidateF
