module

public import Silmaril.Wasm.Perf.ValidateF.Defs

/-!
# Silmaril's Core validator on a reversed operand stack

`Perf.ValidateF` (silmaril's `validate?` with array lookups) keeps silmaril's operand stack: a
`List CValType` with its top at the **end**. At every instruction it measures the stack, drops
its bottom to reach the operands (`popOk`, `topSub`: `S.drop (S.length - n)`), rebuilds it
(`s.take (s.length - n) ++ out`, and `List.take` goes through an `Array`), and its
`checkSeq` is not tail-recursive (it appends the initialised locals and adds the dead-code
counts after the recursive call).

Here the stack is kept **reversed** (top first), so an instruction reads its operands from the
head of the list and pushes its results by consing:

* `prefixSub Δ R ps`: the first entries of `R` are subtypes of `ps` (`topSub Δ R.reverse t` is
  `prefixSub Δ R t.reverse`); `stepAR`, `stepBR`, `finishCheckR`, `checkBySigR`;
* `atomR`: silmaril's atom oracle `atomC` (families A, then B) with each family's checker on
  the reversed stack, the signature functions (`numericType?`, `memorySig?`, `refSig?`, …)
  reused as they are; `directStepGR`: `directStep atomC tyOkC` on the reversed stack;
  `directStepR`: `ValidateF.directStepF` on it;
* `checkInstrR` and `checkSeqR` (mutual): `ValidateF.checkInstrF`/`checkSeqF` with the stack
  reversed and its length carried beside it, the initialised locals accumulated (reversed) in
  an argument and the dead-code count, which no caller reads, dropped; `checkSeqR` is
  tail-recursive;
* the hot instructions (`local.get/set/tee`, `global.get`, the numeric instructions, `call`,
  `drop`, `br_if`) take a direct path (`fastR`) that allocates no `InstrType`;
* `checkExprR`, `checkModuleR`, `validateR`.

Depends on silmaril only. The component validator over `validateR` (`checkCore3R`) is
`Perf.ValidateComp`.

`Thms.lean`: `checkSeqR_eq` (the relation to `checkSeqF`), **`validateR_eq : validateR =
validate?`** (registered with `@[csimp]`).
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.ValidateR

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs
open Silmaril.Wasm.Perf.ValidateF

/-! ## Operands at the head of the reversed stack -/

/-- The first `ps.length` entries of `R` are subtypes of `ps`, pointwise. -/
def prefixSub (Δ : TypeCtx) : List CValType → List CValType → Bool
  | _, [] => true
  | x :: R, p :: ps => Δ.checkVal x p && prefixSub Δ R ps
  | [], _ :: _ => false

/-- `stepA` on the reversed stack. -/
def stepAR (Δ : TypeCtx) (R t₁ : List CValType) (xs : List Nat) (out : List CValType) :
    Option StepRes :=
  if prefixSub Δ R t₁.reverse then some (.normal t₁.length xs out) else none

/-- `stepB` on the reversed stack. -/
def stepBR (Δ : TypeCtx) (R t₁ : List CValType) : Option StepRes :=
  if prefixSub Δ R t₁.reverse then some (.poly t₁) else none

/-- `finishCheck` on the reversed stack. -/
def finishCheckR (C : Context) (R : List CValType) (it : InstrType) :
    Option (Nat × List Nat × List CValType) :=
  if prefixSub C.toTypeCtx R it.params.reverse then
    some (it.params.length, it.inits, it.results)
  else none

/-- `checkBySig` on the reversed stack. -/
def checkBySigR (Δ : TypeCtx) (sig : Option InstrType) (R : List CValType) :
    Option (Nat × List Nat × List CValType) :=
  match sig with
  | some it =>
    if prefixSub Δ R it.params.reverse then some (it.params.length, it.inits, it.results)
    else none
  | none => none

/-- `topHeap` on the reversed stack. -/
def topHeapR (R : List CValType) : Option CHeapType :=
  match R.head? with
  | some (.refv (.ref _ ht)) => some ht
  | some .botv => some .bot
  | _ => none

/-! ## The atom oracle on the reversed stack -/

/-- `selectImplType?` on the reversed stack. -/
def selectImplTypeR (R : List CValType) : Option CValType :=
  match R with
  | _ :: b :: a :: _ =>
    if a.IsNumOrVec then some a else if b.IsNumOrVec then some b else none
  | _ => none

/-- `parametricType?` on the reversed stack. -/
def parametricTypeR (tyOk : {k : TKind} → Silmaril.Wasm.Validation.Ty k → Bool) (C : Context) (R : List CValType) :
    Instr → Option InstrType
  | .nop => some (.plain [] [])
  | .drop =>
    match R.head? with
    | some t => if tyOk t then some (.plain [t] []) else none
    | none => none
  | .select (some [t]) =>
    if tyOk (C.closeVal t) then
      some (.plain [C.closeVal t, C.closeVal t, .i32] [C.closeVal t])
    else none
  | .select none =>
    match selectImplTypeR R with
    | some t => some (.plain [t, t, .i32] [t])
    | none => none
  | _ => none

/-- `atomicA?` on the reversed stack. -/
def atomicAR (tyOk : {k : TKind} → Silmaril.Wasm.Validation.Ty k → Bool) (C : Context) (R : List CValType)
    (i : Instr) : Option (Nat × List Nat × List CValType) :=
  match (parametricTypeR tyOk C R i).bind (finishCheckR C R) with
  | some r => some r
  | none =>
    match (numericType? i).bind (finishCheckR C R) with
    | some r => some r
    | none =>
      match (variableType? C i).bind (finishCheckR C R) with
      | some r => some r
      | none => (vectorType? i).bind (finishCheckR C R)

/-- `atomicB?` on the reversed stack. -/
def atomicBR (tyOk : {k : TKind} → Silmaril.Wasm.Validation.Ty k → Bool) (C : Context) (R : List CValType)
    (i : Instr) : Option (Nat × List Nat × List CValType) :=
  match checkBySigR C.toTypeCtx (tableSig? C i) R with
  | some r => some r
  | none => match checkBySigR C.toTypeCtx (memorySig? C i) R with
    | some r => some r
    | none => checkBySigR C.toTypeCtx (refSig? tyOk C R.head? i) R

/-- `atomC` on the reversed stack. -/
def atomR (C : Context) (R : List CValType) (i : Instr) :
    Option (Nat × List Nat × List CValType) :=
  atomicAR (@tyOkC C.toTypeCtx) C R i <|> atomicBR (@tyOkC C.toTypeCtx) C R i

/-- The operands `br_table` forwards: the `m` entries under the top of the reversed stack,
in stack order. -/
def brTableTs (R : List CValType) (m : Nat) : List CValType := ((R.take (m + 1)).reverse).take m

/-- `directStep atomC tyOkC` on the reversed stack. -/
def directStepGR (C : Context) (R : List CValType) (i : Instr) : Option StepRes :=
  match i with
  | .unreachable => stepBR C.toTypeCtx R []
  | .br l =>
    match C.labels[l.toNat]? with
    | some ts => stepBR C.toTypeCtx R ts
    | none => none
  | .brIf l =>
    match C.labels[l.toNat]? with
    | some ts => stepAR C.toTypeCtx R (ts ++ [.i32]) [] ts
    | none => none
  | .brTable ls l' =>
    match C.labels[l'.toNat]? with
    | some lt' =>
      let m := lt'.length
      if m + 1 ≤ R.length then
        let ts := brTableTs R m
        if resOk tyOkC C.toTypeCtx ts &&
            (l' :: ls).all (fun l => match C.labels[l.toNat]? with
              | some lt => resSub C.toTypeCtx ts lt
              | none => false) then
          stepBR C.toTypeCtx R (ts ++ [.i32])
        else none
      else none
    | none => none
  | .brOnNull l =>
    match C.labels[l.toNat]?, topHeapR R with
    | some ts, some ht =>
      if tyOkC C.toTypeCtx ht then
        stepAR C.toTypeCtx R (ts ++ [.refT true ht]) [] (ts ++ [.refT false ht])
      else none
    | _, _ => none
  | .brOnNonNull l =>
    match C.labels[l.toNat]? with
    | some lt =>
      match splitLast lt with
      | some (ts, .refv (.ref _ ht)) => stepAR C.toTypeCtx R (ts ++ [.refT true ht]) [] ts
      | _ => none
    | none => none
  | .brOnCast l rt₁ rt₂ =>
    match C.labels[l.toNat]? with
    | some lt =>
      match splitLast lt with
      | some (ts, .refv rt) =>
        if tyOkC C.toTypeCtx (C.closeRef rt₁) && tyOkC C.toTypeCtx (C.closeRef rt₂) &&
            Sub.check C.toTypeCtx (C.closeRef rt₂) (C.closeRef rt₁) &&
            Sub.check C.toTypeCtx (C.closeRef rt₂) rt then
          stepAR C.toTypeCtx R (ts ++ [.refv (C.closeRef rt₁)]) []
            (ts ++ [.refv (Silmaril.Wasm.Validation.Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂))])
        else none
      | _ => none
    | none => none
  | .brOnCastFail l rt₁ rt₂ =>
    match C.labels[l.toNat]? with
    | some lt =>
      match splitLast lt with
      | some (ts, .refv rt) =>
        if tyOkC C.toTypeCtx (C.closeRef rt₁) && tyOkC C.toTypeCtx (C.closeRef rt₂) &&
            Sub.check C.toTypeCtx (C.closeRef rt₂) (C.closeRef rt₁) &&
            Sub.check C.toTypeCtx (Silmaril.Wasm.Validation.Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂)) rt then
          stepAR C.toTypeCtx R (ts ++ [.refv (C.closeRef rt₁)]) []
            (ts ++ [.refv (C.closeRef rt₂)])
        else none
      | _ => none
    | none => none
  | .call x =>
    match C.funcs[x.toNat]? with
    | some d =>
      match funcOfDef? d with
      | some (ps, rs) => stepAR C.toTypeCtx R ps.toList [] rs.toList
      | none => none
    | none => none
  | .callRef x =>
    match C.type? x with
    | some d =>
      match funcOfDef? d with
      | some (ps, rs) =>
        stepAR C.toTypeCtx R (ps.toList ++ [.refT true (.defHeap d)]) [] rs.toList
      | none => none
    | none => none
  | .callIndirect x y =>
    match C.tables[x.toNat]?, C.type? y with
    | some tt, some d =>
      if Sub.check C.toTypeCtx tt.element Silmaril.Wasm.Validation.Ty.funcref then
        match funcOfDef? d with
        | some (ps, rs) =>
          stepAR C.toTypeCtx R (ps.toList ++ [tt.address.valType]) [] rs.toList
        | none => none
      else none
    | _, _ => none
  | .return_ =>
    match C.return_ with
    | some ts => stepBR C.toTypeCtx R ts
    | none => none
  | .returnCall x =>
    match C.funcs[x.toNat]?, C.return_ with
    | some d, some rs' =>
      match funcOfDef? d with
      | some (ps, rs) =>
        if resSub C.toTypeCtx rs.toList rs' then stepBR C.toTypeCtx R ps.toList else none
      | none => none
    | _, _ => none
  | .returnCallRef x =>
    match C.type? x, C.return_ with
    | some d, some rs' =>
      match funcOfDef? d with
      | some (ps, rs) =>
        if resSub C.toTypeCtx rs.toList rs' then
          stepBR C.toTypeCtx R (ps.toList ++ [.refT true (.defHeap d)])
        else none
      | none => none
    | _, _ => none
  | .returnCallIndirect x y =>
    match C.tables[x.toNat]?, C.type? y, C.return_ with
    | some tt, some d, some rs' =>
      if Sub.check C.toTypeCtx tt.element Silmaril.Wasm.Validation.Ty.funcref then
        match funcOfDef? d with
        | some (ps, rs) =>
          if resSub C.toTypeCtx rs.toList rs' then
            stepBR C.toTypeCtx R (ps.toList ++ [tt.address.valType])
          else none
        | none => none
      else none
    | _, _, _ => none
  | .throw x =>
    match tagParams? C x with
    | some ts => stepBR C.toTypeCtx R ts
    | none => none
  | .throwRef => stepBR C.toTypeCtx R [.refT true (.abs .exn)]
  | i =>
    match atomR C R i with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none

/-- `ValidateF.directStepF` on the reversed stack. -/
def directStepR (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context)
    (R : List CValType) (i : Instr) : Option StepRes :=
  match i with
  | .localGet x =>
    match (localType la (.localGet x)).bind (finishCheckR C R) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | .localSet x =>
    match (localType la (.localSet x)).bind (finishCheckR C R) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | .localTee x =>
    match (localType la (.localTee x)).bind (finishCheckR C R) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | .call x =>
    match fa[x.toNat]? with
    | some d =>
      match funcOfDef? d with
      | some (ps, rs) => stepAR C.toTypeCtx R ps.toList [] rs.toList
      | none => none
    | none => none
  | .returnCall x =>
    match fa[x.toNat]?, C.return_ with
    | some d, some rs' =>
      match funcOfDef? d with
      | some (ps, rs) =>
        if resSub C.toTypeCtx rs.toList rs' then stepBR C.toTypeCtx R ps.toList else none
      | none => none
    | _, _ => none
  | .refFunc x =>
    match checkBySigR C.toTypeCtx (refFuncSig fa rs x) R with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  | i => directStepGR C R i

/-! ## The hot instructions -/

/-- `Δ.checkVal t (.num n)`, without the context. -/
def subNum (t : CValType) (n : NumType) : Bool :=
  match t with
  | .num m => decide (m = n)
  | .botv => true
  | _ => false

/-- `tyOkC Δ t`, answered at once on numeric types. -/
def tyOkV (Δ : TypeCtx) (t : CValType) : Bool :=
  match t with
  | .num _ => true
  | t => tyOkC Δ t

/-- The result of `fastR`: `next xs R' len'` (the instruction initialises the locals `xs` and
leaves the reversed stack `R'`, of length `len'`), `fail` (it is rejected), `slow` (no direct
path: `checkSeqR` takes the general one). -/
inductive FStep where
  | next (xs : List Nat) (R : List CValType) (len : Nat)
  | fail
  | slow

/-- One step of `checkSeqR` on the reversed stack `R` of length `len`, outside dead code, for
the instructions with a direct path (no `InstrType` built; see `FStep`). -/
def fastR (la : Array LocalType) (C : Context) (R : List CValType)
    (len : Nat) (i : Instr) : FStep :=
  match i with
  | .localGet x =>
    match la[x.toNat]? with
    | some ⟨.set, t⟩ =>
      if tyOkV C.toTypeCtx t then .next [] (t :: R) (len + 1) else .fail
    | _ => .fail
  | .localSet x =>
    match la[x.toNat]?, R with
    | some ⟨_, t⟩, u :: R' =>
      if C.toTypeCtx.checkVal u t then .next [x.toNat] R' (len - 1) else .fail
    | _, _ => .fail
  | .localTee x =>
    match la[x.toNat]?, R with
    | some ⟨_, t⟩, u :: R' =>
      if C.toTypeCtx.checkVal u t && tyOkV C.toTypeCtx t then
        .next [x.toNat] (t :: R') len
      else .fail
    | _, _ => .fail
  | .intConst t _ => .next [] (.num (.int t) :: R) (len + 1)
  | .floatConst t _ => .next [] (.num (.float t) :: R) (len + 1)
  | .intUnOp t op =>
    if op.valid t then
      match R with
      | u :: R' => if subNum u (.int t) then .next [] (.num (.int t) :: R') (len) else .fail
      | [] => .fail
    else .slow
  | .intBinOp t _ =>
    match R with
    | u :: v :: R' =>
      if subNum v (.int t) && subNum u (.int t) then
        .next [] (.num (.int t) :: R') (len - 1)
      else .fail
    | _ => .fail
  | .intTestOp t _ =>
    match R with
    | u :: R' => if subNum u (.int t) then .next [] (.i32 :: R') (len) else .fail
    | [] => .fail
  | .intRelOp t _ =>
    match R with
    | u :: v :: R' =>
      if subNum v (.int t) && subNum u (.int t) then .next [] (.i32 :: R') (len - 1)
      else .fail
    | _ => .fail
  | .floatUnOp t _ =>
    match R with
    | u :: R' =>
      if subNum u (.float t) then .next [] (.num (.float t) :: R') (len) else .fail
    | [] => .fail
  | .floatBinOp t _ =>
    match R with
    | u :: v :: R' =>
      if subNum v (.float t) && subNum u (.float t) then
        .next [] (.num (.float t) :: R') (len - 1)
      else .fail
    | _ => .fail
  | .floatRelOp t _ =>
    match R with
    | u :: v :: R' =>
      if subNum v (.float t) && subNum u (.float t) then .next [] (.i32 :: R') (len - 1)
      else .fail
    | _ => .fail
  | .convert op =>
    match R with
    | u :: R' =>
      if subNum u op.source then .next [] (.num op.target :: R') (len) else .fail
    | [] => .fail
  | _ => .slow

/-! ## Sequences -/

mutual

/-- `ValidateF.checkInstrF` on the reversed stack `R`. -/
def checkInstrR (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context)
    (R : List CValType) : Instr → Option StepRes
  | .block bt body =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ then
        match checkSeqR fa rs la (C.withLabel t₂) t₁.reverse t₁.length false (some t₂) [] body with
        | some (_, xsb) =>
          if localsOkL la xsb then stepAR C.toTypeCtx R t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .loop bt body =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ then
        match checkSeqR fa rs la (C.withLabel t₁) t₁.reverse t₁.length false (some t₂) [] body with
        | some (_, xsb) =>
          if localsOkL la xsb then stepAR C.toTypeCtx R t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .if_ bt b₁ b₂ =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ then
        match checkSeqR fa rs la (C.withLabel t₂) t₁.reverse t₁.length false (some t₂) [] b₁,
            checkSeqR fa rs la (C.withLabel t₂) t₁.reverse t₁.length false (some t₂) [] b₂ with
        | some (_, xs₁), some (_, xs₂) =>
          if localsOkL la xs₁ && localsOkL la xs₂ then
            stepAR C.toTypeCtx R (t₁ ++ [.i32]) [] t₂
          else none
        | _, _ => none
      else none
    | none => none
  | .tryTable bt cs body =>
    match blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      if resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ && cs.all (catchOk? C) then
        match checkSeqR fa rs la (C.withLabel t₂) t₁.reverse t₁.length false (some t₂) [] body with
        | some (_, xsb) =>
          if localsOkL la xsb then stepAR C.toTypeCtx R t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .select none =>
    match stepAR C.toTypeCtx R [.botv, .botv, .i32] [] [.botv] with
    | some r => some r
    | none => directStepGR C R (.select none)
  | i => directStepR fa rs la C R i

/-- `ValidateF.checkSeqF` on the reversed stack `r` of length `len`, with the initialised
locals accumulated (reversed) in `acc`; the dead-code count is not returned. -/
def checkSeqR (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context)
    (r : List CValType) (len : Nat) (poly : Bool) (goal : Option (List CValType))
    (acc : List Nat) : List Instr → Option (List CValType × List Nat)
  | [] =>
    match goal with
    | none => some (r.reverse, acc)
    | some g =>
      if resSub C.toTypeCtx (List.replicate (if poly then g.length - len else 0) .botv ++ r.reverse) g
          && resOk tyOkC C.toTypeCtx g then
        some (g, acc)
      else none
  | i :: is =>
    match (if poly then .slow else fastR la C r len i) with
    | .next xs r' len' =>
      checkSeqR fa rs (initLocalsL la xs) C r' len' poly goal (xs.reverse ++ acc) is
    | .fail => none
    | .slow =>
      match checkInstrR fa rs la C (if poly then r ++ List.replicate (padForF fa C true i) .botv else r) i with
      | some (.normal n xs out) =>
        if localsOkL la xs && resOk tyOkC C.toTypeCtx out then
          checkSeqR fa rs (initLocalsL la xs) C (out.reverse ++ r.drop n) (len - n + out.length)
            poly goal (xs.reverse ++ acc) is
        else none
      | some (.poly _) => checkSeqR fa rs la C [] 0 true goal acc is
      | none => none

end

/-- `ValidateF.checkExprF` with `checkSeqR`. -/
def checkExprR (fa : Array DefType) (rs : Std.HashSet Nat) (C : Context) (e : Expr)
    (ts : List CValType) : Bool :=
  resOk tyOkC C.toTypeCtx ts &&
    match checkSeqR fa rs C.locals.toArray { C with locals := [] } [] 0 false (some ts) [] e with
    | some _ => true
    | none => false

/-- `ValidateF.checkModuleF` with `checkExprR` (copied verbatim otherwise). -/
def checkModuleR (m : Module) : Option CModuleType := do
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
  if m.memories.all K.mem && allPairs (funcCheck tyOkC (checkExprR fa rs) C) m.funcs fdts &&
      m.data.all (K.data C) &&
      allPairs (fun e rt => elemCheck? tyOkC (constOk (checkExprR fa rs)) C e == some rt) m.elems
        rts && m.start.all (K.start C) then
    let xtE ← m.exports.mapM (exportCheckF fa C)
    if nodupF (m.exports.map Export.name) then some ⟨xtI, xtE⟩ else none
  else none

/-- **`validate?` on a reversed operand stack** (`validateR_eq`). -/
def validateR (m : Module) : Option CModuleType := checkModuleR m

end Silmaril.Wasm.Perf.ValidateR
