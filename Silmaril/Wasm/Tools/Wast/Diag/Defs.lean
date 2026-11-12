module

public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Why a module is invalid: wasmparser-style messages for the certified validator's verdict

`wasm-tools validate` and `wasm-tools wast` print wasmparser's reason for an invalid module,
and `wast` checks it against the message of every `assert_invalid` (unless
`--ignore-error-messages`). Silmaril-lean's certified validator (`Validation.validate?`,
sound for `ModuleOk`) only answers yes or no. `diagnose m`, for a module the validator
rejects, re-runs the validator's own steps (`checkModule?` of `defaultCheckers`, and inside
function bodies `checkSeq`/`checkInstr` with the same oracles `atomC`/`tyOkC`) to find the
**first failing step**, in wasmparser's section order, and names it:

* index spaces: `unknown local N`, `unknown global N`, `unknown function N`, `unknown table N`,
  `unknown memory N`, `unknown type`, `unknown label`, `unknown data segment N`,
  `unknown elem segment N`, `unknown tag N`, when the failing instruction's or definition's
  index is out of its space;
* `alignment must not be larger than natural` for a memory access whose alignment exceeds
  its natural alignment; `global is immutable: cannot modify it with \`global.set\``;
  `uninitialized local`; `invalid result arity` (`select` with several types);
  `undeclared function reference`;
* module level: `duplicate export name`, `memory size must be at most …`, `size minimum must
  not be greater than maximum`, `start function must have type [] -> []`, `constant
  expression required`;
* otherwise, in a function body or constant expression, `type mismatch` (the step is the
  operand-stack check).

Only the message is diagnostic: whether a module is valid is decided by the certified
validator alone. This is a tested heuristic over the validator's steps, not a proved
statement about wasmparser's messages (the parity tests compare them).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast.Diag

open Silmaril Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs

/-- The natural alignment exponent of a memory access, when it has one. -/
def naturalAlign : Instr → Option (Nat × Nat)
  | .intLoad t none _ a => some ((match t with | .i32 => 2 | .i64 => 3), a.align.val)
  | .intLoad _ (some (p, _)) _ a => some ((match p.width with | 8 => 0 | 16 => 1 | _ => 2), a.align.val)
  | .floatLoad t _ a => some ((match t with | .f32 => 2 | .f64 => 3), a.align.val)
  | .intStore t none _ a => some ((match t with | .i32 => 2 | .i64 => 3), a.align.val)
  | .intStore _ (some p) _ a => some ((match p.width with | 8 => 0 | 16 => 1 | _ => 2), a.align.val)
  | .floatStore t _ a => some ((match t with | .f32 => 2 | .f64 => 3), a.align.val)
  | .vecStore _ a => some (4, a.align.val)
  | .vecLoad op _ a =>
    let n := match op with
      | .full => 4 | .extend8x8 _ | .extend16x4 _ | .extend32x2 _ => 3
      | .splat p => (match p.width with | 8 => 0 | 16 => 1 | 32 => 2 | _ => 3)
      | .zero32 => 2 | .zero64 => 3
    some (n, a.align.val)
  | .vecLoadLane p _ a _ | .vecStoreLane p _ a _ =>
    some ((match p.width with | 8 => 0 | 16 => 1 | 32 => 2 | _ => 3), a.align.val)
  | _ => none

/-- The offset of a memory access (0 for other instructions). -/
def memOffset : Instr → Nat
  | .intLoad _ _ _ a | .floatLoad _ _ a | .intStore _ _ _ a | .floatStore _ _ a
  | .vecLoad _ _ a | .vecLoadLane _ _ a _ | .vecStore _ a | .vecStoreLane _ _ a _ => a.offset.val
  | _ => 0

/-- The memory an instruction uses, when it uses one. -/
def memOf : Instr → List MemIdx
  | .intLoad _ _ m _ | .floatLoad _ m _ | .intStore _ _ m _ | .floatStore _ m _
  | .vecLoad _ m _ | .vecLoadLane _ m _ _ | .vecStore m _ | .vecStoreLane _ m _ _
  | .memorySize m | .memoryGrow m | .memoryFill m | .memoryInit m _ => [m]
  | .memoryCopy a b => [a, b]
  | _ => []

def tablesOf : Instr → List TableIdx
  | .tableGet t | .tableSet t | .tableSize t | .tableGrow t | .tableFill t | .tableInit t _
  | .callIndirect t _ | .returnCallIndirect t _ => [t]
  | .tableCopy a b => [a, b]
  | _ => []

def typesOf : Instr → List TypeIdx
  | .callRef t | .returnCallRef t | .callIndirect _ t | .returnCallIndirect _ t
  | .structNew t | .structNewDefault t | .structGet _ t _ | .structSet t _
  | .arrayNew t | .arrayNewDefault t | .arrayNewFixed t _ | .arrayNewData t _
  | .arrayNewElem t _ | .arrayGet _ t | .arraySet t | .arrayFill t | .arrayInitData t _
  | .arrayInitElem t _ => [t]
  | .arrayCopy a b => [a, b]
  | .block (.typeIdx t) _ | .loop (.typeIdx t) _ | .if_ (.typeIdx t) _ _
  | .tryTable (.typeIdx t) _ _ => [t]
  | _ => []

def labelsOf : Instr → List LabelIdx
  | .br l | .brIf l | .brOnNull l | .brOnNonNull l | .brOnCast l _ _ | .brOnCastFail l _ _ => [l]
  | .brTable ls d => ls ++ [d]
  | _ => []

/-- The reason a non-block instruction fails at a context, from its immediates. -/
def instrReason (C : Context) (i : Instr) : String :=
  let bad {k : IndexKind} (xs : List (Idx k)) (n : Nat) : Option Nat :=
    (xs.find? (·.toNat ≥ n)).map (·.toNat)
  match i with
  | .localGet x | .localSet x | .localTee x =>
    if x.toNat ≥ C.locals.length then s!"unknown local {x.toNat}: local index out of bounds"
    else match i, C.locals[x.toNat]? with
      | .localGet _, some ⟨.unset, _⟩ => s!"uninitialized local: {x.toNat}"
      | _, _ => "type mismatch"
  | .globalGet x =>
    if x.toNat ≥ C.globals.length then "unknown global: global index out of bounds"
    else "type mismatch"
  | .globalSet x =>
    match C.globals[x.toNat]? with
    | none => "unknown global: global index out of bounds"
    | some g => if g.mutability == .const then
        "global is immutable: cannot modify it with `global.set`" else "type mismatch"
  | .call f | .returnCall f =>
    if f.toNat ≥ C.funcs.length then s!"unknown function {f.toNat}: function index out of bounds"
    else "type mismatch"
  | .refFunc f =>
    if f.toNat ≥ C.funcs.length then s!"unknown function {f.toNat}: function index out of bounds"
    else if !C.refs.contains f.toNat then "undeclared function reference"
    else "type mismatch"
  | .throw t =>
    if t.toNat ≥ C.tags.length then s!"unknown tag {t.toNat}: tag index out of bounds"
    else "type mismatch"
  | .dataDrop d | .memoryInit _ d | .arrayNewData _ d | .arrayInitData _ d =>
    match bad (memOf i) C.mems.length with
    | some m => s!"unknown memory {m}"
    | none =>
      if d.toNat ≥ C.datas.length then s!"unknown data segment {d.toNat}" else "type mismatch"
  | .elemDrop e | .tableInit _ e | .arrayNewElem _ e | .arrayInitElem _ e =>
    match bad (tablesOf i) C.tables.length with
    | some t => s!"unknown table {t}: table index out of bounds"
    | none =>
      if e.toNat ≥ C.elems.length then s!"unknown elem segment {e.toNat}: segment index out of bounds"
      else "type mismatch"
  | .select (some ts) => if ts.length != 1 then "invalid result arity" else "type mismatch"
  | _ =>
    match bad (labelsOf i) C.labels.length with
    | some _ => "unknown label: branch depth too large"
    | none =>
    match bad (memOf i) C.mems.length with
    | some m => s!"unknown memory {m}"
    | none =>
    match bad (tablesOf i) C.tables.length with
    | some t => s!"unknown table {t}: table index out of bounds"
    | none =>
    match bad (typesOf i) C.types.length with
    | some _ => "unknown type: type index out of bounds"
    | none =>
    match naturalAlign i with
    | some (n, a) =>
      if a > n then "invalid memop alignment: alignment must not be larger than natural"
      else if memOffset i ≥ 2 ^ 32 && (memOf i).all (fun m =>
          match C.mems[m.toNat]? with | some mt => mt.address == .i32 | none => true) then
        "offset out of range: must be <= 2**32"
      else "type mismatch"
    | none => "type mismatch"

mutual
  /-- The reason `checkInstr atomC tyOkC C S i` fails (`none` when it does not). -/
  def instrDiag (C : Context) (S : List CValType) : Instr → Option String
    | i@(.block bt body) | i@(.loop bt body) | i@(.tryTable bt _ body) =>
      match CheckInstrs.blockType? tyOkC C bt with
      | none => some (instrReason C i)
      | some (t₁, t₂) =>
        if !(resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂) then some "type mismatch"
        else
          let lab := match i with | .loop .. => t₁ | _ => t₂
          match checkSeq atomC tyOkC (C.withLabel lab) t₁ false (some t₂) body with
          | none => seqDiag (C.withLabel lab) t₁ false (some t₂) body
          | some _ =>
            if (checkInstr atomC tyOkC C S i).isSome then none
            else some "type mismatch"
    | i@(.if_ bt b₁ b₂) =>
      match CheckInstrs.blockType? tyOkC C bt with
      | none => some (instrReason C i)
      | some (t₁, t₂) =>
        if !(resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂) then some "type mismatch"
        else
          match checkSeq atomC tyOkC (C.withLabel t₂) t₁ false (some t₂) b₁ with
          | none => seqDiag (C.withLabel t₂) t₁ false (some t₂) b₁
          | some _ =>
            match checkSeq atomC tyOkC (C.withLabel t₂) t₁ false (some t₂) b₂ with
            | none => seqDiag (C.withLabel t₂) t₁ false (some t₂) b₂
            | some _ =>
              if (checkInstr atomC tyOkC C S i).isSome then none else some "type mismatch"
    | i => if (checkInstr atomC tyOkC C S i).isSome then none else some (instrReason C i)

  /-- The reason `checkSeq atomC tyOkC C s poly goal is` fails (`none` when it does not). -/
  def seqDiag (C : Context) (s : List CValType) (poly : Bool) (goal : Option (List CValType)) :
      List Instr → Option String
    | [] => if (checkSeq atomC tyOkC C s poly goal []).isSome then none else some "type mismatch"
    | i :: is =>
      let S := padStack (padFor C poly i) s
      match checkInstr atomC tyOkC C S i with
      | none => (instrDiag C S i).orElse fun _ => some (instrReason C i)
      | some (.normal n xs out) =>
        if !(localsOk C xs && resOk tyOkC C.toTypeCtx out) then some "type mismatch"
        else seqDiag (C.initLocals xs) (s.take (s.length - n) ++ out) poly goal is
      | some (.poly _) => seqDiag C [] true goal is
end

/-- The reason an expression fails `checkExpr? atomC tyOkC C e ts`. -/
def exprDiag (C : Context) (e : Expr) (ts : List CValType) : String :=
  match seqDiag C [] false (some ts) e with
  | some r => r
  | none => "type mismatch"

/-- The reason a constant expression fails. -/
def constDiag (C : Context) (e : Expr) (t : CValType) : String :=
  let constInstr : Instr → Bool
    | .intConst .. | .floatConst .. | .vecConst _ | .refNull _ | .refFunc _ | .globalGet _
    | .refI31 | .structNew _ | .structNewDefault _ | .arrayNew _ | .arrayNewDefault _
    | .arrayNewFixed .. | .anyConvertExtern | .externConvertAny => true
    | .intBinOp _ op => (match op with | .add | .sub | .mul => true | _ => false)
    | _ => false
  match e.find? (!constInstr ·) with
  | some _ => "constant expression required: non-constant operator"
  | none =>
    match e.find? (fun | .globalGet x => x.toNat ≥ C.globals.length | _ => false) with
    | some (.globalGet x) => s!"unknown global {x.toNat}: global index out of bounds"
    | _ =>
      let mutGet : Instr → Bool
        | .globalGet x => (C.globals[x.toNat]?.map (·.mutability == .var)).getD false
        | _ => false
      match e.find? mutGet with
      | some _ => "constant expression required: global.get of mutable global"
      | none =>
        match e.find? (fun | .refFunc f => f.toNat ≥ C.funcs.length | _ => false) with
        | some (.refFunc f) => s!"unknown function {f.toNat}: function index out of bounds"
        | _ => exprDiag C e [t]

/-- The reason a memory or table limit is invalid. -/
def limitsDiag (l : Limits) (bound : Nat) (what : String) : String :=
  match l.max with
  | some mx => if l.min.val > mx.val then "size minimum must not be greater than maximum"
    else s!"{what} size must be at most {bound}"
  | none => s!"{what} size must be at most {bound}"

/-- wasmparser's message for a memory whose limits exceed the address space. -/
def memSizeMsg (mt : MemoryType) : String :=
  match mt.limits.max with
  | some mx => if mt.limits.min.val > mx.val then "size minimum must not be greater than maximum"
    else if mt.address == .i32 then "memory size must be at most 0x10000 65536-byte pages"
    else "memory size must be at most 2**48 65536-byte pages"
  | none => if mt.address == .i32 then "memory size must be at most 0x10000 65536-byte pages"
    else "memory size must be at most 2**48 65536-byte pages"

/-- The reason an import is invalid. -/
def importDiag (C : Context) (im : Import) : String :=
  match im.type with
  | .func t | .tag t =>
    if t.toNat ≥ C.types.length then s!"unknown type {t.toNat}: type index out of bounds"
    else "type mismatch: invalid import type"
  | .memory mt => memSizeMsg mt
  | .table tt =>
    match tt.limits.max with
    | some mx => if tt.limits.min.val > mx.val then "size minimum must not be greater than maximum"
      else "type mismatch: invalid table type"
    | none => "type mismatch: invalid table type"
  | .global _ => "type mismatch: invalid global type"

def externDesc : ExternIdx → String × Nat
  | .func f => ("function", f.toNat) | .table t => ("table", t.toNat)
  | .memory m => ("memory", m.toNat) | .global g => ("global", g.toNat) | .tag t => ("tag", t.toNat)

/-- The first duplicate of a list of names. -/
def firstDup : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDup xs

/-- **The reason** a module the certified validator rejects is invalid (see the module
docstring); the steps of `checkModule? defaultCheckers` in wasmparser's section order. -/
def diagnose (m : Module) : String := Id.run do
  let K := defaultCheckers
  let some dts := K.types? {} m.types | return "invalid type definition"
  let C0 : Context := { types := dts }
  let some xtI := m.imports.mapM (K.import? C0) |
    return (match m.imports.find? (fun im => (K.import? C0 im).isNone) with
      | some im => importDiag C0 im
      | none => "type mismatch: invalid import type")
  let some fdts := m.funcs.mapM (fun f => C0.type? f.type) |
    return (match m.funcs.find? (fun f => (C0.type? f.type).isNone) with
      | some f => s!"unknown type {f.type.toNat}: type index out of bounds"
      | none => "unknown type: type index out of bounds")
  let C' := moduleCtx' m dts xtI fdts
  let some tts := m.tables.mapM (K.table? C') |
    return (match m.tables.find? (fun t => (K.table? C' t).isNone) with
      | some t =>
        match t.type.limits.max with
        | some mx => if t.type.limits.min.val > mx.val then
            "size minimum must not be greater than maximum" else constDiag C' t.init (C'.closeVal (.ref t.type.element))
        | none => constDiag C' t.init (C'.closeVal (.ref t.type.element))
      | none => "type mismatch")
  if let some mt := m.memories.find? (!K.mem ·) then
    return memSizeMsg mt
  let some jts := m.tags.mapM (K.tag? C') | return "type mismatch: invalid tag type"
  let some gts := K.globals? C' m.globals |
    return (match m.globals with
      | [] => "type mismatch"
      | gs =>
        -- the first global whose initializer fails, with the globals before it in scope
        let rec go (C : Context) : List Global → String
          | [] => "type mismatch"
          | g :: gs =>
            match K.globals? C [g] with
            | some [gt] => go { C with globals := C.globals ++ [gt] } gs
            | _ => constDiag C g.init (C.closeVal g.type.value)
        go C' gs)
  let rts := m.elems.map fun e => C'.closeRef e.type
  let C := moduleCtx m C' xtI jts gts tts rts
  match m.exports.find? (fun e => (K.export? C e).isNone) with
  | some e =>
    let (k, i) := externDesc e.index
    return s!"unknown {k} {i}: exported {k} index out of bounds"
  | none => pure ()
  if let some n := firstDup (m.exports.map Export.name) then
    return s!"duplicate export name `{n}` already defined"
  if let some x := m.start then
    if !K.start C x then
      return (if x.toNat ≥ C.funcs.length then
        s!"unknown function {x.toNat}: func index out of bounds"
        else "invalid start function type")
  for (e, rt) in m.elems.zip rts do
    if K.elem? C e != some rt then
      match e.mode with
      | .active t off =>
        if t.toNat ≥ C.tables.length then return s!"unknown table {t.toNat}: table index out of bounds"
        match C.tables[t.toNat]? with
        | some tt =>
          if !(constC C off (.num (.int (match tt.address with | .i32 => .i32 | .i64 => .i64)))) then
            return constDiag C off (.num (.int (match tt.address with | .i32 => .i32 | .i64 => .i64)))
        | none => pure ()
      | _ => pure ()
      for x in e.init do
        if !(constC C x (.refv rt)) then return constDiag C x (.refv rt)
      return "type mismatch"
  for (f, d) in m.funcs.zip fdts do
    if !K.func C f d then
      match d.expand? with
      | some (.func ps rs) =>
        match localsCheck? tyOkC C f.locals with
        | none => return "type mismatch: invalid local type"
        | some lts => return exprDiag (C.funcBody ps.toList rs.toList lts) f.body rs.toList
      | _ => return "type mismatch: function type expected"
  for d in m.data do
    if !K.data C d then
      match d.mode with
      | .active mi off =>
        if mi.toNat ≥ C.mems.length then return s!"unknown memory {mi.toNat}: memory index out of bounds"
        match C.mems[mi.toNat]? with
        | some mt =>
          return constDiag C off (.num (.int (match mt.address with | .i32 => .i32 | .i64 => .i64)))
        | none => pure ()
      | _ => pure ()
      return "type mismatch"
  return "type mismatch"

end Silmaril.Wasm.Tools.Wast.Diag
