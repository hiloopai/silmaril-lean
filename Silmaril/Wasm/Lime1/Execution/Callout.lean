module

public import Silmaril.Wasm.Lime1.Execution.Step

/-!
# Suspending Lime1 execution at host calls

The Lime1 machine (`Lime1.Execution.Step`) performs a host call atomically: the rule
`invokeHost` consults the supplied relation `host fn s args (.returned s' r)` and replaces
`values args ++ [.invoke a]` by `result r` in one transition. Component-level concurrency
needs more: a blocking canonical built-in (`waitable-set.wait`, `stream.read`, …), a stackful
thread switch, or a call into another component must be able to *park* a core activation and
resume it later, possibly after other activations ran. The reference interpreter does this with
host threads (`cont_new`, `resume`, `block`, and `Thread.suspend`/`Thread.resume` in
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`); wasmtime uses fibers
(`suspend(SuspendReason)` in `crates/wasmtime/src/runtime/component/concurrent.rs` at
`a7b4f29`).

This file adds, without changing the machine, an *open* view of it:

* Generic evaluation contexts `Runtime.EvalCtx` over the shared administrative syntax
  (`hole`, a value prefix with a tail, `label`, `frame`), with `EvalCtx.plug`. They are
  parameterized by the language's value encoding (`Runtime.ValueCoding`) so that WebAssembly
  1.0 (`V1.Execution.Callout`) reuses them.
* `Runtime.Callout`: a decomposition of the code into a context and a host-call redex
  `values args ++ [.invoke function]`, carrying the store's host code identifier (`host`) and
  stored type. `Runtime.Callout.Located` says a decomposition is correct for a store and code.
* `Runtime.decomposeFrom?`: a computable, structurally recursive decomposer (it scans the
  maximal value prefix, then descends into the first label or frame).
* For Lime1: `CalloutAt cfg c`, `resume cfg c s' r` (plug `result r`, including a trap result,
  back into the context with the host's store `s'`), `Internal` (the machine with no host
  calls), the labelled `OpenStep`, and `Answer`, the atomic completion of a callout.
* An executable reference stepper `step?` for host-free steps and a fuel driver `run` that
  stops when the code is a result, at a callout, when the stepper finds no step, or when fuel is
  exhausted.

`Callout/Properties.lean` proves plug/decompose lemmas, soundness and completeness of the
decomposer (unique up to the plugged code), that callout configurations take no internal step,
the decomposition of `Step host` into internal steps and host-answered callouts, and soundness
of `step?` and `run`, and runs an instantiated module whose import is a host function.

Not modelled or claimed: the host still sees only the store and arguments (no caller frame or
state outside the store), so any component-level state lives with the caller of `run`. `step?`
makes one deterministic choice where the machine is nondeterministic (it uses the deterministic
float results and successful `memory.grow` when `Memory.grow?` succeeds); it is sound but it is
not claimed to cover every machine transition. Fuel exhaustion is not divergence. The open
machine inherits the machine's nondeterminism (NaN results, `memory.grow` failure), so
`OpenStep` is not deterministic; what is unique is the callout of a configuration (up to the
shape of its context) and the fact that a parked configuration has no host-free step.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Runtime

/-- How a language represents runtime values as administrative instructions. Both scalar
languages use their constant instructions. -/
structure ValueCoding (I : Type*) where
  encode : Value → AdminInstr I
  decode : AdminInstr I → Option Value
  decode_encode (v : Value) : decode (encode v) = some v
  encode_of_decode {x : AdminInstr I} {v : Value} : decode x = some v → encode v = x
  source_of_decode {x : AdminInstr I} {v : Value} : decode x = some v → ∃ i, x = .source i

/-- Evaluation contexts of the scalar machines. `seq` mirrors the `context` rule (a value
prefix and an arbitrary tail), `label` and `frame` mirror the rules of the same name; a frame
context records the frame that is active inside it. -/
inductive EvalCtx (I : Type*) where
  | hole
  | seq (values : List Value) (inner : EvalCtx I) (tail : List (AdminInstr I))
  | label (arity : Nat) (continuation : List I) (inner : EvalCtx I)
  | frame (arity : Nat) (locals : Frame) (inner : EvalCtx I)
  deriving Repr

namespace EvalCtx

variable {I : Type*}

def plug (encode : Value → AdminInstr I) : EvalCtx I → List (AdminInstr I) → List (AdminInstr I)
  | .hole, code => code
  | .seq vs inner tail, code => vs.map encode ++ inner.plug encode code ++ tail
  | .label n cont inner, code => [.label n cont (inner.plug encode code)]
  | .frame n fr inner, code => [.frame n fr (inner.plug encode code)]

/-- Context composition: `(outer.comp inner).plug e code = outer.plug e (inner.plug e code)`. -/
def comp : EvalCtx I → EvalCtx I → EvalCtx I
  | .hole, inner => inner
  | .seq vs outer tail, inner => .seq vs (outer.comp inner) tail
  | .label n cont outer, inner => .label n cont (outer.comp inner)
  | .frame n fr outer, inner => .frame n fr (outer.comp inner)

/-- The frame in force at the hole, given the configuration's frame. -/
def activeFrame : EvalCtx I → Frame → Frame
  | .hole, f => f
  | .seq _ inner _, f => inner.activeFrame f
  | .label _ _ inner, f => inner.activeFrame f
  | .frame _ fr inner, _ => inner.activeFrame fr

end EvalCtx

/-- A host-call redex in context. `host` is the host code identifier stored at
`function` (the `Host` of `FuncInst.host`); `type` is its stored type. -/
structure Callout (Host I : Type*) where
  context : EvalCtx I
  function : FuncAddr
  type : V1.FuncType
  host : Host
  args : List Value
  deriving Repr

namespace Callout

variable {Code Host I : Type*}

/-- The redex `values args ++ [.invoke function]`. -/
def redex (C : ValueCoding I) (c : Callout Host I) : List (AdminInstr I) :=
  c.args.map C.encode ++ [.invoke c.function]

/-- Plug replacement code (a host result) into the callout's context. -/
def fill (C : ValueCoding I) (c : Callout Host I) (code : List (AdminInstr I)) :
    List (AdminInstr I) :=
  c.context.plug C.encode code

/-- `c` is a correct decomposition of `code` under store `s`: the code is the redex in its
context, the invoked address holds a host function with the recorded type and code, and the
argument count is the parameter count (exactly the premises of `invokeHost`). -/
structure Located (C : ValueCoding I) (s : Store Code Host) (code : List (AdminInstr I))
    (c : Callout Host I) : Prop where
  plugged : code = c.fill C (c.redex C)
  found : s.funcs[c.function.value]? = some (.host c.type c.host)
  arity : c.args.length = c.type.params.length

end Callout

/-- Machines with no host behavior: host invocations have no transition at all (neither a
result nor divergence). Stepping under it is exactly the host-free part of a machine. -/
def noHostCalls {Code Host : Type*} : HostSemantics Code Host := fun _ _ _ _ => False

section Decompose

variable {Code Host I : Type*}

mutual
/-- Scan code for its host-call redex. `acc` is the value prefix already scanned (in program
order). The first non-value instruction decides: a host `invoke` with enough preceding values
is the redex; a label or frame is searched recursively; anything else is not a callout. -/
def decomposeFrom? (C : ValueCoding I) (s : Store Code Host) (acc : List Value) :
    List (AdminInstr I) → Option (Callout Host I)
  | [] => none
  | x :: tail =>
    match C.decode x with
    | some v => decomposeFrom? C s (acc ++ [v]) tail
    | none => decomposeHead? C s acc tail x
termination_by structural code => code

/-- The head case of `decomposeFrom?` for a non-value instruction `x` followed by `tail`. -/
def decomposeHead? (C : ValueCoding I) (s : Store Code Host) (acc : List Value)
    (tail : List (AdminInstr I)) : AdminInstr I → Option (Callout Host I)
  | .invoke a =>
    match s.funcs[a.value]? with
    | some (.host ft h) =>
      if ft.params.length ≤ acc.length then
        some ⟨.seq (acc.take (acc.length - ft.params.length)) .hole tail, a, ft, h,
          acc.drop (acc.length - ft.params.length)⟩
      else none
    | _ => none
  | .label n cont body =>
    (decomposeFrom? C s [] body).map fun c =>
      { c with context := .seq acc (.label n cont c.context) tail }
  | .frame n fr body =>
    (decomposeFrom? C s [] body).map fun c =>
      { c with context := .seq acc (.frame n fr c.context) tail }
  | _ => none
termination_by structural x => x
end

end Decompose

end Silmaril.Wasm.Execution.Runtime

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- The inverse of `value` on administrative instructions. -/
def asValue? : Admin → Option Value
  | .source (.intConst t b) => some ⟨.int t, b⟩
  | .source (.floatConst t b) => some ⟨.float t, b⟩
  | _ => none

/-- Lime1's value encoding: constants. -/
def coding : ValueCoding Instr where
  encode := value
  decode := asValue?
  decode_encode v := by
    rcases v with ⟨t, b⟩
    cases t <;> rfl
  encode_of_decode {x v} h := by
    rcases x with (i | _ | _ | _ | _)
    · cases i <;> simp only [asValue?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl
    all_goals simp [asValue?] at h
  source_of_decode {x v} h := by
    rcases x with (i | _ | _ | _ | _) <;> simp [asValue?] at h ⊢

/-- `c` is the host-call redex of configuration `cfg`. -/
def CalloutAt {H : Type*} (cfg : Config H) (c : Runtime.Callout H Instr) : Prop :=
  c.Located coding cfg.store cfg.code

/-- Resume a parked configuration with the host's store and result (`.trap` included). The
outer frame is kept, as in the atomic `invokeHost` rule. -/
def resume {H : Type*} (cfg : Config H) (c : Runtime.Callout H Instr) (s' : Store H)
    (r : Result) : Config H :=
  ⟨s', cfg.frame, c.fill coding (result r)⟩

/-- The executable decomposition of a configuration. -/
def decompose? {H : Type*} (cfg : Config H) : Option (Runtime.Callout H Instr) :=
  decomposeFrom? coding cfg.store [] cfg.code

/-- Host-free transitions: the existing machine with no host behavior. -/
abbrev Internal {H : Type*} : Config H → Config H → Prop := Step noHostCalls

/-- Labels of the open machine. -/
inductive Transition (H : Type*) where
  | internal (next : Config H)
  | callout (callout : Runtime.Callout H Instr)

/-- The open machine: host-free steps, and an observable stop at each callout. -/
inductive OpenStep {H : Type*} : Config H → Transition H → Prop where
  | internal {a b : Config H} (h : Internal a b) : OpenStep a (.internal b)
  | callout {a : Config H} {c : Runtime.Callout H Instr} (h : CalloutAt a c) :
      OpenStep a (.callout c)

/-- How the atomic machine completes a callout under a host relation: by resumption with the
returned store and result, or by the self-loop of `invokeHostDiverges`. -/
inductive Answer {H : Type*} (host : HostSemantics H) (cfg : Config H)
    (c : Runtime.Callout H Instr) : Config H → Prop where
  | returned (s' : Store H) (r : Result) (h : host c.host cfg.store c.args (.returned s' r)) :
      Answer host cfg c (resume cfg c s' r)
  | diverged (h : host c.host cfg.store c.args .diverged) : Answer host cfg c cfg

/-! ## Executable host-free stepping -/

/-- A typed view of a runtime value. -/
def numOf? : (t : NumType) → Value → Option (BitVec t.width)
  | .int .i32, ⟨.int .i32, b⟩ => some b
  | .int .i64, ⟨.int .i64, b⟩ => some b
  | .float .f32, ⟨.float .f32, b⟩ => some b
  | .float .f64, ⟨.float .f64, b⟩ => some b
  | _, _ => none

abbrev intOf? (t : IntType) : Value → Option (BitVec t.width) := numOf? (.int t)
abbrev floatOf? (t : FloatType) : Value → Option (BitVec t.width) := numOf? (.float t)

/-- The maximal value prefix of administrative code. -/
def splitValues : List Admin → List Value × List Admin
  | [] => ([], [])
  | x :: xs =>
    match asValue? x with
    | some v => (v :: (splitValues xs).1, (splitValues xs).2)
    | none => ([], x :: xs)

/-- One source instruction against an operand stack (`stack` has its top first). The result is
the untouched rest of the stack, the new store and frame, and the replacement code; the
consumed operands and the instruction form a redex of the machine. -/
def stepInstr? {H : Type*} (s : Store H) (f : Frame) (stack : List Value) :
    Instr → Option (List Value × Store H × Frame × List Admin)
  | .nop => some (stack, s, f, [])
  | .unreachable => some (stack, s, f, [.trap])
  | .drop =>
    match stack with
    | _ :: rest => some (rest, s, f, [])
    | [] => none
  | .select =>
    match stack with
    | c :: b :: a :: rest =>
      match intOf? .i32 c with
      | some c =>
        if a.type = b.type then
          if c = 0 then some (rest, s, f, [value b]) else some (rest, s, f, [value a])
        else none
      | none => none
    | _ => none
  | .block bt body =>
    match blockType? f.module.types bt with
    | some ft =>
      if ft.params.length ≤ stack.length then
        some (stack.drop ft.params.length, s, f, [.label ft.results.length []
          (values (stack.take ft.params.length).reverse ++ expression body)])
      else none
    | none => none
  | .loop bt body =>
    match blockType? f.module.types bt with
    | some ft =>
      if ft.params.length ≤ stack.length then
        some (stack.drop ft.params.length, s, f, [.label ft.params.length [.loop bt body]
          (values (stack.take ft.params.length).reverse ++ expression body)])
      else none
    | none => none
  | .if_ bt left right =>
    match stack with
    | c :: rest =>
      match intOf? .i32 c with
      | some c =>
        if c = 0 then some (rest, s, f, [.source (.block bt right)])
        else some (rest, s, f, [.source (.block bt left)])
      | none => none
    | [] => none
  | .br _ => none
  | .brIf l =>
    match stack with
    | c :: rest =>
      match intOf? .i32 c with
      | some c => if c = 0 then some (rest, s, f, []) else some (rest, s, f, [.source (.br l)])
      | none => none
    | [] => none
  | .brTable ls d =>
    match stack with
    | c :: rest =>
      match intOf? .i32 c with
      | some c => some (rest, s, f, [.source (.br (ls[c.toNat]?.getD d))])
      | none => none
    | [] => none
  | .call i =>
    match f.module.funcs[i.toNat]? with
    | some a => some (stack, s, f, [.invoke a])
    | none => none
  | .callIndirect i =>
    match stack with
    | c :: rest =>
      match intOf? .i32 c, frameTable s f with
      | some c, some table =>
        match table.refs[c.toNat]? with
        | none => some (rest, s, f, [.trap])
        | some none => some (rest, s, f, [.trap])
        | some (some a) =>
          match f.module.types[i.toNat]?, s.funcs[a.value]? with
          | some ft, some fn =>
            if fn.type = ft then some (rest, s, f, [.invoke a]) else some (rest, s, f, [.trap])
          | _, _ => none
      | _, _ => none
    | [] => none
  | .return_ => none
  | .localGet i =>
    match f.locals[i.toNat]? with
    | some v => some (stack, s, f, [value v])
    | none => none
  | .localSet i =>
    match stack, f.locals[i.toNat]? with
    | v :: rest, some _ => some (rest, s, {f with locals := f.locals.set i.toNat v}, [])
    | _, _ => none
  | .localTee i =>
    match stack with
    | v :: rest => some (rest, s, f, [value v, value v, .source (.localSet i)])
    | [] => none
  | .globalGet i =>
    match f.module.globals[i.toNat]? with
    | some a =>
      match s.globals[a.value]? with
      | some g => some (stack, s, f, [value g.value])
      | none => none
    | none => none
  | .globalSet i =>
    match stack with
    | v :: rest =>
      match f.module.globals[i.toNat]? with
      | some a =>
        match s.globals[a.value]? with
        | some g =>
          if g.mutability = .var then some (rest, setGlobal s a {g with value := v}, f, [])
          else none
        | none => none
      | none => none
    | [] => none
  | .intLoad t packed arg =>
    match stack with
    | c :: rest =>
      match intOf? .i32 c, frameMemory s f with
      | some c, some (_, m) =>
        match loadInt t packed m.data (effectiveAddress c arg) with
        | some v => some (rest, s, f, [value v])
        | none => some (rest, s, f, [.trap])
      | _, _ => none
    | [] => none
  | .floatLoad t arg =>
    match stack with
    | c :: rest =>
      match intOf? .i32 c, frameMemory s f with
      | some c, some (_, m) =>
        match loadFloat t m.data (effectiveAddress c arg) with
        | some v => some (rest, s, f, [value v])
        | none => some (rest, s, f, [.trap])
      | _, _ => none
    | [] => none
  | .intStore t packed arg =>
    match stack with
    | x :: c :: rest =>
      match intOf? t x, intOf? .i32 c, frameMemory s f with
      | some x, some c, some (a, m) =>
        match storeInt t packed m.data (effectiveAddress c arg) x with
        | some bytes => some (rest, setMemory s a {m with data := bytes}, f, [])
        | none => some (rest, s, f, [.trap])
      | _, _, _ => none
    | _ => none
  | .floatStore t arg =>
    match stack with
    | x :: c :: rest =>
      match floatOf? t x, intOf? .i32 c, frameMemory s f with
      | some x, some c, some (a, m) =>
        match storeFloat t m.data (effectiveAddress c arg) x with
        | some bytes => some (rest, setMemory s a {m with data := bytes}, f, [])
        | none => some (rest, s, f, [.trap])
      | _, _, _ => none
    | _ => none
  | .memorySize =>
    match frameMemory s f with
    | some (_, m) =>
      some (stack, s, f, [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))])
    | none => none
  | .memoryGrow =>
    match stack with
    | c :: rest =>
      match intOf? .i32 c, frameMemory s f with
      | some c, some (a, m) =>
        match Memory.grow? m.data m.max c.toNat with
        | some bytes => some (rest, setMemory s a {m with data := bytes}, f,
            [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))])
        | none => some (rest, setMemory s a {m with data := m.data}, f,
            [value (.int .i32 (-1))])
      | _, _ => none
    | [] => none
  | .memoryFill =>
    match stack with
    | n :: b :: d :: rest =>
      match intOf? .i32 n, intOf? .i32 b, intOf? .i32 d, frameMemory s f with
      | some n, some b, some d, some (a, m) =>
        match Memory.fill m.data d.toNat (UInt8.ofNat b.toNat) n.toNat with
        | some bytes => some (rest, setMemory s a {m with data := bytes}, f, [])
        | none => some (rest, s, f, [.trap])
      | _, _, _, _ => none
    | _ => none
  | .memoryCopy =>
    match stack with
    | n :: src :: d :: rest =>
      match intOf? .i32 n, intOf? .i32 src, intOf? .i32 d, frameMemory s f with
      | some n, some src, some d, some (a, m) =>
        match Memory.copy m.data d.toNat src.toNat n.toNat with
        | some bytes => some (rest, setMemory s a {m with data := bytes}, f, [])
        | none => some (rest, s, f, [.trap])
      | _, _, _, _ => none
    | _ => none
  | .intConst _ _ => none
  | .floatConst _ _ => none
  | .intUnOp t op =>
    match stack with
    | x :: rest =>
      match intOf? t x with
      | some x =>
        if op.toCore.valid t = true then
          some (rest, s, f, [value (.int t (Numerics.intUnOp t op.toCore x))])
        else none
      | none => none
    | [] => none
  | .intBinOp t op =>
    match stack with
    | y :: x :: rest =>
      match intOf? t x, intOf? t y with
      | some x, some y =>
        match Numerics.intBinOp t op x y with
        | .ok z => some (rest, s, f, [value (.int t z)])
        | .error _ => some (rest, s, f, [.trap])
      | _, _ => none
    | _ => none
  | .intTestOp t op =>
    match stack with
    | x :: rest =>
      match intOf? t x with
      | some x => some (rest, s, f, [value (.int .i32 (Numerics.intTestOp t op x))])
      | none => none
    | [] => none
  | .intRelOp t op =>
    match stack with
    | y :: x :: rest =>
      match intOf? t x, intOf? t y with
      | some x, some y => some (rest, s, f, [value (.int .i32 (Numerics.intRelOp t op x y))])
      | _, _ => none
    | _ => none
  | .floatUnOp t op =>
    match stack with
    | x :: rest =>
      match floatOf? t x with
      | some x => some (rest, s, f, [value (.float t (Numerics.floatUnOp t op x))])
      | none => none
    | [] => none
  | .floatBinOp t op =>
    match stack with
    | y :: x :: rest =>
      match floatOf? t x, floatOf? t y with
      | some x, some y => some (rest, s, f, [value (.float t (Numerics.floatBinOp t op x y))])
      | _, _ => none
    | _ => none
  | .floatRelOp t op =>
    match stack with
    | y :: x :: rest =>
      match floatOf? t x, floatOf? t y with
      | some x, some y =>
        some (rest, s, f, [value (.int .i32 (Numerics.floatRelOp t op x y))])
      | _, _ => none
    | _ => none
  | .convert op =>
    match stack with
    | x :: rest =>
      match numOf? op.source x with
      | some x =>
        match Numerics.convert op x with
        | .ok y => some (rest, s, f, [value ⟨op.target, y⟩])
        | .error _ => some (rest, s, f, [.trap])
      | none => none
    | [] => none

mutual
/-- Find and perform one host-free step. `stack` holds the already scanned value prefix, top
first. Host functions are never invoked (their invocation is a callout, see `decompose?`). -/
def stepFrom? {H : Type*} (s : Store H) (f : Frame) (stack : List Value) :
    List Admin → Option (Store H × Frame × List Admin)
  | [] => none
  | x :: tail =>
    match asValue? x with
    | some v => stepFrom? s f (v :: stack) tail
    | none => stepHead? s f stack tail x
termination_by structural code => code

/-- The head case of `stepFrom?` for the non-value instruction `x` followed by `tail`. -/
def stepHead? {H : Type*} (s : Store H) (f : Frame) (stack : List Value) (tail : List Admin) :
    Admin → Option (Store H × Frame × List Admin)
  | .source i =>
    (stepInstr? s f stack i).map fun (rest, s', f', after) =>
      (s', f', values rest.reverse ++ after ++ tail)
  | .invoke a =>
    match s.funcs[a.value]? with
    | some (.wasm ft module fn) =>
      if ft.params.length ≤ stack.length then
        some (s, f, values (stack.drop ft.params.length).reverse ++
          [.frame ft.results.length
            ⟨(stack.take ft.params.length).reverse ++ fn.locals.map Value.zero, module⟩
            [.label ft.results.length [] (expression fn.body)]] ++ tail)
      else none
    | _ => none
  | .trap =>
    match stack, tail with
    | [], [] => none
    | _, _ => some (s, f, [.trap])
  | .label n cont body =>
    match splitValues body with
    | (vs, []) => some (s, f, values stack.reverse ++ values vs ++ tail)
    | ([], [.trap]) => some (s, f, values stack.reverse ++ [.trap] ++ tail)
    | (vs, .source (.br l) :: _) =>
      if l.toNat = 0 then
        if n ≤ vs.length then
          some (s, f, values stack.reverse ++ (values (vs.drop (vs.length - n)) ++
            expression cont) ++ tail)
        else none
      else
        some (s, f, values stack.reverse ++ (values vs ++ [.source (.br (lowerLabel l))]) ++ tail)
    | (vs, .source .return_ :: _) =>
      some (s, f, values stack.reverse ++ (values vs ++ [.source .return_]) ++ tail)
    | _ =>
      (stepFrom? s f [] body).map fun (s', f', body') =>
        (s', f', values stack.reverse ++ [.label n cont body'] ++ tail)
  | .frame n fr body =>
    match splitValues body with
    | (vs, []) =>
      if vs.length = n then some (s, f, values stack.reverse ++ values vs ++ tail) else none
    | ([], [.trap]) => some (s, f, values stack.reverse ++ [.trap] ++ tail)
    | (vs, .source .return_ :: _) =>
      if n ≤ vs.length then
        some (s, f, values stack.reverse ++ values (vs.drop (vs.length - n)) ++ tail)
      else none
    | _ =>
      (stepFrom? s fr [] body).map fun (s', fr', body') =>
        (s', f, values stack.reverse ++ [.frame n fr' body'] ++ tail)
termination_by structural x => x
end

/-- One executable host-free step of a configuration. -/
def step? {H : Type*} (cfg : Config H) : Option (Config H) :=
  (stepFrom? cfg.store cfg.frame [] cfg.code).map fun (s, f, code) => ⟨s, f, code⟩

/-- Final code: a value sequence or a lone trap. -/
def terminal? (code : List Admin) : Option Result :=
  match code with
  | [.trap] => some .trap
  | _ =>
    match splitValues code with
    | (vs, []) => some (.values vs)
    | _ => none

/-- Why the driver stopped. -/
inductive Status (H : Type*) where
  | returned (result : Result)
  | callout (callout : Runtime.Callout H Instr)
  | stuck
  | exhausted

/-- Run host-free steps until the code is final, a callout is reached, the stepper finds no
step, or `fuel` steps have been taken. Returns the configuration reached and the reason. -/
def run {H : Type*} : Nat → Config H → Config H × Status H
  | fuel, cfg =>
    match terminal? cfg.code with
    | some r => (cfg, .returned r)
    | none =>
      match decompose? cfg with
      | some c => (cfg, .callout c)
      | none =>
        match fuel with
        | 0 => (cfg, .exhausted)
        | n + 1 =>
          match step? cfg with
          | some next => run n next
          | none => (cfg, .stuck)

end Silmaril.Wasm.Lime1.Execution
