module

public import Silmaril.Wasm.Lime1.Execution.Pure
public import Silmaril.Foundations.InfiniteTrace

/-!
# Lime1 reduction

The transition relation covers source instructions, administrative calls,
labels and frames. Stores and local frames are threaded explicitly. An invalid
runtime index is stuck, while specified arithmetic, indirect-call and memory
faults reduce to `trap`. Host behavior is a supplied relation; its typing and
store-extension contract is independent of the reduction rules. Function invocation
fuses frame creation with opening its initial administrative label; this machine
is not claimed to match each normative administrative step one-for-one.

A host divergence outcome gives an infinite invocation reduction. Together
with permitted NaN results and memory-growth failure this makes the semantics
intentionally nondeterministic.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

inductive Step {H : Type*} (host : HostSemantics H) : Config H → Config H → Prop where
  | pure (s : Store H) (f : Frame) {before after : List Admin}
      (h : PureStep f.module.types before after) : Step host ⟨s, f, before⟩ ⟨s, f, after⟩
  | context {s s' : Store H} {f f' : Frame} {before after : List Admin}
      (h : Step host ⟨s, f, before⟩ ⟨s', f', after⟩) (vs : List Value) (tail : List Admin) :
      Step host ⟨s, f, values vs ++ before ++ tail⟩ ⟨s', f', values vs ++ after ++ tail⟩
  | label {s s' : Store H} {f f' : Frame} {before after : List Admin}
      (h : Step host ⟨s, f, before⟩ ⟨s', f', after⟩) (n : Nat) (cont : Expr) :
      Step host ⟨s, f, [.label n cont before]⟩ ⟨s', f', [.label n cont after]⟩
  | frame {s s' : Store H} {inner inner' : Frame} {before after : List Admin}
      (h : Step host ⟨s, inner, before⟩ ⟨s', inner', after⟩) (n : Nat) (outer : Frame) :
      Step host ⟨s, outer, [.frame n inner before]⟩ ⟨s', outer, [.frame n inner' after]⟩
  | localGet (s : Store H) (f : Frame) (i : LocalIdx) (v : Value)
      (found : f.locals[i.toNat]? = some v) :
      Step host ⟨s, f, [.source (.localGet i)]⟩ ⟨s, f, [value v]⟩
  | localSet (s : Store H) (f : Frame) (i : LocalIdx) (v old : Value)
      (found : f.locals[i.toNat]? = some old) :
      Step host ⟨s, f, [value v, .source (.localSet i)]⟩
        ⟨s, {f with locals := f.locals.set i.toNat v}, []⟩
  | globalGet (s : Store H) (f : Frame) (i : GlobalIdx) (a : GlobalAddr) (g : GlobalInst)
      (index : f.module.globals[i.toNat]? = some a) (found : s.globals[a.value]? = some g) :
      Step host ⟨s, f, [.source (.globalGet i)]⟩ ⟨s, f, [value g.value]⟩
  | globalSet (s : Store H) (f : Frame) (i : GlobalIdx) (a : GlobalAddr) (g : GlobalInst)
      (v : Value) (index : f.module.globals[i.toNat]? = some a)
      (found : s.globals[a.value]? = some g) (mutable : g.mutability = .var) :
      Step host ⟨s, f, [value v, .source (.globalSet i)]⟩
        ⟨setGlobal s a {g with value := v}, f, []⟩
  | call (s : Store H) (f : Frame) (i : FuncIdx) (a : FuncAddr)
      (found : f.module.funcs[i.toNat]? = some a) :
      Step host ⟨s, f, [.source (.call i)]⟩ ⟨s, f, [.invoke a]⟩
  | callIndirect (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
      (table : TableInst) (a : FuncAddr) (fn : FuncInst Func H) (ft : FuncType)
      (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
      (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
      (typeMatch : fn.type = ft) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.invoke a]⟩
  | callIndirectBounds (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
      (table : TableInst) (tableFound : frameTable s f = some table)
      (outOfBounds : table.refs[c.toNat]? = none) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  | callIndirectNull (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
      (table : TableInst) (tableFound : frameTable s f = some table)
      (null : table.refs[c.toNat]? = some none) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  | callIndirectType (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
      (table : TableInst) (a : FuncAddr) (fn : FuncInst Func H) (ft : FuncType)
      (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
      (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
      (typeMismatch : fn.type ≠ ft) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  | invokeWasm (s : Store H) (f : Frame) (a : FuncAddr) (ft : FuncType)
      (module : ModuleInst) (fn : Func) (args : List Value)
      (found : s.funcs[a.value]? = some (.wasm ft module fn))
      (arity : args.length = ft.params.length) :
      Step host ⟨s, f, values args ++ [.invoke a]⟩
        ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Value.zero, module⟩
          [.label ft.results.length [] (expression fn.body)]]⟩
  | invokeHost (s s' : Store H) (f : Frame) (a : FuncAddr) (ft : FuncType)
      (fn : H) (args : List Value) (r : Result)
      (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
      (behavior : host fn s args (.returned s' r)) :
      Step host ⟨s, f, values args ++ [.invoke a]⟩ ⟨s', f, result r⟩
  | invokeHostDiverges (s : Store H) (f : Frame) (a : FuncAddr) (ft : FuncType)
      (fn : H) (args : List Value)
      (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
      (behavior : host fn s args .diverged) :
      Step host ⟨s, f, values args ++ [.invoke a]⟩ ⟨s, f, values args ++ [.invoke a]⟩
  | intLoad (s : Store H) (f : Frame) (t : IntType) (packed : Option (PackSize × Signedness))
      (arg : MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Value)
      (memory : frameMemory s f = some (a, m))
      (loaded : loadInt t packed m.data (effectiveAddress c arg) = some v) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [value v]⟩
  | intLoadTrap (s : Store H) (f : Frame) (t : IntType) (packed : Option (PackSize × Signedness))
      (arg : MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m))
      (loaded : loadInt t packed m.data (effectiveAddress c arg) = none) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [.trap]⟩
  | floatLoad (s : Store H) (f : Frame) (t : FloatType) (arg : MemArg) (c : BitVec 32)
      (a : MemAddr) (m : MemInst) (v : Value) (memory : frameMemory s f = some (a, m))
      (loaded : loadFloat t m.data (effectiveAddress c arg) = some v) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [value v]⟩
  | floatLoadTrap (s : Store H) (f : Frame) (t : FloatType) (arg : MemArg) (c : BitVec 32)
      (a : MemAddr) (m : MemInst) (memory : frameMemory s f = some (a, m))
      (loaded : loadFloat t m.data (effectiveAddress c arg) = none) :
      Step host ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [.trap]⟩
  | intStore (s : Store H) (f : Frame) (t : IntType) (packed : Option PackSize)
      (arg : MemArg) (c : BitVec 32) (x : BitVec t.width) (a : MemAddr) (m : MemInst)
      (bytes : Memory.Bytes) (memory : frameMemory s f = some (a, m))
      (stored : storeInt t packed m.data (effectiveAddress c arg) x = some bytes) :
      Step host ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t packed arg)]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  | intStoreTrap (s : Store H) (f : Frame) (t : IntType) (packed : Option PackSize)
      (arg : MemArg) (c : BitVec 32) (x : BitVec t.width) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m))
      (stored : storeInt t packed m.data (effectiveAddress c arg) x = none) :
      Step host ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t packed arg)]⟩
        ⟨s, f, [.trap]⟩
  | floatStore (s : Store H) (f : Frame) (t : FloatType) (arg : MemArg) (c : BitVec 32)
      (x : BitVec t.width) (a : MemAddr) (m : MemInst) (bytes : Memory.Bytes)
      (memory : frameMemory s f = some (a, m))
      (stored : storeFloat t m.data (effectiveAddress c arg) x = some bytes) :
      Step host ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  | floatStoreTrap (s : Store H) (f : Frame) (t : FloatType) (arg : MemArg) (c : BitVec 32)
      (x : BitVec t.width) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m))
      (stored : storeFloat t m.data (effectiveAddress c arg) x = none) :
      Step host ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩
        ⟨s, f, [.trap]⟩
  | memorySize (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m)) :
      Step host ⟨s, f, [.source .memorySize]⟩
        ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩
  | memoryGrow (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst) (c r : BitVec 32)
      (bytes : Memory.Bytes) (memory : frameMemory s f = some (a, m))
      (grown : Memory.Grow m.data m.max c.toNat bytes r) :
      Step host ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
        ⟨setMemory s a {m with data := bytes}, f, [value (.int .i32 r)]⟩
  | memoryCopy (s : Store H) (f : Frame) (destination source count : BitVec 32)
      (a : MemAddr) (m : MemInst) (bytes : Memory.Bytes)
      (memory : frameMemory s f = some (a, m))
      (copied : Memory.copy m.data destination.toNat source.toNat count.toNat = some bytes) :
      Step host ⟨s, f, [value (.int .i32 destination), value (.int .i32 source),
        value (.int .i32 count), .source .memoryCopy]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  | memoryCopyTrap (s : Store H) (f : Frame) (destination source count : BitVec 32)
      (a : MemAddr) (m : MemInst) (memory : frameMemory s f = some (a, m))
      (copied : Memory.copy m.data destination.toNat source.toNat count.toNat = none) :
      Step host ⟨s, f, [value (.int .i32 destination), value (.int .i32 source),
        value (.int .i32 count), .source .memoryCopy]⟩ ⟨s, f, [.trap]⟩
  | memoryFill (s : Store H) (f : Frame) (destination byte count : BitVec 32)
      (a : MemAddr) (m : MemInst) (bytes : Memory.Bytes)
      (memory : frameMemory s f = some (a, m))
      (filled : Memory.fill m.data destination.toNat (UInt8.ofNat byte.toNat) count.toNat = some bytes) :
      Step host ⟨s, f, [value (.int .i32 destination), value (.int .i32 byte),
        value (.int .i32 count), .source .memoryFill]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  | memoryFillTrap (s : Store H) (f : Frame) (destination byte count : BitVec 32)
      (a : MemAddr) (m : MemInst) (memory : frameMemory s f = some (a, m))
      (filled : Memory.fill m.data destination.toNat (UInt8.ofNat byte.toNat) count.toNat = none) :
      Step host ⟨s, f, [value (.int .i32 destination), value (.int .i32 byte),
        value (.int .i32 count), .source .memoryFill]⟩ ⟨s, f, [.trap]⟩

abbrev Steps {H : Type*} (host : HostSemantics H) := Relation.ReflTransGen (Step host)

/-- An infinite reduction trace; finite stuckness is not divergence. -/
def Diverges {H : Type*} (host : HostSemantics H) (initial : Config H) : Prop :=
  InfiniteTrace (Step host) initial

theorem Step.steps {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) : Steps host a b := Relation.ReflTransGen.single h

end Silmaril.Wasm.Lime1.Execution
