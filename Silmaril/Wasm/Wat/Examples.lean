module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.V1.Validation.Examples
public import Silmaril.Wasm.V1.Execution.Step
public import Silmaril.Wasm.V1.Execution.Properties

/-! # Kernel-checked WAT expansion regressions -/

@[expose] public section
namespace Silmaril.Wasm.Wat.Examples

def addModule := wat1! r#"
(module
  (func $add (export "add") (param $x i32) (param $y i32) (result i32)
    (i32.add (local.get $x) (local.get $y))))
"#

example : addModule = V1.Validation.Examples.addModule := rfl
example : V1.Validation.ModuleValid addModule := V1.Validation.Examples.addModule_valid

open Silmaril.Wasm.Execution.Runtime V1.Execution

/-- The body produced by the quotation executes in the existing small-step semantics. -/
theorem add_body_executes {H : Type} (host : HostSemantics H) (store : Store H)
    (module : ModuleInst) (x y : BitVec 32) :
    let frame : Frame := ⟨[.int .i32 x, .int .i32 y], module⟩
    Steps host ⟨store, frame, expression (addModule.funcs[0]).body⟩
      ⟨store, frame, [value (.int .i32 (x + y))]⟩ := by
  intro frame
  have first := Step.context (Step.localGet (host := host) store frame ⟨0⟩ (.int .i32 x) rfl)
    [] [.source (.localGet ⟨1⟩), .source (.intBinOp .i32 .add)]
  have second := Step.context (Step.localGet (host := host) store frame ⟨1⟩ (.int .i32 y) rfl)
    [.int .i32 x] [.source (.intBinOp .i32 .add)]
  have last := Step.pure (host := host) store frame
    (PureStep.intBinary .i32 .add x y (x + y) rfl)
  exact first.steps.trans (second.steps.trans last.steps)

/-- Invoke the actual quoted function stored in a module instance, including frame return. -/
theorem add_invocation_executes {H : Type} (host : HostSemantics H) (caller : Frame)
    (x y : BitVec 32) :
    let module : ModuleInst := { types := addModule.types, funcs := [⟨0⟩] }
    let store : Store H := { funcs := [.wasm addModule.types[0] module addModule.funcs[0]] }
    Steps host ⟨store, caller, values [.int .i32 x, .int .i32 y] ++ [.invoke ⟨0⟩]⟩
      ⟨store, caller, [value (.int .i32 (x + y))]⟩ := by
  intro module store
  let inner : Frame := ⟨[.int .i32 x, .int .i32 y], module⟩
  have opened := Step.invokeWasm (host := host) store caller ⟨0⟩ addModule.types[0]
    module addModule.funcs[0] [.int .i32 x, .int .i32 y] rfl rfl (by decide)
  have body := ((add_body_executes host store module x y).label 1 []).frame 1 caller
  have closed := (Step.pure (host := host) store inner
    (PureStep.labelDone 1 [] [.int .i32 (x + y)])).frame 1 caller
  have returned := Step.pure (host := host) store caller
    (PureStep.frameDone 1 inner [.int .i32 (x + y)] rfl)
  exact opened.steps.trans (body.trans (closed.steps.trans returned.steps))

example : wat1_expr! "i32.const -0x8000_0000 i32.const 0xffff_ffff i32.sub" =
    [V1.Instr.intConst .i32 0x80000000, .intConst .i32 0xffffffff, .intBinOp .i32 .sub] := rfl

example : wat1_expr! "i64.const -9223372036854775808 i64.const 0xffff_ffff_ffff_ffff i64.const +9223372036854775807 i64.const -0" =
    [V1.Instr.intConst .i64 0x8000000000000000, .intConst .i64 0xffffffffffffffff,
      .intConst .i64 0x7fffffffffffffff, .intConst .i64 0] := rfl

example : wat1_expr! "(i32.sub (i32.const 8) (i32.mul (i32.const 2) (i32.const 3)))" =
    [V1.Instr.intConst .i32 8, .intConst .i32 2, .intConst .i32 3,
      .intBinOp .i32 .mul, .intBinOp .i32 .sub] := rfl

def boundScopes := wat1! r#"
(module
  (import "env" "f" (func $f (param i32) (result i32)))
  (global $f i32 (i32.const 9))
  (func $g (param $f i32) (local $x i64)
    block $exit
      loop $again
        local.get $f
        call $f
        global.get $f
        br_if $exit
        br $again
      end $again
    end $exit))
"#

example : (boundScopes.funcs[0]).body =
    [V1.Instr.block none [.loop none [.localGet ⟨0⟩, .call ⟨0⟩, .globalGet ⟨0⟩,
      .brIf ⟨1⟩, .br ⟨0⟩]]] := rfl

example : wat1_expr! "block $x block $x br $x end $x end $x" =
    [V1.Instr.block none [.block none [.br ⟨0⟩]]] := rfl

example : wat1_expr! "(if (result i32) (i32.const 1) (then (i32.const 2)) (else (i32.const 3)))" =
    [V1.Instr.intConst .i32 1, .if_ (some .i32) [.intConst .i32 2] [.intConst .i32 3]] := rfl

example : watLime_expr! "i32.load16_u offset=3 align=2 memory.copy i64.extend32_s" =
    [Lime1.Instr.intLoad .i32 (some (.i16, .unsigned)) ⟨1, 3⟩, .memoryCopy,
      .intUnOp .i64 (.extend .i32)] := rfl

def explicitTypes := watLime! r#"
(module
  (func $f (type $later) (param $x i32) (result i64 i32)
    (block (type $later) (local.get $x) (i64.const 1) (local.get $x)))
  (type $later (func (param i32) (result i64 i32)))
  (type $duplicate (func (param i32) (result i64 i32))))
"#

example : explicitTypes.types.length = 2 := rfl
example : (explicitTypes.funcs[0]).type = ⟨0⟩ := rfl

/-- Folded sugar is expanded before implicit signatures are allocated. -/
def indirectTypes := wat1! r#"
(module
  (table 1 funcref)
  (func (result i32)
    (call_indirect (param i32) (result i32)
      (call_indirect (param i64) (result i32) (i64.const 0) (i32.const 0))
      (i32.const 0))))
"#

example : indirectTypes.types =
    [⟨[], [.i32]⟩, ⟨[.i64], [.i32]⟩, ⟨[.i32], [.i32]⟩] := rfl
example : (indirectTypes.funcs[0]).body =
    [.intConst .i64 0, .intConst .i32 0, .callIndirect ⟨1⟩,
      .intConst .i32 0, .callIndirect ⟨2⟩] := rfl

def ifTypes := watLime! r#"
(module
  (func
    (if (result i32 i64)
      (call_indirect (param i64) (result i32) (i64.const 0) (i32.const 0))
      (then (i32.const 1) (i64.const 2)) (else (i32.const 3) (i64.const 4)))))
"#

example : ifTypes.types = [⟨[], []⟩, ⟨[.i64], [.i32]⟩, ⟨[], [.i32, .i64]⟩] := rfl

/-- Empty annotations do not manufacture type entries and shift later indices. -/
def compactBlocks := watLime! r#"
(module (func
  block (param) end
  block (param) (result i32) i32.const 1 end
  drop))
"#

example : compactBlocks.types = [⟨[], []⟩] := rfl
example : compactBlocks.funcs[0].body =
    [.block .empty [], .block (.value .i32) [.intConst .i32 1], .drop] := rfl

/-- An explicit type index remains explicit even for a compact signature. -/
example : (watLime! "(module (type (func)) (func (block (type 0))))").funcs[0].body =
    [.block (.typeIdx ⟨0⟩) []] := rfl

/-- Raw byte escapes stay bytes; names decode Unicode, while comments can nest. -/
def segments := wat1! r#"
(module (; outer (; nested ;) comment ;)
  (memory $m (export "m") 1)
  (table $t 1 funcref)
  (func $f)
  (elem $t (i32.const 0) $f)
  (data $m (i32.const 2) "\00\ff" "é") ;; bytes, not a Unicode name
  (export "\u{66}" (func $f)))
"#

example : (segments.data[0]).bytes = ⟨#[0, 255, 195, 169]⟩ := rfl
example : segments.exports = [⟨"m", .memory ⟨0⟩⟩, ⟨"f", .func ⟨0⟩⟩] := rfl

end Silmaril.Wasm.Wat.Examples
