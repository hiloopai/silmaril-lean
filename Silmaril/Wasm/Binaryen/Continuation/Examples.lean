module

public import Silmaril.Wasm.Binaryen.Continuation.Thms
import Silmaril.Wasm.Binaryen.Interp
import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
import Silmaril.Wasm.Execution.Core.Properties
import Silmaril.Wasm.Validation.Check.Validate

public section

namespace Silmaril.Wasm.Binaryen.Continuation.Examples

open Validation Execution.Core

def blockSig : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32, .i32]⟩⟩]⟩
def recordSig : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
def chooseSig : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i64, .i32, .i32]⟩⟩]⟩

private def closed (signature : RecType) : DefType :=
  (({} : Context).rollGroup signature).head!

def chooseCtx : Context :=
  ({ types := [closed blockSig, closed recordSig, closed chooseSig],
     funcs := [closed recordSig, closed chooseSig] } : Context).funcBody [.i32] [.i64, .i32, .i32] []

private theorem scalars (ctx : Context) (stack : List CValType)
    (allInt : ∀ value ∈ stack, value = .i32 ∨ value = .i64) : ResultOk ctx.toTypeCtx stack := by
  intro value mem
  rcases allInt value mem with rfl | rfl <;> exact .num _

private theorem callRecord {ctx : Context} (callee : ctx.funcs[0]? = some (closed recordSig)) :
    InstrOk ctx (.call ⟨0⟩) (.plain [.i32] [.i32]) :=
  .call (ps := .cons .i32 .nil) (rs := .cons .i32 .nil) callee (Expand.iff.mpr rfl)

private def trueBranch : Raw := .let_ (.call ⟨0⟩)
  (.let_ (.intConst .i32 5) (.let_ (.call ⟨0⟩) .done))

private def falseBranch : Raw := .let_ (.intConst .i32 7) .done

private def chooseWith (onTrue : Raw) : Raw := .let_ (.intConst .i64 99) (.let_ (.intConst .i32 4)
  (.let_ (.localGet ⟨0⟩) (.if_ (.typeIdx ⟨0⟩) onTrue falseBranch .done)))

def chooseRaw : Raw := chooseWith trueBranch

def chooseCode : Code chooseCtx [] [.i64, .i32, .i32] chooseRaw :=
  .let_ (stackPrefix := []) (by simp [ResultOk]) (.numeric (.intConst .i64 99))
    (.let_ (stackPrefix := [.i64]) (scalars _ _ (by simp)) (.numeric (.intConst .i32 4))
      (.let_ (stackPrefix := [.i64, .i32]) (scalars _ _ (by simp))
        (.variable (.localGet rfl))
        (.if_ (stackPrefix := [.i64]) (scalars _ _ (by simp))
          (.typeIdx (ps := .cons .i32 .nil) (rs := .cons .i32 (.cons .i32 .nil)) rfl (Expand.iff.mpr rfl))
          (.let_ (stackPrefix := []) (by simp [ResultOk]) (callRecord rfl)
            (.let_ (stackPrefix := [.i32]) (scalars _ _ (by simp)) (.numeric (.intConst .i32 5))
              (.let_ (stackPrefix := [.i32]) (scalars _ _ (by simp)) (callRecord rfl)
                (.done (scalars _ _ (by simp))))))
          (.let_ (stackPrefix := [.i32]) (scalars _ _ (by simp)) (.numeric (.intConst .i32 7))
            (.done (scalars _ _ (by simp [Ty.i32]))))
          (.done (scalars _ _ (by simp))))))

def folded : List BExpr := [.op (.intConst .i64 99) [], .op (.intConst .i32 4) [],
  .if_ (.typeIdx ⟨0⟩) [.op (.localGet ⟨0⟩) []]
    [.op (.call ⟨0⟩) [], .op (.call ⟨0⟩) [.op (.intConst .i32 5) []]]
    [.op (.intConst .i32 7) []]]

theorem folded_read : Raw.ofBinaryen folded = some chooseRaw :=
  Raw.read_eq_some_iff.mpr rfl

theorem folded_core : BExpr.lowerList folded = chooseCode.toCore.erase :=
  (Raw.lower_of_read folded_read).symm.trans chooseCode.core_erase.symm

private def embeddedCondition : List BExpr → Bool
  | [_, _, .if_ _ [_] _ _] => true
  | _ => false

example : folded ≠ chooseRaw.toBinaryen := by
  intro equal
  have bad : true = false := congrArg embeddedCondition equal
  cases bad

private def recordOps : List Instr :=
  [.globalGet ⟨0⟩, .intConst .i32 10, .intBinOp .i32 .mul, .localGet ⟨0⟩,
   .intBinOp .i32 .add, .globalSet ⟨0⟩, .localGet ⟨0⟩]

def fixture : Module := {
  types := [blockSig, recordSig, chooseSig]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨1⟩, [], recordOps⟩, ⟨⟨2⟩, [], chooseRaw.lower⟩]
  exports := [⟨"choose", .func ⟨1⟩⟩, ⟨"log", .global ⟨0⟩⟩] }

example : (validate? fixture).isSome = true := by decide +kernel

private def replaceChoose (ops : List Instr) : Module :=
  { fixture with funcs := [⟨⟨1⟩, [], recordOps⟩, ⟨⟨2⟩, [], ops⟩] }

example : (validate? (replaceChoose [.intConst .i64 99, .intConst .i32 4, .localGet ⟨0⟩,
    .if_ (.typeIdx ⟨0⟩) ([.drop, .call ⟨0⟩] ++ trueBranch.lower) falseBranch.lower])).isSome = false :=
  by decide +kernel

example : (validate? (replaceChoose [.intConst .i64 99, .intConst .i64 4, .localGet ⟨0⟩,
    .if_ (.typeIdx ⟨0⟩) trueBranch.lower falseBranch.lower])).isSome = false :=
  by decide +kernel

private def unreachableChoose : List Instr := [.unreachable]

example : (validate? (replaceChoose unreachableChoose)).isSome = true := by decide +kernel
example : Raw.read unreachableChoose = none := by simp [unreachableChoose, Raw.read, Op.read]

private def runChoose (mod : Module) (flag : BitVec 32) : Option (Store Empty × Flow) := do
  let (store, frame, none) ← instantiateOnce? ({} : Store Empty) mod [] | none
  let addr ← exportFunc? frame.module "choose"
  invokeRun 48 store addr [Val.i32 flag]

def observe (mod : Module) (flag : BitVec 32) : Option (BitVec 64 × BitVec 32 × BitVec 32 × BitVec 32) := do
  let (after, .normal [saved, first, second]) ← runChoose mod flag | none
  let log ← after.globals[0]?
  return (← asInt .i64 saved, ← asInt .i32 first, ← asInt .i32 second, ← asInt .i32 log.value)

example : observe fixture 0 = some (99, 4, 7, 0) := by decide +kernel
example : observe fixture 1 = some (99, 4, 5, 45) := by decide +kernel

private def trappingRaw : Raw := chooseWith (.let_ (.call ⟨0⟩) (.let_ (.intConst .i32 0)
  (.let_ (.intBinOp .i32 (.div .signed)) (.let_ (.intConst .i32 5) (.let_ (.call ⟨0⟩) .done)))))

private def trapping : Module := replaceChoose trappingRaw.lower

private def trapLog : Option (BitVec 32) := do
  let (after, .trap) ← runChoose trapping 1 | none
  let log ← after.globals[0]?
  asInt .i32 log.value

example : (validate? trapping).isSome = true := by decide +kernel
example : (Raw.read (trapping.funcs[1]?.map (·.body) |>.getD [])).isSome = true := by
  change (Raw.read trappingRaw.lower).isSome = true
  simp [trappingRaw.read_lower]
example : trapLog = some 4 := by decide +kernel

example {P : Numerics.Profile} {host : HostSemantics Empty} {store : Store Empty} {frame : Frame}
    {saved args : List Val} {sig : BlockType} {onTrue onFalse : List Instr} {next : List Admin}
    {params results : List CValType} (type : frame.module.blockType? sig = some (params, results))
    (arity : args.length = params.length) :
    Steps P host
      ⟨store, frame, vals saved ++ (vals args ++ [constI32 0, .plain (.if_ sig onTrue onFalse)]) ++ next⟩
      ⟨store, frame, vals saved ++ [.label results.length [] (vals args ++ expression onFalse)] ++ next⟩ := by
  have select : Steps P host ⟨store, frame, vals args ++ [constI32 0, .plain (.if_ sig onTrue onFalse)]⟩
      ⟨store, frame, vals args ++ [.plain (.block sig onFalse)]⟩ := by
    simpa only [List.append_nil] using Steps.ctxtInstrs (vs := args) (rest := []) Step.ifFalse.steps
  exact Steps.ctxtInstrs (select.trans (Step.block type arity).steps)

end Silmaril.Wasm.Binaryen.Continuation.Examples
