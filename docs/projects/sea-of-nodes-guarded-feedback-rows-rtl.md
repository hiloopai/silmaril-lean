# Guarded feedback rows in RTL and explicit Φ

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms`.
`checkPlan` admits a typed i64 bank at a supplied width. Entry and copy
indices are zero-based and checked against the full bank. Each computation
reads two old bank slots and writes a fresh temporary. Destinations are
distinct. The guard names one computed producer and its destination.
The checker requires them to agree. The guard compares that producer
with `eq`, `ne`, or signed `slt` against `limit` by default. Set
`guardRhs := some (.arg slot)` to read an old bank slot, or
`guardRhs := some (.output producer 0)` to read a distinct row result.
Exit reads the old `exitSlot` by default. Set
`exitOrigin := some (.output producer 0)` to return a computed result
from that activation. The checker requires that producer's destination
to be `exitSlot`. Positional `Spec` literals take `exitOrigin` followed
by `guardRhs`.
[Guarded pair][pair] · [Row compiler][row] · [Explicit Φ baseline][phi]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def crossed : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 0]
  updates := [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩]
  guardOrigin := .output 1 0
  guardDestination := 0
  comparison := .ne
  limit := 14
  exitSlot := 2

def sampleInput : WordTuple 3 := .cons (5 : Word) (.cons (2 : Word) (.cons (20 : Word) .nil))

#eval do
  let plan ← checkPlan 3 crossed
  let (rtl, ssa) ← lowerChecked 3 crossed
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let observe (backedges : Nat) :=
    let machine := (rtl.runMain (plan.rtlFuel backedges) 0 (words sampleInput) mem).returnedValues?
    let typed := (Generic.Fuel.run model (inputEnv model sampleInput) (backedges + 1) ssa).bind fun (_, packet) =>
      (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
    (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)
  pure (observe 1, observe 2)
-- some ((none, none), some [7], some 7)
```

The first two activations feed back `(7, 3, 5)` and `(10, 4, 7)`.
The guard's addition reads old slot 1 even though the subtraction
replaces it, and slot 2 copies old slot 0. The next comparison sees 14
and exit projects the old slot 2, which is 7. Changing the guard origin
to `.output 0 0` is refused because producer 0 writes slot 1.
[Activation regression][regression] · [Whole-loop regression][fuel-regression]

`activation_agrees` proves the guard choice and complete feedback tuple
or exit projection. `incoming_alignment` identifies the actual entry
and feedback branches in either predecessor order. The two orders
recover the same branch terms of the emitted CFG. [Activation theorems][thms]

For a row with `k` computations, `activationSteps` is `k + 3`
with a fixed limit and `k + 2` with an old-bank or computed operand.
Both execute the row, comparison and branch. The fixed limit adds one literal.
A return after `b` backedges needs exactly
`activationSteps * (b + 1) + 2` RTL steps including entry and return,
and `b + 1` λSSA visits. The fixed-limit example needs 17 RTL steps
and 3 λSSA visits.
`runMain_fuel_iff` gives the threshold at arbitrary RTL fuel.
`bounded_returns_iff` and `bounded_absence_iff` compare observation at
the matched budgets. `returns_iff` relates the checked targets' finite
returns with the entire final memory equal to the initial memory.
The proofs cover the current pure single-header i64 bank profile.
[Whole-loop theorems][fuel-thms]

## Return a computed row value

A native loop can name a header producer in its result wire, as the
source swap example does. This add/sub row selects the exit producer
independently of the guard producer. The selection uses the existing
exit successor and introduces no additional machine step.
[Native result wire][native-result]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def subtractOnExit : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 2]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .ne
  limit := 3
  exitSlot := 2
  exitOrigin := some (.output 1 0)

def observe (spec : Spec) (input : WordTuple 3) := do
  let plan ← checkPlan 3 spec
  let (rtl, ssa) ← lowerChecked 3 spec
  let initial := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain (plan.rtlFuel 2) 0 (words input) initial).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 3 ssa).bind
    fun (_, packet) => (Generic.Fuel.decodeArgs model [word] packet).map fun fields =>
      Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)

#eval observe subtractOnExit (.cons (0 : Word) (.cons (1 : Word) (.cons (10 : Word) .nil)))
-- some (some [7], some 7)

#eval observe { subtractOnExit with limit := 42, guardRhs := some (.arg 2) }
  (.cons (0 : Word) (.cons (1 : Word) (.cons (5 : Word) .nil)))
-- some (some [2], some 2)

#eval observe { subtractOnExit with guardRhs := some (.output 1 0) }
  (.cons (0 : Word) (.cons (1 : Word) (.cons (6 : Word) .nil)))
-- some (some [3], some 3)

def signedCrossing : Spec :=
  { subtractOnExit with
    updates := [⟨.add, 0, 0, 1⟩, ⟨.add, 2, 2, 1⟩]
    comparison := .slt
    guardRhs := some (.output 1 0) }

#eval observe signedCrossing (.cons (-2 : Word) (.cons (1 : Word) (.cons (0x7fff_ffff_ffff_fffe : Word) .nil)))
-- some (some [9223372036854775808], some 9223372036854775808)
```

At `(0, 1, 10)` two backedges lead to old bank `(2, 1, 8)`.
The exit guard sees 3 and returns the freshly computed `8 - 1 = 7`.
An old-slot exit would return 8. With stride zero and counter 1 a
fixed-point proof excludes every finite return in both targets.
Selecting guard producer 0 as the exit origin while retaining
`exitSlot := 2` is refused. `no_finite_return_iff` in
`Rows.Institution.Thms` applies to either exit selection.
[Computed exit regression][computed-regression] · [Observation laws][institution-thms]

## Compare with an old bank slot

The source swap loop's comparison with a runtime input motivates this
two-operand guard. An old bank slot can supply the right operand of
any supported comparison. In the second call above, two backedges lead
to `(2, 1, 3)`. The guard compares the next counter 3 with old slot 2's
value 3. The subtraction has already computed 2 for that slot, and
the exit passes that computed word. The return takes 14 RTL steps and
3 λSSA visits. The checker rejects an out-of-range `.arg` slot for
`guardRhs`. Reindexing the external inputs leaves that bank-local
operand in place. [Native loop example][native-result] · [Operand regressions][operand-regression]

## Compare two row results

Simple's chapter 13 loop regression has a continuation branch that
compares two arithmetic expressions. The last call above uses the same
operand shape with a single `ne` guard over an add and a subtraction.
Both producers read the old bank. At `(2, 1, 4)` the computed words
are both 3, so the loop exits. Using the old value 4 as the RHS would
take the backedge. `guard_compare_computed` identifies the two actual
RTL producer registers. The regression also inspects the emitted λSSA
operands and branch packets, then checks both returns under an external
input swap. A producer outside the update row, a port other than 0,
and reuse of the left producer are refused. [Simple loop branch][simple-two-expressions] · [Operand regressions][operand-regression]

## Signed less-than

Simple's pinned `BoolNode.LT` compares signed Java `long` operands.
For `comparison := .slt`, RTL emits `cmp lts lhs rhs` and λSSA
interprets the typed `WordOp.slt` in the native word model. In
`signedCrossing`, the first comparison is `-1 < 2^63 - 1` and takes
feedback. The next RHS wraps to `-2^63`, so `0 < -2^63` is false and
the computed RHS is returned. Unsigned order or swapped operands
would exit on the first visit. The regression checks both actual
branch packets, the whole memory, and no finite return for a zero
stride. It also checks re-emission after swapping inputs 0 and 1
using `Rows.Reindex.Thms`.
[Simple comparison class][simple-lt] · [Signed guard regression][signed-regression]

## Check a native signed loop

`Rows.Native.lowerChecked` takes a typed `BankGraph` directly.
It reconstructs the guarded row from the native header and its entry
and feedback columns, then checks the reconstructed opcodes and typed
wire origins against the graph. `Native.recognize_sound` proves the
checked plan reconstructs that graph, including the predicate and
exit projection. `Native.activation_agrees` identifies the taken
packet in both emitted targets. The two return iff laws preserve the
whole memory, and `Native.no_finite_return_iff` handles undefinedness
without choosing a common fuel.

The admitted shape has an empty preheader and equal input and bank widths.
Each wrapping add/sub reads the old bank and supplies exactly one feedback
destination. Remaining feedback slots copy old words. The final signed
comparison takes a computed result on the left and either a distinct row
result or a latched bank slot on the right. The recognizer translates old
header argument positions to bank-local slots. Captured inputs and literal
operands are outside this profile. The true successor feeds back the whole
tuple and the false successor returns an old field or a row result, as
specified by the native `Loop.Graph`.

This example isolates Simple chapter 13's
`(arg + 79) < (32 - arg)` continuation test. The example passes
the offsets as inputs and exposes the computed RHS on exit.
[Simple loop branch][simple-two-expressions] · [Native regression][native-guard-regression]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.RVSDG (Origin)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def oldPort (slot : Fin 4) := suffixPort (wordPorts 4) (argumentPort 4 slot)

def source (rhs : Origin (bankArgs 4) [[wordPort], [wordPort]] wordPort) :
    BankGraph 4 [[wordPort], [wordPort], [.value .predicate]] where
  preheader := .nil
  header :=
    .cons .add (.cons (.arg (oldPort 0)) (.cons (.arg (oldPort 1)) .nil))
      (.cons .sub (.cons (.arg (oldPort 2)) (.cons (.arg (oldPort 0)) .nil))
        (.cons .slt (.cons (.output (0 : Fin 2) .head) (.cons rhs .nil)) .nil))
  phiInputs
    | .entry => .cons (.arg (argumentPort 4 0)) (.cons (.arg (argumentPort 4 2))
        (.cons (.arg (argumentPort 4 1)) (.cons (.arg (argumentPort 4 3)) .nil)))
    | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.arg (oldPort 1))
        (.cons (.arg (oldPort 2)) (.cons (.output (1 : Fin 3) .head) .nil)))
  predicate := .output (2 : Fin 3) .head
  result := .output (1 : Fin 3) .head

def observeNative (rhs : Origin (bankArgs 4) [[wordPort], [wordPort]] wordPort)
    (rtlFuel lambdaFuel : Nat) := do
  let (rtl, ssa) ← Native.lowerChecked (source rhs)
  let input : WordTuple 4 := .cons (-80 : Word) (.cons (32 : Word) (.cons (79 : Word) (.cons (0 : Word) .nil)))
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain rtlFuel 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) lambdaFuel ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)

#eval observeNative (.output (1 : Fin 2) .head) 10 2
-- some (some [33], some 33)

#eval observeNative (.arg (oldPort 3)) 14 3
-- some (some [-46], some (-46))
```

The first guard compares `-1 < 112` and feeds back
`(-1, 79, 32, 112)`. Both unsigned and reversed comparison would
return 112 there. The next guard compares `78 < 33`, so both targets
return the fresh RHS 33. The checker refuses changing the add's left
operand to the captured input, which would stop reading the latched value.

With the old bank RHS, the second guard compares 78 with the latched 112
and takes another backedge. The fresh RHS 33 would exit at that point.
Both targets return the computed word `-46` on the third visit. Swapping
the operands puts the old slot on the left and is refused. Using the
captured input at absolute header port 3 in place of old slot 3 at port 7
is also refused. [Native regression][native-guard-regression]

## Latch a computed initializer

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Thms`.
`Native.Preheader.lowerChecked` takes a native graph with one preheader
producer, a wrapping i64 add or sub over captured inputs. At least one
entry slot must read its result. Other entry reads come from the captured
inputs. The header uses the existing signed guarded-row profile with equal
input and bank widths. `Native.lowerChecked` still handles the empty
preheader. The checker for this extension rejects literal initializers.
[Simple's first Loop/Phi arrival][simple-latch]

`recognize_sound` proves exact reconstruction of the typed source.
`entry_packet` relates the RTL initializer and jump to the λSSA entry
packet while preserving captures. `header_packet` relates the taken
feedback tuple or exit word in the emitted targets. Feedback rebinds the
whole bank from the old snapshot. The return and absence iff laws use
native finite execution and preserve the entire initial memory on return.

For a return after `b` backedges, `rtl_runMain_fuel_iff` gives the exact
minimum of `activationSteps * (b + 1) + 3` instructions, including the
initializer, jump, and return. `lambda_run_succ` uses `b + 1` header
visits and evaluates entry outside that budget. The two runners count
different operations. [Checked regressions][preheader-regression]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def capture (slot : Fin 3) := argumentPort 3 slot
def old (slot : Fin 3) := suffixPort (wordPorts 3) (capture slot)

def initialized : Preheader.Source 3 [[wordPort], [.value .predicate]] where
  preheader := .cons .sub (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil)) .nil
  header :=
    .cons .add (.cons (.arg (old 0)) (.cons (.arg (old 1)) .nil))
      (.cons .slt (.cons (.output (0 : Fin 1) .head) (.cons (.arg (old 2)) .nil)) .nil)
  phiInputs
    | .entry => .cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) (.cons (.arg (capture 2)) .nil))
    | .backedge => .cons (.output (0 : Fin 2) .head) (.cons (.arg (old 1)) (.cons (.arg (old 2)) .nil))
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

#eval do
  let (rtl, ssa) ← Preheader.lowerChecked initialized
  let input : WordTuple 3 := .cons (6 : Word) (.cons (2 : Word) (.cons (5 : Word) .nil))
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 9 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [5], some 5)
```

The initial bank is `(1, 2, 5)`, so the first comparison is `3 < 5`
and feeds back `(3, 2, 5)`. Passing the raw first capture to slot 0
would instead test `8 < 5` and exit on the first visit. A captured read
in a feedback copy is refused even when it currently agrees with the
corresponding bank slot.

## Schedule dependent preheader producers

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms`.
`Table.lowerChecked` admits a typed, straight-line preheader made of
wrapping i64 adds and subs. Each operand can read a captured input or an
earlier result. At least one entry slot must read a computed result.
The checker keeps the original ordered entry column and reuses the
existing signed-row header check. `recognize_sound` recovers the exact
native graph. The original empty and singleton entry APIs are available
for their respective profiles.

`entry_block` proves that the emitted RTL operations preserve the whole
memory and make every native capture and computed word available in its
assigned register. `entry_packet` covers the subsequent simultaneous
bank binding in both RTL.SSA and explicit-Φ λSSA. Feedback and exit use
the existing header proof. The return and absence iff laws relate both
targets to native finite execution, with full memory equality on return.

With `k` producers and `b` backedges the minimum RTL fuel is
`k + activationSteps * (b + 1) + 2` instructions. This includes `k`
preheader operations, one entry jump, and one return. The λSSA runner
evaluates entry outside its budget and needs `b + 1` header visits.
[Checked regression][table-regression]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Thms

open Silmaril.Isotope.Institution.Observational (Observation ssaBeh)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber (inputModel)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Behavior)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader
open Silmaril.Machine.SeaOfNodes.Loop.RTL
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def capture (slot : Fin 3) := argumentPort 3 slot
def old (slot : Fin 3) := suffixPort (wordPorts 3) (capture slot)

def dependent :
    SourceWithEntry 3 [[wordPort], [wordPort]] [[wordPort], [.value .predicate]] where
  preheader :=
    .cons .sub (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil))
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) .nil)) .nil)
  header :=
    .cons .add (.cons (.arg (old 0)) (.cons (.arg (old 1)) .nil))
      (.cons .slt (.cons (.output (0 : Fin 1) .head) (.cons (.arg (old 2)) .nil)) .nil)
  phiInputs
    | .entry =>
      .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) (.cons (.arg (capture 2)) .nil))
    | .backedge =>
      .cons (.output (0 : Fin 2) .head) (.cons (.arg (old 1)) (.cons (.arg (old 2)) .nil))
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

#eval do
  let (rtl, ssa) ← Table.lowerChecked dependent
  let input : WordTuple 3 := .cons (6 : Word) (.cons (2 : Word) (.cons (5 : Word) .nil))
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 10 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [7], some 7)

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (input : WordTuple 3) (initial : Memory) :
    Table.rtlDenote targets.1 input initial = Table.nativeDenote dependent input initial ∧
      Table.lambdaDenote targets.2 input initial = Table.nativeDenote dependent input initial :=
  Table.denotations_eq accepted input initial

def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))

theorem spinAbsent : dependent.denote model (bank 0 1 1) = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact dependent.not_returns_of_backedge_invariant model (bank 0 1 1) value
    (· = bank (-1) 0 1) (by cbv)
    (fun old fixed => fixed.symm ▸ ⟨bank (-1) 0 1, by cbv, rfl⟩)
    ((dependent.returns_iff_mem_denote model _ _).mpr present)

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    ¬ (∀ input : WordTuple 3, (Rows.rtlObservation targets.1 input initial).Nonempty) ∧
    ¬ (∀ input : WordTuple 3,
        (Table.Institution.lambdaReturns input initial (Table.Institution.scope accepted)).Nonempty) := by
  have absent : ¬ (Loop.Institution.Sentence.terminates (Table.Institution.program dependent)).Holds model :=
    fun holds => (Part.eq_none_iff'.mp spinAbsent) (holds (bank 0 1 1))
  have agrees := Table.Institution.terminates_holds_iff accepted initial
  exact ⟨absent ∘ agrees.1.mp, absent ∘ agrees.2.mp⟩

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    Observation.diverge initial ∈ ssaBeh 1
      (inputModel (P := Rows.wordSignature) model Memory (bank 0 1 1))
      (Table.Institution.scope accepted) :=
  (Table.Institution.room_diverges_iff accepted (bank 0 1 1) initial).mpr spinAbsent

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    targets.1.divOracle 0 (words (bank 0 1 1)) initial :=
  (Table.Institution.rtl_divOracle_iff accepted (bank 0 1 1) initial).mpr spinAbsent

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    Observation.diverge initial ∈ ssaBeh 1
      (inputModel (P := Rows.wordSignature) model Memory (bank 0 1 1))
      (Table.Institution.scope accepted) ↔
    Behavior.diverges ∈ Table.Institution.rtlBehaviors (bank 0 1 1) initial targets.1 :=
  Table.Institution.rtl_room_observation_iff accepted (bank 0 1 1) (.diverge initial)

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (perm : Rows.InputPermutation 3) :
    ∃ after, Table.lowerChecked (Table.reindexCaptures perm dependent) = some after :=
  Table.lowerChecked_reindex perm accepted

#eval do
  let swap : Rows.InputPermutation 3 := Equiv.swap 0 2
  let (rtl, ssa) ← Table.lowerChecked (Table.reindexCaptures swap dependent)
  let input := bank 5 2 6
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 10 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [7], some 7)

#eval do
  let identify : Rows.InputMap 3 := fun slot => if slot = 2 then 0 else slot
  let (rtl, ssa) ← Table.lowerChecked (Table.mapCaptures identify dependent)
  let input := bank 5 2 6
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 13 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 3 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [6], some 6)

#eval do
  let contract : Rows.InputMap 3 2 := fun slot => if slot = 1 then 1 else 0
  let (rtl, ssa) ← Table.Width.lowerChecked contract dependent
  let input : WordTuple 2 := .cons (5 : Word) (.cons (2 : Word) .nil)
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 13 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 3 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  let params := (rtl.func? 0).map (fun fn : Silmaril.Machine.RTL.SSA.Func _ => fn.sig.params)
  pure (params, machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some 2, some [6], some 6)
```

The two results are `6 - 5 = 1` and `1 + 2 = 3`, so the bank enters as
`(1, 3, 5)` and feeds back `(4, 3, 5)` before returning 7. Using captured
2 as the entry stride returns 5 instead. A captured stride in the feedback
column and a literal in the producer table both fail the check.

## Unbounded partial observations

`Table.denotations_eq` in `Table.Denotation.Thms` identifies each checked target's
`Part (Word × Memory)` with the native partial word paired with the whole
initial memory. The RTL observer selects a singleton return from the
program's call oracle. The λSSA observer selects an exit-zero packet and
final memory from actual Region evaluation. Determinism makes each
witness unique.

Use `mem_rtlDenote_iff_runMain` with an RTL instruction budget and
`mem_lambdaDenote_iff_run` with a λSSA visit budget. The partial
observations range over all finite witnesses. `denotations_none_iff`
relates `Part.none` in each target to no finite native return.
In the regression, input `(0, 1, 1)` initializes `(-1, 0, 1)`.
That bank takes a backedge to itself on every activation, so both target
observations are undefined. The observers describe finite word returns
in this profile. [Return and fixed-point checks][table-regression]

## Satisfaction of observation equations

`Table.Institution.program` and `equation` package checked graphs at the
existing native word signature. The two sides share their typed input
and result sorts. Their producer signatures can differ internally.
`equation_holds_iff` compares the native equation with the existing
`Observational.Sentence.eq` on the emitted RTL and scoped λSSA.
At each typed input and common initial memory, the observations contain
each returned word and its entire final memory. The same theorem gives
a cross-backend comparison, and `equation_at_iff` states the pointwise law.

`room_ret_iff` describes every return in the existing λSSA room. Its exit
is zero, the payload packs the native word, and the final memory equals
the initial memory. `room_other_exit_absent` and `room_fault_absent` give
the corresponding exclusions. The concrete word room model has no
primitive faults.

`room_diverges_iff` identifies the room's divergence observation with
undefined native denotation. From a bank with no finite return, the total
header must choose a backedge and the next bank still has no finite return.
The proof coinducts on these actual λSSA transitions using the entry and
header packet laws. Deterministic finite evaluation excludes divergence in
the other direction.

`room_equation_at_iff` and `room_equation_holds_iff` compare native equations
with the full room at the concrete word signature, pointwise and across all
typed inputs respectively. Room satisfaction compares all initial and final
memories. The initial memory passed to the theorem supplies one witness for
reflection through the return projection. On `(6, 2, 5)` the room observes
return 7 with unchanged memory. On `(0, 1, 1)` it observes divergence.
Changing the first preheader subtraction to addition makes the alternative
graph return 3 at that same input, so the room equation fails.
[Checked regression][table-regression]

### Full RTL.SSA behaviours

`rtlBehaviors` collects the existing `RTL.SSA.Behaves` outcomes from
function zero's actual start. `rtl_start_exists` certifies the start
for every typed input and initial memory. `rtl_behavior_iff` classifies
all outcomes. Returns contain exactly one native word with the entire
initial memory. `rtl_no_fault` excludes both traps and stuck states.

`rtl_divOracle_iff` relates native undefinedness to an infinite sequence
of machine instructions. The proof follows the emitted entry and then
the nonempty instruction path for each taken backedge. A header with
no finite native return must take that backedge, and the successor
bank still has no finite return. Determinism excludes divergence when
the machine has a finite return. Bounded `runMain` still reports a
running state when its instruction budget is exhausted.

`rtl_equation_at_iff` and `rtl_equation_holds_iff` compare native
equations with full RTL behaviour equations at one typed input or all
typed inputs, with a common initial memory. The regression checks
return 7, divergence on the fixed-point input, and a failed RTL equation
when the other side returns 3 at that input. [Checked regression][table-regression]

### Comparing the emitted backends

`rtl_room_observation_iff` compares the full room with actual RTL outcomes
at the memory recorded in each room observation. An exit-zero packet
and a singleton RTL return carry the same word and the entire initial
memory. Divergence observations correspond in both directions.
`rtl_room_return_iff` queries an exact word and final memory directly.

`rtl_room_equation_at_iff` compares actual RTL equation satisfaction at a
shared typed input and initial memory with full room satisfaction at
that input. For the checked pure profile, one common initial memory
suffices to reflect the room equation, which ranges over all memories.
`rtl_room_equation_holds_iff` quantifies the comparison over typed inputs.
The regression pairs return 7 and fixed-point divergence across both
backends and checks the mismatch when RTL returns 3 and the other
emitted region diverges. [Checked regression][table-regression]

These comparisons are at the concrete dependent-preheader word signature.
`terminates_holds_iff` relates the native termination sentence to a
nonempty return set at every typed input.

### Permuting dependent-preheader captures

`Table.reindexCaptures` uses the typed `Rows.InputPermutation` on external
reads in the preheader producer table and the entry column. Earlier producer
references, header bank slots and incoming occurrences retain their identity.
`Table.initial_reindex` proves the whole entry latch commutes with
`perm.pull`. `Table.denote_reindex` extends this to the native partial
result of a recognized graph.

Run the ordinary `Table.lowerChecked` on the mapped graph to re-emit both
targets. `Table.lowerChecked_reindex` proves acceptance from the original
successful check. The existing computed-initializer requirement and supported
opcode checks still apply. The typed entry reads remain in scope at each
instruction, and the header and exit keep their original checks.
`Table.lowerChecked_reindex_iff` reflects acceptance by applying the inverse
permutation.

`Table.reemit_observations` takes just the original success and supplies the
new checker result together with full RTL and λSSA observation equality
at every pulled valuation. This includes exact returns with unchanged
memory and actual divergence.

`Table.reindex_equation_at_iff` compares each re-emitted equation at the
pulled valuation. The all-input law covers every old valuation because
`InputPermutation.pull_symm` supplies an inverse. In the regression,
swapping captures 0 and 2 reverses the subtraction operands and redirects
the entry limit. Input `(5, 2, 6)` now returns 7, and `(1, 1, 0)` reaches
the fixed point on both targets. The original machine returns 3 at
`(1, 1, 0)`. A typed table whose entry uses only raw captures is refused
before and after permutation. [Checked regression][table-regression]

### Identifying dependent-preheader captures

`Rows.InputMap` maps old word slots to new slots in the same typed interface.
`Table.mapCaptures` applies it to the dependent producer reads and entry
column. The carried bank retains its width and occurrence routing. In the
example, old slots 0 and 2 both read new slot 0, leaving new slot 2 unused.

`Table.lowerChecked_mapCaptures` proves forward acceptance through the
ordinary checker. `Table.reemit_mapped_observations` uses that check to
compare actual RTL and λSSA observations at the pulled valuation, including
returns with the whole initial memory and genuine divergence. The inverse
acceptance and global equation laws above apply to permutations.

`Table.mapCaptures_equation_holds_iff` tests the original equation only on
the image of `InputMap.pull`. The fixture compares two dependent preheaders
whose first subtractions read `0 - 2` and `2 - 2`, where the numbers name
capture slots. At `(6, 2, 5)` they originally return 7 and 6. After capture
identification they agree at every new valuation because pulled slots 0
and 2 are equal. At new input `(5, 2, 6)` both emitted targets return 6
with the whole initial memory. At `(1, 0, 42)` both diverge at the fixed
point. [Checked regression][table-regression]

### Changing the capture width

`Rows.InputMap old new` sends each old slot to a new slot of the same word
sort. Its second width defaults to the first for the same-width API.
`InputMap.pull_comp` composes valuation pullbacks. `Table.Width.Source`
separates capture count from carried-bank width. `Width.mapCaptures`
renames external reads in both scopes. `Width.headerPort_bank` shows that
each bank operand still names its original bank position. The producer table
order and incoming occurrences stay fixed.

`Width.lowerChecked` checks the original table, emits a native function
at the new arity, and validates that function with the ordinary RTL.SSA
well-formedness check. `Width.lowerFunc_wellFormed` proves that check
succeeds for the typed emission. `Width.layout_disjoint` separates the
capture prefix, carried parameters, preheader results, and header
producer registers. Only the capture width changes. Entry and feedback
still pass one complete carried bank to the header.

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Thms

open Silmaril.Machine.SeaOfNodes.Loop.RTL
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

example {entrySigs sigs : List (List PortTy)}
    (source : SourceWithEntry 3 entrySigs sigs) (mapping : InputMap 3 2)
    {before : Checked.Phi.Targets} (accepted : Table.lowerChecked source = some before) :
    Table.Width.lowerChecked mapping source =
      some (Table.Width.lowerRTL (Table.Width.mapCaptures mapping source),
        Generic.lower (Table.Width.mapCaptures mapping source)) :=
  Table.Width.lowerChecked_of_accepted mapping accepted
```

`Width.denote_mapCaptures` proves native partial-result agreement under
pullback, and `Width.equation_on_image` compares the original equation
on just the pulled valuations. `Width.lambda_return_iff` and
`Width.lambda_diverges_iff` give exact λSSA returns with unchanged memory
and actual divergence for checked re-emissions. The three-to-two
regression calls both targets and returns 6 with the initial memory. Its
RTL runner rejects the old three-argument call. For input `(1, 0)` the
λSSA proof observes divergence and RTL reaches a three-instruction
machine cycle. The separate three-to-four regression routes the third
capture to slot four and checks the emitted entry and header registers
and both target returns. [Checked regression][table-regression]

`Width.checked_entry_packet` starts the actual resized RTL function at
the new arity and matches the native initial bank at the pulled inputs.
`Width.header_producers` executes the operations emitted by
`Diamond.RTL.emitOpsWith`, taking one instruction per producer and
establishing the word and guard reads for `Width.header_terminator`.
`Width.header_activation` includes the branch. It rebinds the whole
feedback tuple from the predecessor frame and restores the bank
invariant, or reaches the exit and returns the exact word on the next
instruction. The full memory is preserved on both paths.

For a native return after `k` backedges, the minimum RTL fuel is
`Width.rtlFuel entrySigs sigs k`. It counts the entry producers and jump,
`k + 1` visits of the header producers and branch, and one return
instruction. `Width.rtl_runMain_fuel_iff` accepts arbitrary RTL fuel.
`Width.rtl_runMain_backedges_iff` uses the corresponding native bound
directly, as in this three-to-four call.

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader

example {entrySigs sigs : List (List PortTy)} {source : SourceWithEntry 3 entrySigs sigs}
    {mapping : InputMap 3 4} {targets : Checked.Phi.Targets}
    (accepted : Table.Width.lowerChecked mapping source = some targets)
    (input : WordTuple 4) (mem : Memory) (k : Nat) (word : Word)
    (observed : source.evalBackedges model k (mapping.pull input) = some word) :
    targets.1.runMain (Table.Width.rtlFuel entrySigs sigs k) 0 (words input) mem =
      .returned [word] mem :=
  (Table.Width.rtl_runMain_backedges_iff accepted input mem mem [word] k).mpr
    ⟨word, observed, rfl, rfl⟩
```

`Width.rtl_return_iff` and `Width.rtl_no_finite_return_iff` compare unbounded
finite observations at the pulled valuation. `Width.rtl_divOracle_iff`
uses productive machine backedges to prove actual divergence from native
undefinedness. The constrained input and opcode admission is the same
checked pure, single-header dependent-preheader profile. The regressions
cover zero, one, and two backedges, RTL fuel one instruction below a
return, and genuinely nonreturning inputs.

### Two feedback successor occurrences

`Width.Dispatch.Source` shares one admitted dependent preheader, one pure
header producer table, the continue guard, and the exit projection.
Its alternate column is checked by the ordinary row recognizer as a
second native graph projection. An independent typed word selects a
column on a continuing visit. Each projection still has the existing
explicit-Φ view, and `Dispatch.phi_feedback` identifies its latch with
the corresponding column. [Resized entry and header proofs][resized-rtl]

The RTL ABI uses the mapped capture count and the original bank width.
The header branches to a dispatcher whose successors both target the
header. Slot 0 carries the nonzero selector's column and slot 1 carries
the zero selector's column. `Dispatch.checked_activation` proves the
fetched terminator, the slot selected by the actual frame read, and
all operand values before rebinding. The original native step at the
pulled captures selects the same occurrence and whole packet. The
transfer and return preserve all memory.

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Thms

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader

example {entrySigs sigs : List (List PortTy)} (mapping : InputMap 3 2)
    (source : Table.Width.Dispatch.Source 3 3 entrySigs sigs) {a b : Checked.Phi.Targets}
    (primary : Table.lowerChecked (source.row true) = some a)
    (other : Table.lowerChecked (source.row false) = some b) :
    Table.Width.Dispatch.lowerChecked mapping source =
      some (Table.Width.Dispatch.lowerRTL (Table.Width.Dispatch.mapCaptures mapping source)) :=
  Table.Width.Dispatch.lowerChecked_of_accepted mapping source primary other
```

`Dispatch.rtl_runMain_fuel_iff` and `Dispatch.rtl_return_iff` relate
independent finite return witnesses. A return after `k` feedback transfers
uses `entrySigs.length + 1 + (sigs.length + 2) * (k + 1)` instructions.
A visit ends with either the dispatch transfer or the return instruction.
The three-to-two regression observes different packets at the same
header, rejects a duplicate producer in the alternate row, and checks
returns after one or two feedbacks on nonempty memory.
[Checked regression][table-regression]

### A typed family of feedback slots

`Width.Dispatch.Family.Choices` indexes the number of tests, with one
additional default column. Each `.test` checks a typed word for nonzero
and otherwise advances. A `.last` supplies the default, including in a
family with one slot. Each column goes through the ordinary guarded-row
checker as a projection of the shared producer table. The emitted ABI
uses the mapped capture width and the same carried bank.

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Thms

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch

example {entrySigs sigs : List (List PortTy)} (mapping : InputMap 3 4)
    (source : Family.Source 3 3 entrySigs sigs 2)
    (rows : ∀ slot, ∃ prior, Table.lowerChecked (source.row slot) = some prior) :
    Family.lowerChecked mapping source = some (Family.lowerRTL (Family.mapCaptures mapping source)) :=
  Family.lowerChecked_of_accepted mapping source rows
```

Slot `i` is successor 0 of RTL block `3 + i`. Full packets pass to block 1.
`Family.checked_activation` proves the actual chain reaches that
occurrence, reading the whole packet before rebinding and preserving
memory. `Family.selected_phi_packet` relates the same packet to the
existing explicit-Φ view of its native projection.

`Family.rtl_runMain_fuel_iff` relates RTL instructions to the native
sequence of selected slots. Entry costs one instruction per producer
plus its jump. A continuing visit costs one per header producer, one
continue branch, and `i + 1` dispatch instructions for slot `i`. The
returning visit costs one per header producer, one branch, and one
return. `Family.rtl_return_iff` relates finite witnesses with the same
word and whole memory. The earlier two-slot API keeps its single
dispatch instruction and its cost law. The three-to-four regression
checks all three packets and return costs, rejects a malformed last
column, and exercises the one-slot family.
[Checked regression][table-regression]

### Extract explicit Φ from the emitted RTL

`Family.Phi.extract fn tests` runs the ordinary RTL checker and reads
the actual header incoming operands from `fn`. Its typed finite index
enumerates the entry at `(0, 0)` and then feedback slot `i` at
`(3 + i, 0)`. The pair is the source block and successor position.
`reemit_roundTrip` decodes the `PhiView` column into the original
ordered RTL operands at each occurrence. The view presents branch leaves
in a flat word-register context. `selected` compares a normalized branch's
actual λSSA evaluation with the RTL transfer from the same pre-rebind frame,
including the complete bank and memory. [Public API][family-phi]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Thms

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch

example {entrySigs sigs : List (List PortTy)} (source : Family.Source 4 3 entrySigs sigs 2)
    (slot : Fin 3) :
    let fn := Family.lowerFunc source
    let view := (Family.Phi.extract fn 2).get (Family.Phi.extract_family source)
    let key := Family.Phi.key slot.succ
    (fn.block? key.1).bind (fun block => block.term.args[key.2]?) = view.reemit slot.succ :=
  Family.Phi.reemit_roundTrip _ slot.succ
```

`region_hasType` and `region_return_iff` concern the whole region emitted by
the canonical `RTL.SSA.toLambdaSSA` translator. Its packed exit-zero return
agrees with the machine's word list and final memory. Compose with
`Family.rtl_return_iff` for the native trace and unchanged full memory.
`region_no_return_iff` quantifies over all finite return witnesses. The three-to-four regression covers all
three feedback packets, a missing occurrence, a finite return and a
fixed bank with no finite return. [Checked regression][table-regression]

### Live header values in MLIR CF

`Family.MLIR.check` reads every dispatch row from the emitted RTL
function. A row must be the expected empty dispatcher block with a
positional feedback edge to header 1. Each subsequent test is the next
dispatcher. Each selector and feedback register must occur in the
declared live list. `column_eq_phi` recovers the same ordered operands as
the existing explicit-Φ view at that occurrence.
[Typed transport API][cf-dispatch]

`Family.MLIR.lower` takes a typed CF bank program and a list of live
header origins. The existing producer emitter runs its preheader and
header, including flag-free wrapping subtraction and signed comparison.
The header passes the live words as block arguments. Each conditional
dispatcher uses unsigned `0 < selector` to implement RTL's nonzero test.
A fallthrough forwards the whole live tuple. A selected feedback edge
projects its ordered operands from that tuple, including any old bank
words or header temporaries, before the header rebinds its bank.
[Shared word operations][cf-word-ops] · [CF block scope][cf-scope]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Thms

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg)
open Silmaril.Machine.RTL.SSA (Func)
open Silmaril.MLIR.Arith (Width)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch

example {entrySigs sigs : List (List (Silmaril.SSA.SeaOfNodes.Diamond.Ty Width))}
    (fn : Func Reg) (g : Family.MLIR.Program 4 3 entrySigs sigs)
    (live : Family.MLIR.Live 4 3 sigs) :
    Option (Cfg TargetOp (Family.MLIR.Label live.length 3 2) (Family.MLIR.wordsTy 4) [i64]) :=
  (Family.MLIR.check fn (Family.MLIR.liveRegs live) 3 2).map (Family.MLIR.lower g live)
```

`header_frame` establishes the CF header packet from the supplied CF
producer table. `checked_dispatch_step` compares execution of every
emitted dispatcher block with the corresponding actual RTL.SSA step
when its live arguments match the old RTL frame. The theorem records
the successor occurrence, exact ordered operands, post-transfer bank
readback, and unchanged whole memory. A fallthrough preserves the frame
and transported tuple, so the same relation applies at the next block.
The three-to-four regression exercises three distinct feedback packets,
an actually used header result, and refusal when that result is missing
from the live list. The prefix theorem below composes these dispatcher
steps under local producer agreement.
[Checked regression][table-regression]

### Bounded feedback prefixes

`Family.MLIR.Prefix.predecessor_snapshot` derives the live CF words
from the real RTL producer frame. `Setup` associates each declared CF
live origin with its typed native origin at the same RTL register.
`HeaderMatch` states the local agreement of the supplied producer table
on the guard and those words at the current carried bank. It requires
agreement at each visited header. The RTL execution supplies the
register reads, so subsequent visits rebuild the snapshot from the
new bank established by the previous Φ latch.
[Prefix API][cf-prefix]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Thms

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.MLIR.Arith (Width)

example {old new tests : Nat} {rtlEntry rtlHeader : List (List PortTy)}
    {entrySigs sigs : List (List (Silmaril.SSA.SeaOfNodes.Diamond.Ty Width))}
    {mapping : InputMap old new} {source : Family.Source old old rtlEntry rtlHeader tests}
    {g : Family.MLIR.Program new old entrySigs sigs} {wires : Family.MLIR.Live new old sigs}
    (sys : Family.MLIR.Prefix.Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {carried finish : WordTuple old}
    (path : Family.MLIR.Prefix.Admitted sys input slots carried finish) (frame : Frame Reg)
    (matched : ArgsMatch frame (appendTuple carried input)) :
    ∃ after, Family.MLIR.Prefix.Realized sys input mem slots carried frame finish after :=
  Family.MLIR.Prefix.prefix_correct sys input mem path frame matched
```

The certificate records the real CF path and RTL instruction path at
each visit, the reached successor occurrence and complete explicit-Φ
latch, and the untouched RTL memory. A skipped row forwards the same
live tuple. `realized_run` consumes `rtlHeader.length + 1 + (i + 1)` RTL
instructions and `i + 2` CF blocks for feedback slot `i`, leaving
independent continuation budgets at the new header. The empty prefix
stops at the input header. The checked producer translation below
discharges local agreement for the shared word profile.

### Generate the CF producer tables from the checked RTL source

`Family.MLIR.Prefix.Producer.compile` takes a native family, a typed
capture map, and an ordered list of live native header origins. It runs
the ordinary resized RTL checker, translates that same mapped producer
table, and checks the dispatcher scope and explicit-Φ view. The
translator accepts i64 constants, wrapping add/subtract, and signed
less-than with ordered operands, emitted as existing `arith` operations.
It preserves captures, old-bank reads and earlier producer references
by position. Equality and inequality producers are outside this
translation. The ordinary RTL checker still governs source admission.
[Producer API][cf-producer] · [Shared arithmetic][cf-word-ops]

`entry_frame` proves the actual CF entry supplies the same initial bank
as the RTL entry at the pulled capture valuation. `header_match` proves
the guard and every live word agree at any shared bank. Pass the native
feedback path to `prefix_correct`; it derives a fresh agreement on each
visit and establishes the same simultaneous Φ packet and RTL memory
frame as the original prefix proof. The result covers entry and
continuing feedback visits. The exit theorem below composes with it.
[Prefix API][cf-producer]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Thms

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Family.MLIR.Prefix.Producer (compile prefix_correct Feedbacks)

example {old new tests : Nat} {entry header : List (List PortTy)}
    (mapping : InputMap old new) (source : Family.Source old old entry header tests)
    (live : List (HeaderWord new old header)) (checked : (compile mapping source live).isSome)
    (input : WordTuple new) (mem : Memory) {slots : List (Fin (tests + 1))}
    {carried finish : WordTuple old}
    (path : Feedbacks source (mapping.pull input) slots carried finish) (frame : Frame Reg)
    (matched : ArgsMatch frame (appendTuple carried input)) :
    ∃ after, Family.MLIR.Prefix.Realized (compile mapping source live |>.get checked).setup
      input mem slots carried frame finish after :=
  prefix_correct ((compile mapping source live).get checked) input mem path frame matched
```

In the three-to-four capture fixture, the generated preheader subtracts
and then adds to the earlier result. The generated header adds two old
bank words and compares the result against the third. Slot 0 latches
`[0, 1, 5]`, which zeros the selector for the next visit. Slot 1 then
latches `[1, 5, 1]`. The regression checks both executions, refuses a
live scope missing the computed word, and shows that the first snapshot
fails against the second real RTL dispatcher frame.
[Checked regression][table-regression]

### Take the first exit after a feedback prefix

`Producer.Exit.after_prefix` uses the same checked compiler, starting
RTL frame relation, and native slot choices. A native return at the
final header determines the taken exit. The theorem records both
actual backend paths and the positional explicit-Φ latches for the
preceding feedback visits. The RTL header’s zero successor (block 1,
slot 1) reads the exact result register from the completed producer
frame, sends it to block 2, and rebinds only the exit parameter. CF
takes the false arm with one i64 block argument and returns it from
the exit block. The RTL branch and return preserve the entire memory.
[Exit API][cf-exit]

`Producer.Exit.check` validates the exact ordered RTL exit operand and
singleton return block. A different register of the same type fails
the check. Capture, carried and producer indices survive the typed
translation. Ordinary native admission restricts the exit result to an
old bank word or an admitted computed row result. The structural
profile has a single signed-guard header exit and one i64 return.
[Definitions][cf-exit-defs]

`Producer.Exit.returns` starts at entry from a native `ReturnsAlong`
witness. It proves the emitted CF and RTL bounded runs return the
same word, and the canonical translated λSSA Region returns its packed
word at exit zero with the full memory preserved. Add one CF block for
entry and two for the final header/exit. RTL adds the preheader count
plus one for entry and the header producer count plus two for the
final branch and return. The feedback costs remain positional as above.
[Exit API][cf-exit]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Family.MLIR.Prefix (cfCost wordEnv)
open Family.MLIR.Prefix.Producer (Compiled)

example {old new tests : Nat} {entry header : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entry header tests}
    {live : List (HeaderWord new old header)}
    (compiled : Compiled mapping source live) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {value : Word}
    (path : source.ReturnsAlong (mapping.pull input) slots
      (source.primary.initial model (mapping.pull input)) value) :
    compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) :=
  (Family.MLIR.Prefix.Producer.Exit.returns compiled input mem path
    (fun _ => Silmaril.Machine.RTL.packValues (words input)) rfl).2.1
```

In the resized fixture the two feedback visits latch `[0, 1, 5]`
and `[1, 5, 1]`. The next header computes `1 + 5` and takes the exit.
The regression checks word `6` at 16 RTL instructions and 8 CF blocks
and at λSSA exit zero. The exit check refuses the first capture as the
operand in place of the sum.
[Checked regression][table-regression]

### Recover the exit from an observed CF return

`Producer.Exit.Inversion.from_entry` starts with a successful
`Producer.compile` result and a return from the actual emitted CF
runner at typed inputs. The checked entry constructs the initial
RTL frame and bank relation. Inverting the remaining CF budget
recovers, in order, the reached feedback occurrences and the first
taken exit. The resulting certificate includes each actual CF and RTL
feedback path, its full explicit-Φ latch, and the final exit packet.
`from_header` also works from a caller-provided matched header frame.
[Inversion API][cf-exit-inversion]

`reflect` gives the same CF result at the recovered path's block cost,
the bounded RTL return at its own instruction cost, and the typed λSSA
return at exit zero. The λSSA environment must supply the packed typed
captures at index zero. RTL and λSSA preserve the full initial memory.
The theorem applies to the checked single-exit i64 family described above.
[Inversion API][cf-exit-inversion]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (packValues)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Family.MLIR.Prefix (cfCost rtlCost wordEnv)
open Family.MLIR.Prefix.Producer (Compiled)

example {old new tests : Nat} {entry header : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entry header tests}
    {origins : List (HeaderWord new old header)}
    (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :
    ∃ slots : List (Fin (tests + 1)), cfCost slots + 2 + 1 ≤ fuel ∧
      compiled.rtl.runMain (entry.length + 1 + (rtlCost header.length slots + (header.length + 2)))
        0 (words input) mem = .returned [value] mem := by
  obtain ⟨slots, _, bound, rtl, _, _⟩ :=
    Family.MLIR.Prefix.Producer.Exit.Inversion.reflect compiled input mem fuel value observed
      (fun _ => packValues (words input)) rfl
  exact ⟨slots, bound, rtl⟩
```

The three-to-four fixture returns `8` in three CF blocks and seven RTL
instructions on an immediate exit. The mixed run returns `6` with CF
budget nine. Inversion recovers slots `[0, 1]` and certifies the return
at eight CF blocks and sixteen RTL instructions. Both regressions start
from the emitted CF result.
[Checked regression][table-regression]

### Recover the CF run from an observed RTL return

`Producer.Exit.Inversion.from_rtl` starts with a successful return of
the actual emitted RTL at an arbitrary instruction budget. The RTL
fuel inversion supplies the finite native path. The checked entry
and each actual dispatch cut then give the ordered successor
occurrences, full explicit-Φ packets and the first taken exit.
The certificate records the singleton returned word and identifies
the entire final memory with the initial memory.
[Inversion API][cf-exit-inversion]

The theorem gives an RTL replay at the consumed instruction budget
`rtlFuel entry header slots` and a CF return at `cfCost slots + 2 + 1`
blocks. The original RTL budget can include spare instructions.
`region_of_rtl` gives λSSA exit zero when environment index zero
contains the packed typed captures.
[Inversion API][cf-exit-inversion]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Family.MLIR.Prefix (cfCost wordEnv)
open Family.MLIR.Prefix.Producer (Compiled)

example {old new tests : Nat} {entry header : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entry header tests}
    {origins : List (HeaderWord new old header)}
    (compiled : Compiled mapping source origins) (input : WordTuple new)
    (initial final : Memory) (fuel : Nat) (returned : List Word)
    (observed : compiled.rtl.runMain fuel 0 (words input) initial = .returned returned final) :
    ∃ slots : List (Fin (tests + 1)), ∃ value : Word,
      returned = [value] ∧ final = initial ∧ Family.rtlFuel entry header slots ≤ fuel ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) := by
  obtain ⟨slots, value, _, _, _, shape, memory, _, bound, _, _, _, _, _, cf⟩ :=
    Family.MLIR.Prefix.Producer.Exit.Inversion.from_rtl compiled input initial final fuel returned observed
  exact ⟨slots, value, shape, memory, bound, cf⟩
```

The resized RTL regressions start with two spare instructions. The
immediate run consumes seven and yields the three-block CF return of
`8`. The mixed run consumes sixteen, recovers slots `[0, 1]`, and yields
the eight-block CF return of `6`.
[Checked regression][table-regression]

### Consolidate the forward and converse termination laws

`Producer.Exit.Inversion.returns_iff` combines the actual-run forward law
(`Exit.returns`/`after_prefix`) and its converse (`from_rtl`) into one
existence statement: a bounded RTL return exists for the typed input and
initial memory exactly when an ordered dispatch route (the positional Φ
observations recorded by `Realized`) reaches a taken exit with the same
word. That single witness also supplies a matching bounded CF return, with
the whole memory preserved by both backends. `Family.returnsAlong_unique`
derives that the recovered route is the only one reaching a given value,
from the deterministic native selector and row step; it does not relate
the independent CF block and RTL instruction bounds. [Inversion API][cf-exit-inversion]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Family.MLIR.Prefix (cfCost Realized wordEnv)
open Family.MLIR.Prefix.Producer (Compiled)
open Family.MLIR.Prefix.Producer.Exit (Taken)

example {old new tests : Nat} {entry header : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entry header tests}
    {origins : List (HeaderWord new old header)}
    (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.rtl.runMain fuel 0 (words input) mem = .returned [value] mem) :
    ∃ slots before finish after,
      source.ReturnsAlong (mapping.pull input) slots
        (source.primary.initial model (mapping.pull input)) value ∧
      Realized compiled.setup input mem slots
        (source.primary.initial model (mapping.pull input)) before finish after ∧
      Taken compiled input mem finish after value ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) := by
  obtain ⟨slots, before, finish, after, route, realized, taken, _, cf⟩ :=
    (Family.MLIR.Prefix.Producer.Exit.Inversion.returns_iff compiled input mem value).mp ⟨fuel, observed⟩
  exact ⟨slots, before, finish, after, route, realized, taken, cf⟩
```

In the resized fixture the immediate run returns `8` along the empty
route, and `Family.returnsAlong_unique` identifies it as the unique route
for that word. The mixed run returns `6` along `[0, 1]`, the same route
the forward and converse directions above separately recover.
[Checked regression][table-regression]

### Finite-return existence and its absence across both backends

`Producer.Exit.Inversion.returns_exists_iff` fills in the CF side of the
existing RTL-oracle law (`Family.rtl_return_iff`): a bounded CF return
exists at some budget for the typed input exactly when the abstract
native source has a finite return along some ordered dispatch route.
Composing it with `Family.rtl_return_iff` gives `rtl_oracle_iff`: the RTL
oracle's unbounded native relation returns some word exactly when the
emitted CF does, at its own bounded budget. `no_return_iff` negates that
agreement to state the absence of any finite return in either backend,
quantifying over every budget rather than reading divergence off one
insufficient run. Under the packed-capture entry side condition,
`region_no_return_iff` extends that absence to the canonical λSSA Region,
composing the existing two-directional `Phi.region_no_return_iff` with
`no_return_iff`. [Inversion API][cf-exit-inversion]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Family.MLIR.Prefix (wordEnv)
open Family.MLIR.Prefix.Producer (Compiled)

example {old new tests : Nat} {entry header : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entry header tests}
    {origins : List (HeaderWord new old header)}
    (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (absent : ¬ ∃ slots value, source.ReturnsAlong (mapping.pull input) slots
      (source.primary.initial model (mapping.pull input)) value) :
    ¬ ∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil) :=
  (not_congr (Family.MLIR.Prefix.Producer.Exit.Inversion.returns_exists_iff compiled input mem)).mpr absent
```

In the resized fixture, `fixedSource` shares the immediate/mixed-feedback
fixture's header and producer table but reorders its dispatch tests so
that every activation from `wideSpin` rebinds the same fixed bank
(`familyFixedBank`) and never selects the exit. The existing
`fixedCannotReturn` induction (already used for the native and λSSA
absence laws) now also certifies that the CF compiled from the same
source never returns at any budget, and that neither does the canonical
λSSA Region. [Checked regression][table-regression]

### One fixed word, two independently bounded runners

`Producer.Exit.Inversion.cf_returns_iff` closes the remaining narrow gap
for a fixed result word: a successful bounded CF run returning that word
exists exactly when an independent, separately bounded RTL run exists
returning the same singleton with the initial memory preserved. It
composes the fixed-value CF inversion (`from_entry`/`Exit.from_return_path`)
with the actual RTL iff (`returns_iff`); neither direction reads a single
insufficient budget as evidence of nonreturn. [Inversion API][cf-exit-inversion]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Family.MLIR.Prefix (wordEnv)
open Family.MLIR.Prefix.Producer (Compiled)

example {old new tests : Nat} {entry header : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entry header tests}
    {origins : List (HeaderWord new old header)}
    (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory) (value : Word)
    (observed : ∃ fuel, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :
    ∃ fuel, compiled.rtl.runMain fuel 0 (words input) mem = .returned [value] mem :=
  (Family.MLIR.Prefix.Producer.Exit.Inversion.cf_returns_iff compiled input mem value).mp observed
```

In the resized fixture, the mixed run's CF return of `6` at budget nine
directly supplies the matching bounded RTL return, without separately
recovering the dispatch route. [Checked regression][table-regression]

### Which checked theorem to use

All of `Producer.Exit.Inversion`'s laws above cover the same checked
single-exit i64 family: one MLIR CF lowering plus resized RTL.SSA for a
`Family.Source`/`Compiled` pair. They do not extend to a general SSA,
RVSDG or unscoped MLIR CF program; for the plain single-latch
`Loop.Graph` → typed MLIR CF lowering outside this guarded dispatch
family, see [A pure Sea of Nodes loop in typed MLIR CF][cf-loop-general]
and [the shared scalar producer bridge][cf-word-ops-general].

| Question | Use | Notes |
| --- | --- | --- |
| Does a CF run returning this exact word exist at some budget, and does a matching RTL run too? | `cf_returns_iff` | Both sides `∃ fuel`; preserves the initial memory on the RTL side. Does not recover the dispatch route or costs — use `returns_iff` for those. |
| I have the dispatch route, costs and `Realized`/`Taken` witnesses already (or want them) | `returns_iff` | Fixes the value on the RTL side and gives the exact CF/RTL costs plus the full witness bundle; the CF component alone is what `cf_returns_iff` abstracts away. |
| Does *some* word have a bounded CF return, witnessed by the native dispatch route? | `returns_exists_iff` (CF ↔ native route) | Existentially quantifies the word, unlike `cf_returns_iff`. Compares the emitted CF directly with `Source.ReturnsAlong`; it does not by itself relate RTL. |
| Does the RTL oracle's unbounded native relation agree with that CF existence? | `rtl_oracle_iff` (RTL oracle ↔ CF) | The actual cross-backend bridge, built by composing `returns_exists_iff` with the existing `Family.rtl_return_iff` (RTL oracle ↔ native route). |
| Does neither backend ever return, at any budget? | `no_return_iff` (RTL oracle ↔ CF) and `region_no_return_iff` (λSSA Region ↔ CF) | Negated existentials throughout; never inferred from one insufficient run. `region_no_return_iff` needs the packed-capture entry side condition below. |
| I need the canonical λSSA Region's packed-capture return for a fixed word | `region_returns_iff` | Needs `env 0 = packValues (words input)`. Composes `reflect` (CF → Region) with `Phi.region_return_iff` and `Family.rtl_return_iff` (Region → CF via `cf_returns_iff`). |

[cf-loop-general]: sea-of-nodes-loop-mlir-cf.md
[cf-word-ops-general]: sea-of-nodes-mlir.md

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms \
  +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Thms \
  +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Thms \
  +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.SignedGuardRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.BankOperandRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.ComputedExitRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Regression
```

[pair]: https://github.com/hiloopai/silmaril-lean/pull/3707
[row]: https://github.com/hiloopai/silmaril-lean/pull/3608
[phi]: https://github.com/hiloopai/silmaril-lean/pull/3631
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Regression.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Thms.lean
[fuel-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Thms.lean
[fuel-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Regression.lean
[computed-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/ComputedExitRegression.lean
[operand-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/BankOperandRegression.lean
[native-result]: ../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/Regression.lean
[institution-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Institution/Thms.lean
[simple-two-expressions]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/test/java/com/seaofnodes/simple/Chapter13Test.java#L169-L173
[simple-lt]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L72
[signed-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/SignedGuardRegression.lean
[native-guard-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Regression.lean
[simple-latch]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L110
[preheader-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Regression.lean
[table-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Regression.lean

[resized-rtl]: https://github.com/hiloopai/silmaril-lean/pull/4456
[family-phi]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/Phi/Thms.lean
[cf-scope]: ../../Silmaril/SSA/MLIR/CF/Basic/Defs.lean
[cf-word-ops]: sea-of-nodes-loop-mlir-cf.md#signed-i64-operations-shared-with-rtl
[cf-dispatch]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/MLIR/Thms.lean
[cf-prefix]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/MLIR/Prefix/Thms.lean
[cf-producer]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/MLIR/Prefix/Producer/Thms.lean
[cf-exit]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/MLIR/Prefix/Producer/Exit/Thms.lean
[cf-exit-defs]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/MLIR/Prefix/Producer/Exit/Defs.lean
[cf-exit-inversion]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/MLIR/Prefix/Producer/Exit/Inversion/Thms.lean
