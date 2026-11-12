module

public import Silmaril.Wasm.SpecTec.Sim10.Encode.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Wasm.SpecTec.Sim.Floats.Defs

/-!
# The 1.0 whole-step target, backward half

The 1.0 route of `docs/projects/spectec/README.md` §1.5 relates silmaril-lean's V1 (`V1.Execution.Step`) to
the wasm-1.0 script `Scripts.Wasm10.fixed`, read at `Sim10.simEnv10 B` under the Round 6 backend
reading (`Round6.Reading.SStepB`), through the encoding `Sim10.configV`.

V1 is close to the 1.0 script. Its `Step.context`, `label` and `frame` are the script's
`ctxt-instrs`, `ctxt-label` and `ctxt-frame` (1.0 has `ctxt-instrs`, which 2.0 lost, and its
`ctxt-frame` updates the inner frame, as V1's does); V1's `invoke` is `CALL_ADDR`, and V1's
`invokeWasm` opens the frame and its label in one step exactly as `Step_read/call_addr` does. The
only structural differences are that V1 reduces `block`/`loop` purely (the script uses
`Step_read`, without reading the state) and that V1 has host functions (the script has none).

**Where V1 checks more than the script.** V1 is stuck where Wasm validation rules a configuration
out, and the script is not:

* `select` with operands of different types (V1's `sameType`; the script's `select-*` do not
  compare them);
* `global.set` of an immutable global (V1's `mutable`);
* invoking a function with more than one result (V1's `resultArity`: 1.0 has no multi-value, but
  1.0's IL `functype` allows several results);
* `call_indirect` through a table entry naming no function (V1 needs the function to exist to
  trap on a type mismatch; the script's `otherwise` traps);
* an instruction naming a local, global, table, memory, type or function that does not exist (the
  script's `memory.grow-fail` has no premise at all, and `call_indirect-trap` traps by
  `otherwise` when table 0 or the type is missing).

So the backward target is asked at configurations that exclude these (`GoodV1`): named resources
exist and `global.set` targets are mutable (`ResOkL10`), store functions have at most one result
and table entries name functions (`StoreOk10`), every active `select` redex has operands of one
type (`SelOk`), and every active `global.set` redex writes a value of its global's type (`GSetOk`;
V1's `GlobalInst` has no type of its own, so a type-changing write would change the image's
`TYPE`, which the script's `$with_global` keeps). Each is implied by V1 validation of the
configuration; none is a restriction of the language.

* `Task.wholeStepBwd10` (frozen): every step of the wasm-1.0 script under the backend reading at
  the spec's builtins `Sim.Floats.floatIntB`, from the image of a `GoodV1` configuration whose
  image is typed, is the image of a V1 step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics value frameMemory frameTable)
open Silmaril.Wasm.Execution.Runtime (Frame FuncInst)
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-! ## Resources -/

/-- The locals, globals, functions, types, table and memory that a V1 instruction names exist in
the store `s` and frame `f`; a `global.set` target is mutable. -/
def InstrResOk10 (s : Store H) (f : Frame) : V1.Instr → Prop
  | .call x => (f.module.funcs[x.toNat]?).isSome
  | .callIndirect x => (frameTable s f).isSome ∧ (f.module.types[x.toNat]?).isSome
  | .localGet x | .localSet x | .localTee x => x.toNat < f.locals.length
  | .globalGet x => ∃ a g, f.module.globals[x.toNat]? = some a ∧ s.globals[a.value]? = some g
  | .globalSet x => ∃ a g, f.module.globals[x.toNat]? = some a ∧ s.globals[a.value]? = some g ∧
      g.mutability = .var
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .memorySize | .memoryGrow =>
      (frameMemory s f).isSome
  | _ => True

mutual
/-- The resources an administrative instruction names exist, each in its own frame: the body of a
`FRAME_` is read in that frame. -/
def ResOkA10 (s : Store H) (f : Frame) : Admin → Prop
  | .source i => InstrResOk10 s f i
  | .label _ _ b => ResOkL10 s f b
  | .frame _ fi b => ResOkL10 s fi b
  | _ => True

/-- The resources a code sequence names exist, at any depth of labels and frames. -/
def ResOkL10 (s : Store H) (f : Frame) : List Admin → Prop
  | [] => True
  | a :: l => ResOkA10 s f a ∧ ResOkL10 s f l
end

/-- The store's functions have at most one result (1.0 has no multi-value) and every table entry
names a function of the store. -/
def StoreOk10 (s : Store H) : Prop :=
  (∀ fi ∈ s.funcs, fi.type.results.length ≤ 1) ∧
    ∀ t ∈ s.tables, ∀ a, some a ∈ t.refs → a.value < s.funcs.length

/-! ## Active code -/

/-- `Active code w`: `w` is a contiguous piece of `code`, or of the body of a label or frame of
`code`, at any depth. -/
inductive Active : List Admin → List Admin → Prop where
  | piece {l₁ w l₂ : List Admin} : Active (l₁ ++ w ++ l₂) w
  | label {code w : List Admin} {n : Nat} {cont : V1.Expr} {body : List Admin} :
      .label n cont body ∈ code → Active body w → Active code w
  | frame {code w : List Admin} {n : Nat} {fi : Frame} {body : List Admin} :
      .frame n fi body ∈ code → Active body w → Active code w

/-- Every active `select` redex has operands of one type. -/
def SelOk (code : List Admin) : Prop :=
  ∀ (a b : Execution.Runtime.Value) (c : BitVec 32),
    Active code [value a, value b, value ⟨.int .i32, c⟩, .source .select] → a.type = b.type

/-- `ActiveF f code f' w`: `w` is a contiguous piece of `code` read in frame `f`, or of the body
of a label (read in the same frame) or of a frame `fi` (read in `fi`) of `code`, at any depth;
`f'` is the frame `w` is read in. -/
inductive ActiveF : Frame → List Admin → Frame → List Admin → Prop where
  | piece {f : Frame} {l₁ w l₂ : List Admin} : ActiveF f (l₁ ++ w ++ l₂) f w
  | label {f f' : Frame} {code w : List Admin} {n : Nat} {cont : V1.Expr} {body : List Admin} :
      .label n cont body ∈ code → ActiveF f body f' w → ActiveF f code f' w
  | frame {f f' : Frame} {code w : List Admin} {n : Nat} {fi : Frame} {body : List Admin} :
      .frame n fi body ∈ code → ActiveF fi body f' w → ActiveF f code f' w

/-- Every active `global.set` redex writes a value of its global's type. V1's `GlobalInst` carries
no type (the image derives `TYPE` from the value), while the script's `$with_global` keeps `TYPE`;
validation guarantees the match. -/
def GSetOk (s : Store H) (f : Frame) (code : List Admin) : Prop :=
  ∀ (f' : Frame) (v : Execution.Runtime.Value) (x : GlobalIdx) (a : Execution.Runtime.GlobalAddr)
    (g : Execution.Runtime.GlobalInst),
    ActiveF f code f' [value v, .source (.globalSet x)] →
    f'.module.globals[x.toNat]? = some a → s.globals[a.value]? = some g → v.type = g.value.type

/-- **The invariant of the 1.0 backward target**: what V1 validation of the configuration
guarantees and V1's reduction checks, but the 1.0 script does not. -/
def GoodV1 (c : Config H) : Prop :=
  ResOkL10 c.store c.frame c.code ∧ StoreOk10 c.store ∧ SelOk c.code ∧
    GSetOk c.store c.frame c.code

/-! ## The target -/

/-- **The backward half of the 1.0 whole step, at the spec's builtins** (frozen): every step of the
wasm-1.0 script under the backend reading at `Sim.Floats.floatIntB`, from the image of a `GoodV1`
configuration whose image is typed, is the image of a V1 step. -/
def Task.wholeStepBwd10 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice) (c : Config H)
      (w : Silmaril.SpecTec.Sem.Value),
      Typed10 (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c → GoodV1 c →
      Sim.Round6.Reading.SStepB (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r)))
        (configV hn c) w →
      ∃ c', w = configV hn c' ∧ V1.Execution.Step host c c'

end Silmaril.Wasm.SpecTec.Sim10
