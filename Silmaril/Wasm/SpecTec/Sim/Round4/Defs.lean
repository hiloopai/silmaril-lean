module

public import Silmaril.Wasm.SpecTec.Sim.Round3.Defs
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# SpecTec ↔ Core 3.0, round 4: the simulation over valid configurations

Round 3 refuted every earlier target (`Round3.not_wholeStepBounded`): `Typed` is SpecTec's
syntactic typing, so it admits configurations Core's validity rejects (`memory.grow 0` with no
memory), and it rejects configurations Core's validity admits (a type index or a `list(·)`
of `2 ^ 32` or more elements, an export, before upstream item U4).

Round 4 states the simulation over **valid** configurations instead: Core's own
`ConfigOk c ts` (silmaril-lean, `Execution/Core/Typing/Config.lean`) together with `Bounded c`,
the size side conditions of SpecTec's syntax that Core's syntax does not impose. The earlier
targets and their refutations are kept unchanged.

## `Bounded`

* `store`: the store invariants of round 2 (`Integrate.StoreOk`): tables, element and data
  segments and arrays with fewer than `2 ^ 32` entries, memories of whole pages with fewer than
  `2 ^ 32` bytes. (The table bound is uniform rather than `2 ^ |at|`, because every existing
  forward lemma uses it; memories of exactly `2 ^ 32` bytes are valid in Core and must be
  excluded, `Memory/Wrap.lean`.)
* `types`: every runtime type of the configuration (`tyBnd`): each `_IDX x` has `x < 2 ^ 32`
  (`typeidx = u32`), and each `list(·)` position (`REC list(subtype)`,
  `STRUCT list(fieldtype)`, `FUNC resulttype -> resulttype`) has fewer than `2 ^ 32` elements.
* `exports`: every export name has a UTF-8 encoding of fewer than `2 ^ 32` bytes (the premise of
  SpecTec's `name`).
* `instrs`: every instruction of the configuration (`instrBnd`, through block bodies, label
  continuations and function bodies): `try_table`'s `list(catch)` has fewer than `2 ^ 32`
  entries, and no instruction has a *provisional* encoding (the four SIMD memory
  instructions, which `instrToV` still sends through `schemaInstrV`). The second half is an
  encoding gap of this development, not a restriction of Core or SpecTec; it is to be dropped
  when `instrToV` encodes those instructions.

## The target

`Task.wholeStepValid` (frozen): for every injective host-name encoding, finite host and
`Profile.spec nd r`, some `B` makes both one-step simulations hold up to `Bwd.ConfigEq` from
every valid, bounded source. The forward conjunct also asks `Bounded c'` of the Core successor:
`Bounded` is not preserved by Core (`memory.grow` may produce a memory of exactly `2 ^ 32` bytes,
`Memory.grow_full`; a host may return any store), and SpecTec can only reach images of bounded
configurations. `ConfigOk c'` is not asked: it follows from `ConfigOk c` for every `HostOk` host
(`Step.preservation`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-! ## Bounds of runtime types -/

/-- `2 ^ 32`, the bound of `u32` and of `list(·)`. -/
abbrev bnd32 : Nat := 2 ^ 32

/-- **A runtime type within SpecTec's syntax**: every `_IDX x` has `x < 2 ^ 32`, and every
`list(·)` position (`REC`'s subtypes, `STRUCT`'s fields, `FUNC`'s parameters and results) has
fewer than `2 ^ 32` elements. -/
def tyBnd : {k : TKind} → Ty k → Bool
  | _, .nil => true
  | _, .cons a l => tyBnd a && tyBnd l
  | _, .idx x => decide (x < bnd32)
  | _, .recv _ => true
  | _, .dt d => tyBnd d
  | _, .defn g _ => tyBnd g
  | _, .abs _ => true
  | _, .bot => true
  | _, .use u => tyBnd u
  | _, .ref _ h => tyBnd h
  | _, .num _ => true
  | _, .vec _ => true
  | _, .refv r => tyBnd r
  | _, .botv => true
  | _, .val t => tyBnd t
  | _, .pack _ => true
  | _, .field _ s => tyBnd s
  | _, .struct fs => decide (fs.toList.length < bnd32) && tyBnd fs
  | _, .array f => tyBnd f
  | _, .func ps rs =>
      decide (ps.toList.length < bnd32) && decide (rs.toList.length < bnd32) && tyBnd ps &&
        tyBnd rs
  | _, .sub _ sups body => tyBnd sups && tyBnd body
  | _, .group subs => decide (subs.toList.length < bnd32) && tyBnd subs

/-! ## Bounds of instructions -/

mutual
/-- **An instruction within SpecTec's syntax, with a final encoding**: `try_table`'s catches are a
`list(catch)`, and the four SIMD memory instructions are excluded (their `instrToV` clause is
the provisional `schemaInstrV`). Recurses into block bodies. -/
def instrBnd : Instr → Bool
  | .block _ body => instrsBnd body
  | .loop _ body => instrsBnd body
  | .if_ _ b₁ b₂ => instrsBnd b₁ && instrsBnd b₂
  | .tryTable _ cs body => decide (cs.length < bnd32) && instrsBnd body
  | .vecLoad .. | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. => false
  | _ => true

/-- `instrBnd` on a sequence. -/
def instrsBnd : List Instr → Bool
  | [] => true
  | i :: is => instrBnd i && instrsBnd is
end

/-! ## Bounds of instances, stores and configurations -/

/-- A module instance within SpecTec's syntax: bounded defined types, and export names whose
UTF-8 encoding is shorter than `2 ^ 32` bytes (`name`'s premise). -/
def ModuleBnd (m : ModuleInst) : Prop :=
  (∀ d ∈ m.types, tyBnd d = true) ∧ ∀ e ∈ m.exports, e.name.utf8ByteSize < bnd32

variable {H : Type}

/-- A function instance within SpecTec's syntax: bounded type, module and body. -/
def FuncBnd (fi : FuncInst H) : Prop :=
  tyBnd fi.type = true ∧ ModuleBnd fi.module ∧
    ∀ fn, fi.code = .wasm fn → instrsBnd fn.body = true

/-- The types, modules and code a store holds, within SpecTec's syntax. -/
structure StoreBnd (s : Store H) : Prop where
  /-- Tag types. -/
  tags : ∀ ti ∈ s.tags, tyBnd ti.type = true
  /-- Global types. -/
  globals : ∀ gi ∈ s.globals, tyBnd gi.type.type = true
  /-- Table element types. -/
  tables : ∀ ti ∈ s.tables, tyBnd ti.type.element = true
  /-- Function instances. -/
  funcs : ∀ fi ∈ s.funcs, FuncBnd fi
  /-- Element segment types. -/
  elems : ∀ ei ∈ s.elems, tyBnd ei.type = true
  /-- Structure instance types. -/
  structs : ∀ si ∈ s.structs, tyBnd si.type = true
  /-- Array instance types. -/
  arrays : ∀ ai ∈ s.arrays, tyBnd ai.type = true

mutual
/-- An administrative instruction within SpecTec's syntax: its instructions, annotations and
frames' modules, at every depth. -/
def AdminBnd : Admin → Prop
  | .plain i => instrBnd i = true
  | .ref _ => True
  | .callRefType d => tyBnd d = true
  | .returnCallRefType d => tyBnd d = true
  | .label _ cont body => instrsBnd cont = true ∧ AdminsBnd body
  | .handler _ _ body => AdminsBnd body
  | .frame _ f body => ModuleBnd f.module ∧ AdminsBnd body
  | .trap => True

/-- `AdminBnd` on a sequence. -/
def AdminsBnd : List Admin → Prop
  | [] => True
  | a :: l => AdminBnd a ∧ AdminsBnd l
end

/-- **A configuration within SpecTec's syntax**: the size side conditions SpecTec's IL types
impose and Core's syntax does not (module doc). -/
structure Bounded (c : Config H) : Prop where
  /-- Table, segment, array and memory sizes (round 2's store invariants). -/
  store : Integrate.StoreOk c.store
  /-- Types, modules and code held by the store. -/
  storeBnd : StoreBnd c.store
  /-- The frame's module. -/
  frame : ModuleBnd c.frame.module
  /-- The active code. -/
  code : AdminsBnd c.code

/-! ## The target -/

/-- **The round-4 target** (frozen): the one-step simulation, both directions up to
`Bwd.ConfigEq`, from every valid (`ConfigOk`) and bounded (`Bounded`) source configuration. The
forward conjunct also assumes the Core successor bounded (module doc). The earlier targets
`Task.wholeStep`, `Bwd.Task.wholeStepUpTo` and `Integrate.Task.wholeStepBounded` are kept, with
their refutations (`Round3.not_wholeStep`, …). -/
def Task.wholeStepValid : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
      ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Bounded c → Bounded c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Bounded c →
          SStep (simEnv B) (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

/-- The two one-step simulations of `Task.wholeStepValid` at one `B`, encoding, host and profile:
what the multi-step corollaries assume. -/
def OneStep (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Bounded c → Bounded c' →
    Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
  (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Bounded c →
    SStep (simEnv B) (configV hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c')

/-! ## `ConfigOk ∧ Bounded → Typed`, reduced -/

/-- **The positive typing of the encoding's leaves** that `ConfigOk c ts → Bounded c → Typed`
reduces to (`Round4.typed_of_configOk`): every valid, bounded instruction, runtime `CALL_REF`
annotation, catch clause, frame module and store has an image of its IL type. The reduction
proves the rest: the configuration, state and frame records, values, references, traps and the
`throw_ref` of an exception, and labels, handlers and frames at every depth of the code. None of
these fields is discharged yet (`docs/projects/spectec/README.md`). -/
structure PosTyping (B : Builtins) (hn : H → String) : Prop where
  /-- A valid instruction within SpecTec's syntax is a typed `instr`. -/
  instr : ∀ (C : Context) (i : Instr) (it : InstrType), InstrOk C i it → instrBnd i = true →
    TypedV (simEnv B) (.varT "instr" []) (instrToV i)
  /-- A valid, bounded `CALL_REF dt` is a typed `instr`. -/
  callRefType : ∀ d : DefType, TyOk {} d → tyBnd d = true →
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.callRefType d))
  /-- A valid, bounded `RETURN_CALL_REF dt` is a typed `instr`. -/
  returnCallRefType : ∀ d : DefType, TyOk {} d → tyBnd d = true →
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.returnCallRefType d))
  /-- The module of a valid frame, within SpecTec's syntax, is a typed `moduleinst`. -/
  moduleinst : ∀ (s : Store H) (m : ModuleInst) (C : Context), ModuleInstOk s m C → ModuleBnd m →
    TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m)
  /-- A valid, bounded store is a typed `store`. -/
  store : ∀ s : Store H, StoreOk s → Integrate.StoreOk s → StoreBnd s →
    TypedV (simEnv B) storeT (storeV hn s)

/-! ## Runs -/

/-- SpecTec's reflexive-transitive `Step`, read declaratively. -/
abbrev SSteps (env : Env) : Value → Value → Prop := Relation.ReflTransGen (SStep env)

/-- Every configuration Core reaches from `c` is bounded. (`Bounded` is not an invariant of
Core's step: `memory.grow` can reach a memory of `2 ^ 32` bytes, `Round4.not_bounded_preserved`.) -/
def BoundedReach (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c', Steps P host c c' → Bounded c'

/-- **The simulation relation up to call annotations**: SpecTec's configuration is the image of
`d`, which agrees with Core's `c` up to `CALL_REF` annotations (`Bwd.ConfigEq`) and is `Typed`.
The witness `d` need not be valid in Core: after `return_call_ref` out of a frame SpecTec keeps
the index `y`, which the caller's module need not define (obstruction 1). -/
def SimRel (B : Builtins) (hn : H → String) (c d : Config H) : Prop :=
  Bwd.ConfigEq c d ∧ Typed (simEnv B) hn d

/-- **The one-step simulation along `SimRel`**: from a valid, bounded Core configuration `c` and
any SpecTec witness `d` related to it, both directions. With `d := c` this is `OneStep` (when `c`
is `Typed`); unlike `OneStep` it composes along runs (`Round4.steps_sim`, `Round4.ssteps_sim`),
because the successor witness is again related. -/
def OneStepRel (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  (∀ (c d c' : Config H) (ts : List CValType), ConfigOk c ts → Bounded c → SimRel B hn c d →
    Bounded c' → Step P host c c' →
    ∃ d', SimRel B hn c' d' ∧ SStep (simEnv B) (configV hn d) (configV hn d')) ∧
  (∀ (c d : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Bounded c →
    SimRel B hn c d → SStep (simEnv B) (configV hn d) w →
    ∃ c' d', SimRel B hn c' d' ∧ w = configV hn d' ∧ Step P host c c')

end Silmaril.Wasm.SpecTec.Sim.Round4
