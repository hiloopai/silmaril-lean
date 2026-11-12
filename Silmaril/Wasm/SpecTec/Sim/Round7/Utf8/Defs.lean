module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: the `$utf8` erratum (U7) and the target without `NoExports`

Round 6 proved the whole-step simulation `Round6.Task.wholeStepValidR` at the backend reading,
but only for configurations none of whose module instances exports anything (`NoExports`, part
of `Round5.Target.BoundedSel`). That restriction cannot be dropped while SpecTec is read in
`simEnv B`, for any `B` (`Round6.MemSimd.not_wholeStepValidSelE`). The reason is that the first
clause of `$utf8` (definition 52 of the fixed wasm-3.0 script) matches every list, including a
singleton, and calls itself on it. So `$utf8([ch])` runs out of fuel at every fuel
(`Round5.Pos.tryClauses_utf8`), no one-character name is a `name`, and no module instance with an
export is a typed `moduleinst`.

This header states the **erratum** and the restated target.

* `utf8BaseEnv`: `baseEnv` with `$utf8` rebound to a declaration with the same parameters and
  result type and **no clauses**, as `hint(builtin)` declarations are. Every other definition,
  and every type, relation and grammar, is unchanged.
* `utf8Env B`: `utf8BaseEnv` with the primitives `MemSimd.withUtf8 B`, which answer `$utf8` by
  the UTF-8 encoding of the characters (`MemSimd.utf8Call`) and defer to `B` elsewhere.
  `callDef` consults the builtins when a definition has no applicable clause, so in `utf8Env B`
  the call `$utf8(ch*)` is `String.toUTF8` on the characters.
* `backendE`: round 6's backend reading (`Reading.SStepB`) over `utf8Env B`.
* `NamesBnd c`: every export name of every module instance in `c` has fewer than `2 ^ 32` UTF-8
  bytes (SpecTec's `name` premise). `BoundedSelE c` is `Round4.Bounded c`, no `FloatMissel` code,
  and `NamesBnd c`. This is `Round5.Target.BoundedSel` with `NoExports` replaced by `NamesBnd`.
* `Round7.Task.wholeStepValidRE`: `Round6.Task.wholeStepValidR` with `backendE` for
  `Round6.Int.backend` and `BoundedSelE` for `BoundedSel`. **Frozen; open.** It is a new statement,
  and `Round6.Task.wholeStepValidR` is unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-! ## The erratum -/

/-- The parameters of `$utf8` in the fixed wasm-3.0 script: one `char*`. -/
def utf8Params : List Param := [.expP "_" (.iterT (.varT "char" []) .list)]

/-- The result type of `$utf8`: `byte*`. -/
def utf8Res : Typ := .iterT (.varT "byte" []) .list

/-- **The erratum `utf8Builtin`**: `$utf8` keeps its signature and loses its clauses, so it is
answered by the primitives, as a `hint(builtin)` declaration is. -/
noncomputable def utf8BaseEnv : Env := baseEnv.bindDef "utf8" (utf8Params, utf8Res, [])

/-- **The round-7 environment**: the erratum, with `$utf8` answered by the UTF-8 encoding of its
characters and every other primitive by `B`. -/
noncomputable def utf8Env (B : Builtins) : Env :=
  utf8BaseEnv.withBuiltins (Round6.MemSimd.withUtf8 B)

/-- Round 6's backend reading of SpecTec's `Step`, over the round-7 environment. -/
def backendE : Round6.Target.Reading := ⟨fun B => Round6.Reading.SStepB (utf8Env B)⟩

/-! ## Export names within SpecTec's bound -/

/-- Every export name of a module instance has fewer than `2 ^ 32` UTF-8 bytes. -/
def ModNamesBnd (m : ModuleInst) : Prop := ∀ e ∈ m.exports, e.name.utf8ByteSize < 2 ^ 32

mutual
/-- Every frame inside an administrative instruction has a module with bounded export names. -/
def AdminNB : Admin → Prop
  | .label _ _ body => AdminsNB body
  | .handler _ _ body => AdminsNB body
  | .frame _ f body => ModNamesBnd f.module ∧ AdminsNB body
  | _ => True

/-- `AdminNB` on a sequence. -/
def AdminsNB : List Admin → Prop
  | [] => True
  | a :: l => AdminNB a ∧ AdminsNB l
end

/-- **Every export name in `c` is within SpecTec's bound**: in the store's function instances,
the frame and every frame in the code. -/
structure NamesBnd (c : Config H) : Prop where
  /-- The store's function instances. -/
  store : ∀ fi ∈ c.store.funcs, ModNamesBnd fi.module
  /-- The frame. -/
  frame : ModNamesBnd c.frame.module
  /-- The frames in the code, at every depth. -/
  code : AdminsNB c.code

/-- **`Round5.Target.BoundedSel` with `NoExports` replaced by `NamesBnd`**. -/
def BoundedSelE (c : Config H) : Prop :=
  Round6.MemSimd.BoundedSelE c ∧ NamesBnd c

/-! ## The restated target -/

/-- **The round-7 target without `NoExports`** (frozen, open). It is `Round6.Task.wholeStepValidR`
read in `utf8Env B` (`backendE`), on `BoundedSelE` configurations, so that module instances may
export names. -/
def Task.wholeStepValidRE : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧ backendE.step B (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          BoundedSelE c → backendE.step B (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

/-! ## A host-blind restatement (pass 4) -/

/-- A module instance with its exports removed. -/
def stripModule (m : ModuleInst) : ModuleInst := { m with exports := [] }

/-- A store whose function instances' modules have their exports removed. -/
def stripStore (s : Store H) : Store H :=
  { s with funcs := s.funcs.map fun fi => { fi with module := stripModule fi.module } }

/-- An outcome with the exports of its store removed. -/
def stripOutcome : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result →
    Silmaril.Wasm.Execution.Host.Outcome (Store H) Result
  | .returned s r => .returned (stripStore s) r
  | .diverged => .diverged

/-- **The host does not observe export names**: removing the exports from the store it is called
in removes them from its outcomes and changes nothing else, in both directions. Core's own rules
never read `ModuleInst.exports`; a host sees the whole store (`host h s vs o`), so without this
hypothesis export stripping is not a simulation on the Core side. -/
def HostExportBlind (host : HostSemantics H) : Prop :=
  (∀ (h : H) (s : Store H) (vs : List Val)
      (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
    host h s vs o → host h (stripStore s) vs (stripOutcome o)) ∧
  (∀ (h : H) (s : Store H) (vs : List Val)
      (o' : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
    host h (stripStore s) vs o' → ∃ o, host h s vs o ∧ o' = stripOutcome o)

/-! ## Configurations up to export lists (pass 5) -/

/-- A function instance whose module has its exports removed. -/
def stripFI (fi : FuncInst H) : FuncInst H := { fi with module := stripModule fi.module }

/-- A frame whose module has its exports removed. -/
def stripFrame (f : Frame) : Frame := { f with module := stripModule f.module }

mutual
/-- An administrative instruction with the exports of every frame's module removed. -/
def stripAdmin : Admin → Admin
  | .label n cont body => .label n cont (stripAdmins body)
  | .handler n cs body => .handler n cs (stripAdmins body)
  | .frame n f body => .frame n (stripFrame f) (stripAdmins body)
  | a => a

/-- `stripAdmin` on a sequence. -/
def stripAdmins : List Admin → List Admin
  | [] => []
  | a :: l => stripAdmin a :: stripAdmins l
end

/-- **A configuration with every export removed**: from the store's function instances, the
frame and every frame in the code. Its image satisfies round 5's `NoExports`. -/
def stripConfig (c : Config H) : Config H :=
  ⟨stripStore c.store, stripFrame c.frame, stripAdmins c.code⟩

/-- **Two configurations that agree up to export lists.** Core's rules never read
`ModuleInst.exports`, so this relation is a bisimulation of `Step` for export-blind hosts
(`Round7.exRel_step`). -/
def ExRel (c d : Config H) : Prop := stripConfig c = stripConfig d

/-- **A configuration without exports**: it is its own `stripConfig`. -/
def Stripped (c : Config H) : Prop := stripConfig c = c

/-- **`Round7.Task.wholeStepValidRE` for export-blind hosts** (pass 4; frozen, open). The same
statement with `HostExportBlind host` added to the host hypotheses. It is implied by
`Task.wholeStepValidRE` (`wholeStepValidREH_of_wholeStepValidRE`). It is the statement that the
planned route can prove: environment monotonicity from `simEnv B` to `utf8Env B`, then export
stripping of SpecTec derivations, then round 6 on the stripped configuration, then un-stripping
on the Core side, which is where `HostExportBlind` is used. -/
def Task.wholeStepValidREH : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧ backendE.step B (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          BoundedSelE c → backendE.step B (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round7
