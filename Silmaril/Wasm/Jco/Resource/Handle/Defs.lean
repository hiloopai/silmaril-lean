module

public import Silmaril.Wasm.Jco.Resource.Wrap.Defs

/-!
# Handle-passing modules and their thin wrapper

Part (d) of `docs/projects/wasm-components.md`. `Silmaril.Wasm.Jco.Resource.Wrap` covers **rep-passing** modules:
the generated adaptor calls `resource.rep`/`resource.drop`/`resource.new`, and `M` only sees
reps. A **handle-passing** module calls the resource built-ins itself. It receives handles of
the component instance's table and returns handles. Its thin wrapper needs no adaptor code,
only `canon lift`s of its exports.

* `RBuiltins σ`: an implementation of the built-ins `resource.new r`, `resource.rep r` and
  `resource.drop r` over states `σ`. `canonB M H` is the canonical one over the component
  instance's table: `builtinNew`, `builtinRep` and `builtinDrop` of
  `Silmaril.Wasm.Jco.Resource.Basic`.
* `HMod`: a handle-passing core module. `core` gives its state, its memory and its plain
  exports, the functions that call no built-in. `call B n` is the behaviour of export `n` when
  the module's imports of the built-ins are `B`. `call` is polymorphic in the table type
  `τ`. That alone does not confine the module to `B`: a relation may relate any final table.
  The results therefore assume `HMod.Follows`, which fixes the behaviour.
* `RInstr.stepB`, `execB`, `RFn.runB`: the adaptor instructions of
  `Silmaril.Wasm.Jco.Resource.Adaptor` with the built-ins as a parameter.
* `fuseR M md`: **the fused module**. This is the single core module made of the adaptor
  `adaptorR md` and `M`. Its export `cabi_realloc` is the adaptor's `realloc` shim, and its
  export of world function `f` is the shim `shimR md f` (rep and drop the `own` parameters, run
  `M`'s rep-passing function, `resource.new` the `own` result) with its built-in calls going to
  `B`. Any other name is `M`'s export. It is a handle-passing module.
* `thinR md r`: **the thin wrapper** of a handle-passing module, an `RComp` with no adaptor
  function: `canon lift` of the module's export of each world function, with its `realloc`
  export `r`. `RComp.callExportH N H c` (core references through `HMod.callRef`): the behaviour of such a component around `N`, whose
  built-in imports are `canonB` (an `adapt` reference traps: thin wrappers have none).
* `recognizeThinR md r`: the thin wrapper when `r` is not the name of a world function.
* `HMod.Follows N md`: `N` follows the handle-passing convention for `md`. Its export of every
  world function behaves as the fused shim over its own plain exports, for every built-ins
  implementation `B`.

`Silmaril.Wasm.Jco.Resource.Handle.Thms` proves that the thin wrapper of the fused module **is**
`wrapR md` (`thinR_fuseR`), and that a recognized thin wrapper of a module following the
convention agrees with `wrapR md` (`recognizeThinR_agrees`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat)

/-! ## Built-ins as a parameter -/

/-- An implementation of the resource built-ins over states `σ`. -/
structure RBuiltins (σ : Type) where
  new : RtId → List Flat → RM σ (List Flat)
  rep : RtId → List Flat → RM σ (List Flat)
  drop : RtId → List Flat → RM σ (List Flat)

/-- The canonical built-ins over the component instance's table. -/
def canonB (M : CoreInst) (H : HTab) : RBuiltins (withTab M H.T).St :=
  ⟨builtinNew M H, builtinRep M H, builtinDrop M H⟩

/-- **A handle-passing core module.** -/
structure HMod where
  /-- State, memory, and the exports that call no built-in. -/
  core : CoreInst
  /-- Export `n` with the built-in imports `B`, for every table type. -/
  call : {τ : Type} → RBuiltins (core.St × τ) → String → List Flat → RM (core.St × τ) (List Flat)

section
variable (M : CoreInst) {τ : Type} (B : RBuiltins (M.St × τ))

/-- Call a built-in on the top of the stack. -/
def callTopB (b : List Flat → RM (M.St × τ) (List Flat)) (f : Frame) : RM (M.St × τ) Frame :=
  match f.stack with
  | x :: st => do
    let ys ← b [x]
    pure ⟨f.locals, ys.reverse ++ st⟩
  | [] => RM.fail

/-- One adaptor instruction with the built-ins `B`. -/
def RInstr.stepB : RInstr → Frame → RM (M.St × τ) Frame
  | .base i, f => i.step (withTab M τ) f
  | .resNew r, f => callTopB M (B.new r) f
  | .resRep r, f => callTopB M (B.rep r) f
  | .resDrop r, f => callTopB M (B.drop r) f

/-- A sequence of adaptor instructions with the built-ins `B`. -/
def execB : List RInstr → Frame → RM (M.St × τ) Frame
  | [], f => pure f
  | i :: is, f => do
    let f' ← i.stepB M B f
    execB is f'

/-- An adaptor function with the built-ins `B`: prologue, core shim, epilogue. -/
def RFn.runB (fn : RFn) (args : List Flat) : RM (M.St × τ) (List Flat) := do
  let f ← execB M B fn.pre ⟨args, []⟩
  RM.check f.stack.isEmpty
  let rs ← fn.core.run (withTab M τ) f.locals
  let g ← execB M B fn.post ⟨[], rs.reverse⟩
  pure g.stack.reverse

end

/-! ## The fused module and the thin wrapper -/

/-- The name of the fused module's `realloc` export. -/
def fuseReallocName : String := "cabi_realloc"

/-- **The fused module**: the adaptor `adaptorR md` and `M` as one handle-passing module. -/
def fuseR (M : CoreInst) (md : MetaR) : HMod where
  core := M
  call B n xs :=
    if n = fuseReallocName then (reallocShim md.alloc).run (withTab M _) xs
    else match md.world.find? (·.name == n) with
      | some s => (shimR md s).runB M B xs
      | none => (withTab M _).call n xs

/-- **The thin wrapper** of a handle-passing module: `canon lift`s of its exports, with its
`realloc` export `r`, and no adaptor. -/
def thinR (md : MetaR) (r : String) : RComp :=
  { lifts := md.world.map fun s => ⟨s, .core s.name, .core r⟩ }

/-- Recognition (partial): the thin wrapper, when the `realloc` export is not a world function. -/
def recognizeThinR (md : MetaR) (r : String := fuseReallocName) : Option RComp :=
  if md.world.all (·.name != r) then some (thinR md r) else none

/-- A core function of a component around a handle-passing module. -/
def HMod.callRef (N : HMod) (H : HTab) : CRef → List Flat → RM (withTab N.core H.T).St (List Flat)
  | .core n, xs => N.call (canonB N.core H) n xs
  | .adapt _, _ => RM.fail

namespace RComp

variable (N : HMod) (H : HTab) (c : RComp)

/-- The behaviour of export `name` of a component around a handle-passing module. -/
def callExportH (name : String) (vs : List RVal) : RM (withTab N.core H.T).St (Option RVal) :=
  match c.lifts.find? (·.sig.name == name) with
  | some l => canonCallR N.core H (N.callRef H l.realloc) (N.callRef H l.callee) l.sig vs
  | none => RM.fail

end RComp

/-- `N` **follows the handle-passing convention** for `md`: for every built-ins implementation,
its export of each world function behaves as the fused shim over its plain exports. -/
def HMod.Follows (N : HMod) (md : MetaR) : Prop :=
  ∀ {τ : Type} (B : RBuiltins (N.core.St × τ)) (s : RSig), s ∈ md.world →
    N.call B s.name = (shimR md s).runB N.core B

/-- `N`'s `realloc` export `r` is a plain export: it calls no built-in. -/
def HMod.PlainAt (N : HMod) (r : String) : Prop :=
  ∀ {τ : Type} (B : RBuiltins (N.core.St × τ)), N.call B r = (withTab N.core τ).call r

end Silmaril.Wasm.Jco.Res
