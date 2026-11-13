module

public import Silmaril.Compiler.Mir.ConstProp.Defs
public import Silmaril.Compiler.Mir.CSE.Defs
public import Silmaril.Compiler.Mir.DeadCode.Defs
public import Silmaril.Compiler.Mir.JumpThread.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Defs
public import Silmaril.Compiler.Native.Optimize.LocalSSA.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Defs
/-!
# Native optimization through block-local SSA

Each basic block receives fresh names for its writes. Input names denote the
register values at block entry; `outputs` records the final version of each
register written by the block. Lowering commits those versions before the
terminator, so successors retain Mir's mutable-register interface. Calls remain
effectful, symbolic instructions throughout this transformation.

This is a local SSA representation, without global block arguments or phi
nodes. The renaming/lowering round trip has forward/backward open-block
simulations and finite successful observation equivalence under explicit bounds.
The independent symbolic validator (`Validation.check`) is proved sound only on
call-free fragments: the `check_sound` theorems (`Validation.PureSoundness`,
`Slots.Soundness`, `Effects.Soundness`, `Floating.Soundness`,
`Address.Effects.Soundness`) give, for blocks whose instructions are all admitted
(ops, and depending on the fragment frame slots, finite loads and stores,
floating ops and ordinary addresses; never calls), a candidate run with the same
exit and memory for every successful source run. The LambdaSSA folding traversal
has preservation proofs only for its typed, pure, total arithmetic fragment
(`LambdaSSA.Defs`). The reused Mir optimization passes have their
imported Mir refinement proofs, so `optimizeWith_correct_withoutSSA` proves the
selected optimizer a Mir pass for every program, but only when
`localSSA = false`. With local SSA enabled, including the default `optimize`,
behavior equality is proved only on restricted finite domains: programs whose
entry function has only admitted (call-free) blocks and finitely executes
(`FiniteInstitution` with cleanup off; `SlotsInstitution`, `EffectsInstitution`,
`FloatingInstitution`, `AddressInstitution` for every configuration). These
results do not establish whole-program correctness or correctness of native code
emission.
-/

@[expose] public section

namespace Silmaril.Compiler.Native.Optimize

open Silmaril.Compile
open Silmaril.Machine

/-- Selection of independent local SSA and post-lowering Mir optimizations. -/
structure Config where
  localSSA : Bool := true
  lambdaSSA : Bool := true
  constantPropagation : Bool := true
  commonSubexpressions : Bool := true
  deadCode : Bool := true
  jumpThreading : Bool := true
  deriving Inhabited, Repr

def roundTripBlock (cfg : Config) (base : Nat) (b : Mir.Block) : Mir.Block :=
  let ssa := enter base b
  let candidate := leave ssa
  let fallback := if ssa.isSSA && Validation.check base b candidate then candidate else b
  if cfg.lambdaSSA then
    ((LambdaSSA.optimize? base b).map (·.1)).getD fallback
  else fallback

def versionFunc (cfg : Config) (f : Mir.Func) : Mir.Func :=
  { f with blocks := f.blocks.map (roundTripBlock cfg (freshBase f)) }

/-- Only passes that retain all calls are selected. Native calls may name
external functions that are intentionally absent from the current Mir units. -/
def cleanupPasses (cfg : Config) : List Mir.Pass :=
  (if cfg.constantPropagation then
    [⟨"constProp", Mir.ConstProp.run, Mir.ConstProp.correct⟩] else []) ++
  (if cfg.commonSubexpressions then [Mir.CSE.pass] else []) ++
  (if cfg.deadCode then [⟨"deadCode", Mir.DeadCode.run, Mir.DeadCode.correct⟩] else []) ++
  (if cfg.jumpThreading then [⟨"jumpThread", Mir.JumpThread.run, Mir.JumpThread.correct⟩] else [])

/-- Run the selected local SSA round trip and proved Mir cleanup passes. No
linking or native address interpretation is performed by the optimizer. -/
def optimizeWith (cfg : Config) (us : Array Mir.Unit) : Array Mir.Unit :=
  let versioned := if cfg.localSSA then
    us.map (fun u => { u with funcs := u.funcs.map (versionFunc cfg) }) else us
  Mir.Pass.runAll (cleanupPasses cfg) versioned

def optimize : Array Mir.Unit → Array Mir.Unit := optimizeWith {}

/-- The SSA check on every entered block, exposed separately for diagnostics. -/
def checkSSA (us : Array Mir.Unit) : Bool :=
  us.all fun u => u.funcs.all fun f => f.blocks.all fun b =>
    (enter (freshBase f) b).isSSA

end Silmaril.Compiler.Native.Optimize
