module

public import Silmaril.Proofs.Wasm.Component.Reference.CalloutPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.FloatPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Seq
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.CalloutPath` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.CalloutPath` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId →
  List Silmaril.Wasm.Component.Value.Val → Option (List Silmaril.Wasm.Component.Value.Val × σ)}
  {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## Trap bubbling

Adapted from `Silmaril.Proofs.Wasm.Game.Linking.Split.Typed` (`step_lift_instrs`, `reach_map`,
`fill_trap_reach`), which this topic does not import; Core-level proofs unchanged. -/

/-! ## Plays of the instance -/

/-- The data of an export call of the core instance: the reference engine's core store `cs`
renames to the instance's, and the export question `f` invokes address `a` on the lowered
arguments `xs`. -/
structure CallStart (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (E3 P V IR).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P V IR))) (f : I.F.Op) (a : Nat)
    (xs : List Flat) : Prop where
  good : c.Good
  inst : c.mod.IsInst I
  store : Store.mapH trampIdx cs = I.store
  addr : I.addr f.1 = a
  args : f.2.1 = xs.map ofFlat

theorem CallStart.wf {cs : (E3 P V IR).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P V IR))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs) : I.WellFormed I.store :=
  C.inst.1.choose_spec.ok

/-- The start of the run against the stateful environment of `g`. -/
theorem CallStart.pre {cs : (E3 P V IR).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P V IR))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs) (q : σ) :
    Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke I.store (I.addr f.1) f.2.1, q)
      ((Thread.invokeFlat a xs).config (Store.mapH trampIdx cs), q) := by
  rw [C.store, C.addr, C.args]
  exact .refl

/-- The export question, then a path from the invocation. -/
theorem CallStart.path {cs : (E3 P V IR).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P V IR))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs)
    {rest : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.running f (Store.mapH trampIdx cs) (Thread.invokeFlat a xs)) rest q) :
    I.Path P (.idle I.store) (.inr (.ask f) :: rest) q := by
  have hi : I.initThread f = Thread.invokeFlat a xs := by
    show Thread.pending (I.addr f.1) f.2.1 = _
    rw [C.addr, C.args]
    rfl
  rw [C.store] at h
  exact .cons (.call I.store f) (hi ▸ h)

/-- The data of an export call of the core instance at a later store `s`: the reference
engine's core store `cs` renames to `s`, which is well formed, and the export question `f`
invokes address `a` on the lowered arguments `xs`. -/
structure CallStartAt (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance) (s : Store Nat)
    (cs : (E3 P V IR).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P V IR))) (f : I.F.Op) (a : Nat)
    (xs : List Flat) : Prop where
  good : c.Good
  inst : c.mod.IsInst I
  store : Store.mapH trampIdx cs = s
  wf : I.WellFormed s
  addr : I.addr f.1 = a
  args : f.2.1 = xs.map ofFlat

/-- The start of the run against the stateful environment of `g`, at a later store. -/
theorem CallStartAt.pre {s : Store Nat}
    {cs : (E3 P V IR).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P V IR))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStartAt c I s cs f a xs) (q : σ) :
    Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke s (I.addr f.1) f.2.1, q)
      ((Thread.invokeFlat a xs).config (Store.mapH trampIdx cs), q) := by
  rw [C.store, C.addr, C.args]
  exact .refl

/-- The export question at a later store, then a path from the invocation. -/
theorem CallStartAt.path {s : Store Nat}
    {cs : (E3 P V IR).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P V IR))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStartAt c I s cs f a xs)
    {rest : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.running f (Store.mapH trampIdx cs) (Thread.invokeFlat a xs)) rest q) :
    I.Path P (.idle s) (.inr (.ask f) :: rest) q := by
  have hi : I.initThread f = Thread.invokeFlat a xs := by
    show Thread.pending (I.addr f.1) f.2.1 = _
    rw [C.addr, C.args]
    rfl
  rw [C.store] at h
  exact .cons (.call s f) (hi ▸ h)

/-! ## Component import calls -/

end Silmaril.Proofs.Wasm.Component.Param.Core3R
