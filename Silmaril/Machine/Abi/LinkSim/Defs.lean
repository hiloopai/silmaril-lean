module

public import Silmaril.Machine.Abi.Link.Thms
public import Silmaril.Machine.Abi.Thunk.Thms
/-! # Link bridges with simulating thunks

Track C's `Link.Bridge` asks a `thunk` edge for a C1 `Thunk.Correct` adapter. C2 showed that
realistic adapters (gcc's `call_ms`) are not `Correct`: they satisfy the forward simulation
`Thunk.Simulates room guar`, relative to a caller-side room assumption and a callee-side
guarantee. This module adds, *alongside* the existing definitions:

* `SimThunk A B p`: a thunk with its room, guarantee and simulation proof;
* `SimBridge A B p v`: what a link edge with verdict `v` must supply: nothing for `direct`, a
  `SimThunk` for `thunk`, nothing can be supplied for `reject`;
* `SimBridge.wrap`, `SimBridge.room`, `SimBridge.guar`: the importer's call relation through
  the bridge, and the room and guarantee of the edge (trivial for `direct`);
* `Bridge.toSim`: every old `Bridge` is a `SimBridge` (`Thunk.Correct.simulates`), with the same
  wrapped relation and a trivial room and guarantee.

The restated link soundness theorem is `Thms.link_sound_sim`.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Link

open Silmaril.Machine.Abi.SystemV (Proto vocab sysv CallSite)
open Silmaril.Machine.SystemV.Abi (Ffi.State)
open Silmaril.Logic.Institution.Bridges

/-- A thunk from `A` callers to `B` callees with its simulation proof. -/
structure SimThunk (A B : Convention vocab Ffi.State CallSite) (p : Proto) where
  thunk : Convention.Thunk A B p
  room : Ffi.State → Prop
  guar : Ffi.State → Ffi.State → Prop
  simulates : thunk.Simulates room guar

/-- What a link edge with a given verdict must supply, with simulating thunks. -/
def SimBridge (A B : Convention vocab Ffi.State CallSite) (p : Proto) : Verdict → Type
  | .direct => PUnit
  | .thunk => SimThunk A B p
  | .reject => Empty

namespace SimBridge

variable {A B : Convention vocab Ffi.State CallSite} {p : Proto}

/-- The machine relation the importer calls through the bridge. -/
def wrap : (v : Verdict) → SimBridge A B p v → Contracts.Model Ffi.State Ffi.State →
    Contracts.Model Ffi.State Ffi.State
  | .direct, _, model => model
  | .thunk, t, model => (SimThunk.thunk t).wrap model
  | .reject, e, _ => nomatch e

/-- The caller-side assumption of the edge. -/
def room : (v : Verdict) → SimBridge A B p v → Ffi.State → Prop
  | .direct, _ => fun _ => True
  | .thunk, t => SimThunk.room t
  | .reject, e => nomatch e

/-- The callee-side guarantee the edge needs. -/
def guar : (v : Verdict) → SimBridge A B p v → Ffi.State → Ffi.State → Prop
  | .direct, _ => fun _ _ => True
  | .thunk, t => SimThunk.guar t
  | .reject, e => nomatch e

end SimBridge

/-- An old bridge (correct thunk) as a simulating bridge, with trivial room and guarantee. -/
def Bridge.toSim {A B : Convention vocab Ffi.State CallSite} {p : Proto} :
    (v : Verdict) → Bridge A B p v → SimBridge A B p v
  | .direct, _ => PUnit.unit
  | .thunk, t => ⟨t.1, fun _ => True, fun _ _ => True, t.2.simulates _ _⟩
  | .reject, e => nomatch e

end Silmaril.Machine.Abi.Link
