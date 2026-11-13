module

public import Silmaril.Wasm.Jco.Bridge.State.Defs
public import Silmaril.Wasm.Jco.Bridge.Thms
import Silmaril.Proofs.Wasm.Jco.Bridge.State

/-!
# Relating the two settings for stateful modules: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Bridge.State`. On memory-free worlds (`Meta.memFree`) and
stateful modules (`SMod σ`):

* **`wrap_state`**, `thinComp_state` (memory-based model): over the instance of a stateful
  module, `wrap md` and the thin wrapper `thinComp md r` behave as `specState md m`, the
  state-passing `RM.ofFun (stateCall m s vs)`. The instance state is threaded through calls.
* **`mem_sem_iff`** (component IR, the core module): the IR strategy of a stateful module
  contains the play of questions `qs` answered by `rs` exactly when `rs` are the answers of its
  state machine from the initial state, one call after another (`SMod.answers`).
* **`inst_ok`**, **`inst_trap`** (the two notions of program, for one call): the state machine
  answers a flat question to export `i` with `ys` and moves to `s'` exactly when the
  memory-based instance's call of export `i` returns `ys` in state `s'`. It answers `none`
  exactly when that call traps.
* `stateCall_toS`, **`specState_toS`**: a pure module seen as a stateful module with one state
  (`PMod.toS`) gives the pure bridge's `specPure`. The stateful bridge extends the pure one.

Open: the component-level IR statement for stateful modules, **`SimpleCompState`** (a
frozen `Prop`). With it, `mem_sem_iff`-style plays of the component would be the answers of
`stateCall`, as `specState` is on the memory side. The modelling choices: a trap answers
`none` and leaves the state unchanged in the IR, while `RM` has no state after a trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco (PTy PVal Meta inMem wrap thinComp)

variable {σ : Type}

/-- A memory-free world function under the C convention, over a stateful module. -/
theorem specCall_state (md : Meta) (m : SMod σ) (s : Silmaril.Wasm.Jco.Sig)
    (hp : s.params.all PTy.memFree = true) (hr : inMem s.result = false) (vs : List Val) :
    md.specCall m.inst s (vs.map PVal.val) = Silmaril.Wasm.Jco.RM.ofFun (stateCall m s vs) :=
  Silmaril.Proofs.Wasm.Jco.Bridge.State.specCall_state md m s hp hr vs

/-- The C convention over a stateful module. -/
theorem spec_state (md : Meta) (m : SMod σ) (h : md.memFree = true) (name : String)
    (vs : List Val) : md.spec m.inst name (vs.map PVal.val) = specState md m name vs := by
  unfold Meta.spec specState
  rcases hf : md.world.find? (·.name == name) with _ | s
  · rw [hf]
    rfl
  · have hs := Silmaril.Wasm.Jco.memFree_mem md h (List.mem_of_find?_eq_some hf)
    rw [hf]
    exact specCall_state md m s hs.1 hs.2 vs

/-- **`wrap md` over a stateful module is state passing.** -/
theorem wrap_state (md : Meta) (m : SMod σ) (h : md.memFree = true) (name : String)
    (vs : List Val) :
    (wrap md).callExport m.inst name (vs.map PVal.val) = specState md m name vs := by
  rw [wrap_memFree _ md h, spec_state md m h]

/-- **The thin wrapper over a stateful module is state passing.** -/
theorem thinComp_state (md : Meta) (m : SMod σ) (h : md.memFree = true) (r name : String)
    (vs : List Val) :
    (thinComp md r).callExport m.inst name (vs.map PVal.val) = specState md m name vs := by
  rw [Silmaril.Wasm.Jco.thinComp_callExport, Silmaril.Wasm.Jco.canonSpec_eq_spec_memFree _ _ r h,
    spec_state md m h]

/-- **The IR strategy of a stateful module contains exactly the plays it answers.** -/
theorem mem_sem_iff (m : SMod σ) (qs : List m.Q) (rs : List (Option Payload))
    (hlen : rs.length = qs.length) :
    m.plays qs rs ∈ (smodSem σ).sem m ↔ rs = (m.answers m.init qs).1 :=
  Silmaril.Proofs.Wasm.Jco.Bridge.State.mem_sem_iff m qs rs hlen

/-- **The machine's answer is the instance's result.** -/
theorem inst_ok (m : SMod σ) (i : Fin m.exports.length) (xs ys : List Flat) (s s' : σ) :
    m.inst.call (m.exports[i]).1 xs s (.ok ys s') ↔ m.ans (i, .flat xs) s = (some (.flat ys), s') :=
  Silmaril.Proofs.Wasm.Jco.Bridge.State.inst_ok m i xs ys s s'

/-- **The machine traps exactly when the instance does.** -/
theorem inst_trap (m : SMod σ) (i : Fin m.exports.length) (xs : List Flat) (s : σ) :
    m.inst.call (m.exports[i]).1 xs s .trap ↔ (m.ans (i, .flat xs) s).1 = none :=
  Silmaril.Proofs.Wasm.Jco.Bridge.State.inst_trap m i xs s

/-- A pure module as a stateful one computes `pureCall`. -/
theorem stateCall_toS (m : PMod) (s : Silmaril.Wasm.Jco.Sig) (vs : List Val) :
    stateCall m.toS s vs () = (pureCall m s vs).map fun r => (r, ()) := by
  unfold stateCall pureCall
  cases checkLower (s.params.map PTy.toVal) vs with
  | none => rfl
  | some xs =>
    simp only [Option.bind_some, SMod.callN, PMod.callN, PMod.toS]
    by_cases hb : (m.exports.any fun x => x.1 == s.name) = true
    · simp only [hb, ↓reduceIte]
      cases m.fn s.name xs <;> simp
    · simp [hb]

/-- **The stateful bridge extends the pure one.** -/
theorem specState_toS (md : Meta) (m : PMod) : specState md m.toS = specPure md m := by
  funext name vs u o
  unfold specState specPure
  cases md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    show Silmaril.Wasm.Jco.RM.ofFun (stateCall m.toS s vs) u o =
      Silmaril.Wasm.Jco.RM.ofOption (pureCall m s vs) u o
    unfold Silmaril.Wasm.Jco.RM.ofFun
    rw [stateCall_toS]
    cases pureCall m s vs <;> rfl

end Silmaril.Wasm.Jco.Bridge
