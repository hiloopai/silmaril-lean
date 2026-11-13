module

public import Silmaril.Wasm.Jco.Bridge.StateFix.Defs
public import Silmaril.Proofs.Wasm.Jco.Bridge.StateFix

/-!
# The stateful component bridge, restated: theorems

Proofs in `Silmaril.Proofs.Wasm.Jco.Bridge.StateFix`.

* `compLTS_eq`: `compLTS md m` is the answering machine `ansLTS (compAns md m) m.init`.
* `mem_ans_iff`: a play of questions and answers is in the strategy of an answering machine
  exactly when the answers are the machine's.
* **`simpleComp_state_of_S`**: the restated target `SimpleCompStateS` gives the original
  statement of `SimpleCompState` on every module whose returned calls lift
  (`LiftTotal`), where the two answers agree (`compAnsS_eq`).
* **`bump_differs`**: on `bumpMod` (a lift failure that changes the state) the strategies of
  `compLTS` and `compLTSS` differ: after a first call that traps, the second answers `none`
  in `compLTS` and `7` in `compLTSS`.
* **`not_simpleComp_state_of_S`**: so `SimpleCompStateS` and `SimpleCompState` are
  not both true. The original target holds only if the IR rolled the core instance back on a
  lift trap, which it does not (`SMod.Step.ret`); the restated one is the one to prove.

Both targets stay open; the results here are conditional on `SimpleCompStateS`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco (Meta)

variable {σ : Type}

theorem compLTS_eq (md : Meta) (m : SMod σ) : compLTS md m = ansLTS (compAns md m) m.init :=
  Silmaril.Proofs.Wasm.Jco.Bridge.StateFix.compLTS_eq md m

theorem compAnsS_eq (md : Meta) (m : SMod σ) (h : LiftTotal md m) :
    compAnsS md m = compAns md m :=
  Silmaril.Proofs.Wasm.Jco.Bridge.StateFix.compAnsS_eq md m h

/-- **The strategy of an answering machine contains exactly the plays it answers.** -/
theorem mem_ans_iff (f : sigU.Op → σ → Option Payload × σ) (s₀ : σ) (qs : List sigU.Op)
    (rs : List (Option Payload)) (hlen : rs.length = qs.length) :
    ansPlays qs rs ∈ Strategy.ofLTS (ansLTS f s₀) ↔ rs = (ansList f s₀ qs).1 :=
  Silmaril.Proofs.Wasm.Jco.Bridge.StateFix.mem_ans_iff f s₀ qs rs hlen

/-- **The restated target gives the original one on modules whose results lift.** -/
theorem simpleComp_state_of_S (hS : SimpleCompStateS) (md : Meta) (m : SMod σ)
    (hf : md.memFree = true) (hl : LiftTotal md m) :
    (Silmaril.Wasm.Jco.Fuse.simpleComp [] (Meta.iface md) m).denU
        (Silmaril.Wasm.Jco.Fuse.baseSem (smodSem σ)) = Strategy.ofLTS (compLTS md m) := by
  rw [hS σ md m hf, compLTSS, compAnsS_eq md m hl, compLTS_eq]

theorem bumpMeta_memFree : bumpMeta.memFree = true := rfl

/-- **The two machines differ on `bumpMod`.** -/
theorem bump_differs :
    Strategy.ofLTS (compLTS bumpMeta bumpMod) ≠ Strategy.ofLTS (compLTSS bumpMeta bumpMod) :=
  Silmaril.Proofs.Wasm.Jco.Bridge.StateFix.bump_differs

/-- **The restated and the original target are not both true.** -/
theorem not_simpleComp_state_of_S (hS : SimpleCompStateS) : ¬ SimpleCompState :=
  fun h => bump_differs ((h Bool bumpMeta bumpMod bumpMeta_memFree).symm.trans
    (hS Bool bumpMeta bumpMod bumpMeta_memFree))

end Silmaril.Wasm.Jco.Bridge

/--
info: 'Silmaril.Wasm.Jco.Bridge.not_simpleComp_state_of_S' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Bridge.not_simpleComp_state_of_S
