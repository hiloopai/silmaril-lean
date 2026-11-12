module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostD.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.Call

/-!
# Round 7, memory SIMD: `$hostcall` keyed on `storeVD` images

Round 5, pass 1 proved that `OpenRMRest`'s builtins `BM` answer no host call made from a store
with memory SIMD code (`Round7.MSPres.bm_hostcall_none`). `BD` (`Defs`) keys `$hostcall` on
`storeVD` images and encodes the outcomes by `storeVD`. This header proves that it removes that
obstruction:

* **`storeVD` is injective on typed store images** (`storeVD_inj_typed`), for an injective `hn`.
  Round 5 proved this of `storeV`. Here `instrToVD` is injective at good images
  (`instrToVD_inj`): off blocks and memory SIMD instructions it is `instrToV`, the four memory
  SIMD images are injective (`instrToVM_inj_memSimd`), and the block cases recurse.
* **Every host respects the `storeVD` encoding** at calls on typed store images
  (`hostRespectsDT_all`).
* **`BD` answers every host call on a typed `storeVD` image** (`hostcallD_typed`): its
  `$hostcall` is a list containing the `outcomeVD` image of every outcome, and only such images
  (`hostInvD_typed`). On a store with memory SIMD code `BM` answers nothing there
  (`bd_answers_bm_not`).
* `BD` is `BM` off `$hostcall` (`bd_call_of_ne`). Off memory SIMD code `hostArgsD` and `outcomeVD`
  are round 3's `Prims.hostArgs` and `outcomeV` (`hostArgsD_eq`, `outcomeVD_eq`).

**What is not proved here.** That `OpenRMRest`'s fields hold at `BD`. Changing the builtins
from `BM` to `BD` also moves every field already proved at `BM` (`typed`, the memory SIMD rules
`readMSD`/`stepMSD`), and each would need re-proving or a transfer lemma for builtins that agree
off `$hostcall`. Round 7's `VAgree` gives such a transfer at the evaluator level only for
`$vbytes_`, not at the declarative level.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostD

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (storeVD withVBytes instrToVD)

variable {H : Type}

/-- **`instrToVD` is injective at typed images.** -/
theorem instrToVD_inj_typed {B : Builtins} {i j : Instr}
    (hi : Round5.FwdRef2.InstrG B (instrToVD i)) (h : instrToVD i = instrToVD j) : i = j :=
  (Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.instrToVD_inj_and
    (Round5.FwdRef2.goodV_typed B)).1 i j hi h

/-- **`storeVD` is injective on stores with typed images**, for an injective `hn`. -/
theorem storeVD_inj_typed {B : Builtins} {hn : H → String} (hinj : Function.Injective hn)
    {s s' : Store H} (hs : TypedV (simEnv B) storeT (storeVD hn s))
    (h : storeVD hn s = storeVD hn s') : s = s' :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.storeVD_inj_typed hinj hs h

/-- **Every host respects the `storeVD` encoding** at calls on typed store images. -/
theorem hostRespectsDT_all {hn : H → String} (B : Builtins) (hinj : Function.Injective hn)
    (host : HostSemantics H) : HostRespectsDT (simEnv B) hn host :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.hostRespectsDT_all B hinj host

/-- **`BD` answers every host call on a typed `storeVD` image** with the `outcomeVD` images of
exactly the outcomes the host allows. -/
theorem hostcallD_typed {hn : H → String} {P : Profile} {host : HostSemantics H}
    (hinj : Function.Injective hn) (hf : HostFinite host) (h : H) (s : Store H) (vs : List Val)
    (hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s)) :
    ∃ os : List Value,
      Applies (simEnv (BD P hn host)) "hostcall" (hostArgsD hn h s vs) (.list os) ∧
      (∀ o, host h s vs o → outcomeVD hn o ∈ os) ∧
      ∀ x ∈ os, ∃ o, host h s vs o ∧ x = outcomeVD hn o :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.hostcallD_typed hf
    (Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.hostRespectsDT_all _ hinj host) h s vs hst

/-- **`BD` answers the host calls that `BM` cannot** (stores with memory SIMD code). -/
theorem bd_answers_bm_not {hn : H → String} {P : Profile} {host : HostSemantics H}
    (hinj : Function.Injective hn) (hf : HostFinite host) (h : H) {s : Store H}
    (hs : ¬ Round6.MemSimd.StoreMS s) (vs : List Val)
    (hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s)) :
    (∃ os : List Value,
      Applies (simEnv (BD P hn host)) "hostcall" (hostArgsD hn h s vs) (.list os) ∧
      ∀ o, host h s vs o → outcomeVD hn o ∈ os) ∧
    (withVBytes (Prims.builtins P hn host)).call "hostcall" (hostArgsD hn h s vs) = none :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.bd_answers_bm_not hinj hf h hs vs hst

/-- `BD` is `BM` off `$hostcall`. -/
theorem bd_call_of_ne {hn : H → String} {P : Profile} {host : HostSemantics H} {x : IL.Id}
    (hx : x ≠ "hostcall") (ws : List ArgV) :
    (BD P hn host).call x ws = (withVBytes (Prims.builtins P hn host)).call x ws :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.bd_call_of_ne hx ws

/-! The axiom audit. -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostD.storeVD_inj_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storeVD_inj_typed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostD.hostcallD_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hostcallD_typed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostD.bd_answers_bm_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bd_answers_bm_not

end Silmaril.Wasm.SpecTec.Sim.Round7.HostD
