module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Defs

/-!
# Round 7, memory SIMD: `$hostcall` keyed on `storeVD` images (definitions)

`OpenRMRest` fixes the builtins `BM = withVBytes (Prims.builtins P hn host)`. Their `$hostcall`
answers at `Prims.hostArgs hn h s vs`, whose store argument is round 3's `storeV hn s`, and lists
outcomes encoded by `storeV`. The round-7 target encodes configurations by `configVD`, whose store
is `storeVD hn s`. Round 5, pass 1 proved that `BM` answers no host call made from a store with
memory SIMD code (`Round7.MSPres.bm_hostcall_none`).

The definitions below key `$hostcall` on `storeVD` images instead:

* `hostArgsD hn h s vs`: the arguments of `$hostcall(hf, s, val*)` at `configVD`;
* `outcomeVD hn o`: the image of a host outcome, with its store encoded by `storeVD`;
* `hostcallCallD hn host`: at the image of some host call with finitely many outcomes, the
  `outcomeVD` images of the outcomes of a chosen such call;
* `BD P hn host`: `BM` with `$hostcall` answered by `hostcallCallD` (every other name as `BM`);
* `HostRespectsDT env hn host`: two host calls with the same `hostArgsD` image, the first on a
  store whose `storeVD` image is a typed `store`, have outcomes with the same `outcomeVD` images
  (round 5's `HostRespectsT` at `storeVD`);
* `StoreInjTD env hn`: `storeVD hn` is injective on stores with typed images.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostD

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (storeVD withVBytes)

variable {H : Type}

/-- The arguments of `$hostcall(hf, s, val*)` for a Core host call, with the store encoded by
`storeVD`. -/
def hostArgsD (hn : H → String) (h : H) (s : Store H) (vs : List Val) : List ArgV :=
  [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeVD hn s), .val (.list (vs.map valV))]

/-- `hostcallresult = RES store result | BOT`, with the store encoded by `storeVD`. -/
def outcomeVD (hn : H → String) :
    Silmaril.Wasm.Execution.Host.Outcome (Store H) Result → Value
  | .returned s r => .case "RES" (.tuple [storeVD hn s, resultV r])
  | .diverged => .case "BOT" (.tuple [])

/-- `$hostcall` keyed on `storeVD` images: at the image of some host call with finitely many
outcomes, the `outcomeVD` images of the outcomes of a chosen such call. -/
noncomputable def hostcallCallD (hn : H → String) (host : HostSemantics H) (ws : List ArgV) :
    Option Value :=
  open Classical in
  if h : ∃ p : H × Store H × List Val, ws = hostArgsD hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os then
    some (.list (h.choose_spec.2.choose.map (outcomeVD hn)))
  else none

/-- **`BM` with `$hostcall` keyed on `storeVD` images.** Every name other than `$hostcall` is
answered as by `withVBytes (Prims.builtins P hn host)`. -/
noncomputable def BD (P : Profile) (hn : H → String) (host : HostSemantics H) : Builtins :=
  ⟨fun x ws => if x = "hostcall" then hostcallCallD hn host ws
    else (withVBytes (Prims.builtins P hn host)).call x ws⟩

/-- **The host respects the `storeVD` encoding at calls on typed store images.** -/
def HostRespectsDT (env : Env) (hn : H → String) (host : HostSemantics H) : Prop :=
  ∀ (h h' : H) (s s' : Store H) (vs vs' : List Val), TypedV env storeT (storeVD hn s) →
    hostArgsD hn h s vs = hostArgsD hn h' s' vs' →
    ∀ o, host h s vs o → ∃ o', host h' s' vs' o' ∧ outcomeVD hn o = outcomeVD hn o'

/-- **`storeVD` is injective on stores with typed images.** -/
def StoreInjTD (env : Env) (hn : H → String) : Prop :=
  ∀ s s' : Store H, TypedV env storeT (storeVD hn s) → storeVD hn s = storeVD hn s' → s = s'

end Silmaril.Wasm.SpecTec.Sim.Round7.HostD
