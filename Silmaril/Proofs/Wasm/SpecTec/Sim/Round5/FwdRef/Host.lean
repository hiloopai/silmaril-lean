module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.Defs

/-!
# Round 5, pass 2, track fwdref: `HostRespects` fails for a finite `HostOk` host

`Prims.HostRespects hn host` asks that two host calls whose SpecTec images agree have outcomes
with the same images. With `hn` injective it would follow from injectivity of `storeV` and
`valV` (`valV` is injective, `Typing.valV_injective`), but **`storeV` is not injective**:
`instrToV` sends every instruction outside `Equiv.instrV`'s table to the junk value `.tuple []`,
for example `i32.extend32_s` and `i32.extend64_s` (`intUnOp .i32 (.extend .i32)`,
`intUnOp .i32 (.extend .i64)`, both invalid). The two stores `junkStore .i32` and
`junkStore .i64`, each holding one Wasm function whose body is one of them, differ but have the
same image (`storeV_junkStore`).

`HostOk` constrains a host only at stores that hold a host function (and are `StoreOk`), so the
host `junkHost`, which diverges everywhere except at `junkStore .i64` (where it has no outcome), is
finite and `HostOk`, yet it does not respect the encoding (`not_hostRespects_junkHost`). Hence
`Round5.Int.Open`, which has `HostRespects` as a field, fails for it at every profile
(`not_open_junkHost`), and the hypothesis of `Round5.Int.wholeStepValidOk_of_open` is
unsatisfiable (`not_open_all`). The restated target itself is not refuted by this: only
configurations whose store holds a host function call the host, and the junk stores hold none.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-- The function whose body is the one invalid instruction `i32.extend{8·|p|}_s` at width `p`. -/
def junkFunc (p : PackSize) : FuncInst Unit :=
  ⟨.defn (.group .nil) 0, {}, .wasm ⟨⟨0⟩, [], [.intUnOp .i32 (.extend p)]⟩⟩

/-- The store holding only `junkFunc p`. -/
def junkStore (p : PackSize) : Store Unit := { funcs := [junkFunc p] }

/-- `i32.extend32_s` and `i32.extend64_s` are both sent to the junk value. -/
theorem instrToV_junk : instrToV (.intUnOp .i32 (.extend .i32)) =
    instrToV (.intUnOp .i32 (.extend .i64)) := rfl

/-- The two junk stores differ. -/
theorem junkStore_ne : junkStore .i32 ≠ junkStore .i64 := by
  intro h
  have h' := congrArg (fun s : Store Unit => s.funcs.map fun fi => match fi.code with
    | .wasm fn => fn.body
    | .host _ => []) h
  simp [junkStore, junkFunc] at h'

/-- **`storeV` is not injective**: the two junk stores have the same image. -/
theorem storeV_junkStore (hn : Unit → String) :
    storeV hn (junkStore .i32) = storeV hn (junkStore .i64) := by
  simp only [storeV, junkStore, junkFunc, funcInstV, instrsToV, instrToV_junk, List.map_cons,
    List.map_nil]

/-- The host that diverges at every store but `junkStore .i64`, where it has no outcome. -/
def junkHost : HostSemantics Unit := fun _ s _ o => o = .diverged ∧ s ≠ junkStore .i64

theorem hostFinite_junkHost : HostFinite junkHost := by
  intro h s vs
  by_cases hs : s = junkStore .i64
  · exact ⟨[], fun o => by simp [junkHost, hs]⟩
  · exact ⟨[.diverged], fun o => by simp [junkHost, hs]⟩

/-- `junkStore .i64` holds no host function. -/
theorem no_host_junkStore {fi : FuncInst Unit} {h : Unit} (hfi : fi ∈ (junkStore .i64).funcs)
    (hc : fi.code = .host h) : False := by
  simp only [junkStore, List.mem_singleton] at hfi
  subst hfi
  simp [junkFunc] at hc

/-- **`junkHost` is `HostOk`**: wherever it is called on a store holding a host function, it
diverges. -/
theorem hostOk_junkHost : HostOk junkHost := by
  intro s fi h vs ps rs _ hfi hc _ _
  have hs : s ≠ junkStore .i64 := by
    rintro rfl
    exact no_host_junkStore hfi hc
  exact ⟨⟨.diverged, rfl, hs⟩, fun out hout => by
    obtain ⟨rfl, -⟩ := hout
    trivial⟩

/-- **`junkHost` does not respect the encoding**, at any `hn`. -/
theorem not_hostRespects_junkHost (hn : Unit → String) : ¬ Prims.HostRespects hn junkHost := by
  intro hr
  have hargs : Prims.hostArgs hn () (junkStore .i32) [] = Prims.hostArgs hn () (junkStore .i64) [] := by
    simp only [Prims.hostArgs, storeV_junkStore]
  obtain ⟨o', ho', -⟩ := hr () () _ _ [] [] hargs .diverged ⟨rfl, junkStore_ne⟩
  exact ho'.2 rfl

/-- **`Round5.Int.Open` fails for `junkHost`**, at every profile. -/
theorem not_open_junkHost (hn : Unit → String) (P : Profile) :
    ¬ Round5.Int.Open hn P junkHost := fun O => not_hostRespects_junkHost hn O.hostRespects

/-- **The hypothesis of `Round5.Int.wholeStepValidOk_of_open` is unsatisfiable**: it fails at the
injective `Pos.hnU` and the finite, `HostOk` host `junkHost`. -/
theorem not_open_all :
    ¬ ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Round5.Int.Open hn (Profile.spec nd r) host :=
  fun h => not_open_junkHost Pos.hnU _ (h Unit Pos.hnU Pos.hnU_injective junkHost
    hostFinite_junkHost hostOk_junkHost false {})

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef
