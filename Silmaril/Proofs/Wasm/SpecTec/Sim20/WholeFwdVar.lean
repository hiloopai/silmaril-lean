module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeValTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdTop
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestVar

/-!
# The restricted forward 2.0 half, widened to `local.set` and `global.set`

`WholeFwdTop` covers the growth, table-set and drop rules. `Step` 4 (`local.set`) and 5
(`global.set`) quantify `val : val`, and pass 3 stopped there because the IL typing of V2 values
was not proved for `simEnv20`. `WholeValTyping.typedV_val20` proves it, so the per-rule `iff`s of
track F3 (`State.localSet_iff`, `State.globalSet_iff`) now fire forward with no hypothesis left:

* `fires_localSet`, `fires_globalSet`: each fires from the image of V2's left-hand side to the
  image of V2's successor, from a typed state, at any builtins;
* `TopVarStep20 P`: `TopStep20 P` plus V2's `localSet` and `globalSet`, with V2's premises
  (`TopVarStep20.step` embeds it in `Step`);
* **`Task.wholeStepTopVar20`** (proved, `wholeStepTopVar20`): `Task.wholeStepTop20` with
  `TopVarStep20` for `TopStep20`, at `growB`.

`Pure.drop_fires` and the `select` rules take the same hypothesis; it is discharged by
`typedV_val20` there too (`drop_iff20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB FiresB)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The two rules, forward -/

/-- **`Step/local.set` fires forward** at the image of V2's `localSet`. -/
theorem fires_localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) (hlt : x.toNat < f.locals.length) :
    Fires (simEnv20 B) "Step" 4 (.tuple [configV hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩,
      configV hn ⟨s, f.setLocal x v, []⟩]) :=
  firesB_step20_iff.1 ((State.localSet_iff B hn hlt hz (typedV_val20 v) (typedV_idx20 x)).2 rfl)

/-- **`Step/global.set` fires forward** at the image of V2's `globalSet`. -/
theorem fires_globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : Nat}
    {g : GlobalInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
    Fires (simEnv20 B) "Step" 5 (.tuple [configV hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩,
      configV hn ⟨s.setGlobalInst a { g with value := v }, f, []⟩]) :=
  firesB_step20_iff.1
    ((State.globalSet_iff B hn ha hg hz (typedV_val20 v) (typedV_idx20 x)).2 rfl)

/-- **`Step_pure/drop` is `PureStep.drop`** at every V2 value: pass 5's `Pure.drop_iff`, with
its typing hypothesis discharged. -/
theorem drop_iff20 (v : Val) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 2
        (.tuple [.list (adminsToV [v.toAdmin, .plain .drop]), w]) ↔
      w = .list (adminsToV []) :=
  Pure.drop_iff B (typedV_val20 v)

/-! ## The fragment and the target -/

/-- **The top-level steps of V2 the forward half covers, with the variable writes**: `TopStep20`
and V2's `localSet` and `globalSet`, with their premises. -/
inductive TopVarStep20 (P : Profile) : Config H → Config H → Prop where
  | top {c c' : Config H} (h : TopStep20 P c c') : TopVarStep20 P c c'
  | localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
      (hx : x.toNat < f.locals.length) :
      TopVarStep20 P ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩
  | globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : GlobalAddr}
      {gi : GlobalInst} (ha : f.module.globalAddr? x = some a) (hg : s.globalInst? a = some gi) :
      TopVarStep20 P ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩
        ⟨s.setGlobalInst a { gi with value := v }, f, []⟩

/-- Every step of the fragment is a V2 step. -/
theorem TopVarStep20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : TopVarStep20 P c c') : Step P host c c' := by
  cases h with
  | top h => exact h.step
  | localSet hx => exact .localSet hx
  | globalSet ha hg => exact .globalSet ha hg

/-- **The forward half on the fragment**, at builtins answering V2's growth. -/
theorem fwd_topVarStep20 {P : Profile} (hG : GrowCalls20 B) {c c' : Config H}
    (hc : Typed20 (simEnv20 B) hn c) (hw : WholePages c.store) (h : TopVarStep20 P c c') :
    SStepB (simEnv20 B) (configV hn c) (configV hn c') := by
  have hz := typedV_state_of_typed20 hc
  cases h with
  | top h => exact fwd_topStep20 hG hc hw h
  | localSet hx => exact sstepB_of_fires20 (fires_localSet hz hx)
  | globalSet ha hg => exact sstepB_of_fires20 (fires_globalSet hz ha hg)

/-- **`Task.wholeStepTop20` with the variable writes** (proved below). -/
def Task.wholeStepTopVar20 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
      GrowLike20 (Profile.spec nd r) B ∧
      (∀ c c' : Config H, Typed20 (simEnv20 B) hn c → WholePages c.store →
        TopVarStep20 (Profile.spec nd r) c c' →
        SStepB (simEnv20 B) (configV hn c) (configV hn c')) ∧
      (∀ (c : Config H) (w : Value), GoodW c → SStepB (simEnv20 B) (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c')

/-- **`Task.wholeStepTopVar20` holds**, at `growB`. -/
theorem wholeStepTopVar20 : Task.wholeStepTopVar20 := by
  intro H hn _ host nd r
  refine ⟨growB (Profile.spec nd r), growLike20_growB _, fun c c' hc hw h => ?_,
    fun c w hg hs => wholeStepBwdW_growB nd r c w hg hs⟩
  exact fwd_topVarStep20 (growCalls20_growB _) hc hw h

end Silmaril.Wasm.SpecTec.Sim20.Whole
