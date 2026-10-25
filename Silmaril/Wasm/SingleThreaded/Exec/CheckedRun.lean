module

public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck

@[expose] public section

/-! # Checked validate-instantiate-run

`runChecked?` validates the module, checks the imports against the store, then
instantiates and interprets. The end-to-end theorems need only `StoreOk s`.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-- Validate, check imports, instantiate and run. -/
def runChecked? (o : GrowOracle) (n : Nat) (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Config H × Bool × Option Result) :=
  match validate? m with
  | none => none
  | some mt =>
    if externAddrsOk? s xas mt.imports then EndToEnd.runModule? (interpHead o) n s m xas
    else none

namespace CheckedRun

variable {o : GrowOracle}

theorem runChecked?_inv {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr}
    {res : Config H × Bool × Option Result} (h : runChecked? o n s m xas = some res) :
    (∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) ∧
      EndToEnd.runModule? (interpHead o) n s m xas = some res := by
  unfold runChecked? at h
  split at h
  · cases h
  · rename_i mt hv
    split at h
    · rename_i hx
      exact ⟨⟨mt.exports, mt.imports, validate?_sound hv, externAddrsOk?_sound hx⟩, h⟩
    · cases h

/-- **Soundness** of the checked pipeline. -/
theorem runChecked?_sound {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr}
    (hs : StoreOk s) {c' : Config H} {b : Bool} {r : Option Result}
    (h : runChecked? o n s m xas = some (c', b, r)) :
    (∃ c₀, Instantiate (profile o) divHost s m xas c₀ ∧ Steps (profile o) divHost c₀ c') ∧
      ConfigOk c' [] ∧ (∀ res, r = some res → c'.code = res.toAdmin) :=
  let ⟨hv, h⟩ := runChecked?_inv h
  EndToEnd.runModuleI?_sound hs hv h

theorem runChecked?_steps_noHost {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr}
    (hs : StoreOk s) {c' : Config H} {b : Bool} {r : Option Result}
    (h : runChecked? o n s m xas = some (c', b, r)) :
    ∃ c, instantiateInit? s m xas = some c ∧ Steps (profile o) noHost c c' :=
  let ⟨hv, h⟩ := runChecked?_inv h
  EndToEnd.runModuleI?_steps_noHost hs hv h

/-- A stopped checked result is terminal or can only step through the host. -/
theorem runChecked?_stopped {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr}
    (hs : StoreOk s) {c' : Config H} {r : Option Result}
    (h : runChecked? o n s m xas = some (c', true, r)) :
    (c'.Terminal ∨ ∃ c'', Step (profile o) divHost c' c'') ∧
      ∀ c'', ¬ Step (profile o) noHost c' c'' :=
  let ⟨hv, h⟩ := runChecked?_inv h
  EndToEnd.runModuleI?_stopped hs hv h

/-- **Completeness** of the checked pipeline. -/
theorem runChecked?_complete {s : Store H} {m : Module} {xas : List ExternAddr}
    {mt : CModuleType} (hs : StoreOk s) (hm : validate? m = some mt)
    (hx : List.Forall₂ (ExternAddrOk s) xas mt.imports)
    {c c' : Config H} (hc : instantiateInit? s m xas = some c)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, runChecked? o n s m xas = some (c', true, c'.outcome?) := by
  obtain ⟨n, hn⟩ := EndToEnd.runModuleI?_complete hs
    ⟨mt.exports, mt.imports, validate?_sound hm, hx⟩ hc h hnf
  refine ⟨n, ?_⟩
  unfold runChecked?
  rw [hm]
  simp only [externAddrsOk?_complete hs hx, ↓reduceIte, hn]

end CheckedRun

end Silmaril.Wasm.SingleThreaded.Exec
