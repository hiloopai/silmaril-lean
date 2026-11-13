module

public import Silmaril.Proofs.Wasm.Models.V10Mvp.Module
public import Silmaril.Wasm.Models.V10.Thms

/-!
# The point map of `v10own` lands in `core|v10`

`v10own` reaches Core 3.0 through Lime1 and 2.0 (`V10.v10_core_obs`): a 1.0 store is mapped to
Lime1 (`Store.mapCode Func.toLime`), then to 2.0 (`Store.toV2`), then to Core
(`V2.Execution.Store.toCore`). Every Wasm function of that Core store has a body in `v10`:

* `funcInst_v10`: the Core image of the 2.0 image of the Lime1 image of a 1.0 function
  instance has a body in `v10` (`Lime1.Func.toV2_toCore`, `V1.Func.toLime_toCore`,
  `Lime1Mvp.v10_expr_inFeat`);
* **`storeIn_v10_v2`**: the whole Core store is `Rt.StoreIn v10`;
* **`ptCore_dom_v10`**: for a point in the domain of `v10own`, the Core point
  `V2Core.ptCore (ptV2 p)` lies in the domain of `core|v10` (the induced host keeps functions
  and never throws).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Mvp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Mvp

variable {H : Type}

/-- The Core image of the 2.0 image of the Lime1 image of a 1.0 function instance runs `v10`
code. -/
theorem funcInst_v10 (fi : Silmaril.Wasm.Execution.Runtime.FuncInst Silmaril.Wasm.V1.Func H)
    {ci : Silmaril.Wasm.Execution.Core.FuncInst H}
    (h : Silmaril.Wasm.V2.Execution.FuncInst.toCore
        (Silmaril.Wasm.Execution.Runtime.FuncInst.toV2
          (fi.mapCode Silmaril.Wasm.V1.Func.toLime)) = some ci)
    {fn : Func} (hc : ci.code = .wasm fn) : Instr.insInFeatB v10 fn.body = true := by
  cases fi with
  | wasm t m c =>
    simp only [Silmaril.Wasm.Execution.Runtime.FuncInst.mapCode,
      Silmaril.Wasm.Execution.Runtime.FuncInst.toV2, Silmaril.Wasm.V2.Execution.FuncInst.toCore,
      Silmaril.Wasm.Lime1.Func.toV2_toCore, Option.map_some, Option.some.injEq] at h
    subst h
    cases hc
    rw [Silmaril.Wasm.V1.Func.toLime_toCore]
    exact v10_expr_inFeat c.body
  | host t h' =>
    simp only [Silmaril.Wasm.Execution.Runtime.FuncInst.mapCode,
      Silmaril.Wasm.Execution.Runtime.FuncInst.toV2, Silmaril.Wasm.V2.Execution.FuncInst.toCore,
      Option.some.injEq] at h
    subst h
    cases hc

/-- **The Core store `v10own` runs, through Lime1 and 2.0, is in `v10`.** -/
theorem storeIn_v10_v2 (s : Silmaril.Wasm.V1.Execution.Store H)
    {X : Silmaril.Wasm.Execution.Core.Store H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore
        (Silmaril.Wasm.Execution.Runtime.Store.toV2 (s.mapCode Silmaril.Wasm.V1.Func.toLime)) =
      some X) :
    Rt.StoreIn v10 X := by
  intro a ci fn ha hc
  obtain ⟨fs, hfs, rfl⟩ := Silmaril.Proofs.Wasm.Models.V2Core.toCore_eq_some.mp hX
  have hget := Silmaril.Wasm.V2.Execution.ToCoreSim.mapM_funcInst_getElem hfs a
  have ha' : fs[a]? = some ci := ha
  rw [ha'] at hget
  simp only [Silmaril.Wasm.Execution.Runtime.Store.toV2, List.getElem?_map,
    Silmaril.Wasm.Execution.Runtime.Store.mapCode_funcs_getElem?] at hget
  cases hfi : s.funcs[a]? with
  | none =>
    rw [hfi] at hget
    cases hget
  | some fi =>
    rw [hfi] at hget
    exact funcInst_v10 fi hget.symm hc

/-- **The Core point of a `v10own` point lies in the domain of `core|v10`.** -/
theorem ptCore_dom_v10 {p : Silmaril.Wasm.Models.V10.Pt H} (hp : Silmaril.Wasm.Models.V10.dom p) :
    coreDom v10 (Silmaril.Wasm.Models.V2Core.ptCore (Silmaril.Wasm.Models.V10.ptV2 p)) := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp
    (Silmaril.Proofs.Wasm.Models.V10.ptV2_dom hp).2.1
  rw [Silmaril.Wasm.Models.V2Core.ptCore_eq hX]
  exact ⟨storeIn_v10_v2 p.1 hX, Silmaril.Proofs.Wasm.Models.V2Core.keeps _,
    Silmaril.Proofs.Wasm.Models.V2Core.throwsIn v10 _⟩

end Silmaril.Proofs.Wasm.Models.V10Mvp
