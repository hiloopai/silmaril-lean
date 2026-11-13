module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.CoreEval

/-!
# `$evalglobals` on the Core image of Lime1 globals

Lime1's `allocate?` evaluates every global initializer with the imported globals only (none
here) and allocates the globals with these values. Core 3.0's `$evalglobals` (`evalGlobals?`, as
run by `instantiateOnce?`) evaluates the images of the initializers and allocates each global
with its closed declared type. Typed initializers make the two agree (`evalGlobals_core`): the
Core store gains exactly the images of the Lime1 global instances.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm Silmaril.Wasm.Lime1
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst GlobalInst)

/-- The Lime1 global instances of globals with initializer values. -/
def globalInsts (gs : List Lime1.Global) (vals : List Value) : List GlobalInst :=
  List.zipWith (fun g v => GlobalInst.mk v g.type.mutability) gs vals

theorem closed_num (t : NumType) (σ : List Silmaril.Wasm.Validation.CTypeUse) :
    (Silmaril.Wasm.Validation.liftVal (.num t)).substAll σ = .num t := rfl

/-- **`$evalglobals` on the image of typed Lime1 initializers** allocates the images of the
Lime1 global instances. -/
theorem evalGlobals_core {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {H' : Type} :
    ∀ {gs : List Lime1.Global} {vals : List Value},
      gs.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr? s {} g.init) = some vals →
      (∀ g ∈ gs, ∀ v, Silmaril.Wasm.Lime1.Execution.constExpr? s {} g.init = some v →
        v.type = g.type.value) →
      ∀ (S : Silmaril.Wasm.Execution.Core.Store H') (F : Silmaril.Wasm.Execution.Core.Frame),
      ∃ F', Silmaril.Wasm.Execution.Core.evalGlobals? Silmaril.Wasm.Execution.Core.evalConst? S F
          (gs.map fun g => ⟨g.type.mutability, .num g.type.value⟩)
          (gs.map fun g => Lime1.Expr.toCore g.init) =
        some ({ S with globals := S.globals ++ (globalInsts gs vals).map GlobalInst.toCore }, F',
          vals.map Value.toCore)
  | [], vals, h, _, S, F => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨F, by simp [Silmaril.Wasm.Execution.Core.evalGlobals?, globalInsts]⟩
  | g :: gs, vals, h, hty, S, F => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    have hvt : v.type = g.type.value := hty g (by simp) v hv
    have hc := evalConst?_toCore (mod := {}) rfl hv S F
    obtain ⟨F', hF'⟩ := evalGlobals_core hvs (fun g' hg' => hty g' (by simp [hg']))
      (Silmaril.Wasm.Execution.Core.allocGlobal S ⟨g.type.mutability, .num g.type.value⟩
        v.toCore).1
      { F with module := { F.module with globals := F.module.globals ++
        [(Silmaril.Wasm.Execution.Core.allocGlobal S ⟨g.type.mutability, .num g.type.value⟩
          v.toCore).2] } }
    have hhead : GlobalInst.toCore ⟨v, g.type.mutability⟩ =
        ⟨⟨g.type.mutability, .num g.type.value⟩, v.toCore⟩ := by
      rw [← hvt]; rfl
    refine ⟨F', ?_⟩
    simp only [List.map_cons, Silmaril.Wasm.Execution.Core.evalGlobals?, hc, hF']
    simp only [Silmaril.Wasm.Execution.Core.allocGlobal, globalInsts, List.zipWith_cons_cons,
      List.map_cons, hhead, List.append_assoc, List.singleton_append]

end Silmaril.Proofs.Wasm.Component.Lime1Inst
