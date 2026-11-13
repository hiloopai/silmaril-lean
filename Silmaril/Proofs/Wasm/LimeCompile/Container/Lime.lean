module

public import Silmaril.Wasm.LimeCompile.Container.Defs
public import Silmaril.Proofs.Wasm.LimeCompile.Select.Inv

/-!
# The container compiler on Lime1 images

Lime1 code has only the untyped `select`, whose Core image is `select none`, so erasure fixes the
Core image of every Lime1 module (`selM_toCore`), and the compiler reads it back exactly
(`compile_toCore`). The types of a Lime1 image are single final function types over numeric
value types (`types_toCore`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Container

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Select Silmaril.Wasm.LimeCompile.Container
open Silmaril.Proofs.Wasm.LimeCompile.Select

/-- Erasure fixes the Core image of Lime1 code. -/
theorem selL_toCore (b : Lime1.Expr) : selL (Lime1.Expr.toCore b) = Lime1.Expr.toCore b := by
  cases b with
  | nil => rfl
  | cons i b =>
    have hb : selL (Lime1.Expr.toCore b) = Lime1.Expr.toCore b := selL_toCore b
    show selI (Lime1.Instr.toCore i) :: selL (Lime1.Expr.toCore b) =
      Lime1.Instr.toCore i :: Lime1.Expr.toCore b
    rw [hb]
    cases i with
    | block t body => rw [Lime1.Instr.toCore, selI_block, selL_toCore body]
    | loop t body => rw [Lime1.Instr.toCore, selI_loop, selL_toCore body]
    | if_ t b₁ b₂ => rw [Lime1.Instr.toCore, selI_if, selL_toCore b₁, selL_toCore b₂]
    | _ => rfl
termination_by sizeOf b

theorem selFn_toCore (f : Lime1.Func) : selFn (Lime1.Func.toCore f) = Lime1.Func.toCore f :=
  congrArg (fun b => (⟨f.type, f.locals.map V1.ValType.toCore, b⟩ : Func)) (selL_toCore f.body)

/-- **Erasure fixes the Core image of a Lime1 module.** -/
theorem selM_toCore (L : Lime1.Module) : selM L.toCore = L.toCore := by
  simp only [selM, Lime1.Module.toCore, List.map_map, Function.comp_def, selFn_toCore]

/-- **The compiler is the identity on Lime1 images**: it reads back the Lime1 module. -/
theorem compile_toCore (L : Lime1.Module) : compile L.toCore = some L := by
  rw [compile, selM_toCore, Lime1.Module.ofCore?_toCore]

theorem compile_of_eq {m : Module} {L : Lime1.Module} (h : L.toCore = selM m) :
    compile m = some L := by
  rw [compile, ← h, Lime1.Module.ofCore?_toCore]

/-- The types of a Lime1 image are single final function types over numeric value types. -/
theorem types_toCore (L : Lime1.Module) :
    ∀ rt ∈ L.toCore.types, ∃ ft : V1.FuncType, rt = ft.toCoreRec := by
  intro rt hrt
  obtain ⟨ft, -, rfl⟩ := List.mem_map.mp hrt
  exact ⟨ft, rfl⟩

end Silmaril.Proofs.Wasm.LimeCompile.Container
