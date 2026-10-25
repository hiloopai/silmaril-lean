module

public import Silmaril.Wasm.Execution.Core.Soundness.ConstEvalTyping

@[expose] public section

/-! # Directize: the cast of the call site succeeds

`call_indirect t y` casts the slot's reference to `(ref null y)`. When the slot holds
`ref.func a` and the function at `a` has the defined type `types[y]` of the instance, the
cast succeeds (`refOk_cast`). This is the cast fact of the Directize simulation
(`Binaryen/DirectizeRel.lean`, `DInv`).
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizeCast

open Execution.Core Validation

variable {H : Type}

/-- `$inst_reftype(mi, (ref null y))` when `y` names a type. -/
theorem instRef_typeIdx {mi : ModuleInst} {y : TypeIdx} {d : DefType}
    (h : mi.types[y.toNat]? = some d) :
    mi.instRef ⟨true, .typeIdx y⟩ = .ref true (.use (.dt d)) := by
  simp [ModuleInst.instRef, liftRef, liftHeap, liftTypeIdx, Ty.substAll, Ty.subst, Subst.all, h]

/-- **The cast fact.** -/
theorem refOk_cast {s : Store H} {a : Nat} {fi : FuncInst H} {mi : ModuleInst} {y : TypeIdx}
    (hf : s.funcs[a]? = some fi) (hy : mi.types[y.toNat]? = some fi.type) (hok : TyOk {} fi.type) :
    RefOk s (.func a) (mi.instRef ⟨true, .typeIdx y⟩) := by
  rw [instRef_typeIdx hy]
  exact .sub (.func hf) (.ref (.use (.dt hok))) (.refNull .heapRefl)

end DirectizeCast

end Silmaril.Wasm.Binaryen
