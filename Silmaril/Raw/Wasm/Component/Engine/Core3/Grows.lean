module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs

public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.SingleThreaded.Exec.Status
public import Silmaril.Wasm.SingleThreaded.Interface

@[expose] public section

/-!
# Untyped store growth of the Core 3.0 machine

`Grows s s'` is the part of store extension that the component runtime observes
(`CoreEngine.Extends`, Engine/Laws.lean), stated for the concrete Core 3.0 store
`Execution.Core.Store` without any typing:

* the function instances of `s` are a prefix of those of `s'`;
* every memory of `s` still exists in `s'`, with the same address type and at least as many
  bytes (`memory.grow` only appends pages, stores keep the size);
* every table of `s` still exists in `s'`, with the same address type.

Unlike `Execution.Core.Extend` (the typed store extension of the soundness proof), `Grows`
needs no `StoreOk`: every reduction rule of the host-free machine grows the store
(`Step.grows`, one lemma per family; `Step.grows_of_host` for host relations that grow the
store), and so do runs (`Steps.grows`), head steps (`Head.grows`) and internal steps of the
single-threaded machine (`Internal.grows`). Allocation grows the store (`Grows.of_prefix`), and
so does typed extension (`Grows.of_extend`).

Callout statuses persist under `Grows`: `decompose?` reads the store only through
`hostArity?`, which is stable under function prefixes (`decompose?_prefix`); the code of a
thread is stable once its callee is allocated (`Thread.config_code_prefix`), and a thread
with a host-call redex has its callee allocated (`Thread.loaded_of_decompose?`). Hence
`statusC_callout_grows`, for any step function. The fields of `CoreEngine.Extends` over the
raw store functions are `Grows.funcType`, `Grows.memAddrType`, `Grows.memSize`,
`Grows.tableAddrType` and `Grows.status_callout_of` (for any status built from `statusC`
that is a callout only on `statusC` callouts).
-/

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## The relation -/

theorem Grows.addStruct (s : Store H) (si : StructInst) : Grows s (s.addStruct si) :=
  .of_eq rfl rfl rfl

theorem Grows.addArray (s : Store H) (ai : ArrayInst) : Grows s (s.addArray ai) :=
  .of_eq rfl rfl rfl

theorem Grows.setStructField (s : Store H) (a i : Nat) (fv : FieldVal) :
    Grows s (s.setStructField a i fv) := .of_eq rfl rfl rfl

theorem Grows.setArrayField (s : Store H) (a i : Nat) (fv : FieldVal) :
    Grows s (s.setArrayField a i fv) := .of_eq rfl rfl rfl

/-- Typed extension of function instances keeps them unchanged. -/
theorem extendFunc_eq {a b : FuncInst H} (h : ExtendFunc a b) : b = a := by
  obtain ⟨ht, hm, hw, hh⟩ := h
  rcases a with ⟨ta, ma, ca⟩
  rcases b with ⟨tb, mb, cb⟩
  dsimp only at ht hm hw hh
  subst ht hm
  cases ca with
  | wasm c => rw [hw c rfl]
  | host h => rw [hh h rfl]

/-- The typed store extension of the soundness proof (`Extend_store`) implies growth. -/
theorem Grows.of_extend {s s' : Store H} (h : Extend s s') : Grows s s' where
  funcs := List.prefix_iff_getElem?.mpr fun i hi => by
    obtain ⟨y, hy, he⟩ := h.funcs.2 i _ (List.getElem?_eq_getElem hi)
    rw [hy, extendFunc_eq he]
  mems a mi hm := by
    obtain ⟨mi', e, ha, -, -, hb⟩ := h.mems.2 a mi hm
    exact ⟨mi', e, ha.symm, hb⟩
  tables a ti ht := by
    obtain ⟨ti', e, ha, -⟩ := h.tables.2 a ti ht
    exact ⟨ti', e, ha.symm⟩

/-! ## Store accessors and growth of single instances -/

/-! ## Reduction families -/

section Variable

end Variable

section Table

end Table

section Memory

end Memory

section Reference

end Reference

section Aggregate

end Aggregate

/-! ## Steps, head steps, runs and internal steps -/

theorem Internal.grows {o : GrowOracle} {s s' : Store H} {t t' : Thread}
    (h : Internal o (s, t) (s', t')) : Grows s s' := by
  obtain ⟨f', code', -, h⟩ := h
  simpa [Thread.config_store] using Step.grows h

theorem Internal.steps_grows {o : GrowOracle} {x y : Store H × Thread}
    (h : Relation.ReflTransGen (Internal o) x y) : Grows x.1 y.1 := by
  induction h with
  | refl => exact Grows.refl _
  | @tail y z _ step ih =>
    obtain ⟨s₁, t₁⟩ := y
    obtain ⟨s₂, t₂⟩ := z
    exact ih.trans (Internal.grows step)

/-! ## Callouts persist -/

theorem Thread.Loaded.prefix {s s' : Store H} (h : s.funcs <+: s'.funcs) {t : Thread}
    (ht : Thread.Loaded s t) : Thread.Loaded s' t := by
  cases t with
  | pending a args =>
    simp only [Thread.Loaded] at ht ⊢
    exact Nat.lt_of_lt_of_le ht h.length_le
  | active => trivial

theorem Thread.config_frame_eq (s s' : Store H) (t : Thread) :
    (t.config s').frame = (t.config s).frame := by
  cases t <;> rfl

/-- Resuming a callout thread does not depend on functions allocated later. -/
theorem resume_prefix {s s' : Store H} (hg : s.funcs <+: s'.funcs) {t : Thread}
    {x : Ctx × Nat × H × List Val} (hd : decompose? s (t.config s).code = some x)
    (r : Silmaril.Wasm.SingleThreaded.CallResult) : resume s' t r = resume s t r := by
  obtain ⟨E, a, h, args⟩ := x
  unfold resume
  dsimp only
  rw [Thread.config_code_prefix hg (Thread.loaded_of_decompose? hd), decompose?_prefix hg hd,
    hd, Thread.config_frame_eq]

/-! ## What `CoreEngine.Extends` needs, over the raw store functions -/

end Silmaril.Wasm.Component.Engine.Core3
