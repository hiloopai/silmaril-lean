module

public import Silmaril.Wasm.Link.Recipe

/-! # Identity relocation keeps provider code unchanged

The linker uses the same partial rewrite to enforce its supported instruction
fragment on the provider. If that identity rewrite succeeds, it preserves the
source function, including nested blocks, exactly.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.Identity

@[simp] theorem shift_zero {kind : IndexKind} (i : Idx kind) :
    shiftIdx? 0 i = some i := by simp [shiftIdx?]

@[simp] theorem function_identity (i : FuncIdx) :
    function? Recipe.identity i = some i := by simp [function?, Recipe.identity]

@[simp] theorem heap_zero (h : HeapType) : heap? 0 h = some h := by
  cases h <;> simp [heap?]

@[simp] theorem ref_zero (r : RefType) : refType? 0 r = some r := by simp [refType?]

@[simp] theorem val_zero (v : ValType) : valType? 0 v = some v := by
  cases v <;> simp [valType?]

@[simp] theorem vals_zero (vs : List ValType) : vs.mapM (valType? 0) = some vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [List.mapM_cons, ih]

@[simp] theorem block_zero (t : BlockType) : blockType? 0 t = some t := by
  cases t <;> simp [blockType?]

private theorem mapM_eq_map {α β : Type} {f : α → Option β} {g : α → β}
    (hf : ∀ {a b}, f a = some b → b = g a) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys = xs.map g := by
  have hr := Validation.List.mapM_some_forall₂ hf h
  clear h
  induction hr with
  | nil => rfl
  | cons hab _ ih => simp [hab, ih]

/-- Successful identity relocation preserves every supported instruction,
including recursively rewritten branch and loop bodies. -/
theorem instruction_identity (i i' : Instr)
    (h : instruction? Recipe.identity i = some i') : i' = i := by
  cases hi : i with
  | block t body =>
    rw [hi] at h
    simp only [instruction?, Recipe.identity, block_zero, Option.bind_eq_bind, Option.bind_some,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨body', hb, rfl⟩ := h
    have he := mapM_eq_map (g := fun a => a.val)
      (fun {a b} h => instruction_identity a.val b h) hb
    simpa using congrArg (Instr.block t) he
  | loop t body =>
    rw [hi] at h
    simp only [instruction?, Recipe.identity, block_zero, Option.bind_eq_bind, Option.bind_some,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨body', hb, rfl⟩ := h
    have he := mapM_eq_map (g := fun a => a.val)
      (fun {a b} h => instruction_identity a.val b h) hb
    simpa using congrArg (Instr.loop t) he
  | if_ t yes no =>
    rw [hi] at h
    simp only [instruction?, Recipe.identity, block_zero, Option.bind_eq_bind, Option.bind_some,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨yes', hy, no', hn, rfl⟩ := h
    have hey := mapM_eq_map (g := fun a => a.val)
      (fun {a b} h => instruction_identity a.val b h) hy
    have hen := mapM_eq_map (g := fun a => a.val)
      (fun {a b} h => instruction_identity a.val b h) hn
    simpa using congrArg₂ (Instr.if_ t) hey hen
  | select types =>
    rw [hi] at h
    cases types <;> simp [instruction?, Recipe.identity] at h <;> exact h.symm
  | _ =>
    rw [hi] at h
    simpa [instruction?, Recipe.identity, function?] using h.symm
termination_by sizeOf i
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem a.property
  all_goals simp_all
  all_goals omega

theorem instructions_identity {body body' : List Instr}
    (h : instructions? Recipe.identity body = some body') : body' = body := by
  simpa only [List.map_id] using mapM_eq_map (g := id) (fun h => instruction_identity _ _ h) h

theorem func_identity {f f' : Func} (h : func? Recipe.identity f = some f') : f' = f := by
  simp only [func?, Recipe.identity, shift_zero, vals_zero, Option.bind_eq_bind, Option.bind_some,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨body, hb, rfl⟩ := h
  rw [instructions_identity hb]

theorem global_identity {g g' : Global} (h : global? Recipe.identity g = some g') : g' = g := by
  simp only [global?, Recipe.identity, val_zero, Option.bind_eq_bind, Option.bind_some,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨body, hb, rfl⟩ := h
  rw [instructions_identity hb]

theorem provider_funcs {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) :
    w.providerFuncs = provider.funcs := by
  simpa only [List.map_id] using mapM_eq_map (g := id) func_identity w.providerFuncsRewrite

theorem provider_globals {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) :
    w.providerGlobals = provider.globals := by
  simpa only [List.map_id] using mapM_eq_map (g := id) global_identity w.providerGlobalsRewrite

end Silmaril.Wasm.Link.GC.Identity
