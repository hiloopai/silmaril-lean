module

public import Silmaril.Wasm.Binaryen.InlDet
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

@[expose] public section

/-! # Instantiating a module with one function's code replaced

`allocModule?_set`: allocating a module whose defined function `g` has new code of the
same type allocates the same store, except for the code of that function. The
instantiations of such modules therefore correspond (`instantiate_set`).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type}

theorem modifyAt_const_eq_set {α : Type} (a : α) : ∀ (n : Nat) (l : List α),
    modifyAt (fun _ => a) n l = l.set n a
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | n + 1, b :: l => by simp [modifyAt, modifyAt_const_eq_set a n l]

theorem lower_setFunc (m : BModule) (g : Nat) (nf : BFunc) :
    (m.setFunc g nf).lower =
      { m.lower with funcs := m.lower.funcs.set g (nf.mapBody BExpr.lowerList) } := by
  simp only [BModule.lower, BModule.setFunc, modifyAt_const_eq_set, List.map_set]

theorem mapM_set_eq {α β : Type} (T : α → Option β) {a b : α} (hab : T b = T a) :
    ∀ (l : List α) (g : Nat), l[g]? = some a → (l.set g b).mapM T = l.mapM T
  | [], _, h => by simp at h
  | x :: l, 0, h => by
    simp at h
    subst h
    simp [List.mapM_cons, hab]
  | x :: l, g + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [List.mapM_cons, mapM_set_eq T hab l g h]

theorem modify_append_len {α : Type} (l₁ l₂ : List α) (g : Nat) (f : α → α) :
    (l₁ ++ l₂).modify (l₁.length + g) f = l₁ ++ l₂.modify g f := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_modify]
  by_cases hj : j < l₁.length
  · rw [List.getElem?_append_left hj, List.getElem?_append_left hj]
    cases l₁[j]? <;> simp; omega
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_modify]
    have hiff : (l₁.length + g = j) ↔ (g = j - l₁.length) := by omega
    simp only [hiff]

theorem map_zip_set {α β γ : Type} (F : α × β → γ) (G : γ → γ) {b : β}
    (hG : ∀ a b₀, G (F (a, b₀)) = F (a, b)) :
    ∀ (as : List α) (bs : List β) (g : Nat),
      (as.zip (bs.set g b)).map F = ((as.zip bs).map F).modify g G
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: as, b₀ :: bs, 0 => by simp [hG]
  | a :: as, b₀ :: bs, g + 1 => by
    simp [map_zip_set F G hG as bs g]

/-- The function list with the code of address `a` replaced. -/
def setCode (fs : List (FuncInst H)) (a : Nat) (c : Func) : List (FuncInst H) :=
  fs.modify a fun fi => ⟨fi.type, fi.module, .wasm c⟩

/-- **Allocation with one function's code replaced.** -/
theorem allocModule?_set {s s' : Store H} {M : Module} {xas : List ExternAddr} {valsG : List Val}
    {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst} {g : Nat} {f₀ f₁ : Func}
    (hg : M.funcs[g]? = some f₀) (hty : f₁.type = f₀.type)
    (h : allocModule? s M xas valsG refsT refsE = some (s', mi)) :
    allocModule? s { M with funcs := M.funcs.set g f₁ } xas valsG refsT refsE =
      some (withFuncs s' (setCode s'.funcs (s.funcs.length + g) f₁), mi) := by
  obtain ⟨tagTypes, funcTypes, xi, ht, hf, hx, rfl, rfl⟩ := allocModule?_inv h
  have hf' : (M.funcs.set g f₁).mapM (fun fn => (allocTypes M.types)[fn.type.toNat]?) =
      some funcTypes := by
    rw [mapM_set_eq _ (by rw [hty]) M.funcs g hg]; exact hf
  unfold allocModule?
  simp only [Option.bind_eq_bind, List.length_set]
  simp only [ht, hf', Option.bind_some, allocMany_tag_eq, allocMany_global_eq, allocMany_mem_eq,
    allocMany_table_eq, allocMany_data_eq, allocMany_elem_eq, List.length_zip, List.length_map]
  simp only [hx, Option.bind_some, allocMany_func_eq, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq, and_true]
  simp only [withFuncs, setCode]
  congr 1
  rw [modify_append_len]
  congr 1
  exact map_zip_set _ _ (fun _ _ => rfl) _ _ _

theorem mapM_some_forall₂ {α β : Type} {T : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM T = some ys → List.Forall₂ (fun a b => T a = some b) l ys
  | [], ys, h => by simp at h; subst h; exact .nil
  | a :: l, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases ha : T a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM T with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h
        subst h
        exact .cons ha (mapM_some_forall₂ hl)

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {ys : List β}, List.Forall₂ R l ys → ∀ {j : Nat} {a : α}, l[j]? = some a →
      ∃ b, ys[j]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _, _, .cons _ t, j + 1, _, h => by simpa using forall₂_getElem? t (by simpa using h)

/-- What an instantiation allocates for the defined functions: they sit at `n₀ ..`. -/
structure FuncAlloc (M : Module) (xas : List ExternAddr) (c : Config H) (n₀ : Nat) : Prop where
  funcs : c.frame.module.funcs = ExternAddr.funcs xas ++ (List.range M.funcs.length).map (n₀ + ·)
  types : c.frame.module.types = allocTypes M.types
  code : ∀ j f, M.funcs[j]? = some f → ∃ d, (allocTypes M.types)[f.type.toNat]? = some d ∧
    c.store.funcs[n₀ + j]? = some ⟨d, c.frame.module, .wasm f⟩

theorem initial_set {s : Store H} {M : Module} {xas : List ExternAddr} {g : Nat} {f₁ : Func} :
    ModuleInst.initial s { M with funcs := M.funcs.set g f₁ } xas = ModuleInst.initial s M xas := by
  simp [ModuleInst.initial]

/-- **Instantiating a module with one function's code replaced.** -/
theorem instantiate_set {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {M : Module}
    {xas : List ExternAddr} {c : Config H} {g : Nat} {f₀ f₁ : Func} (hg : M.funcs[g]? = some f₀)
    (hty : f₁.type = f₀.type)
    (hval : ∀ mt, ModuleOk M mt → ModuleOk { M with funcs := M.funcs.set g f₁ } mt)
    (h : Instantiate P host s M xas c) :
    ∃ n₀ c', Instantiate P host s { M with funcs := M.funcs.set g f₁ } xas c' ∧
      c'.frame = c.frame ∧ c'.code = c.code ∧
      c'.store = withFuncs c.store (setCode c.store.funcs (n₀ + g) f₁) ∧ FuncAlloc M xas c n₀ := by
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁', f₂, f₃, valsG, refsT, refsE, mi, hG, hT,
    hE, hA, rfl⟩ := h
  have hA' := allocModule?_set hg hty hA
  obtain ⟨tagTypes, funcTypes, xi, -, hf, -, hmi, hs₄⟩ := allocModule?_inv hA
  refine ⟨s₃.funcs.length, ⟨withFuncs s₄ (setCode s₄.funcs (s₃.funcs.length + g) f₁),
    { module := mi }, _⟩, ⟨⟨xtE, xtI, hval _ hmt, hxas⟩, hbd, s₁, s₂, s₃, _, f₁', f₂, f₃, valsG,
      refsT, refsE, mi, by rw [initial_set]; exact hG, hT, hE, hA', rfl⟩, rfl, rfl, rfl, ?_⟩
  refine ⟨by rw [hmi], by rw [hmi], fun j f hj => ?_⟩
  obtain ⟨d, hd, hTd⟩ := forall₂_getElem? (mapM_some_forall₂ hf) hj
  refine ⟨d, hTd, ?_⟩
  have hz : (funcTypes.zip M.funcs)[j]? = some (d, f) := List.getElem?_zip_eq_some.mpr ⟨hd, hj⟩
  rw [hs₄]
  simp only
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map, hz]
  rfl

end Silmaril.Wasm.Binaryen.InlR
