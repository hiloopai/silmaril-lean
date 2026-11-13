module

public import Silmaril.Wasm.Models.FXRename.Defs

/-!
# The exception renaming is the identity below `n`

* `rnRef_below`, `rnVal_below`, `rnField_below`, `rnAdmins_below`, `rnFrame_below`: the
  renaming fixes everything whose exception addresses are below `n`;
* `rnAdmins_vals`, `rnAdmins_expression`, `rnAdmins_append`: the renaming on value code and on
  plain instructions;
* **`exnRen_addExn`**: a store whose exception addresses are all below `n = s.exns.length` is
  related by `ExnRen n` to itself with one more exception instance appended;
* `rnIdx_ne`, `rnIdx_injective`: the renaming avoids `n` and is injective.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRename

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXRename

theorem rnIdx_ne (n a : Nat) : rnIdx n a ≠ n := by
  unfold rnIdx
  split <;> omega

theorem rnIdx_injective (n : Nat) : Function.Injective (rnIdx n) := by
  intro a b h
  unfold rnIdx at h
  split at h <;> split at h <;> omega

theorem rnRef_below {n : Nat} : ∀ {r : Ref}, RefBelow n r → rnRef n r = r
  | .exn a, h => by simp [rnRef, rnIdx, show a < n from h]
  | .extern r, h => by rw [rnRef, rnRef_below (r := r) h]
  | .i31 _, _ => rfl
  | .null, _ => rfl
  | .struct _, _ => rfl
  | .array _, _ => rfl
  | .func _, _ => rfl
  | .host _, _ => rfl

theorem rnVal_below {n : Nat} {v : Val} (h : ValBelow n v) : rnVal n v = v := by
  cases v with
  | ref r => rw [rnVal, rnRef_below h]
  | num _ => rfl
  | vec _ => rfl

theorem rnField_below {n : Nat} {fv : FieldVal} (h : FieldBelow n fv) : rnField n fv = fv := by
  cases fv with
  | val v => rw [rnField, rnVal_below h]
  | pack _ _ => rfl

theorem locals_below {n : Nat} {ls : List (Option Val)} (h : ∀ o ∈ ls, ∀ v ∈ o, ValBelow n v) :
    ls.map (Option.map (rnVal n)) = ls := by
  conv_rhs => rw [← List.map_id ls]
  apply List.map_congr_left
  intro o ho
  cases o with
  | none => rfl
  | some v => rw [Option.map_some, rnVal_below (h _ ho v rfl), id]

mutual
theorem rnAdmin_below {n : Nat} : ∀ {a : Admin}, AdminBelow n a → rnAdmin n a = a
  | .label _ _ body, h => by rw [rnAdmin, rnAdmins_below (l := body) h]
  | .handler _ _ body, h => by rw [rnAdmin, rnAdmins_below (l := body) h]
  | .frame _ f body, h => by
    rw [rnAdmin, rnAdmins_below (l := body) h.2, locals_below h.1]
  | .ref r, h => by rw [rnAdmin, rnRef_below h]
  | .plain _, _ => rfl
  | .callRefType _, _ => rfl
  | .returnCallRefType _, _ => rfl
  | .trap, _ => rfl

theorem rnAdmins_below {n : Nat} : ∀ {l : List Admin}, AdminsBelow n l → rnAdmins n l = l
  | [], _ => rfl
  | a :: l, h => by rw [rnAdmins, rnAdmin_below h.1, rnAdmins_below (l := l) h.2]
end

theorem rnFrame_below {n : Nat} {f : Frame} (h : FrameBelow n f) : rnFrame n f = f := by
  simp only [rnFrame, locals_below h]

theorem rnAdmins_append (n : Nat) : ∀ (l l' : List Admin),
    rnAdmins n (l ++ l') = rnAdmins n l ++ rnAdmins n l'
  | [], _ => rfl
  | a :: l, l' => by rw [List.cons_append, rnAdmins, rnAdmins, rnAdmins_append n l l',
      List.cons_append]

theorem rnAdmin_toAdmin (n : Nat) (v : Val) : rnAdmin n v.toAdmin = (rnVal n v).toAdmin := by
  cases v with
  | num c => obtain ⟨t, b⟩ := c; cases t <;> rfl
  | vec _ => rfl
  | ref _ => rfl

theorem rnAdmins_vals (n : Nat) : ∀ vs : List Val, rnAdmins n (vals vs) = vals (vs.map (rnVal n))
  | [] => rfl
  | v :: vs => by
    simp only [vals, List.map_cons, rnAdmins, rnAdmin_toAdmin] at *
    rw [← vals, rnAdmins_vals n vs, vals]

theorem rnAdmins_expression (n : Nat) : ∀ es : List Instr, rnAdmins n (expression es) = expression es
  | [] => rfl
  | i :: es => by
    simp only [expression, List.map_cons, rnAdmins, rnAdmin] at *
    rw [← expression, rnAdmins_expression n es, expression]

theorem map_rnVal_below {n : Nat} {vs : List Val} (h : ∀ v ∈ vs, ValBelow n v) :
    vs.map (rnVal n) = vs := by
  conv_rhs => rw [← List.map_id vs]
  exact List.map_congr_left fun v hv => rnVal_below (h v hv)

/-- **Appending one exception to a store whose exception addresses lie below its exception
count gives an `ExnRen` target.** -/
theorem exnRen_addExn {H : Type} {s : Store H} (hb : StoreBelow s.exns.length s) (e : ExnInst) :
    ExnRen s.exns.length s (s.addExn e) := by
  have hexn : s.exns.map (rnExn s.exns.length) = s.exns := by
    conv_rhs => rw [← List.map_id s.exns]
    refine List.map_congr_left fun x hx => ?_
    show { x with fields := x.fields.map (rnVal _) } = x
    rw [map_rnVal_below (hb.exns x hx)]
  refine ⟨le_rfl, ⟨e, ?_⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show s.exns ++ [e] = _
    rw [List.take_length, List.drop_length, List.map_nil, hexn]
  · show s.globals = _
    conv_lhs => rw [← List.map_id s.globals]
    exact List.map_congr_left fun g hg => by rw [rnVal_below (hb.globals g hg)]; rfl
  · show s.tables = _
    conv_lhs => rw [← List.map_id s.tables]
    refine List.map_congr_left fun ti hti => ?_
    show ti = { ti with refs := ti.refs.map (rnRef _) }
    have hr : ti.refs.map (rnRef s.exns.length) = ti.refs := by
      conv_rhs => rw [← List.map_id ti.refs]
      exact List.map_congr_left fun r hr => rnRef_below (hb.tables ti hti r hr)
    rw [hr]
  · show s.elems = _
    conv_lhs => rw [← List.map_id s.elems]
    refine List.map_congr_left fun ei hei => ?_
    show ei = { ei with refs := ei.refs.map (rnRef _) }
    have hr : ei.refs.map (rnRef s.exns.length) = ei.refs := by
      conv_rhs => rw [← List.map_id ei.refs]
      exact List.map_congr_left fun r hr => rnRef_below (hb.elems ei hei r hr)
    rw [hr]
  · show s.structs = _
    conv_lhs => rw [← List.map_id s.structs]
    refine List.map_congr_left fun si hsi => ?_
    show si = { si with fields := si.fields.map (rnField _) }
    have hr : si.fields.map (rnField s.exns.length) = si.fields := by
      conv_rhs => rw [← List.map_id si.fields]
      exact List.map_congr_left fun fv hfv => rnField_below (hb.structs si hsi fv hfv)
    rw [hr]
  · show s.arrays = _
    conv_lhs => rw [← List.map_id s.arrays]
    refine List.map_congr_left fun ai hai => ?_
    show ai = { ai with fields := ai.fields.map (rnField _) }
    have hr : ai.fields.map (rnField s.exns.length) = ai.fields := by
      conv_rhs => rw [← List.map_id ai.fields]
      exact List.map_congr_left fun fv hfv => rnField_below (hb.arrays ai hai fv hfv)
    rw [hr]

end Silmaril.Proofs.Wasm.Models.FXRename
