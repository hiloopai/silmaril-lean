module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.Step
public import Mathlib.Tactic.CasesM

/-!
# Exception renaming: inverting the renaming on code, frames and stores

The backward half of the renaming simulation starts from a step of the renamed configuration.
These lemmas read the renamed code back: `rnAdmins n L = P`, for each shape `P` of a rule,
gives `L` of the same shape with the pieces of `P` renamed pieces of `L`. Together with
`subst_vars` they put a target step in the form of a renamed source step. The store lookups of
an `ExnRen n` target are pulled back as well (`global_rn_back`, …).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FXRename
open Silmaril.Proofs.Wasm.Models.FXRename (rnIdx_injective)

variable {H : Type} {n : Nat}

theorem rnAdmins_eq_map (l : List Admin) : rnAdmins n l = l.map (rnAdmin n) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ## Code -/

theorem rnAdmins_eq_cons_iff {L : List Admin} {a : Admin} {P : List Admin} :
    rnAdmins n L = a :: P ↔ ∃ a₀ L₀, L = a₀ :: L₀ ∧ rnAdmin n a₀ = a ∧ rnAdmins n L₀ = P := by
  cases L <;> simp [and_assoc]

theorem rnAdmins_eq_nil_iff' {L : List Admin} : rnAdmins n L = [] ↔ L = [] := by
  cases L <;> simp

theorem rnAdmins_eq_append_iff {L A B : List Admin} :
    rnAdmins n L = A ++ B ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ rnAdmins n L₁ = A ∧ rnAdmins n L₂ = B := by
  simp only [rnAdmins_eq_map, List.map_eq_append_iff]

theorem rnAdmin_eq_toAdmin_iff {a : Admin} {v : Val} :
    rnAdmin n a = v.toAdmin ↔ ∃ v₀, a = v₀.toAdmin ∧ rnVal n v₀ = v := by
  constructor
  · intro h
    cases a with
    | plain i =>
      refine ⟨v, ?_, ?_⟩
      · rw [← h]; rfl
      · rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r <;> first | rfl | (simp [Val.toAdmin] at h)
    | ref r =>
      refine ⟨.ref r, rfl, ?_⟩
      rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r' <;> simp_all [Val.toAdmin]
    | _ => rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h
  · rintro ⟨v₀, rfl, rfl⟩; exact rnAdmin_toAdmin' v₀

theorem rnAdmins_eq_vals_iff {L : List Admin} {vs : List Val} :
    rnAdmins n L = vals vs ↔ ∃ vs₀, L = vals vs₀ ∧ vs₀.map (rnVal n) = vs := by
  induction L generalizing vs with
  | nil => cases vs <;> simp [vals]
  | cons a L ih =>
    cases vs with
    | nil => simp [vals]
    | cons v vs =>
      have hcons : rnAdmins n (a :: L) = vals (v :: vs) ↔
          rnAdmin n a = v.toAdmin ∧ rnAdmins n L = vals vs := by
        simp only [rnAdmins_cons, vals, List.map_cons, List.cons.injEq]
      rw [hcons, rnAdmin_eq_toAdmin_iff, ih]
      constructor
      · rintro ⟨⟨v₀, rfl, rfl⟩, ⟨vs₀, rfl, rfl⟩⟩; exact ⟨v₀ :: vs₀, rfl, rfl⟩
      · rintro ⟨_ | ⟨v₀, vs₀⟩, hL, hv⟩
        · simp [vals] at hL
        · simp only [vals, List.map_cons, List.cons.injEq] at hL hv
          exact ⟨⟨v₀, hL.1, hv.1⟩, ⟨vs₀, hL.2, hv.2⟩⟩

theorem rnAdmin_eq_plain_iff {a : Admin} {i : Instr} : rnAdmin n a = .plain i ↔ a = .plain i := by
  cases a <;> simp

theorem rnAdmin_eq_constI32_iff {a : Admin} {c : BitVec 32} :
    rnAdmin n a = constI32 c ↔ a = constI32 c := rnAdmin_eq_plain_iff

theorem rnAdmin_eq_aconst_iff {a : Admin} {at' : AddrType} {i : BitVec at'.intType.width} :
    rnAdmin n a = aconst at' i ↔ a = aconst at' i := rnAdmin_eq_plain_iff

theorem rnAdmin_eq_store8_iff {a : Admin} {x : MemIdx} : rnAdmin n a = store8 x ↔ a = store8 x :=
  rnAdmin_eq_plain_iff

theorem rnAdmin_eq_load8u_iff {a : Admin} {x : MemIdx} : rnAdmin n a = load8u x ↔ a = load8u x :=
  rnAdmin_eq_plain_iff

theorem rnAdmin_eq_trap_iff {a : Admin} : rnAdmin n a = .trap ↔ a = .trap := by
  cases a <;> simp

theorem rnAdmin_eq_ref_iff {a : Admin} {r : Ref} :
    rnAdmin n a = .ref r ↔ ∃ r₀, a = .ref r₀ ∧ rnRef n r₀ = r := by
  cases a <;> simp

theorem rnAdmin_eq_callRefType_iff {a : Admin} {d : DefType} :
    rnAdmin n a = .callRefType d ↔ a = .callRefType d := by
  cases a <;> simp

theorem rnAdmin_eq_returnCallRefType_iff {a : Admin} {d : DefType} :
    rnAdmin n a = .returnCallRefType d ↔ a = .returnCallRefType d := by
  cases a <;> simp

theorem rnAdmin_eq_label_iff {a : Admin} {k : Nat} {cont : List Instr} {body : List Admin} :
    rnAdmin n a = .label k cont body ↔ ∃ body₀, a = .label k cont body₀ ∧ rnAdmins n body₀ = body := by
  cases a <;> simp [and_assoc, eq_comm]

theorem rnAdmin_eq_handler_iff {a : Admin} {k : Nat} {cs : List Catch} {body : List Admin} :
    rnAdmin n a = .handler k cs body ↔
      ∃ body₀, a = .handler k cs body₀ ∧ rnAdmins n body₀ = body := by
  cases a <;> simp [and_assoc, eq_comm]

theorem rnAdmin_eq_frame_iff {a : Admin} {k : Nat} {fi : Frame} {body : List Admin} :
    rnAdmin n a = .frame k fi body ↔
      ∃ fi₀ body₀, a = .frame k fi₀ body₀ ∧ rnFrame n fi₀ = fi ∧ rnAdmins n body₀ = body := by
  cases a <;> simp [and_assoc, eq_comm]

theorem rnAdmins_eq_throwing_iff {L : List Admin} {b : Nat} :
    rnAdmins n L = throwing b ↔ ∃ a, L = throwing a ∧ rnIdx n a = b := by
  constructor
  · intro h
    obtain ⟨a₀, L₀, rfl, h₀, hL⟩ := rnAdmins_eq_cons_iff.mp h
    obtain ⟨a₁, L₁, rfl, h₁, hL₁⟩ := rnAdmins_eq_cons_iff.mp hL
    obtain ⟨r₀, rfl, hr⟩ := rnAdmin_eq_ref_iff.mp h₀
    rw [rnAdmin_eq_plain_iff] at h₁
    rw [rnAdmins_eq_nil_iff'] at hL₁
    subst h₁ hL₁
    cases r₀ <;> simp [rnRef] at hr
    exact ⟨_, rfl, hr⟩
  · rintro ⟨a, rfl, rfl⟩; rfl

/-! ## References and values -/

theorem rnRef_eq_null_iff {r : Ref} : rnRef n r = .null ↔ r = .null := rnRef_eq_null

theorem rnRef_eq_func_iff {r : Ref} {a : Nat} : rnRef n r = .func a ↔ r = .func a := by
  cases r <;> simp [rnRef]

theorem rnRef_eq_struct_iff {r : Ref} {a : Nat} : rnRef n r = .struct a ↔ r = .struct a := by
  cases r <;> simp [rnRef]

theorem rnRef_eq_array_iff {r : Ref} {a : Nat} : rnRef n r = .array a ↔ r = .array a := by
  cases r <;> simp [rnRef]

theorem rnRef_eq_i31_iff {r : Ref} {b : BitVec 31} : rnRef n r = .i31 b ↔ r = .i31 b := by
  cases r <;> simp [rnRef]

theorem rnRef_eq_exn_iff {r : Ref} {b : Nat} :
    rnRef n r = .exn b ↔ ∃ a, r = .exn a ∧ rnIdx n a = b := by
  cases r <;> simp [rnRef]

theorem rnRef_eq_extern_iff {r : Ref} {r' : Ref} :
    rnRef n r = .extern r' ↔ ∃ r₀, r = .extern r₀ ∧ rnRef n r₀ = r' := by
  cases r <;> simp [rnRef]

theorem map_rnVal_eq_nil_iff {vs : List Val} : vs.map (rnVal n) = [] ↔ vs = [] := List.map_eq_nil_iff

/-! ## Stores and frames -/

section Back

variable {s t : Store H} (h : ExnRen n s t) {f : Frame}
include h

theorem global_rn_back {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hl : t.global? (rnFrame n f) x = some (a, g)) :
    ∃ g₀, s.global? f x = some (a, g₀) ∧ rnGlobal n g₀ = g := by
  simp only [Store.global?, rnFrame_module, h.globals, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, List.getElem?_map,
    Option.map_eq_some_iff, Prod.mk.injEq] at hl ⊢
  obtain ⟨a', ha, g', ⟨g₀, hg₀, rfl⟩, rfl, rfl⟩ := hl
  exact ⟨g₀, ⟨a', ha, g₀, hg₀, rfl, rfl⟩, rfl⟩

theorem table_rn_back {x : TableIdx} {a : Nat} {ti : TableInst}
    (hl : t.table? (rnFrame n f) x = some (a, ti)) :
    ∃ ti₀, s.table? f x = some (a, ti₀) ∧ rnTable n ti₀ = ti := by
  simp only [Store.table?, rnFrame_module, h.tables, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, List.getElem?_map,
    Option.map_eq_some_iff, Prod.mk.injEq] at hl ⊢
  obtain ⟨a', ha, g', ⟨g₀, hg₀, rfl⟩, rfl, rfl⟩ := hl
  exact ⟨g₀, ⟨a', ha, g₀, hg₀, rfl, rfl⟩, rfl⟩

theorem elem_rn_back {x : ElemIdx} {a : Nat} {ei : ElemInst}
    (hl : t.elem? (rnFrame n f) x = some (a, ei)) :
    ∃ ei₀, s.elem? f x = some (a, ei₀) ∧ rnElem n ei₀ = ei := by
  simp only [Store.elem?, rnFrame_module, h.elems, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, List.getElem?_map,
    Option.map_eq_some_iff, Prod.mk.injEq] at hl ⊢
  obtain ⟨a', ha, g', ⟨g₀, hg₀, rfl⟩, rfl, rfl⟩ := hl
  exact ⟨g₀, ⟨a', ha, g₀, hg₀, rfl, rfl⟩, rfl⟩

theorem mem_rn_back {x : MemIdx} {a : Nat} {mi : MemInst}
    (hl : t.mem? (rnFrame n f) x = some (a, mi)) : s.mem? f x = some (a, mi) := by
  simpa only [Store.mem?, rnFrame_module, h.mems] using hl

theorem data_rn_back {x : DataIdx} {a : Nat} {di : DataInst}
    (hl : t.data? (rnFrame n f) x = some (a, di)) : s.data? f x = some (a, di) := by
  simpa only [Store.data?, rnFrame_module, h.datas] using hl

theorem tag_rn_back {x : TagIdx} {a : Nat} {ti : TagInst}
    (hl : t.tag? (rnFrame n f) x = some (a, ti)) : s.tag? f x = some (a, ti) := by
  simpa only [Store.tag?, rnFrame_module, h.tags] using hl

theorem funcs_rn_back {a : Nat} {fi : FuncInst H} (hl : t.funcs[a]? = some fi) :
    s.funcs[a]? = some fi := by
  rw [← h.funcs]; exact hl

theorem structs_rn_back {a : Nat} {si : StructInst} (hl : t.structs[a]? = some si) :
    ∃ si₀, s.structs[a]? = some si₀ ∧ rnStruct n si₀ = si := by
  rw [h.structs, List.getElem?_map, Option.map_eq_some_iff] at hl
  obtain ⟨si₀, h₀, rfl⟩ := hl
  exact ⟨si₀, h₀, rfl⟩

theorem arrays_rn_back {a : Nat} {ai : ArrayInst} (hl : t.arrays[a]? = some ai) :
    ∃ ai₀, s.arrays[a]? = some ai₀ ∧ rnArray n ai₀ = ai := by
  rw [h.arrays, List.getElem?_map, Option.map_eq_some_iff] at hl
  obtain ⟨ai₀, h₀, rfl⟩ := hl
  exact ⟨ai₀, h₀, rfl⟩

theorem exns_rn_back {a : Nat} {e : ExnInst} (hl : t.exns[rnIdx n a]? = some e) :
    ∃ e₀, s.exns[a]? = some e₀ ∧ rnExn n e₀ = e := by
  rw [exns_rn h, Option.map_eq_some_iff] at hl
  exact hl

end Back

theorem local_rn_back {f : Frame} {x : LocalIdx} {v : Val}
    (hl : (rnFrame n f).local? x = some (some v)) :
    ∃ v₀, f.local? x = some (some v₀) ∧ rnVal n v₀ = v := by
  rw [rnFrame_local?, Option.map_eq_some_iff] at hl
  obtain ⟨o, ho, hv⟩ := hl
  cases o with
  | none => cases hv
  | some v₀ => cases hv; exact ⟨v₀, ho, rfl⟩

/-- The inversion lemmas, as a simp set for a hypothesis `rnAdmins n L = P`. -/
macro "rn_inv" h:ident : tactic => `(tactic|
  (simp only [rnCfg, Config.mk.injEq,
      rnAdmins_eq_cons_iff, rnAdmins_eq_nil_iff', rnAdmins_eq_append_iff, rnAdmins_eq_vals_iff,
      rnAdmins_eq_throwing_iff,
      rnAdmin_eq_toAdmin_iff, rnAdmin_eq_plain_iff, rnAdmin_eq_constI32_iff,
      rnAdmin_eq_aconst_iff, rnAdmin_eq_store8_iff, rnAdmin_eq_load8u_iff, rnAdmin_eq_trap_iff,
      rnAdmin_eq_ref_iff, rnAdmin_eq_callRefType_iff, rnAdmin_eq_returnCallRefType_iff,
      rnAdmin_eq_label_iff, rnAdmin_eq_handler_iff, rnAdmin_eq_frame_iff, rnRef_eq_null_iff,
      rnRef_eq_func_iff, rnRef_eq_struct_iff, rnRef_eq_array_iff, rnRef_eq_i31_iff,
      rnRef_eq_exn_iff, rnRef_eq_extern_iff, exists_and_left, exists_and_right, exists_eq_left,
      exists_eq_right, and_assoc] at $h:ident
   casesm* (_ = _) ∧ _, (Exists _) ∧ _, Exists _
   subst_vars))

end Silmaril.Proofs.Wasm.Models.FXRenameSim
