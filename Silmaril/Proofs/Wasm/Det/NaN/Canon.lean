module

public import Silmaril.Proofs.Wasm.Det.NaN.Float

/-!
# Canonicalising NaNs in configurations: structural lemmas (proofs)

`canonAdmins` is a map, it is idempotent, and it commutes with the operations of Core
reduction: values as instructions (`canonAdmins_vals`), locals (`canonFrame_local?`,
`canonFrame_setLocal`, `canonFrame_forCall`), globals (`canonStore_global?`,
`canonStore_setGlobal`), evaluation contexts (`canonCtx_fill`) and the host-call redex search
(`decompose?_canon`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NaN

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (asF32 asF64)
open Silmaril.Wasm.Det.NaN

/-! ## Values -/

theorem canonBits_idem : ∀ (t : NumType) (b : BitVec t.width),
    canonBits t (canonBits t b) = canonBits t b
  | .int _, _ => rfl
  | .float .f32, b => canon32_idem b
  | .float .f64, b => canon64_idem b

@[simp] theorem canonVal_idem (v : Val) : canonVal (canonVal v) = canonVal v := by
  rcases v with ⟨t, b⟩ | _ | _
  · simp only [canonVal, canonBits_idem]
  · rfl
  · rfl

@[simp] theorem canonVal_comp : canonVal ∘ canonVal = canonVal := funext canonVal_idem

@[simp] theorem canonVal_num (t : NumType) (b : BitVec t.width) :
    canonVal (.num ⟨t, b⟩) = .num ⟨t, canonBits t b⟩ := rfl

@[simp] theorem canonVal_ref (r : Ref) : canonVal (.ref r) = .ref r := rfl

@[simp] theorem canonVal_i32 (b : BitVec 32) : canonVal (Val.i32 b) = Val.i32 b := rfl

@[simp] theorem canonInstr_idem (i : Instr) : canonInstr (canonInstr i) = canonInstr i := by
  cases i
  case floatConst t b => exact congrArg (Instr.floatConst t) (canonBits_idem (.float t) b)
  all_goals rfl

/-! ## Code -/

@[simp] theorem canonAdmins_nil : canonAdmins [] = [] := rfl

@[simp] theorem canonAdmins_cons (a : Admin) (as : List Admin) :
    canonAdmins (a :: as) = canonAdmin a :: canonAdmins as := rfl

theorem canonAdmins_eq_map : ∀ l : List Admin, canonAdmins l = l.map canonAdmin
  | [] => rfl
  | a :: as => by rw [canonAdmins_cons, canonAdmins_eq_map as, List.map_cons]

@[simp] theorem canonAdmins_append (l l' : List Admin) :
    canonAdmins (l ++ l') = canonAdmins l ++ canonAdmins l' := by
  simp only [canonAdmins_eq_map, List.map_append]

@[simp] theorem canonAdmin_toAdmin (v : Val) : canonAdmin v.toAdmin = (canonVal v).toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem canonAdmins_vals (vs : List Val) :
    canonAdmins (vals vs) = vals (vs.map canonVal) := by
  simp only [canonAdmins_eq_map, vals, List.map_map]
  exact List.map_congr_left fun v _ => canonAdmin_toAdmin v

@[simp] theorem canonAdmin_constI32 (b : BitVec 32) : canonAdmin (constI32 b) = constI32 b := rfl

@[simp] theorem canonAdmin_trap : canonAdmin .trap = .trap := rfl

@[simp] theorem canonAdmin_ref (r : Ref) : canonAdmin (.ref r) = .ref r := rfl

@[simp] theorem canonAdmin_callRefType (d : Validation.DefType) :
    canonAdmin (.callRefType d) = .callRefType d := rfl

@[simp] theorem canonAdmin_label (n : Nat) (cont : List Instr) (body : List Admin) :
    canonAdmin (.label n cont body) = .label n cont (canonAdmins body) := rfl

@[simp] theorem canonAdmin_handler (n : Nat) (cs : List Catch) (body : List Admin) :
    canonAdmin (.handler n cs body) = .handler n cs (canonAdmins body) := rfl

@[simp] theorem canonAdmin_frame (n : Nat) (f : Frame) (body : List Admin) :
    canonAdmin (.frame n f body) = .frame n (canonFrame f) (canonAdmins body) := rfl

@[simp] theorem canonAdmin_plain (i : Instr) : canonAdmin (.plain i) = .plain (canonInstr i) := rfl

@[simp] theorem canonFrame_idem (f : Frame) : canonFrame (canonFrame f) = canonFrame f := by
  simp only [canonFrame, List.map_map]
  congr 1
  refine List.map_congr_left fun o _ => ?_
  cases o
  · rfl
  · simp only [Function.comp, Option.map_some, canonVal_idem]

mutual
theorem canonAdmin_idem : ∀ a : Admin, canonAdmin (canonAdmin a) = canonAdmin a
  | .plain i => by simp only [canonAdmin_plain, canonInstr_idem]
  | .label n cont body => by simp only [canonAdmin_label, canonAdmins_idem body]
  | .handler n cs body => by simp only [canonAdmin_handler, canonAdmins_idem body]
  | .frame n f body => by simp only [canonAdmin_frame, canonFrame_idem, canonAdmins_idem body]
  | .ref _ => rfl
  | .callRefType _ => rfl
  | .returnCallRefType _ => rfl
  | .trap => rfl

theorem canonAdmins_idem : ∀ l : List Admin, canonAdmins (canonAdmins l) = canonAdmins l
  | [] => rfl
  | a :: as => by simp only [canonAdmins_cons, canonAdmin_idem a, canonAdmins_idem as]
end

/-! ## Frames and stores -/

@[simp] theorem canonFrame_module (f : Frame) : (canonFrame f).module = f.module := rfl

@[simp] theorem canonFrame_length (f : Frame) :
    (canonFrame f).locals.length = f.locals.length := by
  simp only [canonFrame, List.length_map]

theorem canonFrame_local? (f : Frame) (x : LocalIdx) :
    (canonFrame f).local? x = (f.local? x).map (Option.map canonVal) := by
  simp only [Frame.local?, canonFrame, List.getElem?_map]

theorem canonFrame_setLocal (f : Frame) (x : LocalIdx) (v : Val) :
    canonFrame (f.setLocal x v) = (canonFrame f).setLocal x (canonVal v) := by
  simp only [canonFrame, Frame.setLocal, List.map_set, Option.map_some]

theorem canonVal_default (t : Validation.CValType) :
    (defaultVal? t).map canonVal = defaultVal? t := by
  unfold defaultVal?
  split <;> first | rfl | (rename_i ft; cases ft <;> rfl)

theorem canonFrame_forCall (m : ModuleInst) (vs : List Val) (ls : List ValType) :
    canonFrame (Frame.forCall m vs ls) = Frame.forCall m (vs.map canonVal) ls := by
  simp only [canonFrame, Frame.forCall, List.map_append, List.map_map, Function.comp_def,
    Option.map_some, canonVal_default]

@[simp] theorem canonStore_funcs (s : Store Nat) : (canonStore s).funcs = s.funcs := rfl

@[simp] theorem canonStore_idem (s : Store Nat) : canonStore (canonStore s) = canonStore s := by
  simp only [canonStore, List.map_map]
  congr 1
  exact List.map_congr_left fun g _ => by simp only [Function.comp, canonVal_idem]

theorem canonStore_global? (s : Store Nat) (f : Frame) (x : GlobalIdx) :
    (canonStore s).global? f x =
      (s.global? f x).map fun p => (p.1, { p.2 with value := canonVal p.2.value }) := by
  simp only [Store.global?, canonStore]
  cases f.module.globals[x.toNat]? with
  | none => rfl
  | some a =>
    cases hg : s.globals[a]? <;> simp [hg, List.getElem?_map]

theorem modify_map {α : Type} (l : List α) (h g g' : α → α) (hc : ∀ x, h (g x) = g' (h x))
    (a : Nat) : (l.modify a g).map h = (l.map h).modify a g' := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_modify]
  by_cases hi : a = i
  · subst hi
    cases l[a]? <;> simp [hc]
  · simp [hi]

theorem canonStore_setGlobal (s : Store Nat) (a : Nat) (v : Val) :
    canonStore (s.setGlobal a v) = (canonStore s).setGlobal a (canonVal v) := by
  simp only [canonStore, Store.setGlobal]
  congr 1
  exact modify_map s.globals (fun g => { g with value := canonVal g.value })
    (fun g => { g with value := v }) (fun g => { g with value := canonVal v }) (fun _ => rfl) a

/-! ## Contexts and the host-call redex search -/

theorem canonCtx_fill : ∀ (E : Ctx) (xs : List Admin),
    canonAdmins (E.fill xs) = (canonCtx E).fill (canonAdmins xs)
  | .top pre rest, xs => by simp only [Ctx.fill, canonCtx, canonAdmins_append, canonAdmins_vals]
  | .label pre n cont E rest, xs => by
    simp only [Ctx.fill, canonCtx, canonAdmins_append, canonAdmins_vals, canonAdmins_cons,
      canonAdmins_nil, canonAdmin_label, canonCtx_fill E xs]
  | .handler pre n cs E rest, xs => by
    simp only [Ctx.fill, canonCtx, canonAdmins_append, canonAdmins_vals, canonAdmins_cons,
      canonAdmins_nil, canonAdmin_handler, canonCtx_fill E xs]
  | .frame pre n f E rest, xs => by
    simp only [Ctx.fill, canonCtx, canonAdmins_append, canonAdmins_vals, canonAdmins_cons,
      canonAdmins_nil, canonAdmin_frame, canonCtx_fill E xs]

theorem val?_canon (a : Admin) : (canonAdmin a).val? = a.val?.map canonVal := by
  cases a with
  | plain i => cases i <;> rfl
  | _ => rfl

theorem isCallRef_canon (a : Admin) : (canonAdmin a).isCallRef = a.isCallRef := by
  cases a with
  | plain i => cases i <;> rfl
  | _ => rfl

theorem splitVals_canon : ∀ l : List Admin,
    splitVals (canonAdmins l) = ((splitVals l).1.map canonVal, canonAdmins (splitVals l).2)
  | [] => rfl
  | a :: as => by
    have ih := splitVals_canon as
    rw [canonAdmins_cons]
    unfold splitVals
    rw [val?_canon]
    cases a.val? with
    | none => rfl
    | some v => simp only [Option.map_some, ih, List.map_cons]


/-- The canonical image of a host-call redex. -/
def canonRedex (x : Ctx × Nat × Nat × List Val) : Ctx × Nat × Nat × List Val :=
  (canonCtx x.1, x.2.1, x.2.2.1, x.2.2.2.map canonVal)

theorem topRedex_canon_of_last {s : Store Nat} {vs : List Val} {rest : List Admin} {a : Nat}
    (hl : vs.getLast? = some (.ref (.func a))) :
    topRedex s (vs.map canonVal) (canonAdmins rest) = (topRedex s vs rest).map canonRedex := by
  unfold topRedex
  rw [List.getLast?_map, hl]
  simp only [Option.map_some, canonVal_ref]
  rcases hostArity? s a with _ | ⟨h, n⟩
  · rfl
  · simp only [← List.map_dropLast, List.length_map]
    split
    · simp only [Option.map_some, canonRedex, canonCtx, List.map_take, List.map_drop,
        canonAdmins_eq_map]
    · rfl

theorem topRedex_none {s : Store Nat} {vs : List Val} {rest : List Admin}
    (h : ∀ a, vs.getLast? ≠ some (.ref (.func a))) : topRedex s vs rest = none := by
  unfold topRedex
  split
  · rename_i a ha
    exact absurd ha (h a)
  · rfl

theorem canonVal_eq_ref {v : Val} {r : Ref} (h : canonVal v = .ref r) : v = .ref r := by
  rcases v with ⟨t, b⟩ | b | r'
  · cases h
  · cases h
  · exact h

theorem topRedex_canon (s : Store Nat) (vs : List Val) (rest : List Admin) :
    topRedex s (vs.map canonVal) (canonAdmins rest) = (topRedex s vs rest).map canonRedex := by
  by_cases h : ∃ a, vs.getLast? = some (.ref (.func a))
  · obtain ⟨a, ha⟩ := h
    exact topRedex_canon_of_last ha
  · have h₁ : ∀ a, vs.getLast? ≠ some (.ref (.func a)) := fun a ha => h ⟨a, ha⟩
    have h₂ : ∀ a, (vs.map canonVal).getLast? ≠ some (.ref (.func a)) := by
      intro a ha
      rw [List.getLast?_map] at ha
      obtain ⟨v, hv, hcv⟩ := Option.map_eq_some_iff.mp ha
      exact h₁ a (by rw [hv, canonVal_eq_ref hcv])
    rw [topRedex_none h₂, topRedex_none h₁]
    rfl

/-- `decompHead` at a flat administrative instruction. -/
theorem decompHead_canon_flat {s : Store Nat} {vs : List Val} {rest : List Admin} {d : Admin}
    (h₁ : decompHead s (vs.map canonVal) (canonAdmin d) (canonAdmins rest) =
      if (canonAdmin d).isCallRef then topRedex s (vs.map canonVal) (canonAdmins rest) else none)
    (h₂ : decompHead s vs d rest = if d.isCallRef then topRedex s vs rest else none) :
    decompHead s (vs.map canonVal) (canonAdmin d) (canonAdmins rest) =
      (decompHead s vs d rest).map canonRedex := by
  rw [h₁, h₂, isCallRef_canon]
  split
  · exact topRedex_canon s vs rest
  · rfl

theorem decompose?_canon (s : Store Nat) (code : List Admin) :
    decompose? s (canonAdmins code) = (decompose? s code).map canonRedex := by
  rw [decompose?_eq s (canonAdmins code), decompose?_eq s code, splitVals_canon]
  rcases hsp : splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · rfl
  · show decompHead s (vs.map canonVal) (canonAdmin d) (canonAdmins rest) =
      (decompHead s vs d rest).map canonRedex
    have hsz : sizeOf (d :: rest) ≤ sizeOf code := by
      simpa only [hsp] using splitVals_snd_sizeOf code
    cases d with
    | label n cont body =>
      have : sizeOf body < sizeOf code := Nat.lt_of_lt_of_le
        (by simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec]; omega) hsz
      simp only [canonAdmin_label, decompHead, decompose?_canon s body, Option.map_map]
      rfl
    | handler n cs body =>
      have : sizeOf body < sizeOf code := Nat.lt_of_lt_of_le
        (by simp only [List.cons.sizeOf_spec, Admin.handler.sizeOf_spec]; omega) hsz
      simp only [canonAdmin_handler, decompHead, decompose?_canon s body, Option.map_map]
      rfl
    | frame n f body =>
      have : sizeOf body < sizeOf code := Nat.lt_of_lt_of_le
        (by simp only [List.cons.sizeOf_spec, Admin.frame.sizeOf_spec]; omega) hsz
      simp only [canonAdmin_frame, decompHead, decompose?_canon s body, Option.map_map]
      rfl
    | plain i => exact decompHead_canon_flat rfl rfl
    | ref r => exact decompHead_canon_flat rfl rfl
    | callRefType t => exact decompHead_canon_flat rfl rfl
    | returnCallRefType t => exact decompHead_canon_flat rfl rfl
    | trap => exact decompHead_canon_flat rfl rfl
termination_by sizeOf code

end Silmaril.Proofs.Wasm.Det.NaN
