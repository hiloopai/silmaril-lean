module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapTypCode

/-!
# A `Good20BU` configuration with re-encoded exports is `Good20B`

Round 7's `Utf8StripGood` (leg 2) for a re-encoding `F` whose export images are typed in
`simEnv20`:

* `ctrlOkB_exp`, `okB_exp`: the code checks read a module only through its types.
* `eDA_exp`, `eraseS_exp`: round 5's body erasure commutes with re-encoding exports.
* `plain20_exp`, `storeOkB_exp`, `storeSmall_exp`: the non-typing parts of the invariant.
* **`good20B_exp`**: a `Good20BU` configuration whose export lists are re-encoded by `F` is
  `Good20B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (ctrlOkB ctrlOkBL okB okBL StoreOkB StoreSmall Good20B)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eDA eDAL eD)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (eraseS eraseFI TypF)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Plain20 PendOp)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (Good20BU storeB_utf8)

variable {H : Type} {F : ModuleInst → List ExportInst}

/-- `ctrlOkB` and `ctrlOkBL` read a module only through its types. -/
theorem ctrlOkB_exp (m : ModuleInst) (i : V2.Instr) :
    ctrlOkB (expModule20 F m) i = ctrlOkB m i := by
  induction i using V2.Instr.rec
    (motive_2 := fun l => ctrlOkBL (expModule20 F m) l = ctrlOkBL m l) with
  | nil => rfl
  | cons _ _ h₁ h₂ => exact congrArg₂ (· && ·) h₁ h₂
  | block _ _ h => exact h
  | loop _ _ h => exact h
  | if_ _ _ _ h₁ h₂ => exact congrArg₂ (· && ·) h₁ h₂
  | _ => rfl

/-- `ctrlOkBL` reads a module only through its types. -/
theorem ctrlOkB_all_exp (m : ModuleInst) (l : List V2.Instr) :
    l.all (ctrlOkB (expModule20 F m)) = l.all (ctrlOkB m) :=
  congrArg l.all (funext (ctrlOkB_exp m))

/-- **`okB` of a stripped instruction in the stripped module is `okB`.** -/
theorem okB_exp (a : Admin) : ∀ m : ModuleInst,
    okB (expModule20 F m) (expAdmin20 F a) = okB m a := by
  induction a using Admin.rec
    (motive_2 := fun l => ∀ m : ModuleInst,
      okBL (expModule20 F m) (expAdmins20 F l) = okBL m l) with
  | nil => rfl
  | cons _ _ h₁ h₂ => rename_i m; exact congrArg₂ (· && ·) (h₁ m) (h₂ m)
  | plain i => intro m; exact ctrlOkB_exp m i
  | label _ cont _ h =>
    intro m
    have hc : ctrlOkBL (expModule20 F m) cont = ctrlOkBL m cont := by
      simpa only [StoreBulk.ctrlOkBL_eq] using ctrlOkB_all_exp m cont
    exact congrArg₂ (· && ·) hc (h m)
  | frame _ f _ h => intro _; exact h f.module
  | _ => intro _; rfl

/-- `okB_exp` on a sequence. -/
theorem all_okB_exp (m : ModuleInst) (l : List Admin) :
    (expAdmins20 F l).all (okB (expModule20 F m)) = l.all (okB m) := by
  simp only [expAdmins20_eq_map, List.all_map, Function.comp_def, okB_exp]

/-- **Body erasure commutes with removing exports.** -/
theorem eDA_exp (a : Admin) : eDA (expAdmin20 F a) = expAdmin20 F (eDA a) := by
  induction a using Admin.rec
    (motive_2 := fun l => (expAdmins20 F l).map eDA = expAdmins20 F (l.map eDA)) with
  | nil => rfl
  | cons _ _ h₁ h₂ => exact congrArg₂ List.cons h₁ h₂
  | label n cont _ h =>
    show Admin.label n (StoreDeep.eDL cont) (eDAL _) = .label n _ (expAdmins20 F (eDAL _))
    rw [StoreDeep.eDAL_eq, StoreDeep.eDAL_eq, h]
  | frame n f _ h =>
    show Admin.frame n _ (eDAL _) = .frame n _ (expAdmins20 F (eDAL _))
    rw [StoreDeep.eDAL_eq, StoreDeep.eDAL_eq, h]
  | _ => rfl

/-- `eDA_exp` on a sequence. -/
theorem map_eDA_exp (l : List Admin) : (expAdmins20 F l).map eDA = expAdmins20 F (l.map eDA) := by
  simp only [expAdmins20_eq_map, List.map_map, Function.comp_def, eDA_exp]

/-- Body erasure commutes with removing exports, on stores. -/
theorem eraseS_exp (s : Store H) : eraseS (expStore20 F s) = expStore20 F (eraseS s) := by
  simp only [eraseS, expStore20, List.map_map]
  rfl

/-- A pending operator is fixed by `expAdmin20`. -/
theorem expAdmin20_pendOp {y : Admin} (hy : PendOp y) : expAdmin20 F y = y := by
  rcases hy with ⟨x, rfl⟩ | rfl <;> rfl

/-- **The plain-tail invariant survives removing exports.** -/
theorem plain20_exp {s : Store H} {f : Frame} {code : List Admin} (h : Plain20 s f code) :
    Plain20 (expStore20 F s) (expFrame20 F f) (expAdmins20 F code) := by
  induction h with
  | allVals vs => simpa only [expAdmins20_vals] using Plain20.allVals vs
  | plain vs i is hi =>
    simpa only [expAdmins20_append, expAdmins20_vals, expAdmins20_cons, expAdmin20_plain,
      expAdmins20_expression] using Plain20.plain vs i is hi
  | trap vs is =>
    simpa only [expAdmins20_append, expAdmins20_vals, expAdmins20_cons, expAdmin20_trap,
      expAdmins20_expression] using Plain20.trap vs is
  | callAddr vs a is =>
    simpa only [expAdmins20_append, expAdmins20_vals, expAdmins20_cons,
      expAdmin20_callAddr, expAdmins20_expression] using Plain20.callAddr vs a is
  | label vs n cont body is _ ih =>
    simpa only [expAdmins20_append, expAdmins20_vals, expAdmins20_cons, expAdmin20_label,
      expAdmins20_expression] using Plain20.label vs n cont _ is ih
  | frame vs n fi body is _ ih =>
    simpa only [expAdmins20_append, expAdmins20_vals, expAdmins20_cons, expAdmin20_frame,
      expAdmins20_expression] using Plain20.frame vs n _ _ is ih
  | pend vs i v y ws is hy hok =>
    simpa only [expAdmins20_append, expAdmins20_vals, expAdmins20_cons,
      expAdmin20_pendOp hy, expAdmins20_expression] using
      Plain20.pend (s := expStore20 F _) (f := expFrame20 F _) vs i v y ws is hy hok

/-- **`StoreOkB` survives removing exports.** -/
theorem storeOkB_exp {s : Store H} (h : StoreOkB s) : StoreOkB (expStore20 F s) := by
  intro a fi' hf
  have hm : Option.map (expFI20 F) (s.funcInst? a) = some fi' :=
    (funcInst?_expStore20 s a).symm.trans hf
  obtain ⟨fi, hfi, he⟩ : ∃ fi, s.funcInst? a = some fi ∧ expFI20 F fi = fi' :=
    Option.map_eq_some_iff.1 hm
  obtain ⟨fn, hc, hb⟩ := h a fi hfi
  refine ⟨fn, he ▸ hc, ?_⟩
  rw [← he]
  exact (ctrlOkB_all_exp fi.module fn.body).trans hb

/-- **`StoreSmall` survives removing exports.** -/
theorem storeSmall_exp {s : Store H} (h : StoreSmall s) : StoreSmall (expStore20 F s) :=
  ⟨h.mems, h.datas, h.tables, h.elems⟩

/-- **Leg 2 of `Utf8Mono.Task.fwdU20`**: a `Good20BU` configuration without its exports is
`Good20B`. -/
theorem good20B_exp {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile} {c : Config H}
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 (Whole.storeB P)) exportsT (expV (F m)))
    (hg : Good20BU hn P c) : Good20B hn P (expConfig20 F c) := by
  have hB := storeB_utf8 P
  have hS : TypedV (simEnv20 (Whole.storeB P)) (.varT "state" [])
      (stateV hn (eraseS (expStore20 F c.store)) (expFrame20 F c.frame)) := by
    rw [eraseS_exp]
    exact typedV_state_exp hB hF hg.typ.state
  have hC : TypedV (simEnv20 (Whole.storeB P)) StepFix.adminsTy
      (.list (adminsToV ((expAdmins20 F c.code).map eDA))) := by
    rw [map_eDA_exp]
    exact typedV_admins_exp hB hF _ hg.typ.code
  have hok : (expAdmins20 F c.code).all (okB (expModule20 F c.frame.module)) = true :=
    (all_okB_exp c.frame.module c.code).trans hg.ok
  exact ⟨⟨hS, hC⟩, plain20_exp hg.plain, hok, storeOkB_exp hg.store,
    storeSmall_exp hg.small⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
