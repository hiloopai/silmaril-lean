module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripTypCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripFwd

/-!
# Leg 2: a `Good20BU` configuration without exports is `Good20B`

* `ctrlOkB_strip`, `okB_strip`: the code checks read a module only through its types, so they
  are unchanged when the exports go (frames inside the code included).
* `eDA_strip`, `eraseS_strip`: round 5's body erasure commutes with removing exports.
* `plain20_strip`, `storeOkB_strip`, `storeSmall_strip`: the non-typing parts of the invariant.
* **`good20B_strip`** (`goodStrip20_holds`): `Task.goodStrip20`. The typing parts come from
  `typedV_state_strip` and `typedV_admins_strip`.
* **`fwdU20_of_unstrip`**: `Utf8Mono.Task.fwdU20` from `Task.goodUnstrip20` and
  `Task.unstripStep20` alone.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (ctrlOkB ctrlOkBL okB okBL StoreOkB StoreSmall Good20B)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eDA eDAL eD)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (eraseS eraseFI TypF)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Plain20 PendOp)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (Good20BU storeB_utf8)

variable {H : Type}

/-- `ctrlOkB` and `ctrlOkBL` read a module only through its types. -/
theorem ctrlOkB_strip (m : ModuleInst) (i : V2.Instr) :
    ctrlOkB (stripModule20 m) i = ctrlOkB m i := by
  induction i using V2.Instr.rec
    (motive_2 := fun l => ctrlOkBL (stripModule20 m) l = ctrlOkBL m l) with
  | nil => rfl
  | cons _ _ h₁ h₂ => exact congrArg₂ (· && ·) h₁ h₂
  | block _ _ h => exact h
  | loop _ _ h => exact h
  | if_ _ _ _ h₁ h₂ => exact congrArg₂ (· && ·) h₁ h₂
  | _ => rfl

/-- `ctrlOkBL` reads a module only through its types. -/
theorem ctrlOkB_all_strip (m : ModuleInst) (l : List V2.Instr) :
    l.all (ctrlOkB (stripModule20 m)) = l.all (ctrlOkB m) :=
  congrArg l.all (funext (ctrlOkB_strip m))

/-- **`okB` of a stripped instruction in the stripped module is `okB`.** -/
theorem okB_strip (a : Admin) : ∀ m : ModuleInst,
    okB (stripModule20 m) (stripAdmin20 a) = okB m a := by
  induction a using Admin.rec
    (motive_2 := fun l => ∀ m : ModuleInst,
      okBL (stripModule20 m) (stripAdmins20 l) = okBL m l) with
  | nil => rfl
  | cons _ _ h₁ h₂ => rename_i m; exact congrArg₂ (· && ·) (h₁ m) (h₂ m)
  | plain i => intro m; exact ctrlOkB_strip m i
  | label _ cont _ h =>
    intro m
    have hc : ctrlOkBL (stripModule20 m) cont = ctrlOkBL m cont := by
      simpa only [StoreBulk.ctrlOkBL_eq] using ctrlOkB_all_strip m cont
    exact congrArg₂ (· && ·) hc (h m)
  | frame _ f _ h => intro _; exact h f.module
  | _ => intro _; rfl

/-- `okB_strip` on a sequence. -/
theorem all_okB_strip (m : ModuleInst) (l : List Admin) :
    (stripAdmins20 l).all (okB (stripModule20 m)) = l.all (okB m) := by
  simp only [stripAdmins20_eq_map, List.all_map, Function.comp_def, okB_strip]

/-- **Body erasure commutes with removing exports.** -/
theorem eDA_strip (a : Admin) : eDA (stripAdmin20 a) = stripAdmin20 (eDA a) := by
  induction a using Admin.rec
    (motive_2 := fun l => (stripAdmins20 l).map eDA = stripAdmins20 (l.map eDA)) with
  | nil => rfl
  | cons _ _ h₁ h₂ => exact congrArg₂ List.cons h₁ h₂
  | label n cont _ h =>
    show Admin.label n (StoreDeep.eDL cont) (eDAL _) = .label n _ (stripAdmins20 (eDAL _))
    rw [StoreDeep.eDAL_eq, StoreDeep.eDAL_eq, h]
  | frame n f _ h =>
    show Admin.frame n _ (eDAL _) = .frame n _ (stripAdmins20 (eDAL _))
    rw [StoreDeep.eDAL_eq, StoreDeep.eDAL_eq, h]
  | _ => rfl

/-- `eDA_strip` on a sequence. -/
theorem map_eDA_strip (l : List Admin) : (stripAdmins20 l).map eDA = stripAdmins20 (l.map eDA) := by
  simp only [stripAdmins20_eq_map, List.map_map, Function.comp_def, eDA_strip]

/-- Body erasure commutes with removing exports, on stores. -/
theorem eraseS_strip (s : Store H) : eraseS (stripStore20 s) = stripStore20 (eraseS s) := by
  simp only [eraseS, stripStore20, List.map_map]
  rfl

/-- A pending operator is fixed by `stripAdmin20`. -/
theorem stripAdmin20_pendOp {y : Admin} (hy : PendOp y) : stripAdmin20 y = y := by
  rcases hy with ⟨x, rfl⟩ | rfl <;> rfl

/-- **The plain-tail invariant survives removing exports.** -/
theorem plain20_strip {s : Store H} {f : Frame} {code : List Admin} (h : Plain20 s f code) :
    Plain20 (stripStore20 s) (stripFrame20 f) (stripAdmins20 code) := by
  induction h with
  | allVals vs => simpa only [stripAdmins20_vals] using Plain20.allVals vs
  | plain vs i is hi =>
    simpa only [stripAdmins20_append, stripAdmins20_vals, stripAdmins20_cons, stripAdmin20_plain,
      stripAdmins20_expression] using Plain20.plain vs i is hi
  | trap vs is =>
    simpa only [stripAdmins20_append, stripAdmins20_vals, stripAdmins20_cons, stripAdmin20_trap,
      stripAdmins20_expression] using Plain20.trap vs is
  | callAddr vs a is =>
    simpa only [stripAdmins20_append, stripAdmins20_vals, stripAdmins20_cons,
      stripAdmin20_callAddr, stripAdmins20_expression] using Plain20.callAddr vs a is
  | label vs n cont body is _ ih =>
    simpa only [stripAdmins20_append, stripAdmins20_vals, stripAdmins20_cons, stripAdmin20_label,
      stripAdmins20_expression] using Plain20.label vs n cont _ is ih
  | frame vs n fi body is _ ih =>
    simpa only [stripAdmins20_append, stripAdmins20_vals, stripAdmins20_cons, stripAdmin20_frame,
      stripAdmins20_expression] using Plain20.frame vs n _ _ is ih
  | pend vs i v y ws is hy hok =>
    simpa only [stripAdmins20_append, stripAdmins20_vals, stripAdmins20_cons,
      stripAdmin20_pendOp hy, stripAdmins20_expression] using
      Plain20.pend (s := stripStore20 _) (f := stripFrame20 _) vs i v y ws is hy hok

/-- **`StoreOkB` survives removing exports.** -/
theorem storeOkB_strip {s : Store H} (h : StoreOkB s) : StoreOkB (stripStore20 s) := by
  intro a fi' hf
  have hm : Option.map stripFI20 (s.funcInst? a) = some fi' :=
    (funcInst?_stripStore20 s a).symm.trans hf
  obtain ⟨fi, hfi, he⟩ : ∃ fi, s.funcInst? a = some fi ∧ stripFI20 fi = fi' :=
    Option.map_eq_some_iff.1 hm
  obtain ⟨fn, hc, hb⟩ := h a fi hfi
  refine ⟨fn, he ▸ hc, ?_⟩
  rw [← he]
  exact (ctrlOkB_all_strip fi.module fn.body).trans hb

/-- **`StoreSmall` survives removing exports.** -/
theorem storeSmall_strip {s : Store H} (h : StoreSmall s) : StoreSmall (stripStore20 s) :=
  ⟨h.mems, h.datas, h.tables, h.elems⟩

/-- **Leg 2 of `Utf8Mono.Task.fwdU20`**: a `Good20BU` configuration without its exports is
`Good20B`. -/
theorem good20B_strip {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile} {c : Config H}
    (hg : Good20BU hn P c) : Good20B hn P (stripConfig20 c) := by
  have hB := storeB_utf8 P
  have hS : TypedV (simEnv20 (Whole.storeB P)) (.varT "state" [])
      (stateV hn (eraseS (stripStore20 c.store)) (stripFrame20 c.frame)) := by
    rw [eraseS_strip]
    exact typedV_state_strip hB hg.typ.state
  have hC : TypedV (simEnv20 (Whole.storeB P)) StepFix.adminsTy
      (.list (adminsToV ((stripAdmins20 c.code).map eDA))) := by
    rw [map_eDA_strip]
    exact typedV_admins_strip hB _ hg.typ.code
  have hok : (stripAdmins20 c.code).all (okB (stripModule20 c.frame.module)) = true :=
    (all_okB_strip c.frame.module c.code).trans hg.ok
  exact ⟨⟨hS, hC⟩, plain20_strip hg.plain, hok, storeOkB_strip hg.store,
    storeSmall_strip hg.small⟩

/-- **`Task.goodStrip20` holds.** -/
theorem goodStrip20_holds : Task.goodStrip20 := fun _ _ _ _ hg => good20B_strip hg

/-- **`Utf8Mono.Task.fwdU20` from the two legs that remain open.** -/
theorem fwdU20_of_unstrip (h₂' : Task.goodUnstrip20) (h₃ : Task.unstripStep20) :
    Utf8Mono.Task.fwdU20 :=
  fwdU20_of_legs goodStrip20_holds h₂' h₃

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
