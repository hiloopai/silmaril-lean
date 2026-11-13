module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapEnc

/-!
# Re-encoding export lists: how the map acts on code and on the store

* `expAdmin20` is the identity on every administrative instruction but `LABEL_` and `FRAME_`
  (`expAdmin20_plain`, …), so `expAdmins20` fixes values and plain code
  (`expAdmins20_vals`, `expAdmins20_expression`) and distributes over `++`.
* `funcInst?_expStore20`: a function instance of the re-encoded store is the re-encoded
  instance.

These are round 7's `Utf8StripBase` lemmas for any re-encoding `F` (stripping is `F = []`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution

variable {H : Type} {F : ModuleInst → List ExportInst}

@[simp] theorem expAdmin20_plain (i : V2.Instr) : expAdmin20 F (.plain i) = .plain i := rfl
@[simp] theorem expAdmin20_trap : expAdmin20 F .trap = .trap := rfl
@[simp] theorem expAdmin20_callAddr (a : FuncAddr) : expAdmin20 F (.callAddr a) = .callAddr a :=
  rfl
@[simp] theorem expAdmin20_refFuncAddr (a : FuncAddr) :
    expAdmin20 F (.refFuncAddr a) = .refFuncAddr a := rfl
@[simp] theorem expAdmin20_refHostAddr (a : HostAddr) :
    expAdmin20 F (.refHostAddr a) = .refHostAddr a := rfl
@[simp] theorem expAdmin20_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    expAdmin20 F (.label n cont body) = .label n cont (expAdmins20 F body) := rfl
@[simp] theorem expAdmin20_frame (n : Nat) (f : Frame) (body : List Admin) :
    expAdmin20 F (.frame n f body) = .frame n (expFrame20 F f) (expAdmins20 F body) := rfl

@[simp] theorem expAdmins20_nil : expAdmins20 F [] = [] := rfl
@[simp] theorem expAdmins20_cons (a : Admin) (l : List Admin) :
    expAdmins20 F (a :: l) = expAdmin20 F a :: expAdmins20 F l := rfl

theorem expAdmins20_eq_map : ∀ l : List Admin, expAdmins20 F l = l.map (expAdmin20 F)
  | [] => rfl
  | a :: l => by simp [expAdmins20_eq_map l]

@[simp] theorem expAdmins20_append (l₁ l₂ : List Admin) :
    expAdmins20 F (l₁ ++ l₂) = expAdmins20 F l₁ ++ expAdmins20 F l₂ := by
  simp [expAdmins20_eq_map]

@[simp] theorem expAdmins20_eq_nil {l : List Admin} : expAdmins20 F l = [] ↔ l = [] := by
  simp [expAdmins20_eq_map]

@[simp] theorem expAdmin20_toAdmin (v : Val) : expAdmin20 F v.toAdmin = v.toAdmin := by
  unfold Val.toAdmin
  split <;> rfl

@[simp] theorem expAdmins20_vals (vs : List Val) : expAdmins20 F (vals vs) = vals vs := by
  simp [expAdmins20_eq_map, vals]

@[simp] theorem expAdmins20_expression (is : List V2.Instr) :
    expAdmins20 F (expression is) = expression is := by
  simp [expAdmins20_eq_map, expression]

@[simp] theorem expAdmin20_store8 : expAdmin20 F store8 = store8 := rfl
@[simp] theorem expAdmin20_load8u : expAdmin20 F load8u = load8u := rfl

theorem funcInst?_expStore20 (s : Store H) (a : FuncAddr) :
    (expStore20 F s).funcInst? a = (s.funcInst? a).map (expFI20 F) := by
  simp [expStore20, Store.funcInst?]

theorem expFrame20_forCall (m : ModuleInst) (vs : List Val) (ls : List V2.ValType) :
    expFrame20 F (Frame.forCall m vs ls) = Frame.forCall (expModule20 F m) vs ls := rfl

theorem expFrame20_setLocal (f : Frame) (x : LocalIdx) (v : Val) :
    expFrame20 F (f.setLocal x v) = (expFrame20 F f).setLocal x v := rfl

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
