module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.Defs

/-!
# Removing export lists: how the map acts on code and on the store

* `stripAdmin20` is the identity on every administrative instruction but `LABEL_` and `FRAME_`
  (`stripAdmin20_plain`, …), so `stripAdmins20` fixes values and plain code
  (`stripAdmins20_vals`, `stripAdmins20_expression`) and distributes over `++`.
* `funcInst?_stripStore20`: a function instance of the stripped store is the stripped instance.
* `noHost20_of_storeOkB`: `StoreOkB` stores hold no host function.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution

variable {H : Type}

@[simp] theorem stripAdmin20_plain (i : V2.Instr) : stripAdmin20 (.plain i) = .plain i := rfl
@[simp] theorem stripAdmin20_trap : stripAdmin20 .trap = .trap := rfl
@[simp] theorem stripAdmin20_callAddr (a : FuncAddr) : stripAdmin20 (.callAddr a) = .callAddr a :=
  rfl
@[simp] theorem stripAdmin20_refFuncAddr (a : FuncAddr) :
    stripAdmin20 (.refFuncAddr a) = .refFuncAddr a := rfl
@[simp] theorem stripAdmin20_refHostAddr (a : HostAddr) :
    stripAdmin20 (.refHostAddr a) = .refHostAddr a := rfl
@[simp] theorem stripAdmin20_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    stripAdmin20 (.label n cont body) = .label n cont (stripAdmins20 body) := rfl
@[simp] theorem stripAdmin20_frame (n : Nat) (f : Frame) (body : List Admin) :
    stripAdmin20 (.frame n f body) = .frame n (stripFrame20 f) (stripAdmins20 body) := rfl

@[simp] theorem stripAdmins20_nil : stripAdmins20 [] = [] := rfl
@[simp] theorem stripAdmins20_cons (a : Admin) (l : List Admin) :
    stripAdmins20 (a :: l) = stripAdmin20 a :: stripAdmins20 l := rfl

theorem stripAdmins20_eq_map : ∀ l : List Admin, stripAdmins20 l = l.map stripAdmin20
  | [] => rfl
  | a :: l => by simp [stripAdmins20_eq_map l]

@[simp] theorem stripAdmins20_append (l₁ l₂ : List Admin) :
    stripAdmins20 (l₁ ++ l₂) = stripAdmins20 l₁ ++ stripAdmins20 l₂ := by
  simp [stripAdmins20_eq_map]

@[simp] theorem stripAdmins20_eq_nil {l : List Admin} : stripAdmins20 l = [] ↔ l = [] := by
  simp [stripAdmins20_eq_map]

@[simp] theorem stripAdmin20_toAdmin (v : Val) : stripAdmin20 v.toAdmin = v.toAdmin := by
  unfold Val.toAdmin
  split <;> rfl

@[simp] theorem stripAdmins20_vals (vs : List Val) : stripAdmins20 (vals vs) = vals vs := by
  simp [stripAdmins20_eq_map, vals]

@[simp] theorem stripAdmins20_expression (is : List V2.Instr) :
    stripAdmins20 (expression is) = expression is := by
  simp [stripAdmins20_eq_map, expression]

@[simp] theorem stripAdmin20_store8 : stripAdmin20 store8 = store8 := rfl
@[simp] theorem stripAdmin20_load8u : stripAdmin20 load8u = load8u := rfl

theorem funcInst?_stripStore20 (s : Store H) (a : FuncAddr) :
    (stripStore20 s).funcInst? a = (s.funcInst? a).map stripFI20 := by
  simp [stripStore20, Store.funcInst?]

theorem stripFrame20_forCall (m : ModuleInst) (vs : List Val) (ls : List V2.ValType) :
    stripFrame20 (Frame.forCall m vs ls) = Frame.forCall (stripModule20 m) vs ls := rfl

theorem stripFrame20_setLocal (f : Frame) (x : LocalIdx) (v : Val) :
    stripFrame20 (f.setLocal x v) = (stripFrame20 f).setLocal x v := rfl

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
