module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripStep

/-!
# Module instances of a configuration, and V2 steps

The successor half of leg 2 puts the export lists of `c'` back. They come from `c`: a V2 step
never makes a module instance, it only copies the callee's module into a new frame. This file
states that as the preservation of a property `Q` of all module instances.

* `AdminMods Q a`, `AdminsMods Q l`: every frame inside the code has a module with `Q`.
* `ModsQ Q c`: every function instance of the store, the frame, and every frame in the code have
  modules with `Q`.
* **`modsQ_step`**: on a store without host functions, a V2 step keeps `ModsQ Q`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {Q : ModuleInst → Prop}

mutual
/-- Every frame inside `a` has a module with `Q`. -/
def AdminMods (Q : ModuleInst → Prop) : Admin → Prop
  | .label _ _ body => AdminsMods Q body
  | .frame _ f body => Q f.module ∧ AdminsMods Q body
  | _ => True

/-- `AdminMods` on a sequence. -/
def AdminsMods (Q : ModuleInst → Prop) : List Admin → Prop
  | [] => True
  | a :: l => AdminMods Q a ∧ AdminsMods Q l
end

/-- **Every module instance of `c` has `Q`.** -/
structure ModsQ (Q : ModuleInst → Prop) (c : Config H) : Prop where
  funcs : ∀ fi ∈ c.store.funcs, Q fi.module
  frame : Q c.frame.module
  code : AdminsMods Q c.code

@[simp] theorem adminMods_plain (i : V2.Instr) : AdminMods Q (.plain i) := trivial
@[simp] theorem adminMods_trap : AdminMods Q .trap := trivial
@[simp] theorem adminMods_callAddr (a : FuncAddr) : AdminMods Q (.callAddr a) := trivial
@[simp] theorem adminMods_refFuncAddr (a : FuncAddr) : AdminMods Q (.refFuncAddr a) := trivial
@[simp] theorem adminMods_refHostAddr (a : HostAddr) : AdminMods Q (.refHostAddr a) := trivial
@[simp] theorem adminMods_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    AdminMods Q (.label n cont body) ↔ AdminsMods Q body := Iff.rfl
@[simp] theorem adminMods_frame (n : Nat) (f : Frame) (body : List Admin) :
    AdminMods Q (.frame n f body) ↔ Q f.module ∧ AdminsMods Q body := Iff.rfl
@[simp] theorem adminsMods_nil : AdminsMods Q [] := trivial
@[simp] theorem adminsMods_cons (a : Admin) (l : List Admin) :
    AdminsMods Q (a :: l) ↔ AdminMods Q a ∧ AdminsMods Q l := Iff.rfl

@[simp] theorem adminsMods_append (l₁ l₂ : List Admin) :
    AdminsMods Q (l₁ ++ l₂) ↔ AdminsMods Q l₁ ∧ AdminsMods Q l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, and_assoc]

@[simp] theorem adminMods_toAdmin (v : Val) : AdminMods Q v.toAdmin := by
  unfold Val.toAdmin
  split <;> trivial

@[simp] theorem adminsMods_vals (vs : List Val) : AdminsMods Q (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨adminMods_toAdmin v, ih⟩

@[simp] theorem adminsMods_expression (is : List V2.Instr) : AdminsMods Q (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih => exact ⟨trivial, ih⟩

/-- **A pure step keeps the modules of the code.** -/
theorem pureStep_mods {P : Profile} {is is' : List Admin} (h : PureStep P is is')
    (hq : AdminsMods Q is) : AdminsMods Q is' := by
  cases h <;> simp_all [constI32, vconst]

/-- **A read step keeps the modules of the code, given those of the store.** -/
theorem readStep_mods {s : Store H} {f : Frame} {is is' : List Admin} (h : ReadStep s f is is')
    (hs : ∀ fi ∈ s.funcs, Q fi.module) (hq : AdminsMods Q is) : AdminsMods Q is' := by
  cases h with
  | callAddr hf _ _ =>
    have hm : Q _ := hs _ (List.mem_of_getElem? hf)
    simpa using hm
  | _ => simp_all [constI32, vconst, store8, load8u]

/-- **A V2 step keeps `ModsQ Q`** on a store without host functions. -/
theorem modsQ_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hs : NoHost20 c.store) (hq : ModsQ Q c) : ModsQ Q c' := by
  induction h with
  | pure h => exact ⟨hq.funcs, hq.frame, pureStep_mods h hq.code⟩
  | read h => exact ⟨hq.funcs, hq.frame, readStep_mods h hq.funcs hq.code⟩
  | @ctxtInstrs _ _ _ _ vs is _ rest _ _ ih =>
    have hc : AdminsMods Q (vals vs) ∧ AdminsMods Q is ∧ AdminsMods Q rest := by
      simpa only [adminsMods_append, and_assoc] using hq.code
    have h' := ih hs ⟨hq.funcs, hq.frame, hc.2.1⟩
    exact ⟨h'.funcs, h'.frame, by simpa only [adminsMods_append] using ⟨⟨hc.1, h'.code⟩, hc.2.2⟩⟩
  | @ctxtLabel _ _ _ _ _ _ is _ _ ih =>
    have hc : AdminsMods Q is := by simpa using hq.code
    have h' := ih hs ⟨hq.funcs, hq.frame, hc⟩
    exact ⟨h'.funcs, h'.frame, by simpa using h'.code⟩
  | @ctxtFrame _ _ _ fi _ _ is _ _ ih =>
    have hc : Q fi.module ∧ AdminsMods Q is := by simpa using hq.code
    have h' := ih hs ⟨hq.funcs, hc.1, hc.2⟩
    exact ⟨h'.funcs, hq.frame, by simpa using ⟨h'.frame, h'.code⟩⟩
  | callAddrHost hf hcode => exact absurd hcode (hs _ _ _ hf)
  | callAddrHostDiv hf hcode => exact absurd hcode (hs _ _ _ hf)
  | _ => exact ⟨hq.funcs, hq.frame, by simp⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
