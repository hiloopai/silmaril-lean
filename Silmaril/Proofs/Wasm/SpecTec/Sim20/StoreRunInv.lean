module

public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Thms

/-!
# The storing example has exactly one V2 step

`StoreAgree.memStoreCfg2` is one empty memory, no functions, and code
`i32.const 0; i32.const 0; i32.store; nop`. An earlier step showed that it steps to `trap; nop` in V2 and in
`simEnv20T`, but left the step-shape clause of `GoodStore20T` ("every V2 step from `c` is this
store") as a hypothesis. This module proves it by inverting V2's `Step` on the concrete code:

* `not_pure_st`, `not_read_st`: no `Step_pure` or `Step_read` rule applies to the code or to any
  window of it that is not all values;
* `split1`–`split6`: the windows `is` of a context split `val* is rest` of each code;
* `not_step1`–`not_step4`: `i32.store`, `i32.const 0; i32.store`, `i32.store; nop` and
  `i32.const 0; i32.store; nop` have no step;
* `step5`: `i32.const 0; i32.const 0; i32.store` traps, since the memory is empty
  (`writeBytes?_empty` rules out `store-num-val`);
* **`step_memStoreCfg2_inv`**: every V2 step from `memStoreCfg2` is to `memStoreCfg2'`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreRun

open Silmaril.Wasm Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (memOnlyStore memStoreCfg2 memStoreCfg2')
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (memFrame i32Store0)

/-- `i32.store` at `memarg 0 0`. -/
abbrev st0 : Admin := .plain i32Store0
/-- `nop`. -/
abbrev np0 : Admin := .plain .nop
/-- `i32.const 0`. -/
abbrev c00 : Admin := constI32 0

@[simp] theorem toAdmin_ne_st (v : Val) : (v.toAdmin = st0) ↔ False := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> simp [Val.toAdmin]

@[simp] theorem toAdmin_ne_np (v : Val) : (v.toAdmin = np0) ↔ False := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> simp [Val.toAdmin]

/-- The codes of the example and their inner windows. -/
def StoreCode (l : List Admin) : Prop :=
  l = [st0] ∨ l = [c00, st0] ∨ l = [st0, np0] ∨ l = [c00, st0, np0] ∨ l = [c00, c00, st0] ∨
    l = [c00, c00, st0, np0]

theorem not_pure_st {P : Profile} {l is' : List Admin} (hl : StoreCode l) : ¬ PureStep P l is' := by
  intro h
  cases h <;> simp_all [StoreCode, vals, constI32, aref, vconst]
  case trapVals vs rest _ =>
    have hm : Admin.trap ∈ vals vs ++ Admin.trap :: rest := by simp
    rcases hl with hc | hc | hc | hc | hc | hc <;> simp_all [vals]

theorem not_read_st {H : Type} {s : Store H} {f : Frame} {l is' : List Admin} (hl : StoreCode l) :
    ¬ ReadStep s f l is' := by
  intro h
  cases h <;> simp_all [StoreCode, vals, constI32, vconst]
  all_goals
    rcases hl with hc | hc | hc | hc | hc | hc <;>
      · have hl := congrArg List.getLast? hc
        simp at hl

theorem split1 {vs : List Val} {is rest : List Admin} (h : vals vs ++ is ++ rest = [st0])
    (hv : is.all Admin.isVal = false) (hne : vs ≠ [] ∨ rest ≠ []) : False := by
  rcases vs with _ | ⟨v₁, vs⟩ <;> rcases is with _ | ⟨j₁, _ | ⟨j₂, is⟩⟩ <;>
  simp_all [vals, Admin.isVal, Admin.val?]

theorem split2 {vs : List Val} {is rest : List Admin} (h : vals vs ++ is ++ rest = [c00, st0])
    (hv : is.all Admin.isVal = false) (hne : vs ≠ [] ∨ rest ≠ []) : is = [st0] := by
  rcases vs with _ | ⟨v₁, _ | ⟨v₂, vs⟩⟩ <;> rcases is with _ | ⟨j₁, _ | ⟨j₂, _ | ⟨j₃, is⟩⟩⟩ <;>
  simp_all [vals, Admin.isVal, Admin.val?]

theorem split3 {vs : List Val} {is rest : List Admin} (h : vals vs ++ is ++ rest = [st0, np0])
    (hv : is.all Admin.isVal = false) (hne : vs ≠ [] ∨ rest ≠ []) : is = [st0] := by
  rcases vs with _ | ⟨v₁, vs⟩ <;> rcases is with _ | ⟨j₁, _ | ⟨j₂, _ | ⟨j₃, is⟩⟩⟩ <;>
  simp_all [vals, Admin.isVal, Admin.val?]

theorem split4 {vs : List Val} {is rest : List Admin} (h : vals vs ++ is ++ rest = [c00, st0, np0])
    (hv : is.all Admin.isVal = false) (hne : vs ≠ [] ∨ rest ≠ []) :
    is = [st0] ∨ is = [c00, st0] ∨ is = [st0, np0] := by
  rcases vs with _ | ⟨v₁, _ | ⟨v₂, vs⟩⟩ <;>
  rcases is with _ | ⟨j₁, _ | ⟨j₂, _ | ⟨j₃, _ | ⟨j₄, is⟩⟩⟩⟩ <;>
  simp_all [vals, Admin.isVal, Admin.val?]

theorem split5 {vs : List Val} {is rest : List Admin} (h : vals vs ++ is ++ rest = [c00, c00, st0])
    (hv : is.all Admin.isVal = false) (hne : vs ≠ [] ∨ rest ≠ []) :
    is = [st0] ∨ is = [c00, st0] := by
  rcases vs with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, vs⟩⟩⟩ <;>
  rcases is with _ | ⟨j₁, _ | ⟨j₂, _ | ⟨j₃, _ | ⟨j₄, is⟩⟩⟩⟩ <;>
  simp_all [vals, Admin.isVal, Admin.val?]

theorem split6 {vs : List Val} {is rest : List Admin}
    (h : vals vs ++ is ++ rest = [c00, c00, st0, np0])
    (hv : is.all Admin.isVal = false) (hne : vs ≠ [] ∨ rest ≠ []) :
    (vs = [] ∧ is = [c00, c00, st0] ∧ rest = [np0]) ∨ is = [st0] ∨ is = [c00, st0] ∨
      is = [st0, np0] ∨ is = [c00, st0, np0] := by
  rcases vs with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, vs⟩⟩⟩ <;>
  rcases is with _ | ⟨j₁, _ | ⟨j₂, _ | ⟨j₃, _ | ⟨j₄, is⟩⟩⟩⟩ <;>
  simp_all [vals, Admin.isVal, Admin.val?]

variable {P : Profile} {host : HostSemantics Empty}

/-- No step from `i32.store` alone. -/
theorem not_step1 {c c' : Config Empty} (h : Step P host c c') : c.code ≠ [st0] := by
  induction h with
  | pure hp => exact fun hc => not_pure_st (Or.inl hc) hp
  | read hr => exact fun hc => not_read_st (Or.inl hc) hr
  | ctxtInstrs hs hne _ => exact fun hc => split1 hc hs.not_allVals hne
  | callAddrHost => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | callAddrHostDiv => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | _ => simp

/-- No step from `i32.const 0; i32.store`. -/
theorem not_step2 {c c' : Config Empty} (h : Step P host c c') : c.code ≠ [c00, st0] := by
  induction h with
  | pure hp => exact fun hc => not_pure_st (Or.inr (Or.inl hc)) hp
  | read hr => exact fun hc => not_read_st (Or.inr (Or.inl hc)) hr
  | ctxtInstrs hs hne _ => exact fun hc => not_step1 hs (split2 hc hs.not_allVals hne)
  | callAddrHost => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | callAddrHostDiv => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | _ => simp

/-- No step from `i32.store; nop`. -/
theorem not_step3 {c c' : Config Empty} (h : Step P host c c') : c.code ≠ [st0, np0] := by
  induction h with
  | pure hp => exact fun hc => not_pure_st (Or.inr (Or.inr (Or.inl hc))) hp
  | read hr => exact fun hc => not_read_st (Or.inr (Or.inr (Or.inl hc))) hr
  | ctxtInstrs hs hne _ => exact fun hc => not_step1 hs (split3 hc hs.not_allVals hne)
  | callAddrHost => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | callAddrHostDiv => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | _ => simp

/-- No step from `i32.const 0; i32.store; nop`. -/
theorem not_step4 {c c' : Config Empty} (h : Step P host c c') : c.code ≠ [c00, st0, np0] := by
  induction h with
  | pure hp => exact fun hc => not_pure_st (Or.inr (Or.inr (Or.inr (Or.inl hc)))) hp
  | read hr => exact fun hc => not_read_st (Or.inr (Or.inr (Or.inr (Or.inl hc)))) hr
  | ctxtInstrs hs hne _ =>
    intro hc
    rcases split4 hc hs.not_allVals hne with h₁ | h₁ | h₁
    · exact not_step1 hs h₁
    · exact not_step2 hs h₁
    · exact not_step3 hs h₁
  | callAddrHost => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | callAddrHostDiv => exact fun hc => by have hl := congrArg List.getLast? hc; simp at hl
  | _ => simp

/-- No write into an empty memory. -/
theorem writeBytes?_empty {mi : MemInst} (h : mi.bytes.size = 0) {i j : Nat} (hj : 0 < j)
    (bs : Silmaril.Wasm.Execution.Memory.Bytes) : mi.writeBytes? i j bs = none := by
  unfold MemInst.writeBytes?
  split
  · rename_i hb
    have hn : ¬ (i + bs.size ≤ mi.bytes.size) := by omega
    simp [Silmaril.Wasm.Execution.Memory.writeBytes, hn]
  · rfl

/-- The memory of `memOnlyStore` is empty. -/
theorem memOnly_empty {a : MemAddr} {mi : MemInst} (hm : memOnlyStore.memInst? a = some mi) :
    mi.bytes.size = 0 := by
  rcases a with _ | a
  · have e : mi = ⟨⟨⟨0, none⟩⟩, ByteArray.empty⟩ := by
      simpa [memOnlyStore, Store.memInst?] using hm.symm
    rw [e]; rfl
  · simp [memOnlyStore, Store.memInst?] at hm

/-- **The store from the empty memory traps.** -/
theorem step5 {c c' : Config Empty} (h : Step P host c c') (hs : c.store = memOnlyStore)
    (hf : c.frame = memFrame) (hc : c.code = [c00, c00, st0]) :
    c' = ⟨memOnlyStore, memFrame, [.trap]⟩ := by
  induction h with
  | pure hp => exact (not_pure_st (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))) hp).elim
  | read hr => exact (not_read_st (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))) hr).elim
  | ctxtInstrs hst hne _ =>
    rcases split5 hc hst.not_allVals hne with h₁ | h₁
    · exact (not_step1 hst h₁).elim
    · exact (not_step2 hst h₁).elim
  | storeIntTrap ha hm h => simp_all
  | storeIntVal ha hm hw =>
    rename_i s f t ao i cv a mi mi'
    have hs' : s = memOnlyStore := hs
    have hmi : mi.bytes.size = 0 := memOnly_empty (hs' ▸ hm)
    rw [writeBytes?_empty hmi (by cases t <;> decide)] at hw
    cases hw
  | callAddrHost => have hl := congrArg List.getLast? hc; simp at hl
  | callAddrHostDiv => have hl := congrArg List.getLast? hc; simp at hl
  | _ => simp_all

/-- **The example has exactly one step**: the store traps, the `nop` waits. -/
theorem step6 {c c' : Config Empty} (h : Step P host c c') (hs : c.store = memOnlyStore)
    (hf : c.frame = memFrame) (hc : c.code = [c00, c00, st0, np0]) :
    c' = ⟨memOnlyStore, memFrame, [.trap, np0]⟩ := by
  induction h with
  | pure hp => exact (not_pure_st (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))) hp).elim
  | read hr => exact (not_read_st (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))) hr).elim
  | ctxtInstrs hst hne _ =>
    rcases split6 hc hst.not_allVals hne with ⟨rfl, h₁, rfl⟩ | h₁ | h₁ | h₁ | h₁
    · have e := step5 hst hs hf h₁
      simp only [Config.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      subst hs hf
      rfl
    · exact (not_step1 hst h₁).elim
    · exact (not_step2 hst h₁).elim
    · exact (not_step3 hst h₁).elim
    · exact (not_step4 hst h₁).elim
  | callAddrHost => have hl := congrArg List.getLast? hc; simp at hl
  | callAddrHostDiv => have hl := congrArg List.getLast? hc; simp at hl
  | _ => simp_all

theorem step_memStoreCfg2_inv {c' : Config Empty} (h : Step P host memStoreCfg2 c') :
    c' = memStoreCfg2' :=
  step6 h rfl rfl rfl


end Silmaril.Wasm.SpecTec.Sim20.StoreRun
