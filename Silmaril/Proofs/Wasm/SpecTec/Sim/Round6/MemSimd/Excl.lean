module

public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs

/-!
# Round 6: the memory SIMD exclusion is implied by `Round4.Bounded`

`Round4.instrBnd` rejects the four memory SIMD constructors, so a bounded instruction, code or
store contains none of them, at any depth: `noMemSimd_of_bounded`. The domain of every target
since round 4 (`Round4.Bounded`, `Pos.BoundedNE`, `Target.BoundedSel`) therefore already
excludes memory SIMD; `NoMemSimd` makes that exclusion explicit.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

mutual
/-- A bounded instruction has no memory SIMD instruction. -/
theorem instrMS_of_instrBnd : ∀ {i : Instr}, Round4.instrBnd i = true → instrMS i = true
  | i, h => by
    cases i
    case block _ body =>
      simp only [Round4.instrBnd, instrMS] at h ⊢
      exact instrsMS_of_instrsBnd h
    case loop _ body =>
      simp only [Round4.instrBnd, instrMS] at h ⊢
      exact instrsMS_of_instrsBnd h
    case if_ _ b₁ b₂ =>
      simp only [Round4.instrBnd, instrMS, Bool.and_eq_true] at h ⊢
      exact ⟨instrsMS_of_instrsBnd h.1, instrsMS_of_instrsBnd h.2⟩
    case tryTable _ _ body =>
      simp only [Round4.instrBnd, instrMS, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact instrsMS_of_instrsBnd h.2
    all_goals first | rfl | simp_all [Round4.instrBnd]

/-- A bounded sequence has no memory SIMD instruction. -/
theorem instrsMS_of_instrsBnd : ∀ {is : List Instr}, Round4.instrsBnd is = true →
    instrsMS is = true
  | [], _ => rfl
  | i :: is, h => by
    simp only [Round4.instrsBnd, instrsMS, Bool.and_eq_true] at h ⊢
    exact ⟨instrMS_of_instrBnd h.1, instrsMS_of_instrsBnd h.2⟩
end

mutual
/-- A bounded administrative instruction has no memory SIMD instruction. -/
theorem adminMS_of_adminBnd : ∀ {a : Admin}, Round4.AdminBnd a → AdminMS a
  | .plain _, h => instrMS_of_instrBnd h
  | .ref _, _ => trivial
  | .callRefType _, _ => trivial
  | .returnCallRefType _, _ => trivial
  | .label _ _ _, h => ⟨instrsMS_of_instrsBnd h.1, adminsMS_of_adminsBnd h.2⟩
  | .handler _ _ _, h => adminsMS_of_adminsBnd h
  | .frame _ _ _, h => adminsMS_of_adminsBnd h.2
  | .trap, _ => trivial

/-- A bounded code has no memory SIMD instruction. -/
theorem adminsMS_of_adminsBnd : ∀ {l : List Admin}, Round4.AdminsBnd l → AdminsMS l
  | [], _ => trivial
  | _ :: _, h => ⟨adminMS_of_adminBnd h.1, adminsMS_of_adminsBnd h.2⟩
end

/-- A bounded store has no memory SIMD function body. -/
theorem storeMS_of_storeBnd {s : Store H} (h : Round4.StoreBnd s) : StoreMS s :=
  fun fi hfi fn hc => instrsMS_of_instrsBnd ((h.funcs fi hfi).2.2 fn hc)

/-- **`Round4.Bounded` excludes memory SIMD**, in the code and in the store. -/
theorem noMemSimd_of_bounded {c : Config H} (h : Round4.Bounded c) : NoMemSimd c :=
  ⟨storeMS_of_storeBnd h.storeBnd, adminsMS_of_adminsBnd h.code⟩

/-- `Target.BoundedSel` (the domain of `Round5.Task.wholeStepValidSel`) excludes memory SIMD. -/
theorem noMemSimd_of_boundedSel {c : Config H} (h : Round5.Target.BoundedSel c) : NoMemSimd c :=
  noMemSimd_of_bounded h.1.1

/-- A memory SIMD instruction is never bounded. -/
theorem instrBnd_of_memSimd {i : Instr} (h : memSimd i = true) : Round4.instrBnd i = false := by
  cases i <;> simp_all [memSimd, Round4.instrBnd]

end Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd
