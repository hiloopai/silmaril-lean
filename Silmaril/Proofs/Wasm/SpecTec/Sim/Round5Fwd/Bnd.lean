module

public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Defs

/-!
# Round 5: `Bounded` through the evaluation contexts

The forward recursion carries `Round4.Bounded c`. The four context rules keep the store and
step an inner configuration whose code is part of the outer code (and, for `frame`, whose frame
is the one the code holds), so the inner configuration is bounded too (`bounded_ctxt*`).

`Bounded` excludes the memory SIMD instructions (`Round4.instrBnd`), so no `MemoryStep` at
one of them starts from a bounded configuration (`not_vecMem`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round4 (Bounded AdminBnd AdminsBnd instrBnd)

variable {H : Type}

/-- `AdminsBnd` of a concatenation. -/
theorem adminsBnd_append (l₁ l₂ : List Admin) :
    AdminsBnd (l₁ ++ l₂) ↔ AdminsBnd l₁ ∧ AdminsBnd l₂ := by
  induction l₁ with
  | nil => simp [AdminsBnd]
  | cons a l ih => simp [AdminsBnd, ih, and_assoc]

/-- A plain instruction of bounded code is bounded. -/
theorem instrBnd_of_mem {l : List Admin} (hb : AdminsBnd l) {i : Instr}
    (hi : Admin.plain i ∈ l) : instrBnd i = true := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    simp only [AdminsBnd] at hb
    rcases List.mem_cons.1 hi with rfl | hi
    · simpa [AdminBnd] using hb.1
    · exact ih hb.2 hi

/-- `ctxt-instrs`: the inner configuration of a bounded one is bounded. -/
theorem bounded_ctxtInstrs {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    (hb : Bounded ⟨s, f, vals vs ++ is ++ rest⟩) : Bounded ⟨s, f, is⟩ :=
  have hc := (adminsBnd_append _ _).1 hb.code
  ⟨hb.store, hb.storeBnd, hb.frame, ((adminsBnd_append _ _).1 hc.1).2⟩

/-- `ctxt-label`. -/
theorem bounded_ctxtLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {is : List Admin} (hb : Bounded ⟨s, f, [.label n cont is]⟩) : Bounded ⟨s, f, is⟩ := by
  have hc : AdminBnd (.label n cont is) ∧ AdminsBnd [] := hb.code
  simp only [AdminBnd] at hc
  exact ⟨hb.store, hb.storeBnd, hb.frame, hc.1.2⟩

/-- `ctxt-handler`. -/
theorem bounded_ctxtHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {is : List Admin} (hb : Bounded ⟨s, f, [.handler n cs is]⟩) : Bounded ⟨s, f, is⟩ := by
  have hc : AdminBnd (.handler n cs is) ∧ AdminsBnd [] := hb.code
  simp only [AdminBnd] at hc
  exact ⟨hb.store, hb.storeBnd, hb.frame, hc.1⟩

/-- `ctxt-frame`: the inner configuration runs in the frame the code holds. -/
theorem bounded_ctxtFrame {s : Store H} {f fi : Frame} {n : Nat} {is : List Admin}
    (hb : Bounded ⟨s, f, [.frame n fi is]⟩) : Bounded ⟨s, fi, is⟩ := by
  have hc : AdminBnd (.frame n fi is) ∧ AdminsBnd [] := hb.code
  simp only [AdminBnd] at hc
  exact ⟨hb.store, hb.storeBnd, hc.1.1, hc.1.2⟩

/-- **No memory SIMD instruction in bounded code.** -/
theorem not_vecMem {l : List Admin} (hb : AdminsBnd l) {i : Instr} (hi : Admin.plain i ∈ l)
    (hv : R4Fwd.VecMemI i = true) : False := by
  have h := instrBnd_of_mem hb hi
  cases i <;> simp_all [R4Fwd.VecMemI, instrBnd]

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
