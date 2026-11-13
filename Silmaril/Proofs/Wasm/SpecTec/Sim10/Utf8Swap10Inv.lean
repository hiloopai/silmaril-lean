module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Swap10Step

/-!
# Removing export lists keeps round 4's non-typing invariants

Round 4's forward run (`Whole.wholeRunFwd10T`) asks, besides typing, for plain code
(`Whole.Plain10`), aligned memories (`Whole.MemsAligned10`) and type-correct `global.set` redexes
(`GSetOk`). Stripping keeps all three:

* `plain10_exp`: stripping maps plain code to plain code;
* `memsAligned10_exp`: the memories are untouched;
* `activeF_unstrip`, **`gSetOk_exp10`**: an active piece of source instructions in the re-encoded
  code is an active piece of the original code, in a frame with the same globals;
* `noHost10_of_strip`: a host function of the store is one of the re-encoded store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config value values)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst ExportInst)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk ActiveF)
open Silmaril.Wasm.SpecTec.Sim10.Whole (Plain10 MemsAligned10 NoHost10)

variable {H : Type} {μ : ModuleInst → List ExportInst}

/-- **Stripping keeps plain code plain.** -/
theorem plain10_exp {l : List Admin} (h : Plain10 l) : Plain10 (expAdmins10 μ l) := by
  induction h with
  | plain is => simpa only [expAdmins10_sources] using Plain10.plain is
  | trap vs is =>
    simpa only [expAdmins10_append, expAdmins10_values, expAdmins10_cons,
      expAdmin10_trap, expAdmins10_sources] using Plain10.trap vs is
  | invoke vs a is =>
    simpa only [expAdmins10_append, expAdmins10_values, expAdmins10_cons,
      expAdmin10_invoke, expAdmins10_sources] using Plain10.invoke vs a is
  | label vs n cont body is _ ih =>
    simpa only [expAdmins10_append, expAdmins10_values, expAdmins10_cons,
      expAdmin10_label, expAdmins10_sources] using Plain10.label vs n cont _ is ih
  | frame vs n fr body is _ ih =>
    simpa only [expAdmins10_append, expAdmins10_values, expAdmins10_cons,
      expAdmin10_frame, expAdmins10_sources] using Plain10.frame vs n _ _ is ih

/-- **Stripping keeps the memories.** -/
theorem memsAligned10_exp {s : Store H} (h : MemsAligned10 s) :
    MemsAligned10 (expStore10 μ s) := h

/-- A host function of the store is a host function of the re-encoded store. -/
theorem noHost10_of_strip {s : Store H} (h : NoHost10 (expStore10 μ s)) : NoHost10 s := by
  intro i ft hh hs
  apply h i ft hh
  rw [funcs_stripStore10, hs]
  rfl

/-- Source instructions have only themselves as re-encoded preimages. -/
theorem expAdmins10_eq_sources : ∀ {b : List Admin} {ws : List V1.Instr},
    expAdmins10 μ b = ws.map .source → b = ws.map .source
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: b, w :: ws, h => by
    simp only [expAdmins10_cons, List.map_cons, List.cons.injEq] at h
    obtain ⟨ha, hb⟩ := h
    have ha' : a = .source w := by cases a <;> simp_all
    rw [ha', expAdmins10_eq_sources hb, List.map_cons]

/-- A piece of source instructions of re-encoded code is a piece of the code. -/
theorem piece_unstrip {code l₁ w l₂ : List Admin} {ws : List V1.Instr}
    (hC : expAdmins10 μ code = l₁ ++ w ++ l₂) (hw : w = ws.map .source) :
    ∃ a c, code = a ++ w ++ c := by
  rw [expAdmins10_eq_map] at hC
  obtain ⟨a₁₂, c, hcode, h₁₂, -⟩ := List.map_eq_append_iff.1 hC
  obtain ⟨a, b, ha₁₂, -, hb⟩ := List.map_eq_append_iff.1 h₁₂
  have hb' : expAdmins10 μ b = ws.map .source := by rw [expAdmins10_eq_map, hb, hw]
  have hbw : b = w := (expAdmins10_eq_sources hb').trans hw.symm
  exact ⟨a, c, by rw [hcode, ha₁₂, hbw]⟩

/-- A label of re-encoded code is the re-encoded form of a label of the code. -/
theorem label_mem_unstrip {code body : List Admin} {n : Nat} {cont : V1.Expr}
    (hm : .label n cont body ∈ expAdmins10 μ code) :
    ∃ body₀, .label n cont body₀ ∈ code ∧ body = expAdmins10 μ body₀ := by
  rw [expAdmins10_eq_map] at hm
  obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
  cases a with
  | label n₀ cont₀ body₀ =>
    have he' : n₀ = n ∧ cont₀ = cont ∧ expAdmins10 μ body₀ = body := by simpa using he
    exact ⟨body₀, he'.1 ▸ he'.2.1 ▸ ha, he'.2.2.symm⟩
  | _ => simp [expAdmin10] at he

/-- A frame of re-encoded code is the re-encoded form of a frame of the code. -/
theorem frame_mem_unstrip {code body : List Admin} {n : Nat} {fi : Frame}
    (hm : .frame n fi body ∈ expAdmins10 μ code) :
    ∃ fi₀ body₀, .frame n fi₀ body₀ ∈ code ∧ fi = expFrame10 μ fi₀ ∧
      body = expAdmins10 μ body₀ := by
  rw [expAdmins10_eq_map] at hm
  obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
  cases a with
  | frame n₀ fi₀ body₀ =>
    have he' : n₀ = n ∧ expFrame10 μ fi₀ = fi ∧ expAdmins10 μ body₀ = body := by simpa using he
    exact ⟨fi₀, body₀, he'.1 ▸ ha, he'.2.1.symm, he'.2.2.symm⟩
  | _ => simp [expAdmin10] at he

/-- **An active piece of source instructions in re-encoded code** is an active piece of the
original code, read in a frame that strips to the same frame. -/
theorem activeF_unstrip {F C f' w} (h : ActiveF F C f' w) {ws : List V1.Instr}
    (hw : w = ws.map .source) :
    ∀ {f : Frame} {code : List Admin}, F = expFrame10 μ f → C = expAdmins10 μ code →
      ∃ f'', ActiveF f code f'' w ∧ expFrame10 μ f'' = f' := by
  induction h with
  | piece =>
    intro f code hF hC
    obtain ⟨a, c, hcode⟩ := piece_unstrip hC.symm hw
    exact ⟨f, hcode ▸ ActiveF.piece, hF.symm⟩
  | label hm _ ih =>
    intro f code hF hC
    obtain ⟨body₀, hm₀, hbody⟩ := label_mem_unstrip (hC ▸ hm)
    obtain ⟨f'', hA, hf''⟩ := ih hw hF hbody
    exact ⟨f'', ActiveF.label hm₀ hA, hf''⟩
  | frame hm _ ih =>
    intro f code _ hC
    obtain ⟨fi₀, body₀, hm₀, hfi, hbody⟩ := frame_mem_unstrip (hC ▸ hm)
    obtain ⟨f'', hA, hf''⟩ := ih hw hfi hbody
    exact ⟨f'', ActiveF.frame hm₀ hA, hf''⟩

/-- **Stripping keeps `GSetOk`.** -/
theorem gSetOk_exp10 {s : Store H} {f : Frame} {code : List Admin} (h : GSetOk s f code) :
    GSetOk (expStore10 μ s) (expFrame10 μ f) (expAdmins10 μ code) := by
  intro f' v x a g hA hx hg
  obtain ⟨i, hi⟩ := Whole.value_source v
  obtain ⟨f'', hA', rfl⟩ := activeF_unstrip hA (ws := [i, .globalSet x])
    (by simp [hi]) rfl rfl
  exact h f'' v x a g hA' hx hg

end Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10
