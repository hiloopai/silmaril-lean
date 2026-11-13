module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Step

/-!
# Removing export lists keeps round 4's non-typing invariants

Round 4's forward run (`Whole.wholeRunFwd10T`) asks, besides typing, for plain code
(`Whole.Plain10`), aligned memories (`Whole.MemsAligned10`) and type-correct `global.set` redexes
(`GSetOk`). Stripping keeps all three:

* `plain10_strip`: stripping maps plain code to plain code;
* `memsAligned10_strip`: the memories are untouched;
* `activeF_unstrip`, **`gSetOk_strip10`**: an active piece of source instructions in the stripped
  code is an active piece of the original code, in a frame with the same globals;
* `noHost10_of_strip`: a host function of the store is one of the stripped store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk ActiveF)
open Silmaril.Wasm.SpecTec.Sim10.Whole (Plain10 MemsAligned10 NoHost10)

variable {H : Type}

/-- **Stripping keeps plain code plain.** -/
theorem plain10_strip {l : List Admin} (h : Plain10 l) : Plain10 (stripAdmins10 l) := by
  induction h with
  | plain is => simpa only [stripAdmins10_sources] using Plain10.plain is
  | trap vs is =>
    simpa only [stripAdmins10_append, stripAdmins10_values, stripAdmins10_cons,
      stripAdmin10_trap, stripAdmins10_sources] using Plain10.trap vs is
  | invoke vs a is =>
    simpa only [stripAdmins10_append, stripAdmins10_values, stripAdmins10_cons,
      stripAdmin10_invoke, stripAdmins10_sources] using Plain10.invoke vs a is
  | label vs n cont body is _ ih =>
    simpa only [stripAdmins10_append, stripAdmins10_values, stripAdmins10_cons,
      stripAdmin10_label, stripAdmins10_sources] using Plain10.label vs n cont _ is ih
  | frame vs n fr body is _ ih =>
    simpa only [stripAdmins10_append, stripAdmins10_values, stripAdmins10_cons,
      stripAdmin10_frame, stripAdmins10_sources] using Plain10.frame vs n _ _ is ih

/-- **Stripping keeps the memories.** -/
theorem memsAligned10_strip {s : Store H} (h : MemsAligned10 s) :
    MemsAligned10 (stripStore10 s) := h

/-- A host function of the store is a host function of the stripped store. -/
theorem noHost10_of_strip {s : Store H} (h : NoHost10 (stripStore10 s)) : NoHost10 s := by
  intro i ft hh hs
  apply h i ft hh
  rw [funcs_stripStore10, hs]
  rfl

/-- Source instructions have only themselves as stripped preimages. -/
theorem stripAdmins10_eq_sources : ∀ {b : List Admin} {ws : List V1.Instr},
    stripAdmins10 b = ws.map .source → b = ws.map .source
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: b, w :: ws, h => by
    simp only [stripAdmins10_cons, List.map_cons, List.cons.injEq] at h
    obtain ⟨ha, hb⟩ := h
    have ha' : a = .source w := by cases a <;> simp_all
    rw [ha', stripAdmins10_eq_sources hb, List.map_cons]

/-- A piece of source instructions of stripped code is a piece of the code. -/
theorem piece_unstrip {code l₁ w l₂ : List Admin} {ws : List V1.Instr}
    (hC : stripAdmins10 code = l₁ ++ w ++ l₂) (hw : w = ws.map .source) :
    ∃ a c, code = a ++ w ++ c := by
  rw [stripAdmins10_eq_map] at hC
  obtain ⟨a₁₂, c, hcode, h₁₂, -⟩ := List.map_eq_append_iff.1 hC
  obtain ⟨a, b, ha₁₂, -, hb⟩ := List.map_eq_append_iff.1 h₁₂
  have hb' : stripAdmins10 b = ws.map .source := by rw [stripAdmins10_eq_map, hb, hw]
  have hbw : b = w := (stripAdmins10_eq_sources hb').trans hw.symm
  exact ⟨a, c, by rw [hcode, ha₁₂, hbw]⟩

/-- A label of stripped code is the stripped form of a label of the code. -/
theorem label_mem_unstrip {code body : List Admin} {n : Nat} {cont : V1.Expr}
    (hm : .label n cont body ∈ stripAdmins10 code) :
    ∃ body₀, .label n cont body₀ ∈ code ∧ body = stripAdmins10 body₀ := by
  rw [stripAdmins10_eq_map] at hm
  obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
  cases a with
  | label n₀ cont₀ body₀ =>
    have he' : n₀ = n ∧ cont₀ = cont ∧ stripAdmins10 body₀ = body := by simpa using he
    exact ⟨body₀, he'.1 ▸ he'.2.1 ▸ ha, he'.2.2.symm⟩
  | _ => simp [stripAdmin10] at he

/-- A frame of stripped code is the stripped form of a frame of the code. -/
theorem frame_mem_unstrip {code body : List Admin} {n : Nat} {fi : Frame}
    (hm : .frame n fi body ∈ stripAdmins10 code) :
    ∃ fi₀ body₀, .frame n fi₀ body₀ ∈ code ∧ fi = stripFrame10 fi₀ ∧
      body = stripAdmins10 body₀ := by
  rw [stripAdmins10_eq_map] at hm
  obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
  cases a with
  | frame n₀ fi₀ body₀ =>
    have he' : n₀ = n ∧ stripFrame10 fi₀ = fi ∧ stripAdmins10 body₀ = body := by simpa using he
    exact ⟨fi₀, body₀, he'.1 ▸ ha, he'.2.1.symm, he'.2.2.symm⟩
  | _ => simp [stripAdmin10] at he

/-- **An active piece of source instructions in stripped code** is an active piece of the
original code, read in a frame that strips to the same frame. -/
theorem activeF_unstrip {F C f' w} (h : ActiveF F C f' w) {ws : List V1.Instr}
    (hw : w = ws.map .source) :
    ∀ {f : Frame} {code : List Admin}, F = stripFrame10 f → C = stripAdmins10 code →
      ∃ f'', ActiveF f code f'' w ∧ stripFrame10 f'' = f' := by
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
theorem gSetOk_strip10 {s : Store H} {f : Frame} {code : List Admin} (h : GSetOk s f code) :
    GSetOk (stripStore10 s) (stripFrame10 f) (stripAdmins10 code) := by
  intro f' v x a g hA hx hg
  obtain ⟨i, hi⟩ := Whole.value_source v
  obtain ⟨f'', hA', rfl⟩ := activeF_unstrip hA (ws := [i, .globalSet x])
    (by simp [hi]) rfl rfl
  exact h f'' v x a g hA' hx hg

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
