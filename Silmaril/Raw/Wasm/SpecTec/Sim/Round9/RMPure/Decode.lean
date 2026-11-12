module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.Thms
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms

/-!
# Round 9, rm: decoding `adminsToVD` images (unrefined)

Round 6's backward leaves for the control rules of `Step_pure` decode `adminsToV` images through
`CtrlDecode`. At `adminsToVD`, an instruction whose head is not `RMAtom.badHead` has the same
image under both encodings (`toV_of_atomD`), so those decoders apply unchanged; the structured
heads (`LABEL_`, `HANDLER_`, `FRAME_`, `IF`) are decoded directly (`labelD_of`, `handlerD_of`,
`frameD_of`, `ifD_of`), and a typed `val*` prefix is a value sequence (`vals_of_typedD`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMPure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (adminsToVD adminToVD instrsToVD adminToVD_case adminsToVD_eq_map)

/-- **At a head that is not `badHead`, the two encodings agree.** -/
theorem toV_of_atomD {a : Admin} {op : MixopS} {x : Value} (h : adminToVD a = .case op x)
    (hop : RMAtom.badHead op = false) : adminToV a = .case op x := by
  have hh : op = Typing.adminHead a := adminToVD_case h
  have hms : Round6.MemSimd.AdminMS a := RMAtom.adminMS_of_head (hh ▸ hop)
  rw [← Round7.MemSimd.adminToVD_eq a hms]
  exact h

/-- A `LABEL_` image at `adminToVD`. -/
theorem labelD_of {a : Admin} {n c b : Value}
    (h : adminToVD a = .case "LABEL_%{%}%" (.tuple [n, c, b])) :
    ∃ k cont body, a = .label k cont body ∧ n = .num (.natN k) ∧
      c = .list (instrsToVD cont) ∧ b = .list (adminsToVD body) := by
  have hh := adminToVD_case h
  cases a with
  | plain i => cases i <;> simp [Typing.adminHead, Typing.instrHead] at hh
  | label k cont body =>
    simp only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
      and_true] at h
    exact ⟨k, cont, body, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  | ref r => cases r <;> simp [Typing.adminHead, Typing.refHead] at hh
  | _ => simp [Typing.adminHead] at hh

/-- A `HANDLER_` image at `adminToVD`. -/
theorem handlerD_of {a : Admin} {n c b : Value}
    (h : adminToVD a = .case "HANDLER_%{%}%" (.tuple [n, c, b])) :
    ∃ k cs body, a = .handler k cs body ∧ n = .num (.natN k) ∧
      c = .list (cs.map Encode.toValue) ∧ b = .list (adminsToVD body) := by
  have hh := adminToVD_case h
  cases a with
  | plain i => cases i <;> simp [Typing.adminHead, Typing.instrHead] at hh
  | handler k cs body =>
    simp only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
      and_true] at h
    exact ⟨k, cs, body, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  | ref r => cases r <;> simp [Typing.adminHead, Typing.refHead] at hh
  | _ => simp [Typing.adminHead] at hh

/-- A `FRAME_` image at `adminToVD`. -/
theorem frameD_of {a : Admin} {n c b : Value}
    (h : adminToVD a = .case "FRAME_%{%}%" (.tuple [n, c, b])) :
    ∃ k fi body, a = .frame k fi body ∧ n = .num (.natN k) ∧ c = frameV fi ∧
      b = .list (adminsToVD body) := by
  have hh := adminToVD_case h
  cases a with
  | plain i => cases i <;> simp [Typing.adminHead, Typing.instrHead] at hh
  | frame k fi body =>
    simp only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
      and_true] at h
    exact ⟨k, fi, body, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  | ref r => cases r <;> simp [Typing.adminHead, Typing.refHead] at hh
  | _ => simp [Typing.adminHead] at hh

/-- An `IF` image at `adminToVD`. -/
theorem ifD_of {a : Admin} {bt' v₁ v₂ : Value}
    (h : adminToVD a = .case "IF%%ELSE%" (.tuple [bt', v₁, v₂])) :
    ∃ bt b₁ b₂, a = .plain (.if_ bt b₁ b₂) ∧ bt' = Encode.toValue bt ∧
      v₁ = .list (instrsToVD b₁) ∧ v₂ = .list (instrsToVD b₂) := by
  have hh := adminToVD_case h
  cases a with
  | plain i =>
    cases i <;> simp [Typing.adminHead, Typing.instrHead] at hh
    rename_i bt b₁ b₂
    simp only [adminToVD, Round7.MemSimd.instrToVD, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, true_and, and_true] at h
    exact ⟨bt, b₁, b₂, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  | ref r => cases r <;> simp [Typing.adminHead, Typing.refHead] at hh
  | _ => simp [Typing.adminHead] at hh

/-- An `adminsToVD` image split around one element. -/
theorem adminsToVD_eq_split {l : List Admin} {A C : List Value} {x : Value}
    (h : adminsToVD l = A ++ [x] ++ C) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ adminsToVD l₁ = A ∧ adminToVD a = x ∧
      adminsToVD l₂ = C := by
  obtain ⟨l₁, m, l₂, rfl, h₁, hm, h₂⟩ := Round7.MemSimd.adminsToVD_split3 h
  obtain ⟨a, rfl, ha⟩ := Round7.MemSimd.adminsToVD_eq_single hm
  exact ⟨l₁, a, l₂, rfl, h₁, ha, h₂⟩

/-- A typed `val*` prefix at `adminsToVD`, decoded with its image. -/
theorem valsD_of {B : Builtins} {σ : List (IL.Id × Value)} {l : List Admin} {ws : List Value}
    (hl : adminsToVD l = ws) (ht : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs, l = vals vs ∧ adminsToV (vals vs) = ws ∧ ws.length = vs.length := by
  obtain ⟨vs, rfl⟩ := Round7.MemSimd.vals_of_typedD (B := B) ⟨rfl, rfl, rfl⟩ (hl ▸ ht)
  have h' : adminsToV (vals vs) = ws := by rw [← hl, Round7.MemSimd.adminsToVD_vals]
  exact ⟨vs, rfl, h', by rw [← h', adminsToV_length, vals_length]⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.RMPure
