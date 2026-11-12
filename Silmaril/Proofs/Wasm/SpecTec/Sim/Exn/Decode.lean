module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Otherwise

/-!
# Family X: decoding the encoding at the tags the exception rules use

`instrToV_case` and `adminToV_case` read an instruction back from its image when the head tag
is one the exception rules match (`REF.NULL_ADDR`, `REF.EXN_ADDR`, `THROW_REF`, `THROW`,
`TRY_TABLE`, `HANDLER_%{%}%`, `LABEL_%{%}%`, `FRAME_%{%}%`). The proof is a case split over every
instruction. Along the way it shows that `instrToV` sends the invalid integer extensions (a pack
size not narrower than the type) and **every `trunc_sat` conversion** to the junk value
`.tuple []`, which is `Equiv.instrV`'s fallback. Family E should fix the
`trunc_sat` clause.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core


/-- A schema constructor is encoded with its own tag. -/
theorem schemaInstrV_case (c : Silmaril.Wasm.SpecTecEnc.Constructor) :
    ∃ w, schemaInstrV c = .case c.tag w := by
  unfold schemaInstrV
  split <;> exact ⟨_, rfl⟩


set_option maxHeartbeats 4000000 in
/-- The tags an instruction can encode to, as far as the exception rules care. -/
theorem instrToV_case {i : Instr} {op : MixopS} {w : Value} (h : instrToV i = .case op w) :
    (op = "THROW_REF" → i = .throwRef) ∧
    (op = "THROW" → ∃ x, i = .throw x ∧ w = Encode.toValue x) ∧
    (op = "TRY_TABLE" → ∃ bt cs body, i = .tryTable bt cs body ∧
      w = .tuple [Encode.toValue bt, .case "%" (.tuple [.list (cs.map Encode.toValue)]),
        .list (instrsToV body)]) ∧
    op ≠ "REF.NULL_ADDR" ∧ op ≠ "REF.EXN_ADDR" ∧ op ≠ "HANDLER_%{%}%" ∧
    op ≠ "LABEL_%{%}%" ∧ op ≠ "FRAME_%{%}%" := by
  cases i
  all_goals try first
    | (obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp)
    | (have h' : schemaInstrV (Silmaril.Wasm.SpecTecEnc.encodeInstruction _) = _ := h
       obtain ⟨w', hw'⟩ := schemaInstrV_case (Silmaril.Wasm.SpecTecEnc.encodeInstruction _)
       rw [hw'] at h'
       obtain ⟨rfl, rfl⟩ := Value.case.inj h'
       simp [Silmaril.Wasm.SpecTecEnc.encodeInstruction])
  iterate 4 (all_goals (try (rename_i x; cases x)))
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp)
    | exact Value.noConfusion h

/-- The tags an administrative instruction can encode to, as far as the exception rules care. -/
theorem adminToV_case {a : Admin} {op : MixopS} {w : Value} (h : adminToV a = .case op w) :
    (op = "REF.NULL_ADDR" → a = .ref .null) ∧
    (op = "REF.EXN_ADDR" → ∃ k, a = .ref (.exn k) ∧ w = .num (.natN k)) ∧
    (op = "THROW_REF" → a = .plain .throwRef) ∧
    (op = "THROW" → ∃ x, a = .plain (.throw x) ∧ w = Encode.toValue x) ∧
    (op = "TRY_TABLE" → ∃ bt cs body, a = .plain (.tryTable bt cs body) ∧
      w = .tuple [Encode.toValue bt, .case "%" (.tuple [.list (cs.map Encode.toValue)]),
        .list (instrsToV body)]) ∧
    (op = "HANDLER_%{%}%" → ∃ n cs body, a = .handler n cs body ∧
      w = .tuple [.num (.natN n), .list (cs.map Encode.toValue), .list (adminsToV body)]) ∧
    (op = "LABEL_%{%}%" → ∃ n cont body, a = .label n cont body ∧
      w = .tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)]) ∧
    (op = "FRAME_%{%}%" → ∃ n fr body, a = .frame n fr body ∧
      w = .tuple [.num (.natN n), frameV fr, .list (adminsToV body)]) := by
  cases a with
  | plain i =>
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := instrToV_case h
      refine ⟨fun e => absurd e h₄, fun e => absurd e h₅, fun e => by rw [h₁ e], fun e => ?_,
        fun e => ?_, fun e => absurd e h₆, fun e => absurd e h₇, fun e => absurd e h₈⟩
      · obtain ⟨x, rfl, rfl⟩ := h₂ e
        exact ⟨x, rfl, rfl⟩
      · obtain ⟨bt, cs, body, rfl, rfl⟩ := h₃ e
        exact ⟨bt, cs, body, rfl, rfl⟩
  | ref r =>
      cases r <;> (obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp)
  | callRefType d => obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp
  | returnCallRefType d => obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp
  | label n cont body => obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp
  | handler n cs body => obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp
  | frame n fr body => obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp
  | trap => obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp


/-! ## Injectivity and sequence decoding -/

/-- `Encode.toValue` is injective. -/
theorem toValue_inj {α : Type} [Encode α] {a b : α} (h : Encode.toValue a = Encode.toValue b) :
    a = b := by
  have h' := congrArg (Encode.ofValue (α := α)) h
  rw [Encode.ofValue_toValue, Encode.ofValue_toValue] at h'
  exact Option.some.inj h'

/-- …and so is it on lists. -/
theorem map_toValue_inj {α : Type} [Encode α] {a b : List α}
    (h : a.map Encode.toValue = b.map Encode.toValue) : a = b :=
  List.map_injective_iff.2 (fun _ _ => toValue_inj) h

/-- A one-element image. -/
theorem adminsToV_eq_one {l : List Admin} {x : Value} (h : adminsToV l = [x]) :
    ∃ a, l = [a] ∧ adminToV a = x := by
  rw [adminsToV_eq_map] at h
  obtain ⟨a, rest, rfl, ha, hr⟩ := List.map_eq_cons_iff.1 h
  obtain rfl := List.map_eq_nil_iff.1 hr
  exact ⟨a, rfl, ha⟩

/-- A two-element image. -/
theorem adminsToV_eq_two {l : List Admin} {x y : Value} (h : adminsToV l = [x, y]) :
    ∃ a b, l = [a, b] ∧ adminToV a = x ∧ adminToV b = y := by
  rw [adminsToV_eq_map] at h
  obtain ⟨a, rest, rfl, ha, hr⟩ := List.map_eq_cons_iff.1 h
  obtain ⟨b, rest', rfl, hb, hr'⟩ := List.map_eq_cons_iff.1 hr
  obtain rfl := List.map_eq_nil_iff.1 hr'
  exact ⟨a, b, rfl, ha, hb⟩

/-- A sequence encoded as `REF.EXN_ADDR v; THROW_REF` is `throwing k`. -/
theorem adminsToV_eq_throwing {l : List Admin} {v : Value}
    (h : adminsToV l = [.case "REF.EXN_ADDR" v, .case "THROW_REF" (.tuple [])]) :
    ∃ k, l = throwing k ∧ v = .num (.natN k) := by
  obtain ⟨a, b, rfl, ha, hb⟩ := adminsToV_eq_two h
  obtain ⟨k, rfl, rfl⟩ := (adminToV_case ha).2.1 rfl
  obtain rfl := (adminToV_case hb).2.2.1 rfl
  exact ⟨k, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Exn
