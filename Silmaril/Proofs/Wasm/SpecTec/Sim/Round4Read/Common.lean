module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4Read.Generic
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Dispatch
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.TableFwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.TableAll
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Refs

/-!
# Shared readers

* `idx_of_valid`, `table_of_isSome`, …: index resolution read off `ReadValid`.
* `decode_aconst_at`: an instruction whose image is `CONST at i`, with `at` the image of an
  address type, is that address type's constant.
* `cfgV_quad`: the image of a four-instruction configuration, as a `cfgV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)

variable {H : Type}

/-! ## Index resolution -/

/-- The last instruction of a valid code sequence has its indices resolved. -/
theorem idx_last {s : Store H} {f : Frame} {l : List Admin} {i : Instr}
    (h : codeIdx s f (l ++ [.plain i])) : Instr.IdxOk s f i :=
  ((codeIdx_append _ _).1 h).2.1

/-- The last instruction of a four-instruction valid configuration. -/
theorem idx_last4 {c : Config H} {a₁ a₂ a₃ : Admin} {i : Instr}
    (hv : ReadValid c) (h : c.code = [a₁, a₂, a₃, .plain i]) : Instr.IdxOk c.store c.frame i := by
  have := hv.idx
  rw [h] at this
  exact idx_last (l := [a₁, a₂, a₃]) this

/-- A resolved table. -/
theorem table_of_isSome {s : Store H} {f : Frame} {x : TableIdx} (h : (s.table? f x).isSome) :
    ∃ ta ti, s.table? f x = some (ta, ti) := by
  obtain ⟨⟨ta, ti⟩, h⟩ := Option.isSome_iff_exists.1 h
  exact ⟨ta, ti, h⟩

/-- A resolved element segment. -/
theorem elem_of_isSome {s : Store H} {f : Frame} {x : ElemIdx} (h : (s.elem? f x).isSome) :
    ∃ ea ei, s.elem? f x = some (ea, ei) := by
  obtain ⟨⟨ea, ei⟩, h⟩ := Option.isSome_iff_exists.1 h
  exact ⟨ea, ei, h⟩

/-- A resolved memory. -/
theorem mem_of_isSome {s : Store H} {f : Frame} {x : MemIdx} (h : (s.mem? f x).isSome) :
    ∃ ma mi, s.mem? f x = some (ma, mi) := by
  obtain ⟨⟨ma, mi⟩, h⟩ := Option.isSome_iff_exists.1 h
  exact ⟨ma, mi, h⟩

/-- A resolved data segment. -/
theorem data_of_isSome {s : Store H} {f : Frame} {x : DataIdx} (h : (s.data? f x).isSome) :
    ∃ da di, s.data? f x = some (da, di) := by
  obtain ⟨⟨da, di⟩, h⟩ := Option.isSome_iff_exists.1 h
  exact ⟨da, di, h⟩

/-! ## Decoding address-typed constants -/

/-- **An address-typed constant, decoded from its type.** -/
theorem decode_aconst_at {a : Admin} {t : AddrType} {I : Value}
    (h : adminToV a = .case "CONST" (.tuple [Encode.toValue t, I])) :
    ∃ b : BitVec t.intType.width, a = aconst t b ∧ I = idxV b.toNat := by
  rcases Typing.head_const (Typing.adminToV_case h).symm with ⟨t', b, rfl⟩ | ⟨t', b, rfl⟩
  · cases t' <;> cases t
    · have h' : valV (.num ⟨.int .i32, b⟩) = _ := h
      simp only [valV, numV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
        true_and] at h'
      exact ⟨b, rfl, h'.2.symm⟩
    · have h' : valV (.num ⟨.int .i32, b⟩) = _ := h
      simp [valV, numV, Encode.toValue] at h'
    · have h' : valV (.num ⟨.int .i64, b⟩) = _ := h
      simp [valV, numV, Encode.toValue] at h'
    · have h' : valV (.num ⟨.int .i64, b⟩) = _ := h
      simp only [valV, numV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
        true_and] at h'
      exact ⟨b, rfl, h'.2.symm⟩
  · have h' : valV (.num ⟨.float t', b⟩) = _ := h
    cases t' <;> cases t <;> simp [valV, numV, floatV, Encode.toValue] at h'

/-! ## Inverting the typing of `addrtype` -/

/-- A payload typed by some case of a variant names one of its cases. -/
theorem findCase_of_hasTypCase {env : Env} {σ : VarEnv} :
    ∀ {cs : List TypCase} {op : MixopS} {w : Value}, HasTypCase env σ cs op w →
      ∃ tp, IntNumeric.findCase cs op = some tp
  | [], _, _, h => absurd h not_hasTypCase_nil
  | .mk o t' _ prems' :: _, op, _, h => by
      by_cases ho : o = op
      · subst ho
        exact ⟨(t', prems'), by simp [IntNumeric.findCase]⟩
      · simpa [IntNumeric.findCase, ho] using
          findCase_of_hasTypCase ((hasTypCase_cons_miss_iff ho).1 h)

/-- **Inversion of `addrtype`**: a typed `addrtype` is an injection named by one of its cases. -/
theorem addrtype_inv {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "addrtype" []) v) :
    ∃ op w tp, v = .case op w ∧
      IntNumeric.findCase (IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d88 0)
        op = some tp := by
  have hl : localTyp? ρ "addrtype" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [Typing.findTyp_addrtype] at htd
  cases htd
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hi'
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    exact ⟨op, w, _, rfl, (findCase_of_hasTypCase hc).choose_spec⟩
  · exact absurd hi' not_hasTypInsts_nil

set_option maxRecDepth 100000 in
/-- `F32` is not an `addrtype`. -/
theorem findCase_addrtype_f32 :
    IntNumeric.findCase (IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d88 0)
      "F32" = none := by decide

set_option maxRecDepth 100000 in
/-- `F64` is not an `addrtype`. -/
theorem findCase_addrtype_f64 :
    IntNumeric.findCase (IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d88 0)
      "F64" = none := by decide

/-- A float constant's number type is not an `addrtype`. -/
theorem not_addrtype_float {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {t : FloatType}
    {b : BitVec t.width} {AT I : Value}
    (h : valV (.num ⟨.float t, b⟩) = .case "CONST" (.tuple [AT, I]))
    (hAT : HasTyp (simEnv B) ρ (.varT "addrtype" []) AT) : False := by
  obtain ⟨op, w, tp, rfl, hf⟩ := addrtype_inv hρ hAT
  cases t <;> simp only [valV, numV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at h
  · have e : Value.case op w = Value.case "F32" (.tuple []) := h.2.1.symm.trans rfl
    injection e with e₁
    subst e₁
    simp [findCase_addrtype_f32] at hf
  · have e : Value.case op w = Value.case "F64" (.tuple []) := h.2.1.symm.trans rfl
    injection e with e₁
    subst e₁
    simp [findCase_addrtype_f64] at hf

/-- **An address-typed constant, decoded from the typing of its type.** -/
theorem decode_aconst_typed {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {a : Admin}
    {AT I : Value} (h : adminToV a = .case "CONST" (.tuple [AT, I]))
    (hAT : HasTyp (simEnv B) ρ (.varT "addrtype" []) AT) :
    ∃ (t : AddrType) (b : BitVec t.intType.width), a = aconst t b ∧ AT = Encode.toValue t ∧
      I = idxV b.toNat := by
  rcases Typing.head_const (Typing.adminToV_case h).symm with ⟨t', b, rfl⟩ | ⟨t', b, rfl⟩
  · cases t'
    · have h' : valV (.num ⟨.int .i32, b⟩) = _ := h
      simp only [valV, numV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
        true_and] at h'
      exact ⟨.i32, b, rfl, h'.1.symm, h'.2.symm⟩
    · have h' : valV (.num ⟨.int .i64, b⟩) = _ := h
      simp only [valV, numV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
        true_and] at h'
      exact ⟨.i64, b, rfl, h'.1.symm, h'.2.symm⟩
  · exact (not_addrtype_float hρ h hAT).elim

/-! ## The bounds -/

/-- Under the store bounds, a resolved table is shorter than `2 ^ 32`. -/
theorem table_lt32 {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (hs : Integrate.StoreOk s) (ht : s.table? f x = some (ta, ti)) : ti.refs.length < 2 ^ 32 :=
  hs.tables.1 ti (List.mem_of_getElem? (State.Store.table?_eq_some ht).2)

/-- Under the store bounds, a resolved element segment is shorter than `2 ^ 32`. -/
theorem elem_lt32 {s : Store H} {f : Frame} {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (hs : Integrate.StoreOk s) (he : s.elem? f y = some (ea, ei)) : ei.refs.length < 2 ^ 32 :=
  hs.tables.2 ei (List.mem_of_getElem? (State.Store.elem?_eq_some he).2)

/-- Both address types are at least 32 bits wide. -/
theorem lt_width {a : AddrType} {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ a.intType.width :=
  Nat.lt_of_lt_of_le h (Memory.pow32_le a)

end Silmaril.Wasm.SpecTec.Sim.Round4Read
