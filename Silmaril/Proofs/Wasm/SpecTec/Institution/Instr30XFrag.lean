module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XNum

/-!
# Instruction typing of the wasm-3.0 script, extended: preservation over `fragX`

The model is `stepModel BI`, as in `Instr30`.

* `instrX_preserves`: on `DomX`, an `Instr_ok {}` judgement Core validates is a fact: `Instr30`'s
  instructions, and the integer numeric ones through `Instr30XNum`.
* `fragOkX_dd`, `instrsX_preserves`, `instrsX_holds`: the same for `Instrs_ok {}` on `FragOkX`
  derivations.
* `constAdd`: non-vacuity, `i32.const a; i32.const b; i32.add` at `[] -> [i32]`, through
  `Instrs_ok/seq` twice and `Instrs_ok/frame`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (tyV instrtypeV)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ISen ItBnd frag itV ctxT_empty typedV_vals
  instrtypeV_plain instrsToV_append)

variable {H : Type} (P : Profile) (hn : H → String) (host : HostSemantics H)

/-- The model: `stepModel` at the concrete primitives `BI`. -/
local notation "MB" => Wasm30.stepModel (Round4Int.BI P hn host)

/-- Its evaluator. -/
local notation "EB" => simEnv (Round4Int.BI P hn host)

/-- Core types an integer numeric instruction by its numeric family only. -/
theorem numericOk_of {i : Instr} {it : InstrType} (hf : intNum i = true) (h : InstrOk {} i it) :
    NumericInstrOk {} i it := by
  cases i <;> simp only [intNum, Bool.false_eq_true] at hf <;>
    cases h <;> first | assumption | (rename_i h; nomatch h)

/-- An integer numeric instruction Core validates at `it`, as an `Instr_ok {}` fact. -/
theorem instr_intNum (O : ElseI) {i : Instr} {it : InstrType} (hf : intNum i = true)
    (h : InstrOk {} i it) :
    DDerivesB (EB) O "Instr_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, instrToV i, instrtypeV it]) := by
  cases numericOk_of hf h with
  | intConst t b => exact dd_intConst O ctxT_empty t b
  | intUnOp hv => exact dd_intUnOp O ctxT_empty hv
  | intBinOp t op => exact dd_intBinOp O ctxT_empty t op
  | intTestOp t op => exact dd_intTestOp O ctxT_empty t op
  | intRelOp t op => exact dd_intRelOp O ctxT_empty t op
  | _ => simp [intNum] at hf

/-- `Instr_ok {}` on `fragX` at a bounded type, under every reading of `otherwise`. -/
theorem instrX_preserves' (O : ElseI) {i : Instr} {it : InstrType} (hf : fragX i = true)
    (hb : ItBnd it) (h : InstrOk {} i it) :
    DDerivesB (EB) O "Instr_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, instrToV i, instrtypeV it]) := by
  rcases Bool.or_eq_true_iff.1 hf with hf | hf
  · exact Instr30.instr_preserves' P hn host O hf hb h
  · exact instr_intNum P hn host O hf h

/-- **Core validation is preserved** for `Instr_ok` on `DomX`. -/
theorem instrX_preserves {i : Instr} {it : InstrType} (hd : DomX (ISen.instr i it))
    (h : (ISen.instr i it).Holds) : ((ISen.instr i it).toSen).Sat backend (MB).env (MB).D :=
  instrX_preserves' P hn host _ hd.1 hd.2 h

/-! ## Sequences -/

set_option maxRecDepth 100000 in
/-- A valid instruction of `fragX` has a typed image. -/
theorem typedV_fragX {B : Builtins} {i : Instr} {it : InstrType} (hf : fragX i = true)
    (h : InstrOk {} i it) : TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  rcases Bool.or_eq_true_iff.1 hf with hf | hf
  · exact Instr30.typedV_frag hf
  · cases i <;> simp only [intNum, Bool.false_eq_true] at hf
    · exact Round5.Pos.typedV_instrToV_of _ rfl rfl fun _ hb => by simp [Instr.bodies] at hb
    · exact Round5.Pos.typedV_intNumeric h (.inl ⟨_, _, rfl⟩)
    · exact Round5.Pos.typedV_intNumeric h (.inr (.inl ⟨_, _, rfl⟩))
    · exact Round5.Pos.typedV_intNumeric h (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    · exact Round5.Pos.typedV_intNumeric h (.inr (.inr (.inr ⟨_, _, rfl⟩)))

/-- A `FragOkX` derivation is a Core derivation. -/
theorem fragOkX_sound {is : List Instr} {it : InstrType} (h : FragOkX is it) : InstrsOk {} is it := by
  induction h with
  | nil => exact .nil
  | instr _ _ h => exact .instr h
  | seq _ _ _ ih₁ ih₂ => exact .seq ih₁ (fun _ hx => absurd hx List.not_mem_nil) ih₂
  | frame _ hok _ ih => exact .frame ih hok

/-- A `FragOkX` derivation has bounded types. -/
theorem fragOkX_bnd {is : List Instr} {it : InstrType} (h : FragOkX is it) : ItBnd it := by
  induction h with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | instr _ hb _ => exact hb
  | seq _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | frame hb _ _ ih =>
    exact ⟨fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.1 t),
      fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.2 t)⟩

/-- The instructions of a `FragOkX` derivation have typed images. -/
theorem fragOkX_typed {B : Builtins} {is : List Instr} {it : InstrType} (h : FragOkX is it) :
    ∀ v ∈ instrsToV is, TypedV (simEnv B) (.varT "instr" []) v := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | instr hf _ h =>
    intro v hv
    rw [Exn.instrsToV_eq_map] at hv
    obtain rfl := List.mem_singleton.1 hv
    exact typedV_fragX hf h
  | seq _ _ _ ih₁ ih₂ =>
    intro v hv
    rw [instrsToV_append] at hv
    exact (List.mem_append.1 hv).elim (ih₁ v) (ih₂ v)
  | frame _ _ _ ih => exact ih

/-- **`FragOkX` derivations are read by `DDerivesB`.** -/
theorem fragOkX_dd (O : ElseI) {is : List Instr} {it : InstrType} (h : FragOkX is it) :
    DDerivesB (EB) O "Instrs_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list (instrsToV is), instrtypeV it]) := by
  induction h with
  | nil => exact Instr30.dd_instrsEmpty O ctxT_empty
  | instr hf hb h =>
    exact Instr30.dd_instrsInstr O ctxT_empty (typedV_fragX hf h) (typedV_vals hb.1)
      (fun _ h => absurd h List.not_mem_nil) (typedV_vals hb.2) (instrX_preserves' P hn host O hf hb h)
  | @seq is₁ is₂ t₁ t₂ t₃ hb h₁ h₂ ih₁ ih₂ =>
    show DDerivesB (EB) O "Instrs_ok" "%|-%:%" [] (.tuple [Round6.RefOkV.ctxEmptyV,
      .list (instrsToV (is₁ ++ is₂)), itV (t₁.map tyV) [] (t₃.map tyV)])
    rw [instrsToV_append]
    exact Instr30.dd_instrsSeq O ctxT_empty (fragOkX_typed h₁) (fragOkX_typed h₂)
      (typedV_vals (fragOkX_bnd h₁).1) (typedV_vals hb) (typedV_vals (fragOkX_bnd h₂).2) ih₁ ih₂
  | @frame is ts t₁ t₂ hb hok h ih =>
    show DDerivesB (EB) O "Instrs_ok" "%|-%:%" [] (.tuple [Round6.RefOkV.ctxEmptyV,
      .list (instrsToV is), itV ((ts ++ t₁).map tyV) [] ((ts ++ t₂).map tyV)])
    rw [List.map_append, List.map_append]
    exact Instr30.dd_instrsFrame O ctxT_empty (fragOkX_typed h) (typedV_vals hb)
      (typedV_vals (fragOkX_bnd h).1) (typedV_vals (fragOkX_bnd h).2) ih
      (Instr30.resulttypeOk_of P hn host O hb hok)

/-- **Core validation is preserved** for `Instrs_ok` on `DomX`. -/
theorem instrsX_preserves {is : List Instr} {it : InstrType} (hd : DomX (ISen.instrs is it)) :
    ((ISen.instrs is it).toSen).Sat backend (MB).env (MB).D :=
  fragOkX_dd P hn host _ hd

/-- `instrs` judgements in `DomX` hold in Core. -/
theorem instrsX_holds {is : List Instr} {it : InstrType} (hd : DomX (ISen.instrs is it)) :
    (ISen.instrs is it).Holds :=
  fragOkX_sound hd

/-! ## Non-vacuity -/

/-- `i32` is bounded. -/
theorem bnd_i32 : ∀ t ∈ [Ty.i32], Round4.tyBnd t = true := fun _ ht => (List.mem_singleton.1 ht) ▸ rfl

/-- `i32 i32` is bounded. -/
theorem bnd_i32i32 : ∀ t ∈ [Ty.i32, Ty.i32], Round4.tyBnd t = true := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ht
  exact ht ▸ rfl

/-- `[]` is bounded. -/
theorem bnd_nil : ∀ t ∈ ([] : List CValType), Round4.tyBnd t = true :=
  fun _ h => absurd h List.not_mem_nil

/-- `i32.const a; i32.const b; i32.add` at `[] -> [i32]`: the second constant is framed under the
first, and the add is sequenced after both. -/
theorem fragOkX_constAdd (a b : BitVec 32) :
    FragOkX [.intConst .i32 a, .intConst .i32 b, .intBinOp .i32 .add] (.plain [] [Ty.i32]) := by
  have hc (x : BitVec 32) : FragOkX [.intConst .i32 x] (.plain [] [Ty.i32]) :=
    .instr rfl ⟨bnd_nil, bnd_i32⟩ (.numeric (.intConst .i32 x))
  have hcc : FragOkX [.intConst .i32 a, .intConst .i32 b] (.plain [] [Ty.i32, Ty.i32]) :=
    .seq (is₁ := [.intConst .i32 a]) (is₂ := [.intConst .i32 b]) bnd_i32 (hc a)
      (.frame (ts := [Ty.i32]) (t₁ := []) bnd_i32
        (fun _ ht => (List.mem_singleton.1 ht) ▸ TyOk.num _) (hc b))
  exact .seq (is₁ := [.intConst .i32 a, .intConst .i32 b]) (is₂ := [.intBinOp .i32 .add])
    bnd_i32i32 hcc (.instr rfl ⟨bnd_i32i32, bnd_i32⟩ (.numeric (.intBinOp .i32 .add)))

/-- **Non-vacuity**: `i32.const a; i32.const b; i32.add` at `[] -> [i32]` is an `Instrs_ok {}`
fact of `stepModel BI` and Core-valid. -/
theorem constAdd (a b : BitVec 32) :
    ((ISen.instrs [.intConst .i32 a, .intConst .i32 b, .intBinOp .i32 .add]
        (.plain [] [Ty.i32])).toSen).Sat backend (MB).env (MB).D ∧
      (ISen.instrs [.intConst .i32 a, .intConst .i32 b, .intBinOp .i32 .add]
        (.plain [] [Ty.i32])).Holds :=
  ⟨instrsX_preserves P hn host (fragOkX_constAdd a b), instrsX_holds (fragOkX_constAdd a b)⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30X
