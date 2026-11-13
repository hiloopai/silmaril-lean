module

public import Silmaril.Wasm.SpecTec.Institution.Instr30.Thms

/-!
# Instruction typing of the wasm-3.0 script, extended: `Instrs_ok` is not reflected

`Instr30.instrs_holds` reflects `Instrs_ok {}` only on its domain, the `FragOk` derivations, which
is a Core-side condition. On the syntactic domain (sequences of `Instr30.frag` instructions at
bounded types) reflection fails:

* `instrsOk_params`: in Core, every derivation of `C ⊢ is : t₁ -> t₂` over `frag` instructions has
  valid parameter types `t₁` (each of the six `Instrs_ok` rules either reads `t₁` off a
  `nop`/`unreachable`/`drop` typing or a sub-derivation, or checks it: `sub` by
  `Instrtype_ok`, `frame` by `Resulttype_ok`);
* `not_dropNestedS`: so Core rejects `{} ⊢ drop : [REF NULL D_out] -> []`;
* `dropNestedS`: while `stepModel BI` has it as an `Instrs_ok {}` fact, through `Instrs_ok/instr`
  over `Instr30.drop_nested`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ISen ItBnd frag ctxT_empty typedV_vals)

/-- Core types a `frag` instruction by its parametric family only. -/
theorem parametricOk_of {C : Context} {i : Instr} {it : InstrType} (hf : frag i = true)
    (h : InstrOk C i it) : ParametricInstrOk C i it := by
  cases i <;> simp only [frag, Bool.false_eq_true] at hf <;>
    cases h <;> first | assumption | (rename_i h; nomatch h)

/-- A `frag` instruction Core types at `t₁ -> t₂` has valid parameters. -/
theorem instrOk_frag_params {C : Context} {i : Instr} {it : InstrType} (hf : frag i = true)
    (h : InstrOk C i it) : ResultOk C.toTypeCtx it.params := by
  cases parametricOk_of hf h with
  | nop => exact fun _ h => absurd h List.not_mem_nil
  | unreachable hok => exact hok.1
  | drop ht => exact fun _ ht' => (List.mem_singleton.1 ht') ▸ ht
  | _ => simp [frag] at hf

/-- **Core derivations over `frag` instructions have valid parameter types.** -/
theorem instrsOk_params {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    (hf : ∀ i ∈ is, frag i = true) : ResultOk C.toTypeCtx it.params :=
  match h with
  | .nil => fun _ h => absurd h List.not_mem_nil
  | .instr hi => instrOk_frag_params (hf _ (List.mem_singleton_self _)) hi
  | .seq h₁ _ _ => by
    have h' := instrsOk_params h₁ fun i hi => hf i (List.mem_append_left _ hi)
    exact h'
  | .cons hi _ _ => by
    have h' := instrOk_frag_params (hf _ List.mem_cons_self) hi
    exact h'
  | .sub _ _ hok => hok.1
  | .frame h hok => fun t ht =>
    (List.mem_append.1 ht).elim (hok t) (instrsOk_params h hf t)

/-- `drop` at `[REF NULL D_out] -> []`, as a sequence. -/
def dropNestedS : ISen := .instrs [.drop] (.plain [.refv Round5.RefOk.nestedRT] [])

/-- **Core rejects `drop` at `REF NULL D_out`, as a sequence.** -/
theorem not_dropNestedS : ¬ dropNestedS.Holds := by
  intro h
  have hp := instrsOk_params h fun i hi => (List.mem_singleton.1 hi) ▸ rfl
  cases hp _ (List.mem_singleton_self _) with
  | refv hr => exact Round5.RefOk.not_tyOk_nested hr

variable {H : Type} (P : Profile) (hn : H → String) (host : HostSemantics H)

/-- **`Instrs_ok` is not reflected on reached sequences at bounded types**: `[drop]` at
`[REF NULL D_out] -> []` is over `frag`, at a bounded type, an `Instrs_ok {}` fact of
`stepModel BI`, and Core rejects it. -/
theorem dropNestedS_not_reflected :
    (∀ i ∈ [Instr.drop], frag i = true) ∧ ItBnd (.plain [.refv Round5.RefOk.nestedRT] []) ∧
      (dropNestedS.toSen).Sat backend (Wasm30.stepModel (Round4Int.BI P hn host)).env
        (Wasm30.stepModel (Round4Int.BI P hn host)).D ∧ ¬ dropNestedS.Holds := by
  obtain ⟨hd, hs, -⟩ := Instr30.drop_nested P hn host
  refine ⟨fun i hi => (List.mem_singleton.1 hi) ▸ rfl, hd.2, ?_, not_dropNestedS⟩
  exact Instr30.dd_instrsInstr _ ctxT_empty (Instr30.typedV_frag rfl) (typedV_vals hd.2.1)
    (fun _ h => absurd h List.not_mem_nil) (typedV_vals hd.2.2) hs

end Silmaril.Wasm.SpecTec.Institution.Instr30X
