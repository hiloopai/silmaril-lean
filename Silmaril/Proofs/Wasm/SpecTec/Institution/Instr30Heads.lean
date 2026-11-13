module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Rules

/-!
# Instruction typing of the wasm-3.0 script: which rules can type which instruction

Every one of the 110 rules of `Instr_ok` has a conclusion `(C, OP …, it)`: its instruction is a
case expression with a fixed head `OP` (`ruleHead`). `instrOk_heads` checks, by `decide` on the
rule list of `simEnv B`, that the heads `NOP`, `UNREACHABLE` and `DROP` occur only in rules 0, 1
and 2. With the reading of conclusions (`conclAlts`), which keeps the outer shape of a conclusion
(`mem_conclAlts_head`), this is the inversion principle `Instr30Inv` uses.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading

/-- The head of the instruction in a conclusion `(C, OP …, it)`. -/
def instrHead : Exp → Option MixopS
  | .tupE [_, .caseE op _, _] => some op
  | _ => none

/-- The head of the instruction a rule types. -/
def ruleHead : Rule → Option MixopS
  | .ruleD _ _ _ e _ => instrHead e

/-- The heads `NOP`, `UNREACHABLE`, `DROP` occur at rules 0, 1, 2 only, and every rule has a
head. -/
def headsOk (rules : List Rule) : Bool :=
  rules.zipIdx.all fun (r, j) =>
    match ruleHead r with
    | some o => (o != "NOP" || j == 0) && (o != "UNREACHABLE" || j == 1) && (o != "DROP" || j == 2)
    | none => false

set_option maxRecDepth 100000 in
/-- **The rule list of `Instr_ok` passes `headsOk`.** -/
theorem instrOk_heads {B : Builtins} : ∃ ps t rules,
    (simEnv B).findRel? "Instr_ok" = some (ps, "%|-%:%", t, rules) ∧ headsOk rules = true :=
  ⟨_, _, _, rfl, by decide⟩

/-- A rule at index `j` of a list passing `headsOk` has a head, and the three heads are at their
indices. -/
theorem head_of_headsOk {rules : List Rule} (h : headsOk rules = true) {j : Nat} {r : Rule}
    (hj : rules[j]? = some r) : ∃ o, ruleHead r = some o ∧ (o = "NOP" → j = 0) ∧
      (o = "UNREACHABLE" → j = 1) ∧ (o = "DROP" → j = 2) := by
  have hm : (r, j) ∈ rules.zipIdx := List.mem_zipIdx_iff_getElem?.2 hj
  have hr := List.all_eq_true.1 h _ hm
  simp only at hr
  cases ho : ruleHead r with
  | none => rw [ho] at hr; exact absurd hr Bool.false_ne_true
  | some o =>
    rw [ho] at hr
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hr
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hr
    exact ⟨o, rfl, fun e => h₁.resolve_left (not_not.2 e), fun e => h₂.resolve_left (not_not.2 e),
      fun e => h₃.resolve_left (not_not.2 e)⟩

/-- **The reading keeps the head**: an alternative of a conclusion `(a, OP b, c)` is again of
that form. -/
theorem mem_conclAlts_head {a b c e' : Exp} {op : MixopS}
    (h : e' ∈ conclAlts (.tupE [a, .caseE op b, c])) :
    ∃ a' b' c', e' = .tupE [a', .caseE op b', c'] := by
  unfold conclAlts at h
  rcases List.mem_cons.1 h with rfl | h
  · exact ⟨a, b, c, rfl⟩
  · split at h
    · simp only [optAlts, optAltsL, prod2, List.mem_map, List.mem_flatMap, List.mem_singleton]
        at h
      obtain ⟨w₂, ⟨a', -, w₁, ⟨x, ⟨b', -, hb⟩, w, ⟨c', -, l, hl, hc⟩, hx⟩, h₂⟩, he⟩ := h
      subst hl hc hb hx h₂ he
      exact ⟨a', b', c', rfl⟩
    · exact absurd h List.not_mem_nil

end Silmaril.Wasm.SpecTec.Institution.Instr30
