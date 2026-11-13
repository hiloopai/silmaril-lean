module

public import Silmaril.Wasm.SpecTec.Institution.Wasm20.Thms
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The store-changing `Step` rules at wasm-2.0, by inversion

The wasm-2.0 script has no `Step/ctxt-instrs` rule: its `Step` has `pure` (0), `read` (1),
`ctxt-label` (2), `ctxt-frame` (3) and then the head rules (4–21). So inverting a `Step` fact
needs no argument about infixes, and no length: if no `Step_pure` and no `Step_read` rule names
only constructors of the code, and the code has no label or frame, the fact is a head rule from
rule 4 on, fired at the whole code. This holds at every `simEnv20 B`, so at every model
`Wasm20.stepModel20 B` (whose `Step` facts are the declarative ones, `Whole.sstepB20_iff`).

* `sstep20_head`: the inversion, from the tag tables `pureTags20`, `readTags20` (`checkAvoid`).
* `stepCombos20_ok`: the check at the ten instructions of the store-changing head rules of
  fixed arity (`local.set`, `global.set`, `table.set`, `table.grow`, `elem.drop`, the stores,
  `memory.grow`, `data.drop`), after any value prefix (kernel `decide`).
* `stepModel20_head`: **at every `stepModel20 B`, a `Step` fact from the image of a V2
  configuration whose code is values and one such instruction is a head rule of `Step` from
  rule 4 on, fired at the whole code.**

Nothing here says such a fact exists: at wasm-2.0 the forward half fails
(`Sim20.Whole.not_wholeStepValid`), and there is no `Wasm20.builtins` analogue of
`stepObs_builtins`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30D

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (SStep SRead SPure dderives_iff_fires Fires cfgV)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn LhsIn ruleTags relRules checkAvoid
  not_ruleBody_of_tags)
open Silmaril.Wasm.SpecTec.Sim20
open Silmaril.Wasm.SpecTec.Sim20.Whole

variable {H : Type}

/-- The `Step` rule `i` of the wasm-2.0 script does not fire at a code avoiding one of its
forced constructors. -/
theorem not_fires_tag20 {B : Builtins} {i : Nat} {ts : List MixopS} (hts : stepTags20[i]? = some ts)
    {op : MixopS} (hop : op ∈ ts) {S : List MixopS} (hS : op ∉ S) {z : Value} {l : List Value}
    (hl : TagsIn S l) {w : Value} : ¬ Fires (simEnv20 B) "Step" i (.tuple [cfgV z l, w]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hT : rules.map ruleTags = stepTags20 := by
    have h := stepTags20_eq
    rw [← relRules_simEnv20 B] at h
    simpa [relRules, hrel] using h
  have htag : ruleTags r = ts := by
    rw [← hT, List.getElem?_map, hr] at hts
    exact Option.some.inj hts
  exact not_ruleBody_of_tags (Or.inr ⟨z, l, rfl, hl⟩) (htag ▸ hop) hS hb

/-- **Inversion at wasm-2.0**: at every `simEnv20 B`, a `Step` fact from `z; l`, with the
constructors of `l` in `S`, is a rule of `Step` from rule 4 on fired at the whole of `z; l`,
when every rule of `Step_pure` and `Step_read` names a constructor outside `S`, and `S` has no
label or frame. -/
theorem sstep20_head (B : Builtins) {S : List MixopS} {z : Value} {l : List Value}
    (hl : TagsIn S l) (hp : checkAvoid pureTags20 pureTags20.length [] S = true)
    (hr : checkAvoid readTags20 readTags20.length [] S = true)
    (hlab : "LABEL_%{%}%" ∉ S) (hfr : "FRAME_%{%}%" ∉ S) {w : Value}
    (hs : SStep (simEnv20 B) (cfgV z l) w) :
    ∃ i, 4 ≤ i ∧ Fires (simEnv20 B) "Step" i (.tuple [cfgV z l, w]) := by
  have hstep : ∃ t rules, (simEnv20 B).findRel? "Step" = some ([], "%~>%", t, rules) :=
    ⟨_, _, rfl⟩
  obtain ⟨t, rules, hrel⟩ := hstep
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  have hpT : (relRules (simEnv20 B) "Step_pure").map ruleTags = pureTags20 := by
    rw [relRules_simEnv20]; exact pureTags20_eq
  have hrT : (relRules (simEnv20 B) "Step_read").map ruleTags = readTags20 := by
    rw [relRules_simEnv20]; exact readTags20_eq
  match i, hf with
  | 0, hf =>
    obtain ⟨z₁, is, js, h₁, -, -, -, hq⟩ := inv_pure20 (hasRuleAt_stepPure B) hf
    have el : l = is := (Sim.Bwd.cfgV_inj h₁).2
    exact absurd hq (not_dderives_of_table (x := "Step_pure") rfl hpT
      (.inl ⟨is, rfl, el ▸ hl⟩) hp (fun _ h => absurd h List.not_mem_nil))
  | 1, hf =>
    obtain ⟨z₁, is, js, h₁, -, -, -, hq⟩ := inv_read20 (hasRuleAt_stepRead B) hf
    have el : l = is := (Sim.Bwd.cfgV_inj h₁).2
    exact absurd hq (not_dderives_of_table (x := "Step_read") rfl hrT
      (.inr ⟨z₁, is, rfl, el ▸ hl⟩) hr (fun _ h => absurd h List.not_mem_nil))
  | 2, hf => exact absurd hf (not_fires_tag20 rfl (List.mem_singleton_self _) hlab hl)
  | 3, hf => exact absurd hf (not_fires_tag20 rfl (List.mem_singleton_self _) hfr hl)
  | k + 4, hf => exact ⟨k + 4, by omega, hf⟩

/-- The constructors of the store-changing head rules of `Step` of fixed arity at wasm-2.0. -/
def stepCombos20 : List MixopS :=
  ["LOCAL.SET", "GLOBAL.SET", "TABLE.SET", "TABLE.GROW", "ELEM.DROP", "STORE", "VSTORE",
   "VSTORE_LANE", "MEMORY.GROW", "DATA.DROP"]

/-- **The check at every instruction of `stepCombos20`**, after any value prefix. -/
theorem stepCombos20_ok : ∀ t ∈ stepCombos20,
    (checkAvoid pureTags20 pureTags20.length [] (t :: Pure.valHeads20) &&
      checkAvoid readTags20 readTags20.length [] (t :: Pure.valHeads20)) = true := by
  decide +kernel

/-- **The store-changing `Step` rules at every `stepModel20 B`**: a `Step` fact from the image
of a V2 configuration whose instructions are values and instructions named `t`, for `t` a
store-changing instruction of fixed arity, is a head rule of `Step` from rule 4 on, fired at the
whole code. -/
theorem stepModel20_head (B : Builtins) (hn : H → String) {c : Config H} {t : MixopS}
    (ht : t ∈ stepCombos20) (hh : ∀ a ∈ c.code, adminHead20 a ∈ t :: Pure.valHeads20) {w : Value}
    (hs : (Wasm20.stepModel20 B).D "Step" "%~>%" [] (.tuple [configV hn c, w])) :
    ∃ i, 4 ≤ i ∧ Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) := by
  have hok := stepCombos20_ok t ht
  simp only [Bool.and_eq_true] at hok
  have hs' : SStep (simEnv20 B) (configV hn c) w :=
    (sstepB20_iff B).1 ((Wasm20.mem_stepModel20_iff B _ _).1 hs)
  have hl : TagsIn (t :: Pure.valHeads20) (adminsToV c.code) := fun x hx op u hxe => by
    have hm : op ∈ c.code.map adminHead20 := tagsIn_heads c.code x hx op u hxe
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
    exact hh a ha
  have hst : ("LABEL_%{%}%" ∉ t :: Pure.valHeads20) ∧ ("FRAME_%{%}%" ∉ t :: Pure.valHeads20) := by
    simp only [stepCombos20, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact sstep20_head B hl hok.1 hok.2 hst.1 hst.2 hs'

end Silmaril.Wasm.SpecTec.Institution.FwdB30D
