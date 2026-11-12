module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLoadVal
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRestQ

/-!
# The unrestricted `memory.size` field is false (round 4)

Pass 2's `FwdRestQ10` asked, as its `memorySize` field, that V1's `memory.size` be matched by the
1.0 script at **every** memory. Round 3 proved it under `MemAligned10` (page-aligned, fewer than
`2^32` pages) and said the unrestricted field was expected to be false. This module proves that.

* **The rule tables of 1.0** (`pureTags10`, `readTags10`, `stepTags10`): the constructors forced
  by the left-hand side of each of the 29 `Step_pure`, 13 `Step_read` and 13 `Step` rules, checked
  against the script by kernel `rfl`. `Step/pure`, `Step/read` and `Step/ctxt-instrs` force none.
* **`z; ε` is stuck** (`not_sstep10_nil`): every rule but `Step/ctxt-instrs` forces a
  constructor, and `ctxt-instrs` needs a non-empty `val*` or tail.
* **`z; MEMORY.SIZE` is stuck at a memory that is not page-aligned**
  (`not_sstep10_memorySize`, `stuck10_memorySize`): `Step/pure`, rules 2–3 and 5–12 force other
  constructors; `Step/ctxt-instrs` would need `z; ε` to step; and `Step/read` can only use
  `Step_read/memory.size` (rule 12), whose premise `n * 64 * $Ki = |$mem(z, 0).BYTES|` has no
  solution. This holds at every builtins.
* **The witness** (`memSizeCfg10`): a store with one memory of one byte. V1 steps `memory.size`
  to `i32.const 0`, both images are IL-typed (kernel evaluation of the type checker), and the
  script has no step at all. So `MemorySizeField10 B hn` (the unrestricted field) is false
  (`not_memorySizeField10`) and so is pass 2's `FwdRestQ10` (`not_fwdRestQ10`), at every builtins.
  Round 3's restatement under `MemAligned10` (`fwdAt10_memorySize`) is the documented fix, and
  `MemsAligned10` holds along every V1 run from an aligned store (`memsAligned10_steps`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep SRead SPure Fires cfgV
  dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (ruleTags relRules LhsIn TagsIn checkAvoid checkAvoid_sound
  not_ruleBody_of_tags)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.Whole (not_dderives_of_table memSize_inv)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## The rule tables of 1.0 -/

/-- The forced constructors of the 29 rules of wasm-1.0 `Step_pure`, in order. -/
def pureTags10 : List (List MixopS) :=
  [["UNREACHABLE"], ["NOP"], ["DROP"], ["CONST", "SELECT"], ["CONST", "SELECT"],
   ["CONST", "IF%%ELSE%"], ["CONST", "IF%%ELSE%"], ["LABEL_%{%}%"], ["LABEL_%{%}%"],
   ["LABEL_%{%}%"], ["CONST", "BR_IF"], ["CONST", "BR_IF"], ["CONST", "BR_TABLE"],
   ["CONST", "BR_TABLE"], ["FRAME_%{%}%"], ["FRAME_%{%}%"], ["LABEL_%{%}%"], ["TRAP"],
   ["LABEL_%{%}%"], ["FRAME_%{%}%"], ["CONST", "UNOP"], ["CONST", "UNOP"],
   ["CONST", "CONST", "BINOP"], ["CONST", "CONST", "BINOP"], ["CONST", "TESTOP"],
   ["CONST", "CONST", "RELOP"], ["CONST", "CVTOP"], ["CONST", "CVTOP"], ["LOCAL.TEE"]]

/-- The forced constructors of the 13 rules of wasm-1.0 `Step_read`, in order. -/
def readTags10 : List (List MixopS) :=
  [["BLOCK"], ["LOOP"], ["CALL"], ["CONST", "CALL_INDIRECT"], ["CONST", "CALL_INDIRECT"],
   ["CALL_ADDR"], ["LOCAL.GET"], ["GLOBAL.GET"], ["CONST", "LOAD"], ["CONST", "LOAD"],
   ["CONST", "LOAD"], ["CONST", "LOAD"], ["MEMORY.SIZE"]]

/-- The forced constructors of the 13 rules of wasm-1.0 `Step`, in order. `Step/pure`,
`Step/read` and `Step/ctxt-instrs` (rules 0, 1 and 4) force none. -/
def stepTags10 : List (List MixopS) :=
  [[], [], ["LABEL_%{%}%"], ["FRAME_%{%}%"], [], ["LOCAL.SET"], ["GLOBAL.SET"],
   ["CONST", "CONST", "STORE"], ["CONST", "CONST", "STORE"], ["CONST", "CONST", "STORE"],
   ["CONST", "CONST", "STORE"], ["CONST", "MEMORY.GROW"], ["CONST", "MEMORY.GROW"]]

/-- `relRules` only looks relations up. -/
theorem relRules_simEnv10 (x : IL.Id) :
    relRules (simEnv10 B) x = relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed) x :=
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `pureTags10` is the tag table of wasm-1.0 `Step_pure`. -/
theorem pureTags10_eq :
    (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed) "Step_pure").map ruleTags =
      pureTags10 := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `readTags10` is the tag table of wasm-1.0 `Step_read`. -/
theorem readTags10_eq :
    (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed) "Step_read").map ruleTags =
      readTags10 := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `stepTags10` is the tag table of wasm-1.0 `Step`. -/
theorem stepTags10_eq :
    (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed) "Step").map ruleTags =
      stepTags10 := by
  rfl

/-- **A `Step` rule outside 0, 1 and 4 does not fire at a left-hand side avoiding its tags.** -/
theorem not_fires_step_tag10 {S : List MixopS} {k : Nat} {a w : Value} (ha : LhsIn S a)
    (hc : checkAvoid stepTags10 stepTags10.length [0, 1, 4] S = true) (hk : k ∉ [0, 1, 4]) :
    ¬ Fires (simEnv10 B) "Step" k (.tuple [a, w]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hT : rules.map ruleTags = stepTags10 := by
    have h₀ := stepTags10_eq
    rw [← relRules_simEnv10 B] at h₀
    simpa [relRules, hrel] using h₀
  have hlt : k < stepTags10.length := by
    rw [← hT, List.length_map]
    exact (List.getElem?_eq_some_iff.1 hr).1
  have htag : stepTags10[k]?.getD [] = ruleTags r := by
    rw [← hT, List.getElem?_map, hr]
    rfl
  obtain ⟨op, hop, hS⟩ := checkAvoid_sound hc hlt hk
  exact not_ruleBody_of_tags ha (htag ▸ hop) hS hb

/-! ## `z; ε` is stuck -/

theorem tagsIn_nil10 (S : List MixopS) : TagsIn S [] := fun _ hx => absurd hx List.not_mem_nil

/-- No `Step_pure` step from the empty sequence. -/
theorem not_spure10_nil (js : List Value) : ¬ SPure (simEnv10 B) [] js := by
  obtain ⟨t, rules, hrel⟩ := findRel_pure10 B
  exact not_dderives_of_table hrel (T := pureTags10)
    (by rw [relRules_simEnv10]; exact pureTags10_eq) (S := []) (exc := [])
    (Or.inl ⟨_, rfl, tagsIn_nil10 _⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)

/-- No `Step_read` step from `z; ε`. -/
theorem not_sread10_nil (z : Value) (js : List Value) : ¬ SRead (simEnv10 B) (cfgV z []) js := by
  obtain ⟨t, rules, hrel⟩ := findRel_read10 B
  exact not_dderives_of_table hrel (T := readTags10)
    (by rw [relRules_simEnv10]; exact readTags10_eq) (S := []) (exc := [])
    (Or.inr ⟨z, _, rfl, tagsIn_nil10 _⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)

/-! ## The structural rules at a short sequence -/

/-- `Step/ctxt-instrs` on a sequence of at most one instruction has an empty middle part. -/
theorem ctxt_mid_nil10 {vs is rest l : List Value} (hl : l.length ≤ 1)
    (hne : vs ≠ [] ∨ rest ≠ []) (e : l = vs ++ is ++ rest) : is = [] := by
  have h₀ : (vs ++ is ++ rest).length ≤ 1 := e ▸ hl
  have h₁ : vs.length + is.length + rest.length ≤ 1 := by
    simpa only [List.length_append] using h₀
  have h₂ : 1 ≤ vs.length + rest.length := by
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; omega
    · have := List.length_pos_iff.2 h; omega
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- `Step/pure` does not fire at `z; l` when `Step_pure` has no step from `l`. -/
theorem not_fires10_pure {z w : Value} {l : List Value} (hp : ∀ js, ¬ SPure (simEnv10 B) l js) :
    ¬ Fires (simEnv10 B) "Step" 0 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, -, -, hs⟩ := inv_pure10 (hasRuleAt_pure10 B) hf
  have e : l = is := (Sim.Bwd.cfgV_inj h₁).2
  exact hp js (e ▸ hs)

/-- `Step/read` does not fire at `c` when `Step_read` has no step from `c`. -/
theorem not_fires10_read {c w : Value} (hr : ∀ js, ¬ SRead (simEnv10 B) c js) :
    ¬ Fires (simEnv10 B) "Step" 1 (.tuple [c, w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, -, -, hs⟩ := inv_read10 (hasRuleAt_read10 B) hf
  exact hr js (h₁ ▸ hs)

/-- `Step/ctxt-instrs` does not fire at `z; ε`. -/
theorem not_fires10_ctxtInstrs_nil {z w : Value} :
    ¬ Fires (simEnv10 B) "Step" 4 (.tuple [cfgV z [], w]) := by
  intro hf
  obtain ⟨z₁, z', vs, is, is', rest, -, hne, h₁, -, -⟩ :=
    inv_ctxtInstrs10 (hasRuleAt_ctxtInstrs10 B) hf
  have e : vs ++ is ++ rest = [] := ((Sim.Bwd.cfgV_inj h₁).2).symm
  have ev : vs = [] ∧ rest = [] := ⟨by simp_all, by simp_all⟩
  rcases hne with h | h
  · exact h ev.1
  · exact h ev.2

/-- `Step/ctxt-instrs` does not fire at `z; l`, for `l` of length at most one, when `z'; ε` is
stuck for every `z'`. -/
theorem not_fires10_ctxtInstrs {z w : Value} {l : List Value} (hl : l.length ≤ 1)
    (hnil : ∀ z' w', ¬ SStep (simEnv10 B) (cfgV z' []) w') :
    ¬ Fires (simEnv10 B) "Step" 4 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z₁, z', vs, is, is', rest, -, hne, h₁, -, hs⟩ :=
    inv_ctxtInstrs10 (hasRuleAt_ctxtInstrs10 B) hf
  have his : is = [] := ctxt_mid_nil10 hl hne (Sim.Bwd.cfgV_inj h₁).2
  exact hnil z₁ _ (his ▸ hs)

/-- **No `Step` from `z; l`** when the three structural rules 0, 1 and 4 do not fire and `l`'s
constructors avoid the tags of the other rules. -/
theorem not_sstep10_of {z w : Value} {l : List Value} {S : List MixopS} (hS : TagsIn S l)
    (hc : checkAvoid stepTags10 stepTags10.length [0, 1, 4] S = true)
    (h₀ : ¬ Fires (simEnv10 B) "Step" 0 (.tuple [cfgV z l, w]))
    (h₁ : ¬ Fires (simEnv10 B) "Step" 1 (.tuple [cfgV z l, w]))
    (h₄ : ¬ Fires (simEnv10 B) "Step" 4 (.tuple [cfgV z l, w])) :
    ¬ SStep (simEnv10 B) (cfgV z l) w := by
  intro hs
  obtain ⟨t, rules, hrel⟩ := findRel_step10 B
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  by_cases hi : i ∈ [0, 1, 4]
  · have hi' : i = 0 ∨ i = 1 ∨ i = 4 := by simpa only [List.mem_cons, List.not_mem_nil,
      or_false] using hi
    rcases hi' with rfl | rfl | rfl
    · exact h₀ hf
    · exact h₁ hf
    · exact h₄ hf
  · exact not_fires_step_tag10 B (Or.inr ⟨z, _, rfl, hS⟩) hc hi hf

/-- **`z; ε` is stuck in the wasm-1.0 script.** -/
theorem not_sstep10_nil (z w : Value) : ¬ SStep (simEnv10 B) (cfgV z []) w :=
  not_sstep10_of B (S := []) (tagsIn_nil10 _) (by decide) (not_fires10_pure B (not_spure10_nil B))
    (not_fires10_read B (not_sread10_nil B z)) (not_fires10_ctxtInstrs_nil B)
/-! ## `z; MEMORY.SIZE` is stuck at a memory that is not page-aligned -/

/-- The image of `memory.size`. -/
abbrev memSizeV10 : Value := caseNilV "MEMORY.SIZE"

theorem tagsIn_memSize10 : TagsIn ["MEMORY.SIZE"] [memSizeV10] := by
  intro x hx op w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  simp only [memSizeV10, caseNilV, Value.case.injEq] at hxw
  simp [← hxw.1]

/-- No `Step_pure` step from `MEMORY.SIZE`. -/
theorem not_spure10_memSize (js : List Value) : ¬ SPure (simEnv10 B) [memSizeV10] js := by
  obtain ⟨t, rules, hrel⟩ := findRel_pure10 B
  exact not_dderives_of_table hrel (T := pureTags10)
    (by rw [relRules_simEnv10]; exact pureTags10_eq) (S := ["MEMORY.SIZE"]) (exc := [])
    (Or.inl ⟨_, rfl, tagsIn_memSize10⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)

/-- `Step_read/memory.size` does not fire at a memory whose size is not a whole number of
pages. -/
theorem not_fires10_memorySize {H : Type} {hn : H → String} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (hm : frameMemory s f = some (a, m))
    (hal : m.data.size % Execution.Memory.pageSize ≠ 0) (w : Value) :
    ¬ Fires (simEnv10 B) "Step_read" 12 (.tuple [configV hn ⟨s, f, [.source .memorySize]⟩, w]) := by
  intro hf
  obtain ⟨σ, -, fz, -, -, hp⟩ := firesCfg10_inv (hasRuleAt10_memorySize B) hf
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ :=
    evalExp_cmpE_iff.1 (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  have ev : v₁ = .num (.natN m.data.size) :=
    (cmpValues_eq_true_iff.1 hcmp).trans (EvalExp.unique e₂ (evalExp_memLen10 rfl fz hm))
  obtain ⟨k, -, hk⟩ := memSize_inv (evalExp_ki10 rfl) (ev ▸ e₁)
  apply hal
  simp only [Execution.Memory.pageSize, ← hk]
  omega

/-- No `Step_read` step from `z; MEMORY.SIZE` at a memory that is not page-aligned. -/
theorem not_sread10_memSize {H : Type} {hn : H → String} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (hm : frameMemory s f = some (a, m))
    (hal : m.data.size % Execution.Memory.pageSize ≠ 0) (js : List Value) :
    ¬ SRead (simEnv10 B) (configV hn ⟨s, f, [.source .memorySize]⟩) js := by
  obtain ⟨t, rules, hrel⟩ := findRel_read10 B
  refine not_dderives_of_table hrel (T := readTags10)
    (by rw [relRules_simEnv10]; exact readTags10_eq) (S := ["MEMORY.SIZE"]) (exc := [12])
    (Or.inr ⟨stateV hn s f, _, rfl, tagsIn_memSize10⟩) (by decide) ?_
  intro i hi r hr hb
  obtain rfl : i = 12 := List.mem_singleton.1 hi
  exact not_fires10_memorySize B hm hal _ ⟨t, rules, r, hrel, hr, hb⟩

/-- **`z; MEMORY.SIZE` is stuck in the wasm-1.0 script** at a memory whose size is not a whole
number of pages, at every builtins. -/
theorem not_sstep10_memorySize {H : Type} {hn : H → String} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (hm : frameMemory s f = some (a, m))
    (hal : m.data.size % Execution.Memory.pageSize ≠ 0) (w : Value) :
    ¬ SStep (simEnv10 B) (configV hn ⟨s, f, [.source .memorySize]⟩) w :=
  not_sstep10_of B (z := stateV hn s f) (l := [memSizeV10]) tagsIn_memSize10 (by decide)
    (not_fires10_pure B (not_spure10_memSize B)) (not_fires10_read B (not_sread10_memSize B hm hal))
    (not_fires10_ctxtInstrs B (by decide) (not_sstep10_nil B))
/-- **`z; MEMORY.SIZE` is stuck under the backend reading** at a memory that is not page-aligned. -/
theorem stuck10_memorySize {H : Type} {hn : H → String} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (hm : frameMemory s f = some (a, m))
    (hal : m.data.size % Execution.Memory.pageSize ≠ 0) (w : Value) :
    ¬ SStepB (simEnv10 B) (configV hn ⟨s, f, [.source .memorySize]⟩) w :=
  fun h => not_sstep10_memorySize B hm hal w ((sstepB10_iff B).1 h)

/-! ## The witness -/

/-- A store with one memory of one byte, and nothing else. -/
def memSizeStore10 (H : Type) : Store H :=
  { memories := [⟨ByteArray.mk #[0], none⟩] }

/-- A frame whose module's memory 0 is that memory. -/
def memSizeFrame10 : Frame := { module := { memories := [⟨0⟩] } }

/-- `memory.size` at the one-byte memory. -/
def memSizeCfg10 (H : Type) : Config H := ⟨memSizeStore10 H, memSizeFrame10, [.source .memorySize]⟩

/-- What V1 answers there: `i32.const 0`. -/
def memSizeCfg10' (H : Type) : Config H :=
  ⟨memSizeStore10 H, memSizeFrame10, [value (.int .i32 (BitVec.ofNat 32 0))]⟩

theorem frameMemory_memSize10 (H : Type) :
    frameMemory (memSizeStore10 H) memSizeFrame10 = some (⟨0⟩, ⟨ByteArray.mk #[0], none⟩) := rfl

/-- **V1 steps `memory.size` to `i32.const 0`** at the one-byte memory. -/
theorem step_memSize10 {H : Type} (host : HostSemantics H) :
    Step host (memSizeCfg10 H) (memSizeCfg10' H) :=
  .memorySize _ _ _ _ (frameMemory_memSize10 H)

set_option maxHeartbeats 4000000 in
/-- The image of `memSizeCfg10` is IL-typed. -/
theorem typed10_memSize {H : Type} (hn : H → String) :
    Typed10 (simEnv10 B) hn (memSizeCfg10 H) :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
/-- The image of `memSizeCfg10'` is IL-typed. -/
theorem typed10_memSize' {H : Type} (hn : H → String) :
    Typed10 (simEnv10 B) hn (memSizeCfg10' H) :=
  ⟨100, by with_unfolding_all rfl⟩

/-- **The unrestricted `memory.size` field** of pass 2's `FwdRestQ10`. -/
def MemorySizeField10 {H : Type} (B : Builtins) (hn : H → String) : Prop :=
  ∀ (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst), frameMemory s f = some (a, m) →
    FwdAt10 B hn ⟨s, f, [.source .memorySize]⟩
      ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩

/-- **The unrestricted `memory.size` field is false**, at every builtins: at a one-byte memory V1
answers `0`, both images are typed, and the 1.0 script is stuck. -/
theorem not_memorySizeField10 {H : Type} (hn : H → String) : ¬ MemorySizeField10 B hn := by
  intro F
  have hc := typed10_memSize B hn (H := H)
  have hc' := typed10_memSize' B hn (H := H)
  have h := F (memSizeStore10 H) memSizeFrame10 ⟨0⟩ ⟨ByteArray.mk #[0], none⟩
    (frameMemory_memSize10 H) (typedV_state_of_typed10 hc) (typedV_state_of_typed10 hc')
    (typedV_code_of_typed10 hc) (typedV_code_of_typed10 hc')
  exact stuck10_memorySize B (frameMemory_memSize10 H) (by decide) _ h

/-- **Pass 2's `FwdRestQ10` cannot hold**, at any builtins: its `memorySize` field is false. -/
theorem not_fwdRestQ10 {H : Type} (hn : H → String) (host : HostSemantics H) :
    ¬ FwdRestQ10 B hn host :=
  fun R => not_memorySizeField10 B hn R.memorySize

end Silmaril.Wasm.SpecTec.Sim10.Whole
