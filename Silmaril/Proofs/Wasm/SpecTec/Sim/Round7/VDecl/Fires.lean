module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.Else

/-!
# Round 7, memory SIMD: single rules fire alike at `withVBytes B` and at `B`

`Fires env x i v`, the unit of the per-rule backward lemmas, reads rule `i` of `x` declaratively,
with premise relations read by `DDerives env (otherwise env)` and the rule's own `otherwise`
premise by `otherwise env x [] i v`. For builtins that agree off `$vbytes_`:

* `fires_agree`: a `GoodRule` fires alike, provided its own `otherwise` premise (if it has one)
  moves across (`hels`);
* `fires_pure_iff`: every rule of `Step_pure`;
* `fires_read_iff`: every rule of `Step_read` other than 43. The `otherwise` rules up to 42 read
  only `GoodRule`s; those after 43 (54–102) end their left-hand sides in an instruction other
  than `VLOAD` (`read_elseAltsOk`), so rule 43 does not fire on their left-hand sides
  (`otherwiseAt_read`);
* `fires_step_iff`: every rule of `Step` other than 1–5 and 23 (`Step` has no `otherwise`, at any
  depth: `step_elseDeep`).

At round 7's pair `withVBytes B` and `B`: `fires_pure_withVBytes_iff`, `fires_read_withVBytes_iff`
and `fires_step_withVBytes_iff`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evRule stepReach)
open Round7.VAgree (GoodEvs GoodRel GoodRule AgreeOff agreeOff_symm agreeOff_withVBytes
  findRel?_simEnv)

variable {B₁ B₂ : Builtins}

/-- The hypothesis of `fires_agree`: where rule `i` of `x` has an `otherwise` premise and its
conclusion evaluates to `v`, the `otherwise` reading moves from `B₁` to `B₂`. -/
def ElseMoves (B₁ B₂ : Builtins) (x : IL.Id) (i : Nat) (v : Value) : Prop :=
  ∀ nm qs op e prems t rules,
    (simEnv B₁).findRel? x = some ([], "%~>%", t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    (∃ ρ, EvalExp (simEnv B₁) ρ e v) → prems.all elseFree = false →
    otherwise (simEnv B₁) x [] i v → otherwise (simEnv B₂) x [] i v

/-- **A `GoodRule` of a relation `Step` reaches fires alike**, when its `otherwise` premise moves
across. -/
theorem fires_agree (hB : AgreeOff B₁ B₂) {x : IL.Id} {i : Nat} {v : Value}
    (hx : (0, x) ∈ stepReach) (hg : GoodRule x i) (hels : ElseMoves B₁ B₂ x i v)
    (h : Fires (simEnv B₁) x i v) : Fires (simEnv B₂) x i v := by
  obtain ⟨t, rules, r, hrel, hr, hb⟩ := h
  have hRF : ruleFactsB r = true := (relFacts_of_find hrel hx).2 r (List.mem_of_getElem? hr)
  have hG : GoodEvs (evRule r) := hg B₁ _ r hrel hr
  obtain ⟨nm, qs, op, e, prems⟩ := r
  have hE : ∃ ρ, EvalExp (simEnv B₁) ρ e v := by
    obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
    exact ⟨_, he⟩
  refine ⟨t, rules, _, (findRel?_simEnv B₂ B₁ x).trans hrel, hr, ?_⟩
  exact ruleBody_agree hB (fun _ _ _ _ hy _ hd => dderives_otherwise hB hy hd) (quant_rg hRF)
    (alt_rg hRF e List.mem_cons_self) (goodEvs_prems_of_rule hG)
    (fun hf => hels nm qs op e prems t rules hrel hr hE hf) hb

/-! ## `otherwise` at any depth -/

/-- A rule with an `otherwise` premise is listed by `elseFreeIdx`. -/
theorem mem_elseFreeIdx {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param}
    {op : MixopS} {e : Exp} {prems : List Prem} (hr : rules[i]? = some (.ruleD nm qs op e prems))
    (hf : prems.all elseFree = false) : i ∈ elseFreeIdx rules := by
  have hlt : i < rules.length := (List.getElem?_eq_some_iff.mp hr).1
  simp only [elseFreeIdx, List.mem_filter, List.mem_range, hr, hf, Bool.not_false, and_self, hlt]

/-! ## The three relations -/

theorem pure_goodRel : GoodRel "Step_pure" :=
  ⟨VAgree.pure_mem_stepReach, by decide, by decide⟩

/-- **Every rule of `Step_pure` fires alike.** -/
theorem fires_pure (hB : AgreeOff B₁ B₂) (i : Nat) (v : Value)
    (h : Fires (simEnv B₁) "Step_pure" i v) : Fires (simEnv B₂) "Step_pure" i v :=
  fires_agree hB pure_goodRel.1 (VAgree.goodRule_pure i)
    (fun _ _ _ _ _ _ _ _ _ _ _ => otherwiseAt_goodRel hB pure_goodRel [] i v) h

/-- **Every rule of `Step` other than 1–5 and 23 fires alike.** -/
theorem fires_step (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ∉ [1, 2, 3, 4, 5, 23]) (v : Value)
    (h : Fires (simEnv B₁) "Step" i v) : Fires (simEnv B₂) "Step" i v := by
  refine fires_agree hB Round7.Script.step_mem_stepReach (VAgree.goodRule_step hi) ?_ h
  intro nm qs op e prems t rules hrel hr _ hf
  have hmem : i ∈ elseFreeIdx rules := mem_elseFreeIdx hr hf
  have hnil : elseFreeIdx rules = [] := by
    have h₁ := onRel_of_find elseFreeIdx hrel
    rw [step_elseDeep] at h₁
    exact (Option.some.inj h₁).symm
  rw [hnil] at hmem
  exact absurd hmem List.not_mem_nil

/-- After 43, a rule of `Step_read` with an `otherwise` premise has an atom other than `VLOAD`. -/
theorem read_else_atom {B : Builtins} {t : Typ} {rules : List Rule} {i : Nat} {r : Rule}
    (hrel : (simEnv B).findRel? "Step_read" = some ([], "%~>%", t, rules))
    (hr : rules[i]? = some r) (hmem : i ∈ elseFreeIdx rules) (hi : 43 < i) :
    ∃ b, VElse.ruleAtom r = some b ∧ b ≠ "VLOAD" := by
  have h₁ := onRel_of_find elseAltsOk hrel
  rw [read_elseAltsOk] at h₁
  have hok : elseAltsOk rules = true := (Option.some.inj h₁).symm
  simp only [elseAltsOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hj := hok.2 i hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, hr] at hj
  rcases hj with hj | hj
  · omega
  · split at hj
    · rename_i b hb
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
      exact ⟨b, hb, hj.1⟩
    · cases hj

/-- **Every rule of `Step_read` other than 43 fires alike.** -/
theorem fires_read (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ≠ 43) (v : Value)
    (h : Fires (simEnv B₁) "Step_read" i v) : Fires (simEnv B₂) "Step_read" i v := by
  refine fires_agree hB read_mem_stepReach (VAgree.goodRule_read hi) ?_ h
  intro nm qs op e prems t rules hrel hr hE hf
  refine otherwiseAt_read hB [] ?_
  by_cases hle : i ≤ 43
  · exact .inl hle
  · obtain ⟨b, hb, hne⟩ := read_else_atom hrel hr (mem_elseFreeIdx hr hf) (by omega)
    obtain ⟨ρ, he⟩ := hE
    exact .inr (by rw [lhsAtom_of_eval hb he]; exact fun h => hne (Option.some.inj h))

/-! ## Both directions, at `withVBytes B` -/

theorem fires_pure_iff (hB : AgreeOff B₁ B₂) (i : Nat) (v : Value) :
    Fires (simEnv B₁) "Step_pure" i v ↔ Fires (simEnv B₂) "Step_pure" i v :=
  ⟨fires_pure hB i v, fires_pure (agreeOff_symm hB) i v⟩

theorem fires_read_iff (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ≠ 43) (v : Value) :
    Fires (simEnv B₁) "Step_read" i v ↔ Fires (simEnv B₂) "Step_read" i v :=
  ⟨fires_read hB hi v, fires_read (agreeOff_symm hB) hi v⟩

theorem fires_step_iff (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ∉ [1, 2, 3, 4, 5, 23]) (v : Value) :
    Fires (simEnv B₁) "Step" i v ↔ Fires (simEnv B₂) "Step" i v :=
  ⟨fires_step hB hi v, fires_step (agreeOff_symm hB) hi v⟩

/-- **Every rule of `Step_pure` fires alike at `withVBytes B` and at `B`.** -/
theorem fires_pure_withVBytes_iff (B : Builtins) (i : Nat) (v : Value) :
    Fires (simEnv (MemSimd.withVBytes B)) "Step_pure" i v ↔ Fires (simEnv B) "Step_pure" i v :=
  fires_pure_iff (agreeOff_withVBytes B) i v

/-- **Every rule of `Step_read` other than 43 fires alike at `withVBytes B` and at `B`.** -/
theorem fires_read_withVBytes_iff (B : Builtins) {i : Nat} (hi : i ≠ 43) (v : Value) :
    Fires (simEnv (MemSimd.withVBytes B)) "Step_read" i v ↔ Fires (simEnv B) "Step_read" i v :=
  fires_read_iff (agreeOff_withVBytes B) hi v

/-- **Every rule of `Step` other than 1–5 and 23 fires alike at `withVBytes B` and at `B`.** -/
theorem fires_step_withVBytes_iff (B : Builtins) {i : Nat} (hi : i ∉ [1, 2, 3, 4, 5, 23])
    (v : Value) :
    Fires (simEnv (MemSimd.withVBytes B)) "Step" i v ↔ Fires (simEnv B) "Step" i v :=
  fires_step_iff (agreeOff_withVBytes B) hi v

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
