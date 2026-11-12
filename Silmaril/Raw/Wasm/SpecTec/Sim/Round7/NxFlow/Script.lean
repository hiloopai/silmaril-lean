module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Clause3
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxAssemble
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Thms

/-!
# Round 7, REH route 2: the static facts hold in the round-7 environment (unrefined)

`envFacts_utf8Env`: in `utf8Env B`, every definition with a parameter entry in `tsigFixed` is
`$utf8` without clauses or a definition of the fixed script that passes the flow check
(`NxTyped.flowItems_fixed`) and the side conditions (`auxItems_fixed`); and no type is named
`X`. With `sigsAux_fixed`, `flowSound'` proves `NxSound.Task.flowSound`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

theorem sum_zero : ∀ l : List Nat, l.sum = 0 → ∀ x ∈ l, x = 0
  | [], _, x, hx => by simp at hx
  | a :: l, h, x, hx => by
    simp only [List.sum_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · exact sum_zero l (by omega) x hx

theorem defFacts_of_decD {f : String} {ps : List Param} {t : Typ} {cls : List Clause}
    (hfl : flowItem sigX tsigFixed (.decD f ps t cls) = 0)
    (hax : auxItem tsigFixed (.decD f ps t cls) = true) (hr : reach 1 f = true) :
    DefFacts f ps t cls := by
  simp only [flowItem, hr, ite_true, Nat.add_eq_zero_iff] at hfl
  obtain ⟨h₁, h₂⟩ := hfl
  simp only [auxItem, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hax
  obtain ⟨⟨⟨hX, hle⟩, hng⟩, hcl⟩ := hax
  refine ⟨?_, ?_, ?_, ?_, hcl⟩
  · by_contra hc
    simp_all
  · match hp : typParams ps, hle with
    | [], _ => exact .inl rfl
    | [x], _ =>
      have := hX x (by rw [hp]; exact List.mem_singleton_self _)
      simp only [beq_iff_eq] at this
      subst this
      exact .inr rfl
    | _ :: _ :: _, hl => simp at hl
  · intro p hp
    have := hng p hp
    cases p <;> simp_all
  · intro b hb c hc
    have hm := sum_zero _ h₂ _ (List.mem_map.2 ⟨b, hb, rfl⟩)
    exact sum_zero _ hm _ (List.mem_map.2 ⟨c, hc, rfl⟩)

mutual
theorem defFacts_def : ∀ d : Def, flowItem sigX tsigFixed d = 0 → auxItem tsigFixed d = true →
    ∀ p ∈ defsOfDef d, reach 1 p.1 = true → DefFacts p.1 p.2.1 p.2.2.1 p.2.2.2
  | .decD f ps t cls, hfl, hax, p, hp, hr => by
    simp only [defsOfDef, Map.bind, Map.empty] at hp
    split at hp
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact defFacts_of_decD hfl hax hr
  | .recD ds, hfl, hax, p, hp, hr => by
    simp only [flowItem] at hfl
    simp only [auxItem] at hax
    simp only [defsOfDef] at hp
    exact defFacts_defs ds hfl hax p hp hr
  | .typD _ _ _, _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp
  | .relD _ _ _ _ _, _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp
  | .gramD _ _ _ _, _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp

theorem defFacts_defs : ∀ ds : List Def, flowItems sigX tsigFixed ds = 0 →
    auxItems tsigFixed ds = true →
    ∀ p ∈ defsOfDefs ds, reach 1 p.1 = true → DefFacts p.1 p.2.1 p.2.2.1 p.2.2.2
  | [], _, _, p, hp, _ => by simp [defsOfDefs, Map.empty] at hp
  | d :: ds, hfl, hax, p, hp, hr => by
    simp only [flowItems, Nat.add_eq_zero_iff] at hfl
    simp only [auxItems, Bool.and_eq_true] at hax
    simp only [defsOfDefs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact defFacts_defs ds hfl.2 hax.2 p hp hr
    · exact defFacts_def d hfl.1 hax.1 p hp hr
end

mutual
theorem typs_def : ∀ d : Def, auxItem tsigFixed d = true → ∀ p ∈ typsOfDef d, p.1 ≠ "X"
  | .typD x _ _, hax, p, hp => by
    simp only [auxItem, bne_iff_ne, ne_eq] at hax
    simp only [typsOfDef, Map.bind, Map.empty] at hp
    split at hp
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact hax
  | .recD ds, hax, p, hp => by
    simp only [auxItem] at hax
    simp only [typsOfDef] at hp
    exact typs_defs ds hax p hp
  | .decD _ _ _ _, _, p, hp => by simp [typsOfDef, Map.empty] at hp
  | .relD _ _ _ _ _, _, p, hp => by simp [typsOfDef, Map.empty] at hp
  | .gramD _ _ _ _, _, p, hp => by simp [typsOfDef, Map.empty] at hp

theorem typs_defs : ∀ ds : List Def, auxItems tsigFixed ds = true →
    ∀ p ∈ typsOfDefs ds, p.1 ≠ "X"
  | [], _, p, hp => by simp [typsOfDefs, Map.empty] at hp
  | d :: ds, hax, p, hp => by
    simp only [auxItems, Bool.and_eq_true] at hax
    simp only [typsOfDefs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact typs_defs ds hax.2 p hp
    · exact typs_def d hax.1 p hp
end

theorem find?_mem {α : Type} : ∀ {m : Map α} {x : IL.Id} {v : α}, m.find? x = some v → (x, v) ∈ m
  | [], _, _, h => by simp [Map.find?] at h
  | (y, u) :: m, x, v, h => by
    simp only [Map.find?] at h
    split at h
    · cases h; rename_i hy; subst hy; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (find?_mem h)

theorem find?_none_of {α : Type} : ∀ {m : Map α} {x : IL.Id}, (∀ p ∈ m, p.1 ≠ x) →
    m.find? x = none
  | [], _, _ => rfl
  | (y, u) :: m, x, h => by
    simp only [Map.find?]
    have hy : y ≠ x := h (y, u) (List.mem_cons_self ..)
    simp only [hy, ite_false]
    exact find?_none_of fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem memTyp_utf8Env_X (B : Builtins) : (utf8Env B).memTyp "X" = false := by
  have h : (simEnv B).findTyp? "X" = none := by
    simp only [simEnv, baseEnv, Env.findTyp?, Env.withBuiltins, envOfScript, envOfDefs_eq]
    refine find?_none_of fun p hp => ?_
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact typs_defs fixed auxItems_fixed p hp
    · simp [Env.empty, Map.empty] at hp
  simp only [Env.memTyp, Map.mem]
  have := findTyp?_utf8Env B "X"
  simp only [Env.findTyp?] at this h
  rw [this, h]
  rfl

theorem mem_defs_of_findDef' {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (simEnv B).findDef? x = some v) : (x, v) ∈ defsOfDefs fixed := by
  unfold simEnv baseEnv at h
  rw [Env.findDef?_withBuiltins, envOfScript, envOfDefs_eq] at h
  have hm := find?_mem h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

/-- **The static facts hold in the round-7 environment.** -/
theorem envFacts_utf8Env (B : Builtins) : EnvFacts (utf8Env B) where
  memX := memTyp_utf8Env_X B
  defs := by
    intro f d hd hp
    by_cases hu : f = "utf8"
    · subst hu
      rw [findDef?_utf8Env] at hd
      cases hd
      exact .inl rfl
    · rw [findDef?_utf8Env_of_ne B hu] at hd
      refine .inr ?_
      have hm := mem_defs_of_findDef' hd
      have hr : reach 1 f = true := by
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hp
        have := (List.all_eq_true.1 (sigFacts sigsAux_fixed).params) _ (mem_of_lookup hc)
        simp only [Bool.and_eq_true] at this
        exact this.1
      exact defFacts_defs fixed flowItems_fixed auxItems_fixed _ hm hr

/-- **The flow check is sound**: `NxSound.Task.flowSound`. -/
theorem flowSound' : Task.flowSound := by
  intro B hB n
  exact defsVT_all (sigFacts sigsAux_fixed) (envFacts_utf8Env B) hB n

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
