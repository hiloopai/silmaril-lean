module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.StepQC

/-!
# Round 7, moving derivations across erasure: a typed state is a real state (unrefined)

`state_inv`: in `utf8Env B`, a value typed `state` (in a scope without type variables) is
`stV S F` with a store `S` that has no record field `EXPORTS`. The type `state` has the one case
`%;%` over `store` and `frame`, and `store` is a record type none of whose fields is `EXPORTS`;
record typing is positional (`hasTypFields`), so a typed store has exactly the store's fields.

This is the hypothesis of round 3's `Round7.EraseAll.callDef_withTableinst_state` and
`callDef_withMeminst_state` at the grow rules of `Step`, whose first argument is the quantifier
`z : state`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

/-- The type definition `state`: one case `%;%` over `store` and `frame`. -/
def stateTD : TypDef :=
  ([], [.instD [] [] (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []),
    .mk "frame" (.varT "frame" [])]) [] []])])

/-- The fields of a record type definition with one instance and no parameters. -/
def fieldsOf : Option TypDef → List TypField
  | some ([], [.instD [] [] (.structT fs)]) => fs
  | _ => []

/-- No field is `EXPORTS`. -/
def noExpFields (fs : List TypField) : Bool :=
  fs.all fun f => match f with | .mk a _ _ _ => a != "EXPORTS"

set_option maxRecDepth 100000 in
theorem findTyp_state_u (B : Builtins) : (utf8Env B).findTyp? "state" = some stateTD := by
  rw [findTyp?_utf8Env]; rfl

set_option maxRecDepth 100000 in
theorem findTyp_store_u (B : Builtins) :
    (utf8Env B).findTyp? "store" =
      some ([], [.instD [] [] (.structT (fieldsOf ((utf8Env B).findTyp? "store")))]) := by
  rw [findTyp?_utf8Env]; rfl

set_option maxRecDepth 100000 in
theorem store_noExp (B : Builtins) : noExpFields (fieldsOf ((utf8Env B).findTyp? "store")) = true := by
  rw [findTyp?_utf8Env]; rfl

theorem localTyp_none {ρ : VarEnv} (hρ : ρ.typs = []) (x : IL.Id) : localTyp? ρ x [] = none := by
  simp [localTyp?, VarEnv.findTyp?, hρ]

theorem matchArgs_nil_nil {env : Env} {ρ σ : VarEnv} (h : MatchArgs env ρ [] [] σ) : σ = ρ := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [matchArgs] at hn
  | succ n => simp only [matchArgs] at hn; exact (Except.ok.inj hn).symm

theorem not_hasTypInsts_nil {env : Env} {ws : List ArgV} {v : Value} :
    ¬ HasTypInsts env [] ws v := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => rw [hasTypInsts_zero] at hn; simp at hn
  | succ n => rw [hasTypInsts_succ_nil] at hn; simp at hn

/-- A type with one instance without patterns, at no arguments, unfolds to its body. -/
theorem hasTyp_varT_one {env : Env} {ρ : VarEnv} (hρ : ρ.typs = []) {x : IL.Id} {dt : DefTyp}
    (hx : env.findTyp? x = some ([], [.instD [] [] dt])) {v : Value}
    (h : HasTyp env ρ (.varT x []) v) : HasTypDef env VarEnv.empty dt v := by
  obtain ⟨td, ws, htd, hws, hi⟩ := (hasTyp_varT_global_iff (localTyp_none hρ x)).1 h
  rw [hx] at htd
  cases htd
  have hws' : ws = [] := evalArgs_nil_iff.1 hws
  subst hws'
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hn
  · rw [matchArgs_nil_nil hm] at hd; exact hd
  · exact absurd hn not_hasTypInsts_nil

/-- Typed record fields have the declared names, in order. -/
theorem names_of_hasTypFields {env : Env} {ρ : VarEnv} :
    ∀ {fs : List TypField} {gs : List (AtomS × Value)}, HasTypFields env ρ fs gs →
      gs.map Prod.fst = fs.map fun f => match f with | .mk a _ _ _ => a
  | [], gs, h => by rw [hasTypFields_nil_iff.1 h]; rfl
  | .mk a t qs prems :: fs, gs, h => by
    obtain ⟨w, gs', rfl, -, -, h'⟩ := hasTypFields_cons_iff.1 h
    simp only [List.map_cons, names_of_hasTypFields h']

theorem hasExp_false_of_names {gs : List (AtomS × Value)} {fs : List TypField}
    (hn : gs.map Prod.fst = fs.map fun f => match f with | .mk a _ _ _ => a)
    (hf : noExpFields fs = true) : hasExp gs = false := by
  simp only [hasExp, List.any_eq_false, beq_iff_eq]
  intro g hg hge
  have hm : g.1 ∈ fs.map fun f => match f with | .mk a _ _ _ => a := hn ▸ List.mem_map_of_mem hg
  obtain ⟨f, hf', hfe⟩ := List.mem_map.1 hm
  have := List.all_eq_true.1 hf f hf'
  obtain ⟨a, t, qs, prems⟩ := f
  simp only at hfe this
  rw [hfe, hge] at this
  simp at this

/-- **A typed store has no `EXPORTS` field.** -/
theorem store_inv {B : Builtins} {ρ : VarEnv} (hρ : ρ.typs = []) {S : Value}
    (h : HasTyp (utf8Env B) ρ (.varT "store" []) S) :
    ∀ gs, S = .struct gs → hasExp gs = false := by
  have hd := hasTyp_varT_one hρ (findTyp_store_u B) h
  obtain ⟨gs₀, rfl, hf⟩ := hasTypDef_structT_iff.1 hd
  intro gs hgs
  cases hgs
  exact hasExp_false_of_names (names_of_hasTypFields hf) (store_noExp B)

/-- **A typed state is a state `(S; F)` whose store has no `EXPORTS` field.** -/
theorem state_inv {B : Builtins} {ρ : VarEnv} (hρ : ρ.typs = []) {z : Value}
    (h : HasTyp (utf8Env B) ρ (.varT "state" []) z) :
    ∃ S F, z = stV S F ∧ ∀ gs, S = .struct gs → hasExp gs = false := by
  have hd := hasTyp_varT_one hρ (findTyp_state_u B) h
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
  by_cases hop : "%;%" = op
  · subst hop
    obtain ⟨ht, -⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    obtain ⟨vs, rfl, htup⟩ := hasTyp_tupT_iff.1 ht
    obtain ⟨S, vs', rfl, hS, htup'⟩ := hasTypTup_cons_iff.1 htup
    obtain ⟨F, vs'', rfl, -, htup''⟩ := hasTypTup_cons_iff.1 htup'
    rw [hasTypTup_nil_iff.1 htup'']
    exact ⟨S, F, rfl, store_inv rfl hS⟩
  · exact absurd ((hasTypCase_cons_miss_iff hop).1 hc) not_hasTypCase_nil

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
