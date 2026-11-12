module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureControl

/-!
# The concatenation rules of wasm-2.0 `Step_pure`: unique splits

The left-hand sides of `br-zero`, `br-succ`, `return-frame`, `return-label` and `trap-vals` are
concatenations `val* M instr*` of a value prefix, a marker `M` (`BR l`, `RETURN`, `TRAP`) and a
tail. Reading such a rule back at the image of a V2 code sequence needs the split to be unique.
It is, because

* every element of the IL prefix has the IL type `val`, and a typed `val` is a `case` whose
  constructor is one of `val`'s five (`head_of_typed_val20`, from the 2.0 script's definition of
  `val`), while
* the marker's constructor (`BR`, `RETURN`, `TRAP`) is not one of them, and
* the image of a V2 value has one of them (`valHead_valV`).

`split_unique` is the list fact; `valHead_of_typed`, `not_valHead_*` and `valHead_valV` are its
three inputs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

/-! ## The list fact -/

/-- **A split at the first element outside `p` is unique.** -/
theorem split_unique {α : Type} {p : α → Prop} :
    ∀ {xs ys : List α} {x y : α} {r s : List α}, (∀ a ∈ xs, p a) → (∀ a ∈ ys, p a) →
      ¬ p x → ¬ p y → xs ++ x :: r = ys ++ y :: s → xs = ys ∧ x = y ∧ r = s
  | [], [], _, _, _, _, _, _, _, _, h => by
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h⟩
  | [], b :: ys, _, _, _, _, _, hys, hx, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hys b (.head _)) hx
  | a :: xs, [], _, _, _, _, hxs, _, _, hy, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hxs a (.head _)) hy
  | a :: xs, b :: ys, _, _, _, _, hxs, hys, hx, hy, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := split_unique (fun c hc => hxs c (.tail _ hc))
        (fun c hc => hys c (.tail _ hc)) hx hy h
      exact ⟨rfl, rfl, rfl⟩

/-! ## Value heads -/

/-- The constructors of the wasm-2.0 IL type `val` (`Scripts.Wasm20.Original.d282`). -/
def valHeads20 : List MixopS := ["CONST", "VCONST", "REF.NULL", "REF.FUNC_ADDR", "REF.HOST_ADDR"]

/-- `u` is a `case` with one of `val`'s constructors. -/
def ValHead (u : Value) : Prop := ∃ op w, u = .case op w ∧ op ∈ valHeads20

/-- A marker `op x` whose constructor is not one of `val`'s. -/
theorem not_valHead_case {op : MixopS} {x : Value} (h : op ∉ valHeads20) :
    ¬ ValHead (.case op x) := by
  rintro ⟨op', w, he, hm⟩
  obtain ⟨rfl, -⟩ := Value.case.inj he
  exact h hm

/-- `BR l` is not a value. -/
theorem not_valHead_br {x : Value} : ¬ ValHead (.case "BR" x) :=
  not_valHead_case (by decide)

/-- `RETURN` is not a value. -/
theorem not_valHead_return : ¬ ValHead (caseNilV "RETURN") :=
  not_valHead_case (by decide)

/-- `TRAP` is not a value. -/
theorem not_valHead_trap : ¬ ValHead (caseNilV "TRAP") :=
  not_valHead_case (by decide)

/-- The image of a V2 value has a value head. -/
theorem valHead_valV (v : Val) : ValHead (valV v) := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> exact ⟨_, _, rfl, by decide⟩

/-- The image of a V2 value sequence has value heads only. -/
theorem valHead_vals (vs : List Val) : ∀ u ∈ adminsToV (vals vs), ValHead u := by
  rw [adminsToV_vals]
  intro u hu
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
  exact valHead_valV v

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `val`, as `simEnv20 B` finds it. -/
theorem findTyp_val20 : (simEnv20 B).findTyp? "val" =
    some ([], [.instD [] [] (.variantT
      (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
        Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d282 0))]) := rfl

set_option maxRecDepth 100000 in
/-- The constructors of `val`, read off the script. -/
theorem valCases20_heads :
    (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
        Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d282 0).map
      (fun c : TypCase => match c with | .mk o _ _ _ => o) = valHeads20 := rfl

/-- **A typed wasm-2.0 `val` has a value head.** -/
theorem valHead_of_typed {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv20 B) ρ (.varT "val" []) v) : ValHead v := by
  have hl : localTyp? ρ "val" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_val20] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    have hmem := List.mem_map_of_mem (f := fun c : TypCase => match c with | .mk o _ _ _ => o) hm
    rw [valCases20_heads] at hmem
    exact ⟨op, w, rfl, hmem⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- Every element of a typed `val*` has a value head. -/
theorem valHeads_of_typed {ρ : VarEnv} (hρ : ValsOnly ρ) {ws : List Value}
    (h : HasTyp (simEnv20 B) ρ valsT (.list ws)) : ∀ u ∈ ws, ValHead u := by
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := (Value.list.inj hvs).symm
  exact fun u hu => valHead_of_typed hρ (hasTypList_iff.1 hl u hu)

/-- A scope built by `bindVals` binds term variables only. -/
theorem valsOnly_bindVals (σ : List (IL.Id × Value)) : ValsOnly (VarEnv.empty.bindVals σ) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Encodings of sequences -/

/-- `adminsToV` is a `map`. -/
theorem adminsToV_eq_map : ∀ l : List Admin, adminsToV l = l.map adminToV
  | [] => rfl
  | a :: l => by
    show adminToV a :: adminsToV l = _
    rw [adminsToV_eq_map l]
    rfl

/-- `adminsToV` distributes over `++`. -/
theorem adminsToV_append (l₁ l₂ : List Admin) :
    adminsToV (l₁ ++ l₂) = adminsToV l₁ ++ adminsToV l₂ := by
  simp only [adminsToV_eq_map, List.map_append]

/-- A plain instruction sequence is encoded as the instruction sequence. -/
theorem adminsToV_expression : ∀ is : List V2.Instr, adminsToV (expression is) = instrsToV is
  | [] => rfl
  | i :: is => by
    show adminToV (.plain i) :: adminsToV (expression is) = instrToV i :: instrsToV is
    rw [adminsToV_expression is]
    rfl

/-- A value sequence split in two. -/
theorem map_valV_eq_append {us : List Val} {a b : List Value} (h : us.map valV = a ++ b) :
    ∃ vs' vs, us = vs' ++ vs ∧ vs'.map valV = a ∧ vs.map valV = b := by
  obtain ⟨vs', vs, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 h
  exact ⟨vs', vs, rfl, h₁, h₂⟩

/-! ## Label indices -/

/-- Unfold a closed alias `x = t`. -/
theorem hasTyp_closedAlias {env : Env} {x : IL.Id} {t : Typ} {ρ : VarEnv} (hρ : ValsOnly ρ)
    (htd : env.findTyp? x = some ([], [.instD [] [] (.aliasT t)])) {v : Value}
    (h : HasTyp env ρ (.varT x []) v) : HasTyp env VarEnv.empty t v := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Silmaril.Wasm.SpecTec.Sim.IntNumeric.matchArgs_nil_scope hm
    exact hasTypDef_aliasT_iff.1 hd
  · exact absurd hrest not_hasTypInsts_nil

set_option maxRecDepth 100000 in
theorem findTyp_labelidx20 : (simEnv20 B).findTyp? "labelidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_idx20 : (simEnv20 B).findTyp? "idx" =
    some ([], [.instD [] [] (.aliasT (.varT "u32" []))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_u32_20 : (simEnv20 B).findTyp? "u32" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 32))]))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_uN20 : ∃ ps qs, (simEnv20 B).findTyp? "uN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT
      (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
        Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d17 0))]) := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem uNCases20 : ∃ p, Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
    Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d17 0 =
      [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] p] := ⟨_, rfl⟩

/-- A payload of `uN`'s one case is a numeral `%(k)`. -/
theorem uNCase_inv {σ : VarEnv} {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv20 B) σ (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d17 0) op w) : ∃ k, Value.case op w = pctV k := by
  obtain ⟨t, qs', prems, hm, ht, -⟩ := hasTypCase_mem hc
  obtain ⟨p, hp⟩ := uNCases20
  have hm' : TypCase.mk op t qs' prems = .mk "%" (.tupT [.mk "i" (.numT .natT)]) [] p :=
    List.mem_singleton.1 (hp ▸ hm)
  obtain ⟨rfl, rfl, -, -⟩ := TypCase.mk.inj hm'
  obtain ⟨vs, rfl, ht'⟩ := hasTyp_tupT_iff.1 ht
  obtain ⟨x, vs₁, rfl, hx, ht₁⟩ := hasTypTup_cons_iff.1 ht'
  have hv₁ : vs₁ = [] := hasTypTup_nil_iff.1 ht₁
  obtain ⟨m, rfl, hm''⟩ := hasTyp_numT_iff.1 hx
  cases m with
  | natN k => exact ⟨k, by rw [hv₁]; rfl⟩
  | _ => simp [Num.toTyp, Num.subTyp] at hm''

/-- A value of `uN(32)` is a numeral `%(k)`. -/
theorem uN32_inv {ρ : VarEnv} {v : Value}
    (h : HasTyp (simEnv20 B) ρ (.varT "uN" [.expA (.numE (.natN 32))]) v) : ∃ k, v = pctV k := by
  obtain ⟨ps, qs, htd⟩ := findTyp_uN20 (B := B)
  have hl : localTyp? ρ "uN" [.expA (.numE (.natN 32))] = none := by simp [localTyp?]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  have etd : td = (ps, [.instD qs [.expA (.varE "N")] (.variantT
      (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
        Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d17 0))]) :=
    (Option.some.inj (htd.symm.trans htd')).symm
  rcases hasTypInsts_cons_inv (etd ▸ hi) with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    exact uNCase_inv hc
  · exact absurd hrest not_hasTypInsts_nil

/-- **A typed wasm-2.0 `labelidx` is a numeral `%(k)`.** -/
theorem labelidx_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv20 B) ρ labelidxT v) : ∃ k, v = pctV k :=
  uN32_inv (hasTyp_closedAlias ⟨rfl, rfl, rfl⟩ findTyp_u32_20
    (hasTyp_closedAlias ⟨rfl, rfl, rfl⟩ findTyp_idx20 (hasTyp_closedAlias hρ findTyp_labelidx20 h)))

end Silmaril.Wasm.SpecTec.Sim20.Pure
