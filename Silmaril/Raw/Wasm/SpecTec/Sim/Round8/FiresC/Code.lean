module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.FiresC.TypBase
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckTyp

/-!
# Round 8, typing across code erasure: the `CODE` field (unrefined)

The one place where typing is not congruent with `eraseC`: a `CODE` field `u` becomes
`hostC u = _HOSTFUNC (enc u)`. `hasTyp_code`: if any `u` is a `funccode` at fuel `n`, so is every
`hostC u'`. A `FUNC` code needs at least fuel 4 at the variant (its tuple has a binder), a
`_HOSTFUNC` code exactly 3, at the same fuel.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

theorem funccodeOk_shape {d : TypDef} (h : funccodeOk d = true) :
    ∃ ps q t₁ qs₁ prems₁, (∃ b bs, t₁ = .tupT (b :: bs)) ∧
      d = (ps, [.instD q [] (.variantT [.mk "FUNC" t₁ qs₁ prems₁, .mk "_HOSTFUNC" .textT [] []])]) := by
  unfold funccodeOk at h
  split at h
  · exact ⟨_, _, _, _, _, ⟨_, _, rfl⟩, rfl⟩
  · cases h

theorem findTyp_funccode {B : Builtins} {d : TypDef}
    (h : (simEnv B).findTyp? "funccode" = some d) : funccodeOk d = true := by
  have hm := Round7.TypAgree.mem_typs_of_findTyp h
  have := List.all_eq_true.1 funccodeMap_fixed _ hm
  simpa using this

section
variable (env : Env) (ρ : VarEnv) (t₁ : Typ) (qs₁ : List Param) (prems₁ : List Prem)

/-- With fuel 3 or more, `_HOSTFUNC s` is a case of the variant. -/
theorem hasTypCase_host (k : Nat) (s : String) :
    hasTypCase (k + 3) env ρ [.mk "FUNC" t₁ qs₁ prems₁, .mk "_HOSTFUNC" .textT [] []]
      "_HOSTFUNC" (.text s) = .ok true := by
  simp only [hasTypCase]
  simp only [show ("FUNC" : String) ≠ "_HOSTFUNC" by decide, ↓reduceIte]
  simp only [hasTyp, Value.asText?, Option.isSome_some, quantDefs, List.flatMap_nil, bindQuants]
  simp [Res.elimUndef, premsOk, premsHold_nil_eq]

/-- A case of the variant needs fuel 3. -/
theorem hasTypCase_three {op : MixopS} {w : Value} {b : Nat} (ht : ∃ c cs, t₁ = .tupT (c :: cs))
    (h : hasTypCase b env ρ [.mk "FUNC" t₁ qs₁ prems₁, .mk "_HOSTFUNC" .textT [] []] op w =
      .ok true) : 3 ≤ b := by
  obtain ⟨c, cs, rfl⟩ := ht
  rcases b with _ | _ | _ | b
  · simp [hasTypCase] at h
  · simp only [hasTypCase] at h
    split at h
    · simp [hasTyp] at h
    · simp at h
  · simp only [hasTypCase] at h
    split at h
    · cases hw : w.asTuple? <;> simp [hasTyp, hasTypTup, hw] at h
    · simp [hasTyp] at h
  · omega

end

/-- **A `funccode` value at fuel `n` makes every `hostC u'` one**, in scopes without type
variables. -/
theorem hasTyp_code {B : Builtins} {n : Nat} {ρ ρ' : VarEnv} (h₁ : ρ.typs = []) (h₂ : ρ'.typs = [])
    {u : Value} (u' : Value)
    (h : hasTyp n (simEnv B) ρ (.varT "funccode" []) u = .ok true) :
    hasTyp n (simEnv B) ρ' (.varT "funccode" []) (hostC u') = .ok true := by
  rcases n with _ | a
  · simp [hasTyp] at h
  have hl : ∀ σ : VarEnv, σ.typs = [] → localTyp? σ "funccode" [] = none := by
    intro σ hσ; simp [localTyp?, VarEnv.findTyp?, hσ]
  simp only [hasTyp, hl ρ h₁, hl ρ' h₂] at h ⊢
  rw [Res.bind_eq_ok] at h ⊢
  obtain ⟨td, htd, h⟩ := h
  have hf : (simEnv B).findTyp? "funccode" = some td := by
    cases hf : (simEnv B).findTyp? "funccode" with
    | none => rw [hf] at htd; simp [Res.ofOption] at htd
    | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
  refine ⟨td, htd, ?_⟩
  obtain ⟨ps, q, t₁, qs₁, prems₁, ht₁, rfl⟩ := funccodeOk_shape (findTyp_funccode hf)
  rw [Res.bind_eq_ok] at h ⊢
  obtain ⟨ws, hws, h⟩ := h
  rcases a with _ | a
  · simp [evalArgs] at hws
  have hws' : ws = [] := by
    simp only [evalArgs, List.mapM_nil] at hws
    cases hws; rfl
  subst hws'
  refine ⟨[], by simp [evalArgs]; rfl, ?_⟩
  simp only [hasTypInsts] at h ⊢
  rcases a with _ | a
  · simp [matchArgs, Res.elimUndef] at h
  simp only [matchArgs, Res.elimUndef, hasTypDef] at h ⊢
  have hc : (hostC u').asCase? = some ("_HOSTFUNC", .text (enc u')) := rfl
  rw [hc]
  cases hu : u.asCase? with
  | none => rw [hu] at h; cases h
  | some p =>
    rw [hu] at h
    obtain ⟨op, w⟩ := p
    have h3 := hasTypCase_three _ _ _ _ _ ht₁ h
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 3 := ⟨a - 3, by omega⟩
    exact hasTypCase_host _ _ _ _ _ k _

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
