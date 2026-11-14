module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Basic

/-!
# The encodings have the IL types their rules declare

`typedV_con` reduces the typing of a constructor value `con c vs` at a closed variant type to the
typing of its payload; the instances below discharge the quantifiers of the fragment's rules:
`S` (`typedV_emptyS`), the operators at `unop`/`binop`/`cmpop` and their sub-sorts, numbers at
`num`, encoded expressions at `exp` (`typedV_enc`), literals at `val`. Conversely an encoded
expression of type `val` is a literal (`isLit_of_typedV_val`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

set_option maxRecDepth 100000

/-! ## Scopes that bind values only -/

theorem valsOnly_empty : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩

theorem ValsOnly.bindVal {ρ : VarEnv} (h : ValsOnly ρ) (x : IL.Id) (v : Value) :
    ValsOnly (ρ.bindVal x v) := h

theorem ValsOnly.bindVals {ρ : VarEnv} (h : ValsOnly ρ) (σ : List (IL.Id × Value)) :
    ValsOnly (ρ.bindVals σ) := h

theorem localTyp_none {ρ : VarEnv} (h : ValsOnly ρ) (x : IL.Id) : localTyp? ρ x [] = none := by
  simp [localTyp?, VarEnv.findTyp?, h.1]

/-! ## Closed variant types -/

/-- The operator of a case. -/
def TypCase.op : TypCase → MixopS
  | .mk o _ _ _ => o

/-- The first case of `cs` with operator `c` has payload type `t`, no quantifiers and no
premises. -/
def FindCase (cs : List TypCase) (c : MixopS) (t : Typ) : Prop :=
  cs.find? (fun tc => TypCase.op tc == c) = some (.mk c t [] [])

theorem hasTypCase_of_find {env : Env} {ρ : VarEnv} {c : MixopS} {t : Typ} {w : Value} :
    ∀ {cs : List TypCase}, FindCase cs c t → HasTyp env ρ t w → HasTypCase env ρ cs c w
  | [], h, _ => by simp [FindCase] at h
  | .mk o t' qs ps :: cs, h, hw => by
      by_cases ho : o = c
      · subst ho
        simp only [FindCase, List.find?_cons, TypCase.op, beq_self_eq_true,
          Option.some.injEq, TypCase.mk.injEq, true_and] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (hasTypCase_cons_hit_iff rfl).2 ⟨hw, premsOk_nil⟩
      · rw [hasTypCase_cons_miss_iff ho]
        have hb : (o == c) = false := by simpa using ho
        simp only [FindCase, List.find?_cons, TypCase.op, hb] at h
        exact hasTypCase_of_find h hw

/-- The case `c` of an inhabited case means `c` is among the operators. -/
theorem mem_ops_of_hasTypCase {env : Env} {ρ : VarEnv} {c : MixopS} {w : Value} :
    ∀ {cs : List TypCase}, HasTypCase env ρ cs c w → c ∈ cs.map TypCase.op
  | [], h => absurd h not_hasTypCase_nil
  | .mk o t' qs ps :: cs, h => by
      by_cases ho : o = c
      · subst ho; simp [TypCase.op]
      · rw [hasTypCase_cons_miss_iff ho] at h
        exact List.mem_cons_of_mem _ (mem_ops_of_hasTypCase h)

/-- `x` is a closed variant type with cases `cs`. -/
def VariantDef (env : Env) (x : IL.Id) (cs : List TypCase) : Prop :=
  env.findTyp? x = some ([], [.instD [] [] (.variantT cs)])

/-- A constructor value at a closed variant type: its payload at the case's type. -/
theorem typedV_case {env : Env} {x : IL.Id} {cs : List TypCase} {c : MixopS} {t : Typ}
    {w : Value} (hd : VariantDef env x cs) (hc : FindCase cs c t)
    (hw : ∀ ρ, ValsOnly ρ → HasTyp env ρ t w) : TypedV env (.varT x []) (.case c w) := by
  intro ρ hρ
  refine (hasTyp_varT_global_iff (localTyp_none hρ x)).2 ⟨_, [], hd, evalArgs_nil _ _, ?_⟩
  exact hasTypInsts_head matchArgs_nil
    (hasTypDef_variantT_iff.2 ⟨c, w, rfl, hasTypCase_of_find hc (hw _ valsOnly_empty)⟩)

/-- The inversion: a value of a closed variant type is a case whose operator is declared. -/
theorem case_of_typed {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id}
    {cs : List TypCase} (hd : VariantDef env x cs) {v : Value}
    (h : HasTyp env ρ (.varT x []) v) : ∃ c w, v = .case c w ∧ c ∈ cs.map TypCase.op := by
  obtain ⟨td, ws, htd, hws, hi⟩ := (hasTyp_varT_global_iff (localTyp_none hρ x)).1 h
  rw [hd] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hdt⟩ | hrest
  · obtain ⟨c, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hdt
    exact ⟨c, w, rfl, mem_ops_of_hasTypCase hc⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- A tuple of payloads, component by component (the binders bind values only). -/
theorem hasTypTup_cons {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id} {t : Typ}
    {bs : List TypBind} {w : Value} {ws : List Value}
    (hw : ∀ ρ, ValsOnly ρ → HasTyp env ρ t w)
    (hws : ∀ ρ, ValsOnly ρ → HasTypTup env ρ bs ws) :
    HasTypTup env ρ (.mk x t :: bs) (w :: ws) :=
  hasTypTup_cons_iff.2 ⟨w, ws, rfl, hw ρ hρ, hws _ (ValsOnly.bindVal hρ x w)⟩

theorem hasTypTup_nil {env : Env} {ρ : VarEnv} : HasTypTup env ρ [] [] :=
  hasTypTup_nil_iff.2 rfl

/-- A constructor `con c vs` at a closed variant type whose case `c` carries the tuple `bs`. -/
theorem typedV_con {env : Env} {x : IL.Id} {cs : List TypCase} {c : MixopS}
    {bs : List TypBind} {vs : List Value} (hd : VariantDef env x cs)
    (hc : FindCase cs c (.tupT bs)) (hvs : ∀ ρ, ValsOnly ρ → HasTypTup env ρ bs vs) :
    TypedV env (.varT x []) (con c vs) :=
  typedV_case hd hc fun ρ hρ => hasTyp_tupT_iff.2 ⟨vs, rfl, hvs ρ hρ⟩

end Silmaril.Wasm.SpecTec.Meta
