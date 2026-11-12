module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Assemble

/-!
# Round 7, REH route 2: values of a checked type conform (unrefined)

`vtTyp : ∀ n, VtTyp env n`: by induction on `Sem.hasTyp`'s fuel, a value of type `t` conforms
to `toAT t` under `sigX`, in a scope whose type variables are export-free, in an environment
whose types pass `typVt` and whose export-free types are export-free (`NxSites.EnvNx`).
Export-free types are round 6's `NxSites.nxTyp`; the others are read through the instances of
their type definitions, which agree with `sigX`'s entries.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## Facts about one type -/

/-- **What `typVt` says about one instance body of `x`.** -/
structure XF (x : String) (dt : DefTyp) : Prop where
  ali : ∀ p ∈ sigX.aliases, p.1 = x → ∃ t, dt = .aliasT t ∧ toAT t = p.2
  field : ∀ p ∈ sigX.fields, p.1 = x → ∃ fs, dt = .structT fs ∧
    (fieldOf p.2.1 fs).map toAT = some p.2.2
  case : ∀ p ∈ sigX.cases, p.1 = x → ∃ cs, dt = .variantT cs ∧
    (caseOf p.2.1 cs).map toAT = some p.2.2
  nodup : ∀ fs, dt = .structT fs → nodupS (fieldAtoms fs) = true
  good : sigX.good.contains x = true → goodDT sigX.good dt = true

/-- **What `typVt` says about the instances of `x`.** -/
def IF (x : String) (insts : List Inst) : Prop :=
  ∀ i ∈ insts, (match i with | .instD _ pats _ => ∀ a ∈ pats, ∀ t, a ≠ .typA t) ∧
    XF x (instDT i)

theorem atEq_beq_iff {a b : AT} : (a == b) = true ↔ a = b := atEq_iff a b

theorem optAT_beq_iff {o : Option AT} {a : AT} : (o == some a) = true ↔ o = some a := by
  cases o with
  | none => simp
  | some b =>
    show (atEq b a = true) ↔ some b = some a
    rw [atEq_iff]; simp

theorem if_of_typVt {x : String} {ps : List Param} {insts : List Inst}
    (h : typVt sigX x ps insts = true) (he : hasEntry sigX x = true) : IF x insts := by
  simp only [typVt, he, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hs, _⟩, hi⟩ := h
  simp only [sigTypOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
    at hs
  obtain ⟨⟨⟨ha, hf⟩, hc⟩, hg⟩ := hs
  intro i hmi
  have hio := hi i hmi
  obtain ⟨q, pats, dt⟩ := i
  simp only [instOk, Bool.and_eq_true, List.all_eq_true] at hio
  refine ⟨fun a ha' t heq => by have := hio.1 a ha'; subst heq; simp at this, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp hx
    rcases ha p hp with h1 | h1
    · exact absurd hx h1
    · obtain ⟨_, h2⟩ := h1
      have := h2 _ hmi
      simp only [instDT] at this ⊢
      split at this
      · rename_i t
        exact ⟨t, rfl, atEq_beq_iff.1 this⟩
      · cases this
  · intro p hp hx
    rcases hf p hp with h1 | h1
    · exact absurd hx h1
    · obtain ⟨_, h2⟩ := h1
      have := h2 _ hmi
      simp only [instDT] at this ⊢
      split at this
      · rename_i fs
        refine ⟨fs, rfl, ?_⟩
        exact optAT_beq_iff.1 (by simpa using this)
      · cases this
  · intro p hp hx
    rcases hc p hp with h1 | h1
    · exact absurd hx h1
    · obtain ⟨_, h2⟩ := h1
      have := h2 _ hmi
      simp only [instDT] at this ⊢
      split at this
      · rename_i cs
        refine ⟨cs, rfl, ?_⟩
        exact optAT_beq_iff.1 (by simpa using this)
      · cases this
  · intro fs hfs
    simp only [instDT] at hfs
    subst hfs
    simpa using hio.2
  · intro hgx
    rcases hg with h1 | h1
    · simp_all
    · exact h1 _ hmi

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## Unfolding names -/

theorem unf_name_none {x : String} {A : List AT} (h : sigX.aliases.lookup x = none) :
    unf sigX (.name x A) = .name x A := by
  simp [unf, unalias, h]

theorem unf_name_some {x : String} {A : List AT} {a : AT} (h : sigX.aliases.lookup x = some a) :
    unf sigX (.name x A) = unf sigX a := by
  have hm := List.all_eq_true.1 aliasFuelOk_sigX _ (mem_of_lookup' h)
  simp only [atEq_iff] at hm
  simp only [unf, unalias, h]
  exact hm
where
  mem_of_lookup' {l : List (String × AT)} {x : String} {a : AT} (h : l.lookup x = some a) :
      (x, a) ∈ l := by
    induction l with
    | nil => simp [List.lookup] at h
    | cons p l ih =>
      obtain ⟨y, b⟩ := p
      simp only [List.lookup] at h
      split at h
      · rename_i hy; cases h; rw [beq_iff_eq.1 hy]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_entry {x : String} {a : AT} (h : sigX.aliases.lookup x = some a) :
    ∃ p ∈ sigX.aliases, p.1 = x ∧ p.2 = a :=
  ⟨(x, a), unf_name_some.mem_of_lookup' h, rfl, rfl⟩

theorem fieldAT_cases (x k : String) :
    fieldAT sigX x k = .unk ∨ ∃ p ∈ sigX.fields, p.1 = x ∧ p.2.1 = k ∧ fieldAT sigX x k = p.2.2 := by
  unfold fieldAT
  split
  · rename_i p hp
    have hm := List.mem_of_find?_eq_some hp
    have hc := List.find?_some hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact .inr ⟨p, hm, hc.1, hc.2, rfl⟩
  · exact .inl rfl

theorem caseAT_cases (x k : String) :
    caseAT sigX x k = .unk ∨ ∃ p ∈ sigX.cases, p.1 = x ∧ p.2.1 = k ∧ caseAT sigX x k = p.2.2 := by
  unfold caseAT
  split
  · rename_i p hp
    have hm := List.mem_of_find?_eq_some hp
    have hc := List.find?_some hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact .inr ⟨p, hm, hc.1, hc.2, rfl⟩
  · exact .inl rfl

theorem vtF_noFields {x : String} (h : ∀ p ∈ sigX.fields, p.1 ≠ x) :
    ∀ gs : List (AtomS × Value), vtF sigX x gs = true
  | [] => rfl
  | (k, w) :: gs => by
    simp only [vtF, Bool.and_eq_true]
    refine ⟨?_, vtF_noFields h gs⟩
    rcases fieldAT_cases x k with he | ⟨p, hp, hx, _, _⟩
    · rw [he]; exact vtB_unk _ _
    · exact absurd hx (h p hp)

theorem caseAT_noCases {x k : String} (h : ∀ p ∈ sigX.cases, p.1 ≠ x) :
    caseAT sigX x k = .unk := by
  rcases caseAT_cases x k with he | ⟨p, hp, hx, _, _⟩
  · exact he
  · exact absurd hx (h p hp)

theorem matchArgs_typs {env : Env} : ∀ (n : Nat) (ρ ρ' : VarEnv) (pats : List Arg)
    (ws : List ArgV), (∀ a ∈ pats, ∀ t, a ≠ .typA t) → matchArgs n env ρ pats ws = .ok ρ' →
    ρ'.typs = ρ.typs
  | 0, _, _, _, _, _, h => by simp [matchArgs] at h
  | n + 1, ρ, ρ', [], [], _, h => by simp only [matchArgs, Except.ok.injEq] at h; subst h; rfl
  | n + 1, ρ, ρ', a :: pats, w :: ws, hp, h => by
    simp only [matchArgs, Res.bind_eq_ok] at h
    obtain ⟨ρ₁, h₁, h₂⟩ := h
    have e₂ := matchArgs_typs n ρ₁ ρ' pats ws (fun b hb => hp b (List.mem_cons_of_mem _ hb)) h₂
    rw [e₂]
    rcases n with _ | n
    · simp [matchArg] at h₁
    cases a <;> cases w <;> simp only [matchArg] at h₁
    case expA.val e v =>
      split at h₁
      · exact (TypAgree.typsPres env n).matchExp _ _ _ _ h₁
      · cases h₁
    case typA.typ t _ => exact absurd rfl (hp _ (List.mem_cons_self ..) t)
    case defA.defName => cases h₁; rfl
    case gramA.gram => exact matchSymV_typs' h₁
    all_goals cases h₁
  | n + 1, _, _, [], _ :: _, _, h => by simp [matchArgs] at h
  | n + 1, _, _, _ :: _, [], _, h => by simp [matchArgs] at h

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
