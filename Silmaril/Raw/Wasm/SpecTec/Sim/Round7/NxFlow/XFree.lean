module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Agree

/-!
# Round 7, REH route 2: types without `X`, and the clause signature (unrefined)

`vtB_clauseSig`: conformance under `NxTyped.clauseSig sigX tps b qs` is conformance under
`sigX`, for a non-generic clause at every type and for a generic one (type parameter `X`) at
types that do not mention `X`. Substituting the type parameter removes `X` (`xFree_substTP_X`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## `xFree` -/

theorem xFree_iff (a : AT) : xFree a = true ↔ ∀ n ∈ atNames a, n ≠ "X" := by
  unfold xFree
  constructor
  · intro h n hn hx
    subst hx
    simp at h
    exact h hn
  · intro h
    cases hc : (atNames a).contains "X"
    · rfl
    · exact absurd rfl (h _ (List.contains_iff_mem.1 hc))

theorem mem_of_lookup {β : Type} : ∀ {l : List (String × β)} {n : String} {a : β},
    l.lookup n = some a → (n, a) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (m, b) :: l, n, a, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hm
      cases h
      rw [beq_iff_eq.1 hm]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem xFree_base : xFree .base = true := rfl
theorem xFree_unk : xFree .unk = true := rfl

theorem xFree_iter {a : AT} : xFree (.iter a) = xFree a := by simp [xFree, atNames]

theorem xFree_tup {xs : List AT} (h : xFree (.tup xs) = true) : ∀ b ∈ xs, xFree b = true := by
  intro b hb
  rw [xFree_iff] at h ⊢
  intro n hn
  refine h n ?_
  simp only [atNames]
  have : ∀ ys : List AT, b ∈ ys → n ∈ atNames b → n ∈ atNamesL ys := by
    intro ys
    induction ys with
    | nil => intro h; simp at h
    | cons c ys ih =>
      intro hb hn
      simp only [atNamesL, List.mem_append]
      rcases List.mem_cons.1 hb with rfl | hb
      · exact .inl hn
      · exact .inr (ih hb hn)
  exact this xs hb hn

/-! ## Substitution -/

mutual
theorem substTP_nil (b : AT) : ∀ a : AT, substTP [] b a = a
  | .base => rfl
  | .name n xs => by simp [substTP, substTPs_nil b xs]
  | .iter a => by simp [substTP, substTP_nil b a]
  | .tup xs => by simp [substTP, substTPs_nil b xs]
  | .unk => rfl

theorem substTPs_nil (b : AT) : ∀ xs : List AT, substTPs [] b xs = xs
  | [] => rfl
  | a :: xs => by simp [substTPs, substTP_nil b a, substTPs_nil b xs]
end

theorem substPT_nil (b : AT) (p : PT) : substPT [] b p = p := by
  cases p with
  | exp a => simp [substPT, substTP_nil]
  | defn ps r =>
    simp only [substPT, substTP_nil]
    congr 1
    induction ps with
    | nil => rfl
    | cons o ps ih => cases o <;> simp [substTP_nil, ih]
  | other => rfl

theorem map_substPT_nil (b : AT) (ps : List PT) : ps.map (substPT [] b) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [substPT_nil, ih]

mutual
theorem atNames_substTP (tps : List String) (b : AT) :
    ∀ a : AT, ∀ n ∈ atNames (substTP tps b a), n ∈ atNames b ∨ (n ∈ atNames a ∧ ¬ tps.contains n = true)
  | .base, n, h => by simp [substTP, atNames] at h
  | .name m xs, n, h => by
    simp only [substTP] at h
    split at h
    · exact .inl h
    · rename_i hm
      simp only [atNames, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr ⟨by simp [atNames], hm⟩
      · rcases atNamesL_substTPs tps b xs n h with h | ⟨h, h'⟩
        · exact .inl h
        · exact .inr ⟨by simp [atNames, h], h'⟩
  | .iter a, n, h => by
    simp only [substTP, atNames] at h
    rcases atNames_substTP tps b a n h with h | ⟨h, h'⟩
    · exact .inl h
    · exact .inr ⟨by simp [atNames, h], h'⟩
  | .tup xs, n, h => by
    simp only [substTP, atNames] at h
    rcases atNamesL_substTPs tps b xs n h with h | ⟨h, h'⟩
    · exact .inl h
    · exact .inr ⟨by simp [atNames, h], h'⟩
  | .unk, n, h => by simp [substTP, atNames] at h

theorem atNamesL_substTPs (tps : List String) (b : AT) :
    ∀ xs : List AT, ∀ n ∈ atNamesL (substTPs tps b xs),
      n ∈ atNames b ∨ (n ∈ atNamesL xs ∧ ¬ tps.contains n = true)
  | [], n, h => by simp [substTPs, atNamesL] at h
  | a :: xs, n, h => by
    simp only [substTPs, atNamesL, List.mem_append] at h
    rcases h with h | h
    · rcases atNames_substTP tps b a n h with h | ⟨h, h'⟩
      · exact .inl h
      · exact .inr ⟨by simp [atNamesL, h], h'⟩
    · rcases atNamesL_substTPs tps b xs n h with h | ⟨h, h'⟩
      · exact .inl h
      · exact .inr ⟨by simp [atNamesL, h], h'⟩
end

/-- Substituting `X` by a type without `X` removes `X`. -/
theorem xFree_substTP_X {tps : List String} (hx : tps.contains "X" = true) {b : AT}
    (hb : xFree b = true) (a : AT) : xFree (substTP tps b a) = true := by
  rw [xFree_iff] at hb ⊢
  intro n hn
  rcases atNames_substTP tps b a n hn with h | ⟨_, h'⟩
  · exact hb n h
  · intro e; subst e; exact h' hx

/-- Substitution by a type without `X` keeps a type without `X`. -/
theorem xFree_substTP {tps : List String} {b : AT} (hb : xFree b = true) {a : AT}
    (ha : xFree a = true) : xFree (substTP tps b a) = true := by
  rw [xFree_iff] at hb ha ⊢
  intro n hn
  rcases atNames_substTP tps b a n hn with h | ⟨h, _⟩
  · exact hb n h
  · exact ha n h

/-! ## The clause signature -/

theorem SameShape.symm {S₁ S₂ : Sig} (h : SameShape S₁ S₂) : SameShape S₂ S₁ :=
  ⟨h.aliases.symm, h.fields.symm, h.cases.symm⟩

theorem sameShape_clauseSig (S : Sig) (tps : List String) (b : AT) (qs : List Param) :
    SameShape S (clauseSig S tps b qs) := ⟨rfl, rfl, rfl⟩

theorem clauseSig_good_nil (S : Sig) (b : AT) (qs : List Param) :
    (clauseSig S [] b qs).good = S.good := by
  simp only [clauseSig]
  split <;> simp

theorem clauseSig_good_X (S : Sig) (b : AT) (qs : List Param) :
    (clauseSig S ["X"] b qs).good = S.good ∨
      (clauseSig S ["X"] b qs).good = S.good.filter (fun x => !["X"].contains x) := by
  simp only [clauseSig]
  split
  · exact .inr rfl
  · exact .inl rfl

theorem unalias_xFree {S : Sig} (hS : (S.aliases.all fun p => xFree p.2) = true) :
    ∀ k a, xFree a = true → xFree (unalias S k a) = true
  | 0, _, h => h
  | k + 1, .name n xs, h => by
    simp only [unalias]
    split
    · rename_i a ha
      refine unalias_xFree hS k a ?_
      have hm : (n, a) ∈ S.aliases := mem_of_lookup ha
      exact (List.all_eq_true.1 hS) _ hm
    · exact h
  | _ + 1, .base, h => h
  | _ + 1, .iter _, h => h
  | _ + 1, .tup _, h => h
  | _ + 1, .unk, h => h

theorem fieldAT_xFree {S : Sig} (hS : (S.fields.all fun p => xFree p.2.2) = true) (n k : String) :
    xFree (fieldAT S n k) = true := by
  unfold fieldAT
  split
  · rename_i p hp
    exact (List.all_eq_true.1 hS) _ (List.mem_of_find?_eq_some hp)
  · rfl

theorem caseAT_xFree {S : Sig} (hS : (S.cases.all fun p => xFree p.2.2) = true) (n k : String) :
    xFree (caseAT S n k) = true := by
  unfold caseAT
  split
  · rename_i p hp
    exact (List.all_eq_true.1 hS) _ (List.mem_of_find?_eq_some hp)
  · rfl

/-- **Conformance under the clause signature of a definition with type parameters `tps`**, at a
type that is free of `X` unless the definition is not generic. -/
theorem vtB_clauseSig {S : Sig} (ha₁ : (S.aliases.all fun p => xFree p.2) = true)
    (hf₁ : (S.fields.all fun p => xFree p.2.2) = true)
    (hc₁ : (S.cases.all fun p => xFree p.2.2) = true) {tps : List String}
    (htps : tps = [] ∨ tps = ["X"]) (b : AT) (qs : List Param) {a : AT}
    (ha : tps = [] ∨ xFree a = true) (v : Value) :
    vtB (clauseSig S tps b qs) a v = vtB S a v := by
  rcases htps with rfl | rfl
  · exact vtB_eq_good (sameShape_clauseSig S [] b qs).symm (clauseSig_good_nil S b qs) a v
  · rcases ha with h | ha
    · cases h
    rcases clauseSig_good_X S b qs with hg | hg
    · exact vtB_eq_good (sameShape_clauseSig S ["X"] b qs).symm hg a v
    · have hQ : ShapeClosed S (clauseSig S ["X"] b qs).good (fun a => xFree a = true) := {
        names := fun a ha n hn => by
          rw [hg]
          have hnx : n ≠ "X" := (xFree_iff a).1 ha n hn
          simp [List.mem_filter, hnx]
        unf := fun a ha => unalias_xFree ha₁ 8 a ha
        iter := fun a ha => by rwa [xFree_iter] at ha
        tup := fun xs h => xFree_tup h
        field := fun n k => fieldAT_xFree hf₁ n k
        case := fun n k => caseAT_xFree hc₁ n k
        unk := rfl }
      exact (vtB_agree (sameShape_clauseSig S ["X"] b qs) hQ v a ha).symm

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
