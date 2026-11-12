module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.StepMatch2

/-!
# Round 7, REH route 2: conformance under a clause's signature (unrefined)

Inside a clause the flow check reads the signature `NxTyped.clauseSig`: the same aliases, fields
and cases, other result types, and, for a generic definition checked with unknown type
parameters, `good` without `X`. Conformance does not read result types, and reads `good` only
at the names of the types involved, so it agrees between the two signatures at types that do not
mention `X` (`vtB_agree`). With `good` unchanged, `atLe` and `defSub` agree as well.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-- Two signatures with the same aliases, fields and cases. -/
structure SameShape (S₁ S₂ : Sig) : Prop where
  aliases : S₁.aliases = S₂.aliases
  fields : S₁.fields = S₂.fields
  cases : S₁.cases = S₂.cases

theorem unalias_shape {S₁ S₂ : Sig} (h : SameShape S₁ S₂) : ∀ k a, unalias S₁ k a = unalias S₂ k a
  | 0, _ => rfl
  | k + 1, .name n xs => by simp only [unalias, h.aliases, unalias_shape h k]
  | _ + 1, .base => rfl
  | _ + 1, .iter _ => rfl
  | _ + 1, .tup _ => rfl
  | _ + 1, .unk => rfl

theorem unf_shape {S₁ S₂ : Sig} (h : SameShape S₁ S₂) (a : AT) : unf S₁ a = unf S₂ a :=
  unalias_shape h 8 a

theorem fieldAT_shape {S₁ S₂ : Sig} (h : SameShape S₁ S₂) (n k : String) :
    fieldAT S₁ n k = fieldAT S₂ n k := by simp only [fieldAT, h.fields]

theorem caseAT_shape {S₁ S₂ : Sig} (h : SameShape S₁ S₂) (n k : String) :
    caseAT S₁ n k = caseAT S₂ n k := by simp only [caseAT, h.cases]

mutual
theorem nxAT_agree {g₁ g₂ : List String} : ∀ a : AT,
    (∀ n ∈ atNames a, g₁.contains n = g₂.contains n) → nxAT g₁ a = nxAT g₂ a
  | .base, _ => rfl
  | .name n xs, h => by
    simp only [atNames, List.mem_cons] at h
    simp only [nxAT, h n (.inl rfl), nxATs_agree xs fun m hm => h m (.inr hm)]
  | .iter a, h => by simp only [atNames] at h; simp only [nxAT, nxAT_agree a h]
  | .tup xs, h => by simp only [atNames] at h; simp only [nxAT, nxATs_agree xs h]
  | .unk, _ => rfl

theorem nxATs_agree {g₁ g₂ : List String} : ∀ xs : List AT,
    (∀ n ∈ atNamesL xs, g₁.contains n = g₂.contains n) → nxATs g₁ xs = nxATs g₂ xs
  | [], _ => rfl
  | a :: xs, h => by
    simp only [atNamesL, List.mem_append] at h
    simp only [nxATs, nxAT_agree a fun n hn => h n (.inl hn),
      nxATs_agree xs fun n hn => h n (.inr hn)]
end

/-- A predicate on abstract types closed under what conformance reads. -/
structure ShapeClosed (S : Sig) (g₂ : List String) (Q : AT → Prop) : Prop where
  names : ∀ a, Q a → ∀ n ∈ atNames a, S.good.contains n = g₂.contains n
  unf : ∀ a, Q a → Q (unf S a)
  iter : ∀ a, Q (.iter a) → Q a
  tup : ∀ xs, Q (.tup xs) → ∀ b ∈ xs, Q b
  field : ∀ n k, Q (fieldAT S n k)
  case : ∀ n k, Q (caseAT S n k)
  unk : Q .unk

theorem ShapeClosed.nx {S : Sig} {g₂ : List String} {Q : AT → Prop} (hQ : ShapeClosed S g₂ Q)
    {a : AT} (ha : Q a) : nxAT S.good a = nxAT g₂ a :=
  nxAT_agree a (hQ.names a ha)

mutual
theorem vtB_agree {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) {Q : AT → Prop}
    (hQ : ShapeClosed S₁ S₂.good Q) : ∀ (v : Value) (a : AT), Q a → vtB S₁ a v = vtB S₂ a v
  | .bool _, _, _ => by simp [vtB]
  | .num _, _, _ => by simp [vtB]
  | .text _, _, _ => by simp [vtB]
  | .opt none, _, _ => by simp [vtB]
  | .struct gs, a, ha => by
    have hu := hQ.unf a ha
    simp only [vtB, hQ.nx ha, ← unf_shape hs a]
    split
    · rfl
    · split
      · rename_i n xs hn
        exact vtF_agree hs hQ n gs
      · rfl
  | .case op w, a, ha => by
    have hu := hQ.unf a ha
    simp only [vtB, hQ.nx ha, ← unf_shape hs a]
    split
    · rfl
    · split
      · rename_i n xs hn
        rw [← caseAT_shape hs]
        exact vtB_agree hs hQ w _ (hQ.case n op)
      · rfl
  | .list vs, a, ha => by
    have hu := hQ.unf a ha
    simp only [vtB, hQ.nx ha, ← unf_shape hs a]
    split
    · rfl
    · split
      · rename_i b hb
        rw [hb] at hu
        exact vtL_agree hs hQ b (hQ.iter b hu) vs
      · rfl
  | .opt (some w), a, ha => by
    have hu := hQ.unf a ha
    simp only [vtB, hQ.nx ha, ← unf_shape hs a]
    split
    · rfl
    · split
      · rename_i b hb
        rw [hb] at hu
        exact vtB_agree hs hQ w b (hQ.iter b hu)
      · rfl
  | .tuple vs, a, ha => by
    have hu := hQ.unf a ha
    simp only [vtB, hQ.nx ha, ← unf_shape hs a]
    split
    · rfl
    · split
      · rename_i xs hx
        rw [hx] at hu
        exact vtT_agree hs hQ xs (hQ.tup xs hu) vs
      · rfl

theorem vtL_agree {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) {Q : AT → Prop}
    (hQ : ShapeClosed S₁ S₂.good Q) (b : AT) (hb : Q b) :
    ∀ vs : List Value, vtL S₁ b vs = vtL S₂ b vs
  | [] => rfl
  | v :: vs => by simp only [vtL, vtB_agree hs hQ v b hb, vtL_agree hs hQ b hb vs]

theorem vtF_agree {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) {Q : AT → Prop}
    (hQ : ShapeClosed S₁ S₂.good Q) (n : String) :
    ∀ gs : List (AtomS × Value), vtF S₁ n gs = vtF S₂ n gs
  | [] => rfl
  | (k, v) :: gs => by
    simp only [vtF]
    rw [vtB_agree hs hQ v _ (hQ.field n k), fieldAT_shape hs, vtF_agree hs hQ n gs]

theorem vtT_agree {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) {Q : AT → Prop}
    (hQ : ShapeClosed S₁ S₂.good Q) : ∀ (xs : List AT), (∀ b ∈ xs, Q b) →
    ∀ vs : List Value, vtT S₁ xs vs = vtT S₂ xs vs
  | _, _, [] => rfl
  | xs, hx, v :: vs => by
    have h1 : Q (xs.headD .unk) := by
      cases xs with
      | nil => exact hQ.unk
      | cons b _ => exact hx b (List.mem_cons_self ..)
    have h2 : ∀ b ∈ xs.tail, Q b := fun b hb => hx b (List.mem_of_mem_tail hb)
    simp only [vtT, vtB_agree hs hQ v _ h1, vtT_agree hs hQ xs.tail h2 vs]
end

/-! ## Equal `good` -/

theorem shapeClosed_true {S₁ S₂ : Sig} (hg : S₁.good = S₂.good) :
    ShapeClosed S₁ S₂.good (fun _ => True) where
  names := fun _ _ _ _ => by rw [hg]
  unf := fun _ _ => trivial
  iter := fun _ _ => trivial
  tup := fun _ _ _ _ => trivial
  field := fun _ _ => trivial
  case := fun _ _ => trivial
  unk := trivial

theorem vtB_eq_good {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) (hg : S₁.good = S₂.good) (a : AT)
    (v : Value) : vtB S₁ a v = vtB S₂ a v :=
  vtB_agree hs (shapeClosed_true hg) v a trivial

theorem trivK_eq_good {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) (hg : S₁.good = S₂.good) :
    ∀ k a, trivK S₁ k a = trivK S₂ k a
  | 0, _ => rfl
  | k + 1, a => by
    simp only [trivK, hg, unf_shape hs a, ← hs.fields, ← hs.cases, trivK_eq_good hs hg k]

theorem triv_eq_good {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) (hg : S₁.good = S₂.good) (a : AT) :
    triv S₁ a = triv S₂ a := trivK_eq_good hs hg 8 a

theorem atLe_eq_good {S₁ S₂ : Sig} (hs : SameShape S₁ S₂) (hg : S₁.good = S₂.good) :
    ∀ k a b, atLe S₁ k a b = atLe S₂ k a b
  | 0, a, b => by simp only [atLe, hg, triv_eq_good hs hg]
  | k + 1, a, b => by
    simp only [atLe, hg, triv_eq_good hs hg, unf_shape hs, atLe_eq_good hs hg k]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
