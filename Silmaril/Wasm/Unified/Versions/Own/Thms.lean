module

public import Silmaril.Wasm.Unified.Versions.Own.Defs
public import Silmaril.Wasm.Unified.Versions.Run.Thms
public import Silmaril.Wasm.Unified.Core30Faithful.Thms

/-!
# Own syntaxes as opcode algebras: the meaning is the preimage of Core's

* `forall₂_unique`, `Syn.tr_unique`: translation of own code is functional.
* **`mem_evalCode`**: for a coherent own syntax, the own meaning of code is the set of own
  programs translating to a Core 3.0 meaning of the code (`mem_evalInstr`, `forall₂_evalBlocks`
  for instructions and blocks); `evalOwn_encCode`: at an encoded Core program, the own programs
  translating to it.
* **`refines_model30`**: if every own program, validated, translates to a Core-validated program
  whose Core behaviours contain the own ones (a code-level simulation, `CodeSim`), the own model
  refines `model30`; `refines_reduct`: hence on every version signature, the own model's reduct
  refines the reduct of `model30`.
* **`not_refines_own`** (the converse fails): an encoded Core program that no own program
  translates to has no own observations, so a Core observation of it refutes the converse
  refinement (and the equation of observations).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)
open CategoryTheory

variable {L : Syn}

/-- `Forall₂` of a functional relation is functional. -/
theorem forall₂_unique {α β : Type} {R : α → β → Prop} (hR : ∀ a b b', R a b → R a b' → b = b') :
    {l : List α} → {l₁ l₂ : List β} → List.Forall₂ R l l₁ → List.Forall₂ R l l₂ → l₁ = l₂
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [hR _ _ _ h₁ h₂, forall₂_unique hR t₁ t₂]

/-- Translation of own code is functional. -/
theorem Syn.tr_unique {js : List L.J} {is is' : List Instr} (h : L.Tr js is) (h' : L.Tr js is') :
    is = is' :=
  forall₂_unique (fun _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂)) h h'

/-- Translation of blocks is functional. -/
theorem Syn.trs_unique {bs : List (List L.J)} {bs₁ bs₂ : List (List Instr)}
    (h₁ : List.Forall₂ L.Tr bs bs₁) (h₂ : List.Forall₂ L.Tr bs bs₂) : bs₁ = bs₂ :=
  forall₂_unique (R := L.Tr) (fun _ _ _ h h' => Syn.tr_unique h h') h₁ h₂

/-- The own meaning of an instruction, as a set. -/
abbrev evalOwnI (L : Syn) (u : UInstr sig30.Op) : Set L.J := (ownAlg L).evalInstr u

/-- The own meanings of blocks, as sets. -/
abbrev ownBlocks (L : Syn) (bs : List (UCode sig30.Op)) : List (Set (List L.J)) :=
  (ownAlg L).evalBlocks bs

/-- The Core 3.0 meanings of blocks, as sets. -/
abbrev blocks30 (bs : List (UCode sig30.Op)) : List (Set (List Instr)) := alg30.evalBlocks bs

theorem mem_nil_iff (js : List L.J) :
    js ∈ ({[]} : Set (List L.J)) ↔ ∃ is ∈ ({[]} : Set (List Instr)), L.Tr js is := by
  refine ⟨fun h => ⟨[], rfl, (Set.mem_singleton_iff.1 h) ▸ .nil⟩, ?_⟩
  rintro ⟨is, his, h⟩
  rw [Set.mem_singleton_iff.1 his] at h
  cases h
  rfl

mutual
/-- The own meaning of an instruction: own instructions translating to a Core meaning. -/
theorem mem_evalInstr (hc : L.Coh) :
    (u : UInstr sig30.Op) → ∀ j, j ∈ evalOwnI L u ↔ ∃ i ∈ evalI30 u, L.tr j = some i
  | .op o imms bs hs => fun j => by
    have hb := forall₂_evalBlocks hc bs (L.bod j)
    simp only [evalOwnI, evalI30, Alg.evalInstr]
    constructor
    · rintro ⟨i, hi, hh, him, hhd, hB⟩
      obtain ⟨bsI, hI, hT⟩ := hb.1 hB
      rw [Syn.trs_unique hT (hc j i hi)] at hI
      exact ⟨i, ⟨hh, him, hhd, hI⟩, hi⟩
    · rintro ⟨i, ⟨hh, him, hhd, hI⟩, hi⟩
      exact ⟨i, hi, hh, him, hhd, hb.2 ⟨_, hI, hc j i hi⟩⟩
/-- **The own meaning of code is the preimage of the Core meaning.** -/
theorem mem_evalCode (hc : L.Coh) :
    (c : UCode sig30.Op) → ∀ js, js ∈ evalOwn L c ↔ ∃ is ∈ evalC30 c, L.Tr js is
  | [] => fun js => mem_nil_iff js
  | u :: c => fun js => by
    simp only [evalOwn, evalC30, Alg.evalCode]
    constructor
    · rintro ⟨j, t, rfl, hj, ht⟩
      obtain ⟨i, hi, hji⟩ := (mem_evalInstr hc u j).1 hj
      obtain ⟨is, his, ht'⟩ := (mem_evalCode hc c t).1 ht
      exact ⟨i :: is, ⟨i, is, rfl, hi, his⟩, .cons hji ht'⟩
    · rintro ⟨_, ⟨i, is, rfl, hi, his⟩, h⟩
      obtain ⟨j, t, hji, ht, rfl⟩ := List.forall₂_cons_right_iff.1 h
      exact ⟨_, _, rfl, (mem_evalInstr hc u _).2 ⟨i, hi, hji⟩,
        (mem_evalCode hc c _).2 ⟨is, his, ht⟩⟩
/-- Blocks: pointwise. -/
theorem forall₂_evalBlocks (hc : L.Coh) :
    (bs : List (UCode sig30.Op)) → ∀ bsJ : List (List L.J),
      List.Forall₂ (· ∈ ·) bsJ (ownBlocks L bs) ↔
        ∃ bsI, List.Forall₂ (· ∈ ·) bsI (blocks30 bs) ∧ List.Forall₂ L.Tr bsJ bsI
  | [] => fun bsJ => by
    simp only [ownBlocks, blocks30, Alg.evalBlocks]
    constructor
    · intro h
      cases h
      exact ⟨[], .nil, .nil⟩
    · rintro ⟨_, hI, hT⟩
      cases hI
      cases hT
      exact .nil
  | b :: bs => fun bsJ => by
    simp only [ownBlocks, blocks30, Alg.evalBlocks]
    constructor
    · intro h
      obtain ⟨bJ, bsJ', hb, hbs, rfl⟩ := List.forall₂_cons_right_iff.1 h
      obtain ⟨is, his, ht⟩ := (mem_evalCode hc b bJ).1 hb
      obtain ⟨bsI, hI, hT⟩ := (forall₂_evalBlocks hc bs bsJ').1 hbs
      exact ⟨is :: bsI, .cons his hI, .cons ht hT⟩
    · rintro ⟨_, hI, hT⟩
      obtain ⟨is, bsI, his, hI', rfl⟩ := List.forall₂_cons_right_iff.1 hI
      obtain ⟨bJ, bsJ', ht, hT', rfl⟩ := List.forall₂_cons_right_iff.1 hT
      exact .cons ((mem_evalCode hc b bJ).2 ⟨is, his, ht⟩)
        ((forall₂_evalBlocks hc bs bsJ').2 ⟨bsI, hI', hT'⟩)
end

/-- At an encoded Core program, the own meaning is the own programs translating to it. -/
theorem evalOwn_encCode (hc : L.Coh) (is : List Instr) :
    evalOwn L (encCode is) = {js | L.Tr js is} := by
  ext js
  rw [mem_evalCode hc, evalC30_encCode]
  simp

/-- **A code-level simulation** of an own semantics in Core 3.0: every validated own program
translates to a Core-validated program whose Core behaviours contain the own ones. -/
def CodeSim (L : Syn) (okJ : List L.J → Prop) (beh : List L.J → UIn → Set UObs) (P : Profile)
    {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame) (okc : List Instr → Prop) :
    Prop :=
  ∀ js is, L.Tr js is → okJ js → okc is ∧ ∀ vs, beh js vs ⊆ behCode P host s f is vs

/-- **The own model refines Core 3.0** under a code-level simulation. -/
theorem refines_model30 (hc : L.Coh) {okJ : List L.J → Prop} {beh : List L.J → UIn → Set UObs}
    {P : Profile} {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {okc : List Instr → Prop} (hs : CodeSim L okJ beh P host s f okc) :
    Refines (ownModel L okJ beh) (model30 P host s f okc) := by
  rintro ⟨c, vs⟩ b ⟨-, js, hjs, hok, hb⟩
  obtain ⟨is, his, htr⟩ := (mem_evalCode hc c js).1 hjs
  obtain ⟨hokc, hsub⟩ := hs js is htr hok
  exact ⟨⟨is, his, hokc⟩, is, his, hokc, hsub vs hb⟩

/-- On every version signature: the reducts. -/
theorem refines_reduct (hc : L.Coh) {okJ : List L.J → Prop} {beh : List L.J → UIn → Set UObs}
    {P : Profile} {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {okc : List Instr → Prop} (hs : CodeSim L okJ beh P host s f okc) {K : FSig}
    (σ : K ⟶ sig30) :
    Refines ((ownModel L okJ beh).reduct σ) ((model30 P host s f okc).reduct σ) :=
  (refines_model30 hc hs).reduct σ

/-- An encoded Core program no own program translates to has no own observations. -/
theorem obs_encCode_empty (hc : L.Coh) {okJ : List L.J → Prop}
    {beh : List L.J → UIn → Set UObs} {is : List Instr} (h : ∀ js, ¬ L.Tr js is) (vs : UIn) :
    (ownModel L okJ beh).obs (encCode is, vs) = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, js, hjs, -⟩
  have hjs' : js ∈ evalOwn L (encCode is) := hjs
  rw [evalOwn_encCode hc] at hjs'
  exact h js hjs'

/-- **The converse refinement fails** at a validated Core program with a behaviour that no own
program translates to. -/
theorem not_refines_own (hc : L.Coh) {okJ : List L.J → Prop}
    {beh : List L.J → UIn → Set UObs} {P : Profile} {H : Type} {host : HostSemantics H}
    {s : Store H} {f : Frame} {okc : List Instr → Prop} {is : List Instr}
    (h : ∀ js, ¬ L.Tr js is) (hok : okc is) {vs : UIn} {b : UObs}
    (hb : b ∈ behCode P host s f is vs) :
    ¬ Refines (model30 P host s f okc) (ownModel L okJ beh) := fun hr => by
  have hm := hr (encCode is, vs) ((obs_encCode P host s f okc is vs).symm ▸ ⟨hok, hb⟩ :
    b ∈ (model30 P host s f okc).obs (encCode is, vs))
  rw [obs_encCode_empty hc h vs] at hm
  exact hm

end Silmaril.Wasm.Unified.Versions.Own
