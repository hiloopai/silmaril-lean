module

public import Silmaril.Project.Shapes.Consequence.Thms
public import ProjectSelfTest.Consequence.Gentzen
public import ProjectSelfTest.Consequence.Multi
public import ProjectSelfTest.Consequence.Wasm
public import ProjectSelfTest.Consequence.Partial
public import ProjectSelfTest.Consequence.WasmSeq
public import ProjectSelfTest.Consequence.Structural

/-!
# The `sil project` self-test: consequence systems

A small, complete example of `silmaril consequence_system` and the standard shapes
`silmaril.shapes.consequence.*` (`docs/projects/consequence-systems.md`).

Sentences are four atoms `p`, `q`, `r` and a chosen `ff`; a context is a finite list
`C₁, …, Cₙ` of them. Two rules, `p ⇒ q` and `q ⇒ r`, give these systems:

* `raw` (`op := decl`): one rule applied to a one-element context, and nothing else. **No
  structural rule is implicit**: `p ⊢ p` does not hold in `raw`.
* `hyp` (`op := decl`): `Γ ⊢ φ` iff `φ ∈ Γ`.
* `raw_or_hyp` (`op := union` of the two).
* `derivable` (`op := erase` of the witness system `Deriv`): `Deriv Γ φ` is the *type* of
  derivations of `φ` from `Γ` (hypotheses and rule steps), and `derivable Γ φ` is
  `Nonempty (Deriv Γ φ)`.
* `entails` (`op := decl`, the target): every model of the rules that makes `Γ` true makes `φ`
  true, where a model never makes `ff` true.
* `gap` (`op := diff`, `entails \ derivable`) and `checked` (`op := inter`,
  `derivable ⊓ entails`).
* `empty` (`op := decl`): derives nothing.

The problems show each standard question with a proof: member judgments both ways,
soundness (THM) and incompleteness (CSA, with the counterexample `ff ⊢ p` kept) of
`derivable` for `entails`, the difference between a context that derives `ff`, a
context-universal context and a universal system, an empty system, and a translation that
preserves but does not reflect derivability.
-/

namespace ProjectSelfTest.Consequence

@[expose] public section

/-- The sentences: three atoms and a chosen `ff`. -/
inductive Atom where
  | p | q | r | ff
  deriving DecidableEq, Repr

/-- The rules `p ⇒ q` and `q ⇒ r` (a type, so that derivations can be computed with). -/
inductive Rule : Atom → Atom → Type where
  | pq : Rule .p .q
  | qr : Rule .q .r

/-- **Derivations**, a witness system: a hypothesis, or a rule applied to a derivation. -/
inductive Deriv : List Atom → Atom → Type where
  | hyp {Γ : List Atom} {φ : Atom} : φ ∈ Γ → Deriv Γ φ
  | step {Γ : List Atom} {a b : Atom} : Rule a b → Deriv Γ a → Deriv Γ b

/-- **The raw system**: one rule applied to a one-element context; no structural rule. -/
def raw (Γ : List Atom) (φ : Atom) : Prop := ∃ a, Γ = [a] ∧ Nonempty (Rule a φ)

/-- **Hypotheses**: `Γ ⊢ φ` iff `φ ∈ Γ`. -/
def hyp (Γ : List Atom) (φ : Atom) : Prop := φ ∈ Γ

/-- A model: a set of atoms closed under the rules that does not contain `ff`. -/
def Model (v : Atom → Prop) : Prop := ¬ v .ff ∧ ∀ a b, Rule a b → v a → v b

/-- **The target**: every model that makes `Γ` true makes `φ` true. -/
def entails (Γ : List Atom) (φ : Atom) : Prop := ∀ v, Model v → (∀ ψ ∈ Γ, v ψ) → v φ

/-- **The empty system.** -/
def empty (_ : List Atom) (_ : Atom) : Prop := False

/-- Shift every atom one rule forward (`p ↦ q ↦ r ↦ r`, `ff ↦ ff`). -/
def shift : Atom → Atom
  | .p => .q
  | .q => .r
  | .r => .r
  | .ff => .ff

/-- A derivation, shifted: a step by `q ⇒ r` becomes no step. -/
def Deriv.shift : {Γ : List Atom} → {φ : Atom} → Deriv Γ φ → Deriv (Γ.map Consequence.shift) (Consequence.shift φ)
  | _, _, .hyp h => .hyp (List.mem_map_of_mem h)
  | _, _, .step .pq d => .step .qr d.shift
  | _, _, .step .qr d => d.shift

/-- What a context derives stays in any rule-closed set of atoms that contains it. -/
theorem deriv_mem {U : Atom → Prop} (hU : ∀ a b, Rule a b → U a → U b) {Γ : List Atom}
    (hΓ : ∀ ψ ∈ Γ, U ψ) : {φ : Atom} → Deriv Γ φ → U φ
  | _, .hyp h => hΓ _ h
  | _, .step r d => hU _ _ r (deriv_mem hU hΓ d)

/-- No rule leaves `ff` or `r`. -/
theorem stuck {s : Atom} (hs : s = .ff ∨ s = .r) : ∀ a b, Rule a b → a = s → b = s := by
  intro a b r h; subst h; rcases hs with rfl | rfl <;> cases r

/-- `ff` alone derives only `ff`. -/
theorem deriv_ff {φ : Atom} (d : Deriv [.ff] φ) : φ = .ff :=
  deriv_mem (stuck (.inl rfl)) (fun _ h => List.mem_singleton.mp h) d

/-- `r` alone derives only `r`. -/
theorem deriv_r {φ : Atom} (d : Deriv [.r] φ) : φ = .r :=
  deriv_mem (stuck (.inr rfl)) (fun _ h => List.mem_singleton.mp h) d

/-- The empty context derives nothing. -/
theorem deriv_nil {φ : Atom} (d : Deriv [] φ) : False :=
  deriv_mem (U := fun _ => False) (fun _ _ _ h => h) (fun _ h => by cases h) d

/-- A derivation from `Γ` is one from any `Γ' ⊇ Γ`. -/
def Deriv.weaken {Γ Γ' : List Atom} (s : Γ ⊆ Γ') : {φ : Atom} → Deriv Γ φ → Deriv Γ' φ
  | _, .hyp h => .hyp (s h)
  | _, .step r d => .step r (d.weaken s)

/-- `ff` alone entails everything: no model makes `ff` true. -/
theorem entails_ff (φ : Atom) : entails [.ff] φ :=
  fun _ hv hΓ => absurd (hΓ _ (List.mem_singleton_self _)) hv.1

end

end ProjectSelfTest.Consequence

/-! ## Systems -/

silmaril consequence_system silmaril.selftest.consequence.raw := ProjectSelfTest.Consequence.raw
  (title := "One rule step from a one-element context (no structural rules)")
silmaril consequence_system silmaril.selftest.consequence.hyp := ProjectSelfTest.Consequence.hyp
  (title := "Hypotheses: φ ∈ Γ")
silmaril consequence_system silmaril.selftest.consequence.raw_or_hyp (op := union)
  (args := [silmaril.selftest.consequence.raw, silmaril.selftest.consequence.hyp])
  (title := "A rule step or a hypothesis")
silmaril consequence_system silmaril.selftest.consequence.derivable :=
  ProjectSelfTest.Consequence.Deriv (op := erase)
  (title := "Derivable: some derivation from hypotheses by the rules")
silmaril consequence_system silmaril.selftest.consequence.entails :=
  ProjectSelfTest.Consequence.entails (title := "Semantic consequence over the models of the rules")
silmaril consequence_system silmaril.selftest.consequence.gap (op := diff)
  (args := [silmaril.selftest.consequence.entails, silmaril.selftest.consequence.derivable])
  (title := "Entailed but not derivable")
silmaril consequence_system silmaril.selftest.consequence.checked (op := inter)
  (args := [silmaril.selftest.consequence.derivable, silmaril.selftest.consequence.entails])
  (title := "Derivable and entailed")
silmaril consequence_system silmaril.selftest.consequence.empty := ProjectSelfTest.Consequence.empty
  (title := "The empty system")

/-! ## Problems -/

open ProjectSelfTest.Consequence Silmaril.Project.Shapes.Consequence in
section

-- member judgments, closed: `p ⊢ r` by two steps; `r ⊢ p` fails (a closed refutation, stored
-- as UNS: the statement is false)
silmaril instance silmaril.selftest.consequence.p_derives_r (expect := THM)
  (title := "p ⊢ r (derivable)") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.derivable) (Γ := [ProjectSelfTest.Consequence.Atom.p])
  (φ := ProjectSelfTest.Consequence.Atom.r)

@[answers "silmaril.selftest.consequence.p_derives_r" thm]
public theorem p_derives_r : Derives silmaril.selftest.consequence.derivable [.p] .r :=
  ⟨.step .qr (.step .pq (.hyp (List.mem_singleton_self _)))⟩

silmaril instance silmaril.selftest.consequence.r_derives_p (expect := UNS)
  (title := "r ⊢ p (fails)") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.derivable) (Γ := [ProjectSelfTest.Consequence.Atom.r])
  (φ := ProjectSelfTest.Consequence.Atom.p)

@[answers "silmaril.selftest.consequence.r_derives_p" csa]
public theorem r_derives_p : ¬ Derives silmaril.selftest.consequence.derivable [.r] .p :=
  fun ⟨d⟩ => Atom.noConfusion (deriv_r d)

-- no structural rule is implicit: `raw` is not reflexive
silmaril instance silmaril.selftest.consequence.raw_p_p (expect := UNS)
  (title := "p ⊢ p in the raw system (fails: no reflexivity)") := silmaril.shapes.consequence.derives
  (S := ProjectSelfTest.Consequence.raw) (Γ := [ProjectSelfTest.Consequence.Atom.p])
  (φ := ProjectSelfTest.Consequence.Atom.p)

@[answers "silmaril.selftest.consequence.raw_p_p" csa]
public theorem raw_p_p : ¬ Derives ProjectSelfTest.Consequence.raw [.p] .p :=
  fun ⟨a, h, ⟨r⟩⟩ => by cases List.singleton_inj.mp h; cases r

-- soundness of derivations for the target, and of the raw system for derivations
silmaril instance silmaril.selftest.consequence.derivable_sound (expect := THM)
  (title := "Derivable is sound for entails") := silmaril.shapes.consequence.sound_at
  (S := silmaril.selftest.consequence.derivable) (T := ProjectSelfTest.Consequence.entails)

@[answers "silmaril.selftest.consequence.derivable_sound" thm]
public theorem derivable_sound :
    ∀ Γ φ, SoundAt silmaril.selftest.consequence.derivable entails Γ φ :=
  fun _ _ ⟨d⟩ _ hv hΓ => deriv_mem hv.2 hΓ d

silmaril instance silmaril.selftest.consequence.raw_sound (expect := THM)
  (title := "The raw system is sound for derivable") := silmaril.shapes.consequence.sound_at
  (S := ProjectSelfTest.Consequence.raw) (T := silmaril.selftest.consequence.derivable)

@[answers "silmaril.selftest.consequence.raw_sound" thm]
public theorem raw_sound :
    ∀ Γ φ, SoundAt ProjectSelfTest.Consequence.raw silmaril.selftest.consequence.derivable Γ φ :=
  fun _ _ ⟨_, h, ⟨r⟩⟩ => h ▸ ⟨.step r (.hyp (List.mem_singleton_self _))⟩

-- incompleteness, with the counterexample kept: `ff ⊢ p` is entailed, not derivable
silmaril instance silmaril.selftest.consequence.derivable_complete (expect := CSA)
  (title := "Derivable is complete for entails (fails: ff ⊢ p)") :=
  silmaril.shapes.consequence.complete_at
  (S := silmaril.selftest.consequence.derivable) (T := ProjectSelfTest.Consequence.entails)

@[answers "silmaril.selftest.consequence.derivable_complete" csa]
public theorem derivable_complete :
    ∃ Γ φ, ¬ CompleteAt silmaril.selftest.consequence.derivable entails Γ φ :=
  ⟨[.ff], .p, fun h => let ⟨d⟩ := h (entails_ff .p); Atom.noConfusion (deriv_ff d)⟩

-- one step does not chain: `raw_or_hyp` is not complete for `derivable` (`p ⊢ r`)
silmaril instance silmaril.selftest.consequence.raw_or_hyp_complete (expect := CSA)
  (title := "A rule step or a hypothesis is complete for derivable (fails: p ⊢ r)") :=
  silmaril.shapes.consequence.complete_at
  (S := silmaril.selftest.consequence.raw_or_hyp) (T := silmaril.selftest.consequence.derivable)

@[answers "silmaril.selftest.consequence.raw_or_hyp_complete" csa]
public theorem raw_or_hyp_complete : ∃ Γ φ,
    ¬ CompleteAt silmaril.selftest.consequence.raw_or_hyp silmaril.selftest.consequence.derivable Γ φ :=
  ⟨[.p], .r, fun h => (h p_derives_r).elim
    (fun ⟨_, e, ⟨r⟩⟩ => by cases List.singleton_inj.mp e; cases r)
    (fun m => Atom.noConfusion (List.mem_singleton.mp m))⟩

-- three properties, not one "inconsistency"
silmaril instance silmaril.selftest.consequence.entails_ff_universal (expect := THM)
  (title := "ff derives every conclusion in entails (context-universal)") :=
  silmaril.shapes.consequence.context_universal
  (S := ProjectSelfTest.Consequence.entails) (Γ := [ProjectSelfTest.Consequence.Atom.ff])

@[answers "silmaril.selftest.consequence.entails_ff_universal" thm]
public theorem entails_ff_universal : ContextUniversal entails [.ff] := entails_ff

silmaril instance silmaril.selftest.consequence.derivable_ff_universal (expect := UNS)
  (title := "ff derives every conclusion in derivable (fails: ff derives ff, not p)") :=
  silmaril.shapes.consequence.context_universal
  (S := silmaril.selftest.consequence.derivable) (Γ := [ProjectSelfTest.Consequence.Atom.ff])

@[answers "silmaril.selftest.consequence.derivable_ff_universal" csa]
public theorem derivable_ff_universal :
    ¬ ContextUniversal silmaril.selftest.consequence.derivable [.ff] :=
  fun h => let ⟨d⟩ := h .p; Atom.noConfusion (deriv_ff d)

silmaril instance silmaril.selftest.consequence.derivable_derives_ff (expect := contingent)
  (title := "A context derives ff (some do, some do not)") :=
  silmaril.shapes.consequence.derives_bottom
  (S := silmaril.selftest.consequence.derivable) (ff := ProjectSelfTest.Consequence.Atom.ff)

@[answers "silmaril.selftest.consequence.derivable_derives_ff" sat]
public theorem derivable_derives_ff_sat :
    ∃ Γ, DerivesBottom silmaril.selftest.consequence.derivable .ff Γ :=
  ⟨[.ff], ⟨.hyp (List.mem_singleton_self _)⟩⟩

@[answers "silmaril.selftest.consequence.derivable_derives_ff" csa]
public theorem derivable_derives_ff_csa :
    ∃ Γ, ¬ DerivesBottom silmaril.selftest.consequence.derivable .ff Γ :=
  ⟨[], fun ⟨d⟩ => deriv_nil d⟩

silmaril instance silmaril.selftest.consequence.derivable_universal (expect := contingent)
  (title := "Every context derives every conclusion (derivable: no, but it derives something)") :=
  silmaril.shapes.consequence.derives (S := silmaril.selftest.consequence.derivable)

@[answers "silmaril.selftest.consequence.derivable_universal" sat]
public theorem derivable_universal_sat :
    ∃ Γ φ, Derives silmaril.selftest.consequence.derivable Γ φ :=
  ⟨[.p], .p, ⟨.hyp (List.mem_singleton_self _)⟩⟩

@[answers "silmaril.selftest.consequence.derivable_universal" csa]
public theorem derivable_universal_csa :
    ∃ Γ φ, ¬ Derives silmaril.selftest.consequence.derivable Γ φ :=
  ⟨[], .p, fun ⟨d⟩ => deriv_nil d⟩

-- the empty system, and the gap between the target and derivations
silmaril instance silmaril.selftest.consequence.empty_derives (expect := UNS)
  (title := "The empty system derives nothing") :=
  silmaril.shapes.consequence.derives (S := ProjectSelfTest.Consequence.empty)

@[answers "silmaril.selftest.consequence.empty_derives" uns]
public theorem empty_derives : ∀ Γ φ, ¬ Derives ProjectSelfTest.Consequence.empty Γ φ :=
  fun _ _ h => h

silmaril instance silmaril.selftest.consequence.gap_nonempty (expect := SAT)
  (title := "Something is entailed but not derivable") :=
  silmaril.shapes.consequence.derives (S := silmaril.selftest.consequence.gap)

@[answers "silmaril.selftest.consequence.gap_nonempty" sat]
public theorem gap_nonempty : ∃ Γ φ, Derives silmaril.selftest.consequence.gap Γ φ :=
  ⟨[.ff], .p, entails_ff .p, fun ⟨d⟩ => Atom.noConfusion (deriv_ff d)⟩

silmaril instance silmaril.selftest.consequence.checked_complete (expect := THM)
  (title := "Derivable and entailed is complete for derivable (by soundness)") :=
  silmaril.shapes.consequence.complete_at
  (S := silmaril.selftest.consequence.checked) (T := silmaril.selftest.consequence.derivable)

@[answers "silmaril.selftest.consequence.checked_complete" thm]
public theorem checked_complete : ∀ Γ φ,
    CompleteAt silmaril.selftest.consequence.checked silmaril.selftest.consequence.derivable Γ φ :=
  fun Γ φ h => ⟨h, derivable_sound Γ φ h⟩

-- a translation that preserves derivability but does not reflect it (`r ⊢ q`)
silmaril instance silmaril.selftest.consequence.shift_preserves (expect := THM)
  (title := "Shifting atoms preserves derivability") := silmaril.shapes.consequence.translates_at
  (S := silmaril.selftest.consequence.derivable) (T := silmaril.selftest.consequence.derivable)
  (f := List.map ProjectSelfTest.Consequence.shift) (g := ProjectSelfTest.Consequence.shift)

@[answers "silmaril.selftest.consequence.shift_preserves" thm]
public theorem shift_preserves : ∀ Γ φ, TranslatesAt silmaril.selftest.consequence.derivable
    silmaril.selftest.consequence.derivable (List.map shift) shift Γ φ :=
  fun _ _ ⟨d⟩ => ⟨d.shift⟩

silmaril instance silmaril.selftest.consequence.shift_reflects (expect := CSA)
  (title := "Shifting atoms reflects derivability (fails: r ⊢ q)") :=
  silmaril.shapes.consequence.reflects_at
  (S := silmaril.selftest.consequence.derivable) (T := silmaril.selftest.consequence.derivable)
  (f := List.map ProjectSelfTest.Consequence.shift) (g := ProjectSelfTest.Consequence.shift)

@[answers "silmaril.selftest.consequence.shift_reflects" csa]
public theorem shift_reflects : ∃ Γ φ, ¬ ReflectsAt silmaril.selftest.consequence.derivable
    silmaril.selftest.consequence.derivable (List.map shift) shift Γ φ :=
  ⟨[.r], .q, fun h => let ⟨d⟩ := h ⟨.hyp (List.mem_singleton_self _)⟩; Atom.noConfusion (deriv_r d)⟩

end

-- shape evidence: the raw system is permutation-invariant but not weakening-closed; derivations are both
silmaril instance silmaril.selftest.consequence.raw_perm_inv (expect := THM)
  (title := "raw: contexts may be permuted") := silmaril.shapes.consequence.ctx_perm_inv
  (S := ProjectSelfTest.Consequence.raw)

@[answers "silmaril.selftest.consequence.raw_perm_inv" thm]
public theorem raw_perm_inv : Silmaril.Project.Shapes.Consequence.CtxPermInv ProjectSelfTest.Consequence.raw := by
  intro c l l' hp
  constructor
  · rintro ⟨a, rfl, r⟩; exact ⟨a, List.perm_singleton.mp hp.symm, r⟩
  · rintro ⟨a, rfl, r⟩; exact ⟨a, List.perm_singleton.mp hp, r⟩

silmaril instance silmaril.selftest.consequence.raw_up_closed (expect := UNS)
  (title := "raw: contexts may be weakened (fails: p ⊢ q but not p, p ⊢ q)") :=
  silmaril.shapes.consequence.ctx_up_closed (S := ProjectSelfTest.Consequence.raw)

@[answers "silmaril.selftest.consequence.raw_up_closed" csa]
public theorem raw_up_closed : ¬ Silmaril.Project.Shapes.Consequence.CtxUpClosed ProjectSelfTest.Consequence.raw := fun h => by
  obtain ⟨a, he, -⟩ := h .q [.p] [.p, .p] (fun x hx => by simp_all) ⟨.p, rfl, ⟨.pq⟩⟩
  simp at he

silmaril instance silmaril.selftest.consequence.derivable_up_closed (expect := THM)
  (title := "derivable: contexts may be weakened (⊆)") := silmaril.shapes.consequence.ctx_up_closed
  (S := silmaril.selftest.consequence.derivable)

@[answers "silmaril.selftest.consequence.derivable_up_closed" thm]
public theorem derivable_up_closed : Silmaril.Project.Shapes.Consequence.CtxUpClosed silmaril.selftest.consequence.derivable :=
  fun _ _ _ s ⟨d⟩ => ⟨ProjectSelfTest.Consequence.Deriv.weaken s d⟩

silmaril instance silmaril.selftest.consequence.derivable_set_inv (expect := THM)
  (title := "derivable: contexts are read as sets") := silmaril.shapes.consequence.ctx_set_inv
  (S := silmaril.selftest.consequence.derivable)

@[answers "silmaril.selftest.consequence.derivable_set_inv" thm]
public theorem derivable_set_inv : Silmaril.Project.Shapes.Consequence.CtxSetInv silmaril.selftest.consequence.derivable :=
  fun c l l' h => ⟨derivable_up_closed c l l' (fun x hx => (h x).1 hx),
    derivable_up_closed c l' l (fun x hx => (h x).2 hx)⟩

silmaril group silmaril.shapes.consequence (title := "The standard consequence shapes")
  (children := [silmaril.shapes.consequence.derives, silmaril.shapes.consequence.context_universal,
    silmaril.shapes.consequence.derives_bottom, silmaril.shapes.consequence.sound_at,
    silmaril.shapes.consequence.complete_at, silmaril.shapes.consequence.translates_at,
    silmaril.shapes.consequence.reflects_at, silmaril.shapes.consequence.complete_within_at,
    silmaril.shapes.consequence.gentzen_closed, silmaril.shapes.consequence.artifact_defined,
    silmaril.shapes.consequence.context_free, silmaril.shapes.consequence.conclusion_free,
    silmaril.shapes.consequence.supported_ax, silmaril.shapes.consequence.supported_c,
    silmaril.shapes.consequence.ctx_perm_inv, silmaril.shapes.consequence.ctx_set_inv,
    silmaril.shapes.consequence.ctx_up_closed, silmaril.shapes.consequence.ctx_append_extensive,
    silmaril.shapes.consequence.tarski_closed])

silmaril group silmaril.selftest.consequence (title := "Consequence systems")
  (children := [silmaril.selftest.consequence.p_derives_r,
    silmaril.selftest.consequence.r_derives_p, silmaril.selftest.consequence.raw_p_p,
    silmaril.selftest.consequence.derivable_sound, silmaril.selftest.consequence.raw_sound,
    silmaril.selftest.consequence.derivable_complete,
    silmaril.selftest.consequence.raw_or_hyp_complete,
    silmaril.selftest.consequence.entails_ff_universal,
    silmaril.selftest.consequence.derivable_ff_universal,
    silmaril.selftest.consequence.derivable_derives_ff,
    silmaril.selftest.consequence.derivable_universal, silmaril.selftest.consequence.empty_derives,
    silmaril.selftest.consequence.gap_nonempty, silmaril.selftest.consequence.checked_complete,
    silmaril.selftest.consequence.shift_preserves, silmaril.selftest.consequence.shift_reflects,
    silmaril.selftest.consequence.raw_perm_inv, silmaril.selftest.consequence.raw_up_closed,
    silmaril.selftest.consequence.derivable_up_closed, silmaril.selftest.consequence.derivable_set_inv,
    silmaril.shapes.consequence, silmaril.selftest.consequence.gentzen,
    silmaril.selftest.consequence.multi, silmaril.selftest.consequence.wasm,
    silmaril.selftest.consequence.partial, silmaril.selftest.consequence.wasm_seq,
    silmaril.selftest.consequence.structural])
