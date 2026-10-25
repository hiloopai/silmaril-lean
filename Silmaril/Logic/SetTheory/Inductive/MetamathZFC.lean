module

public import Silmaril.Logic.SetTheory.Inductive.MetamathZF
public import Silmaril.Logic.SetTheory.Inductive.MetamathHilbert
public import Silmaril.Logic.SetTheory.Inductive.MetamathSchemas
public import Silmaril.Logic.Metamath.Peano.ZFCSound
public import Silmaril.Logic.SetTheory.Inductive.ZFC

@[expose] public section

/-!
# Exact choice syntax and native proof certificates

The independent named and scoped choice trees encode to the actual native
`axAc` conclusion. The schema includes exactly its seven-variable syntactic
disjointness requirement. Native certificates below use the real Metamath
application rule for axioms, with sorted substitutions and checked disjointness.
The bidirectional common fragment contains the ten set-theoretic schemata
and four propositional assertions. Its named grammar uses `cv` of set
variables as class expressions. Extending the correspondence to the full
predicate/equality calculus and larger class syntax requires definition
elimination, sort preservation, binder freshness, translated defining axioms
and derivation reflection.
-/

namespace Silmaril.Logic.SetTheory.Inductive.MetamathZFC

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion
open MetamathZF

/-- A finite named presentation of precisely set.mm's ax-ac schema. -/
def namedChoice {V : Type*} (x y z w v u t : V) : Named.Formula V :=
  .ex y (.all z (.all w (.imp (.conj (.mem z w) (.mem w x))
    (.ex v (.all u (.iff
      (.ex t (.conj (.conj (.mem u w) (.mem w t)) (.conj (.mem u t) (.mem t y))))
      (.eq u v)))))))

/-- All variable names in an ax-ac instance must be syntactically distinct. -/
inductive ChoiceSchema {V : Type*} : Named.Formula V → Prop
  | ac (x y z w v u t : V) (distinct : [x, y, z, w, v, u, t].Nodup) :
      ChoiceSchema (namedChoice x y z w v u t)

/-- Canonical choice schema at the native variable names. -/
def canonicalChoice : Named.Formula Native.V :=
  namedChoice .x .y .z .w .v .u .t

theorem canonicalChoice_schema : ChoiceSchema canonicalChoice :=
  .ac _ _ _ _ _ _ _ (by decide)

/-- Schema truth is inherited from precisely the matching semantic ZFC axiom. -/
theorem choiceSchema_sound {M V : Type*} [Membership M M] [DecidableEq V]
    (hZFC : SetTheory.ZFC M V) {p : Named.Formula V} (hp : ChoiceSchema p) :
    ∀ E : V → M, p.eval E := by
  cases hp with
  | ac x y z w v u t h => exact hZFC.ac x y z w v u t h

/-- Choice binders in exactly the order prescribed by ax-ac. -/
def choiceNames : Nat → Native.V
  | 0 => .y | 1 => .z | 2 => .w | 3 => .v | 4 => .u | 5 => .t
  | n + 6 => .var n

/-- The independently written named tree is the actual native ax-ac tree. -/
theorem encode_canonicalChoice : encode canonicalChoice = Peano.ZF.axAc.concl.tree := rfl

/-- The de Bruijn presentation names back to the independently written named tree. -/
theorem name_choiceBody :
    name ZFC.choiceBody (fun _ => .x) choiceNames = canonicalChoice := rfl

/-- Exact native syntax agreement, including binder order and unordered-pair memberships. -/
theorem encode_choiceBody :
    encodeScoped ZFC.choiceBody (fun _ => .x) choiceNames = Peano.ZF.axAc.concl.tree := rfl

/-- Lowering forgets bound names and produces the original choice variable instance. -/
theorem lower_canonicalChoice {n : Nat} (ρ : Native.V → Fin n) :
    canonicalChoice.lower ρ = ZFC.choice (ρ .x) := rfl

/-- Disjointness makes every named schema instance lower to the same scoped axiom. -/
theorem lower_namedChoice {V : Type*} [DecidableEq V] {n : Nat}
    (x y z w v u t : V) (h : [x, y, z, w, v, u, t].Nodup) (ρ : V → Fin n) :
    (namedChoice x y z w v u t).lower ρ = ZFC.choice (ρ x) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at h
  simp_all [namedChoice, Named.Formula.lower, Named.Formula.bindNames,
    ZFC.choice, ZFC.choiceBody, Formula.subst, Formula.lift]
  repeat first | apply And.intro | rfl

/-- All renamed native choice leaves have an independent natural-deduction proof. -/
theorem choiceSchemaToSimple_nonempty (Base : Classical.AxiomFamily) {V : Type*}
    [DecidableEq V] {n : Nat}
    (ρ : V → Fin n) (Γ : List (Formula n)) {p : Named.Formula V}
    (hp : ChoiceSchema p) : Nonempty (Classical.Derivation (ZFC.extend Base) Γ (p.lower ρ)) := by
  cases hp with
  | ac a b c d e f g h =>
    rw [lower_namedChoice a b c d e f g h ρ]
    exact ⟨ZFC.choiceInstanceProof Base Γ (ρ a)⟩

/-- Select an actual independent inference object for a renamed native choice leaf. -/
noncomputable def choiceSchemaToSimple (Base : Classical.AxiomFamily) {V : Type*}
    [DecidableEq V] {n : Nat}
    (ρ : V → Fin n) (Γ : List (Formula n)) {p : Named.Formula V}
    (hp : ChoiceSchema p) : Classical.Derivation (ZFC.extend Base) Γ (p.lower ρ) :=
  _root_.Classical.choice (choiceSchemaToSimple_nonempty Base ρ Γ hp)

/-- The native partial decoder recognizes exactly the independent choice formula. -/
theorem decode_choice : decode Peano.ZF.axAc.concl.tree = some canonicalChoice :=
  decode_encode canonicalChoice

/-- Native Tarski meaning agrees with the membership-only choice assertion. -/
theorem sem_nativeChoice {M : Type*} [Membership M M] (E : Native.V → M) :
    Peano.ZF.sem id Peano.ZF.axAc.concl.tree E ↔ Choice.AxAC (E .x) := by
  rw [← encode_canonicalChoice, sem_encode]
  rfl

/-- Reading the native choice axiom gives an actual proof in the independent extension. -/
def simpleChoiceProof (Base : Classical.AxiomFamily) {n : Nat}
    (ρ : Native.V → Fin n) (Γ : List (Formula n)) :
    Classical.Derivation (ZFC.extend Base) Γ (canonicalChoice.lower ρ) := by
  rw [lower_canonicalChoice]
  exact ZFC.choiceInstanceProof Base Γ (ρ .x)

/-- Apply the exact native choice assertion in any frame carrying its syntax and DV data. -/
def nativeChoiceInFrame (A : TAssertion Native.L Native.C Native.V)
    (hctx : ∀ a s, Peano.ZF.axAc.ctx a s → A.ctx a s)
    (hdv : Peano.ZF.axAc.dv ⊆ A.dv) :
    TDerivation Native.grammar Peano.ZF.ZFC A Peano.ZF.axAc.concl := by
  have wf : Peano.ZF.axAc.WellFormed Native.grammar := .of_checkWF (by decide)
  have d := TDerivation.app (G := Native.grammar) (Γ := Peano.ZF.ZFC)
    (A := A) Peano.ZF.axAc
    (Peano.ZF.mem_ZFC.2 (by simp [Peano.ZF.axiomList])) Tree.var
    (fun a s h => .var (hctx a s h))
    (fun e h => by simp [Peano.ZF.axAc, essentials] at h)
    (fun c d hcd a ha b hb => by
      simp at ha hb
      subst a b
      exact ⟨wf.dv_irrefl c d hcd, Or.inl (hdv hcd)⟩)
  simpa using d

/-- Rename the seven mandatory set variables of ax-ac. -/
def choiceSubst (a b c d e f g : Native.V) : Native.V → Tree Native.L Native.V
  | .x => .var a | .y => .var b | .z => .var c | .w => .var d
  | .v => .var e | .u => .var f | .t => .var g
  | i => .var i

/-- A frame declaring all distinct set names disjoint satisfies the source ax-ac DV checks. -/
theorem choiceSubst_dvSafe (A : TAssertion Native.L Native.C Native.V)
    (a b c d e f g : Native.V) (hDistinct : [a, b, c, d, e, f, g].Nodup)
    (hNames : ∀ i ∈ (namedChoice a b c d e f g).vars, A.ctx i .setvar)
    (hComplete : ∀ i j, A.ctx i .setvar → A.ctx j .setvar → i ≠ j → A.Disjoint i j) :
    Peano.ZF.axAc.DVSafe (choiceSubst a b c d e f g) A.Disjoint := by
  intro i j hij ia hia ib hib
  simp [Peano.ZF.axAc, Peano.ZF.dvs] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [choiceSubst, Tree.vars, List.mem_singleton] at hia hib
    subst ia ib
    exact ⟨by simp_all [List.nodup_cons, List.mem_cons], hComplete _ _
      (hNames _ (by simp [namedChoice, Named.Formula.vars]))
      (hNames _ (by simp [namedChoice, Named.Formula.vars]))
      (by simp_all [List.nodup_cons, List.mem_cons])⟩

/-- Compile a renamed ax-ac instance, retaining the actual native DV obligation. -/
def nativeChoiceInstance {Δ : Set (TAssertion Native.L Native.C Native.V)}
    (hAc : Peano.ZF.axAc ∈ Δ) (A : TAssertion Native.L Native.C Native.V)
    (a b c d e f g : Native.V)
    (hNames : ∀ i ∈ (namedChoice a b c d e f g).vars, A.ctx i .setvar)
    (hDV : Peano.ZF.axAc.DVSafe (choiceSubst a b c d e f g) A.Disjoint) :
    TDerivation Native.grammar Δ A
      (Peano.ZF.T.pf (encode (namedChoice a b c d e f g))) := by
  have hs : ∀ i s, Peano.ZF.axAc.ctx i s →
      Native.grammar.HasSort A.ctx (choiceSubst a b c d e f g i) s := by
    intro i s hi
    simp [Peano.ZF.axAc, Peano.ZF.fs, ctx] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact .var (hNames _ (by simp [namedChoice, Named.Formula.vars]))
  have dn := TDerivation.app (G := Native.grammar) (Γ := Δ) (A := A)
    Peano.ZF.axAc hAc
    (choiceSubst a b c d e f g) hs
    (by intro i hi; simp [Peano.ZF.axAc, essentials] at hi) hDV
  simpa [Peano.ZF.axAc, choiceSubst, TExpr.subst, namedChoice, encode] using dn

/-- A native ax-ac proof, with an explicit dummy-variable frame and actual application. -/
def nativeChoiceProof : TProof Native.grammar Peano.ZF.ZFC Peano.ZF.axAc := by
  refine ⟨TDummies.none _, ?_⟩
  rw [extend_none]
  exact nativeChoiceInFrame _ (fun _ _ h => h) (fun _ h => h)

/-- Universally close the free family variable of the native choice assertion. -/
def allChoiceAssertion : TAssertion Native.L Native.C Native.V :=
  { Peano.ZF.axAc with concl := Peano.ZF.T.pf (Peano.ZF.T.wal .x Peano.ZF.axAc.concl.tree) }

theorem allChoiceAssertion_wellFormed : allChoiceAssertion.WellFormed Native.grammar :=
  .of_checkWF (by decide)

/-- A nontrivial two-step native certificate: ax-ac followed by the actual ax-gen rule. -/
def nativeAllChoiceProof : TProof Native.grammar Peano.ZF.ZFC allChoiceAssertion := by
  refine ⟨TDummies.none _, ?_⟩
  rw [extend_none]
  let τ : Native.V → Tree Native.L Native.V :=
    fun a => if a = .ph then Peano.ZF.axAc.concl.tree else .var a
  have hs : ∀ a s, Peano.ZF.axGen.ctx a s →
      Native.grammar.HasSort allChoiceAssertion.ctx (τ a) s := by
    intro a s h
    simp [Peano.ZF.axGen, Peano.ZF.fw, Peano.ZF.fs, ctx] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨s, hs, ht⟩ :=
        (show Peano.ZF.axAc.WellFormed Native.grammar from .of_checkWF (by decide)).concl_wellTyped
      cases hs
      rw [show allChoiceAssertion.ctx = Peano.ZF.axAc.ctx from rfl]
      simpa [τ] using ht
    · exact .var (by simp [allChoiceAssertion, Peano.ZF.axAc, ctx])
  have d := TDerivation.app (G := Native.grammar) (Γ := Peano.ZF.ZFC)
    (A := allChoiceAssertion) Peano.ZF.axGen
    (Peano.ZF.mem_ZFC.2 (by simp [Peano.ZF.axiomList])) τ hs
    (fun e he => by
      simp only [Peano.ZF.axGen, essentials, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton] at he
      subst e
      simpa [TExpr.subst, Tree.subst, τ, Peano.ZF.axAc] using
        nativeChoiceInFrame allChoiceAssertion (fun _ _ h => h) (fun _ h => h))
    (by simp [DVSafe, Peano.ZF.axGen])
  simpa [Peano.ZF.axGen, TExpr.subst, Tree.subst, τ, allChoiceAssertion] using d

/-- The independent universal choice sentence encodes to this actual native certificate. -/
theorem encode_choiceSentence :
    encodeScoped ZFC.choiceSentence Fin.elim0 (fun n => Nat.casesOn n .x choiceNames) =
      allChoiceAssertion.concl.tree := rfl

/-- The supported native fragment adds actual ax-ac to the four propositional assertions. -/
def choiceFragmentAxioms : Set (TAssertion Native.L Native.C Native.V) :=
  propAxioms ∪ {Peano.ZF.axAc}

theorem choiceFragmentAxioms_subset_ZFC : choiceFragmentAxioms ⊆ Peano.ZF.ZFC := by
  intro B hB
  rcases hB with hp | he
  · exact Peano.ZF.ZF0_subset_ZFC (propAxioms_subset_ZF0 hp)
  · obtain rfl := he
    exact Peano.ZF.mem_ZFC.2 (by simp [Peano.ZF.axiomList])

/-- Independent propositional proofs with all distinct-name choice schema instances. -/
abbrev ChoiceHilbert (Γ : List (Named.Formula Native.V)) (p : Named.Formula Native.V) :=
  Named.Hilbert {q | ChoiceSchema q} Γ p

/-- Interpret the supported independent fragment in the full scoped ZFC calculus. -/
noncomputable def choiceHilbertToSimple {n : Nat} (ρ : Native.V → Fin n)
    {Γ : List (Named.Formula Native.V)} {p : Named.Formula Native.V}
    (d : ChoiceHilbert Γ p) : ZFC.Derivation (Γ.map (Named.Formula.lower ρ)) (p.lower ρ) :=
  d.toClassical ρ (fun _ hp => choiceSchemaToSimple ZF.axiomFamily ρ _ hp)

/-- Every independent choice leaf compiles when the frame supplies its required DV pairs. -/
theorem choiceLeafToNative_nonempty (A : TAssertion Native.L Native.C Native.V)
    (hComplete : ∀ i j, A.ctx i .setvar → A.ctx j .setvar → i ≠ j → A.Disjoint i j)
    {p : Named.Formula Native.V} (hp : ChoiceSchema p)
    (hNames : ∀ i ∈ p.vars, A.ctx i .setvar) :
    Nonempty (TDerivation Native.grammar choiceFragmentAxioms A (Peano.ZF.T.pf (encode p))) := by
  cases hp with
  | ac a b c d e f g h =>
    exact ⟨nativeChoiceInstance (Or.inr rfl) A a b c d e f g hNames
      (choiceSubst_dvSafe A a b c d e f g h hNames hComplete)⟩

/-- Translate an entire independent proof into actual native axiom applications. -/
noncomputable def choiceHilbertToNative (A : TAssertion Native.L Native.C Native.V)
    (hComplete : ∀ i j, A.ctx i .setvar → A.ctx j .setvar → i ≠ j → A.Disjoint i j)
    {Γ : List (Named.Formula Native.V)}
    (hΓ : ∀ p ∈ Γ, Peano.ZF.T.pf (encode p) ∈ A.essentials)
    {p : Named.Formula Native.V} (d : ChoiceHilbert Γ p)
    (hctx : ∀ i ∈ d.vars, A.ctx i .setvar) :
    TDerivation Native.grammar choiceFragmentAxioms A (Peano.ZF.T.pf (encode p)) :=
  hilbertToNative (fun _ h => Or.inl h) hΓ
    (fun _ hp hn => _root_.Classical.choice (choiceLeafToNative_nonempty A hComplete hp hn))
    d hctx

/-- Decode any sorted and DV-safe native ax-ac substitution to an independent schema leaf. -/
theorem decodeChoiceInstance (A : TAssertion Native.L Native.C Native.V)
    (hpure : ∀ i s, A.ctx i s → s = .setvar)
    (τ : Native.V → Tree Native.L Native.V)
    (hs : ∀ i s, Peano.ZF.axAc.ctx i s → Native.grammar.HasSort A.ctx (τ i) s)
    (hDV : Peano.ZF.axAc.DVSafe τ A.Disjoint) :
    ∃ p : Named.Formula Native.V, ChoiceSchema p ∧
      Peano.ZF.axAc.concl.subst τ = Peano.ZF.T.pf (encode p) := by
  have parse : ∀ i, Peano.ZF.axAc.ctx i .setvar → ∃ j, τ i = Tree.var j := by
    intro i hi
    exact Peano.ZF.hasSort_setCtx_setvar ((hs i .setvar hi).mono hpure)
  obtain ⟨a, ha⟩ := parse .x (by simp [Peano.ZF.axAc, ctx, Peano.ZF.fs])
  obtain ⟨b, hb⟩ := parse .y (by simp [Peano.ZF.axAc, ctx, Peano.ZF.fs])
  obtain ⟨c, hc⟩ := parse .z (by simp [Peano.ZF.axAc, ctx, Peano.ZF.fs])
  obtain ⟨d, hd⟩ := parse .w (by simp [Peano.ZF.axAc, ctx, Peano.ZF.fs])
  obtain ⟨e, he⟩ := parse .v (by simp [Peano.ZF.axAc, ctx, Peano.ZF.fs])
  obtain ⟨f, hf⟩ := parse .u (by simp [Peano.ZF.axAc, ctx, Peano.ZF.fs])
  obtain ⟨g, hg⟩ := parse .t (by simp [Peano.ZF.axAc, ctx, Peano.ZF.fs])
  have hne : ∀ i j, (i, j) ∈ Peano.ZF.axAc.dv → ∀ a b,
      τ i = Tree.var a → τ j = Tree.var b → a ≠ b := by
    intro i j hij a b hia hjb
    exact (hDV i j hij a (by simp [hia]) b (by simp [hjb])).1
  have hn : [a, b, c, d, e, f, g].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨hne .x .y (by decide) a b ha hb, hne .x .z (by decide) a c ha hc, hne .x .w (by decide) a d ha hd, hne .x .v (by decide) a e ha he, hne .x .u (by decide) a f ha hf, hne .x .t (by decide) a g ha hg⟩, ⟨hne .y .z (by decide) b c hb hc, hne .y .w (by decide) b d hb hd, hne .y .v (by decide) b e hb he, hne .y .u (by decide) b f hb hf, hne .y .t (by decide) b g hb hg⟩, ⟨hne .z .w (by decide) c d hc hd, hne .z .v (by decide) c e hc he, hne .z .u (by decide) c f hc hf, hne .z .t (by decide) c g hc hg⟩, ⟨hne .w .v (by decide) d e hd he, hne .w .u (by decide) d f hd hf, hne .w .t (by decide) d g hd hg⟩, ⟨hne .v .u (by decide) e f he hf, hne .v .t (by decide) e g he hg⟩, hne .u .t (by decide) f g hf hg⟩
  refine ⟨namedChoice a b c d e f g, .ac _ _ _ _ _ _ _ hn, ?_⟩
  simp [Peano.ZF.axAc, TExpr.subst, namedChoice, encode, ha, hb, hc, hd, he, hf, hg]

/-- Reflect every actual native proof in the supported choice/propositional fragment. -/
theorem nativeChoiceToHilbert {A : TAssertion Native.L Native.C Native.V}
    {Γ : List (Named.Formula Native.V)}
    (hpure : ∀ i s, A.ctx i s → s = .setvar)
    (hΓ : ∀ e ∈ A.essentials, ∃ p ∈ Γ, e = Peano.ZF.T.pf (encode p))
    {e : TExpr Native.L Native.C Native.V}
    (d : TDerivation Native.grammar choiceFragmentAxioms A e) :
    ∃ p : Named.Formula Native.V, e = Peano.ZF.T.pf (encode p) ∧ Nonempty (ChoiceHilbert Γ p) := by
  apply nativeToHilbertWithAxioms hpure hΓ _ d
  intro B hB τ hs hDV
  rcases hB with hp | he
  · exact Or.inl hp
  · obtain rfl := he
    exact Or.inr (decodeChoiceInstance A hpure τ hs hDV)

/-- A finite pure native frame with every distinct declared name pair disjoint. -/
def choiceProofFrame (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) : TAssertion Native.L Native.C Native.V :=
  { proofFrame S Γ p with dv := Peano.ZF.dvs S.dedup }

@[simp] theorem choiceProofFrame_ctx (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) (i : Native.V) (s : Native.C) :
    (choiceProofFrame S Γ p).ctx i s ↔ i ∈ S ∧ s = .setvar :=
  proofFrame_ctx S Γ p i s

@[simp] theorem choiceProofFrame_essentials (S : List Native.V)
    (Γ : List (Named.Formula Native.V)) (p : Named.Formula Native.V) :
    (choiceProofFrame S Γ p).essentials = Γ.map (fun q => Peano.ZF.T.pf (encode q)) :=
  proofFrame_essentials S Γ p

theorem choiceProofFrame_complete (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) :
    ∀ i j, (choiceProofFrame S Γ p).ctx i .setvar →
      (choiceProofFrame S Γ p).ctx j .setvar → i ≠ j → (choiceProofFrame S Γ p).Disjoint i j := by
  intro i j hi hj hij
  exact Peano.ZF.mem_dvs_of_ne
    (List.mem_dedup.mpr ((choiceProofFrame_ctx S Γ p i .setvar).mp hi).1)
    (List.mem_dedup.mpr ((choiceProofFrame_ctx S Γ p j .setvar).mp hj).1) hij

/-- Finite proof support makes the compiled assertion well formed, including DV pairs. -/
theorem choiceProofFrame_wellFormed (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) (hp : ∀ i ∈ p.vars, i ∈ S)
    (hΓ : ∀ q ∈ Γ, ∀ i ∈ q.vars, i ∈ S) :
    (choiceProofFrame S Γ p).WellFormed Native.grammar where
  floats_nodup := by
    simpa [choiceProofFrame, proofFrame, floats, Peano.ZF.fs,
      List.filterMap_map, List.map_map, Function.comp_def] using List.nodup_dedup S
  float_sort i s hi := by
    rw [((choiceProofFrame_ctx S Γ p i s).mp hi).2]
    decide
  ess_wellTyped e he := by
    rw [choiceProofFrame_essentials] at he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact ⟨.wff, rfl, encode_sorted_on_vars q (fun i hi =>
      (choiceProofFrame_ctx S Γ p i .setvar).mpr ⟨hΓ q hq i hi, rfl⟩)⟩
  concl_wellTyped := ⟨.wff, rfl, encode_sorted_on_vars p (fun i hi =>
    (choiceProofFrame_ctx S Γ p i .setvar).mpr ⟨hp i hi, rfl⟩)⟩
  dv_irrefl i j hij := Peano.ToZF.ne_of_mem_dvs (List.nodup_dedup S) hij
  dv_float i j hij := by
    obtain ⟨hi, hj⟩ := Peano.ToZF.mem_dvs hij
    exact ⟨⟨.setvar, (choiceProofFrame_ctx S Γ p i .setvar).mpr
      ⟨List.mem_dedup.mp hi, rfl⟩⟩,
      ⟨.setvar, (choiceProofFrame_ctx S Γ p j .setvar).mpr ⟨List.mem_dedup.mp hj, rfl⟩⟩⟩

/-- Actual bidirectional derivability for choice plus propositional inference.
This concerns the displayed native fragment, rather than all native ZFC proofs. -/
theorem choice_propositional_correspondence (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) : Nonempty (ChoiceHilbert Γ p) ↔
    ∃ A : TAssertion Native.L Native.C Native.V,
      A.WellFormed Native.grammar ∧
      (∀ i s, A.ctx i s → s = .setvar) ∧
      (∀ e ∈ A.essentials, ∃ q ∈ Γ, e = Peano.ZF.T.pf (encode q)) ∧
      (∀ q ∈ Γ, Peano.ZF.T.pf (encode q) ∈ A.essentials) ∧
      Nonempty (TDerivation Native.grammar choiceFragmentAxioms A (Peano.ZF.T.pf (encode p))) := by
  constructor
  · rintro ⟨d⟩
    let S := d.vars ++ Γ.flatMap Named.Formula.vars
    let A := choiceProofFrame S Γ p
    refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
    · exact choiceProofFrame_wellFormed S Γ p
        (fun i hi => List.mem_append_left _ (d.conclusion_vars i hi))
        (fun q hq i hi => List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hi⟩))
    · intro i s hs
      exact ((choiceProofFrame_ctx S Γ p i s).mp hs).2
    · intro e he
      rw [choiceProofFrame_essentials] at he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      exact ⟨q, hq, rfl⟩
    · intro q hq
      rw [choiceProofFrame_essentials]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    · refine ⟨choiceHilbertToNative A (choiceProofFrame_complete S Γ p) ?_ d ?_⟩
      · intro q hq
        rw [choiceProofFrame_essentials]
        exact List.mem_map.mpr ⟨q, hq, rfl⟩
      · intro i hi
        exact (choiceProofFrame_ctx S Γ p i .setvar).mpr ⟨List.mem_append_left _ hi, rfl⟩
  · rintro ⟨A, _, hpure, hΓ, _, ⟨d⟩⟩
    obtain ⟨q, he, hd⟩ := nativeChoiceToHilbert hpure hΓ d
    have hq : q = p := encode_injective (congrArg TExpr.tree he).symm
    exact hq ▸ hd

/-- ZFC's common nonlogical fragment extends all nine independent ZF schemas by choice. -/
def ZFCSchema {V : Type*} (p : Named.Formula V) : Prop := ZF.Schema p ∨ ChoiceSchema p

/-- Both independent schema families have their stated meanings in any semantic ZFC model. -/
theorem zfcSchema_sound {M V : Type*} [Membership M M] [DecidableEq V]
    (hZFC : SetTheory.ZFC M V) {p : Named.Formula V} (hp : ZFCSchema p) :
    ∀ E : V → M, p.eval E := by
  rcases hp with hZF | hChoice
  · exact ZF.schema_sound hZFC.toZF hZF
  · exact choiceSchema_sound hZFC hChoice

/-- The independent common-fragment proofs reuse the shared Hilbert rule constructors. -/
abbrev ZFCHilbert {V : Type*} (Γ : List (Named.Formula V)) (p : Named.Formula V) :=
  Named.Hilbert ZFCSchema Γ p

/-- A model bridge for the independently presented supported ZFC proof fragment. -/
theorem zfcHilbert_sound {M V : Type*} [Membership M M] [DecidableEq V]
    (hZFC : SetTheory.ZFC M V) {Γ : List (Named.Formula V)} {p : Named.Formula V}
    (d : ZFCHilbert Γ p) (E : V → M) (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E :=
  d.sound (fun _ hp => zfcSchema_sound hZFC hp) E hΓ

/-- The corresponding actual native fragment: propositions, all nine ZF schemas, and ax-ac. -/
def zfcFragment : Set (TAssertion Native.L Native.C Native.V) := zfFragment ∪ {Peano.ZF.axAc}

theorem zfcFragment_subset_ZFC : zfcFragment ⊆ Peano.ZF.ZFC := by
  intro B hB
  rcases hB with hZF | he
  · exact Peano.ZF.ZF0_subset_ZFC (zfFragment_subset_ZF0 hZF)
  · obtain rfl := he
    exact Peano.ZF.mem_ZFC.2 (by simp [Peano.ZF.axiomList])

theorem choiceFragment_subset_zfcFragment : choiceFragmentAxioms ⊆ zfcFragment := by
  intro B hB
  rcases hB with hp | hc
  · exact Or.inl (Or.inl hp)
  · exact Or.inr hc

/-- Compile full common-fragment ZFC proofs by the two independently checked schema adapters. -/
noncomputable def zfcHilbertToNative (A : TAssertion Native.L Native.C Native.V)
    (hComplete : ∀ i j, A.ctx i .setvar → A.ctx j .setvar → i ≠ j → A.Disjoint i j)
    {Γ : List (Named.Formula Native.V)}
    (hΓ : ∀ p ∈ Γ, Peano.ZF.T.pf (encode p) ∈ A.essentials)
    {p : Named.Formula Native.V} (d : ZFCHilbert Γ p)
    (hctx : ∀ i ∈ d.vars, A.ctx i .setvar) :
    TDerivation Native.grammar zfcFragment A (Peano.ZF.T.pf (encode p)) := by
  apply hilbertToNative (fun _ hp => Or.inl (Or.inl hp)) hΓ _ d hctx
  intro q hq hn
  apply _root_.Classical.choice
  rcases hq with hZF | hChoice
  · exact schema_native (fun _ hs => Or.inl (Or.inr hs)) hZF hn
      (fun i hi j hj hij => hComplete i j (hn i hi) (hn j hj) hij)
  · exact (choiceLeafToNative_nonempty A hComplete hChoice hn).map
      (fun dn => dn.mono choiceFragment_subset_zfcFragment)

/-- Reflect actual native proofs using the exact ZF and choice schema decoders. -/
theorem nativeToZFCHilbert {A : TAssertion Native.L Native.C Native.V}
    {Γ : List (Named.Formula Native.V)}
    (hpure : ∀ i s, A.ctx i s → s = .setvar)
    (hΓ : ∀ e ∈ A.essentials, ∃ p ∈ Γ, e = Peano.ZF.T.pf (encode p))
    {e : TExpr Native.L Native.C Native.V}
    (d : TDerivation Native.grammar zfcFragment A e) :
    ∃ p : Named.Formula Native.V, e = Peano.ZF.T.pf (encode p) ∧ Nonempty (ZFCHilbert Γ p) := by
  apply nativeToHilbertWithAxioms hpure hΓ _ d
  intro B hB τ hs hDV
  rcases hB with (hProp | hZF) | hChoice
  · exact Or.inl hProp
  · obtain ⟨q, hq, he⟩ := native_schema_instance hZF τ hpure hs hDV
    exact Or.inr ⟨q, Or.inl hq, he⟩
  · obtain rfl := hChoice
    obtain ⟨q, hq, he⟩ := decodeChoiceInstance A hpure τ hs hDV
    exact Or.inr ⟨q, Or.inr hq, he⟩

/-- Bidirectional derivability for the supported common ZFC primitive/schema fragment.
Native predicate/equality inference and broader definitional elimination remain separate. -/
theorem zfc_fragment_correspondence (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) : Nonempty (ZFCHilbert Γ p) ↔
    ∃ A : TAssertion Native.L Native.C Native.V,
      A.WellFormed Native.grammar ∧
      (∀ i s, A.ctx i s → s = .setvar) ∧
      (∀ e ∈ A.essentials, ∃ q ∈ Γ, e = Peano.ZF.T.pf (encode q)) ∧
      (∀ q ∈ Γ, Peano.ZF.T.pf (encode q) ∈ A.essentials) ∧
      Nonempty (TDerivation Native.grammar zfcFragment A (Peano.ZF.T.pf (encode p))) := by
  constructor
  · rintro ⟨d⟩
    let S := d.vars ++ Γ.flatMap Named.Formula.vars
    let A := choiceProofFrame S Γ p
    refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
    · exact choiceProofFrame_wellFormed S Γ p
        (fun i hi => List.mem_append_left _ (d.conclusion_vars i hi))
        (fun q hq i hi => List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hi⟩))
    · intro i s hs
      exact ((choiceProofFrame_ctx S Γ p i s).mp hs).2
    · intro e he
      rw [choiceProofFrame_essentials] at he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      exact ⟨q, hq, rfl⟩
    · intro q hq
      rw [choiceProofFrame_essentials]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    · refine ⟨zfcHilbertToNative A (choiceProofFrame_complete S Γ p) ?_ d ?_⟩
      · intro q hq
        rw [choiceProofFrame_essentials]
        exact List.mem_map.mpr ⟨q, hq, rfl⟩
      · intro i hi
        exact (choiceProofFrame_ctx S Γ p i .setvar).mpr ⟨List.mem_append_left _ hi, rfl⟩
  · rintro ⟨A, _, hpure, hΓ, _, ⟨d⟩⟩
    obtain ⟨q, he, hd⟩ := nativeToZFCHilbert hpure hΓ d
    have hq : q = p := encode_injective (congrArg TExpr.tree he).symm
    exact hq ▸ hd

/-- Finite named ZFC leaves have actual proofs in the shared scoped natural-deduction system. -/
theorem zfcSchemaToScoped_nonempty {n : Nat} (Γ : List (Formula n))
    {p : Named.Formula (Fin n)} (hp : ZFCSchema p) :
    Nonempty (ZFC.Derivation Γ (p.lower id)) := by
  rcases hp with hZF | hChoice
  · exact ⟨.ax (Or.inl ⟨n, p, some ∘ id, hZF, Named.Formula.scope_total p id⟩)⟩
  · exact choiceSchemaToSimple_nonempty ZF.axiomFamily id Γ hChoice

/-- Common finite named proofs transport into the full independent scoped ZFC calculus. -/
noncomputable def zfcHilbertToScoped {n : Nat} {Γ : List (Named.Formula (Fin n))}
    {p : Named.Formula (Fin n)} (d : ZFCHilbert Γ p) :
    ZFC.Derivation (Γ.map (Named.Formula.lower id)) (p.lower id) :=
  d.toClassical id (fun _ hp => _root_.Classical.choice (zfcSchemaToScoped_nonempty _ hp))

end Silmaril.Logic.SetTheory.Inductive.MetamathZFC
