module

public import Silmaril.Logic.HOLLight.Consilience.Syntax
public import Silmaril.Logic.HOLLight.Kernel

@[expose] public section

/-!
# Independent inference rules and their kernel translations

`Proof` is an inductive judgment on the second syntax. Each constructor states
its own premises, including typing, freshness, finite-set discharge and both
forms of instantiation. It has no native derivability premise. The two
translations below recurse on actual derivations, rather than deducing
provability from agreement of denotations.
-/
namespace Silmaril.Logic.HOLLight.Consilience

abbrev Context := Finset Term
abbrev Theory := List Term

inductive Proof (sig : Signature) (theory : Theory) : Context → Term → Type where
  | ax {p} (member : p ∈ theory) (typing : Typed sig [] p .bool) : Proof sig theory ∅ p
  | refl {t A} (typing : Typed sig [] t A) : Proof sig theory ∅ (Term.equal A t t)
  | trans {H K A s t r} : Proof sig theory H (Term.equal A s t) →
      Proof sig theory K (Term.equal A t r) → Proof sig theory (H ∪ K) (Term.equal A s r)
  | app {H K A B f g x y} : Proof sig theory H (Term.equal (.arr A B) f g) →
      Proof sig theory K (Term.equal A x y) →
      Proof sig theory (H ∪ K) (Term.equal B (.app f x) (.app g y))
  | lam {H A B s t} (n : Nat) (wf : A.WellFormed sig.tyOps)
      (fresh : ∀ p ∈ H, p.Fresh (n, A)) : Proof sig theory H (Term.equal B s t) →
      Proof sig theory H (Term.equal (.arr A B)
        (.lam A (s.replaceFree (n, A) (.bound 0)))
        (.lam A (t.replaceFree (n, A) (.bound 0))))
  | beta {A B b} (n : Nat) (wf : A.WellFormed sig.tyOps) (typing : Typed sig [A] b B)
      (fresh : b.Fresh (n, A)) : Proof sig theory ∅
        (Term.equal B (.app (.lam A b) (.free n A)) (b.open (.free n A)))
  | hyp {p} (typing : Typed sig [] p .bool) : Proof sig theory {p} p
  | eqMp {H K p q} : Proof sig theory H (Term.equal .bool p q) → Proof sig theory K p →
      Proof sig theory (H ∪ K) q
  | antisym {H K p q} : Proof sig theory H p → Proof sig theory K q →
      Proof sig theory (H.erase q ∪ K.erase p) (Term.equal .bool p q)
  | subst {H p} (σ : Nat → Ty → Term)
      (typing : ∀ n A, A.WellFormed sig.tyOps → Typed sig [] (σ n A) A) :
      Proof sig theory H p → Proof sig theory (H.image (Term.freeSubst σ)) (p.freeSubst σ)
  | instType {H p} (σ : Nat → Ty) (typing : ∀ n, (σ n).WellFormed sig.tyOps) :
      Proof sig theory H p → Proof sig theory (H.image (Term.tySubst σ)) (p.tySubst σ)

def encodeContext (H : Context) : Hyps := H.image Term.encode

def decodeContext (H : Hyps) : Context := H.image Term.decode

def encodeTheory (T : Theory) : HOLLight.Theory := T.map Term.encode

def decodeTheory (T : HOLLight.Theory) : Theory := T.map Term.decode

@[simp] theorem decode_encodeContext (H : Context) : decodeContext (encodeContext H) = H := by
  simp [decodeContext, encodeContext, Finset.image_image, Function.comp_def]

@[simp] theorem encode_decodeContext (H : Hyps) : encodeContext (decodeContext H) = H := by
  simp [decodeContext, encodeContext, Finset.image_image, Function.comp_def]

@[simp] theorem decode_encodeTheory (T : Theory) : decodeTheory (encodeTheory T) = T := by
  simp [decodeTheory, encodeTheory, List.map_map, Function.comp_def]

@[simp] theorem encode_decodeTheory (T : HOLLight.Theory) : encodeTheory (decodeTheory T) = T := by
  simp [decodeTheory, encodeTheory, List.map_map, Function.comp_def]

@[simp] theorem encodeContext_empty : encodeContext ∅ = ∅ := by simp [encodeContext]
@[simp] theorem decodeContext_empty : decodeContext ∅ = ∅ := by simp [decodeContext]

@[simp] theorem encodeContext_union (H K : Context) :
    encodeContext (H ∪ K) = encodeContext H ∪ encodeContext K := by simp [encodeContext, Finset.image_union]

@[simp] theorem decodeContext_union (H K : Hyps) :
    decodeContext (H ∪ K) = decodeContext H ∪ decodeContext K := by simp [decodeContext, Finset.image_union]

@[simp] theorem encodeContext_singleton (p : Term) : encodeContext {p} = {p.encode} := by
  simp [encodeContext]

@[simp] theorem decodeContext_singleton (p : Tm) : decodeContext {p} = {Term.decode p} := by
  simp [decodeContext]

@[simp] theorem encodeContext_erase (H : Context) (p : Term) :
    encodeContext (H.erase p) = (encodeContext H).erase p.encode := by
  exact Finset.image_erase Term.encode_injective H p

@[simp] theorem decodeContext_erase (H : Hyps) (p : Tm) :
    decodeContext (H.erase p) = (decodeContext H).erase (Term.decode p) := by
  exact Finset.image_erase Term.decode_injective H p

@[simp] theorem encodeContext_freeSubst (H : Context) (σ : Nat → Ty → Term) :
    encodeContext (H.image (Term.freeSubst σ)) =
      (encodeContext H).image (Tm.freeSubst (fun n A => (σ n A).encode)) := by
  simp [encodeContext, Finset.image_image, Function.comp_def]

@[simp] theorem decodeContext_freeSubst (H : Hyps) (σ : Nat → Ty → Tm) :
    decodeContext (H.image (Tm.freeSubst σ)) =
      (decodeContext H).image (Term.freeSubst (fun n A => Term.decode (σ n A))) := by
  simp [decodeContext, Finset.image_image, Function.comp_def]

@[simp] theorem encodeContext_tySubst (H : Context) (σ : Nat → Ty) :
    encodeContext (H.image (Term.tySubst σ)) = (encodeContext H).image (Tm.tySubst σ) := by
  simp [encodeContext, Finset.image_image, Function.comp_def]

@[simp] theorem decodeContext_tySubst (H : Hyps) (σ : Nat → Ty) :
    decodeContext (H.image (Tm.tySubst σ)) = (decodeContext H).image (Term.tySubst σ) := by
  simp [decodeContext, Finset.image_image, Function.comp_def]

namespace Proof

/-- Translate a proof rule by rule into the native kernel. -/
theorem encode {sig T H p} (h : Proof sig T H p) :
    Derives sig (encodeTheory T) (encodeContext H) p.encode := by
  induction h with
  | ax member typing =>
    exact .axiom (List.mem_map.mpr ⟨_, member, rfl⟩) typing.encode
  | refl typing => simpa using Derives.refl (theory := encodeTheory T) typing.encode
  | trans _ _ ihl ihr => simpa using ihl.trans ihr
  | app _ _ ihf ihx => simpa [Term.encode] using ihf.mkComb ihx
  | @lam H A B s t n wf fresh _ ih =>
    have hf : ∀ p ∈ encodeContext H, p.Fresh (n, A) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (Term.encode_fresh _ _).mpr (fresh q hq)
    simpa [Term.encode] using Derives.abs n wf hf ih
  | beta n wf typing fresh =>
    simpa [Term.encode] using Derives.beta (theory := encodeTheory T) n wf typing.encode
      ((Term.encode_fresh _ _).mpr fresh)
  | hyp typing => simpa using Derives.assume (theory := encodeTheory T) typing.encode
  | eqMp _ _ iheq ihp => simpa using iheq.eqMp ihp
  | antisym _ _ ihp ihq => simpa using ihp.deductAntisym ihq
  | subst σ typing _ ih =>
    simpa using ih.inst (fun n A => (σ n A).encode) (fun n A wf => (typing n A wf).encode)
  | instType σ typing _ ih => simpa using ih.instType σ typing

/-- Native proofs inhabit `Prop`; decoding recovers existence of a proof tree,
not a selected tree or an inverse on proof objects. -/
theorem decode {sig T H p} (h : Derives sig T H p) :
    Nonempty (Proof sig (decodeTheory T) (decodeContext H) (Term.decode p)) := by
  induction h with
  | «axiom» member typing =>
    exact ⟨.ax (List.mem_map.mpr ⟨_, member, rfl⟩) (Typed.decode typing)⟩
  | refl typing => simpa using (Nonempty.intro (Proof.refl (theory := decodeTheory T) (Typed.decode typing)))
  | trans _ _ ihl ihr =>
    obtain ⟨l⟩ := ihl
    obtain ⟨r⟩ := ihr
    simpa using (Nonempty.intro (Proof.trans l r))
  | mkComb _ _ ihf ihx =>
    obtain ⟨f⟩ := ihf
    obtain ⟨x⟩ := ihx
    simpa [Term.decode] using (Nonempty.intro (Proof.app f x))
  | @abs H A B s t n wf fresh _ ih =>
    obtain ⟨d⟩ := ih
    have hf : ∀ p ∈ decodeContext H, p.Fresh (n, A) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (Term.decode_fresh _ _).mpr (fresh q hq)
    simpa [Term.decode] using (Nonempty.intro (Proof.lam n wf hf d))
  | beta n wf typing fresh =>
    simpa [Term.decode] using (Nonempty.intro (Proof.beta (theory := decodeTheory T) n wf
      (Typed.decode typing) ((Term.decode_fresh _ _).mpr fresh)))
  | assume typing => simpa using (Nonempty.intro (Proof.hyp (theory := decodeTheory T) (Typed.decode typing)))
  | eqMp _ _ iheq ihp =>
    obtain ⟨eq⟩ := iheq
    obtain ⟨p⟩ := ihp
    simpa using (Nonempty.intro (Proof.eqMp eq p))
  | deductAntisym _ _ ihp ihq =>
    obtain ⟨p⟩ := ihp
    obtain ⟨q⟩ := ihq
    simpa using (Nonempty.intro (Proof.antisym p q))
  | inst σ typing _ ih =>
    obtain ⟨d⟩ := ih
    simpa using (Nonempty.intro (Proof.subst (fun n A => Term.decode (σ n A))
      (fun n A wf => Typed.decode (typing n A wf)) d))
  | instType σ typing _ ih =>
    obtain ⟨d⟩ := ih
    simpa using (Nonempty.intro (Proof.instType σ typing d))

/-- Provability equivalence for the complete existing fixed-signature kernel.
The independent proof trees are explicitly truncated with `Nonempty`. -/
theorem encode_iff {sig T H p} :
    Derives sig (encodeTheory T) (encodeContext H) p.encode ↔ Nonempty (Proof sig T H p) :=
  ⟨fun h => by simpa using decode h, fun ⟨h⟩ => encode h⟩

theorem decode_iff {sig T H p} :
    Nonempty (Proof sig (decodeTheory T) (decodeContext H) (Term.decode p)) ↔ Derives sig T H p :=
  ⟨fun ⟨h⟩ => by simpa using encode h, decode⟩

end Proof
end Silmaril.Logic.HOLLight.Consilience
