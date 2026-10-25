module

public import Silmaril.Logic.HOLLight.Consilience.Semantics
public import Silmaril.Logic.HOLLight.Inference
public import Silmaril.Logic.Metatheory.InferenceSystemCat

@[expose] public section

/-!
# Structured inference and category maps

The independent system retains proof trees in `Type`. Its forward morphism
lands in the native proposition-valued kernel. A reverse morphism lands in
the explicitly truncated independent system. Bidirectional provability does
not identify the proof trees with native proof objects.
-/
namespace Silmaril.Logic.HOLLight.Consilience

open Cslib.Logic Cslib.Logic.InferenceSystem Silmaril.Logic.Metatheory CategoryTheory

namespace Formula

def encode {sig : Signature} (p : Formula sig) : HOLLight.Formula sig :=
  ⟨p.term.encode, p.typing.encode⟩

def decode {sig : Signature} (p : HOLLight.Formula sig) : Formula sig :=
  ⟨Term.decode p.term, Typed.decode p.typing⟩

@[ext] theorem ext {sig : Signature} {p q : Formula sig} (h : p.term = q.term) : p = q := by
  cases p
  cases q
  cases h
  rfl

@[simp] theorem decode_encode {sig : Signature} (p : Formula sig) : decode (encode p) = p :=
  ext (Term.decode_encode p.term)

@[simp] theorem encode_decode {sig : Signature} (p : HOLLight.Formula sig) : encode (decode p) = p :=
  HOLLight.Formula.ext (Term.encode_decode p.term)

def syntaxEquiv (sig : Signature) : Formula sig ≃ HOLLight.Formula sig :=
  ⟨encode, decode, decode_encode, encode_decode⟩

end Formula

namespace Sequent

def encode (s : Sequent) : HOLLight.Sequent := ⟨encodeContext s.hyps, s.conclusion.encode⟩
def decode (s : HOLLight.Sequent) : Sequent := ⟨decodeContext s.hyps, Term.decode s.conclusion⟩

@[simp] theorem decode_encode (s : Sequent) : decode (encode s) = s := by
  cases s
  simp [encode, decode]

@[simp] theorem encode_decode (s : HOLLight.Sequent) : encode (decode s) = s := by
  cases s
  simp [encode, decode]

end Sequent

structure TreeSystem (sig : Signature) (T : Theory) (H : Context) where
structure TruncatedSystem (sig : Signature) (T : Theory) (H : Context) where

instance {sig T H} : InferenceSystem (TreeSystem sig T H) Term where
  derivation p := Proof sig T H p

instance {sig T H} : InferenceSystem (TruncatedSystem sig T H) Term where
  derivation p := Nonempty (Proof sig T H p)

/-- The forward proof map consumes a concrete independent derivation tree. -/
def encodeMorphism (sig : Signature) (T : Theory) (H : Context) :
    InferenceMorphism (TreeSystem sig T H)
      (HOLLight.ContextSystem sig (encodeTheory T) (encodeContext H)) Term Tm where
  map := Term.encode
  mapDerivation := Proof.encode

/-- The inverse syntax translation recovers provability, explicitly truncated. -/
def decodeMorphism (sig : Signature) (T : HOLLight.Theory) (H : Hyps) :
    InferenceMorphism (HOLLight.ContextSystem sig T H)
      (TruncatedSystem sig (decodeTheory T) (decodeContext H)) Tm Term where
  map := Term.decode
  mapDerivation := Proof.decode

/-- The two inference systems have exactly the corresponding provable terms. -/
theorem derivable_iff {sig : Signature} {T : Theory} {H : Context} {p : Term} :
    DerivableIn (TreeSystem sig T H) p ↔
      DerivableIn (HOLLight.ContextSystem sig (encodeTheory T) (encodeContext H)) p.encode := by
  constructor
  · exact (encodeMorphism sig T H).preserves
  · intro ⟨h⟩
    exact Proof.encode_iff.mp h

def treeObject (sig : Signature) (T : Theory) (H : Context) : InferenceSystemCat.{0, 1} :=
  InferenceSystemCat.of.{0, 0, 1, 0} (TreeSystem sig T H) Term

def nativeObject (sig : Signature) (T : HOLLight.Theory) (H : Hyps) : InferenceSystemCat.{0, 1} :=
  InferenceSystemCat.of.{0, 0, 0, 1} (HOLLight.ContextSystem sig T H) Tm

def truncatedObject (sig : Signature) (T : Theory) (H : Context) : InferenceSystemCat.{0, 1} :=
  InferenceSystemCat.of.{0, 0, 0, 1} (TruncatedSystem sig T H) Term

/-- A category arrow includes both the syntax map and the actual proof map. -/
def encodeArrow (sig : Signature) (T : Theory) (H : Context) :
    treeObject sig T H ⟶ nativeObject sig (encodeTheory T) (encodeContext H) :=
  InferenceSystemCat.ofMorphism (encodeMorphism sig T H)

def decodeArrow (sig : Signature) (T : HOLLight.Theory) (H : Hyps) :
    nativeObject sig T H ⟶ truncatedObject sig (decodeTheory T) (decodeContext H) :=
  { map := Term.decode
    mapDerivation := fun d => ⟨⟨Proof.decode d.down.down⟩⟩ }

@[simp] theorem encodeArrow_map (sig : Signature) (T : Theory) (H : Context) (p : Term) :
    (encodeArrow sig T H).map p = p.encode := rfl

@[simp] theorem decodeArrow_map (sig : Signature) (T : HOLLight.Theory) (H : Hyps) (p : Tm) :
    (decodeArrow sig T H).map p = Term.decode p := rfl

/-- Decoding after encoding is the identity on conclusions, not proof fibers. -/
theorem roundtrip_conclusion (sig : Signature) (T : Theory) (H : Context) (p : Term) :
    (decodeArrow sig (encodeTheory T) (encodeContext H)).map ((encodeArrow sig T H).map p) = p :=
  Term.decode_encode p

end Silmaril.Logic.HOLLight.Consilience
