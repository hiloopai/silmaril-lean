module

public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Compiler.Core.Verified.OpsLink.Defs

/-! # Proved fragments of the verified compiler

A `Fragment` is one proved piece of `Verified.compile`: a partial compiler from Core documents
to artifacts together with the proof that every artifact it produces satisfies `ArtifactSound`,
the part of the frozen `Spec.SoundSpec` about one document and one artifact. `first fs` tries
the fragments of `fs` in order and returns the first artifact; `first_sound` proves
`SoundSpec (first fs)` for every list, once. A new construct is then a new file that defines a
`Fragment`, plus one entry in `Verified/Fragments.lean`; neither `Verified.compile` nor
`compile_sound` changes.

Most fragments are a syntax-directed recogniser and a link of the recognised data:

* `ofConst recognize`: `recognize doc = some n` and `main` exits with `n` for every argument
  list (`ConstSound`); the artifact is `ConstLink.link n`, which loads `n` and returns it.
* `ofOps recognize ops r`: `recognize doc = some x`, and for every argument list Core either
  reaches undefined behaviour or exits with the word that the register operations `ops x` leave
  in register `r x` from every frame (`OpsSound`); the artifact is `OpsLink.link (ops x) (r x)`.

The hypotheses are Prop-valued definitions so that the values of the fragments, which
`Verified.compile` reaches, mention only the recogniser and the link: the Lir and Core
dynamics stay in the proofs (the evaluator's integrity closure follows values, not theorems).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified

open Silmaril.Cerberus Silmaril.Machine
open Spec Backend

/-- What `Spec.SoundSpec` asks of the artifact `a` compiled from `doc`. -/
def ArtifactSound (doc : Codec.Document) (a : Artifact) : Prop :=
  minArgSize ≤ a.argSize ∧
    ∀ (S : X86.Backend.Space) (exit : X86.Word) (E0 : Nat), Loaded a S exit E0 →
      ∀ (args : List String), ArgsOk args →
      ∀ (saved : X86.Reg → X86.Word) (init : X86.State) (o : Obs),
        MachineBeh a S exit E0 saved init args o → Allowed doc args o

theorem soundSpec_iff (c : Codec.Document → Option Artifact) :
    SoundSpec c ↔ ∀ doc a, c doc = some a → ArtifactSound doc a := Iff.rfl

/-- A proved fragment: a partial compiler and the soundness of what it produces. -/
structure Fragment where
  compile : Codec.Document → Option Artifact
  sound : ∀ doc a, compile doc = some a → ArtifactSound doc a

namespace Fragment

/-- The first fragment of the list that accepts the document. -/
def first : List Fragment → Codec.Document → Option Artifact
  | [], _ => none
  | f :: fs, doc =>
    match f.compile doc with
    | some a => some a
    | none => first fs doc

/-- **Soundness of every list of fragments.** -/
theorem first_sound : (fs : List Fragment) → SoundSpec (first fs)
  | [], _, _, h => by cases h
  | f :: fs, doc, a, h => by
    unfold first at h
    split at h
    · cases h
      exact f.sound doc a ‹_›
    · exact first_sound fs doc a h

/-- The exit status of the 64-bit word of `n` is the status of `n`. -/
theorem status_ofInt (n : Int) : (BitVec.ofInt 64 n).toNat % 256 = (n % 256).toNat := by
  rw [BitVec.toNat_ofInt]
  omega

/-- Every artifact of the backend reserves the specification's argument area. -/
theorem argSize_ok {l : Mir.Linked} {a : Artifact} (h : artifactOf l = .ok a) :
    minArgSize ≤ a.argSize := by
  rw [(ConstLink.artifact_layout h).2.1]
  decide

theorem toOption_ok {l : Mir.Linked} {a : Artifact} (h : (artifactOf l).toOption = some a) :
    artifactOf l = .ok a := by
  revert h
  cases artifactOf l <;> simp [Except.toOption]

/-! ## Constant fragments -/

/-- `recognize`'s integer is the exit status of `main` for every argument list. -/
def ConstSound (recognize : Codec.Document → Option Int) : Prop :=
  ∀ doc n, recognize doc = some n → ∀ args, CoreBeh doc args (.exit (n % 256).toNat [])

def constCompile (recognize : Codec.Document → Option Int) (doc : Codec.Document) :
    Option Artifact :=
  match recognize doc with
  | some n => (artifactOf (ConstLink.link (BitVec.ofInt 64 n))).toOption
  | none => none

theorem constCompile_sound {recognize : Codec.Document → Option Int}
    (hs : ConstSound recognize) (doc : Codec.Document) (a : Artifact)
    (h : constCompile recognize doc = some a) : ArtifactSound doc a := by
  unfold constCompile at h
  split at h
  · rename_i n hn
    have ha := toOption_ok h
    refine ⟨argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases ConstLink.link_sound ha hl hb with rfl | rfl
    · exact .inl rfl
    · rw [status_ofInt]
      exact .inr (.inr (hs doc n hn args))
  · cases h

/-- The fragment that returns `recognize`'s integer (`ConstLink.link`). -/
def ofConst (recognize : Codec.Document → Option Int) (hs : ConstSound recognize) : Fragment where
  compile := constCompile recognize
  sound := constCompile_sound hs

/-! ## Straight-line register fragments -/

/-- For every argument list, Core reaches undefined behaviour from `doc`, or `ops` leave a word
`w` in register `r` from every frame without touching the memory and `main` exits with `w`. -/
def OpsSound {α : Type} (recognize : Codec.Document → Option α)
    (ops : α → List (Lir.Op Mir.Reg)) (r : α → Mir.Reg) : Prop :=
  ∀ doc x, recognize doc = some x → ∀ args, CoreUB doc args ∨
    ∃ w : Lir.Word, (∀ fr0 mem, ∃ fr, Lir.execOps (ops x) fr0 mem = some (fr, mem) ∧
      fr.get (r x) = some w) ∧ CoreBeh doc args (.exit (w.toNat % 256) [])

def opsCompile {α : Type} (recognize : Codec.Document → Option α)
    (ops : α → List (Lir.Op Mir.Reg)) (r : α → Mir.Reg) (doc : Codec.Document) :
    Option Artifact :=
  match recognize doc with
  | some x => (artifactOf (OpsLink.link (ops x) (r x))).toOption
  | none => none

theorem opsCompile_sound {α : Type} {recognize : Codec.Document → Option α}
    {ops : α → List (Lir.Op Mir.Reg)} {r : α → Mir.Reg} (hs : OpsSound recognize ops r)
    (doc : Codec.Document) (a : Artifact) (h : opsCompile recognize ops r doc = some a) :
    ArtifactSound doc a := by
  unfold opsCompile at h
  split at h
  · rename_i x hx
    have ha := toOption_ok h
    refine ⟨argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases hs doc x hx args with ub | ⟨w, hexec, beh⟩
    · exact .inr (.inl ub)
    · rcases OpsLink.link_sound hexec ha hl hb with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inr beh)
  · cases h

/-- The fragment that runs `ops x` and returns register `r x` (`OpsLink.link`). -/
def ofOps {α : Type} (recognize : Codec.Document → Option α) (ops : α → List (Lir.Op Mir.Reg))
    (r : α → Mir.Reg) (hs : OpsSound recognize ops r) : Fragment where
  compile := opsCompile recognize ops r
  sound := opsCompile_sound hs

end Fragment

end Silmaril.Compile.Core.Verified
