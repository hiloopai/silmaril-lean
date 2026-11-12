module

public import Silmaril.Wasm.Component.Binary.Framing.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Parse.ByteParse.Thms

/-!
# Silmaril.Wasm.Binary.Section framing: soundness, completeness, silmaril's section grammar

Statements in the shape of silmaril's `decode?_sound`
(`Silmaril.Wasm.Binary.Core.DecodeSound`): a successful run explains the
whole input by the grammar, here the preamble followed by `RawSection`s, and
`RawSection` is silmaril's `Section id` production. Completeness is the
converse.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary.Framing

open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Binary (Seq U32 Section)

instance lawful_rawSectionG : rawSectionG.Lawful := by grammar_lawful

instance lawful_framingG (pre : List UInt8) : (framingG pre).Lawful := by
  unfold framingG
  grammar_lawful

theorem rawSectionG_iff {l : Bytes} {s : RawSection} : rawSectionG.G l s ↔ RawSection.G l s := by
  constructor
  · rintro ⟨l₁, l₂, id, rfl, rfl, body, ⟨l₃, l₄, n, rfl, hn, rfl, hl⟩, rfl⟩
    exact ⟨l₃, by simp, by rw [Silmaril.Parse.ByteParse.size_eq_length]; exact hl ▸ hn⟩
  · rintro ⟨lb, rfl, hn⟩
    refine ⟨[s.id], lb ++ s.body.data.toList, s.id, by simp, rfl, s.body,
      ⟨lb, s.body.data.toList, s.body.size, rfl, hn, rfl, ?_⟩, rfl⟩
    exact (Silmaril.Parse.ByteParse.size_eq_length _).symm

/-- `RawSection` is silmaril's `Section id` with the body as its one item. -/
theorem rawSection_iff_section {l : Bytes} {s : RawSection} :
    RawSection.G l s ↔ Silmaril.Wasm.Binary.Section s.id (fun c xs => xs = [c]) l [s.body.data.toList] := by
  constructor
  · rintro ⟨lb, rfl, hn⟩
    exact Silmaril.Wasm.Binary.Section.mk hn (Silmaril.Parse.ByteParse.size_eq_length _) rfl
  · intro h
    cases h with
    | mk hl hlen hc =>
      rename_i lb c len
      injection hc with hc
      subst hc
      exact ⟨lb, rfl, by rw [Silmaril.Parse.ByteParse.size_eq_length, ← hlen]; exact hl⟩

theorem seq_rawSection {l : Bytes} {xs : List RawSection} :
    Seq rawSectionG.G l xs → Seq RawSection.G l xs := by
  intro h
  induction h with
  | nil => exact Seq.nil
  | cons hg _ ih => exact Seq.cons (rawSectionG_iff.mp hg) ih

theorem seq_rawSectionG {l : Bytes} {xs : List RawSection} :
    Seq RawSection.G l xs → Seq rawSectionG.G l xs := by
  intro h
  induction h with
  | nil => exact Seq.nil
  | cons hg _ ih => exact Seq.cons (rawSectionG_iff.mpr hg) ih

theorem lit_G_inv : ∀ {pre l : List UInt8} {u : Unit}, (lit pre).G l u → l = pre
  | [], _, _, hp => hp.1
  | _ :: _, _, _, ⟨_, _, _, rfl, rfl, hm⟩ => by rw [lit_G_inv hm]; rfl

theorem framing_sound {pre : List UInt8} {b : ByteArray} {secs : List RawSection}
    (h : Silmaril.Parse.ByteParse.runAll (framingG pre).parse b = .ok secs) :
    ∃ rest, b.data.toList = pre ++ rest ∧ Seq RawSection.G rest secs := by
  obtain ⟨l₁, l₂, u, he, hp, hx⟩ := GrammarE.runAll_sound _ h
  refine ⟨l₂, ?_, seq_rawSection hx⟩
  rw [he, lit_G_inv hp]

theorem framing_complete {pre rest : List UInt8} {secs : List RawSection}
    (h : Seq RawSection.G rest secs) :
    Silmaril.Parse.ByteParse.runAll (framingG pre).parse ⟨(pre ++ rest).toArray⟩ = .ok secs :=
  GrammarE.runAll_complete _ (GrammarE.after_G (lit_G pre) (GrammarE.items_G (seq_rawSectionG h)))

/-- **Soundness** of core framing, in the shape of silmaril's `decode?_sound`. -/
theorem coreFraming_sound {b : ByteArray} {secs : List RawSection} (h : coreFraming b = .ok secs) :
    ∃ rest, b.data.toList = Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version ++ rest ∧
      ∀ s ∈ secs, ∃ l, Silmaril.Wasm.Binary.Section s.id (fun c xs => xs = [c]) l [s.body.data.toList] := by
  obtain ⟨rest, h1, h2⟩ := framing_sound h
  refine ⟨rest, h1, ?_⟩
  intro s hs
  clear h1 h
  induction h2 with
  | nil => simp at hs
  | @cons l₁ _ a _ hg _ ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨l₁, rawSection_iff_section.mp hg⟩
    · exact ih hs

/-- **Completeness** of core framing. -/
theorem coreFraming_complete {rest : List UInt8} {secs : List RawSection}
    (h : Seq RawSection.G rest secs) : coreFraming ⟨(corePreamble ++ rest).toArray⟩ = .ok secs :=
  framing_complete h

/-- Open (frozen): every module that silmaril's core decoder accepts is framed.
This needs the section structure of silmaril's `Encodes`; nothing here
depends on it. -/
def Task.coreFraming_of_decode : Prop :=
  ∀ (b : ByteArray) (m : Silmaril.Wasm.Module), Silmaril.Wasm.Binary.Core.decode? b = some m →
    ∃ secs, coreFraming b = .ok secs

end Silmaril.Wasm.Component.Binary.Framing
