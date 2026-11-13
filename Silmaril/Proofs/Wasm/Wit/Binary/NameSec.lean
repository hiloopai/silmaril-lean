module

public import Silmaril.Wasm.Wit.Binary.NameSec.Defs
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# The `component-name` section reads back

`parseNameSec_encode : encodeNameSubs subs = some l → parseNameSec ⟨l.toArray⟩ = .ok subs`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary
open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Binary (Seq)

instance lawful_nameAssocG : nameAssocG.Lawful := by unfold nameAssocG; grammar_lawful
instance lawful_nameMapG : nameMapG.Lawful := by unfold nameMapG; grammar_lawful
instance lawful_nameSubG : nameSubG.Lawful := by grammar_lawful
instance lawful_nameSecG : nameSecG.Lawful := by unfold nameSecG; grammar_lawful

theorem nameAssoc_G {p : Nat × String} {l : Bytes} (h : nameAssocEnc p = some l) : nameAssocG.G l p := by
  simp only [nameAssocEnc, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact seq_G (Silmaril.Parse.ByteParse.Enc.u32_G ha) (Silmaril.Parse.ByteParse.Enc.name_G hb)

theorem nameSub_G {s : NameSub} {l : Bytes} (h : s.encode = some l) : nameSubG.G l s := by
  cases s with
  | component n =>
    simp only [NameSub.encode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, s, hs, rfl⟩ := h
    obtain ⟨nb, rfl, hn⟩ := Silmaril.Parse.ByteParse.Enc.sized_parts hs
    exact tagged_G _ rfl (map_G (sizedBy_G hn (Silmaril.Parse.ByteParse.Enc.name_G hb)))
  | sort srt ns =>
    simp only [NameSub.encode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨m, hm, s, hs, rfl⟩ := h
    obtain ⟨nb, rfl, hn⟩ := Silmaril.Parse.ByteParse.Enc.sized_parts hs
    have hv : nameMapG.G m ns :=
      Silmaril.Parse.ByteParse.Enc.vec_G (hne := seq_nonEmpty u32_nonEmpty) (fun _ _ _ hp => nameAssoc_G hp) hm
    exact tagged_G _ rfl (map_G (f := fun p => NameSub.sort p.1 p.2) (a := (srt, ns))
      (sizedBy_G hn (seq_G (RoundTrip.sort_G srt) hv)))

theorem nameSubs_G : ∀ {ss : List NameSub} {l : Bytes}, encodeNameSubs ss = some l → Seq nameSubG.G l ss
  | [], l, h => by simp only [encodeNameSubs, Option.some.injEq] at h; subst h; exact Seq.nil
  | s :: ss, l, h => by
    simp only [encodeNameSubs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact Seq.cons (nameSub_G ha) (nameSubs_G hb)

/-- **The component-name section reads back.** -/
theorem parseNameSec_encode {ss : List NameSub} {l : Bytes} (h : encodeNameSubs ss = some l) :
    parseNameSec ⟨l.toArray⟩ = .ok ss :=
  GrammarE.runAll_complete nameSecG (GrammarE.items_G (nameSubs_G h))

end Silmaril.Wasm.Wit.Binary
