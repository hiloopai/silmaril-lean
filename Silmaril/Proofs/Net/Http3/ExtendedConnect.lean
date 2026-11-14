module

public import Silmaril.Net.Http3.ExtendedConnect.Defs

/-!
# Extended CONNECT: proofs

For `Silmaril.Net.Http3.ExtendedConnect.Thms` (RFC 8441 §3–§4, RFC 9220 §3).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http3.ExtendedConnect

open Silmaril.Net.Hpack Silmaril.Net.Http2 Silmaril.Net.Http3

theorem exists_of_hasProtocol {fs : List Entry} (h : hasProtocol fs = true) :
    ∃ e ∈ fs, e.name = ascii ":protocol" := by
  simp only [hasProtocol, pseudoValues, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    ne_eq, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq] at h
  exact Classical.byContradiction fun hne => h fun e he hn => hne ⟨e, he, hn⟩

theorem validRequest_of_hasProtocol {fs : List Entry} (h : hasProtocol fs = true) :
    validRequest fs = false := by
  obtain ⟨e, he, hn⟩ := exists_of_hasProtocol h
  apply Bool.eq_false_iff.2
  intro hv
  simp only [validRequest, validSection, pseudoKnownOnce, Bool.and_eq_true, List.all_eq_true]
    at hv
  have hp : isPseudo e = true := by
    simp only [isPseudo, hn]; decide +kernel
  have hmem : e.name ∈ (fs.filter isPseudo).map Entry.name :=
    List.mem_map_of_mem (List.mem_filter.2 ⟨he, hp⟩)
  have := hv.1.1.2.1 _ hmem
  rw [hn] at this
  revert this; decide +kernel

theorem validRequestExt_disabled (fs : List Entry) : validRequestExt false fs = validRequest fs := by
  unfold validRequestExt
  cases h : hasProtocol fs
  · rfl
  · simp [validRequest_of_hasProtocol h, validExtendedConnect]

theorem validExtendedConnect_spec {en : Bool} {fs : List Entry}
    (h : validExtendedConnect en fs = true) :
    en = true ∧ pseudoValues fs ":method" = [ascii "CONNECT"] ∧ hasProtocol fs = true ∧
      (pseudoValues fs ":scheme").length = 1 ∧ (pseudoValues fs ":path").length = 1 := by
  simp only [validExtendedConnect, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hen, -⟩, hm⟩, hrest⟩ := h
  refine ⟨hen, hm, ?_⟩
  split at hrest
  · rename_i pr s p hpr hs hp
    simp [hasProtocol, hpr, hs, hp]
  · cases hrest

theorem pseudoValues_stripProtocol (fs : List Entry) (n : String)
    (hn : ascii n ≠ ascii ":protocol") :
    pseudoValues (stripProtocol fs) n = pseudoValues fs n := by
  unfold pseudoValues stripProtocol
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro e _
  cases h : e.name == ascii n
  · rfl
  · simp only [beq_iff_eq] at h
    simp [h, hn]

theorem validRequest_stripProtocol {en : Bool} {fs : List Entry}
    (h : validExtendedConnect en fs = true) : validRequest (stripProtocol fs) = false := by
  obtain ⟨-, hm, -, hs, -⟩ := validExtendedConnect_spec h
  have hm' := pseudoValues_stripProtocol fs ":method" (by decide +kernel)
  have hs' := pseudoValues_stripProtocol fs ":scheme" (by decide +kernel)
  rw [hm] at hm'
  unfold validRequest
  rw [hm']
  have : (pseudoValues (stripProtocol fs) ":scheme").isEmpty = false := by
    rw [hs']; cases hx : pseudoValues fs ":scheme" <;> simp_all
  simp [this]

end Silmaril.Proofs.Net.Http3.ExtendedConnect
