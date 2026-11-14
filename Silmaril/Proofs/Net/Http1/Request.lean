module

public import Silmaril.Net.Http1.Request.Defs
public import Silmaril.Net.Http1.Profile.Thms
public import Silmaril.Net.Http1.Message.Thms

/-! Proofs for `Silmaril.Net.Http1.Request.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http1.Proofs.Request

open Silmaril.Net.Http1
open Silmaril.Parse.ByteParse (Bytes)

theorem checkFraming_ok {cfg : ServerConfig} {v : Version} {m : Bytes} {form : TargetForm}
    {fs : List FieldLine} {t host : Bytes} {c : Context}
    (hc : checkRequest.checkFraming cfg v m form fs t host = .ok c) :
    c.form = form ∧ c.framing = cfg.profile.frame v fs ∧ c.framing ≠ .invalid ∧
      checkCodings cfg.implements (transferCodings fs) = .ok ∧ c.method = Http.Method.ofToken m ∧
      c.persistent = (persists cfg.keepAlive v fs && !framingForcesClose v fs) := by
  unfold checkRequest.checkFraming at hc
  simp only at hc
  split at hc
  · cases hc
  next h₁ =>
  split at hc
  · cases hc
  · cases hc
  · cases hc
  · next hk => cases hc; exact ⟨rfl, rfl, h₁, hk, rfl, rfl⟩

theorem checkRequest_ok {cfg : ServerConfig} {h : RequestHead} {c : Context}
    (hc : checkRequest cfg h = .ok c) : Accepted cfg h c := by
  unfold checkRequest at hc
  simp only at hc
  split at hc
  · cases hc
  next h₁ =>
  split at hc
  · cases hc
  next form hform =>
  split at hc
  · cases hc
  next h₂ =>
  split at hc
  · next hh =>
    split at hc
    · cases hc
    · next h₃ =>
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := checkFraming_ok hc
      subst e₁
      exact ⟨by omega, hform, by simpa using h₂, ⟨[], Or.inr ⟨hh, by simpa using h₃⟩⟩, e₂, e₃, e₄,
        e₅, e₆⟩
  · next host hh =>
    split at hc
    · next h₃ =>
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := checkFraming_ok hc
      subst e₁
      exact ⟨by omega, hform, by simpa using h₂, ⟨host, Or.inl ⟨hh, h₃⟩⟩, e₂, e₃, e₄, e₅, e₆⟩
    · cases hc
  · cases hc

theorem checkRequest_connect {cfg : ServerConfig} {h : RequestHead} {c : Context}
    (hc : checkRequest cfg h = .ok c) : h.line.method = methodCONNECT ↔ c.form = .authority := by
  have a := checkRequest_ok hc
  have hf := a.fits
  constructor
  · intro hm
    cases hcf : c.form <;> rw [hcf, hm] at hf
    all_goals exact absurd hf (by decide)
  · intro hcf
    rw [hcf] at hf
    simpa [formFits] using hf

theorem fieldValues_mergeTrailers {hs ts : List FieldLine} {n : Bytes}
    (hn : lower n ∈ trailerForbidden) : fieldValues (mergeTrailers hs ts) n = fieldValues hs n := by
  unfold mergeTrailers fieldValues
  rw [List.filterMap_append]
  suffices hnil : (ts.filter trailerMergeable).filterMap
      (fun f => if lower f.name = lower n then some f.value else none) = [] by
    rw [hnil, List.append_nil]
  rw [List.filterMap_eq_nil_iff]
  intro f hf
  rw [List.mem_filter] at hf
  split
  · next he =>
    have := hf.2
    simp only [trailerMergeable, he, Bool.not_eq_true'] at this
    simp at this
    exact absurd hn this
  · rfl

/-! ## Field predicates of the two tracks agree -/

theorem isTchar_eq : ∀ b : UInt8, Http.Field.isTchar b = isTchar b := by decide
theorem isFieldChar_eq : ∀ b : UInt8, Http.Field.isFieldChar b = isFieldByte b := by decide
theorem isFieldVchar_iff : ∀ b : UInt8, isFieldByte b = true →
    (Http.Field.isFieldVchar b = (!isWS b)) := by decide

theorem isToken_iff (l : Bytes) : Http.Field.isToken l = true ↔ IsToken l := by
  unfold Http.Field.isToken IsToken
  simp [isTchar_eq]

theorem isFieldValue_iff (l : Bytes) : Http.Field.isFieldValue l = true ↔ IsFieldValue l := by
  unfold Http.Field.isFieldValue IsFieldValue
  simp only [Bool.and_eq_true, List.all_eq_true, isFieldChar_eq]
  constructor
  · rintro ⟨⟨ha, hh⟩, hl⟩
    refine ⟨ha, fun b hb => ?_, fun b hb => ?_⟩
    · have hb' := ha b (List.mem_of_mem_head? hb)
      have := isFieldVchar_iff b hb'
      simp only [Option.all_eq_true] at hh
      have := hh b hb
      simp_all
    · have hb' := ha b (List.mem_of_mem_getLast? hb)
      have := isFieldVchar_iff b hb'
      simp only [Option.all_eq_true] at hl
      have := hl b hb
      simp_all
  · rintro ⟨ha, hh, hl⟩
    refine ⟨⟨ha, ?_⟩, ?_⟩
    · simp only [Option.all_eq_true]
      intro b hb
      rw [isFieldVchar_iff b (ha b (List.mem_of_mem_head? hb)), hh b hb]; rfl
    · simp only [Option.all_eq_true]
      intro b hb
      rw [isFieldVchar_iff b (ha b (List.mem_of_mem_getLast? hb)), hl b hb]; rfl

theorem toLine_isValid (f : FieldLine) : f.toLine.isValid = true ↔ f.Valid := by
  unfold FieldLine.toLine Http.Field.Line.isValid FieldLine.Valid
  simp [isToken_iff, isFieldValue_iff]

theorem ofToken_toToken (t : Bytes) : (Http.Method.ofToken t).toToken = t := by
  unfold Http.Method.ofToken
  split
  · next m hm =>
    have := List.find?_some hm
    simpa using this
  · rfl

theorem toRequest_isValid {h : RequestHead} {b : Body} {c : Context} (hv : h.Valid)
    (ht : ∀ f ∈ b.trailers, f.Valid) (hm : c.method = Http.Method.ofToken h.line.method) :
    (toRequest h b c).isValid = true := by
  unfold Http.Request.isValid Http.Message.fieldsValid Http.Request.method
  simp only [toRequest, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]; unfold Http.Method.isValid; rw [ofToken_toToken, isToken_iff]; exact hv.1.1
  · unfold Http.Field.Section.isValid
    simp only [List.all_map, List.all_eq_true, Function.comp_apply]
    exact fun f hf => (toLine_isValid f).2 (hv.2 f hf)
  · unfold Http.Field.Section.isValid
    simp only [List.all_map, List.all_eq_true, Function.comp_apply]
    exact fun f hf => (toLine_isValid f).2 (ht f hf)

end Silmaril.Net.Http1.Proofs.Request
