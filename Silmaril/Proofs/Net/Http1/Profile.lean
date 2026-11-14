module

public import Silmaril.Net.Http1.Profile.Defs
public import Silmaril.Net.Http1.Framing.Thms

/-! Proofs for `Silmaril.Net.Http1.Profile.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http1.Proofs.Profile

open Silmaril.Net.Http1
open Silmaril.Parse.ByteParse

theorem clFrame_strict (p : Profile) (hp : p.dupCl = .strict) (fs : List FieldLine) :
    p.clFrame fs = match contentLength? fs with
      | none => .invalid | some none => .none | some (some n) => .length n := by
  obtain ⟨a, b, c, d, e⟩ := p
  cases hp
  rfl

theorem frame_compliant {p : Profile} (hp : p.Compliant) (v : Version) (fs : List FieldLine) :
    p.SafeOn v fs := by
  have hcl := clFrame_strict p hp.2.1 fs
  obtain ⟨p1, p2, p3, p4, p5⟩ := p
  obtain ⟨h1, h2, rfl, rfl, rfl⟩ := hp
  unfold Profile.SafeOn Profile.frame rfcRequestFraming requestBodyLength bodyLengthOfFields
  rw [hcl]
  cases htc : transferCodings fs with
  | nil => exact Or.inl rfl
  | cons t ts =>
    simp only [List.isEmpty_cons, Bool.false_or, Bool.not_false, Bool.true_and, Bool.and_true,
      Profile.teChunked, Bool.false_eq_true, ite_false, htc]
    by_cases hv : v.is10 = true
    · simp [hv]
    · simp only [hv, ite_false, Bool.false_eq_true]
      split
      · split <;> simp_all
      · cases p1 <;> simp_all

theorem mem_all (p : Profile) : p ∈ Profile.all := by
  obtain ⟨a, b, c, d, e⟩ := p
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem all_witnessed :
    ∀ p ∈ Profile.all, p.Compliant ∨ ∃ w ∈ violationWitnesses, ¬ p.SafeOn w.1 w.2 := by
  decide

theorem compliant_iff_safe (p : Profile) : (∀ v fs, p.SafeOn v fs) ↔ p.Compliant := by
  refine ⟨fun h => ?_, fun hp v fs => frame_compliant hp v fs⟩
  rcases all_witnessed p (mem_all p) with hc | ⟨w, -, hw⟩
  · exact hc
  · exact absurd (h w.1 w.2) hw

theorem parseBody_invalid (bs : ByteArray) (j : Nat) :
    ∃ e, parseBody .invalid bs j = .err e := ⟨_, rfl⟩

theorem parseRequestWith_compliant_agree {p q : Profile} (hp : p.Compliant) (hq : q.Compliant)
    {bs : ByteArray} {i k k' : Nat} {r r' : RequestHead × Body}
    (h₁ : parseRequestWith p bs i = .ok r k) (h₂ : parseRequestWith q bs i = .ok r' k') :
    r = r' ∧ k = k' := by
  unfold parseRequestWith at h₁ h₂
  split at h₁
  · cases h₁
  · next h j hh =>
    rw [hh] at h₂
    simp only at h₁ h₂
    have key : ∀ {s : Profile} {rr : RequestHead × Body} {kk : Nat}, s.Compliant →
        (match parseBody (s.frame h.line.version h.fields) bs j with
          | .ok b k => Res.ok (h, b) k
          | .err e => .err e) = .ok rr kk →
        (match parseBody (rfcRequestFraming h.line.version h.fields) bs j with
          | .ok b k => Res.ok (h, b) k
          | .err e => .err e) = .ok rr kk := by
      intro s rr kk hs hr
      rcases frame_compliant hs h.line.version h.fields with he | he
      · rwa [he] at hr
      · rw [he] at hr; cases hr
    have a₁ := key hp h₁
    have a₂ := key hq h₂
    rw [a₁] at a₂
    cases a₂
    exact ⟨rfl, rfl⟩

theorem parseRequestWith_encode (p : Profile) {h : RequestHead} {b : Body} (hv : h.Valid)
    (hb : b.Fits (p.frame h.line.version h.fields)) (pre rest : Bytes) :
    parseRequestWith p ⟨(pre ++ encRequest h b ++ rest).toArray⟩ pre.length =
      .ok (h, b) (pre.length + (encRequest h b).length) := by
  have e₁ : pre ++ encRequest h b ++ rest = pre ++ encRequestHead h ++ (encBody b ++ rest) := by
    simp [encRequest]
  have e₂ : pre ++ encRequest h b ++ rest = (pre ++ encRequestHead h) ++ encBody b ++ rest := by
    simp [encRequest]
  have hh := requestHead_at hv pre (encBody b ++ rest)
  have hbody := parseBody_encode hb (pre ++ encRequestHead h) rest
  rw [← e₁] at hh
  rw [← e₂] at hbody
  simp only [List.length_append] at hbody
  unfold parseRequestWith
  rw [size_ofList, hh]
  simp only [hbody]
  simp only [encRequest, List.length_append, Nat.add_assoc]

theorem parseRequestWith_invalid (p : Profile) {h : RequestHead} (hv : h.Valid)
    (hf : p.frame h.line.version h.fields = .invalid) (rest : Bytes) :
    ∃ e, parseRequestWith p ⟨(encRequestHead h ++ rest).toArray⟩ 0 = .err e := by
  have hh := requestHead_at hv [] rest
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hh
  unfold parseRequestWith
  rw [size_ofList, hh]
  simp only [hf]
  exact ⟨_, rfl⟩

/-! ## The witnesses -/

theorem clteHead_valid : clteHead.Valid := by decide
theorem teteHead_valid : teteHead.Valid := by decide

theorem encChunked_empty : encChunked emptyChunked = [0x30, CR, LF, CR, LF] := by
  simp only [encChunked, emptyChunked, encChunkLine, List.map_nil, List.flatten_nil,
    List.nil_append, encFields]
  rw [hexDigits]
  decide

/-- The body a CL front end reads: the six octets `0 CRLF CRLF G`. -/
def clBody : Body := .content (encChunked emptyChunked ++ ascii "G")

theorem clBody_fits : clBody.Fits (.length 6) := by
  show (encChunked emptyChunked ++ ascii "G").length = 6
  rw [encChunked_empty]; decide

theorem emptyChunked_fits : (Body.chunked emptyChunked).Fits .chunked := by
  show emptyChunked.Valid
  decide

theorem length_clBody (h : RequestHead) :
    (encRequest h clBody).length = (encRequest h (.chunked emptyChunked)).length + 1 := by
  simp only [encRequest, encBody, clBody, List.length_append, encChunked_empty]
  have : (ascii "G").length = 1 := by decide
  omega

theorem clteOctets_cl : clteOctets = [] ++ encRequest clteHead clBody ++ [] := by
  simp [clteOctets, encRequest, encBody, clBody]

theorem clteOctets_te :
    clteOctets = [] ++ encRequest clteHead (.chunked emptyChunked) ++ ascii "G" := by
  simp [clteOctets, encRequest, encBody]

theorem teteOctets_cl : teteOctets = [] ++ encRequest teteHead clBody ++ [] := by
  simp [teteOctets, encRequest, encBody, clBody]

theorem teteOctets_te :
    teteOctets = [] ++ encRequest teteHead (.chunked emptyChunked) ++ ascii "G" := by
  simp [teteOctets, encRequest, encBody]

theorem desync_clte :
    parseRequestWith Profile.clWins ⟨clteOctets.toArray⟩ 0 =
        .ok (clteHead, clBody) (encRequest clteHead clBody).length ∧
      parseRequestWith Profile.teWins ⟨clteOctets.toArray⟩ 0 =
        .ok (clteHead, .chunked emptyChunked) (encRequest clteHead (.chunked emptyChunked)).length ∧
      (encRequest clteHead clBody).length =
        (encRequest clteHead (.chunked emptyChunked)).length + 1 := by
  have f₁ : Profile.clWins.frame clteHead.line.version clteHead.fields = .length 6 := by decide
  have f₂ : Profile.teWins.frame clteHead.line.version clteHead.fields = .chunked := by decide
  refine ⟨?_, ?_, length_clBody _⟩
  · have := parseRequestWith_encode Profile.clWins clteHead_valid (b := clBody)
      (by rw [f₁]; exact clBody_fits) [] []
    rw [clteOctets_cl]; simpa using this
  · have := parseRequestWith_encode Profile.teWins clteHead_valid (b := .chunked emptyChunked)
      (by rw [f₂]; exact emptyChunked_fits) [] (ascii "G")
    rw [clteOctets_te]; simpa using this

theorem strict_rejects_clte :
    ∃ e, parseRequestWith Profile.strict ⟨clteOctets.toArray⟩ 0 = .err e := by
  have := parseRequestWith_invalid Profile.strict clteHead_valid (by decide)
    (encChunked emptyChunked ++ ascii "G")
  simpa [clteOctets] using this

theorem desync_tete :
    parseRequestWith Profile.teSubstring ⟨teteOctets.toArray⟩ 0 =
        .ok (teteHead, .chunked emptyChunked) (encRequest teteHead (.chunked emptyChunked)).length ∧
      parseRequestWith Profile.teIgnored ⟨teteOctets.toArray⟩ 0 =
        .ok (teteHead, clBody) (encRequest teteHead clBody).length ∧
      (encRequest teteHead clBody).length =
        (encRequest teteHead (.chunked emptyChunked)).length + 1 := by
  have f₁ : Profile.teSubstring.frame teteHead.line.version teteHead.fields = .chunked := by decide
  have f₂ : Profile.teIgnored.frame teteHead.line.version teteHead.fields = .length 6 := by decide
  refine ⟨?_, ?_, length_clBody _⟩
  · have := parseRequestWith_encode Profile.teSubstring teteHead_valid (b := .chunked emptyChunked)
      (by rw [f₁]; exact emptyChunked_fits) [] (ascii "G")
    rw [teteOctets_te]; simpa using this
  · have := parseRequestWith_encode Profile.teIgnored teteHead_valid (b := clBody)
      (by rw [f₂]; exact clBody_fits) [] []
    rw [teteOctets_cl]; simpa using this

theorem teWins_rejects_tete :
    ∃ e, parseRequestWith Profile.teWins ⟨teteOctets.toArray⟩ 0 = .err e := by
  have := parseRequestWith_invalid Profile.teWins teteHead_valid (by decide)
    (encChunked emptyChunked ++ ascii "G")
  simpa [teteOctets] using this

end Silmaril.Net.Http1.Proofs.Profile
