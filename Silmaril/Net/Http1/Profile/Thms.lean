module

public import Silmaril.Net.Http1.Profile.Defs
public import Silmaril.Net.Http1.Framing.Defs
import Silmaril.Proofs.Net.Http1.Profile

/-!
# Recipient profiles and request smuggling: laws

Proofs in `Silmaril/Proofs/Net/Http1/Profile.lean`.

* `frame_compliant`: a compliant profile frames like the reference or rejects.
* `compliant_iff_safe`: a profile never accepts a request with a framing other than the
  reference one **iff** it is compliant (each noncompliant knob has a witness request).
* `parseRequestWith_compliant_agree`: two compliant recipients reading the same octets agree
  on the first request and its end, or one rejects. So compliant recipients never
  desynchronise (`compliant_no_desync`).
* `parseRequestWith_encode`: a valid head whose body fits the profile's framing is read back.
* `desync_clte`: on the CL.TE octets, a `Content-Length`-first front end (`Profile.clWins`)
  reads a 6-octet body while a compliant back end (`Profile.teWins`) reads a 5-octet chunked
  body and leaves `G` as the start of a smuggled request; `strict_rejects_clte`: the
  strict profile rejects these octets.
* `desync_tete`: with `Transfer-Encoding: xchunked`, a substring-matching front end and a
  back end without `Transfer-Encoding` support disagree in the same way;
  `teWins_rejects_tete`: a compliant recipient rejects.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

theorem frame_compliant {p : Profile} (hp : p.Compliant) (v : Version) (fs : List FieldLine) :
    p.SafeOn v fs := Proofs.Profile.frame_compliant hp v fs

theorem compliant_iff_safe (p : Profile) : (∀ v fs, p.SafeOn v fs) ↔ p.Compliant :=
  Proofs.Profile.compliant_iff_safe p

theorem parseRequestWith_compliant_agree {p q : Profile} (hp : p.Compliant) (hq : q.Compliant)
    {bs : ByteArray} {i k k' : Nat} {r r' : RequestHead × Body}
    (h₁ : parseRequestWith p bs i = .ok r k) (h₂ : parseRequestWith q bs i = .ok r' k') :
    r = r' ∧ k = k' := Proofs.Profile.parseRequestWith_compliant_agree hp hq h₁ h₂

theorem compliant_no_desync {p q : Profile} (hp : p.Compliant) (hq : q.Compliant)
    (bs : ByteArray) : ¬ Desync p q bs := by
  rintro ⟨r, r', k, k', h₁, h₂, hne⟩
  exact hne (parseRequestWith_compliant_agree hp hq h₁ h₂).2

theorem parseRequestWith_encode (p : Profile) {h : RequestHead} {b : Body} (hv : h.Valid)
    (hb : b.Fits (p.frame h.line.version h.fields)) (pre rest : Bytes) :
    parseRequestWith p ⟨(pre ++ encRequest h b ++ rest).toArray⟩ pre.length =
      .ok (h, b) (pre.length + (encRequest h b).length) :=
  Proofs.Profile.parseRequestWith_encode p hv hb pre rest

theorem desync_clte : Desync Profile.clWins Profile.teWins ⟨clteOctets.toArray⟩ := by
  obtain ⟨h₁, h₂, hl⟩ := Proofs.Profile.desync_clte
  exact ⟨_, _, _, _, h₁, h₂, by omega⟩

theorem strict_rejects_clte :
    ∃ e, parseRequestWith Profile.strict ⟨clteOctets.toArray⟩ 0 = .err e :=
  Proofs.Profile.strict_rejects_clte

theorem desync_tete : Desync Profile.teSubstring Profile.teIgnored ⟨teteOctets.toArray⟩ := by
  obtain ⟨h₁, h₂, hl⟩ := Proofs.Profile.desync_tete
  exact ⟨_, _, _, _, h₁, h₂, by omega⟩

theorem teWins_rejects_tete :
    ∃ e, parseRequestWith Profile.teWins ⟨teteOctets.toArray⟩ 0 = .err e :=
  Proofs.Profile.teWins_rejects_tete

theorem strict_compliant : Profile.strict.Compliant := by decide
theorem teWins_compliant : Profile.teWins.Compliant := by decide
theorem clWins_not_compliant : ¬ Profile.clWins.Compliant := by decide
theorem teSubstring_not_compliant : ¬ Profile.teSubstring.Compliant := by decide
theorem teIgnored_not_compliant : ¬ Profile.teIgnored.Compliant := by decide

end Silmaril.Net.Http1
