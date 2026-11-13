module

public import Silmaril.Net.Http1.Framing.Defs
public import Silmaril.Net.Http1.Chunked.Thms

/-!
# HTTP/1.1 message framing: laws

* `parseBody_encode`: a body that fits its announced framing is read back exactly;
* `parseRequestAt_encode`, `parseResponseAt_encode`: whole messages are read back after any
  prefix (earlier messages on the connection) and before any suffix (later ones);
* properties of the §6.3 rules: no body for `HEAD`, `1xx`, `204`, `304` responses;
  `Transfer-Encoding` ending in `chunked` overrides `Content-Length`; a request is never
  close-delimited or a tunnel.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

theorem parseBody_encode {len : BodyLength} {b : Body} (hb : b.Fits len) (pre rest : Bytes) :
    parseBody len ⟨(pre ++ encBody b ++ rest).toArray⟩ pre.length =
      .ok b (pre.length + (encBody b).length) := by
  match len, b, hb with
  | .none, .none, _ => simp [parseBody, encBody]
  | .length n, .content d, hd =>
    have hd' : d.length = n := hd
    subst hd'
    have hsz : pre.length + d.length ≤ (⟨(pre ++ d ++ rest).toArray⟩ : ByteArray).size := by
      rw [size_ofList]; simp only [List.length_append]; omega
    have hseg : (ByteArray.extract ⟨(pre ++ d ++ rest).toArray⟩ pre.length
        (pre.length + d.length)).data.toList = d := by
      rw [seg_extract, seg_middle]
    simp only [parseBody, encBody, hsz, ↓reduceIte, hseg]
  | .chunked, .chunked c, hc =>
    have h := parseChunked_encode (c := c) hc pre rest
    simp only [parseBody, encBody, h]

theorem requestHead_at {h : RequestHead} (hv : h.Valid) (pre rest : Bytes) :
    (Grammar.requestHead ((pre ++ encRequestHead h ++ rest).length + 1)).parse
      ⟨(pre ++ encRequestHead h ++ rest).toArray⟩ (pre ++ encRequestHead h ++ rest).length
      pre.length = .ok h (pre.length + (encRequestHead h).length) := by
  have hk : h.fields.length < (pre ++ encRequestHead h ++ rest).length + 1 := by
    have := length_encFields_gt h.fields
    simp [encRequestHead]; omega
  exact (Grammar.requestHead _).complete (Grammar.requestHead_G hv hk) (by simp)
    (by rw [size_ofList]) (seg_middle pre _ rest)

theorem responseHead_at {h : ResponseHead} (hv : h.Valid) (pre rest : Bytes) :
    (Grammar.responseHead ((pre ++ encResponseHead h ++ rest).length + 1)).parse
      ⟨(pre ++ encResponseHead h ++ rest).toArray⟩ (pre ++ encResponseHead h ++ rest).length
      pre.length = .ok h (pre.length + (encResponseHead h).length) := by
  have hk : h.fields.length < (pre ++ encResponseHead h ++ rest).length + 1 := by
    have := length_encFields_gt h.fields
    simp [encResponseHead]; omega
  exact (Grammar.responseHead _).complete (Grammar.responseHead_G hv hk) (by simp)
    (by rw [size_ofList]) (seg_middle pre _ rest)

/-- Round trip of a whole request on a connection: after any earlier octets `pre`, a valid
head whose body fits the framing it announces is read back, and the reader stops where the
next request starts. -/
theorem parseRequestAt_encode {h : RequestHead} {b : Body} (hv : h.Valid)
    (hb : b.Fits (requestBodyLength h.fields)) (pre rest : Bytes) :
    parseRequestAt ⟨(pre ++ encRequest h b ++ rest).toArray⟩ pre.length =
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
  unfold parseRequestAt
  rw [size_ofList, hh]
  simp only [hbody]
  simp only [encRequest, List.length_append, Nat.add_assoc]

theorem parseResponseAt_encode {method : Bytes} {h : ResponseHead} {b : Body} (hv : h.Valid)
    (hb : b.Fits (responseBodyLength method h.line.code h.fields)) (pre rest : Bytes) :
    parseResponseAt method ⟨(pre ++ encResponse h b ++ rest).toArray⟩ pre.length =
      .ok (h, b) (pre.length + (encResponse h b).length) := by
  have e₁ : pre ++ encResponse h b ++ rest = pre ++ encResponseHead h ++ (encBody b ++ rest) := by
    simp [encResponse]
  have e₂ : pre ++ encResponse h b ++ rest = (pre ++ encResponseHead h) ++ encBody b ++ rest := by
    simp [encResponse]
  have hh := responseHead_at hv pre (encBody b ++ rest)
  have hbody := parseBody_encode hb (pre ++ encResponseHead h) rest
  rw [← e₁] at hh
  rw [← e₂] at hbody
  simp only [List.length_append] at hbody
  unfold parseResponseAt
  rw [size_ofList, hh]
  simp only [hbody]
  simp only [encResponse, List.length_append, Nat.add_assoc]

/-- A request alone in a buffer. -/
theorem parseRequest_encode {h : RequestHead} {b : Body} (hv : h.Valid)
    (hb : b.Fits (requestBodyLength h.fields)) (rest : Bytes) :
    parseRequest ⟨(encRequest h b ++ rest).toArray⟩ = .ok (h, b) (encRequest h b).length := by
  unfold parseRequest
  simpa using parseRequestAt_encode hv hb [] rest

/-! ## The §6.3 rules -/

theorem responseBodyLength_HEAD (code : Nat) (fs : List FieldLine) :
    responseBodyLength methodHEAD code fs = .none := by
  simp [responseBodyLength]

theorem responseBodyLength_noContent {method : Bytes} {code : Nat} (fs : List FieldLine)
    (hc : code / 100 = 1 ∨ code = 204 ∨ code = 304) : responseBodyLength method code fs = .none := by
  simp [responseBodyLength, hc]

/-- `Transfer-Encoding` ending in `chunked` decides, whatever `Content-Length` says (rule 3:
"Transfer-Encoding overrides the Content-Length"). -/
theorem bodyLengthOfFields_chunked {fs : List FieldLine} {a c : BodyLength}
    (h : (transferCodings fs).getLast? = some chunkedName) : bodyLengthOfFields fs a c = .chunked := by
  unfold bodyLengthOfFields
  split
  · next he => rw [he] at h; cases h
  · simp [h]

/-- A request body is never delimited by closing the connection, and a request never opens a
tunnel (§6.3 rules 4 and 7: a request without framing headers has no body). -/
theorem requestBodyLength_framed (fs : List FieldLine) :
    requestBodyLength fs ≠ .close ∧ requestBodyLength fs ≠ .tunnel := by
  unfold requestBodyLength bodyLengthOfFields
  split
  · split <;> simp
  · split <;> simp

/-! ## Soundness of whole requests -/

/-- A body read under a framing other than close-delimited or tunnel fits that framing. -/
theorem parseBody_fits {len : BodyLength} {bs : ByteArray} {j k : Nat} {b : Body}
    (hc : len ≠ .close) (ht : len ≠ .tunnel) (hj : j ≤ bs.size) (hp : parseBody len bs j = .ok b k) :
    b.Fits len := by
  match len, hc, ht, hp with
  | .none, _, _, hp => cases hp; trivial
  | .length n, _, _, hp =>
    have hp' : (if j + n ≤ bs.size then Res.ok (Body.content (bs.extract j (j + n)).data.toList) (j + n)
        else .err ⟨j, .eof⟩) = .ok b k := hp
    split at hp'
    · next hn =>
      cases hp'
      show ((bs.extract j (j + n)).data.toList).length = n
      rw [seg_extract, length_seg]; omega
    · cases hp'
  | .chunked, _, _, hp =>
    have hp' : (match parseChunked bs j with
        | .ok c k => Res.ok (Body.chunked c) k
        | .err e => .err e) = .ok b k := hp
    split at hp'
    · next c k' hc' => cases hp'; exact (parseChunked_sound hj hc').2.2.1
    · cases hp'
  | .invalid, _, _, hp => cases hp

/-- Soundness of whole requests: a request read at `i` has a valid head and a body that fits
the framing the head announces; so serializing it again gives octets that read back to it
(`parseRequestAt_encode`). -/
theorem parseRequestAt_sound {bs : ByteArray} {i k : Nat} {h : RequestHead} {b : Body}
    (hi : i ≤ bs.size) (hp : parseRequestAt bs i = .ok (h, b) k) :
    h.Valid ∧ b.Fits (requestBodyLength h.fields) := by
  unfold parseRequestAt at hp
  split at hp
  · cases hp
  · next h' j hh =>
    obtain ⟨-, hj, hg⟩ := (Grammar.requestHead (bs.size + 1)).sound hi le_rfl hh
    split at hp
    · next b' k' hb =>
      cases hp
      exact ⟨Grammar.requestHead_valid hg, parseBody_fits (requestBodyLength_framed _).1
        (requestBodyLength_framed _).2 hj hb⟩
    · cases hp

/-- Reading, writing and reading again gives the same request. -/
theorem parseRequestAt_reencode {bs : ByteArray} {i k : Nat} {h : RequestHead} {b : Body}
    (hi : i ≤ bs.size) (hp : parseRequestAt bs i = .ok (h, b) k) (pre rest : Bytes) :
    parseRequestAt ⟨(pre ++ encRequest h b ++ rest).toArray⟩ pre.length =
      .ok (h, b) (pre.length + (encRequest h b).length) :=
  have hs := parseRequestAt_sound hi hp
  parseRequestAt_encode hs.1 hs.2 pre rest

end Silmaril.Net.Http1
