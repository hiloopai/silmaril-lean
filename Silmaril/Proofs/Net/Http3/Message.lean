module

public import Silmaril.Net.Http3.Message.Defs
import Silmaril.Net.Http.Method.Thms

/-!
# HTTP/3 messages: proofs

The mapping between HTTP/3 field lists and `Http.Request`/`Http.Response` is a round trip on
canonical messages (RFC 9114 §4.2, §4.3), for `Silmaril.Net.Http3.Message.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http3.Message

open Silmaril.Net.Hpack Silmaril.Net.Http2 Silmaril.Net.Http Silmaril.Net.Http3

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem parseStatus_statusDigits {s : Nat} (h : s < 1000) : parseStatus (statusDigits s) = some s := by
  have d1 : (0x30 + s / 100 % 10).toUInt8.toNat = 0x30 + s / 100 % 10 := by
    rw [toNat_toUInt8]; omega
  have d2 : (0x30 + s / 10 % 10).toUInt8.toNat = 0x30 + s / 10 % 10 := by
    rw [toNat_toUInt8]; omega
  have d3 : (0x30 + s % 10).toUInt8.toNat = 0x30 + s % 10 := by
    rw [toNat_toUInt8]; omega
  unfold parseStatus statusDigits
  have hc : ([(0x30 + s / 100 % 10).toUInt8, (0x30 + s / 10 % 10).toUInt8,
      (0x30 + s % 10).toUInt8].all fun d => 0x30 ≤ d && d ≤ 0x39) = true := by
    have h48 : (0x30 : UInt8).toNat = 48 := rfl
    have h57 : (0x39 : UInt8).toNat = 57 := rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
      UInt8.le_iff_toNat_le]
    rw [d1, d2, d3, h48, h57]
    omega
  simp only [hc, ↓reduceIte, d1, d2, d3, Option.some.injEq]
  omega

theorem toLine_ofLine (l : Field.Line) : toLine (ofLine l) = l := rfl

theorem map_toLine_ofLine (ls : List Field.Line) : (ls.map ofLine).map toLine = ls := by
  simp [Function.comp_def, toLine_ofLine]

theorem schemeOf_schemeBytes {sc : Scheme} (h : schemeCanonical sc) : schemeOf (schemeBytes sc) = sc := by
  cases sc with
  | http => rfl
  | https => rfl
  | other v => obtain ⟨h1, h2⟩ := h; simp [schemeOf, schemeBytes, h1, h2]

/-- A field whose name starts with a colon. -/
abbrev PseudoName (n : String) : Prop := (ascii n).head? = some colon

theorem find_regular {ls : List Field.Line} (hreg : ∀ l ∈ ls, validRegular (ofLine l) = true)
    {n : String} (hn : PseudoName n) :
    (ls.map ofLine).find? (·.name == ascii n) = none := by
  rw [List.find?_eq_none]
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
  have hv := hreg l hl
  simp only [validRegular, Bool.and_eq_true, Bool.not_eq_true'] at hv
  have hp : isPseudo (ofLine l) = false := hv.1.1.2
  intro heq
  simp only [beq_iff_eq] at heq
  unfold isPseudo at hp
  rw [heq, hn] at hp
  exact absurd hp (by decide)

theorem firstValue_requestFields (r : Request) (hreg : ∀ l ∈ r.headers, validRegular (ofLine l) = true)
    {n : String} (hn : PseudoName n) :
    firstValue (requestFields r) n = firstValue (requestPseudoFields r) n := by
  unfold firstValue requestFields
  rw [List.find?_append, find_regular hreg hn, Option.or_none]

theorem regular_requestFields (r : Request) (hreg : ∀ l ∈ r.headers, validRegular (ofLine l) = true) :
    regularFields (requestFields r) = r.headers.map ofLine := by
  unfold regularFields requestFields
  rw [List.filter_append]
  have h1 : (requestPseudoFields r).filter (fun e => !isPseudo e) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    unfold requestPseudoFields optField at he
    simp only [List.cons_append, List.mem_cons, List.mem_append] at he
    have key : ∀ (n : String) (v : List UInt8), PseudoName n →
        isPseudo ⟨ascii n, v⟩ = true := by
      intro n v hn; simp only [isPseudo]; rw [hn]; decide
    rcases he with rfl | ((he | he) | he)
    · simp [key ":method" _ (by decide)]
    · split at he <;> simp_all [key ":scheme" _ (by decide)]
    · split at he <;> simp_all [key ":authority" _ (by decide)]
    · split at he <;> simp_all [key ":path" _ (by decide)]
  have h2 : (r.headers.map ofLine).filter (fun e => !isPseudo e) = r.headers.map ofLine := by
    rw [List.filter_eq_self]
    intro e he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
    have hv := hreg l hl
    simp only [validRegular, Bool.and_eq_true, Bool.not_eq_true'] at hv
    simp [hv.1.1.2]
  rw [h1, h2, List.nil_append]

theorem pseudo_values (r : Request) :
    firstValue (requestPseudoFields r) ":method" = some r.method.toToken ∧
    firstValue (requestPseudoFields r) ":scheme" = r.target.scheme.map schemeBytes ∧
    firstValue (requestPseudoFields r) ":authority" = r.target.authority ∧
    firstValue (requestPseudoFields r) ":path" = r.target.pathWithQuery := by
  have n1 : (ascii ":method" == ascii ":scheme") = false := by decide
  have n2 : (ascii ":method" == ascii ":authority") = false := by decide
  have n3 : (ascii ":method" == ascii ":path") = false := by decide
  have n4 : (ascii ":scheme" == ascii ":authority") = false := by decide
  have n5 : (ascii ":scheme" == ascii ":path") = false := by decide
  have n6 : (ascii ":authority" == ascii ":path") = false := by decide
  have m4 : (ascii ":authority" == ascii ":scheme") = false := by decide
  have m5 : (ascii ":path" == ascii ":scheme") = false := by decide
  have m6 : (ascii ":path" == ascii ":authority") = false := by decide
  obtain ⟨⟨m, ⟨sc, au, pa⟩⟩, hd, co, tr⟩ := r
  simp only [requestPseudoFields, firstValue, Request.method, Request.target]
  cases sc <;> cases au <;> cases pa <;>
    simp [optField, n1, n2, n3, n4, n5, n6, m4, m5, m6]

theorem requestOf_requestFields (r : Request) (hm : r.method.Canonical)
    (hs : ∀ sc, r.target.scheme = some sc → schemeCanonical sc)
    (hreg : ∀ l ∈ r.headers, validRegular (ofLine l) = true)
    (hv : validRequest (requestFields r) = true) (ht : trailersValid (requestTrailers r) = true)
    (hcl : contentLengthMatches (requestFields r) r.content.length = true) :
    requestOf (requestFields r) r.content (requestTrailers r) = some r := by
  obtain ⟨p1, p2, p3, p4⟩ := pseudo_values r
  unfold requestOf
  simp only [hv, ht, hcl, Bool.and_self, ↓reduceIte]
  rw [firstValue_requestFields r hreg (n := ":method") (by decide), p1,
    firstValue_requestFields r hreg (n := ":scheme") (by decide), p2,
    firstValue_requestFields r hreg (n := ":authority") (by decide), p3,
    firstValue_requestFields r hreg (n := ":path") (by decide), p4, regular_requestFields r hreg]
  obtain ⟨⟨m, ⟨sc, au, pa⟩⟩, hd, co, tr⟩ := r
  simp only [Request.method, Request.target] at hm hs ⊢
  simp only [Option.map_some, Silmaril.Net.Http.Method.ofToken_toToken hm, requestTrailers,
    map_toLine_ofLine, Option.some.injEq]
  cases sc with
  | none => rfl
  | some sc => simp [schemeOf_schemeBytes (hs sc rfl)]

theorem firstValue_responseFields (r : Response) :
    firstValue (responseFields r) ":status" = some (statusDigits r.status) := by
  unfold firstValue responseFields
  simp [List.find?]

theorem regular_responseFields (r : Response)
    (hreg : ∀ l ∈ r.headers, validRegular (ofLine l) = true) :
    regularFields (responseFields r) = r.headers.map ofLine := by
  unfold regularFields responseFields
  simp only [List.filter_cons]
  have hp : isPseudo ⟨ascii ":status", statusDigits r.status⟩ = true := by
    simp [isPseudo]; decide
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [List.filter_eq_self]
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
  have hv := hreg l hl
  simp only [validRegular, Bool.and_eq_true, Bool.not_eq_true'] at hv
  simp [hv.1.1.2]

theorem responseOf_responseFields (r : Response) (hs : r.status < 1000)
    (hreg : ∀ l ∈ r.headers, validRegular (ofLine l) = true)
    (hv : validResponse (responseFields r) = true) (ht : trailersValid (r.trailers.map ofLine) = true)
    (hcl : contentLengthMatches (responseFields r) r.content.length = true) :
    responseOf (responseFields r) r.content (r.trailers.map ofLine) = some r := by
  unfold responseOf
  simp only [hv, ht, hcl, Bool.and_self, ↓reduceIte]
  rw [firstValue_responseFields r]
  simp only [Option.bind_some, parseStatus_statusDigits hs, regular_responseFields r hreg,
    map_toLine_ofLine]
  rfl

end Silmaril.Proofs.Net.Http3.Message
