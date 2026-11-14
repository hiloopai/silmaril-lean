module

public import Silmaril.Net.Http1.Service.Defs
public import Silmaril.Net.Http1.Institution.Thms
public import Silmaril.Net.Http1.Request.Thms
public import Silmaril.Net.Http1.Message.Thms
public import Silmaril.Net.Http1.Framing.Thms
public import Silmaril.Net.Http.OpenApi.Thms
public import Silmaril.Net.Http.OpenApiPetstore.Thms

/-! Proofs for `Silmaril.Net.Http1.Service.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http1.Proofs.Service

open Silmaril.Net.Http1 Silmaril.Net.Http1.Inst
open Silmaril.Parse.ByteParse (Bytes)

/-! ## Decimal numerals -/

theorem digitByte_ok' : ∀ d < 10, isDigit (digitByte d) = true ∧ digitVal (digitByte d) = d := by
  decide

theorem decValue_append (l : Bytes) (x : UInt8) : decValue (l ++ [x]) = 10 * decValue l + digitVal x := by
  simp [decValue, List.foldl_append]

theorem decValue_decDigits (n : Nat) : decValue (decDigits n) = n := by
  fun_induction decDigits n with
  | case1 n hn => simp [decValue, (digitByte_ok' n hn).2]
  | case2 n hn ih =>
    rw [decValue_append, ih, (digitByte_ok' (n % 10) (Nat.mod_lt _ (by omega))).2]
    omega

theorem decDigits_digit (n : Nat) : ∀ b ∈ decDigits n, isDigit b = true := by
  fun_induction decDigits n with
  | case1 n hn => intro b hb; simp at hb; exact hb ▸ (digitByte_ok' n hn).1
  | case2 n hn ih =>
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ih b hb
    · simp at hb; exact hb ▸ (digitByte_ok' (n % 10) (Nat.mod_lt _ (by omega))).1

theorem decDigits_ne_nil (n : Nat) : decDigits n ≠ [] := by
  fun_induction decDigits n <;> simp

theorem digit_fieldByte : ∀ b : UInt8, isDigit b = true → isFieldByte b = true := by decide
theorem digit_not_ws : ∀ b : UInt8, isDigit b = true → isWS b = false := by decide
theorem digit_not_comma : ∀ b : UInt8, isDigit b = true → b ≠ COMMA := by decide

theorem isFieldValue_digits {l : Bytes} (hd : ∀ b ∈ l, isDigit b = true) : IsFieldValue l :=
  ⟨fun b hb => digit_fieldByte b (hd b hb),
   fun b hb => digit_not_ws b (hd b (List.mem_of_mem_head? hb)),
   fun b hb => digit_not_ws b (hd b (List.mem_of_mem_getLast? hb))⟩

theorem splitOn_of_not_mem {sep : UInt8} : ∀ {l : Bytes}, (∀ b ∈ l, b ≠ sep) → splitOn sep l = [l]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ sep := h c (by simp)
    have ih := splitOn_of_not_mem (l := cs) (fun b hb => h b (by simp [hb]))
    simp [splitOn, hc, ih]

theorem trimOWS_of_ends {l : Bytes} (h₁ : ∀ b ∈ l.head?, isWS b = false)
    (h₂ : ∀ b ∈ l.getLast?, isWS b = false) : trimOWS l = l := by
  have e₁ : l.dropWhile isWS = l := dropWhile_of_head h₁
  have e₂ : l.reverse.dropWhile isWS = l.reverse := by
    apply dropWhile_of_head; rw [List.head?_reverse]; exact h₂
  simp only [trimOWS, e₁, e₂, List.reverse_reverse]

theorem listElements_digits {l : Bytes} (hne : l ≠ []) (hd : ∀ b ∈ l, isDigit b = true) :
    listElements l = [l] := by
  have hv := isFieldValue_digits hd
  unfold listElements
  rw [splitOn_of_not_mem (fun b hb => digit_not_comma b (hd b hb))]
  simp [trimOWS_of_ends hv.2.1 hv.2.2, hne]

/-! ## Responses of a service -/

theorem fieldValues_forwarded (s : Http.Field.Section) {n : Bytes}
    (hn : lower n ∈ serverOwnedNames) : fieldValues (forwardedFields s) n = [] := by
  unfold fieldValues forwardedFields
  rw [List.filterMap_eq_nil_iff]
  intro f hf
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
  have hk := (List.mem_filter.1 hl).2
  split
  · next he =>
    simp only [FieldLine.ofLine] at he
    simp only [he, Bool.not_eq_true'] at hk
    simp at hk
    exact absurd hn hk
  · rfl

theorem toLine_ofLine (l : Http.Field.Line) : (FieldLine.ofLine l).toLine = l := rfl

theorem forwarded_valid {s : Http.Field.Section} (hs : s.isValid = true) :
    ∀ f ∈ forwardedFields s, f.Valid := by
  intro f hf
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
  have hv : l.isValid = true := by
    unfold Http.Field.Section.isValid at hs
    exact List.all_eq_true.1 hs l (List.mem_filter.1 hl).1
  exact (FieldLine.toLine_isValid _).1 (by rw [toLine_ofLine]; exact hv)

theorem clLine_valid (n : Nat) : FieldLine.Valid ⟨ascii "Content-Length", decDigits n⟩ :=
  ⟨by show IsToken (ascii "Content-Length"); decide, isFieldValue_digits (decDigits_digit n)⟩

theorem toResponse_valid {r : Http.Response} (hv : r.headers.isValid = true) (hs : r.status < 1000) :
    (toResponse r).1.Valid := by
  unfold toResponse
  split
  · refine ⟨⟨by show Version.Valid Version.http11; decide, hs, by simp⟩, fun f hf => ?_⟩
    rcases List.mem_append.1 hf with hf | hf
    · exact forwarded_valid hv f hf
    · simp only [List.mem_singleton] at hf; subst hf; exact clLine_valid _
  · exact ⟨⟨by show Version.Valid Version.http11; decide, hs, by simp⟩, forwarded_valid hv⟩

theorem allowsContent_false {s : Nat} (h : Http.Status.allowsContent s = false) :
    s / 100 = 1 ∨ s = 204 ∨ s = 304 := by
  unfold Http.Status.allowsContent Http.Status.class? at h
  by_cases h1 : s / 100 = 1
  · exact Or.inl h1
  · right
    split at h <;> simp_all <;> omega

theorem allowsContent_true {s : Nat} (h : Http.Status.allowsContent s = true) :
    ¬ (s / 100 = 1 ∨ s = 204 ∨ s = 304) := by
  unfold Http.Status.allowsContent Http.Status.class? at h
  split at h <;> simp_all

theorem toResponse_fits (r : Http.Response) {m : Bytes} (hm : m ≠ methodHEAD)
    (hc : ¬ (m = methodCONNECT ∧ r.status / 100 = 2)) :
    (toResponse r).2.Fits (responseBodyLength m (toResponse r).1.line.code (toResponse r).1.fields) := by
  unfold toResponse
  split
  · next ha =>
    have h₁ := allowsContent_true ha
    simp only [responseBodyLength, hm, false_or, h₁, ↓reduceIte, hc]
    have hte : fieldValues (forwardedFields r.headers ++
        [⟨ascii "Content-Length", decDigits r.content.length⟩]) transferEncodingName = [] := by
      unfold fieldValues
      rw [List.filterMap_append]
      have := fieldValues_forwarded r.headers (n := transferEncodingName) (by decide)
      unfold fieldValues at this
      rw [this]
      simp only [List.nil_append, List.filterMap_cons, List.filterMap_nil,
        show ¬ (lower (ascii "Content-Length") = lower transferEncodingName) by decide, ↓reduceIte]
    have hcl : fieldValues (forwardedFields r.headers ++
        [⟨ascii "Content-Length", decDigits r.content.length⟩]) contentLengthName =
          [decDigits r.content.length] := by
      unfold fieldValues
      rw [List.filterMap_append]
      have := fieldValues_forwarded r.headers (n := contentLengthName) (by decide)
      unfold fieldValues at this
      rw [this]
      simp only [List.nil_append, List.filterMap_cons, List.filterMap_nil,
        show lower (ascii "Content-Length") = lower contentLengthName by decide, ↓reduceIte]
    have hel : fieldElements (forwardedFields r.headers ++
        [⟨ascii "Content-Length", decDigits r.content.length⟩]) contentLengthName =
          [decDigits r.content.length] := by
      unfold fieldElements
      rw [hcl]
      simp [listElements_digits (decDigits_ne_nil _) (decDigits_digit _)]
    unfold bodyLengthOfFields transferCodings contentLength?
    unfold fieldElements at hel ⊢
    rw [hte, hel]
    simp only [List.flatMap_nil, List.map_nil, List.all_nil, Bool.and_true]
    simp only [List.all_eq_true.2 (decDigits_digit _), ↓reduceIte, decValue_decDigits]
    show r.content.length = r.content.length
    rfl
  · next ha =>
    rw [responseBodyLength_noContent _ (allowsContent_false (by simpa using ha))]
    trivial

theorem serviceHandler_wellFramed {S : Http.OpenApi.Service} (hS : ServiceValid S) :
    Handler.WellFramed (serviceHandler S) := by
  intro h b c
  unfold serviceHandler
  split
  · exact ⟨toResponse_valid (by decide) (by decide),
      fun hm => toResponse_fits (Http.Response.simple 501 []) hm (by simp [Http.Response.simple, Http.Response.status])⟩
  · next hc => exact ⟨toResponse_valid (hS _).1 (hS _).2,
      fun hm => toResponse_fits _ hm fun h => hc h.1⟩

/-! ## Documents as theories -/

open Silmaril.Net.Http.OpenApi (Document PathItem Operation ResponseKey Documented Closed route
  routePath responseSpec)

theorem opCodes_mem {op : Operation} {cs : List Nat} {code : Nat} (hcs : opCodes op = some cs)
    (hd : Documented op code) : code ∈ cs := by
  unfold opCodes at hcs
  split at hcs
  · cases hcs
  · next hnd =>
    cases hcs
    unfold Documented responseSpec at hd
    simp only [List.mem_flatMap]
    split at hd
    · next k sp he =>
      exact ⟨_, List.mem_of_find?_eq_some he, by
        have := List.find?_some he
        simp only [beq_iff_eq] at this
        rw [this]; simp⟩
    · split at hd
      · next k sp he =>
        refine ⟨_, List.mem_of_find?_eq_some he, ?_⟩
        have := List.find?_some he
        simp only [beq_iff_eq] at this
        rw [this]
        simp only [List.mem_map, List.mem_range]
        exact ⟨code % 100, Nat.mod_lt _ (by omega), by omega⟩
      · next _ =>
        exfalso
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hnd
        cases hf : op.responses.find? (·.1 == .default) with
        | none => simp [hf] at hd
        | some e =>
          have h₁ := List.find?_some hf
          have := hnd e (List.mem_of_find?_eq_some hf)
          simp_all

theorem meth_ne_connect (S : Http.OpenApi.Service) {meth : Http.Method} {m : ApiSig.Meth}
    (h : methodSym meth = some m) : (serviceModel S).meth m ≠ methodCONNECT := by
  cases meth <;> simp only [methodSym] at h <;> cases h <;> simp only [serviceModel] <;> decide

theorem ofToken_meth (S : Http.OpenApi.Service) {meth : Http.Method} {m : ApiSig.Meth}
    (h : methodSym meth = some m) : Http.Method.ofToken ((serviceModel S).meth m) = meth := by
  cases meth <;> simp only [methodSym] at h <;> cases h <;> simp only [serviceModel] <;> decide

theorem targetForm_origin {m t : Bytes} {f : TargetForm} (ht : t.head? = some 0x2F)
    (h : targetForm m t = some f) : f = .origin := by
  unfold targetForm at h
  have h₁ : t ≠ [0x2A] := by rintro rfl; simp at ht
  simp only [h₁, ↓reduceIte, ht] at h
  split at h
  · cases h; rfl
  · cases h

theorem eq_of_nodup_map {α β : Type} {f : α → β} {l : List α} (hl : (l.map f).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (he : f x = f y) : x = y :=
  List.inj_on_of_nodup_map hl hx hy he

theorem closed_satisfies_theory {d : Document} {S : Http.OpenApi.Service} (hd : d.Valid)
    (hc : Closed d S) : SatAll (serviceModel S) (toTheory d) := by
  intro φ hφ
  simp only [toTheory, List.mem_flatMap, List.mem_filterMap] at hφ
  obtain ⟨p, hp, op, hop, hφ⟩ := hφ
  split at hφ
  · next m cs hm hcs =>
    cases hφ
    intro h b rh rb _ hmeth hroute hr
    change (match checkRequest {} h with
      | .ok c => (rh, rb) = stripHead h (serviceHandler S h b c)
      | .error e => (rh, rb) = stripHead h (errorResponse e.status)) at hr
    split at hr
    · next c hck =>
      have e₁ : rh = (stripHead h (serviceHandler S h b c)).1 := congrArg Prod.fst hr
      have hnc : h.line.method ≠ methodCONNECT := hmeth ▸ meth_ne_connect S hm
      have hcode : rh.line.code = (S (toRequest h b c)).status := by
        rw [e₁]
        unfold stripHead serviceHandler toResponse
        simp only [hnc, ↓reduceIte]
        split <;> split <;> rfl
      rw [hcode]
      apply List.mem_append_left
      apply opCodes_mem hcs
      -- the request is routed to `op`
      simp only [routesTo, Bool.and_eq_true, beq_iff_eq] at hroute
      obtain ⟨hhead, hrp⟩ := hroute
      split at hrp
      · next q vs hq =>
        simp only [beq_iff_eq] at hrp
        have a := checkRequest_ok hck
        have hform := targetForm_origin hhead a.form
        obtain ⟨host, htarget⟩ := a.target
        have hpq : Http.OpenApi.targetPq (toRequest h b c).target = h.line.target := by
          simp [toRequest, Http.Request.target, htarget, hform, targetUri,
            Http.OpenApi.targetPq]
        have hmethod : (toRequest h b c).method = op.method := by
          simp only [toRequest, Http.Request.method]
          rw [a.method, hmeth, ofToken_meth S hm]
        obtain ⟨hqd, -⟩ := Http.OpenApi.routePath_mem hq
        have hqp : q = p := eq_of_nodup_map hd.2.1 hqd hp hrp
        subst hqp
        cases hf : q.operations.find? (·.method == (toRequest h b c).method) with
        | none =>
          exfalso
          have := List.find?_eq_none.1 hf op hop
          simp [hmethod] at this
        | some op' =>
          have h₁ := List.find?_some hf
          have h₂ := List.mem_of_find?_eq_some hf
          simp only [beq_iff_eq, hmethod] at h₁
          have hop' : op' = op := eq_of_nodup_map (hd.2.2 q hqd).1 h₂ hop h₁
          subst hop'
          refine hc (toRequest h b c) op' q vs ?_
          unfold route
          rw [hpq, hq]
          simp [hf]
      · cases hrp
    · next e _ =>
      have e₁ : rh = (stripHead h (errorResponse e.status)).1 := congrArg Prod.fst hr
      apply List.mem_append_right
      rw [e₁]
      have := e.status_mem
      unfold stripHead
      split <;> simpa [errorResponse, serverErrorCodes] using this
  · cases hφ

end Silmaril.Net.Http1.Proofs.Service

namespace Silmaril.Net.Http1.Proofs.Service

open Silmaril.Net.Http1 Silmaril.Net.Http1.Inst
open Silmaril.Net.Http.OpenApi.Petstore

theorem petstore_valid : ServiceValid service := by
  intro r
  unfold service Http.OpenApi.Service.ofHandlers
  split
  · next op p vs hr =>
    have hm := Http.OpenApi.route_mem hr
    obtain ⟨hp, hop, -⟩ := hm
    simp only [doc, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop <;>
    rcases hop with rfl | rfl <;>
    simp only [handlers, listPets, createPet, myPets, showPetById, String.reduceEq, ↓reduceIte] <;>
    (try split_ifs) <;> decide
  · split <;> decide

end Silmaril.Net.Http1.Proofs.Service
