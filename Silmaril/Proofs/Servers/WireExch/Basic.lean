module

public import Silmaril.Servers.WireExch.Defs
public import Silmaril.Net.Http1.Framing.Thms
public import Mathlib.Data.List.Forall2

/-!
# HTTP/1.1 exchanges: proofs

For `Silmaril.Servers.WireExch.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WireExch

open Silmaril.Net Silmaril.Net.Http1 Silmaril.Parse.ByteParse Silmaril.Servers.Wire1
open Silmaril.Servers.WireExch

theorem encResponse_pos (h : ResponseHead) (b : Http1.Body) : 0 < (encResponse h b).length := by
  have : 0 < (encStatusLine h.line).length := by
    simp only [encStatusLine, List.length_append, List.length_cons, List.length_nil]; omega
  simp only [encResponse, encResponseHead, List.length_append]; omega

theorem length_le_encResponses : ∀ ms : List WireResp, ms.length ≤ (encResponses ms).length
  | [] => by simp [encResponses]
  | m :: ms => by
    have := length_le_encResponses ms
    have := encResponse_pos m.1 m.2
    simp only [encResponses, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

theorem encResponses_cons (m : WireResp) (ms : List WireResp) :
    encResponses (m :: ms) = encResponse m.1 m.2 ++ encResponses ms := List.flatMap_cons

theorem isCloseBody_of_fits {len : BodyLength} {b : Http1.Body} (h : b.Fits len) :
    isCloseBody b = false := by
  cases len <;> cases b <;> first | rfl | exact h.elim

/-- Interim responses that read back are skipped, each advancing, up to the final one. -/
theorem parseExch_interims {meth : List UInt8} {closed : Bool} (L T : List UInt8)
    (R : Option (List WireResp × WireResp × Nat)) :
    ∀ (is : List WireResp) (pre : List UInt8) (fuel : Nat), (∀ m ∈ is, InterimOk m) →
      is.length < fuel → L = pre ++ encResponses is ++ T →
      (∀ fuel', parseExch ⟨L.toArray⟩ closed meth (fuel' + 1)
        (pre.length + (encResponses is).length) = R) →
      parseExch ⟨L.toArray⟩ closed meth fuel pre.length = R.map fun r => (is ++ r.1, r.2)
  | [], pre, fuel, _, hf, _, hR => by
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have := hR fuel'
    simp only [encResponses, List.flatMap_nil, List.length_nil, Nat.add_zero] at this
    rw [this]
    cases R <;> rfl
  | m :: is, pre, 0, _, hf, _, _ => absurd hf (by simp)
  | m :: is, pre, fuel + 1, hi, hf, hL, hR => by
    obtain ⟨hv, hint, hb⟩ := hi m List.mem_cons_self
    have hfits : m.2.Fits (responseBodyLength meth m.1.line.code m.1.fields) := by
      rw [hb, responseBodyLength_noContent _ (Or.inl (by
        simp only [isInterim, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hint
        exact hint.1))]
      trivial
    have e : L = pre ++ encResponse m.1 m.2 ++ (encResponses is ++ T) := by
      rw [hL]; simp [encResponses_cons]
    have hp := parseResponseAt_encode (method := meth) hv hfits pre (encResponses is ++ T)
    rw [← e] at hp
    have hpos := encResponse_pos m.1 m.2
    have ih := parseExch_interims (meth := meth) (closed := closed) L T R is
      (pre ++ encResponse m.1 m.2) fuel
      (fun x hx => hi x (List.mem_cons_of_mem _ hx)) (by simp at hf; omega)
      (by rw [e]; simp) (fun f' => by
        rw [← hR f']
        congr 1
        simp [encResponses_cons]
        omega)
    simp only [parseExch, hp, hint, ↓reduceIte, show pre.length < pre.length +
      (encResponse m.1 m.2).length by omega]
    rw [show pre.length + (encResponse m.1 m.2).length = (pre ++ encResponse m.1 m.2).length by
      simp, ih, Option.map_map]
    rfl

/-- A final response that fits its framing ends the exchange. -/
theorem parseExch_final {meth : List UInt8} {closed : Bool} {f : WireResp}
    (hf : RespOk meth f) (hi : isInterim f = false) (q rest : List UInt8) (fuel : Nat) :
    parseExch ⟨(q ++ encResponse f.1 f.2 ++ rest).toArray⟩ closed meth (fuel + 1) q.length =
      some ([], f, q.length + (encResponse f.1 f.2).length) := by
  have hp := parseResponseAt_encode (method := meth) hf.1 hf.2 q rest
  simp only [parseExch, hp, hi, isCloseBody_of_fits hf.2, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]

theorem parseResponseAt_close {meth : List UInt8} {h : ResponseHead} {b : List UInt8}
    (hv : h.Valid) (hl : responseBodyLength meth h.line.code h.fields = .close) (q : List UInt8) :
    parseResponseAt meth ⟨(q ++ encResponse h (.close b)).toArray⟩ q.length =
      .ok (h, .close b) (q ++ encResponse h (.close b)).length := by
  have hh := responseHead_at hv q (encBody (.close b))
  have e : q ++ encResponseHead h ++ encBody (.close b) = q ++ encResponse h (.close b) := by
    simp [encResponse]
  rw [e] at hh
  have hext : (ByteArray.extract ⟨(q ++ encResponse h (.close b)).toArray⟩
      (q.length + (encResponseHead h).length) (q ++ encResponse h (.close b)).length).data.toList
      = b := by
    rw [seg_extract]
    have e3 : q ++ encResponse h (.close b) = q ++ encResponseHead h ++ b ++ [] := by
      simp [encResponse, encBody]
    have := seg_middle (q ++ encResponseHead h) b []
    rw [e3]
    simpa [Nat.add_assoc] using this
  unfold parseResponseAt
  rw [size_ofList, hh]
  simp only [hl, parseBody, size_ofList, hext]

/-- A close-delimited final response at the end of the octets: read when the connection is
closed, not before. -/
theorem parseExch_close {meth : List UInt8} {closed : Bool} {f : WireResp}
    (hf : CloseOk meth f) (q : List UInt8) (fuel : Nat) :
    parseExch ⟨(q ++ encResponse f.1 f.2).toArray⟩ closed meth (fuel + 1) q.length =
      if closed then some ([], f, (q ++ encResponse f.1 f.2).length) else none := by
  obtain ⟨hv, hi, hl, b, hb⟩ := hf
  obtain ⟨h, b'⟩ := f
  simp only at hb hv hi hl
  subst hb
  simp only [parseExch, parseResponseAt_close hv hl q, hi, Bool.false_eq_true, ↓reduceIte,
    isCloseBody, Bool.true_and]
  cases closed <;> rfl


theorem encExch_eq (x : List WireResp × WireResp) :
    encExch x = encResponses x.1 ++ encResponse x.2.1 x.2.2 := rfl

/-- **One whole exchange reads back**, after any octets and before any. -/
theorem parseExch_exch {meth : List UInt8} {closed : Bool} {x : List WireResp × WireResp}
    (hx : ExchOk meth x) (q rest : List UInt8) (fuel : Nat) (hf : x.1.length < fuel) :
    parseExch ⟨(q ++ encExch x ++ rest).toArray⟩ closed meth fuel q.length =
      some (x.1, x.2, q.length + (encExch x).length) := by
  obtain ⟨is, f⟩ := x
  obtain ⟨hi, hfi, hok⟩ := hx
  have := parseExch_interims (meth := meth) (closed := closed) (q ++ encExch (is, f) ++ rest)
    (encResponse f.1 f.2 ++ rest) (some ([], f, q.length + (encExch (is, f)).length)) is q fuel hi hf
    (by simp [encExch]) (fun f' => by
      have := parseExch_final (closed := closed) hok hfi (q ++ encResponses is) rest f'
      simp only [List.length_append] at this
      have e1 : q ++ encExch (is, f) ++ rest = q ++ encResponses is ++ encResponse f.1 f.2 ++ rest := by
        simp [encExch]
      have e2 : q.length + (encExch (is, f)).length =
          q.length + (encResponses is).length + (encResponse f.1 f.2).length := by
        simp [encExch]; omega
      rw [e1, e2]
      exact this)
  rw [this]
  simp

theorem length_lt_encExch (x : List WireResp × WireResp) : x.1.length < (encExch x).length + 1 := by
  have := length_le_encResponses x.1
  simp only [encExch, List.length_append]
  omega

/-- **Exchanges back to back read back**, then whatever the rest of the methods read. -/
theorem parseExchs_encode {closed : Bool} {ms : List (List UInt8)}
    {xs : List (List WireResp × WireResp)} (hx : List.Forall₂ ExchOk ms xs) :
    ∀ (q rest : List UInt8) (ms₂ : List (List UInt8)),
      parseExchs ⟨(q ++ encExchs xs ++ rest).toArray⟩ closed (ms ++ ms₂) q.length =
        xs ++ parseExchs ⟨(q ++ encExchs xs ++ rest).toArray⟩ closed ms₂
          (q ++ encExchs xs).length := by
  induction hx with
  | nil => intro q rest ms₂; simp [encExchs]
  | @cons meth x ms xs hm _ ih =>
    intro q rest ms₂
    have e : q ++ encExchs (x :: xs) ++ rest = q ++ encExch x ++ (encExchs xs ++ rest) := by
      simp [encExchs]
    have hsz : x.1.length < (⟨(q ++ encExchs (x :: xs) ++ rest).toArray⟩ : ByteArray).size + 1 := by
      rw [size_ofList]
      have := length_lt_encExch x
      simp [encExchs]
      omega
    have hp := parseExch_exch (closed := closed) hm q (encExchs xs ++ rest) _ hsz
    rw [← e] at hp
    have ih' := ih (q ++ encExch x) rest ms₂
    have e2 : q ++ encExch x ++ encExchs xs ++ rest = q ++ encExchs (x :: xs) ++ rest := by
      simp [encExchs]
    rw [e2] at ih'
    simp only [List.cons_append, parseExchs, hp]
    rw [show q.length + (encExch x).length = (q ++ encExch x).length by simp, ih']
    simp [encExchs]


/-- The last exchange, with a close-delimited final response, read when the connection is
closed and not before. -/
theorem parseExchs_close {closed : Bool} {meth : List UInt8} {x : List WireResp × WireResp}
    (hi : ∀ m ∈ x.1, InterimOk m) (hc : CloseOk meth x.2) (q : List UInt8) :
    parseExchs ⟨(q ++ encExch x).toArray⟩ closed [meth] q.length =
      if closed then [x] else [] := by
  obtain ⟨is, f⟩ := x
  have hsz : is.length < (⟨(q ++ encExch (is, f)).toArray⟩ : ByteArray).size + 1 := by
    rw [size_ofList]
    have := length_lt_encExch (is, f)
    dsimp only at this
    simp only [List.length_append]
    omega
  have := parseExch_interims (meth := meth) (closed := closed) (q ++ encExch (is, f))
    (encResponse f.1 f.2)
    (if closed then some ([], f, (q ++ encExch (is, f)).length) else none) is q _ hi hsz
    (by simp [encExch]) (fun f' => by
      have := parseExch_close (closed := closed) hc (q ++ encResponses is) f'
      have e1 : q ++ encExch (is, f) = q ++ encResponses is ++ encResponse f.1 f.2 := by
        simp [encExch]
      have e2 : (q ++ encExch (is, f)).length = (q ++ encResponses is ++ encResponse f.1 f.2).length := by
        rw [e1]
      rw [e2, e1]
      simpa using this)
  simp only [parseExchs, this]
  cases closed <;> simp

end Silmaril.Proofs.Servers.WireExch
