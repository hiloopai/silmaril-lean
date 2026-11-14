module

public import Silmaril.Servers.Tcp.Defs
public import Silmaril.Servers.Wire1.Thms
public import Silmaril.Servers.WasiBinaries.Thms
public import Silmaril.Servers.Core.Thms
public import Silmaril.Net.Http1.Framing.Thms
public import Mathlib.Data.List.Infix

/-!
# Proofs: HTTP over a TCP byte stream
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Tcp

open Silmaril.Servers Silmaril.Servers.Transport Silmaril.Servers.Wire1 Silmaril.Servers.Tcp
open Silmaril.Net.Http1
open Silmaril.Net.Http (Request Response)

theorem size_ofList (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  simp [ByteArray.size]

/-! ## Reading requests -/

theorem readReqs_fst (bs : ByteArray) : ∀ fuel i, (readReqs bs fuel i).1 = parseRequests bs fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    unfold readReqs parseRequests
    by_cases hi : i < bs.size
    · simp only [hi, ↓reduceIte]
      cases parseRequestAt bs i with
      | ok m k => by_cases hk : i < k <;> simp [hk, readReqs_fst bs fuel k]
      | err _ => rfl
    · simp [hi]

theorem encRequest_pos (h : RequestHead) (b : Silmaril.Net.Http1.Body) : 0 < (encRequest h b).length := by
  have : 0 < (encRequestLine h.line).length := by
    simp only [encRequestLine, List.length_append, List.length_cons, List.length_nil]; omega
  simp only [encRequest, encRequestHead, List.length_append]; omega

theorem readReqs_encode : ∀ (ms : List WireReq) (pre : List UInt8) (fuel : Nat),
    (∀ m ∈ ms, ReqOk m) → ms.length ≤ fuel →
    readReqs ⟨(pre ++ encRequests ms).toArray⟩ fuel pre.length = (ms, (pre ++ encRequests ms).length)
  | [], pre, fuel, _, _ => by
    have e : pre ++ encRequests [] = pre := by simp [encRequests]
    rw [e]
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have : ¬ pre.length < (⟨pre.toArray⟩ : ByteArray).size := by rw [size_ofList]; omega
      simp only [readReqs, this, ↓reduceIte]
  | (_ :: _), _, 0, _, hl => absurd hl (by simp)
  | (h, b) :: ms, pre, fuel + 1, hv, hl => by
    have hm := hv (h, b) List.mem_cons_self
    have e : pre ++ encRequests ((h, b) :: ms) = pre ++ encRequest h b ++ encRequests ms := by
      simp [encRequests]
    have hp := parseRequestAt_encode hm.1 hm.2 pre (encRequests ms)
    have ih := readReqs_encode ms (pre ++ encRequest h b) fuel
      (fun x hx => hv x (List.mem_cons_of_mem _ hx)) (by simp at hl; omega)
    have hpos := encRequest_pos h b
    have hsz : pre.length < (⟨(pre ++ encRequest h b ++ encRequests ms).toArray⟩ : ByteArray).size := by
      rw [size_ofList]; simp only [List.length_append]; omega
    have hk : pre.length < pre.length + (encRequest h b).length := by omega
    simp only at hp
    rw [e]
    simp only [readReqs, hsz, ↓reduceIte, hp, hk]
    simp only [List.length_append] at ih
    rw [ih]
    simp [List.length_append, Nat.add_assoc]

theorem h1Read_encode (ms : List WireReq) (hv : ∀ m ∈ ms, ReqOk m) :
    h1Read (encRequests ms) = ⟨ms, [], false⟩ := by
  have hl : ms.length ≤ (encRequests ms).length + 1 := by
    have := length_le_encRequests' ms; omega
  have := readReqs_encode ms [] _ hv hl
  simp only [List.nil_append, List.length_nil] at this
  simp [h1Read, this]
where
  length_le_encRequests' : ∀ ms : List WireReq, ms.length ≤ (encRequests ms).length
  | [] => by simp [encRequests]
  | m :: ms => by
    have := length_le_encRequests' ms
    have := encRequest_pos m.1 m.2
    simp only [encRequests, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-! ## Protocol selection -/

theorem select_mono {s : Select} {a : Option (List UInt8)} {bs : List UInt8} {p : Proto}
    (h : select s a bs = some p) (more : List UInt8) : select s a (bs ++ more) = some p := by
  cases s with
  | http1 => exact h
  | alpn ids => exact h
  | h2PriorKnowledge =>
    simp only [select] at h ⊢
    by_cases h1 : h2Preface <+: bs
    · rw [ite_eq_left (h1.trans (List.prefix_append bs more))]; rwa [ite_eq_left h1] at h
    · rw [ite_eq_right h1] at h
      by_cases h2 : bs <+: h2Preface
      · rw [ite_eq_left h2] at h; cases h
      · rw [ite_eq_right h2] at h
        have n1 : ¬ h2Preface <+: bs ++ more := fun hp =>
          (List.prefix_or_prefix_of_prefix hp (List.prefix_append bs more)).elim h1 h2
        have n2 : ¬ bs ++ more <+: h2Preface := fun hp => h2 ((List.prefix_append bs more).trans hp)
        rw [ite_eq_right n1, ite_eq_right n2]; exact h
  | sniffPreface =>
    simp only [select] at h ⊢
    by_cases h1 : h2Preface <+: bs
    · rw [ite_eq_left (h1.trans (List.prefix_append bs more))]; rwa [ite_eq_left h1] at h
    · rw [ite_eq_right h1] at h
      by_cases h2 : bs <+: h2Preface
      · rw [ite_eq_left h2] at h; cases h
      · rw [ite_eq_right h2] at h
        have n1 : ¬ h2Preface <+: bs ++ more := fun hp =>
          (List.prefix_or_prefix_of_prefix hp (List.prefix_append bs more)).elim h1 h2
        have n2 : ¬ bs ++ more <+: h2Preface := fun hp => h2 ((List.prefix_append bs more).trans hp)
        rw [ite_eq_right n1, ite_eq_right n2]; exact h

/-! ## Connection traces -/

theorem pending_nil (c : Conn) : ∀ (k : Nat) (rs : List Request) (xs : List Response),
    rs.length ≤ xs.length → pending c k rs xs = []
  | _, [], _, _ => by cases ‹List Response› <;> rfl
  | _, _ :: _, [], h => by simp at h
  | k, _ :: rs, _ :: xs, h => by
    simp only [pending]; exact pending_nil c (k + 1) rs xs (by simp at h; omega)

theorem mem_pairs_resp {c : Conn} : ∀ {k : Nat} {rs : List Request} {xs : List Response}
    {p : ReqId × Request × Response}, p ∈ pairs c k rs xs → p.2.2 ∈ xs
  | _, [], _, _, h => by simp [pairs] at h
  | _, _ :: _, [], _, h => by simp [pairs] at h
  | k, r :: rs, x :: xs, p, h => by
    simp only [pairs, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_pairs_resp h)

theorem mem_pairs_id {c : Conn} : ∀ {k : Nat} {rs : List Request} {xs : List Response}
    {p : ReqId × Request × Response}, p ∈ pairs c k rs xs → p.1.conn = c ∧ k ≤ p.1.seq
  | _, [], _, _, h => by simp [pairs] at h
  | _, _ :: _, [], _, h => by simp [pairs] at h
  | k, r :: rs, x :: xs, p, h => by
    simp only [pairs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, le_refl _⟩
    · have := mem_pairs_id h; exact ⟨this.1, by omega⟩

theorem nodup_pairs (c : Conn) : ∀ (k : Nat) (rs : List Request) (xs : List Response),
    ((pairs c k rs xs).map (·.1)).Nodup
  | _, [], _ => by simp [pairs]
  | _, _ :: _, [] => by simp [pairs]
  | k, r :: rs, x :: xs => by
    simp only [pairs, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_pairs c (k + 1) rs xs⟩
    obtain ⟨p, hp, he⟩ := List.mem_map.1 hm
    have := (mem_pairs_id hp).2
    rw [he] at this
    simp at this

theorem send_mem_seq {L : List (ReqId × Request × Response)} {i : ReqId} {s : Response}
    (h : Event.send i s ∈ Trace.seq (A := Http.sig) L) : ∃ p ∈ L, p.2.2 = s := by
  unfold Trace.seq at h
  obtain ⟨p, hp, h⟩ := List.mem_flatMap.1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · cases h
  · cases h; exact ⟨p, hp, rfl⟩

end Silmaril.Proofs.Servers.Tcp

namespace Silmaril.Proofs.Servers.Tcp

open Silmaril.Servers Silmaril.Servers.Transport Silmaril.Servers.Wire1 Silmaril.Servers.Tcp
open Silmaril.Net.Http1
open Silmaril.Net.Http (Request Response)

/-! ## Hello over TCP -/

theorem helloWire_toResponse : toResponse helloWire = WasiExamples.helloResp := by
  decide +kernel

theorem helloWire_valid : helloWire.1.Valid := by decide +kernel

theorem helloWire_fits : Body.Fits (bodyLengthOfFields helloWire.1.fields .close .close) helloWire.2 := by
  show List.length (ascii "hello") = 5
  decide +kernel

theorem helloWire_respOk {m : List UInt8} (h1 : m ≠ methodHEAD) (h2 : m ≠ methodCONNECT) :
    RespOk m helloWire := by
  refine ⟨helloWire_valid, ?_⟩
  have e : responseBodyLength m helloWire.1.line.code helloWire.1.fields =
      bodyLengthOfFields helloWire.1.fields .close .close := by
    unfold responseBodyLength
    rw [ite_eq_right (by simp [helloWire, h1]), ite_eq_right (by simp [h2])]
  rw [e]; exact helloWire_fits

theorem connTrace_eq {c : Conn} {rs : List Request} {xs : List Response}
    (h : rs.length ≤ xs.length) : connTrace c rs xs = Trace.seq (A := Http.sig) (pairs c 0 rs xs) := by
  simp [connTrace, pending_nil c 0 rs xs h]

/-- The requests and responses of a connection of `helloTcp`. -/
theorem hello_conn {Addr : Type} {p : Port} {t : TTrace Addr} (ht : t ∈ helloTcp p) {c : Conn}
    (hc : c ∈ opened p t) : ∃ ms : List WireReq, (∀ m ∈ ms, Served m) ∧
      requests (streamIn c t) = ms.map toRequest ∧
      responses (requests (streamIn c t)) (streamOut c t) = ms.map fun _ => WasiExamples.helloResp := by
  obtain ⟨ms, hs, hi, ho⟩ := ht.2 c hc
  have hr : requests (streamIn c t) = ms.map toRequest := by
    rw [hi]; exact requests_encode ms fun m hm => (hs m hm).1
  refine ⟨ms, hs, hr, ?_⟩
  rw [hr, ho]
  have hf : List.Forall₂ (fun r m => RespOk r.method.toToken m) (ms.map toRequest)
      (ms.map fun _ => helloWire) :=
    List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun m hm => by
      rw [method_toRequest]; exact helloWire_respOk (hs m hm).2.1 (hs m hm).2.2))
  rw [responses_encode _ _ hf, List.map_map]
  exact List.map_congr_left fun _ _ => helloWire_toResponse

theorem seq_flatMap {A : Servers.Sig} {β : Type} (l : List β)
    (f : β → List (ReqId × A.Req × A.Resp)) :
    Trace.seq (A := A) (l.flatMap f) = l.flatMap fun c => Trace.seq (A := A) (f c) := by
  simp only [Trace.seq, List.flatMap_assoc]

/-- The HTTP trace of `helloTcp` is a sequential trace of answered exchanges. -/
theorem hello_trace {Addr : Type} {p : Port} {t : TTrace Addr} (ht : t ∈ helloTcp p) :
    h1Trace p t = Trace.seq (A := Http.sig) ((opened p t).flatMap fun c =>
      pairs c 0 (requests (streamIn c t)) (responses (requests (streamIn c t)) (streamOut c t))) := by
  refine Eq.trans ?_ (seq_flatMap (A := Http.sig) _ _).symm
  unfold h1Trace
  apply List.flatMap_congr
  intro c hc
  obtain ⟨ms, _, hr, ho⟩ := hello_conn ht hc
  exact connTrace_eq (by rw [ho, hr]; simp)

theorem hello_resp {Addr : Type} {p : Port} {t : TTrace Addr} (ht : t ∈ helloTcp p)
    {q : ReqId × Request × Response} (hq : q ∈ (opened p t).flatMap fun c =>
      pairs c 0 (requests (streamIn c t)) (responses (requests (streamIn c t)) (streamOut c t))) :
    q.2.2 = WasiExamples.helloResp := by
  obtain ⟨c, hc, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨ms, _, _, ho⟩ := hello_conn ht hc
  have := mem_pairs_resp hq
  rw [ho] at this
  obtain ⟨_, _, he⟩ := List.mem_map.1 this
  exact he.symm

theorem hello_nodup {Addr : Type} {p : Port} {t : TTrace Addr} (ht : t ∈ helloTcp p) :
    (((opened p t).flatMap fun c =>
      pairs c 0 (requests (streamIn c t)) (responses (requests (streamIn c t)) (streamOut c t))).map
        (·.1)).Nodup := by
  rw [List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨fun c _ => nodup_pairs c 0 _ _, ?_⟩
  refine ht.1.imp_of_mem fun {a b} _ _ hab => ?_
  intro x hxa hxb
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hxa
  obtain ⟨v, hv, he⟩ := List.mem_map.1 hxb
  exact hab ((mem_pairs_id hu).1.symm.trans (he ▸ (mem_pairs_id hv).1))

/-- **Hello over TCP implements at most the `wasi:http` hello module's per-request server.** -/
theorem hello_atMost {Addr : Type} (p : Port) :
    AtMost (h1Reading (Addr := Addr) .http1 none p) (helloTcp p)
      (Exchange.fresh (WasiCore.wasiServerTy (WasiBinaries.den WasiBinaries.helloCore))) := by
  rintro t' ⟨t, ht, he⟩
  have hs : h1Reading (Addr := Addr) .http1 none p t = some (h1Trace p t) := by
    simp [h1Reading, select]
  rw [hs] at he
  cases he
  rw [hello_trace ht]
  refine ⟨Sen.wf_of_lin ((Sen.lin_seq_iff (S := fun _ => True) _ (hello_nodup ht)).2 trivial),
    fun i r s _ hsend => ?_⟩
  obtain ⟨q, hq, rfl⟩ := send_mem_seq hsend
  rw [hello_resp ht hq]
  exact WasiBinaries.helloBin_answers r

/-- **Hello over TCP realizes every single exchange of a served request.** -/
theorem hello_realizes {Addr : Type} (p : Port) (a : Addr) (m : WireReq) (hm : Served m) :
    [Event.recv ⟨0, 0⟩ (toRequest m), Event.send ⟨0, 0⟩ WasiExamples.helloResp] ∈
      (h1Reading (Addr := Addr) .http1 none p).image (helloTcp p) := by
  let t : TTrace Addr := [.open_ p 0 a, .recv 0 (encRequests [m]), .send 0 (encResponses [helloWire])]
  have ho : opened p t = [0] := by simp [t, opened]
  have hi : streamIn 0 t = encRequests [m] := by simp [t, streamIn, unitsIn]
  have hout : streamOut 0 t = encResponses ([m].map fun _ => helloWire) := by
    simp [t, streamOut, unitsOut]
  have ht : t ∈ helloTcp p := ⟨by rw [ho]; simp, fun c hc => by
    rw [ho] at hc; simp at hc; subst hc
    exact ⟨[m], by simpa using hm, hi, hout⟩⟩
  refine ⟨t, ht, ?_⟩
  have hs : h1Reading (Addr := Addr) .http1 none p t = some (h1Trace p t) := by
    simp [h1Reading, select]
  rw [hs]
  unfold h1Trace
  rw [ho]
  obtain ⟨ms, _, hr, hx⟩ := hello_conn ht (c := 0) (by rw [ho]; simp)
  have hr' : requests (streamIn 0 t) = [toRequest m] := by
    rw [hi]; exact requests_encode [m] (by simpa using hm.1)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hr'] at hx
  rw [hr']
  have hl : ms.length = 1 := by
    have := congrArg List.length hr; rw [hr'] at this; simpa using this.symm
  rw [hx]
  obtain ⟨x, rfl⟩ : ∃ x, ms = [x] := by
    match ms, hl with | [x], _ => exact ⟨x, rfl⟩
  simp [connTrace, pairs, pending, Trace.seq]
  rfl

end Silmaril.Proofs.Servers.Tcp
