module

public import Silmaril.Proofs.Servers.WasiExamples.Answer

/-!
# The echo server: its specification for every host

`echo_sat`: over the reading with request bodies, every exchange of `echo` answers `200` with
the request's content, or `500`. The read loop is proved by induction on the remaining reads,
carrying the bytes read so far (`acc`), the reading of the request body after the events so
far (`istep`) and `BodyOk` along the prefixes of the call.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Exchange
open Silmaril.Servers.Calls
open Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method)

/-- Request getters and body reads do not move the reading of the response. -/
theorem respOf_skip {o : BitVec 32} {f : FnName}
    (hf : f = reqPath ∨ f = reqConsume ∨ f = inStream ∨ f = inRead) (g : FnName) (b a : List Val)
    (n : Option (List Val)) (u : List WEv) :
    respOf o (.req g b :: .imp f a n :: u) = respOf o u := by
  have h : ostep o {} (.imp f a n) = some {} := by
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp [ostep, reqPath, reqConsume, inStream, inRead, setStatus, respBody, bodyWrite,
        streamWrite, bodyFinish, outSet]
  have h0 : ostep o {} (.req g b) = some {} := rfl
  simp [respOf, List.foldlM_cons, h0, h]

/-- The bytes of a list of bytes, back and forth. -/
theorem map_toBitVec_ofBitVec (bs : List (BitVec 8)) :
    (bs.map UInt8.ofBitVec).map UInt8.toBitVec = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons] at ih ⊢; rw [ih]

theorem map_ofBitVec_toBitVec (c : List UInt8) : (c.map UInt8.toBitVec).map UInt8.ofBitVec = c := by
  induction c with
  | nil => rfl
  | cons b c ih => simp only [List.map_cons] at ih ⊢; rw [ih]

theorem istep_req (r : BitVec 32) (st : ISt) (g : FnName) (b : List Val) :
    istep r st (.req g b) = st := rfl

/-- A read on a stream of the request's body delivers its bytes. -/
theorem istep_read_ok {r s : BitVec 32} {st : ISt} (hs : st.streams.contains s = true)
    (a : List Val) (bs : Val) :
    istep r st (.imp inRead (.u32 s :: a) (some [.variant 0 (some bs)])) =
      { st with got := st.got ++ bytesOf bs } := by
  have hs' : s ∈ st.streams := by simpa using hs
  simp [istep, iRead, inRead, reqConsume, inStream, hs']

/-- A read on a stream of the request's body answering `closed`. -/
theorem istep_read_closed {r s : BitVec 32} {st : ISt} (hs : st.streams.contains s = true)
    (a : List Val) :
    istep r st (.imp inRead (.u32 s :: a) (some [.variant 1 (some (.variant 1 none))])) =
      { st with closed := true } := by
  have hs' : s ∈ st.streams := by simpa using hs
  simp [istep, iRead, inRead, reqConsume, inStream, hs']

/-- The responses `echo` may make. -/
def EchoResp (c : List (BitVec 8)) (x : Option Response) : Prop :=
  x = none ∨ x = some (Response.simple 200 (c.map UInt8.ofBitVec)) ∨ x = some failResp

theorem echoResp_fail {c : List (BitVec 8)} {o : BitVec 32} {u : List WEv}
    {r : Option (List Val)} (hl : Leads (answer o failResp) u (.pure r)) :
    EchoResp c (respOf o u) := by
  rcases answer_run rfl (by decide) hl with h | h
  · exact .inl h
  · exact .inr (.inr h)

/-- **The read loop.** -/
theorem loop_run (o s r0 : BitVec 32) (c : List (BitVec 8)) :
    ∀ (n : Nat) (acc : List UInt8) (u : List WEv) (r : Option (List Val)) (pre : List WEv),
      Leads (echoLoop o s n acc) u (.pure r) → (pre.foldl (istep r0) {}).streams.contains s = true →
      (pre.foldl (istep r0) {}).got = acc.map UInt8.toBitVec →
      (∀ v, v <+: pre ++ u → (v.foldl (istep r0) {}).Ok c) → EchoResp c (respOf o u) := by
  intro n
  induction n with
  | zero => intro acc u r pre hl _ _ _; exact echoResp_fail hl
  | succ n ih =>
    intro acc u r pre hl hs hg hB
    obtain ⟨a, u', rfl, h1⟩ := leads_call_pure hl
    show EchoResp c (respOf o (.req inRead [.u32 s, .u64 readLen] ::
      .imp inRead [.u32 s, .u64 readLen] a :: u'))
    rw [respOf_skip (.inr (.inr (.inr rfl)))]
    split at h1
    · rename_i bs
      refine ih _ u' r (pre ++ [.req inRead [.u32 s, .u64 readLen],
        .imp inRead [.u32 s, .u64 readLen] (some [.variant 0 (some bs)])]) h1 ?_ ?_ ?_
      · rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, istep_req, istep_read_ok hs]
        exact hs
      · rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, istep_req, istep_read_ok hs]
        rw [hg, List.map_append, map_toBitVec_ofBitVec]
      · intro v hv
        rw [List.append_assoc] at hv
        exact hB v hv
    · rcases answer_run (resp := Response.simple 200 acc) rfl (show (200 : Nat) < 2 ^ 16 by decide)
        h1 with h | h
      · exact .inl h
      · right; left
        rw [h]
        have hv := hB (pre ++ [.req inRead [.u32 s, .u64 readLen],
          .imp inRead [.u32 s, .u64 readLen] (some [.variant 1 (some (.variant 1 none))])])
          (by simp [pop])
        rw [List.foldl_append] at hv
        simp only [List.foldl_cons, List.foldl_nil, istep_req, istep_read_closed hs] at hv
        have hc := hv.2 rfl
        simp only at hc
        rw [hg] at hc
        rw [← hc, map_ofBitVec_toBitVec]
    · exact echoResp_fail h1

/-- The reading of the request body after `consume` and `stream`. -/
theorem fold_open (r b s : BitVec 32) :
    ([.req reqConsume [.u32 r], .imp reqConsume [.u32 r] (some [.variant 0 (some (.u32 b))]),
      .req inStream [.u32 b], .imp inStream [.u32 b] (some [.variant 0 (some (.u32 s))])] :
        List WEv).foldl (istep r) {} = { bodies := [b], streams := [s] } := by
  simp [istep, iConsume, iStream, reqConsume, inStream]

/-- **Echo answers `200` with the request's content, or `500`**, for every host. -/
theorem echo_sat : Sat (wasiServerB (ofBody echo))
    (each fun q resp => resp = Response.simple 200 q.content ∨ resp = failResp) := by
  refine sat_each fun q c hd hT hans x hx => ?_
  clear hT hans
  rcases c with ⟨fn, args, u, res⟩
  obtain ⟨-, rfl, hl⟩ := hd
  obtain ⟨⟨-, -, hx⟩, hB⟩ := hx
  have key : EchoResp (x.1.content.map UInt8.toBitVec) (respOf (outOf q.2) u) := by
    obtain ⟨n1, u1, rfl, h1⟩ := leads_call_pure hl
    show EchoResp _ (respOf _ (.req reqConsume [.u32 (reqOf q.2)] ::
      .imp reqConsume [.u32 (reqOf q.2)] n1 :: u1))
    rw [respOf_skip (.inr (.inl rfl))]
    split at h1
    · rename_i b
      obtain ⟨n2, u2, rfl, h2⟩ := leads_call_pure h1
      show EchoResp _ (respOf _ (.req inStream [.u32 b] :: .imp inStream [.u32 b] n2 :: u2))
      rw [respOf_skip (.inr (.inr (.inl rfl)))]
      split at h2
      · rename_i s
        refine loop_run (outOf q.2) s (reqOf q.2) _ echoFuel [] u2 _
          [.req reqConsume [.u32 (reqOf q.2)],
            .imp reqConsume [.u32 (reqOf q.2)] (some [.variant 0 (some (.u32 b))]),
            .req inStream [.u32 b], .imp inStream [.u32 b] (some [.variant 0 (some (.u32 s))])]
          h2 ?_ ?_ ?_
        · rw [fold_open]
          simp
        · rw [fold_open]
          rfl
        · exact fun v hv => hB v hv
      · exact echoResp_fail h2
    · exact echoResp_fail h1
  rcases key with h | h | h <;> rw [h] at hx
  · cases hx
  · left
    rw [map_ofBitVec_toBitVec] at hx
    exact (Option.some.inj hx).symm
  · right
    exact (Option.some.inj hx).symm

end Silmaril.Proofs.Servers.WasiExamples
