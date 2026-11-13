module

public import Silmaril.Proofs.Servers.WasiExamples.Answer

/-!
# The greeting server: reading a request header

`greet_sat`: every exchange of `greet` answers `200 hello <first value of x-name>`, or `500`.
The value comes from the header answers of the reading (`HdrOk`): the answer of `fields.get`
on the headers resource taken from the request is the request's list of values for the name.
`greet_serveRef`, `greet_answers`: over the reference host, every request is answered with its
greeting, so the specification is not vacuous.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Exchange
open Silmaril.Servers.Calls
open Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method)

/-- The greeting answers with a 16-bit status and no trailers. -/
theorem greetResp_ok (vs : List (List UInt8)) :
    (greetResp vs).trailers = [] ∧ (greetResp vs).status < 2 ^ 16 :=
  ⟨rfl, show 200 < 2 ^ 16 by decide⟩

theorem failResp_ok : failResp.trailers = [] ∧ failResp.status < 2 ^ 16 := ⟨rfl, by decide⟩

/-- The first value of a list of values read back. -/
theorem firstValue_valuesV (vs : List (List UInt8)) : firstValue (some [valuesV vs]) = vs.head? := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [valuesV, List.map_cons, firstValue, List.head?_cons, octV, bytesOf_bytesV,
      map_ofBitVec_toBitVec]

/-- An import call outside the response code does not change the response. -/
theorem respOf_skipH (o : BitVec 32) {f : FnName} (hf : f = reqHeaders ∨ f = fieldsGet)
    (a : List Val) (n : Option (List Val)) (u : List WEv) :
    respOf o (.req f a :: .imp f a n :: u) = respOf o u := by
  have h : ostep o {} (.imp f a n) = some {} := by
    rcases hf with rfl | rfl <;>
      simp [ostep, reqHeaders, fieldsGet, setStatus, respBody, bodyWrite, streamWrite, bodyFinish,
        outSet, newResp, fieldsAppend]
  have h0 : ostep o {} (.req f a) = some {} := rfl
  simp [respOf, List.foldlM_cons, h0, h]

/-- The headers resource answered by `headers()` is one of the request's. -/
theorem reqHs_headers (r h : BitVec 32) (a : List Val) :
    reqHs r [.req reqHeaders [.u32 r], .imp reqHeaders [.u32 r] (some [.u32 h]), .req fieldsGet a] =
      [h] := by
  simp [reqHs]

/-- **Greeting** answers every request with the greeting of its `x-name` values, or `500`, for
every host. -/
theorem greet_sat : Sat (wasiServer (ofBody greet))
    (each fun q resp => resp = greetResp (q.headers.values nameHdr) ∨ resp = failResp) := by
  refine sat_each fun q c ⟨_, ha, hl⟩ _ _ x hx => ?_
  obtain ⟨n, u, hu, hl⟩ := leads_call_pure hl
  simp only [pop] at hu
  split at hl
  · rename_i h
    obtain ⟨v, w, hw, hl⟩ := leads_call_pure hl
    simp only [pop] at hw
    have hv : v = some [valuesV (x.1.headers.values nameHdr)] := by
      have hh := hx.2.2.1 [.req reqHeaders [.u32 (reqOf q.2)],
        .imp reqHeaders [.u32 (reqOf q.2)] (some [.u32 h]),
        .req fieldsGet [.u32 h, strV nameHdr]] (.imp fieldsGet [.u32 h, strV nameHdr] v) w
        (by rw [hu, hw]; rfl)
      rw [ha, reqHs_headers] at hh
      have := (hh (List.mem_singleton_self h)).1 rfl _ rfl
      rwa [octetsOf_map] at this
    subst hv
    rw [firstValue_valuesV] at hl
    left
    refine obs_of_run ?_ hx
    rw [ha, hu, hw, respOf_skipH _ (.inl rfl), respOf_skipH _ (.inr rfl)]
    exact answer_run (greetResp_ok _).1 (greetResp_ok _).2 hl
  · right
    refine obs_of_run ?_ hx
    rw [ha, hu, respOf_skipH _ (.inl rfl)]
    exact answer_run failResp_ok.1 failResp_ok.2 hl

/-- Greeting over the reference host answers the greeting of the request. -/
theorem greet_serveRef (q : Request) :
    serveRef greet q = some (greetResp (q.headers.values nameHdr)) := by
  have hrun : (runP (refHost q) [] (greet handleQ)).1 =
      .req reqHeaders [.u32 0] :: .imp reqHeaders [.u32 0] (some [.u32 2]) ::
        .req fieldsGet [.u32 2, strV nameHdr] ::
        .imp fieldsGet [.u32 2, strV nameHdr] (some [valuesV (q.headers.values nameHdr)]) ::
        (runP (refHost q) [.imp reqHeaders [.u32 0] (some [.u32 2]),
          .imp fieldsGet [.u32 2, strV nameHdr] (some [valuesV (q.headers.values nameHdr)])]
          (answer 1 (greetResp (q.headers.values nameHdr)))).1 := by
    simp [runP, greet, handleQ, refHost, pop, reqOf, outOf, reqMethod, reqPath, reqHeaders,
      fieldsGet, fieldsEntries, fieldsAppend, newFields, newResp, WasiHttp.strV, octetsOf_map, nameArg,
      firstValue_valuesV, greetResp]
  unfold serveRef
  rw [hrun, respOf_skipH _ (.inl rfl), respOf_skipH _ (.inr rfl)]
  exact answer_ok (greetResp_ok _).1 (greetResp_ok _).2 (leads_runP _ _ _)
    fun f a n hm => (imp_runP hm).elim fun _ e => e ▸ refHost_ok q _ f a

/-- **Greeting is not vacuous**: every request answered with its greeting is a trace. -/
theorem greet_answers (q : Request) :
    [(q, greetResp (q.headers.values nameHdr))] ∈ wasiServer (ofBody greet) :=
  serve_mem (greet_serveRef q)

end Silmaril.Proofs.Servers.WasiExamples
