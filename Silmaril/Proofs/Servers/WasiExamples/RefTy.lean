module

public import Silmaril.Proofs.Servers.WasiExamples.Answer
public import Silmaril.Servers.WasiCore.Defs

/-!
# The reference host is typed

`refHost_ty`: every answer of the reference host has the WIT result type of its function
(`AnsTy`). `serve_memTy`: a response over the reference host is a trace of the component read
as a server over typed hosts, the typed version of `serve_mem`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Exchange
open Silmaril.Servers.Calls Silmaril.Servers.WasiCore
open Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method)

set_option linter.unusedSimpArgs false in
/-- **The reference host's answers are typed.** -/
theorem refHost_ty (q : Request) (past : List WEv) (f : FnName) (a : List Val) :
    AnsTy f (refHost q past f a) := by
  by_cases h0 : f = reqMethod
  · subst h0
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h1 : f = reqPath
  · subst h1
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp only [pathV]
    cases q.target.pathWithQuery with
    | none => simp
    | some p =>
      simp only [WasiHttp.strV]
      exact .inr ⟨p.map fun b => Char.ofNat b.toNat, by simp⟩
  by_cases h2 : f = fieldsGet
  · subst h2
    have e : refHost q past fieldsGet a = some [valuesV (q.headers.values (nameArg a))] := by
      simp [refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend]
    rw [e]
    simp only [AnsTy, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp only [String.reduceEq, and_false, and_true, false_or, or_false, ↓reduceIte, true_or]
    exact ⟨(q.headers.values (nameArg a)).map (List.map UInt8.toBitVec), by
      simp [valuesV, octV, Function.comp_def]⟩
  by_cases h3 : f = fieldsEntries
  · subst h3
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h4 : f = fieldsAppend
  · subst h4
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h5 : f = newFields
  · subst h5
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h6 : f = newResp
  · subst h6
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h7 : f = reqHeaders
  · subst h7
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h8 : f = respBody
  · subst h8
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h9 : f = bodyWrite
  · subst h9
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h10 : f = setStatus
  · subst h10
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h11 : f = streamWrite
  · subst h11
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h12 : f = bodyFinish
  · subst h12
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h13 : f = streamDrop
  · subst h13
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h14 : f = outSet
  · subst h14
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h15 : f = reqConsume
  · subst h15
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h16 : f = inStream
  · subst h16
    simp only [AnsTy, refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp [okV, errV]
  by_cases h17 : f = inRead
  · subst h17
    have e : refHost q past inRead a = if past.any isReadAns then
        some [errV (some (.variant 1 none))] else
        some [okV (some (bytesV (q.content.map UInt8.toBitVec)))] := by
      simp [refHost, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend]
    rw [e]
    simp only [AnsTy, reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet, streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries, fieldsAppend, FnName.mk.injEq]
    simp only [String.reduceEq, and_false, and_true, false_or, or_false, ↓reduceIte, true_or]
    by_cases hp : past.any isReadAns = true
    · simp only [hp, ↓reduceIte]
      exact .inr (.inl (by simp [errV]))
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact .inl ⟨_, rfl⟩
  simp only [AnsTy, refHost, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    or_self, ↓reduceIte]

/-- **A response over the reference host is a trace** of the component read as a server over
typed hosts. -/
theorem serve_memTy {h : Body proxyImports proxyWorld.exports} {q : Request} {x : Response}
    (hx : serveRef h q = some x) : [(q, x)] ∈ wasiServerTy (ofBody h) := by
  refine mem_model_single (q := handleQ) (leads_runP (refHost q) [] (h handleQ)) ?_
    (obs_ref hx).1 (obs_ref hx).2
  intro e he
  simp only [Call.events, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at he
  rcases he with rfl | he | rfl
  · trivial
  · cases e with
    | imp f a n =>
      obtain ⟨past', rfl⟩ := imp_runP he
      exact refHost_ty q past' f a
    | req => trivial
    | call => trivial
    | ret => trivial
  · trivial

end Silmaril.Proofs.Servers.WasiExamples
