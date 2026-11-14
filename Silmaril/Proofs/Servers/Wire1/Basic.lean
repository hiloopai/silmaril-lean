module

public import Silmaril.Servers.Wire1.Defs
public import Silmaril.Net.Http1.Framing.Thms
public import Mathlib.Data.List.Forall2

/-!
# HTTP/1.1 framing of a connection: proofs

For `Silmaril.Servers.Wire1.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Wire1

open Silmaril.Net Silmaril.Net.Http1 Silmaril.Parse.ByteParse Silmaril.Servers.Wire1

theorem size_ofList (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  simp only [ByteArray.size, List.size_toArray]

theorem encRequest_pos (h : RequestHead) (b : Http1.Body) : 0 < (encRequest h b).length := by
  have : 0 < (encRequestLine h.line).length := by
    simp only [encRequestLine, List.length_append, List.length_cons, List.length_nil]; omega
  simp only [encRequest, encRequestHead, List.length_append]; omega

theorem length_le_encRequests : ∀ ms : List WireReq, ms.length ≤ (encRequests ms).length
  | [] => by simp [encRequests]
  | m :: ms => by
    have := length_le_encRequests ms
    have := encRequest_pos m.1 m.2
    simp only [encRequests, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

theorem parseRequests_encode : ∀ (ms : List WireReq) (pre : List UInt8) (fuel : Nat),
    (∀ m ∈ ms, ReqOk m) → ms.length ≤ fuel →
    parseRequests ⟨(pre ++ encRequests ms).toArray⟩ fuel pre.length = ms
  | [], pre, fuel, _, _ => by
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have : ¬ pre.length < (⟨(pre ++ encRequests []).toArray⟩ : ByteArray).size := by
        rw [size_ofList]; simp [encRequests]
      simp only [parseRequests, this, ↓reduceIte]
  | (_ :: _), _, 0, _, hl => absurd hl (by simp)
  | (h, b) :: ms, pre, fuel + 1, hv, hl => by
    have hm := hv (h, b) List.mem_cons_self
    have e : pre ++ encRequests ((h, b) :: ms) = pre ++ encRequest h b ++ encRequests ms := by
      simp [encRequests]
    have hp := parseRequestAt_encode hm.1 hm.2 pre (encRequests ms)
    have ih := parseRequests_encode ms (pre ++ encRequest h b) fuel
      (fun x hx => hv x (List.mem_cons_of_mem _ hx)) (by simp at hl; omega)
    have hpos := encRequest_pos h b
    have hsz : pre.length < (⟨(pre ++ encRequest h b ++ encRequests ms).toArray⟩ : ByteArray).size := by
      rw [size_ofList]; simp only [List.length_append]; omega
    have hk : pre.length < pre.length + (encRequest h b).length := by omega
    rw [e]
    simp only [parseRequests, hsz, ↓reduceIte, hp, hk, List.cons.injEq, true_and]
    simpa only [List.length_append] using ih

theorem parseResponses_encode {methods : List Bytes} {ms : List WireResp}
    (hf : List.Forall₂ RespOk methods ms) :
    ∀ pre : List UInt8, parseResponses ⟨(pre ++ encResponses ms).toArray⟩ methods pre.length = ms := by
  induction hf with
  | nil => intro _; rfl
  | @cons meth m mths ms hm _ ih =>
    intro pre
    obtain ⟨h, b⟩ := m
    have e : pre ++ encResponses ((h, b) :: ms) = pre ++ encResponse h b ++ encResponses ms := by
      simp [encResponses]
    have hp := parseResponseAt_encode hm.1 hm.2 pre (encResponses ms)
    have ih' := ih (pre ++ encResponse h b)
    rw [e]
    simp only [parseResponses, hp, List.cons.injEq, true_and]
    simpa only [List.length_append] using ih'

theorem toToken_ofToken (t : List UInt8) : (Http.Method.ofToken t).toToken = t := by
  unfold Http.Method.ofToken
  split
  · next m hm => simpa using List.find?_some hm
  · rfl

end Silmaril.Proofs.Servers.Wire1
