module

public import Silmaril.Servers.WireExch.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Servers.WireExch.Basic

/-!
# HTTP/1.1 exchanges: round trips

PROVED (standard axioms):

* **`exchanges_encode`**: exchanges sent back to back, each a list of interim responses
  (valid, `1xx` other than `101`, no body) and a final response that is not interim and fits
  the framing its head announces after its request's method, are read back exactly, whether or
  not the connection is closed.
* **`exchanges_encode_close`**: if, in addition, the last exchange's final response is
  delimited by closing the connection (`CloseOk`), it is read back once the server has closed
  the connection;
* **`exchanges_encode_open`**: and it is not read while the connection is open (its body could
  still grow).
* `final_exchanges_encode`: the final responses of `framingC` are those of the exchanges.
-/

@[expose] public section

namespace Silmaril.Servers.WireExch

open Silmaril.Net Silmaril.Net.Http1 Silmaril.Servers.Wire1

/-- An exchange read as an `Http.exchSig` response. -/
def toExch (x : List WireResp × WireResp) : List Http.Response × Http.Response :=
  (x.1.map toResponse, toResponse x.2)

/-- **Round trip of the exchanges of a connection.** -/
theorem exchanges_encode (closed : Bool) (rs : List Http.Request)
    (xs : List (List WireResp × WireResp))
    (hx : List.Forall₂ (fun r x => ExchOk r.method.toToken x) rs xs) :
    exchanges closed rs (encExchs xs) = xs.map toExch := by
  have := Proofs.Servers.WireExch.parseExchs_encode (closed := closed)
    (List.forall₂_map_left_iff.mpr hx) [] [] []
  simp only [List.nil_append, List.append_nil, List.length_nil] at this
  simp only [exchanges, this, parseExchs, List.append_nil]
  rfl

theorem exchanges_close_aux (closed : Bool) (rs : List Http.Request)
    (xs : List (List WireResp × WireResp))
    (hx : List.Forall₂ (fun r x => ExchOk r.method.toToken x) rs xs) (r : Http.Request)
    (x : List WireResp × WireResp) (hi : ∀ m ∈ x.1, InterimOk m)
    (hc : CloseOk r.method.toToken x.2) :
    exchanges closed (rs ++ [r]) (encExchs xs ++ encExch x) =
      (xs ++ if closed then [x] else []).map toExch := by
  have := Proofs.Servers.WireExch.parseExchs_encode (closed := closed)
    (List.forall₂_map_left_iff.mpr hx) [] (encExch x) [r.method.toToken]
  simp only [List.nil_append, List.length_nil] at this
  rw [Proofs.Servers.WireExch.parseExchs_close hi hc] at this
  unfold exchanges
  rw [List.map_append, List.map_singleton, this, List.map_append, List.map_append]
  rfl

/-- **A close-delimited last response is read once the connection is closed.** -/
theorem exchanges_encode_close (rs : List Http.Request) (xs : List (List WireResp × WireResp))
    (hx : List.Forall₂ (fun r x => ExchOk r.method.toToken x) rs xs) (r : Http.Request)
    (x : List WireResp × WireResp) (hi : ∀ m ∈ x.1, InterimOk m)
    (hc : CloseOk r.method.toToken x.2) :
    exchanges true (rs ++ [r]) (encExchs xs ++ encExch x) = (xs ++ [x]).map toExch := by
  simpa using exchanges_close_aux true rs xs hx r x hi hc

/-- **… and not before.** -/
theorem exchanges_encode_open (rs : List Http.Request) (xs : List (List WireResp × WireResp))
    (hx : List.Forall₂ (fun r x => ExchOk r.method.toToken x) rs xs) (r : Http.Request)
    (x : List WireResp × WireResp) (hi : ∀ m ∈ x.1, InterimOk m)
    (hc : CloseOk r.method.toToken x.2) :
    exchanges false (rs ++ [r]) (encExchs xs ++ encExch x) = xs.map toExch := by
  simpa using exchanges_close_aux false rs xs hx r x hi hc

/-- The final responses of `framingC`. -/
theorem final_exchanges_encode (closed : Bool) (rs : List Http.Request)
    (xs : List (List WireResp × WireResp))
    (hx : List.Forall₂ (fun r x => ExchOk r.method.toToken x) rs xs) :
    (framingC closed).responses rs (encExchs xs) = xs.map fun x => toResponse x.2 := by
  simp only [framingC, exchanges_encode closed rs xs hx, List.map_map]
  rfl

end Silmaril.Servers.WireExch
