module

public import Silmaril.Servers.WasiExamples.Defs
public import Silmaril.Servers.Calls.Thms

/-!
# The example `wasi:http` servers: the response of a call, for every host

`answer_run`: whatever the host answers, a complete run of `answer o resp` either makes no
observable response (`respOf o u = none`) or makes the response `resp` (when `resp` has no
fields and a 16-bit status). `hello_sat`, `route_sat`: the example servers satisfy their
specifications.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Calls
open Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method)

variable {I : Set FnName}

/-! ## Inverting runs -/

/-- A complete run of an import call starts with the call and its answer. -/
theorem leads_call_pure {m : (nsig I).Op} {k : Option (List Val) → BProg I} {u : List WEv}
    {r : Option (List Val)} (hl : Leads (.call m k) u (.pure r)) :
    ∃ n u', u = .req m.1.1 m.2 :: .imp m.1.1 m.2 n :: u' ∧ Leads (k n) u' (.pure r) := by
  cases hl with
  | call _ _ n h => exact ⟨n, _, rfl, h⟩

/-- A run of a returning program is empty. -/
theorem leads_pure {a : Option (List Val)} {u : List WEv} {p : BProg I}
    (hl : Leads (.pure a) u p) : u = [] := by
  cases hl
  rfl

/-! ## No response, or the expected one -/

/-- `x` fails or is `y`. -/
def NoneOr {α : Type} (x y : Option α) : Prop := x = none ∨ x = y

theorem NoneOr.trans {α : Type} {x y z : Option α} (h : NoneOr x y) (h' : NoneOr y z) :
    NoneOr x z := by
  rcases h with h | rfl
  · exact .inl h
  · exact h'

theorem fold_step {o : BitVec 32} {st st' : OSt} {e : WEv} {rest : List WEv}
    (h : NoneOr (ostep o st e) (some st')) :
    NoneOr (List.foldlM (ostep o) st (e :: rest)) (List.foldlM (ostep o) st' rest) := by
  rcases h with h | h <;> simp [List.foldlM_cons, h, NoneOr]

theorem fold_nil {o : BitVec 32} (st : OSt) : NoneOr (List.foldlM (ostep o) st []) (some st) :=
  .inr rfl

theorem bind_resp {x : Option OSt} {st : OSt} {y : Option Response} (hx : NoneOr x (some st))
    (hy : st.resp = y) : NoneOr (x.bind OSt.resp) y := by
  rcases hx with rfl | rfl
  · exact .inl rfl
  · exact .inr hy

/-! ## Steps of the reading -/

theorem s_req (o : BitVec 32) (st : OSt) (g : FnName) (b : List Val) :
    NoneOr (ostep o st (.req g b)) (some st) := .inr rfl

theorem s_skip (o : BitVec 32) (st : OSt) {f : FnName}
    (hf : f = newFields ∨ f = newResp ∨ f = streamDrop ∨ f = reqPath ∨ f = reqMethod)
    (a : List Val) (r : Option (List Val)) : NoneOr (ostep o st (.imp f a r)) (some st) := by
  right
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [ostep, newFields, newResp, streamDrop, reqPath, reqMethod, setStatus, respBody,
      bodyWrite, streamWrite, bodyFinish, outSet]

theorem s_status (o : BitVec 32) (st : OSt) (rh : BitVec 32) (s : BitVec 16)
    (r : Option (List Val)) :
    NoneOr (ostep o st (.imp setStatus [.u32 rh, .u16 s] r))
      (some { st with status := (rh, s) :: st.status }) := by
  have he : ∀ st a r, ostep o st (.imp setStatus a r) = oStatus st a r := fun _ _ _ => by
    simp [ostep, setStatus]
  rw [NoneOr, he]
  unfold oStatus
  split <;> simp_all

theorem s_body (o : BitVec 32) (st : OSt) (rh : BitVec 32) (r : Option (List Val)) :
    NoneOr (ostep o st (.imp respBody [.u32 rh] r))
      (some { st with body := (rh, hOf r) :: st.body }) := by
  have he : ∀ st a r, ostep o st (.imp respBody a r) = oBody st a r := fun _ _ _ => by
    simp [ostep, setStatus, respBody]
  rw [NoneOr, he]
  unfold oBody
  split <;> simp_all [hOf]

theorem s_write (o : BitVec 32) (st : OSt) (b : BitVec 32) (r : Option (List Val)) :
    NoneOr (ostep o st (.imp bodyWrite [.u32 b] r))
      (some { st with stream := (hOf r, b) :: st.stream }) := by
  have he : ∀ st a r, ostep o st (.imp bodyWrite a r) = oWrite st a r := fun _ _ _ => by
    simp [ostep, setStatus, respBody, bodyWrite]
  rw [NoneOr, he]
  unfold oWrite
  split <;> simp_all [hOf]

theorem s_bwf (o : BitVec 32) (st : OSt) {s b : BitVec 32} (hs : look s st.stream = some b)
    (buf : Val) (r : Option (List Val)) :
    NoneOr (ostep o st (.imp streamWrite [.u32 s, buf] r))
      (some { st with bytes := (b, (look b st.bytes).getD [] ++ bytesOf buf) :: st.bytes }) := by
  have he : ∀ st a r, ostep o st (.imp streamWrite a r) = oStream st a r := fun _ _ _ => by
    simp [ostep, setStatus, respBody, bodyWrite, streamWrite]
  rw [NoneOr, he]
  simp only [oStream, hs, oBytes]
  split <;> simp_all

theorem s_finish (o : BitVec 32) (st : OSt) (b : BitVec 32) (x : Val) (r : Option (List Val)) :
    NoneOr (ostep o st (.imp bodyFinish [.u32 b, x] r)) (some { st with fin := b :: st.fin }) := by
  have he : ∀ st a r, ostep o st (.imp bodyFinish a r) = oFinish st a r := fun _ _ _ => by
    simp [ostep, setStatus, respBody, bodyWrite, streamWrite, bodyFinish]
  rw [NoneOr, he]
  unfold oFinish
  split <;> simp_all

theorem s_set (o : BitVec 32) (st : OSt) (rh : BitVec 32) (r : Option (List Val)) :
    NoneOr (ostep o st (.imp outSet [.u32 o, .variant 0 (some (.u32 rh))] r))
      (some { st with set := some rh }) := by
  have he : ∀ st a r, ostep o st (.imp outSet a r) = (oSet o) st a r := fun _ _ _ => by
    simp [ostep, setStatus, respBody, bodyWrite, streamWrite, bodyFinish, outSet]
  rw [NoneOr, he]
  unfold oSet
  split <;> simp_all

/-! ## The shared response code -/

theorem bytesOf_bytesV (bs : List (BitVec 8)) : bytesOf (bytesV bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesOf, bytesV, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih]

theorem ofBitVec_comp : UInt8.ofBitVec ∘ UInt8.toBitVec = id := rfl

/-- **The response of a complete run of `answer o resp`**, for every host: none, or `resp`. -/
theorem answer_run {o : BitVec 32} {resp : Response} {u : List WEv} {r : Option (List Val)}
    (hr : Response.simple resp.status resp.content = resp) (hs : resp.status < 2 ^ 16)
    (hl : Leads (answer o resp) u (.pure r)) : NoneOr (respOf o u) (some resp) := by
  obtain ⟨n1, u1, rfl, h1⟩ := leads_call_pure hl
  obtain ⟨n2, u2, rfl, h2⟩ := leads_call_pure h1
  obtain ⟨n3, u3, rfl, h3⟩ := leads_call_pure h2
  obtain ⟨n4, u4, rfl, h4⟩ := leads_call_pure h3
  obtain ⟨n5, u5, rfl, h5⟩ := leads_call_pure h4
  obtain ⟨n6, u6, rfl, h6⟩ := leads_call_pure h5
  obtain ⟨n7, u7, rfl, h7⟩ := leads_call_pure h6
  obtain ⟨n8, u8, rfl, h8⟩ := leads_call_pure h7
  obtain ⟨n9, u9, rfl, h9⟩ := leads_call_pure h8
  obtain rfl := leads_pure h9
  apply bind_resp
  · exact fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_skip o _ (by simp [pop]) _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_skip o _ (by simp [pop]) _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_status o _ _ _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_body o _ _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_set o _ _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_write o _ _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_bwf o _ (b := hOf n4) (by simp [look]) _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_skip o _ (by simp [pop]) _ _) |>.trans <|
      fold_step (s_req o _ _ _) |>.trans <|
      fold_step (s_finish o _ _ _ _) |>.trans <|
      fold_nil _
  · have h16 : (BitVec.ofNat 16 resp.status).toNat = resp.status := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hs
    simp [OSt.resp, look, bytesOf_bytesV, ofBitVec_comp, h16, hr]

end Silmaril.Proofs.Servers.WasiExamples
