module

public import Silmaril.Servers.WasiExamples.Defs
public import Silmaril.Servers.Calls.Thms
public import Silmaril.Servers.WasiHttp.Thms

/-!
# The example `wasi:http` servers: the response of a call, for every host

`answer_run`: whatever the host answers, a complete run of `answer o resp` either makes no
observable response (`respOf o u = none`) or makes the response `resp` (when `resp` has no
fields and a 16-bit status). `hello_sat`, `route_sat`: the example servers satisfy their
specifications.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Exchange
open Silmaril.Servers.Calls
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

/-! ## Exact steps on successful answers -/

theorem fold_eq {o : BitVec 32} {st st' : OSt} {e : WEv} {rest : List WEv}
    (h : ostep o st e = some st') :
    List.foldlM (ostep o) st (e :: rest) = List.foldlM (ostep o) st' rest := by
  simp [List.foldlM_cons, h]

theorem x_req (o : BitVec 32) (st : OSt) (g : FnName) (b : List Val) :
    ostep o st (.req g b) = some st := rfl

theorem x_skip (o : BitVec 32) (st : OSt) {f : FnName}
    (hf : f = newFields ∨ f = newResp ∨ f = streamDrop ∨ f = reqPath ∨ f = reqMethod)
    (a : List Val) (r : Option (List Val)) : ostep o st (.imp f a r) = some st := by
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [ostep, newFields, newResp, streamDrop, reqPath, reqMethod, setStatus, respBody,
      bodyWrite, streamWrite, bodyFinish, outSet]

theorem x_status (o : BitVec 32) (st : OSt) (rh : BitVec 32) (s : BitVec 16) :
    ostep o st (.imp setStatus [.u32 rh, .u16 s] (some [okV none])) =
      some { st with status := (rh, s) :: st.status } := by
  simp [ostep, oStatus, okV]

theorem x_body (o : BitVec 32) (st : OSt) (rh b : BitVec 32) :
    ostep o st (.imp respBody [.u32 rh] (some [okV (some (.u32 b))])) =
      some { st with body := (rh, b) :: st.body } := by
  simp [ostep, oBody, okV, respBody, setStatus]

theorem x_write (o : BitVec 32) (st : OSt) (b s : BitVec 32) :
    ostep o st (.imp bodyWrite [.u32 b] (some [okV (some (.u32 s))])) =
      some { st with stream := (s, b) :: st.stream } := by
  simp [ostep, oWrite, okV, bodyWrite, respBody, setStatus]

theorem x_bwf (o : BitVec 32) (st : OSt) {s b : BitVec 32} (hs : look s st.stream = some b)
    (buf : Val) :
    ostep o st (.imp streamWrite [.u32 s, buf] (some [okV none])) =
      some { st with bytes := (b, (look b st.bytes).getD [] ++ bytesOf buf) :: st.bytes } := by
  simp [ostep, oStream, oBytes, hs, okV, streamWrite, bodyWrite, respBody, setStatus]

theorem x_finish (o : BitVec 32) (st : OSt) (b : BitVec 32) (x : Val) :
    ostep o st (.imp bodyFinish [.u32 b, x] (some [okV none])) =
      some { st with fin := b :: st.fin } := by
  simp [ostep, oFinish, okV, bodyFinish, streamWrite, bodyWrite, respBody, setStatus]

theorem x_set (o : BitVec 32) (st : OSt) (rh : BitVec 32) :
    ostep o st (.imp outSet [.u32 o, .variant 0 (some (.u32 rh))] (some [])) =
      some { st with set := some rh } := by
  simp [ostep, oSet, outSet, bodyFinish, streamWrite, bodyWrite, respBody, setStatus]

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

/-! ## The example servers -/

/-- The response of an answered call of a body whose runs answer `resp`. -/
theorem obs_of_run {c : Call} {x : Exch httpIface} {resp : Response}
    (hrun : NoneOr (respOf (outOf c.args) c.inner) (some resp)) (hx : Obs c x) : x.2 = resp := by
  obtain ⟨-, -, hx⟩ := hx
  rcases hrun with h | h <;> rw [h] at hx
  · cases hx
  · exact (Option.some.inj hx).symm

/-- **Hello** answers every request `200 hello`, for every host. -/
theorem hello_sat : Sat (wasiServer (ofBody hello)) (each fun _ resp => resp = helloResp) := by
  refine sat_each fun q c ⟨_, ha, hl⟩ _ _ x hx => obs_of_run ?_ hx
  rw [ha]
  exact answer_run rfl (by decide) hl

/-- The route table answers with a 16-bit status and no fields. -/
theorem routeResp_ok (p : Option (List UInt8)) :
    Response.simple (routeResp p).status (routeResp p).content = routeResp p ∧
      (routeResp p).status < 2 ^ 16 := by
  unfold routeResp
  split_ifs <;> exact ⟨rfl, by decide⟩

/-- Reading the path does not change the response. -/
theorem respOf_path (o r : BitVec 32) (n : Option (List Val)) (u : List WEv) :
    respOf o (.req reqPath [.u32 r] :: .imp reqPath [.u32 r] n :: u) = respOf o u := by
  have h : ostep o {} (.imp reqPath [.u32 r] n) = some {} := by
    simp [ostep, reqPath, setStatus, respBody, bodyWrite, streamWrite, bodyFinish, outSet]
  have h0 : ostep o {} (.req reqPath [.u32 r]) = some {} := rfl
  simp [respOf, List.foldlM_cons, h0, h]

/-- **Routing** answers every request from the route table on its path, for every host. -/
theorem route_sat :
    Sat (wasiServer (ofBody route)) (each fun q resp => resp = routeResp q.target.pathWithQuery) := by
  refine sat_each fun q c ⟨_, ha, hl⟩ _ _ x hx => ?_
  obtain ⟨n, u, hu, hl⟩ := leads_call_pure hl
  have hn : n = some [pathV x.1.target.pathWithQuery] := by
    have h := hx.2.1 (.imp reqPath [.u32 (reqOf q.2)] n) (by rw [hu]; simp [pop])
    rw [ha] at h
    exact (h rfl).2 rfl
  subst hn
  rw [pathOf_pathV] at hl
  refine obs_of_run ?_ hx
  rw [hu, ha]
  exact (respOf_path _ _ _ _).symm ▸
    answer_run (routeResp_ok _).1 (routeResp_ok _).2 hl

/-! ## Hello answers -/

/-- An answer of another function than the request getters is consistent with every request. -/
theorem reqOk_other {q : Request} {r : BitVec 32} {f : FnName} {a : List Val}
    {res : Option (List Val)} (h1 : f ≠ reqMethod) (h2 : f ≠ reqPath) :
    ReqOk q r (.imp f a res) := by
  unfold ReqOk
  split <;> simp_all

/-- **Hello is not vacuous**: every request answered `200 hello` is a trace of hello, over a
host whose answers are well formed. -/
theorem hello_answers (q : Request) : [(q, helloResp)] ∈ wasiServer (ofBody hello) := by
  refine mem_model_single (q := handleQ)
    (.call _ _ (some [.u32 1]) <| .call _ _ (some [.u32 2]) <| .call _ _ (some [okV none]) <|
      .call _ _ (some [okV (some (.u32 3))]) <| .call _ _ (some []) <|
      .call _ _ (some [okV (some (.u32 4))]) <| .call _ _ (some [okV none]) <|
      .call _ _ (some []) <| .call _ _ (some [okV none]) <| .refl _)
    (fun _ _ => trivial) rfl ⟨rfl, ?_, rfl⟩
  simp only [List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ h => by simp at h⟩ <;>
    first | trivial | (apply reqOk_other <;> decide)

/-! ## Answers over well-behaved hosts -/

/-- The answer `n` of `f` is the successful one. -/
def OkAns (f : FnName) (n : Option (List Val)) : Prop :=
  ((f = setStatus ∨ f = streamWrite ∨ f = bodyFinish) → n = some [okV none]) ∧
    ((f = respBody ∨ f = bodyWrite) → ∃ h, n = some [okV (some (.u32 h))]) ∧
    (f = outSet → n = some [])

theorem resp_of_fold {x : Option OSt} {st : OSt} {y : Option Response} (hx : x = some st)
    (hy : st.resp = y) : x.bind OSt.resp = y := by
  rw [hx]
  exact hy

/-- **Over a host whose answers succeed**, `answer o resp` makes the response `resp`. -/
theorem answer_ok {o : BitVec 32} {resp : Response} {u : List WEv} {r : Option (List Val)}
    (hr : Response.simple resp.status resp.content = resp) (hs : resp.status < 2 ^ 16)
    (hl : Leads (answer o resp) u (.pure r)) (hok : ∀ f a n, WEv.imp f a n ∈ u → OkAns f n) :
    respOf o u = some resp := by
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
  have k3 := (hok setStatus [.u32 (hOf n2), .u16 (BitVec.ofNat 16 resp.status)] n3 (by simp [pop])).1 (.inl rfl)
  obtain ⟨b, k4⟩ := (hok respBody [.u32 (hOf n2)] n4 (by simp [pop])).2.1 (.inl rfl)
  have k5 := (hok outSet [.u32 o, okV (some (.u32 (hOf n2)))] n5 (by simp [pop])).2.2 rfl
  obtain ⟨s, k6⟩ := (hok bodyWrite [.u32 (hOf n4)] n6 (by simp [pop])).2.1 (.inr rfl)
  have k7 := (hok streamWrite [.u32 (hOf n6), bytesV (resp.content.map UInt8.toBitVec)] n7
    (by simp [pop])).1 (.inr (.inl rfl))
  have k9 := (hok bodyFinish [.u32 (hOf n4), .variant 0 none] n9 (by simp [pop])).1 (.inr (.inr rfl))
  subst k3 k4 k5 k6 k7 k9
  have h16 : (BitVec.ofNat 16 resp.status).toNat = resp.status := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hs
  apply resp_of_fold
  · exact (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_skip o _ (by simp [pop]) _ _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_skip o _ (by simp [pop]) _ _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_status o _ _ _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_body o _ _ _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_set o _ _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_write o _ _ _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <|
    (fold_eq (x_bwf o _ (s := s) (b := b) (by simp [look, hOf, okV]) _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_skip o _ (by simp [pop]) _ _)).trans <|
    (fold_eq (x_req o _ _ _)).trans <| (fold_eq (x_finish o _ _ _)).trans rfl
  · simp [OSt.resp, look, hOf, okV, bytesOf_bytesV, ofBitVec_comp, h16, hr]

/-- The answers of a run over a concrete host are the host's. -/
theorem imp_runP {impl : Impl} {past : List WEv} {p : BProg proxyImports} {f : FnName}
    {a : List Val} {n : Option (List Val)} (h : WEv.imp f a n ∈ (runP impl past p).1) :
    ∃ past', n = impl past' f a := by
  induction p generalizing past with
  | pure r => simp [runP] at h
  | call m k ih =>
    simp only [runP, List.mem_cons] at h
    rcases h with h | h | h
    · cases h
    · obtain ⟨rfl, rfl, rfl⟩ := WEv.imp.inj h
      exact ⟨past, rfl⟩
    · exact ih _ h

/-- The reference host's answers succeed. -/
theorem refHost_ok (q : Request) (past : List WEv) (f : FnName) (a : List Val) :
    OkAns f (refHost q past f a) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (rfl | rfl | rfl) <;>
      simp [refHost, reqMethod, reqPath, newFields, newResp, respBody, bodyWrite, setStatus,
        streamWrite, bodyFinish]
  · rintro (rfl | rfl) <;>
      simp [refHost, okV, reqMethod, reqPath, newFields, newResp, respBody, bodyWrite]
  · rintro rfl
    simp [refHost, reqMethod, reqPath, newFields, newResp, respBody, bodyWrite, setStatus,
      streamWrite, bodyFinish, streamDrop, outSet]

/-- The reference host's answers are consistent with its request. -/
theorem reqOk_runP (q : Request) (r : BitVec 32) (past : List WEv) (p : BProg proxyImports) :
    ∀ e ∈ (runP (refHost q) past p).1, ReqOk q r e := by
  intro e he
  cases e with
  | imp f a n =>
    obtain ⟨past', rfl⟩ := imp_runP he
    unfold ReqOk
    split
    · rename_i hm
      obtain ⟨rfl, rfl, rfl⟩ := WEv.imp.inj hm
      refine fun _ => ⟨?_, ?_⟩ <;> rintro rfl <;> simp [refHost, reqMethod, reqPath]
    · trivial
  | req => trivial
  | call => trivial
  | ret => trivial

/-- **A response over the reference host is a trace** of the component read as a server. -/
theorem serve_mem {h : Body proxyImports proxyWorld.exports} {q : Request} {x : Response}
    (hx : serveRef h q = some x) : [(q, x)] ∈ wasiServer (ofBody h) := by
  refine mem_model_single (q := handleQ) (leads_runP (refHost q) [] (h handleQ))
    (fun _ _ => trivial) ?_ ⟨rfl, reqOk_runP q _ [] _, hx⟩
  have hx' : respOf (outOf handleQ.2) (runP (refHost q) [] (h handleQ)).1 = some x := hx
  simp only [answered]
  rw [hx']
  simp [handleQ]

/-- **Routing is not vacuous**: every request answered from the route table is a trace. -/
theorem route_answers (q : Request) :
    [(q, routeResp q.target.pathWithQuery)] ∈ wasiServer (ofBody route) := by
  refine serve_mem ?_
  have hrun : (runP (refHost q) [] (route handleQ)).1 =
      .req reqPath [.u32 0] :: .imp reqPath [.u32 0] (some [pathV q.target.pathWithQuery]) ::
        (runP (refHost q) [.imp reqPath [.u32 0] (some [pathV q.target.pathWithQuery])]
          (answer 1 (routeResp (pathOf (some [pathV q.target.pathWithQuery]))))).1 := by
    simp [runP, route, handleQ, refHost, pop, reqOf, outOf, reqMethod, reqPath]
  unfold serveRef
  rw [hrun, respOf_path]
  rw [pathOf_pathV]
  exact answer_ok (routeResp_ok _).1 (routeResp_ok _).2 (leads_runP _ _ _)
    fun f a n hm => (imp_runP hm).elim fun _ e => e ▸ refHost_ok q _ f a

end Silmaril.Proofs.Servers.WasiExamples
