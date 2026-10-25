module

public import Silmaril.Wasm.Binaryen.GlobReadSim
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed

@[expose] public section

/-! # Reading an immutable global: runs, sessions and observations

Closed-host runs of the module with `global.get x` and of the module with the literal
correspond (`runs_corr`), given the invariant `GInv` on the left store. The invariant
holds along every typed closed-host run (`ginv_steps`): an immutable global instance is
kept by store extension (`GInv.extend`), and typed runs extend the store
(`Step.preservation` for the always-diverging host, as in `Binaryen/InlUnwrapClosed.lean`).
With the one-step simulation (`Binaryen/GlobReadSim.lean`) left runs are simulated;
determinism of the right side and the stuck-call transport give the converse. Sessions and
module observations follow as for block unwrapping, with the invariant established at
instantiation (`InstCorr`).
-/

namespace Silmaril.Wasm.Binaryen.GlobRead

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm}

/-! ## The invariant along typed runs -/

/-- Typed closed-host runs keep the invariant. -/
theorem ginv_steps {P : Numerics.Profile} {lk : GlobalIdx → Option Instr} {mi : ModuleInst}
    {c x : Config H} {ts : List CValType} (hc : ConfigOk c ts) (hinv : GInv lk mi c.store)
    (h : Steps P closedHost c x) : GInv lk mi x.store := by
  have key : ConfigOk x ts ∧ GInv lk mi x.store := by
    induction h with
    | refl => exact ⟨hc, hinv⟩
    | tail _ hs ih =>
      obtain ⟨hy, hiy⟩ := ih
      obtain ⟨hz, he⟩ := Step.preservation divHost_ok hy (Step.of_noHost divHost hs)
      exact ⟨hz, hiy.extend he⟩
  exact key.2

/-! ## Stuck host calls -/

theorem callout_transport {args : List Val} {a : Nat} {yy : Admin} (hyy : yy.IsCallRef) :
    ∀ (E : Ctx) {cur : ModuleInst} {ns : List Admin},
      GL p.lk p.mi cur (E.fill (vals args ++ [.ref (.func a), yy])) ns →
      ∃ E' : Ctx, ns = E'.fill (vals args ++ [.ref (.func a), yy])
  | .top pre rest, cur, ns, h => by
    obtain ⟨hL, hH, hF, -, -, -⟩ := callRef_flat hyy
    have e : (Ctx.top pre rest).fill (vals args ++ [.ref (.func a), yy]) =
        vals (pre ++ args ++ [.ref (.func a)]) ++ yy :: rest := by
      simp [Ctx.fill, vals, Val.toAdmin]
    rw [e] at h
    obtain ⟨rest', rfl, -⟩ := GL.flat_inv hL hH hF (fun i hi => by
      subst hi
      refine ⟨?_, fun x hx => ?_⟩
      · cases i <;> simp_all [Admin.IsCallRef, structuredInstr]
      · subst hx; simp [Admin.IsCallRef] at hyy) h
    exact ⟨.top pre rest', by simp [Ctx.fill, vals, Val.toAdmin]⟩
  | .label pre n cont E rest, cur, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨nB, rfl, hB⟩ := GL.vals_append_inv h
    cases hB with
    | @cons _ _ _ _ ns' hl hr =>
      cases hl with
      | @label _ _ _ c' _ _ hc hb =>
        obtain ⟨E', rfl⟩ := callout_transport hyy E hb
        exact ⟨.label pre n c' E' ns', by simp [Ctx.fill]⟩
  | .handler pre n cs E rest, cur, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨nB, rfl, hB⟩ := GL.vals_append_inv h
    cases hB with
    | @cons _ _ _ _ ns' hl hr =>
      cases hl with
      | handler hb =>
        obtain ⟨E', rfl⟩ := callout_transport hyy E hb
        exact ⟨.handler pre n cs E' ns', by simp [Ctx.fill]⟩
  | .frame pre n F E rest, cur, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨nB, rfl, hB⟩ := GL.vals_append_inv h
    cases hB with
    | @cons _ _ _ _ ns' hl hr =>
      cases hl with
      | frame hb =>
        obtain ⟨E', rfl⟩ := callout_transport hyy E hb
        exact ⟨.frame pre n F E' ns', by simp [Ctx.fill]⟩

/-! ## Runs -/

section runs

variable {P : Numerics.Profile}

/-- **Terminating left runs are simulated**, along invariant stores. -/
theorem run_sim (hok : PrmOk p) {c c' : Config H} (h : Steps P closedHost c c')
    (hinv : ∀ x, Steps P closedHost c x → GInv p.lk p.mi x.store) {d : Config H}
    (hMR : MR p c d) (hSR : SR p c.store d.store) :
    ∃ d', Steps P closedHost d d' ∧ MR p c' d' ∧ SR p c'.store d'.store := by
  induction h with
  | refl => exact ⟨d, .refl, hMR, hSR⟩
  | @tail x x' hx hstep ih =>
    obtain ⟨dx, hd, hMRx, hSRx⟩ := ih
    obtain ⟨n', hMR', hSR', hprog⟩ :=
      sim hok (sizeOf x.code + 1) x x' dx (by omega) hstep hMRx hSRx (hinv x hx)
    rcases hprog with hp | ⟨hn', -⟩
    · exact ⟨n', hd.trans (steps_of_tg hp closedHost), hMR', hSR'⟩
    · rw [hn'] at hMR' hSR'
      exact ⟨dx, hd, hMR', hSR'⟩

/-- Terminal left configurations: the right configuration has the same code. -/
theorem terminal_code {c d : Config H} (hMR : MR p c d) {r : Result}
    (hr : c.code = r.toAdmin) : d.code = r.toAdmin := by
  have h := hMR.2
  rw [hr] at h
  exact GL.result_inv h

/-- One step of the right side for a diverging left side. -/
theorem div_step (hok : PrmOk p) {c₀ : Config H}
    (hinv : ∀ x, Steps P closedHost c₀ x → GInv p.lk p.mi x.store) :
    ∀ (w : Nat) (x z : Config H), aszs x.code = w → Steps P closedHost c₀ x →
      Diverges P closedHost x → MR p x z → SR p x.store z.store →
      ∃ z₁ x' z', Step P closedHost z z₁ ∧ Steps P closedHost c₀ x' ∧
        Diverges P closedHost x' ∧ MR p x' z' ∧ SR p x'.store z'.store ∧
        Steps P closedHost z₁ z' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro x z hw hx hdiv hMR hSR
  obtain ⟨x₁, hst, hdiv₁⟩ := InfiniteTrace.unfold hdiv
  have hx₁ : Steps P closedHost c₀ x₁ := hx.tail hst
  obtain ⟨n', hMR', hSR', hprog⟩ :=
    sim hok (sizeOf x.code + 1) x x₁ z (by omega) hst hMR hSR (hinv x hx)
  rcases hprog with hp | ⟨hn', hw'⟩
  · obtain ⟨z₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hp
    exact ⟨z₁, x₁, n', Step.of_noHost closedHost h₁, hx₁, hdiv₁, hMR', hSR',
      h₂.lift id (fun _ _ h => Step.of_noHost closedHost h)⟩
  · rw [hn'] at hMR' hSR'
    exact ih (aszs x₁.code) (by omega) x₁ z rfl hx₁ hdiv₁ hMR' hSR'

/-- **Diverging left runs are simulated.** -/
theorem div_sim (hok : PrmOk p) {c : Config H} (hdiv : Diverges P closedHost c)
    (hinv : ∀ x, Steps P closedHost c x → GInv p.lk p.mi x.store)
    {d : Config H} (hMR : MR p c d) (hSR : SR p c.store d.store) : Diverges P closedHost d := by
  refine InfiniteTrace.coinduct
    (fun y => ∃ x z, Steps P closedHost c x ∧ Diverges P closedHost x ∧ MR p x z ∧
      SR p x.store z.store ∧ Steps P closedHost y z) ?_ ⟨c, d, .refl, hdiv, hMR, hSR, .refl⟩
  rintro y ⟨x, z, hx, hdx, hMRx, hSRx, hyz⟩
  rcases Relation.ReflTransGen.cases_head hyz with rfl | ⟨y₁, h₁, h₂⟩
  · obtain ⟨z₁, x', z', hs, hx', hdx', hMR', hSR', hz⟩ :=
      div_step hok hinv (aszs x.code) x y rfl hx hdx hMRx hSRx
    exact ⟨z₁, hs, x', z', hx', hdx', hMR', hSR', hz⟩
  · exact ⟨y₁, h₁, x, z, hx, hdx, hMRx, hSRx, h₂⟩

end runs

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- A call redex of the left side is one of the right side. -/
theorem redex_transport {c d : Config H} (hMR : MR p c d)
    (hSR : SR p c.store d.store) {E : Ctx} {a : Nat} {hh : H} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args)) :
    ∃ F, decompose? d.store d.code = some (F, a, hh, args) := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, hshape⟩ := decompose?_sound hd
  have hag : a ≠ p.ag := by
    rintro rfl; rw [hSR.hg] at hfi; cases hfi; simp [gL] at hcode
  have hfi' : d.store.funcs[a]? = some fi := by
    rw [hSR.get a]; simp only [hag, ↓reduceIte]; exact hfi
  obtain ⟨E', hE'⟩ := callout_transport hyy E (hshape ▸ hMR.2)
  rw [hE']
  exact Unwrap.redex_fill_closed (decompose?_redex hyy hfi' he hlen hcode) E'

/-- A typed nonterminal closed-host normal form is stuck on a host call, which is also
stuck in the related configuration. -/
theorem stuck_transport {c d : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hnt : ¬ c.Terminal)
    (hnf : ∀ y, ¬ Step PD closedHost c y) (hMR : MR p c d)
    (hSR : SR p c.store d.store) :
    ¬ d.Terminal ∧ (∀ y, ¬ Step PD closedHost d y) := by
  obtain ht | ⟨c₁, hs⟩ := Config.progress (P := PD) divHost_ok hc
  · exact (hnt ht).elim
  rcases Step.split_host hs with hn | ⟨E, a, hh, args, hd, hret | hdiv⟩
  · exact (hnf _ hn).elim
  · obtain ⟨s', r, hret, _⟩ := hret
    cases hret
  · obtain ⟨F, hF⟩ := redex_transport hMR hSR hd
    refine ⟨?_, ?_⟩
    · intro ht
      rw [decompose?_terminal ht] at hF
      cases hF
    · intro y hs
      rw [decompose?_none_of_noRedex (Step.noRedex hs)] at hF
      cases hF

/-- Execution terminates, exposes a corresponding stuck call, or diverges. -/
theorem run_trichotomy (hok : PrmOk p) {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hinv : GInv p.lk p.mi c.store) (hMR : MR p c c')
    (hSR : SR p c.store c'.store) :
    (∃ x, Steps PD closedHost c x ∧ x.Terminal) ∨
    (∃ x x', Steps PD closedHost c x ∧ Steps PD closedHost c' x' ∧
      ¬ x'.Terminal ∧ (∀ y, ¬ Step PD closedHost x' y)) ∨
    Diverges PD closedHost c := by
  classical
  by_cases hd : Diverges PD closedHost c
  · exact .inr (.inr hd)
  have hnf : ∃ x, Steps PD closedHost c x ∧ ∀ y, ¬ Step PD closedHost x y := by
    by_contra hne
    simp only [not_exists, not_and, not_forall, not_not] at hne
    exact hd (InfiniteTrace.coinduct (fun x => Steps PD closedHost c x)
      (fun x hx => let ⟨y, hy⟩ := hne x hx; ⟨y, hy, hx.tail hy⟩) .refl)
  obtain ⟨x, hx, hnf⟩ := hnf
  by_cases ht : x.Terminal
  · exact .inl ⟨x, hx, ht⟩
  obtain ⟨x', hx', hMR', hSR'⟩ :=
    run_sim hok hx (fun y hy => ginv_steps hc hinv hy) hMR hSR
  obtain ⟨hnt', hnf'⟩ := stuck_transport (Unwrap.preserves_closed hc hx) ht hnf hMR' hSR'
  exact .inr (.inl ⟨x, x', hx, hx', hnt', hnf'⟩)

/-- **Terminating results and divergence correspond** under the closed host. -/
theorem runs_corr (hok : PrmOk p) {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hinv : GInv p.lk p.mi c.store) (hMR : MR p c c')
    (hSR : SR p c.store c'.store) :
    (∀ x, Steps PD closedHost c x → x.Terminal →
      ∃ x', Steps PD closedHost c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges PD closedHost c → Diverges PD closedHost c') ∧
    (∀ x', Steps PD closedHost c' x' → x'.Terminal →
      ∃ x, Steps PD closedHost c x ∧ x.code = x'.code ∧ SR p x.store x'.store) ∧
    (Diverges PD closedHost c' → Diverges PD closedHost c) := by
  have hinvs : ∀ x, Steps PD closedHost c x → GInv p.lk p.mi x.store :=
    fun x hx => ginv_steps hc hinv hx
  have hclN : ∀ x, Steps PD closedHost c' x → Classif PD closedHost x :=
    fun x _ => Unwrap.classif_closed x
  have R1 : ∀ x, Steps PD closedHost c x → x.Terminal →
      ∃ x', Steps PD closedHost c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store := by
    intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hok hx hinvs hMR hSR
    exact ⟨x', hx', by rw [terminal_code hMR' hr, hr], hSR'⟩
  have R2 : Diverges PD closedHost c → Diverges PD closedHost c' := fun hd =>
    div_sim hok hd hinvs hMR hSR
  refine ⟨R1, R2, ?_, ?_⟩
  · intro x' hx' hxT'
    rcases run_trichotomy hok hc hinv hMR hSR with hterm | hstuck | hdiv
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, hSR''⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      have := nf_unique_classif hx'' hx' hxT'' hxT' hclN
      subst this
      exact ⟨x, hx, hcode.symm, hSR''⟩
    · obtain ⟨x, y, _, hy, hnt, hnf⟩ := hstuck
      have he : y = x' := nf_unique_of_join (fun ha hb => Det.DStep.join' ha hb)
        hy hx' hnf (terminal_no_step hxT')
      exact (hnt (he.symm ▸ hxT')).elim
    · exact (term_not_div hx' hxT' hclN (R2 hdiv)).elim
  · intro hd'
    rcases run_trichotomy hok hc hinv hMR hSR with hterm | hstuck | hdiv
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, -⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      exact (term_not_div hx'' hxT'' hclN hd').elim
    · obtain ⟨x, y, _, hy, _, hnf⟩ := hstuck
      exact (Unwrap.nf_not_div_closed hy hnf hd').elim
    · exact hdiv

end det

/-! ## Invocations and sessions -/

theorem funcType_eq {s t : Store H} (hSR : SR p s t) (a : Nat) :
    (t.funcs[a]?.map FuncInst.type) = (s.funcs[a]?.map FuncInst.type) := by
  have := congrArg (fun l => l[a]?) hSR.sameTypes
  simp only [List.getElem?_map] at this
  rw [hSR.ht]
  exact this

theorem invoke_rel {s t : Store H} (hSR : SR p s t) (a : Nat) (vs : List Val) :
    MR p (invoke s a vs) (invoke t a vs) := by
  refine ⟨rfl, ?_⟩
  simp only [invoke]
  rw [funcType_eq hSR a]
  exact GL.refl _

theorem invokeOk_of {s t : Store H} (hSR : SR p s t) {a : Nat} {vs : List Val}
    (h : InvokeOk s a vs) : InvokeOk t a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  obtain ⟨fi', hfi', ht⟩ := hSR.sameTypes.get hfi
  refine ⟨fi', ps, rs, by rw [hSR.ht]; exact hfi', ht ▸ he, ?_⟩
  rw [hSR.ht]
  exact hvs.imp fun _ _ h => valOk_withFuncs hSR.sameTypes h

theorem invokeOk_of' {s t : Store H} (hSR : SR p s t) {a : Nat} {vs : List Val}
    (h : InvokeOk t a vs) : InvokeOk s a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  rw [hSR.ht] at hfi hvs
  obtain ⟨fi', hfi', ht⟩ := hSR.sameTypes.symm.get hfi
  refine ⟨fi', ps, rs, hfi', ht ▸ he, ?_⟩
  have e : s = withFuncs (withFuncs s (s.funcs.set p.ag (gR p))) s.funcs := rfl
  rw [e]
  exact hvs.imp fun _ _ h => valOk_withFuncs (s := withFuncs s (s.funcs.set p.ag (gR p)))
    hSR.sameTypes.symm h

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- **Sessions of the right module are sessions of the left one.** -/
theorem session_corr₁ (hok : PrmOk p) {mi : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD closedHost mi t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreOk t → GInv p.lk p.mi s → SR p s t →
      Session PD closedHost mi s script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of hSR hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, R3, -⟩ := runs_corr hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO hx'))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN run)) (ginv_steps hcO hinv hx') hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the left module are sessions of the right one.** -/
theorem session_corr₂ (hok : PrmOk p) {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD closedHost mi s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → GInv p.lk p.mi s → SR p s t →
      Session PD closedHost mi t script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨R1, -, -, -⟩ := runs_corr hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO run))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN hx')) (ginv_steps hcO hinv run) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)

/-! ## Module observations -/

/-- A correspondence between the instantiations of the left module `M` and the right module
`M'`, with the invariant on the left instantiation store. -/
def InstCorr (M M' : Module) : Prop :=
  (∀ (s : Store H) xas c, StoreOk s → Instantiate PD closedHost s M xas c →
    ∃ c' p, PrmOk p ∧ Instantiate PD closedHost s M' xas c' ∧ c'.frame = c.frame ∧
      c'.code = c.code ∧ SR p c.store c'.store ∧ GInv p.lk p.mi c.store) ∧
  (∀ (s : Store H) xas c', StoreOk s → Instantiate PD closedHost s M' xas c' →
    ∃ c p, PrmOk p ∧ Instantiate PD closedHost s M xas c ∧ c'.frame = c.frame ∧
      c'.code = c.code ∧ SR p c.store c'.store ∧ GInv p.lk p.mi c.store)

theorem obs_corr
    {M M' : Module} {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {c c' : Config H}
    (hi : Instantiate PD closedHost s M xas c) (hi' : Instantiate PD closedHost s M' xas c')
    (hok : PrmOk p) (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
    (hSR : SR p c.store c'.store) (hinv : GInv p.lk p.mi c.store) (script : List Call) :
    (∀ bs, ((∃ c₁ bs', Steps PD closedHost c' c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c' ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps PD closedHost c c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c ∧ bs = [.diverges]))) ∧
    (∀ bs, ((∃ c₁ bs', Steps PD closedHost c c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps PD closedHost c' c₁ ∧ c₁.code = [] ∧
        Session PD closedHost c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD closedHost c' ∧ bs = [.diverges]))) := by
  have hc := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi)
  have hc' := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi')
  have hMR : MR p c c' := ⟨hfr.symm, by rw [hcode]; exact GL.refl _⟩
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr hok hc hinv hMR hSR
  refine ⟨fun bs h => ?_, fun bs h => ?_⟩
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₁ hok h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc hx))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' h₁)) (ginv_steps hc hinv hx) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₂ hok h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc h₁))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' hx)) (ginv_steps hc hinv h₁) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr {M M' : Module} (h : InstCorr (H := H) (o := o) M M') :
    ExportEquiv (· = ·) PD (closedHost (H := H)) M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', p, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, p, hok, hi, hfr, hcode, hSR, hinv⟩ := h₂ s xas c' hs hi'
    exact ⟨bs, ⟨c, hi, (obs_corr hs hi hi' hok hfr hcode hSR hinv script).1 bs hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, p, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', p, hok, hi', hfr, hcode, hSR, hinv⟩ := h₁ s xas c hs hi
    exact ⟨bs, ⟨c', hi', (obs_corr hs hi hi' hok hfr hcode hSR hinv script).2 bs hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

end det

end Silmaril.Wasm.Binaryen.GlobRead
