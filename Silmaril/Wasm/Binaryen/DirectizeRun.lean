module

public import Silmaril.Wasm.Binaryen.DirectizeSim
public import Silmaril.Wasm.Binaryen.TableFrozen
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed

@[expose] public section

/-! # Directize: runs, sessions and observations

Closed-host runs of the module with `call_indirect` and of the module with `call`
correspond (`runs_corr`), given the invariant `FInv` on the left configuration: the slot
facts `DInv` and, for every table a site reads, `TableFrozen.Frozen` (no code that can run
writes the table). The invariant holds along every typed closed-host run (`finv_steps`):
a frozen table is unchanged by every step (`TableFrozen.Step.frozen`), and the cast fact
survives store extension. With the one-step simulation (`Binaryen/DirectizeSim.lean`) left
runs are simulated; determinism of the right side and the stuck-call transport give the
converse (as for global reads, `Binaryen/GlobReadRun.lean`).

Instantiation differs from the global-read proof: the invariant does not hold at the
instantiation configuration, whose code still initialises the tables. The observations of
a configuration are those of any configuration it runs to (`obs_mid`, by determinism), so
the correspondence of instantiations (`InstCorr`) starts after the element segments, or
records that both instantiations trap.
-/

namespace Silmaril.Wasm.Binaryen.DirSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst}

/-! ## The invariant along typed runs -/

variable (ok mi) in
/-- The run invariant: the slot facts, and every table a site reads is frozen. -/
def FInv (c : Config H) : Prop :=
  DInv ok mi c.store ∧ ∀ t k y fx, ok t k y fx → ∀ ta, mi.tables[t.toNat]? = some ta →
    TableFrozen.Frozen ta c

/-- Typed closed-host runs keep the invariant. -/
theorem finv_steps {P : Numerics.Profile} {c x : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hinv : FInv ok mi c) (h : Steps P closedHost c x) : FInv ok mi x := by
  have key : ConfigOk x ts ∧ FInv ok mi x := by
    induction h with
    | refl => exact ⟨hc, hinv⟩
    | @tail y z _ hs ih =>
      obtain ⟨hy, hdy, hfy⟩ := ih
      obtain ⟨hz, he⟩ := Step.preservation divHost_ok hy (Step.of_noHost divHost hs)
      have hfz : ∀ t k yy fx, ok t k yy fx → ∀ ta, mi.tables[t.toNat]? = some ta →
          TableFrozen.Frozen ta z ∧ z.store.tables[ta]? = y.store.tables[ta]? :=
        fun t k yy fx hok ta hta =>
          TableFrozen.Step.frozen (TableFrozen.closedHost_keeps ta) hs (hfy t k yy fx hok ta hta)
      exact ⟨hz, hdy.extend he (fun t k yy fx hok ta hta => (hfz t k yy fx hok ta hta).2),
        fun t k yy fx hok ta hta => (hfz t k yy fx hok ta hta).1⟩
  exact key.2

/-! ## Stuck host calls -/

theorem callout_transport {args : List Val} {a : Nat} {yy : Admin} (hyy : yy.IsCallRef) :
    ∀ (E : Ctx) {cur : ModuleInst} {ns : List Admin},
      GL ok mi cur (E.fill (vals args ++ [.ref (.func a), yy])) ns →
      ∃ (E' : Ctx) (yy' : Admin), ns = E'.fill (vals args ++ [.ref (.func a), yy']) ∧ yy'.IsCallRef
  | .top pre rest, cur, ns, h => by
    have e : (Ctx.top pre rest).fill (vals args ++ [.ref (.func a), yy]) =
        vals (pre ++ args ++ [.ref (.func a)]) ++ yy :: rest := by
      simp [Ctx.fill, vals, Val.toAdmin]
    rw [e] at h
    obtain ⟨hL, hH, hF, hv, hT, hR⟩ := callRef_flat hyy
    obtain ⟨e', rest', rfl, he, -⟩ := GL.split_pw hv hT hR
      (fun r t z h => by subst h; cases r <;> exact hyy) (fun t h => by subst h; exact hyy)
      (fun z h => by subst h; exact hyy) h
    refine ⟨.top pre rest', e', by simp [Ctx.fill, vals, Val.toAdmin], ?_⟩
    cases he with
    | plain hi =>
      obtain ⟨z, rfl⟩ := isCallRef_plain hyy
      rw [GI.eq_of_flat hi rfl]; trivial
    | ann _ hb => exact hb
    | retAnn ha => exfalso; unfold Admin.IsReturnCallRef at ha; split at ha
                   · obtain ⟨z, h⟩ := isCallRef_plain hyy; cases h
                   · exact hyy
                   · exact ha
    | ref => exact hyy.elim
    | label => exact hyy.elim
    | handler => exact hyy.elim
    | frame => exact hyy.elim
    | trap => exact hyy.elim
  | .label pre n cont E rest, cur, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨e', rest', rfl, he, -⟩ := GL.split_pw (by simp [Admin.val?]) (by simp) (by simp)
      (fun r _ _ h => by cases r <;> cases h) (fun _ h => by cases h) (fun _ h => by cases h) h
    cases he with
    | @label _ _ _ c' _ _ hc hb =>
      obtain ⟨E', yy', rfl, hyy'⟩ := callout_transport hyy E hb
      exact ⟨.label pre n c' E' rest', yy', by simp [Ctx.fill], hyy'⟩
    | ann ha => exact ha.elim
    | retAnn ha => exact ha.elim
  | .handler pre n cs E rest, cur, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨e', rest', rfl, he, -⟩ := GL.split_pw (by simp [Admin.val?]) (by simp) (by simp)
      (fun r _ _ h => by cases r <;> cases h) (fun _ h => by cases h) (fun _ h => by cases h) h
    cases he with
    | handler hb =>
      obtain ⟨E', yy', rfl, hyy'⟩ := callout_transport hyy E hb
      exact ⟨.handler pre n cs E' rest', yy', by simp [Ctx.fill], hyy'⟩
    | ann ha => exact ha.elim
    | retAnn ha => exact ha.elim
  | .frame pre n F E rest, cur, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨e', rest', rfl, he, -⟩ := GL.split_pw (by simp [Admin.val?]) (by simp) (by simp)
      (fun r _ _ h => by cases r <;> cases h) (fun _ h => by cases h) (fun _ h => by cases h) h
    cases he with
    | frame hb =>
      obtain ⟨E', yy', rfl, hyy'⟩ := callout_transport hyy E hb
      exact ⟨.frame pre n F E' rest', yy', by simp [Ctx.fill], hyy'⟩
    | ann ha => exact ha.elim
    | retAnn ha => exact ha.elim

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-! ## Runs -/


variable {P : Numerics.Profile}

/-- **Terminating left runs are simulated**, along invariant stores. -/
theorem run_sim {c c' : Config H} (h : Steps P closedHost c c')
    (hinv : ∀ x, Steps P closedHost c x → DInv ok mi x.store) {d : Config H}
    (hMR : MR ok mi c d) (hSR : SR ok mi c.store d.store) :
    ∃ d', Steps P closedHost d d' ∧ MR ok mi c' d' ∧ SR ok mi c'.store d'.store := by
  induction h with
  | refl => exact ⟨d, .refl, hMR, hSR⟩
  | @tail x x' hx hstep ih =>
    obtain ⟨dx, hd, hMRx, hSRx⟩ := ih
    obtain ⟨n', hMR', hSR', hprog⟩ :=
      sim (sizeOf x.code + 1) x x' dx (by omega) hstep hMRx hSRx (hinv x hx)
    rcases hprog with hp | ⟨hn', -⟩
    · exact ⟨n', hd.trans (steps_of_tg hp closedHost), hMR', hSR'⟩
    · rw [hn'] at hMR' hSR'
      exact ⟨dx, hd, hMR', hSR'⟩

/-- Terminal left configurations: the right configuration has the same code. -/
theorem terminal_code {c d : Config H} (hMR : MR ok mi c d) {r : Result}
    (hr : c.code = r.toAdmin) : d.code = r.toAdmin := by
  have h := hMR.2
  rw [hr] at h
  exact GL.result_inv h

/-- One step of the right side for a diverging left side. -/
theorem div_step {c₀ : Config H}
    (hinv : ∀ x, Steps P closedHost c₀ x → DInv ok mi x.store) :
    ∀ (w : Nat) (x z : Config H), aszs x.code = w → Steps P closedHost c₀ x →
      Diverges P closedHost x → MR ok mi x z → SR ok mi x.store z.store →
      ∃ z₁ x' z', Step P closedHost z z₁ ∧ Steps P closedHost c₀ x' ∧
        Diverges P closedHost x' ∧ MR ok mi x' z' ∧ SR ok mi x'.store z'.store ∧
        Steps P closedHost z₁ z' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro x z hw hx hdiv hMR hSR
  obtain ⟨x₁, hst, hdiv₁⟩ := InfiniteTrace.unfold hdiv
  have hx₁ : Steps P closedHost c₀ x₁ := hx.tail hst
  obtain ⟨n', hMR', hSR', hprog⟩ :=
    sim (sizeOf x.code + 1) x x₁ z (by omega) hst hMR hSR (hinv x hx)
  rcases hprog with hp | ⟨hn', hw'⟩
  · obtain ⟨z₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hp
    exact ⟨z₁, x₁, n', Step.of_noHost closedHost h₁, hx₁, hdiv₁, hMR', hSR',
      h₂.lift id (fun _ _ h => Step.of_noHost closedHost h)⟩
  · rw [hn'] at hMR' hSR'
    exact ih (aszs x₁.code) (by omega) x₁ z rfl hx₁ hdiv₁ hMR' hSR'

/-- **Diverging left runs are simulated.** -/
theorem div_sim {c : Config H} (hdiv : Diverges P closedHost c)
    (hinv : ∀ x, Steps P closedHost c x → DInv ok mi x.store)
    {d : Config H} (hMR : MR ok mi c d) (hSR : SR ok mi c.store d.store) : Diverges P closedHost d := by
  refine InfiniteTrace.coinduct
    (fun y => ∃ x z, Steps P closedHost c x ∧ Diverges P closedHost x ∧ MR ok mi x z ∧
      SR ok mi x.store z.store ∧ Steps P closedHost y z) ?_ ⟨c, d, .refl, hdiv, hMR, hSR, .refl⟩
  rintro y ⟨x, z, hx, hdx, hMRx, hSRx, hyz⟩
  rcases Relation.ReflTransGen.cases_head hyz with rfl | ⟨y₁, h₁, h₂⟩
  · obtain ⟨z₁, x', z', hs, hx', hdx', hMR', hSR', hz⟩ :=
      div_step hinv (aszs x.code) x y rfl hx hdx hMRx hSRx
    exact ⟨z₁, hs, x', z', hx', hdx', hMR', hSR', hz⟩
  · exact ⟨y₁, h₁, x, z, hx, hdx, hMRx, hSRx, h₂⟩


/-- A call redex of the left side is one of the right side. -/
theorem redex_transport {c d : Config H} (hMR : MR ok mi c d)
    (hSR : SR ok mi c.store d.store) {E : Ctx} {a : Nat} {hh : H} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args)) :
    ∃ F, decompose? d.store d.code = some (F, a, hh, args) := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, hshape⟩ := decompose?_sound hd
  obtain ⟨gi, hgi, ht, -, hc⟩ := hSR.get hfi
  have hgc : gi.code = .host hh := by
    cases hg : gi.code with
    | wasm g => rw [hcode, hg] at hc; exact hc.elim
    | host h' => rw [hcode, hg] at hc; rw [hc]
  obtain ⟨E', yy', hE', hyy'⟩ := callout_transport hyy E (hshape ▸ hMR.2)
  rw [hE']
  exact Unwrap.redex_fill_closed (decompose?_redex hyy' hgi (ht ▸ he) hlen hgc) E'

/-- A typed nonterminal closed-host normal form is stuck on a host call, which is also
stuck in the related configuration. -/
theorem stuck_transport {c d : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hnt : ¬ c.Terminal)
    (hnf : ∀ y, ¬ Step PD closedHost c y) (hMR : MR ok mi c d)
    (hSR : SR ok mi c.store d.store) :
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
theorem run_trichotomy {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hinv : FInv ok mi c) (hMR : MR ok mi c c')
    (hSR : SR ok mi c.store c'.store) :
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
    run_sim hx (fun y hy => (finv_steps hc hinv hy).1) hMR hSR
  obtain ⟨hnt', hnf'⟩ := stuck_transport (Unwrap.preserves_closed hc hx) ht hnf hMR' hSR'
  exact .inr (.inl ⟨x, x', hx, hx', hnt', hnf'⟩)

/-- **Terminating results and divergence correspond** under the closed host. -/
theorem runs_corr {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hinv : FInv ok mi c) (hMR : MR ok mi c c')
    (hSR : SR ok mi c.store c'.store) :
    (∀ x, Steps PD closedHost c x → x.Terminal →
      ∃ x', Steps PD closedHost c' x' ∧ x'.code = x.code ∧ SR ok mi x.store x'.store) ∧
    (Diverges PD closedHost c → Diverges PD closedHost c') ∧
    (∀ x', Steps PD closedHost c' x' → x'.Terminal →
      ∃ x, Steps PD closedHost c x ∧ x.code = x'.code ∧ SR ok mi x.store x'.store) ∧
    (Diverges PD closedHost c' → Diverges PD closedHost c) := by
  have hinvs : ∀ x, Steps PD closedHost c x → DInv ok mi x.store :=
    fun x hx => (finv_steps hc hinv hx).1
  have hclN : ∀ x, Steps PD closedHost c' x → Classif PD closedHost x :=
    fun x _ => Unwrap.classif_closed x
  have R1 : ∀ x, Steps PD closedHost c x → x.Terminal →
      ∃ x', Steps PD closedHost c' x' ∧ x'.code = x.code ∧ SR ok mi x.store x'.store := by
    intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hx hinvs hMR hSR
    exact ⟨x', hx', by rw [terminal_code hMR' hr, hr], hSR'⟩
  have R2 : Diverges PD closedHost c → Diverges PD closedHost c' := fun hd =>
    div_sim hd hinvs hMR hSR
  refine ⟨R1, R2, ?_, ?_⟩
  · intro x' hx' hxT'
    rcases run_trichotomy hc hinv hMR hSR with hterm | hstuck | hdiv
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
    rcases run_trichotomy hc hinv hMR hSR with hterm | hstuck | hdiv
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, -⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      exact (term_not_div hx'' hxT'' hclN hd').elim
    · obtain ⟨x, y, _, hy, _, hnf⟩ := hstuck
      exact (Unwrap.nf_not_div_closed hy hnf hd').elim
    · exact hdiv


end det

/-! ## Invocations and sessions -/

theorem funcType_eq {s t : Store H} (hSR : SR ok mi s t) (a : Nat) :
    (t.funcs[a]?.map FuncInst.type) = (s.funcs[a]?.map FuncInst.type) := by
  have := congrArg (fun l => l[a]?) hSR.sameTypes
  simpa only [List.getElem?_map] using this

theorem invoke_rel {s t : Store H} (hSR : SR ok mi s t) (a : Nat) (vs : List Val) :
    MR ok mi (invoke s a vs) (invoke t a vs) := by
  refine ⟨rfl, ?_⟩
  simp only [invoke]
  rw [funcType_eq hSR a]
  exact GL.refl _

theorem invokeOk_of {s t : Store H} (hSR : SR ok mi s t) {a : Nat} {vs : List Val}
    (h : InvokeOk s a vs) : InvokeOk t a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  obtain ⟨fi', hfi', ht⟩ := hSR.sameTypes.get hfi
  refine ⟨fi', ps, rs, hfi', ht ▸ he, ?_⟩
  rw [hSR.eq]
  exact hvs.imp fun _ _ h => valOk_withFuncs hSR.sameTypes h

theorem invokeOk_of' {s t : Store H} (hSR : SR ok mi s t) {a : Nat} {vs : List Val}
    (h : InvokeOk t a vs) : InvokeOk s a vs := by
  obtain ⟨G, hG, rfl⟩ := hSR.cases
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  have hX : SameTypes s.funcs G := (sameTypes_of hG).symm
  obtain ⟨fi', hfi', ht⟩ := hX.get hfi
  refine ⟨fi', ps, rs, hfi', ht ▸ he, ?_⟩
  have e : s = withFuncs (withFuncs s G) s.funcs := rfl
  rw [e]
  exact hvs.imp fun _ _ h => valOk_withFuncs (s := withFuncs s G) hX h

variable (ok mi) in
/-- The store invariant of sessions: the slot facts, and no function of the store writes a
table a site reads. -/
def SInv (s : Store H) : Prop :=
  DInv ok mi s ∧ ∀ t k y fx, ok t k y fx → ∀ ta, mi.tables[t.toNat]? = some ta →
    TableFrozen.StoreK ta s

theorem finv_invoke {s : Store H} (h : SInv ok mi s) (a : Nat) (vs : List Val) :
    FInv ok mi (invoke s a vs) := by
  refine ⟨h.1, fun t k y fx hok ta hta => ⟨h.2 t k y fx hok ta hta, ?_⟩⟩
  simp only [invoke, TableFrozen.AdmsK_append, TableFrozen.AdmsK_cons, TableFrozen.AdmsK_nil]
  exact ⟨TableFrozen.AdmsK_result ta _ (.values vs), trivial, trivial, trivial⟩

theorem sinv_of {c : Config H} (h : FInv ok mi c) : SInv ok mi c.store :=
  ⟨h.1, fun t k y fx hok ta hta => (h.2 t k y fx hok ta hta).store⟩

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- **Sessions of the right module are sessions of the left one.** -/
theorem session_corr₁ {mj : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD closedHost mj t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreOk t → SInv ok mi s → SR ok mi s t →
      Session PD closedHost mj s script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of hSR hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, R3, -⟩ := runs_corr hcO (finv_invoke hinv _ _) (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO hx'))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN run)) (sinv_of (finv_steps hcO (finv_invoke hinv _ _) hx')) hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr hcO (finv_invoke hinv _ _) (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the left module are sessions of the right one.** -/
theorem session_corr₂ {mj : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD closedHost mj s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → SInv ok mi s → SR ok mi s t →
      Session PD closedHost mj t script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨R1, -, -, -⟩ := runs_corr hcO (finv_invoke hinv _ _) (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO run))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN hx')) (sinv_of (finv_steps hcO (finv_invoke hinv _ _) run)) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr hcO (finv_invoke hinv _ _) (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)


end det

/-! ## Module observations -/

section obs

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

variable (o) in
/-- The observations of a configuration that runs instantiation code, then a session. -/
def Obs (c : Config H) (script : List Call) (bs : List (Behaviour Val)) : Prop :=
  (∃ c₁ bs', Steps PD closedHost c c₁ ∧ c₁.code = [] ∧
      Session PD closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
    (∃ (c₁ : Config H) (r : Result), Steps PD closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
      r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
    (Diverges PD closedHost c ∧ bs = [.diverges])

theorem nsteps_rtg {α : Type _} {R : α → α → Prop} : ∀ {k : Nat} {x y : α}, NSteps R k x y →
    Relation.ReflTransGen R x y
  | _, _, _, .refl _ => .refl
  | _, _, _, .head h t => Relation.ReflTransGen.head h (nsteps_rtg t)

/-- A run to a normal form passes through every configuration the start runs to. -/
theorem steps_to_nf {c cm x : Config H} (hm : Steps PD closedHost c cm)
    (hx : Steps PD closedHost c x) (hnf : ∀ z, ¬ Step PD closedHost x z) :
    Steps PD closedHost cm x := by
  have hj : ∀ {a b d : Config H}, Det.DStep o a b → Det.DStep o a d → Det.Join (Det.DStep o) b d :=
    fun ha hb => Det.DStep.join' ha hb
  have hcl : ∀ y, Steps PD closedHost c y → Classif PD closedHost y :=
    fun y _ => Unwrap.classif_closed y
  have hnf' : ∀ z, ¬ Det.DStep o x z := fun z h => hnf z (Step.of_noHost closedHost h)
  obtain ⟨k, hk⟩ := NSteps.of_rtg (steps_noHost_of_classif hx hcl)
  have key : ∀ {y : Config H}, Relation.ReflTransGen (Det.DStep o) c y →
      ∃ m, NSteps (Det.DStep o) m y x := by
    intro y hy
    induction hy with
    | refl => exact ⟨k, hk⟩
    | tail _ hs ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨m', -, hm'⟩ := NSteps.of_step_join hj hnf' hm hs
      exact ⟨m', hm'⟩
  obtain ⟨m, hm'⟩ := key (steps_noHost_of_classif hm hcl)
  exact (nsteps_rtg hm').lift id (fun _ _ h => Step.of_noHost closedHost h)

/-- Divergence is kept along a run. -/
theorem div_mid {c cm : Config H} (hm : Steps PD closedHost c cm) (hd : Diverges PD closedHost c) :
    Diverges PD closedHost cm := by
  classical
  by_contra hnd
  have : ∃ y, Steps PD closedHost cm y ∧ ∀ z, ¬ Step PD closedHost y z := by
    by_contra hne
    simp only [not_exists, not_and, not_forall, not_not] at hne
    exact hnd (InfiniteTrace.coinduct (fun x => Steps PD closedHost cm x)
      (fun x hx => let ⟨y, hy⟩ := hne x hx; ⟨y, hy, hx.tail hy⟩) .refl)
  obtain ⟨y, hy, hnf⟩ := this
  exact Unwrap.nf_not_div_closed (hm.trans hy) hnf hd

theorem div_back {c cm : Config H} (hm : Steps PD closedHost c cm)
    (hd : Diverges PD closedHost cm) : Diverges PD closedHost c := by
  induction hm with
  | refl => exact hd
  | tail _ hs ih => exact ih (InfiniteTrace.fold hs hd)

/-- **Observations are those of any configuration the run passes through.** -/
theorem obs_mid {c cm : Config H} (hm : Steps PD closedHost c cm)
    (hfm : cm.frame.module = c.frame.module) (script : List Call) (bs : List (Behaviour Val)) :
    Obs o c script bs ↔ Obs o cm script bs := by
  constructor
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · refine .inl ⟨c₁, bs', steps_to_nf hm h₁ (terminal_no_step ⟨.values [], h₂⟩), h₂, ?_, rfl⟩
      rw [hfm]; exact h₃
    · exact .inr (.inl ⟨c₁, r, steps_to_nf hm h₁ (terminal_no_step ⟨r, h₂⟩), h₂, h₃, rfl⟩)
    · exact .inr (.inr ⟨div_mid hm h₁, rfl⟩)
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · refine .inl ⟨c₁, bs', hm.trans h₁, h₂, ?_, rfl⟩
      rw [← hfm]; exact h₃
    · exact .inr (.inl ⟨c₁, r, hm.trans h₁, h₂, h₃, rfl⟩)
    · exact .inr (.inr ⟨div_back hm h₁, rfl⟩)

/-- A run that traps observes the trap only. -/
theorem obs_trap {c x : Config H} (hx : Steps PD closedHost c x) (hxc : x.code = [.trap])
    (script : List Call) (bs : List (Behaviour Val)) :
    Obs o c script bs ↔ bs = [Result.trap.toBehaviour] := by
  have hxT : x.Terminal := ⟨.trap, hxc⟩
  have hcl : ∀ z, Steps PD closedHost c z → Classif PD closedHost z :=
    fun z _ => Unwrap.classif_closed z
  constructor
  · rintro (⟨c₁, bs', h₁, h₂, -, rfl⟩ | ⟨c₁, r, h₁, h₂, -, rfl⟩ | ⟨h₁, rfl⟩)
    · have := nf_unique_classif hx h₁ hxT ⟨.values [], h₂⟩ hcl
      subst this
      rw [hxc] at h₂
      cases h₂
    · have := nf_unique_classif hx h₁ hxT ⟨r, h₂⟩ hcl
      subst this
      rw [hxc] at h₂
      cases r with
      | values vs =>
        cases vs with
        | nil => cases h₂
        | cons v vs =>
          simp only [Result.toAdmin, vals, List.map_cons, List.cons.injEq] at h₂
          have := congrArg Admin.val? h₂.1.symm
          rw [Admin.val?_toAdmin] at this
          simp [Admin.val?] at this
      | trap => rfl
      | throw a => simp [Result.toAdmin] at h₂
    · exact (term_not_div hx hxT hcl h₁).elim
  · rintro rfl
    exact .inr (.inl ⟨x, .trap, hx, hxc, by simp, rfl⟩)

/-- Corresponding configurations observe the same. -/
theorem obs_core {cm cm' : Config H} {ts ts' : List CValType} (hc : ConfigOk cm ts)
    (hc' : ConfigOk cm' ts') (hMR : MR ok mi cm cm') (hSR : SR ok mi cm.store cm'.store)
    (hinv : FInv ok mi cm) (script : List Call) (bs : List (Behaviour Val)) :
    Obs o cm script bs ↔ Obs o cm' script bs := by
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr hc hinv hMR hSR
  have hfr := hMR.1
  constructor
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₂ h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc h₁))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' hx))
        (sinv_of (finv_steps hc hinv h₁)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₁ h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc hx))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' h₁))
        (sinv_of (finv_steps hc hinv hx)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)

variable (o ok mi) in
/-- How two instantiation configurations correspond: both run to related configurations
with the invariant (after the element segments), or both trap. -/
def Pre (c c' : Config H) : Prop :=
  (∃ cm cm', Steps PD closedHost c cm ∧ Steps PD closedHost c' cm' ∧ MR ok mi cm cm' ∧
    SR ok mi cm.store cm'.store ∧ FInv ok mi cm) ∨
  (∃ x x', Steps PD closedHost c x ∧ Steps PD closedHost c' x' ∧ x.code = [.trap] ∧
    x'.code = [.trap])

theorem obs_pre {c c' : Config H} {ts ts' : List CValType} (hc : ConfigOk c ts)
    (hc' : ConfigOk c' ts') (h : Pre ok mi o c c') (script : List Call) (bs : List (Behaviour Val)) :
    Obs o c script bs ↔ Obs o c' script bs := by
  rcases h with ⟨cm, cm', hm, hm', hMR, hSR, hinv⟩ | ⟨x, x', hx, hx', hxc, hxc'⟩
  · rw [obs_mid hm (GlobRead.steps_frame_module hm) script bs,
      obs_mid hm' (GlobRead.steps_frame_module hm') script bs]
    exact obs_core (Unwrap.preserves_closed hc hm) (Unwrap.preserves_closed hc' hm') hMR hSR hinv
      script bs
  · rw [obs_trap hx hxc, obs_trap hx' hxc']

variable (o) in
/-- A correspondence between the instantiations of the left module `M` and the right module
`M'`. -/
def InstCorr (M M' : Module) : Prop :=
  (∀ (s : Store H) xas c, StoreOk s → Instantiate PD closedHost s M xas c →
    ∃ c' ok mi, Instantiate PD closedHost s M' xas c' ∧ Pre ok mi o c c') ∧
  (∀ (s : Store H) xas c', StoreOk s → Instantiate PD closedHost s M' xas c' →
    ∃ c ok mi, Instantiate PD closedHost s M xas c ∧ Pre ok mi o c c')

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr {M M' : Module} (h : InstCorr (H := H) o M M') :
    ExportEquiv (· = ·) PD (closedHost (H := H)) M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', -, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, ok, mi, hi, hpre⟩ := h₂ s xas c' hs hi'
    have hc := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi)
    have hc' := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi')
    exact ⟨bs, ⟨c, hi, (obs_pre hc hc' hpre script bs).2 hrun⟩, SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, -, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', ok, mi, hi', hpre⟩ := h₁ s xas c hs hi
    have hc := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi)
    have hc' := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi')
    exact ⟨bs, ⟨c', hi', (obs_pre hc hc' hpre script bs).1 hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

end obs

end Silmaril.Wasm.Binaryen.DirSim
