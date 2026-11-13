module

public import Silmaril.Proofs.Wasm.Resource.CompToy.Make

/-!
# The toy resource component: resolved calls of `make`

* `make_from_core`: from the core activation of `make`, a run where the call is resolved went
  through the core phase (`core_inv` with `make_calloutsAns`, `makeSpec_valid`), returned
  `i32 j` for an index `j` not live at the start of the call, and lifted it with `liftOwn`
  (`runs_lift_make`; `traps_lift_make` when `j` is not live) to `own c`;
* **`toy_make`**: a resolved call of `make` from a configuration between calls was on `[]`,
  answered `own c` (`c` the counter), and ends at the next configuration between calls with
  counter `c + 1 < 2^32` and a handle table that is again `TabB`.

New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

variable {P : Silmaril.Wasm.Numerics.Profile} {prof : ProfileKind} {c : ℕ} {ι : InstState}
  {G : ToyGarb P} {k : ℕ}

/-- The instance during a call. -/
abbrev callI (ι : InstState) (G : ToyGarb P) : InstState := callIn ι ⟨G.threads.length⟩

theorem tStore₄_thread (ft : WIT.FuncType Empty RtId) (ι₄ : InstState) (H₄ : List ResourceHandle)
    (args : List Silmaril.Wasm.Component.Reference.Val) :
    ArenaField.threads.get? (tStore₄ P ft c ι (callI ι G) G k args ι₄ H₄) ⟨G.threads.length⟩ =
      some ((thread₁ G.tasks).withIndex 1) := by
  show (G.threads ++ [(thread₁ G.tasks).withIndex 1])[G.threads.length]? = _
  simp

theorem tStore₄_task (ft : WIT.FuncType Empty RtId) (ι₄ : InstState) (H₄ : List ResourceHandle)
    (args : List Silmaril.Wasm.Component.Reference.Val) :
    ArenaField.tasks.get? (tStore₄ P ft c ι (callI ι G) G k args ι₄ H₄)
      ((thread₁ G.tasks).withIndex 1).task =
      some ((tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started) := by
  show (G.tasks ++ [(tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started])[G.tasks.length]? = _
  simp

/-- The core configuration of a call as a frame of `make`'s core phase. -/
theorem coreCfg_mkB {M₀ : Machine.Config (E3 P) Unit} {ι' : InstState} {H : List ResourceHandle}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)} {x : CoreSt (E3 P)}
    (hi : M₀.store.insts = [ι']) (hH : M₀.store.resHandles = H) :
    coreCfg M₀ th K segs rest x = coreCfg (mkB M₀ ι' ι'.handles H x.1) th K segs rest x := by
  obtain ⟨⟨⟩⟩ := M₀
  dsimp only at hi hH
  subst hi hH
  rfl

/-- The lift of `make`'s result at the return point, for an own handle of representation `c`
at index `j`. -/
theorem make_liftAt {cs' : (core3P P).Store (CanonHost (core3P P))} {T T₅ : Silmaril.Wasm.Component.Runtime.Table HandleEntry}
    {Hs : List ResourceHandle} {j : ℕ} {hid : HandleObjId} (hj : j < 2 ^ 32)
    (hrm : T.remove? j = some (.resource hid, T₅))
    (hH : Hs[hid.idx]? = some { rt := ⟨0⟩, rep := c, own := true }) :
    ∀ m : Machine.Config (E3 P) Unit,
      m.store = { tStore₄ P ftMake c ι (callI ι G) G k [] { callI ι G with handles := T } Hs with
        core := cs' } →
      RunsQ (D P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatResults (.ofList [.int .i32 (BitVec.ofNat 32 j)]) (resultTypes ftMake)) m
        [.tau, .tau, .tau, .tau] ([.own c], ⟨[.int .i32 (BitVec.ofNat 32 j)], 1⟩)
        { m with store := { tStore₄ P ftMake c ι (callI ι G) G k [] { callI ι G with handles := T₅ }
            Hs with core := cs' } } := by
  intro m hm
  obtain ⟨⟩ := m
  dsimp only at hm
  subst hm
  exact runs_lift_make ⟨G.tasks.length⟩ hj rfl (by simp [InstState.removeHandle?, hrm]) hH

/-- **The core phase and return of a call of `make`**: the resolved outcome is `own c`, at the
next configuration between calls with counter `c + 1`. -/
theorem make_from_core {M₀ m' : Machine.Config (E3 P) Unit}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {tr : List (Label (E3 P) Unit)} {r : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (hc : c < 2 ^ 32) (hG : G.Ok) (hk : ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩) (hleave : ι.mayLeave = true)
    (hTB : TabB ι.handles)
    (hst : M₀.store = tStore₄ P ftMake c ι (callI ι G) G k [] (callI ι G) G.handles)
    (hK : ∀ ys, ∃ (β : Type) (f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P) Unit β)
        (g : β → Canon.P (E3 P) Unit (Ret (E3 P))), K ys = (liftFlatValues Limits.spec Quirks.none
          ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
          ABI.maxFlatResults (.ofList ys) (resultTypes ftMake) >>= f) >>= g)
    (hret : ∀ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιc ι₅ : InstState)
        (Hc H₅ : List ResourceHandle) (ys : List FlatValue) (ws : List Silmaril.Wasm.Component.Reference.Val) (cur : FlatCursor)
        (trF : List (Label (E3 P) Unit)) (c' : ℕ),
        (∀ m : Machine.Config (E3 P) Unit,
          m.store = { tStore₄ P ftMake c ι (callI ι G) G k [] ιc Hc with core := cs' } →
          RunsQ (D P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
            ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
            ABI.maxFlatResults (.ofList ys) (resultTypes ftMake)) m trF (ws, cur)
            { m with store := { tStore₄ P ftMake c ι (callI ι G) G k [] ι₅ H₅ with core := cs' } }) →
        cs' = setCtr P (toyInst P).store.core c' →
        ι₅.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι₅) →
        ∃ tr, LRun prof (refHost P).hr (D P)
          { M₀ with store := { tStore₄ P ftMake c ι (callI ι G) G k [] ιc Hc with core := cs' },
                    ctl := ⟨some ⟨G.threads.length⟩, .prog (K ys), segs⟩ :: rest } tr
          (toyCfgX P c' (InstState.removeThread 1 ι₅) (nextG P G ftMake k 0 2 [] ws H₅)))
    (r' : Steps prof (refHost P).hr (D P) (coreCfg M₀ (some ⟨G.threads.length⟩) K segs rest
      (toyCs P c, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 2 [])) tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : (CallOutcome.resolved r).Holds (refHost P).hr ⟨k⟩ m') :
    c + 1 < 2 ^ 32 ∧ ∃ T₅ Hs, TabB T₅ ∧ r = some [.own c] ∧
      m' = toyCfgX P (c + 1) (InstState.removeThread 1 { callI ι G with handles := T₅ })
        (nextG P G ftMake k 0 2 [] [.own c] Hs) := by
  have hl : M₀.store.lockdown = false := by rw [hst]; rfl
  have hv := makeSpec_valid (P := P) hc (Jmake (callI ι G).handles)
  have hco := make_calloutsAns (prof := prof) (M₀ := M₀) (ι' := callI ι G) (K := K) (segs := segs)
    (rest := rest) hc (by rw [hst]; exact tStore₄_thread ftMake _ _ [])
    (by rw [hst]; exact tStore₄_task ftMake _ _ []) rfl hl hleave
  have hInv : MkInv M₀ (callI ι G) c
      (mkB M₀ (callI ι G) (callI ι G).handles G.handles (toyCs P c)) :=
    ⟨_, _, _, rfl, hTB, newOwn_refl _ _ _⟩
  rw [coreCfg_mkB (ι' := callI ι G) (H := G.handles) (by rw [hst]; rfl) (by rw [hst]; rfl)] at r'
  obtain ⟨B', y, l, m₁, tr₂, ⟨T, Hs, cs, rfl, hTB', hn⟩, hreach, hnco, hx, r₃, hsuf⟩ :=
    core_inv (prof := prof) (Hc := Hnew P c (Jmake (callI ι G).handles))
      (Inv := MkInv M₀ (callI ι G) c)
      (c₀ := Silmaril.Wasm.Execution.Core.invoke (toyCs P c) 2 [])
      (fun B ⟨T, Hs, cs, hB, _⟩ => by rw [hB]; exact hl) hco
      (fun c' hs => (hv.invoke_safe ⟨rfl, rfl⟩ hs).imp id fun ⟨o, he, _⟩ => ⟨o, he⟩)
      tr.length _ _ tr m' le_rfl hInv .refl r' ho
  have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (hsuf.subset hm)
  rcases hx with ⟨ys, hys, -, hm₁⟩ | ⟨-, -, hm₁⟩ | ⟨h', args', hco'⟩
  rotate_left
  · subst hm₁
    exact absurd ho (fun hh => absurd (steps_of_locked rfl rfl r₃ ▸ hh).2.1
      (by simp [trapCfg, lockdownSt]))
  · exact (hnco h' args' hco').elim
  obtain ⟨vs, hcode, hmap⟩ := status_values hys
  have e : (y.2.config y.1).store = y.1 := Silmaril.Wasm.SingleThreaded.Thread.config_store y.1 y.2
  have hs' : Silmaril.Wasm.Execution.Core.Steps P (Hnew P c (Jmake (callI ι G).handles))
      (Silmaril.Wasm.Execution.Core.invoke (toyCs P c) 2 [])
      ⟨(y.2.config y.1).store, (y.2.config y.1).frame,
        Silmaril.Wasm.Execution.Core.vals vs⟩ := by
    rw [← hcode]
    exact hreach
  rcases hv.invoke_vals ⟨rfl, rfl⟩ hs' with he | ⟨hc1, hs1, j, ⟨hj32, hjfree⟩, hvs⟩
  · cases he
  obtain rfl := Silmaril.Wasm.Logic.Core.Outcome.normal.inj hvs
  have hys' : ys = [.int .i32 (BitVec.ofNat 32 j)] := Option.some.inj (hmap.symm.trans rfl)
  subst hys'
  rw [e] at hs1
  obtain ⟨β, f, g, hKe⟩ := hK [.int .i32 (BitVec.ofNat 32 j)]
  have hm₁' : m₁ = { M₀ with
      store := { tStore₄ P ftMake c ι (callI ι G) G k [] { callI ι G with handles := T } Hs with
        core := y.1 },
      ctl := ⟨some ⟨G.threads.length⟩, .prog (K [.int .i32 (BitVec.ofNat 32 j)]), segs⟩ :: rest } := by
    rw [hm₁]
    simp only [retCfg, mkB, hst]
    rfl
  cases hrm : T.remove? j with
  | none =>
    have hins : m₁.store.insts = [{ callI ι G with handles := T }] := by rw [hm₁']; rfl
    obtain ⟨trT, mT, hT⟩ := traps_lift_make (th := some ⟨G.threads.length⟩) ⟨G.tasks.length⟩ hj32
      hins (by simp [InstState.removeHandle?, hrm])
    have hctl : m₁.ctl = ⟨some ⟨G.threads.length⟩, .prog ((liftFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatResults (.ofList [.int .i32 (BitVec.ofNat 32 j)]) (resultTypes ftMake) >>= f) >>= g),
        segs⟩ :: rest := by
      rw [hm₁', ← hKe]
    obtain ⟨M', rT, hrun, hlive, hu⟩ := trapsQ_lrun_at (prof := prof) hctl (TrapsQ.left hT)
      (by rw [hm₁']; rfl)
    exact absurd ho (not_resolved_of_trap hrun hlive hu r₃)
  | some p =>
    obtain ⟨e₀, T₅⟩ := p
    obtain ⟨hTB₅, hRR⟩ := remove?_tabB hTB' hrm
    obtain ⟨hid, rfl, hH⟩ := hn.2 j e₀ hRR.1 hjfree
    obtain ⟨trR, hR⟩ := hret y.1 _ _ Hs Hs _ _ _ _ (c + 1) (make_liftAt hj32 hrm hH) hs1
      (removeThread?_callH _ _ _)
    have hres := result?_nextG hG hk (c + 1) (InstState.removeThread 1 { callI ι G with handles := T₅ })
      ftMake 0 2 [] [.own c] Hs
    obtain ⟨hm', hr⟩ := resolved_of_lrun (hm₁' ▸ hR) rfl hres r₃ hev₂ ho
    exact ⟨hc1, T₅, Hs, hTB₅, hr, hm'⟩

/-- **A resolved call of `make`** from a configuration between calls (thread table reusable,
leftovers `Ok`, the instance may leave, handle table `TabB`) was on `[]` and answered `own c`
(`c` the counter); it ends at the next configuration between calls with counter `c + 1 < 2^32`
and a `TabB` handle table. -/
theorem toy_make {a : List Silmaril.Wasm.Component.Reference.Val} {m' : Machine.Config (E3 P) Unit} {r : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (hc : c < 2 ^ 32) (hth : ThreadsFree ι.threads) (hG : G.Ok) (hleave : ι.mayLeave = true)
    (hTB : TabB ι.handles)
    (h : Calls prof (refHost P).hr (D P) (toyCfgX P c ι G) ⟨k⟩ ⟨0⟩ a m' (.resolved r)) :
    a = [] ∧ c + 1 < 2 ^ 32 ∧ ∃ T₅ Hs, TabB T₅ ∧ r = some [.own c] ∧
      m' = toyCfgX P (c + 1) (InstState.removeThread 1 { callI ι G with handles := T₅ })
        (nextG P G ftMake k 0 2 [] [.own c] Hs) := by
  obtain ⟨tr, hs, hev, -, ho⟩ := h
  obtain ⟨m₂, s, r₁⟩ := Steps.cons_iff.mp hs
  obtain ⟨hm₂, hk⟩ := toy_invoke_inv s
  have hadd := addThread?_free hth ⟨G.threads.length⟩
  by_cases ha : a = []
  · subst ha
    obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, rfl, hctl, hst, hK, hret⟩ := toy_callAt prof ftMake
      0 2 [] [] c ι _ _ G k G.handles _ rfl rfl hadd (fun m hm => by
        obtain ⟨⟩ := m
        dsimp only at hm
        subst hm
        exact runs_lower_make _ _)
    rcases hpre.inv (hm₂ ▸ r₁) with hl | ⟨tr', e, r'⟩
    · exact absurd ho (hl.not_holds _ _)
    have hcore : M₀.store.core = toyCs P c := by rw [hst]; rfl
    have hev' : ∀ ev, Label.host ev ∈ tr' → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
    obtain ⟨hc1, T₅, Hs, hTB₅, hr, hm'⟩ := make_from_core hc hG hk hleave hTB hst hK
      (fun cs' ιc ι₅ Hc H₅ ys ws cur trF c' hl hcs hrem =>
        hret cs' ιc ι₅ Hc H₅ ys ws cur trF c' hl hcs hrem)
      (hcore ▸ eq_coreCfg hctl ▸ r') hev' ho
    exact ⟨rfl, hc1, T₅, Hs, hTB₅, hr, hm'⟩
  · obtain ⟨trT, mT, rT, hrun, hlive, hu⟩ := toy_callAt_trap prof ftMake 0 2 a c ι _ G k rfl rfl
      hadd (fun m _ => lower_make_traps _ a ha m)
    exact absurd ho (not_resolved_of_trap hrun hlive hu (hm₂ ▸ r₁))

/-! ## `toyR` and the counter across calls of `make` -/

/-- **Resolved calls of `make` from `toyR`** keep `toyR`, increment the counter, and answer
`own` of the counter before the call (`CtrVCOn.step`, `mono` and `fresh` at `make`). -/
theorem toyR_make {es : List (String × FuncId)} {m m' : Machine.Config (E3 P) Unit}
    {f : FuncId} {a : List Silmaril.Wasm.Component.Reference.Val} {r : Option (List Silmaril.Wasm.Component.Reference.Val)} (hR : toyR P es m)
    (hf : es.lookup (names makeE) = some f)
    (h : Calls prof (refHost P).hr (refHost P).dispatch m ⟨k⟩ f a m' (.resolved r)) :
    toyR P es m' ∧ toyCtrP P m' = toyCtrP P m + 1 ∧ r = some [.own (toyCtrP P m)] := by
  obtain ⟨hes, c, ι, G, hm, hc, hι, hth, hTB, hG⟩ := hR
  subst hes hm
  obtain rfl : f = ⟨0⟩ := (Option.some.inj hf).symm
  rw [toyCfg_eq] at h
  have hleave : ι.mayLeave = true := by rw [hι]
  obtain ⟨-, hc1, T₅, Hs, hTB₅, hr, rfl⟩ := toy_make hc hth hG hleave hTB h
  have hι₅ : ({ ι with handles := T₅ } : InstState) =
      { handles := ({ ι with handles := T₅ } : InstState).handles,
        threads := ({ ι with handles := T₅ } : InstState).threads } := by
    rw [hι]
  have hR' := toyR_next (P := P) (ι := { ι with handles := T₅ }) hc1 hι₅ hth hTB₅ hG
    ⟨G.threads.length⟩ ftMake k 0 2 [] [.own c] Hs
  rw [toyCtrP_toyCfg P _ _ hc]
  refine ⟨hR', ?_, by rw [hr]⟩
  rw [← toyCfg_eq]
  exact toyCtrP_toyCfg P _ _ hc1

end Silmaril.Wasm.Resource.CompToy
