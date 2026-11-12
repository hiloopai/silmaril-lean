module

public import Silmaril.Proofs.Wasm.Resource.CompToy.DropCall

/-!
# The toy resource component: resolved calls of `drop`

* **`toy_drop`**: a resolved call of `drop` from a configuration between calls answered `[]`
  and ends at a configuration between calls with the same counter, an instance with only a
  `TabB` handle table and a reusable thread table (`ThreadsFree`), and leftovers that are `Ok`.
  The core phase goes through `core_inv` with `drop_calloutsAns` and `dropSpec_valid`; whether
  the destructor ran (frame `dF1`) or not (`dF0`), the return half is `toy_callAtX`;
* **`toyR_drop`**: resolved calls of `drop` from `toyR` keep `toyR` and the counter
  (`CtrVCOn.step` and `mono` at `drop`).

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

theorem tStoreX_nil (ft : WIT.FuncType Empty RtId) (c : ℕ) (ι ι' : InstState) (G : ToyGarb P)
    (k : ℕ) (args : List Val) (ιx : InstState) (Hx : List ResourceHandle)
    (cs : (core3P P).Store (CanonHost (core3P P))) :
    tStoreX P ft c ι ι' G k args ιx Hx cs [] [] [] =
      { tStore₄ P ft c ι ι' G k args ιx Hx with core := cs } := by
  unfold tStoreX
  simp only [List.append_nil]
  rfl

/-- The lift of `drop`'s (empty) result. -/
theorem drop_liftAt (S : CStore (E3 P)) (t : TaskId) :
    ∀ m : Machine.Config (E3 P) Unit, m.store = S →
      RunsQ (D P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))
        ABI.maxFlatResults (.ofList []) (resultTypes ftDrop)) m [.tau] ([], .ofList [])
        { m with store := S } := by
  intro m hm
  obtain ⟨⟩ := m
  dsimp only at hm
  subst hm
  exact runs_liftDtor _ _

theorem coreCfg_dF0 {M₀ : Machine.Config (E3 P) Unit} {S₀ : CStore (E3 P)} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {x : CoreSt (E3 P)} (hst : M₀.store = S₀) :
    coreCfg M₀ th K segs rest x = coreCfg (dF0 M₀ S₀ x.1) th K segs rest x := by
  obtain ⟨⟩ := M₀
  dsimp only at hst
  subst hst
  rfl

theorem inst_shape {ι : InstState} (h : ι = { handles := ι.handles, threads := ι.threads })
    (T : Table HandleEntry) (tb : Table ThreadId) :
    ({ ι with handles := T, threads := tb } : InstState) = { handles := T, threads := tb } := by
  rw [h]

/-- The instance between calls after a call of `drop`. -/
def DropAfter (ι' : InstState) : Prop :=
  ι' = { handles := ι'.handles, threads := ι'.threads } ∧ ThreadsFree ι'.threads ∧ TabB ι'.handles

/-- **The core phase and return of a call of `drop`** on `own n`, lowered to entry `i`. -/
theorem drop_from_core {M₀ m' : Machine.Config (E3 P) Unit} {n i : ℕ} {T₄ : Table HandleEntry}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {tr : List (Label (E3 P) Unit)} {r : Option (List Val)}
    (hι : ι = { handles := ι.handles, threads := ι.threads })
    (hth : ThreadsFree ι.threads) (hG : G.Ok) (hk : ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩)
    (hleave : ι.mayLeave = true) (hi32 : i < 2 ^ 32) (hTB₄ : TabB T₄)
    (hT₄ : T₄.get? i = some (.resource ⟨G.handles.length⟩))
    (hst : M₀.store = dS₀ c ι G k n T₄)
    (hret : ∀ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιc ι₅ : InstState)
        (Hc H₅ : List ResourceHandle) (ys : List FlatValue) (ws : List Val) (cur : FlatCursor)
        (trF : List (Label (E3 P) Unit)) (c' : ℕ) (Xt : List (Runtime.Task (E3 P)))
        (Xth : List Runtime.Thread) (Xc : List (Caller (E3 P)))
        (C : List (Option (Activation (E3 P) Unit))),
        (∀ m : Machine.Config (E3 P) Unit,
          m.store = tStoreX P ftDrop c ι (callI ι G) G k [.own n] ιc Hc cs' Xt Xth Xc →
          RunsQ (D P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
            ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
            ABI.maxFlatResults (.ofList ys) (resultTypes ftDrop)) m trF (ws, cur)
            { m with store := tStoreX P ftDrop c ι (callI ι G) G k [.own n] ι₅ H₅ cs' Xt Xth Xc }) →
        cs' = setCtr P (toyInst P).store.core c' →
        ι₅.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι₅) →
        ∃ tr, LRun prof (refHost P).hr (D P)
          { M₀ with store := tStoreX P ftDrop c ι (callI ι G) G k [.own n] ιc Hc cs' Xt Xth Xc,
                    conts := C, ctl := ⟨some ⟨G.threads.length⟩, .prog (K ys), segs⟩ :: rest } tr
          (toyCfgX P c' (InstState.removeThread 1 ι₅)
            (nextGX P G ftDrop k 2 4 [.own n] ws H₅ Xt Xth Xc C)))
    (r' : Steps prof (refHost P).hr (D P) (coreCfg M₀ (some ⟨G.threads.length⟩) K segs rest
      (toyCs P c, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 4 [i32Flat i])) tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : (CallOutcome.resolved r).Holds (refHost P).hr ⟨k⟩ m') :
    r = some [] ∧ ∃ ι' G', m' = toyCfgX P c ι' G' ∧ DropAfter ι' ∧ G'.Ok := by
  obtain ⟨T₅, hrm⟩ : ∃ T₅, T₄.remove? i = some (.resource ⟨G.handles.length⟩, T₅) :=
    ⟨⟨T₄.array.setIfInBounds i none, i :: T₄.free⟩, by simp [Table.remove?, hT₄]⟩
  obtain ⟨hTB₅, hRR⟩ := remove?_tabB hTB₄ hrm
  let w : BitVec 32 := BitVec.ofNat 32 i
  let ι₅ : InstState :=
    { callIn ι ⟨G.threads.length⟩ with handles := T₅, threads := dropT ⟨G.threads.length⟩ }
  have hl : M₀.store.lockdown = false := by rw [hst]; rfl
  have hv := dropSpec_valid (P := P) c w
  have hco := drop_calloutsAns (prof := prof) (M₀ := M₀) (c := c) (k := k) (n := n) (K := K)
    (segs := segs) (rest := rest)
    hi32 hrm hRR.2.1 hleave
  rw [coreCfg_dF0 hst] at r'
  obtain ⟨B', y, l, m₁, tr₂, hB', hreach, hnco, hx, r₃, hsuf⟩ :=
    core_inv (prof := prof) (Hc := Hdrop P w) (Inv := DInv M₀ (dS₀ c ι G k n T₄) n ι₅)
      (c₀ := Silmaril.Wasm.Execution.Core.invoke (toyCs P c) 4 [.i32 w])
      (fun B hB => by
        obtain ⟨cs, rfl | ⟨dtk, dthr, C, rfl⟩⟩ := hB
        · rfl
        · rfl) hco
      (fun c' hs => (hv.invoke_safe ⟨rfl, rfl⟩ hs).imp id fun ⟨o, he, _⟩ => ⟨o, he⟩)
      tr.length _ _ tr m' le_rfl ⟨_, .inl rfl⟩ .refl r' ho
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
  have hs' : Silmaril.Wasm.Execution.Core.Steps P (Hdrop P w)
      (Silmaril.Wasm.Execution.Core.invoke (toyCs P c) 4 [.i32 w])
      ⟨(y.2.config y.1).store, (y.2.config y.1).frame,
        Silmaril.Wasm.Execution.Core.vals vs⟩ := by
    rw [← hcode]
    exact hreach
  obtain ⟨hs1, hvs⟩ := hv.invoke_vals ⟨rfl, rfl⟩ hs'
  obtain rfl := Silmaril.Wasm.Logic.Core.Outcome.normal.inj hvs
  have hys' : ys = [] := Option.some.inj (hmap.symm.trans rfl)
  subst hys'
  rw [e] at hs1
  have hres : ∀ (ι' : InstState) (Xt : List (Runtime.Task (E3 P))) (Xth : List Runtime.Thread)
      (Xc : List (Caller (E3 P))) (C : List (Option (Activation (E3 P) Unit))) (H : List ResourceHandle),
      (toyCfgX P c ι' (nextGX P G ftDrop k 2 4 [.own n] [] H Xt Xth Xc C)).result? ⟨k⟩ =
        some (some []) :=
    fun ι' Xt Xth Xc C H => result?_nextGX hG hk c ι' ftDrop 2 4 [.own n] [] H Xt Xth Xc C
  obtain ⟨cs, rfl | ⟨dtk, dthr, C, rfl⟩⟩ := hB'
  · obtain ⟨trR, hR⟩ := hret y.1 { callI ι G with handles := T₄ } { callI ι G with handles := T₄ }
      _ _ [] [] (.ofList []) [.tau] c [] [] [] M₀.conts (drop_liftAt _ _) hs1
      (removeThread?_callH _ _ _)
    have hm₁' : m₁ = { M₀ with
        store := tStoreX P ftDrop c ι (callI ι G) G k [.own n] { callI ι G with handles := T₄ }
          (G.handles ++ [{ rt := ⟨0⟩, rep := n, own := true }]) y.1 [] [] []
        conts := M₀.conts
        ctl := ⟨some ⟨G.threads.length⟩, .prog (K []), segs⟩ :: rest } := by
      rw [hm₁, tStoreX_nil]
      rfl
    obtain ⟨hm', hr⟩ := resolved_of_lrun (hm₁' ▸ hR) rfl (hres _ _ _ _ _ _) r₃ hev₂ ho
    obtain ⟨tb, etb, htb⟩ := removeThread_call (ι := { ι with handles := T₄ }) hth
      ⟨G.threads.length⟩
    have hX : InstState.removeThread 1 { callI ι G with handles := T₄ } =
        { handles := T₄, threads := tb } :=
      (show InstState.removeThread 1 (callIn { ι with handles := T₄ } ⟨G.threads.length⟩) = _
        from etb).trans (inst_shape hι _ _)
    refine ⟨hr, _, _, hm', ⟨?_, ?_, ?_⟩, nextGX_ok hG _ _ _ _ _ _ _ _ _ _ _⟩
    · rw [hX]
    · rw [hX]
      exact htb
    · rw [hX]
      exact hTB₄
  · obtain ⟨trR, hR⟩ := hret y.1 ι₅ ι₅ _ _ [] [] (.ofList []) [.tau] c [dtk] [dthr]
      [.sub (.destructor n)] C (drop_liftAt _ _) hs1 (removeThread?_dropT _ _ _)
    have hm₁' : m₁ = { M₀ with
        store := tStoreX P ftDrop c ι (callI ι G) G k [.own n] ι₅
          (G.handles ++ [{ rt := ⟨0⟩, rep := n, own := true }]) y.1 [dtk] [dthr]
          [.sub (.destructor n)]
        conts := C
        ctl := ⟨some ⟨G.threads.length⟩, .prog (K []), segs⟩ :: rest } := by
      rw [hm₁]
      rfl
    obtain ⟨hm', hr⟩ := resolved_of_lrun (hm₁' ▸ hR) rfl (hres _ _ _ _ _ _) r₃ hev₂ ho
    refine ⟨hr, _, _, hm', ⟨?_, ?_, ?_⟩, nextGX_ok hG _ _ _ _ _ _ _ _ _ _ _⟩
    · rw [removeThread_dropT, hι]
    · rw [removeThread_dropT]
      exact .inr (.inr rfl)
    · rw [removeThread_dropT]
      exact hTB₅

/-- The lowering of `own n` at the lowering point of a call of `drop`, to the new entry `i`. -/
theorem drop_lowerAt {n i : ℕ} {T₄ : Table HandleEntry} {trL : List (Label (E3 P) Unit)}
    (hL : ∀ (m : Machine.Config (E3 P) Unit) (ι₁ ι₂ : InstState) (i : ℕ),
      m.store.insts = [ι₁] →
      ι₁.addHandle? (.resource ⟨m.store.resHandles.length⟩) = some (i, ι₂) →
      RunsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatParams [.own n] (paramTypes ftDrop) none) m trL ([i32Flat i] ++ [])
        { m with store := newSt m.store n ι₂ })
    (hadd : (callI ι G).addHandle? (.resource ⟨G.handles.length⟩) =
      some (i, { callI ι G with handles := T₄ })) :
    ∀ m : Machine.Config (E3 P) Unit, m.store = tStore₃ P ftDrop c ι (callI ι G) G k [.own n] →
      RunsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatParams [.own n] (paramTypes ftDrop) none) m trL [i32Flat i]
        { m with store := dS₀ c ι G k n T₄ } := by
  intro m hm
  obtain ⟨⟩ := m
  dsimp only at hm
  subst hm
  exact hL _ (callI ι G) _ i rfl hadd

/-- **A resolved call of `drop`** from a configuration between calls answered `[]` and ends at a
configuration between calls with the same counter. -/
theorem toy_drop {a : List Val} {m' : Machine.Config (E3 P) Unit} {r : Option (List Val)}
    (hι : ι = { handles := ι.handles, threads := ι.threads })
    (hth : ThreadsFree ι.threads) (hG : G.Ok) (hleave : ι.mayLeave = true)
    (hTB : TabB ι.handles)
    (h : Calls prof (refHost P).hr (D P) (toyCfgX P c ι G) ⟨k⟩ ⟨2⟩ a m' (.resolved r)) :
    r = some [] ∧ ∃ ι' G', m' = toyCfgX P c ι' G' ∧ DropAfter ι' ∧ G'.Ok := by
  obtain ⟨tr, hs, hev, -, ho⟩ := h
  obtain ⟨m₂, s, r₁⟩ := Steps.cons_iff.mp hs
  obtain ⟨hm₂, hk⟩ := toy_invoke_inv s
  have hadd := addThread?_free hth ⟨G.threads.length⟩
  by_cases ha : ∃ n, a = [.own n] ∧
      ∃ i T₄, (callI ι G).handles.add? (.resource ⟨G.handles.length⟩) = some (i, T₄)
  · obtain ⟨n, rfl, i, T₄, hT⟩ := ha
    obtain ⟨hi32, hTB₄, hAR⟩ := add?_tabB (t := (callI ι G).handles) hTB hT
    have hadd₄ : (callI ι G).addHandle? (.resource ⟨G.handles.length⟩) =
        some (i, { callI ι G with handles := T₄ }) := by
      simp [InstState.addHandle?, hT]
    obtain ⟨trL, hL⟩ := runs_lower_drop (P := P) (th := some ⟨G.threads.length⟩)
      ⟨G.tasks.length⟩ n
    obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, rfl, hctl, hst, -, hret⟩ := toy_callAtX prof ftDrop
      2 4 [.own n] [i32Flat i] c ι _ { callI ι G with handles := T₄ } G k
      (G.handles ++ [{ rt := ⟨0⟩, rep := n, own := true }]) trL rfl rfl hadd
      (drop_lowerAt hL hadd₄)
    rcases hpre.inv (hm₂ ▸ r₁) with hl | ⟨tr', e, r'⟩
    · exact absurd ho (hl.not_holds _ _)
    have hcore : M₀.store.core = toyCs P c := by rw [hst]; rfl
    have hev' : ∀ ev, Label.host ev ∈ tr' → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
    exact drop_from_core hι hth hG hk hleave hi32 hTB₄ hAR.2.1 hst
      (fun cs' ιc ι₅ Hc H₅ ys ws cur trF c' Xt Xth Xc C hl hcs hrem =>
        hret cs' ιc ι₅ Hc H₅ ys ws cur trF c' Xt Xth Xc C hl hcs hrem)
      (hcore ▸ eq_coreCfg hctl ▸ r') hev' ho
  · have hT : ∀ m : Machine.Config (E3 P) Unit, m.store = tStore₃ P ftDrop c ι (callI ι G) G k a →
        ∃ trT mT, TrapsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none
          ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
          ABI.maxFlatParams a (paramTypes ftDrop) none) m trT mT := by
      intro m hm
      refine lower_drop_traps _ a m (ι₁ := callI ι G) (by rw [hm]; rfl) ?_
      by_cases hn : ∃ n, a = [.own n]
      · obtain ⟨n, rfl⟩ := hn
        refine .inr ⟨n, rfl, ?_⟩
        rw [hm]
        cases hx : (callI ι G).handles.add? (.resource ⟨G.handles.length⟩) with
        | none => simp [InstState.addHandle?, hx, tStore₃, tStore₂, tStore₁, toyStoreX]
        | some p => exact absurd ⟨n, rfl, p.1, p.2, hx⟩ ha
      · exact .inl fun n e => hn ⟨n, e⟩
    obtain ⟨trT, mT, rT, hrun, hlive, hu⟩ := toy_callAt_trap prof ftDrop 2 4 a c ι _ G k rfl rfl
      hadd hT
    exact absurd ho (not_resolved_of_trap hrun hlive hu (hm₂ ▸ r₁))

/-- **Resolved calls of `drop` from `toyR`** keep `toyR` and the counter (`CtrVCOn.step` and
`CtrVCOn.mono` at `drop`). -/
theorem toyR_drop {es : List (String × FuncId)} {m m' : Machine.Config (E3 P) Unit}
    {f : FuncId} {a : List Val} {r : Option (List Val)} (hR : toyR P es m)
    (hf : es.lookup (names dropE) = some f)
    (h : Calls prof (refHost P).hr (refHost P).dispatch m ⟨k⟩ f a m' (.resolved r)) :
    toyR P es m' ∧ toyCtrP P m' = toyCtrP P m := by
  obtain ⟨hes, c, ι, G, hm, hc, hι, hth, hTB, hG⟩ := hR
  subst hes hm
  obtain rfl : f = ⟨2⟩ := (Option.some.inj hf).symm
  rw [toyCfg_eq] at h
  have hleave : ι.mayLeave = true := by rw [hι]
  obtain ⟨-, ι', G', rfl, ⟨hι', hth', hTB'⟩, hG'⟩ := toy_drop hι hth hG hleave hTB h
  refine ⟨?_, ?_⟩
  · rw [← toyCfg_eq]
    exact ⟨rfl, c, ι', G', rfl, hc, hι', hth', hTB', hG'⟩
  · rw [← toyCfg_eq, toyCtrP_toyCfg P _ _ hc, toyCtrP_toyCfg P _ _ hc]

end Silmaril.Wasm.Resource.CompToy
