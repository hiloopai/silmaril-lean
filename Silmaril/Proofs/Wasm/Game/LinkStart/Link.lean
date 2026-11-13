module

public import Silmaril.Proofs.Wasm.Game.LinkStart.Phases
public import Silmaril.Proofs.Wasm.Game.LinkStart.Main

/-!
# Static linking with start functions is composition: proofs

For a link with start functions (`StartSetup`) in the scalar fragment and **every profile**
`P`, the finite plays of the instantiable strategy of the linked module (its start sequence:
the provider's start function, then the consumer's) are those of the game-semantic link
`StartSetup.linkInst P` (provider instantiated, and its start function run, before the
consumer) (`linkedInst_forget`).

Both strategies are closed, so a play ending in a Proponent move of the link is the upper
projection of a trace of the consumer's link system whose lower projection is a trace of the
provider's instantiable system (`comp_noEv_isP`). The proof follows such traces through the
three worlds of `Linking.Setup`:

* `linked_sub` (`linked ⊆ link`): a linked start sequence runs in the shared world
  (`link_back`), where the provider's start function is a run of the provider
  (`prov_back`) and the consumer's a run of the consumer whose stub calls are provider
  activations (`cons_back`); after both, the linked module's plays are the provider object
  interacting with the consumer at the stores reached (`Setup.linked_objPlays_at`);
* `comp_sub` (`link ⊆ linked`): conversely, the provider's start, then the consumer's start
  with its stub calls answered by the provider's plays (`provider_split`), run in the shared
  world (`prov_fwd`, `cons_fwd`) and then in the linked one (`link_fwd`), after which the
  composite plays are linked plays (`Setup.interact_subset_linked_at`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
  Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Proofs.Wasm.Game.Start Silmaril.Proofs.Wasm.Game.LinkStart
  Silmaril.Proofs.Wasm.Game.Linking.Split Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable (S : StartSetup) (P : Profile)

/-- The moves of the consumer's link system. -/
abbrev CM : Type :=
  Move (S.consumerI.E.withInst (Behaviour Val)) (S.consumerI.F.withInst (Behaviour Val))

/-- The moves of the provider's instantiable system. -/
abbrev PM : Type := Move S.providerI.E (S.providerI.F.withInst (Behaviour Val))

/-- The moves of the link. -/
abbrev TM : Type := Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))

/-- The provider's instantiable system. -/
noncomputable abbrev Lp : LTS S.providerI.E (S.providerI.F.withInst (Behaviour Val)) :=
  (S.providerI.instSys P S.sp S.provStart).toLTS

/-- The consumer's link system. -/
noncomputable abbrev Lc : LTS (S.consumerI.E.withInst (Behaviour Val))
    (S.consumerI.F.withInst (Behaviour Val)) :=
  (S.consumerI.instSys P S.scs S.consStart).consumerLTS

/-- The linked module's instantiable system. -/
noncomputable abbrev Ll : LTS S.linkedI.E (S.linkedI.F.withInst (Behaviour Val)) :=
  (S.linkedI.instSysSeq P S.sl S.linkedStarts).toLTS

theorem noEv_nil (a : Ev S.providerI.E) : False := Setup.noEv_nil a

/-- The pieces of the link. -/
theorem linkInst_forget_eq :
    (S.linkInst P).forget = (Strategy.ofLTS (Lp S P)).comp (Strategy.ofLTS (Lc S P)) := rfl

theorem linkedInst_forget_eq :
    (S.linkedInstStrategy P).forget = Strategy.ofLTS (Ll S P) := rfl

/-! ## Facts at the start -/

variable {S P}

theorem linkedStarts_eq : S.linkedStarts = S.provStart.toList ++ S.consStart.toList := rfl

theorem shared_provTyped {σ : Store Nat} (hf : σ.funcs = S.sc.funcs) :
    ∀ a ∈ S.provStart, StartTyped σ a := fun a ha =>
  Setup.startTyped_of_funcs (startTyped_sc_of_sp S (S.provStartTyped a ha)) hf

theorem shared_consTyped {σ : Store Nat} (hf : σ.funcs = S.sc.funcs) :
    ∀ a ∈ S.consStart, StartTyped σ a := fun a ha =>
  Setup.startTyped_of_funcs (startTyped_sc_of_scs S (S.consStartTyped a ha)) hf

theorem idle_funcs {St : Static S.toSetup} {σ π κ : Store Nat} (hI : Idle St σ π κ) :
    σ.funcs = S.sc.funcs ∧ π.funcs = S.sp.funcs ∧ κ.funcs = S.scs.funcs := by
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI
  exact ⟨hW.fσ, hW.fπ, hW.fκ⟩

/-- The first moves of a failing provider, in the consumer's link system. -/
theorem lc_fail_trace (b : Behaviour Val) :
    ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (InstAns.fail b)),
      .inr (.ans (m := none) (InstAns.fail b))] : List (CM S)) ∈ (Lc S P).Traces :=
  ⟨_, .vis InstSystem.LinkStep.askInst (.vis InstSystem.LinkStep.pcall
    (.vis (InstSystem.LinkStep.pfail b) (.vis (InstSystem.LinkStep.preport b) (.nil _))))⟩

/-- The first moves of a ready provider, in the consumer's link system. -/
theorem lc_ready_run {w : List (CM S)} {z : (Lc S P).State}
    (h : (Lc S P).Run (.inst (S.consumerI.instSys P S.scs S.consStart).istart) w z) :
    ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) InstAns.ready)] : List (CM S)) ++ w ∈
      (Lc S P).Traces :=
  ⟨_, .vis InstSystem.LinkStep.askInst (.vis InstSystem.LinkStep.pcall
    (.vis InstSystem.LinkStep.pready h))⟩

/-- A play of the composite from traces of the link system and the provider. -/
theorem comp_of_traces {t : List (CM S)}
    (ht : t ∈ (Lc S P).Traces) (hl : (lower t).map .inr ∈ (Lp S P).Traces) :
    (upper t).map .inr ∈ (Strategy.ofLTS (Lp S P)).comp (Strategy.ofLTS (Lc S P)) :=
  comp_noEv_of_traces (noEv_nil S) ht (InstSystem.consumer_traces_legal _ ht) hl
    (InstSystem.traces_legal _ hl)

theorem lp_legal (S : StartSetup) (P : Profile) : ∀ w ∈ (Lp S P).Traces, Legal w :=
  fun _ hw => InstSystem.traces_legal _ hw

/-- A trace of the linked module is one of its plays. -/
theorem mem_ll {u : List (TM S)} (hu : u ∈ (Ll S P).Traces) : u ∈ Strategy.ofLTS (Ll S P) :=
  Strategy.mem_ofLTS_of_mem_traces hu (InstSystem.traces_legal _ hu)

/-- The prefix of the link system's traces when the provider is ready. -/
abbrev pre (S : StartSetup) : List (CM S) :=
  [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) InstAns.ready)]

theorem lower_pre (X : List (CM S)) :
    lower (pre S ++ X) = [Ev.ask none, Ev.ans (m := none) InstAns.ready] ++ lower X := by
  simp [pre]

theorem upper_pre (X : List (CM S)) : upper (pre S ++ X) = [Ev.ask none] ++ upper X := by
  simp [pre]

/-- The lower projection of a consumer's start phase and the rest. -/
theorem lower_start (evs : List (Ev S.consumerI.E)) (a : InstAns (Behaviour Val))
    (Y : List (CM S)) :
    lower (evs.map (InstSystem.liftL (F := S.consumerI.F) (R := Behaviour Val)) ++
      .inr (.ans (m := none) a) :: Y) = evs.map liftEv ++ lower Y := by
  rw [lower_append, lower_map_liftL, lower_cons_inr]

theorem upper_start (evs : List (Ev S.consumerI.E)) (a : InstAns (Behaviour Val))
    (Y : List (CM S)) :
    upper (evs.map (InstSystem.liftL (F := S.consumerI.F) (R := Behaviour Val)) ++
      .inr (.ans (m := none) a) :: Y) = .ans (m := none) a :: upper Y := by
  rw [upper_append, upper_map_liftL, upper_cons_inr, List.nil_append]

/-- A provider play from the store its start function left, as a provider trace. -/
theorem lp_ready {π₁ : Store Nat} (hπ₁ : StartsReach P S.sp S.provStart π₁)
    {pp : List (Move S.providerI.E S.providerI.F)} (hpp : pp ∈ S.providerI.plays P π₁) :
    ([.inr (.ask none), .inr (.ans (m := none) InstAns.ready)] ++
      ((upper pp).map liftEv).map .inr : List (PM S)) ∈ (Lp S P).Traces := by
  rw [← closed_map_liftMove rfl pp]
  exact instSys_ready_traces.2 ⟨π₁, hπ₁, pp, rfl, hpp⟩

/-! ## The linked module's plays are plays of the link -/

section Back

variable (hS : S.Scalar) {St : Static S.toSetup} (hOp : St.Op = S.provOwn)
  (hOc : St.Oc = S.consOwn)
include hS hOp hOc

omit hOc in
/-- The linked provider's start function, read back in the other two worlds. -/
theorem back_prov {l₁ : Store Nat} (h : StartsReach P S.sl S.provStart l₁) :
    ∃ σ₁ π₁, S.Persistent σ₁ l₁ ∧ IdleT St σ₁ π₁ S.scs ∧ StartsReach P S.sp S.provStart π₁ := by
  have hI0 : IdleT St S.sc S.sp S.scs := ⟨St.idle, hS.provider.storeOk, hS.consumer.storeOk⟩
  obtain ⟨σ₁, hσ₁, hp₁⟩ := link_reach_back S (S.persistent_initial hS) (shared_provTyped rfl) h
  obtain ⟨π₁, hπ₁, hI₁⟩ :=
    prov_back S hS hI0 (provStart_own S St hOp) S.provStartTyped hσ₁
  exact ⟨σ₁, π₁, hp₁, hI₁, hπ₁⟩

omit hOc in
/-- A failing linked provider start function is a failing link. -/
theorem linked_sub_provFail {b : Behaviour Val} (h : StartFails P S.sl S.provStart b) :
    ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] : List (TM S)) ∈
      (Strategy.ofLTS (Lp S P)).comp (Strategy.ofLTS (Lc S P)) := by
  have hI0 : IdleT St S.sc S.sp S.scs := ⟨St.idle, hS.provider.storeOk, hS.consumer.storeOk⟩
  have hb₁ : StartFails P S.sc S.provStart b :=
    link_fail_back S (S.persistent_initial hS) (shared_provTyped rfl) h
  have hb₂ : StartFails P S.sp S.provStart b :=
    prov_fail_back S hS hI0 (provStart_own S St hOp) S.provStartTyped hb₁
  have hl : ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] ++ [] :
      List (PM S)) ∈ (Lp S P).Traces := instSys_fail_traces.2 ⟨hb₂, rfl⟩
  rw [List.append_nil] at hl
  exact InstSystem.link_comp_fail (S := S.consumerI.instSys P S.scs S.consStart) (noEv_nil S)
    (L₁ := Lp S P) (lp_legal S P) hl

/-- A failing linked consumer start function is a failing link. -/
theorem linked_sub_consFail {l₁ : Store Nat} {b : Behaviour Val}
    (h₁ : StartsReach P S.sl S.provStart l₁) (h : StartFails P l₁ S.consStart b) :
    ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] : List (TM S)) ∈
      (Strategy.ofLTS (Lp S P)).comp (Strategy.ofLTS (Lc S P)) := by
  obtain ⟨σ₁, π₁, hp₁, hI₁, hπ₁⟩ := back_prov hS hOp h₁
  obtain ⟨c, run, hf⟩ := link_fail_back S hp₁ (shared_consTyped (idle_funcs hI₁.1).1) h
  obtain ⟨r, final, hr, hback⟩ := result_of_startFailed hf
  obtain ⟨evs, pp, κ', π', tc', hl, hres, hpp, hproj, -⟩ :=
    cons_back S hS hI₁ (consStart_own S St hOc) S.consStartTyped run final hr
  have hrun := InstSystem.consumer_run_fail _ ((irun_iff_lrun (s := S.scs) (start := S.consStart)).2 hl) (hback hres)
  have hc := InstSystem.link_comp_start (S := S.consumerI.instSys P S.scs S.consStart)
    (noEv_nil S) (L₁ := Lp S P) (lp_legal S P) (L := []) (U := []) hrun rfl rfl
    (by rw [List.append_nil, hproj]; exact lp_ready hπ₁ ⟨_, hpp⟩)
  simp only [List.map_nil, List.append_nil] at hc
  exact hc

/-- A linked module ready after both start functions plays as the link. -/
theorem linked_sub_ready {l₁ l₂ : Store Nat} (h₁ : StartsReach P S.sl S.provStart l₁)
    (h₂ : StartsReach P l₁ S.consStart l₂) {q : List (Move S.linkedI.E S.linkedI.F)}
    (hq : q ∈ S.linkedI.plays P l₂) :
    ([.inr (.ask none), .inr (.ans (m := none) InstAns.ready)] ++ q.map liftMove :
      List (TM S)) ∈ (Strategy.ofLTS (Lp S P)).comp (Strategy.ofLTS (Lc S P)) := by
  obtain ⟨σ₁, π₁, hp₁, hI₁, hπ₁⟩ := back_prov hS hOp h₁
  obtain ⟨σ₂, ⟨ts₂, run, final⟩, hp₂⟩ :=
    link_reach_back S hp₁ (shared_consTyped (idle_funcs hI₁.1).1) h₂
  obtain ⟨evs, pp₁, κ₁, π₂, tc₁, hl, hres, hpp₁, hproj, hI₂⟩ :=
    cons_back S hS hI₁ (consStart_own S St hOc) S.consStartTyped run final (.inl rfl)
  have hqo : upper q ∈ S.linkedI.objPlays P l₂ := ⟨q, hq, rfl⟩
  rw [S.linked_objPlays_at hS St hI₂ hp₂] at hqo
  obtain ⟨pc, hpc, ⟨pp₂, hpp₂, hu₂⟩, hupc⟩ := hqo
  obtain ⟨z, hz⟩ := consumer_export_run_of (s₀ := S.scs) (start := S.consStart) hpc
  have hrun := InstSystem.consumer_run_ready _ ((irun_iff_lrun (s := S.scs) (start := S.consStart)).2 hl) ⟨hres, rfl⟩ hz
  have hpp : pp₁ ++ pp₂ ∈ S.providerI.plays P π₁ :=
    Silmaril.Proofs.Wasm.Game.ScalarInstance.append_mem_plays_of hpp₁ hpp₂
  have hc := InstSystem.link_comp_start (S := S.consumerI.instSys P S.scs S.consStart)
    (noEv_nil S) (L₁ := Lp S P) (lp_legal S P) (L := lower pc) (U := upper pc) hrun
    (lower_map_liftC pc) (upper_map_liftC pc)
    (by
      have h := lp_ready hπ₁ hpp
      have e₀ : upper (pp₁ ++ pp₂) = upper pp₁ ++ upper pp₂ := upper_append _ _
      have e₁ : upper pp₁ ++ upper pp₂ = id (α := List (Ev S.providerI.F)) evs ++ lower pc := by
        rw [hu₂, hproj]
        rfl
      rw [e₀, e₁] at h
      exact h)
  rw [closed_map_liftMove rfl q, ← hupc]
  exact hc

/-- **The linked module's plays are plays of the link** (those ending in a Proponent move). -/
theorem linked_sub {w : List (TM S)} {o : TM S} (ho : o.IsP) (ht : w ++ [o] ∈ (Ll S P).Traces) :
    w ++ [o] ∈ (Strategy.ofLTS (Lp S P)).comp (Strategy.ofLTS (Lc S P)) := by
  rcases InstSystem.toLTS_trace_cases _ (instSysSeq_no_icall rfl) ht with h | h | ⟨a, w', h⟩
  · exact absurd h (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  · have hl := congrArg List.getLast? h
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at hl
    obtain rfl : o = askInst := Option.some.inj hl
    exact absurd ho (by simp [askInst, Move.IsP])
  · rw [h] at ht ⊢
    cases a with
    | ready =>
      obtain ⟨l₂, hd, q, rfl, hq⟩ := instSysSeq_ready_traces.1 ht
      obtain ⟨l₁, h₁, h₂⟩ := seqDone_pair_iff.1 hd
      exact linked_sub_ready hS hOp hOc h₁ h₂ hq
    | fail b =>
      obtain ⟨hf, rfl⟩ := instSysSeq_fail_traces.1 ht
      rw [List.append_nil]
      rcases seqFail_pair_iff.1 hf with h₁ | ⟨l₁, h₁, h₂⟩
      · exact linked_sub_provFail hS hOp h₁
      · exact linked_sub_consFail hS hOp hOc h₁ h₂

/-! ## The link's plays are plays of the linked module -/

omit hOc in
/-- A failing provider in the link is a failing linked provider start function. -/
theorem comp_sub_provFail {b : Behaviour Val}
    (hb : ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] : List (PM S)) ∈
      (Lp S P).Traces) :
    ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] : List (TM S)) ∈
      Strategy.ofLTS (Ll S P) := by
  have hb' : ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] ++ [] : List (PM S)) ∈
      (Lp S P).Traces := by rw [List.append_nil]; exact hb
  have h₁ : StartFails P S.sp S.provStart b := (instSys_fail_traces.1 hb').1
  have h₂ : StartFails P S.sc S.provStart b := prov_fail_fwd S St.idle (provStart_own S St hOp) h₁
  have h₃ : StartFails P S.sl S.provStart b :=
    link_fail_fwd S (S.persistent_initial hS) (shared_provTyped rfl) h₂
  have hl : ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] ++ [] : List (TM S)) ∈
      (Ll S P).Traces := instSysSeq_fail_traces.2 ⟨seqFail_pair_iff.2 (.inl h₃), rfl⟩
  rw [List.append_nil] at hl
  exact mem_ll hl

omit hOc in
/-- The provider's start function of the link, then in the shared and linked worlds. -/
theorem fwd_prov {π₁ : Store Nat} (hπ₁ : StartsReach P S.sp S.provStart π₁) :
    ∃ σ₁ l₁, Idle St σ₁ π₁ S.scs ∧ S.Persistent σ₁ l₁ ∧ StartsReach P S.sl S.provStart l₁ := by
  obtain ⟨σ₁, hσ₁, hI₁⟩ := prov_fwd S St.idle (provStart_own S St hOp) hπ₁
  obtain ⟨l₁, hl₁, hp₁⟩ := link_reach_fwd S (S.persistent_initial hS) (shared_provTyped rfl) hσ₁
  exact ⟨σ₁, l₁, hI₁, hp₁, hl₁⟩

/-- **The link's plays after the consumer's instantiation phase are linked plays.** -/
theorem comp_sub_inst {l : List (Ev S.consumerI.E)} {a : InstAns (Behaviour Val)}
    {Y : List (CM S)} {c' : (S.consumerI.instSys P S.scs S.consStart).IConf}
    (hIR : InstSystem.IRun (S.consumerI.instSys P S.scs S.consStart)
      (S.consumerI.instSys P S.scs S.consStart).istart l c')
    (ha : (a = .ready ∧ ∃ st z, (S.consumerI.instSys P S.scs S.consStart).iready c' st ∧
        (Lc S P).Run (.ready st) Y z) ∨
      ∃ b, a = .fail b ∧ (S.consumerI.instSys P S.scs S.consStart).ifail c' b ∧ Y = [])
    (hpl : ([.inr (.ask none), .inr (.ans (m := none) InstAns.ready)] ++
      (l.map liftEv ++ lower Y).map .inr : List (PM S)) ∈ (Lp S P).Traces) :
    ([.inr (.ask none), .inr (.ans (m := none) a)] ++ (upper Y).map .inr : List (TM S)) ∈
      Strategy.ofLTS (Ll S P) := by
  obtain ⟨π₁, hπ₁, qp, hqe, hqp⟩ := instSys_ready_traces.1 hpl
  obtain ⟨σ₁, l₁, hI₁, hp₁, hl₁⟩ := fwd_prov hS hOp hπ₁
  have hlr : LRun S.consumerI P (S.scs, startThread S.consStart) l c' :=
    (irun_iff_lrun (s := S.scs) (start := S.consStart)).1 hIR
  obtain ⟨L, pc, hYl, hstep⟩ : ∃ (L : List (Ev S.consumerI.E)) (pc : List (Move S.consumerI.E S.consumerI.F)),
      lower Y = L.map liftEv ∧
      ((a = .ready ∧ Y = pc.map liftC ∧ L = lower pc ∧ pc ∈ S.consumerI.plays P c'.1 ∧
        ResultAt c'.1 c'.2 (.values [])) ∨
        ∃ b, a = .fail b ∧ StartFailed c' b ∧ Y = [] ∧ L = []) := by
    rcases ha with ⟨rfl, st, z, ⟨hres, rfl⟩, hY⟩ | ⟨b, rfl, hf, rfl⟩
    · obtain ⟨pc, rfl, hpc⟩ := consumer_export_run hY
      exact ⟨lower pc, pc, lower_map_liftC pc, .inl ⟨rfl, rfl, rfl, hpc, hres⟩⟩
    · exact ⟨[], [], rfl, .inr ⟨b, rfl, hf, rfl, rfl⟩⟩
  have hq' : qp = (l ++ L).map .inr := by
    apply eq_map_inr_of_liftMove
    rw [← hqe, hYl]
    exact congrArg (List.map Sum.inr) (List.map_append (f := liftEv) (l₁ := l) (l₂ := L)).symm
  obtain ⟨q', hpath⟩ := hqp
  rw [hq'] at hpath
  obtain ⟨π₂, pp₁, pp₂, -, hpp₁, hu₁, hpp₂, hu₂⟩ :=
    provider_split S hlr hpath (upper_map_inr _)
  rcases hstep with ⟨rfl, rfl, rfl, hpc, hres⟩ | ⟨b, rfl, hf, rfl, rfl⟩
  · obtain ⟨σ₂, ts₂, run₂, hres₂, hI₂⟩ :=
      cons_fwd S hI₁ (consStart_own S St hOc) hlr hres (.inl rfl) hpp₁ hu₁.symm
    obtain ⟨l₂, t₂, run', hres', hp₂⟩ :=
      link_fwd S hp₁ (shared_consTyped (idle_funcs hI₁).1) run₂ hres₂
    have hint : upper pc ∈ interact (S.providerI.objPlays P π₂) (S.consumerI.plays P c'.1) :=
      ⟨pc, hpc, ⟨pp₂, ⟨q', hpp₂⟩, hu₂⟩, rfl⟩
    obtain ⟨qℓ, hqℓ, huq⟩ := S.interact_subset_linked_at St hI₂ hp₂ hint
    have h := (instSysSeq_ready_traces (I := S.linkedI) (P := P)).2
      ⟨l₂, seqDone_pair_iff.2 ⟨l₁, hl₁, ⟨t₂, run', hres'⟩⟩, qℓ, rfl, hqℓ⟩
    rw [closed_map_liftMove rfl qℓ, huq] at h
    rw [upper_map_liftC]
    exact mem_ll h
  · obtain ⟨r, final, hr, hback⟩ := result_of_startFailed hf
    obtain ⟨σ₂, ts₂, run₂, hres₂, -⟩ :=
      cons_fwd S hI₁ (consStart_own S St hOc) hlr final hr hpp₁ hu₁.symm
    have hf₂ : StartFails P l₁ S.consStart b :=
      link_fail_fwd S hp₁ (shared_consTyped (idle_funcs hI₁).1) ⟨_, run₂, hback hres₂⟩
    have h := (instSysSeq_fail_traces (I := S.linkedI) (P := P) (w := [])).2
      ⟨seqFail_pair_iff.2 (.inr ⟨l₁, hl₁, hf₂⟩), rfl⟩
    exact mem_ll h

/-- **The link's plays are plays of the linked module** (those ending in a Proponent move). -/
theorem comp_sub {w : List (TM S)} {o : TM S} (ho : o.IsP)
    (h : w ++ [o] ∈ (Strategy.ofLTS (Lp S P)).comp (Strategy.ofLTS (Lc S P))) :
    w ++ [o] ∈ Strategy.ofLTS (Ll S P) := by
  rcases InstSystem.link_comp_cases (S := S.consumerI.instSys P S.scs S.consStart) (noEv_nil S)
      (L₁ := Lp S P) ho h with ⟨b, hb, heq⟩ | ⟨l, a, Y, c', hIR, ha, hpl, heq⟩
  · rw [heq]
    exact comp_sub_provFail hS hOp hb
  · rw [heq]
    exact comp_sub_inst hS hOp hOc hIR ha hpl

end Back

/-- **M3 with start functions** (finite plays, every profile): the instantiable strategy of the
linked module, its start sequence included, has the plays of the link of the instantiable
provider and consumer. -/
theorem linkedInst_forget (hS : S.Scalar) :
    (S.linkedInstStrategy P).forget = (S.linkInst P).forget := by
  obtain ⟨St, hOp, hOc⟩ := static_spec S.toSetup hS
  rw [linkedInst_forget_eq, linkInst_forget_eq]
  apply strategy_ext_isP
  intro w o ho
  constructor
  · intro h
    exact linked_sub hS hOp hOc ho (Silmaril.Proofs.Wasm.Game.GamesAux.trace_of_mem_ofLTS h ho)
  · intro h
    exact comp_sub hS hOp hOc ho h

/-! ## Instantiation outcomes of the linked module -/

theorem startsReach_iff_startsTo {s s' : Store Nat} {o : Option Nat} :
    StartsReach P s o s' ↔ StartsTo P (Det.noHost : HostSemantics Nat) s o s' := by
  constructor
  · rintro ⟨t', hr, hres⟩
    exact ⟨_, reach_iff_steps.1 ⟨(s', t'), hr, rfl⟩, hres, Thread.config_store _ _⟩
  · rintro ⟨_, hc', hcode, rfl⟩
    obtain ⟨c, hc, rfl⟩ := reach_iff_steps.2 hc'
    have hs : (c.2.config c.1).store = c.1 := Thread.config_store _ _
    rw [hs]
    exact ⟨c.2, hc, hcode⟩

/-- **The linked module is ready exactly when its start sequence returns**: the provider's start
function, then the consumer's, under the empty host. -/
theorem linked_instReady_iff :
    (S.linkedInstStrategy P).InstReady ↔
      ∃ l₁ l₂, StartsTo P (Det.noHost : HostSemantics Nat) S.sl S.provStart l₁ ∧
        StartsTo P (Det.noHost : HostSemantics Nat) l₁ S.consStart l₂ := by
  have e : (S.linkedInstStrategy P).InstReady ↔
      ([askInst, ansInst .ready] ++ [] : List (Move S.linkedI.E (S.linkedI.F.withInst (Behaviour Val))))
        ∈ (Ll S P).Traces := by
    show ([askInst, ansInst .ready] : List (TM S)) ∈ Strategy.ofLTS (Ll S P) ↔ _
    rw [List.append_nil]
    exact ⟨fun h => Silmaril.Proofs.Wasm.Game.GamesAux.trace_of_mem_ofLTS (s := [askInst]) h trivial,
      fun h => mem_ll h⟩
  refine e.trans (instSysSeq_ready_traces.trans ?_)
  simp only [← startsReach_iff_startsTo]
  constructor
  · rintro ⟨l₂, hd, -⟩
    obtain ⟨l₁, h₁, h₂⟩ := seqDone_pair_iff.1 hd
    exact ⟨l₁, l₂, h₁, h₂⟩
  · rintro ⟨l₁, l₂, h₁, h₂⟩
    exact ⟨l₂, seqDone_pair_iff.2 ⟨l₁, h₁, h₂⟩, [], rfl, ⟨_, .nil _⟩⟩

end Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup
