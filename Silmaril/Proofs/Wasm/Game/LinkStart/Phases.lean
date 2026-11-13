module

public import Silmaril.Proofs.Wasm.Game.LinkStart.Traces
public import Silmaril.Proofs.Wasm.Game.Linking.StartShared

/-!
# The start phases of a link in the three worlds

For a link with start functions (`StartSetup`) and every profile `P`, the start phase of
each input runs alike in the separated world (provider store, consumer store with stubs),
the shared world and the linked world, in Option form (`startThread o`, a start function or
none):

* `prov_fwd`, `prov_back`, `prov_fail_fwd`, `prov_fail_back`: the provider's start phase,
  provider world ↔ shared world (`Split.prov_start_fwd`, `Split.prov_start_back`);
* `cons_fwd`, `cons_back`: the consumer's start phase, consumer world with the provider
  answering its stub calls ↔ shared world (`Split.LRun.sup`, `Split.cons_start_back`);
* `link_fwd`, `link_back`: shared world ↔ linked world (`Setup.start_transfer`,
  `Setup.start_reflect`);
* list facts about lifted moves and the split of a closed provider's play at the end of a
  run of stub calls (`provider_split`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStart

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
  Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Proofs.Wasm.Game.Start
  Silmaril.Proofs.Wasm.Game.Linking.Split Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

/-! ## Lists of lifted moves -/

section Lists

variable {E F : Sig.{0}} {R : Type}

theorem lower_map_liftL (l : List (Ev E)) :
    lower (l.map (InstSystem.liftL (F := F) (R := R)) : List (Move (E.withInst R) (F.withInst R))) =
      l.map liftEv := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [InstSystem.liftL, ih]

theorem upper_map_liftL (l : List (Ev E)) :
    upper (l.map (InstSystem.liftL (F := F) (R := R)) : List (Move (E.withInst R) (F.withInst R))) =
      [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [InstSystem.liftL, ih]

theorem lower_map_liftC (p : List (Move E F)) :
    lower (p.map (liftC (R := R))) = (lower p).map liftEv := by
  induction p with
  | nil => rfl
  | cons m p ih => rcases m with a | b <;> simpa [liftC] using ih

theorem upper_map_liftC (p : List (Move E F)) :
    upper (p.map (liftC (R := R))) = (upper p).map liftEv := by
  induction p with
  | nil => rfl
  | cons m p ih => rcases m with a | b <;> simpa [liftC] using ih

theorem map_liftMove_inr (l : List (Ev F)) :
    ((l.map .inr : List (Move E F)).map (liftMove (R := R))) = (l.map liftEv).map .inr := by
  simp [liftMove, Function.comp_def]

/-- A list of upper moves relabelled by `liftMove` determines the list. -/
theorem eq_map_inr_of_liftMove {q : List (Move E F)} {l : List (Ev F)}
    (h : q.map (liftMove (R := R)) = (l.map liftEv).map .inr) : q = l.map .inr := by
  rw [← map_liftMove_inr] at h
  exact List.map_injective_iff.2 (upperMap_injective liftEv_injective) h

end Lists

/-! ## Closed instances -/

section Closed

variable {I : ScalarInstance} {P : Profile}

/-- The plays of a closed instance relabelled by `liftMove`. -/
theorem closed_map_liftMove (hI : I.imports = []) (q : List (Move I.E I.F)) {R : Type} :
    q.map (liftMove (R := R)) = ((upper q).map liftEv).map .inr := by
  rw [← map_liftMove_inr, ← Silmaril.Proofs.Wasm.Game.ScalarInstance.eq_map_upper hI q]

end Closed

/-- A run of the finished empty thread stops nowhere. -/
theorem lrun_finished {I : ScalarInstance} {P : Profile} {s : Store Nat}
    {l : List (Ev I.E)} {y : Store Nat × Thread} (h : LRun I P (s, .active {} []) l y) :
    l = [] ∧ y = (s, .active {} []) := by
  cases h with
  | done hr => exact ⟨rfl, reach_finished hr⟩
  | @call x y s₁ t₁ h args e w l' hr hco _ _ =>
    obtain ⟨E, a, hd⟩ := hco
    obtain ⟨hs, ht⟩ := Prod.mk.inj (reach_finished hr)
    have hnone : decompose? s₁ (t₁.config s₁).code = none := by
      rw [ht]
      exact Silmaril.Proofs.Wasm.Game.ScalarInstance.decompose?_toAdmin s₁ (.values [])
    rw [hnone] at hd
    cases hd

namespace StartSetup

variable (S : StartSetup) {P : Profile}

/-- The conclusion of `provider_split`. -/
def SplitAt (π : Store Nat) (pp : List (Move S.providerI.E S.providerI.F)) (q : S.providerI.HState)
    (l L : List (Ev S.consumerI.E)) : Prop :=
  ∃ π' pp₁ pp₂, pp = pp₁ ++ pp₂ ∧ S.providerI.Path P (.idle π) pp₁ (.idle π') ∧
    upper pp₁ = l ∧ S.providerI.Path P (.idle π') pp₂ q ∧ upper pp₂ = L

/-- One step of `provider_split`: a complete activation, then the rest. -/
theorem provider_split_call {π : Store Nat} {pp : List (Move S.providerI.E S.providerI.F)}
    {q : S.providerI.HState} {e : S.consumerI.E.Op} {w : S.consumerI.E.Ar e}
    {l L : List (Ev S.consumerI.E)} (hp : S.providerI.Path P (.idle π) pp q)
    (hu : upper pp = (.ask e :: .ans e w :: (l ++ L) : List (Ev S.consumerI.E)))
    (ih : ∀ {π : Store Nat} {pp : List (Move S.providerI.E S.providerI.F)}
      {q : S.providerI.HState}, S.providerI.Path P (.idle π) pp q →
        upper pp = (l ++ L : List (Ev S.consumerI.E)) → SplitAt S (P := P) π pp q l L) :
    SplitAt S (P := P) π pp q (.ask e :: .ans e w :: l) L := by
  match pp, hp, hu with
  | [], _, hu => cases hu
  | [m], hp, hu =>
    obtain ⟨f, rfl, -⟩ := path_idle_cons hp
    exact absurd (List.cons.inj (hu : [Ev.ask f] = _)).2 (List.cons_ne_nil _ _).symm
  | m :: n :: rest, hp, hu =>
    obtain ⟨f, v, π₁, rfl, rfl, hc, hrest⟩ :=
      ScalarInstance.path_cons_cons_closed (I := S.providerI) rfl hp
    have hu' : (Ev.ask f :: Ev.ans f v :: upper rest : List (Ev S.providerI.F)) =
        Ev.ask e :: Ev.ans e w :: (l ++ L) := hu
    obtain ⟨h₁, hu₂⟩ := List.cons.inj hu'
    obtain ⟨h₂, hu₃⟩ := List.cons.inj hu₂
    obtain ⟨π', pp₁, pp₂, rfl, hp₁, hu₁, hp₂, hL⟩ := ih hrest hu₃
    refine ⟨π', .inr (.ask f) :: .inr (.ans f v) :: pp₁, pp₂, rfl, path_append hc hp₁, ?_, hp₂, hL⟩
    show Ev.ask f :: Ev.ans f v :: upper pp₁ = _
    rw [h₁, h₂, hu₁]
    rfl

/-- **The provider's play splits after the consumer's run of stub calls.** -/
theorem provider_split {x y : Store Nat × Thread} {l : List (Ev S.consumerI.E)}
    (hl : LRun S.consumerI P x l y) :
    ∀ {π : Store Nat} {pp : List (Move S.providerI.E S.providerI.F)} {q : S.providerI.HState}
      {L : List (Ev S.consumerI.E)},
      S.providerI.Path P (.idle π) pp q → upper pp = (l ++ L : List (Ev S.consumerI.E)) →
      ∃ π' pp₁ pp₂, pp = pp₁ ++ pp₂ ∧ S.providerI.Path P (.idle π) pp₁ (.idle π') ∧
        upper pp₁ = l ∧ S.providerI.Path P (.idle π') pp₂ q ∧ upper pp₂ = L := by
  induction hl with
  | done _ =>
    intro π pp q L hp hu
    exact ⟨π, [], pp, rfl, .nil _, rfl, hp, hu⟩
  | call run callout op _ ih =>
    intro π pp q L hp hu
    exact provider_split_call S hp hu ih

/-! ### Typing of the start functions in the shared world -/

theorem startTyped_sc_of_sp {a : Nat} (h : StartTyped S.sp a) : StartTyped S.sc a := by
  obtain ⟨fi, hfi, hty⟩ := h
  have C := once_facts S.assembly.consumerProfile S.sharedInst
  exact ⟨fi, prefix_getElem? C.funcs_prefix hfi, hty⟩

theorem startTyped_sc_of_scs {a : Nat} (h : StartTyped S.scs a) : StartTyped S.sc a := by
  obtain ⟨fi, hfi, hty⟩ := h
  have hfi' : (S.sc.funcs[a]?.map fun fi =>
      if S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs then
        { fi with code := .host (S.stubs.idxOf (a - S.base.funcs.length)) } else fi) = some fi := by
    rw [← stubOut_funcs, ← S.scs_eq_stubOut]
    exact hfi
  obtain ⟨fi₀, h₀, hfi₀⟩ := Option.map_eq_some_iff.mp hfi'
  refine ⟨fi₀, h₀, ?_⟩
  by_cases hst : S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs
  · have e : fi.type = fi₀.type := by rw [← hfi₀]; simp only [hst, and_self, ite_true]
    exact e ▸ hty
  · have e : fi.type = fi₀.type := by rw [← hfi₀]; simp only [hst, ite_false]
    exact e ▸ hty

/-- The provider's start function is the provider's. -/
theorem provStart_own (St : Static S.toSetup) (hOp : St.Op = S.provOwn) :
    ∀ a ∈ S.provStart, St.Op.fn a := by
  intro a ha
  rw [hOp]
  exact S.provStartFunc a ha

/-- The consumer's start function is the consumer's (a consumer function or a stub). -/
theorem consStart_own (St : Static S.toSetup) (hOc : St.Oc = S.consOwn) :
    ∀ a ∈ S.consStart, St.Oc.fn a := by
  intro a ha
  rw [hOc]
  left
  rw [← S.fcs_eq_fc]
  exact S.consStartFunc a ha

/-! ### The provider's start phase: provider world ↔ shared world -/

variable {St : Static S.toSetup}

theorem prov_fwd {σ π κ π₁ : Store Nat} (hI : Idle St σ π κ) {o : Option Nat}
    (hown : ∀ a ∈ o, St.Op.fn a) (h : StartsReach P π o π₁) :
    ∃ σ₁, StartsReach P σ o σ₁ ∧ Idle St σ₁ π₁ κ := by
  cases o with
  | none =>
    obtain rfl := startsReach_none.1 h
    exact ⟨σ, startsReach_none.2 rfl, hI⟩
  | some a =>
    obtain ⟨t', run, final⟩ := h
    obtain ⟨σ', ts', hr, hres, hI'⟩ :=
      prov_start_fwd (hI.startProv (hown a rfl)) (.inl rfl) run final
    exact ⟨σ', ⟨ts', hr, hres⟩, hI'⟩

theorem result_of_startFailed {c : Store Nat × Thread} {b : Behaviour Val}
    (h : StartFailed c b) : ∃ r, ResultAt c.1 c.2 r ∧ (r = .values [] ∨ r = .trap ∨ ∃ a, r = .throw a) ∧
      ∀ {c' : Store Nat × Thread}, ResultAt c'.1 c'.2 r → StartFailed c' b := by
  rcases h with ⟨h, rfl⟩ | ⟨a, h, rfl⟩
  · exact ⟨.trap, h, .inr (.inl rfl), fun h' => .inl ⟨h', rfl⟩⟩
  · exact ⟨.throw a, h, .inr (.inr ⟨a, rfl⟩), fun h' => .inr ⟨a, h', rfl⟩⟩

theorem prov_fail_fwd {σ π κ : Store Nat} (hI : Idle St σ π κ) {o : Option Nat}
    (hown : ∀ a ∈ o, St.Op.fn a) {b : Behaviour Val} (h : StartFails P π o b) :
    StartFails P σ o b := by
  cases o with
  | none => exact absurd h not_startFails_none
  | some a =>
    obtain ⟨⟨π', tp'⟩, run, hf⟩ := h
    obtain ⟨r, final, hr, hback⟩ := result_of_startFailed hf
    obtain ⟨σ', ts', hrun, hres, -⟩ := prov_start_fwd (hI.startProv (hown a rfl)) hr run final
    exact ⟨(σ', ts'), hrun, hback hres⟩

theorem prov_back (hS : S.Scalar) {σ π κ σ₁ : Store Nat} (hI : IdleT St σ π κ) {o : Option Nat}
    (hown : ∀ a ∈ o, St.Op.fn a) (hty : ∀ a ∈ o, StartTyped π a) (h : StartsReach P σ o σ₁) :
    ∃ π₁, StartsReach P π o π₁ ∧ IdleT St σ₁ π₁ κ := by
  cases o with
  | none =>
    obtain rfl := startsReach_none.1 h
    exact ⟨π, startsReach_none.2 rfl, hI⟩
  | some a =>
    obtain ⟨ts', run, final⟩ := h
    obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI.1
    have hwp : S.providerI.WellFormed π := hS.provider.of_funcs hI.2.1 hW.fπ
    have htp : ThreadOk π (.pending a []) (resC startType) := start_typed hwp (hty a rfl)
    obtain ⟨π', tp', hr, hres, hI'⟩ :=
      prov_start_back St P final (σ, .pending a []) run (hI.1.startProv (hown a rfl)) htp
    have hπ' : StoreOk π' := (reachableP_typed (P := P) hr hI.2.1 htp).1
    exact ⟨π', ⟨tp', hr, hres⟩, hI', hπ', hI.2.2⟩

theorem prov_fail_back (hS : S.Scalar) {σ π κ : Store Nat} (hI : IdleT St σ π κ)
    {o : Option Nat} (hown : ∀ a ∈ o, St.Op.fn a) (hty : ∀ a ∈ o, StartTyped π a)
    {b : Behaviour Val} (h : StartFails P σ o b) : StartFails P π o b := by
  cases o with
  | none => exact absurd h not_startFails_none
  | some a =>
    obtain ⟨⟨σ', ts'⟩, run, hf⟩ := h
    obtain ⟨r, final, -, hback⟩ := result_of_startFailed hf
    obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI.1
    have hwp : S.providerI.WellFormed π := hS.provider.of_funcs hI.2.1 hW.fπ
    have htp : ThreadOk π (.pending a []) (resC startType) := start_typed hwp (hty a rfl)
    obtain ⟨π', tp', hr, hres, -⟩ :=
      prov_start_back St P final (σ, .pending a []) run (hI.1.startProv (hown a rfl)) htp
    exact ⟨(π', tp'), hr, hback hres⟩

/-! ### The consumer's start phase: consumer world ↔ shared world -/

theorem exists_startAnswer {r : Result} (hr : r = .values [] ∨ r = .trap ∨ ∃ a, r = .throw a) :
    ∃ v : Answer startType, Answer.ofResult? startType r = some v := by
  rcases hr with rfl | rfl | ⟨a, rfl⟩
  · exact ⟨.values ⟨[], .nil⟩, Answer.ofResult?_toResult (.values ⟨[], .nil⟩)⟩
  · exact ⟨.trap, rfl⟩
  · exact ⟨.throw a, rfl⟩

theorem cons_back (hS : S.Scalar) {σ π κ σf : Store Nat} {tsf : Thread} {rs : Result}
    (hI : IdleT St σ π κ) {o : Option Nat} (hown : ∀ a ∈ o, St.Oc.fn a)
    (hty : ∀ a ∈ o, StartTyped κ a) (run : Reach P (σ, startThread o) (σf, tsf))
    (hfin : ResultAt σf tsf rs) (hrs : rs = .values [] ∨ rs = .trap ∨ ∃ a, rs = .throw a) :
    ∃ (evs : List (Ev S.consumerI.E)) (pp : List (Move S.providerI.E S.providerI.F))
      (κ' π' : Store Nat) (tc' : Thread),
      LRun S.consumerI P (κ, startThread o) evs (κ', tc') ∧ ResultAt κ' tc' rs ∧
      S.providerI.Path P (.idle π) pp (.idle π') ∧ evs = upper pp ∧ IdleT St σf π' κ' := by
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (reach_finished run)
    have hrs' : rs = .values [] := resultAt_unique hfin (r' := .values []) rfl
    subst hrs'
    exact ⟨[], [], κ, π, .active {} [], .done .refl, rfl, .nil _, rfl, hI⟩
  | some a =>
    obtain ⟨v, hv⟩ := exists_startAnswer hrs
    obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI.1
    have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hI.2.2 hW.fκ
    have htc : ThreadOk κ (.pending a []) (resC startType) := start_typed hwc (hty a rfl)
    obtain ⟨evs, pp, κ', π', ⟨tc', r, hl, hres, hans⟩, hpp, hproj, hI'⟩ :=
      cons_start_back St hS P hI (hown a rfl) htc run hfin hv
    have hr : r = rs :=
      (Answer.toResult_of_ofResult? hans).symm.trans (Answer.toResult_of_ofResult? hv)
    exact ⟨evs, pp, κ', π', tc', hl, hr ▸ hres, hpp, hproj, hI'⟩

theorem cons_fwd {σ π κ π' κ' : Store Nat} {tc' : Thread} {r : Result}
    {evs : List (Ev S.consumerI.E)} {pp : List (Move S.providerI.E S.providerI.F)}
    (hI : Idle St σ π κ) {o : Option Nat} (hown : ∀ a ∈ o, St.Oc.fn a)
    (hl : LRun S.consumerI P (κ, startThread o) evs (κ', tc')) (hres : ResultAt κ' tc' r)
    (hr : r = .values [] ∨ r = .trap ∨ ∃ a, r = .throw a)
    (hpp : S.providerI.Path P (.idle π) pp (.idle π')) (hproj : evs = upper pp) :
    ∃ σ' ts', Reach P (σ, startThread o) (σ', ts') ∧ ResultAt σ' ts' r ∧ Idle St σ' π' κ' := by
  cases o with
  | none =>
    obtain ⟨rfl, hy⟩ := lrun_finished hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy
    obtain ⟨-, hq⟩ := provider_path_nil hpp hproj.symm
    cases hq
    exact ⟨σ, .active {} [], .refl, hres, hI⟩
  | some a =>
    obtain ⟨σ', ts', hrun, hR⟩ := LRun.sup St hl (hI.startCons (hown a rfl)) hpp hproj
    obtain ⟨-, ⟨ρ, hres'⟩, hI'⟩ := hR.result hres
    have hρ : ρ.result r = r := ren_start_result hr
    exact ⟨σ', ts', hrun, hρ ▸ hres', hI'⟩

/-! ### Start phases: shared world ↔ linked world -/

theorem link_fwd {σ l σ₁ : Store Nat} {t₁ : Thread} {r : Result} (hp : S.Persistent σ l)
    {o : Option Nat} (hty : ∀ a ∈ o, StartTyped σ a) (run : Reach P (σ, startThread o) (σ₁, t₁))
    (hres : ResultAt σ₁ t₁ r) :
    ∃ l₁ t₁', Reach P (l, startThread o) (l₁, t₁') ∧ ResultAt l₁ t₁' r ∧ S.Persistent σ₁ l₁ := by
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (reach_finished run)
    exact ⟨l, .active {} [], .refl, hres, hp⟩
  | some a => exact S.start_transfer hp (hty a rfl) run hres

theorem link_back {σ l l₁ : Store Nat} {t₁ : Thread} {r : Result} (hp : S.Persistent σ l)
    {o : Option Nat} (hty : ∀ a ∈ o, StartTyped σ a) (run : Reach P (l, startThread o) (l₁, t₁))
    (hres : ResultAt l₁ t₁ r) :
    ∃ σ₁ t₁', Reach P (σ, startThread o) (σ₁, t₁') ∧ ResultAt σ₁ t₁' r ∧ S.Persistent σ₁ l₁ := by
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (reach_finished run)
    exact ⟨σ, .active {} [], .refl, hres, hp⟩
  | some a => exact S.start_reflect hp (hty a rfl) run hres

theorem link_reach_fwd {σ l σ₁ : Store Nat} (hp : S.Persistent σ l) {o : Option Nat}
    (hty : ∀ a ∈ o, StartTyped σ a) (h : StartsReach P σ o σ₁) :
    ∃ l₁, StartsReach P l o l₁ ∧ S.Persistent σ₁ l₁ := by
  obtain ⟨t₁, run, hres⟩ := h
  obtain ⟨l₁, t₁', hr, hres', hp'⟩ := link_fwd S hp hty run hres
  exact ⟨l₁, ⟨t₁', hr, hres'⟩, hp'⟩

theorem link_reach_back {σ l l₁ : Store Nat} (hp : S.Persistent σ l) {o : Option Nat}
    (hty : ∀ a ∈ o, StartTyped σ a) (h : StartsReach P l o l₁) :
    ∃ σ₁, StartsReach P σ o σ₁ ∧ S.Persistent σ₁ l₁ := by
  obtain ⟨t₁, run, hres⟩ := h
  obtain ⟨σ₁, t₁', hr, hres', hp'⟩ := link_back S hp hty run hres
  exact ⟨σ₁, ⟨t₁', hr, hres'⟩, hp'⟩

theorem link_fail_fwd {σ l : Store Nat} (hp : S.Persistent σ l) {o : Option Nat}
    (hty : ∀ a ∈ o, StartTyped σ a) {b : Behaviour Val} (h : StartFails P σ o b) :
    StartFails P l o b := by
  obtain ⟨⟨σ₁, t₁⟩, run, hf⟩ := h
  obtain ⟨r, final, -, hback⟩ := result_of_startFailed hf
  obtain ⟨l₁, t₁', hr, hres', -⟩ := link_fwd S hp hty run final
  exact ⟨(l₁, t₁'), hr, hback hres'⟩

theorem link_fail_back {σ l : Store Nat} (hp : S.Persistent σ l) {o : Option Nat}
    (hty : ∀ a ∈ o, StartTyped σ a) {b : Behaviour Val} (h : StartFails P l o b) :
    StartFails P σ o b := by
  obtain ⟨⟨l₁, t₁⟩, run, hf⟩ := h
  obtain ⟨r, final, -, hback⟩ := result_of_startFailed hf
  obtain ⟨σ₁, t₁', hr, hres', -⟩ := link_back S hp hty run final
  exact ⟨(σ₁, t₁'), hr, hback hres'⟩

end StartSetup

end Silmaril.Proofs.Wasm.Game.LinkStart
