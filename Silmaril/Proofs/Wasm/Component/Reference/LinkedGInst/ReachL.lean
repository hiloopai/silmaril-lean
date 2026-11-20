module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Reach
public import Silmaril.Proofs.Wasm.Component.Reference.InstExport
public import Silmaril.Wasm.Component.Reference.LinkedGInst.Defs

/-!
# Programs in focus reaching their results by live runs

`ReachL th p m Q` is `Reach` of `LinkedGInit` whose run is a live run of unique steps (`LRun`):
from `m` (not locked down), the program `p` in focus, under any continuation, segments and rest
of the control chain, runs by an `LRun` (without host events or traps) to `f a` at `m'` (not
locked down) with `Q os a m'`.

* `liveDet_lrun`, `lrun_liveDet`: the public `LiveDet` is `LRun`;
* `ReachL.pure`, `bind`, `bind_eq`, `mono`, `toReach`: the monad laws, and `ReachL` is a `Reach`;
* `ReachL.ofRunsQ`, `ofSRuns`, `ofTRuns`, `call`, `callItems`, the folds: as for `Reach`, from
  `RunsQ.lrun`;
* `reach_initU`: R4 with the read-back (`RefData.InitU`) is a `ReachL` of the late-bound call
  `Call.instantiate ⟨e.ref, outer⟩ []`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {D : Call E → P E σ (Ret E)}

/-! ## `LiveDet` is `LRun` -/

theorem liveDet_lrun {m m₂ : Config E σ} {tr : List (Label E σ)}
    (h : LiveDet prof hr D m tr m₂) : LRun prof hr D m tr m₂ := by
  induction h with
  | refl => exact .refl _
  | cons hc hl s hu _ ih => exact .cons ⟨hc, hl⟩ ⟨s, hu⟩ ih

theorem lrun_liveDet {m m₂ : Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr D m tr m₂) : LiveDet prof hr D m tr m₂ := by
  induction h with
  | refl => exact .refl _
  | cons hl s _ ih => exact .cons hl.1 hl.2 s.1 s.2 ih

/-! ## Live reaches -/

variable (prof hr D) in
/-- **The program `p` in focus reaches a result satisfying `Q` by a live run**, in any
context. -/
def ReachL {α : Type} (th : Option ThreadId) (p : P E σ α) (m : Config E σ)
    (Q : List HostObs → α → Config E σ → Prop) : Prop :=
  m.store.lockdown = false →
  ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
    ∃ (tr : List (Label E σ)) (a : α) (m' : Config E σ),
      LRun prof hr D { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ m'.store.lockdown = false ∧
      Q (traceObs tr) a m'

namespace ReachL

variable {th : Option ThreadId}

theorem toReach {α : Type} {p : P E σ α} {m : Config E σ}
    {Q : List HostObs → α → Config E σ → Prop} (h : ReachL prof hr D th p m Q) :
    Reach prof hr D th p m Q := by
  intro hl f segs rest
  obtain ⟨tr, a, m', s, h₁, h₂, hl', hq⟩ := h hl f segs rest
  exact ⟨tr, a, m', s.steps, h₁, h₂, hl', hq⟩

theorem mono {α : Type} {p : P E σ α} {m : Config E σ}
    {Q Q' : List HostObs → α → Config E σ → Prop} (h : ReachL prof hr D th p m Q)
    (hQ : ∀ os a m', Q os a m' → Q' os a m') : ReachL prof hr D th p m Q' := by
  intro hl f segs rest
  obtain ⟨tr, a, m', s, h₁, h₂, hl', hq⟩ := h hl f segs rest
  exact ⟨tr, a, m', s, h₁, h₂, hl', hQ _ a m' hq⟩

theorem pure {α : Type} (a : α) (m : Config E σ) :
    ReachL prof hr D th (Pure.pure a : P E σ α) m (fun os b m' => os = [] ∧ b = a ∧ m' = m) := by
  intro hl f segs rest
  refine ⟨[], a, m, ?_, fun _ h => (nomatch h), fun _ h => (nomatch h), hl, rfl, rfl, rfl⟩
  rw [pure_bind]
  exact .refl _

theorem pure_of {α : Type} {a : α} {m : Config E σ}
    {R : List HostObs → α → Config E σ → Prop} (h : R [] a m) :
    ReachL prof hr D th (Pure.pure a : P E σ α) m R :=
  (pure a m).mono fun _ _ _ ⟨e₁, e₂, e₃⟩ => by subst e₁ e₂ e₃; exact h

theorem bind {α β : Type} {p : P E σ α} {g : α → P E σ β} {m : Config E σ}
    {Q : List HostObs → α → Config E σ → Prop} {R : List HostObs → β → Config E σ → Prop}
    (h₁ : ReachL prof hr D th p m Q)
    (h₂ : ∀ os a m', Q os a m' →
      ReachL prof hr D th (g a) m' (fun os' b m'' => R (os ++ os') b m'')) :
    ReachL prof hr D th (p >>= g) m R := by
  intro hl f segs rest
  obtain ⟨tr₁, a, m₁, s₁, h₁h, h₁t, hl₁, hQ⟩ := h₁ hl (fun a => g a >>= f) segs rest
  obtain ⟨tr₂, b, m₂, s₂, h₂h, h₂t, hl₂, hR⟩ := h₂ _ a m₁ hQ hl₁ f segs rest
  refine ⟨tr₁ ++ tr₂, b, m₂, ?_, fun ev h => ?_, fun r h => ?_, hl₂, ?_⟩
  · rw [bind_assoc]
    exact s₁.trans s₂
  · rcases List.mem_append.1 h with h | h
    · exact h₁h ev h
    · exact h₂h ev h
  · rcases List.mem_append.1 h with h | h
    · exact h₁t r h
    · exact h₂t r h
  · rw [traceObs_append]
    exact hR

theorem bind_eq {α β : Type} {p : P E σ α} {g : α → P E σ β} {m m₁ : Config E σ} {a : α}
    {R : List HostObs → β → Config E σ → Prop}
    (h₁ : ReachL prof hr D th p m (fun os b m' => os = [] ∧ b = a ∧ m' = m₁))
    (h₂ : ReachL prof hr D th (g a) m₁ R) : ReachL prof hr D th (p >>= g) m R := by
  refine bind h₁ fun os b m' ⟨e₁, e₂, e₃⟩ => ?_
  subst e₁ e₂ e₃
  exact h₂.mono fun _ _ _ h => by rwa [List.nil_append]

theorem of_eq {γ : Type} {p q : P E σ γ} {m : Config E σ}
    {Q : List HostObs → γ → Config E σ → Prop} (e : p = q)
    (h : ReachL prof hr D th q m Q) : ReachL prof hr D th p m Q := e ▸ h

theorem ofRunsQ {α : Type} {p : P E σ α} {m m' : Config E σ} {tr : List (Label E σ)} {a : α}
    (h : RunsQ D th p m tr a m') :
    ReachL prof hr D th p m (fun os b m'' => os = traceObs tr ∧ b = a ∧ m'' = m') := by
  intro hl f segs rest
  have q := noHost_of_quiet (runsQ_quiet h)
  exact ⟨tr, a, m', h.lrun (prof := prof) (hr := hr) hl f segs rest,
    q.1, q.2, h.lock.trans hl, rfl, rfl, rfl⟩

theorem ofSRuns {α : Type} {p : P E σ α} {m m' : Config E σ} {os : List HostObs} {a : α}
    (h : SRuns p m os a m') :
    ReachL prof hr D th p m (fun os' b m'' => os' = os ∧ b = a ∧ m'' = m') := by
  obtain ⟨tr, hr', ho⟩ := SRuns.runsQO (dispatch := D) h th
  exact (ofRunsQ (prof := prof) (hr := hr) hr').mono fun _ _ _ ⟨e, h⟩ => ⟨e.trans ho, h⟩

theorem ofTRuns {γ : Type} {p : P E σ γ} {m m' : Config E σ} {a : γ}
    (h : TRuns p m a m') :
    ReachL prof hr D th p m (fun os b m'' => os = [] ∧ b = a ∧ m'' = m') :=
  ofSRuns h

theorem call {c : Call E} {m m' : Config E σ} {os : List HostObs} {r : Ret E}
    (h : SRuns (D c) m os r m') :
    ReachL prof hr D th (callRet c : P E σ (Ret E)) m
      (fun os' b m'' => os' = os ∧ b = r ∧ m'' = m') := by
  obtain ⟨tr, hr', ho⟩ := SRuns.runsQO (dispatch := D) h th
  have hc : RunsQ D th (callRet c : P E σ (Ret E)) m (.tau :: (tr ++ [.tau])) r m' := by
    unfold callRet perform Prog.lift
    exact RunsQ.call hr' (RunsQ.pure _ _)
  have e : traceObs (.tau :: (tr ++ [.tau]) : List (Label E σ)) = os := by
    rw [← ho]
    show (Label.tau :: (tr ++ [Label.tau])).filterMap Label.obs? = tr.filterMap Label.obs?
    rw [List.filterMap_cons_none rfl, List.filterMap_append, List.filterMap_cons_none rfl,
      List.filterMap_nil, List.append_nil]
  exact (ofRunsQ (prof := prof) (hr := hr) hc).mono fun _ _ _ ⟨e', h⟩ => ⟨e'.trans e, h⟩

theorem callItems {c : Call E} {m : Config E σ} {Q : List HostObs → Ret E → Config E σ → Prop}
    {R : List HostObs → List (String × Instantiate.ItemVal E) → Config E σ → Prop}
    (h : ReachL prof hr D th (callRet c : P E σ (Ret E)) m Q)
    (hQ : ∀ os r m', Q os r m' → ∃ es, r = .items es ∧ R os es m') :
    ReachL prof hr D th (Canon.callItems c : P E σ _) m R := by
  unfold Canon.callItems
  refine bind h fun os r m' hq => ?_
  obtain ⟨es, rfl, hR⟩ := hQ os r m' hq
  exact (pure es m').mono fun _ _ _ ⟨e₁, e₂, e₃⟩ => by
    subst e₁ e₂ e₃
    rwa [List.append_nil]

variable {α β : Type}

theorem foldlM_append {g : β → α → P E σ β} {b : β} {l l' : List α}
    {m : Config E σ} {Q R : List HostObs → β → Config E σ → Prop}
    (h₁ : ReachL prof hr D th (l.foldlM g b) m Q)
    (h₂ : ∀ os s m', Q os s m' →
      ReachL prof hr D th (l'.foldlM g s) m' (fun os' b' m'' => R (os ++ os') b' m'')) :
    ReachL prof hr D th ((l ++ l').foldlM g b) m R := by
  rw [List.foldlM_append]
  exact bind h₁ h₂

theorem foldlM_cons {g : β → α → P E σ β} {b : β} {x : α} {l : List α}
    {m : Config E σ} {Q R : List HostObs → β → Config E σ → Prop}
    (h₁ : ReachL prof hr D th (g b x) m Q)
    (h₂ : ∀ os s m', Q os s m' →
      ReachL prof hr D th (l.foldlM g s) m' (fun os' b' m'' => R (os ++ os') b' m'')) :
    ReachL prof hr D th ((x :: l).foldlM g b) m R := by
  rw [List.foldlM_cons]
  exact bind h₁ h₂

theorem foldlM_nil {g : β → α → P E σ β} {b : β} {m : Config E σ}
    {R : List HostObs → β → Config E σ → Prop} (h : R [] b m) :
    ReachL prof hr D th (([] : List α).foldlM g b) m R :=
  pure_of h

end ReachL

/-! ## R4 with the read-back as a live reach -/

variable {P : Profile} {impl : HostImpl (core3P P) σ}

/-- **`InitU` implies `InitS`.** -/
theorem initU_initS {e : ExpSpec} {d : e.RefData P} (h : d.InitU) : d.InitS := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, hA, -⟩ :=
    h prof impl M th outer k segs rest hcore hlock
  exact ⟨tr, m, pl, F, es, (liveDet_lrun hs).steps, hh, ht, ho, hc, hA⟩

/-- **`InitU` implies `InitUX`.** -/
theorem initU_initUX {e : ExpSpec} {d : e.RefData P} (h : d.InitU) : d.InitUX := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, hA, hw⟩ :=
    h prof impl M th outer k segs rest hcore hlock
  exact ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, ⟨hA.lock, hA.ext, hA.hold, hA.block, hA.exports,
    hA.pending, hA.results, hA.nest, hA.globals, hA.fidInj⟩, hw⟩

/-- **`InitUX` implies `InitSX`.** -/
theorem initUX_initSX {e : ExpSpec} {d : e.RefData P} (h : d.InitUX) : d.InitSX := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, hA, -⟩ :=
    h prof impl M th outer k segs rest hcore hlock
  exact ⟨tr, m, pl, F, es, (liveDet_lrun hs).steps, hh, ht, ho, hc, hA⟩

/-- **What R4 with the read-back shows of its end**: `InitAtX`, and the waiting threads kept. -/
structure InitW {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (F : CoreFoot)
    (es : List (String × Instantiate.ItemVal (core3P P))) (M m : Machine.Config (core3P P) σ) : Prop
    extends d.InitAtX pl F es M m where
  waiting : m.store.waiting = M.store.waiting

/-- **R4 with the read-back reaches the exporter's exports by a live run**, in any context. -/
theorem reach_initU {e : ExpSpec} {d : e.RefData P} (hI : d.InitUX) (th : Option ThreadId)
    (outer : List (Instantiate.Frame (core3P P))) (M : Machine.Config (core3P P) σ)
    (hcore : M.core = (core3P P).empty _) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (callRet (.instantiate ⟨e.ref, outer⟩ []) : Canon.P (core3P P) σ (Ret (core3P P))) M
      (fun os r m => os = [] ∧ ∃ pl F es, r = .items es ∧ InitW d pl F es M m) := by
  intro hl f segs rest
  obtain ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, hA, hw⟩ :=
    hI prof impl M th outer f segs rest hcore hl
  have hm : { m with ctl := ⟨th, .prog (f (.items es)), segs⟩ :: rest } = m := by rw [← hc]
  refine ⟨tr, .items es, m, ?_, hh, ht, hA.lock, ho, pl, F, es, rfl, ⟨hA, hw⟩⟩
  rw [hm]
  exact liveDet_lrun hs

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst
