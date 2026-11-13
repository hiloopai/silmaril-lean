module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCallout

/-!
# Segmented runs of the importer's core phase with nested calls

The importer's core activation of a `Linked2` runs in the shared core store, in segments:
host-free core runs separated by callouts to the trampolines of the exporter's lifted functions,
each answered by a nested call (`nest_at`): a host-free run of the exporter's core activation
from the importer's store at the callout, returning flat values that lift, whose lowered
results resume the importer.

* `LSeg B x recs z`: such a segmented run from `x` to `z`, the nested calls recorded (`LRec`);
* `LinkOk B x`: every callout reachable along `LSeg` is to a trampoline of the exporter at the
  IR types, and the exporter's runs from it never call out and return values of the result types
  (to be discharged by the split of the shared store);
* `lsegs_inv`: every machine run from the importer's activation, in any frame `extN B ιe N C`
  with a reusable thread table of the exporter, that ends where a call outcome holds is a
  segmented run followed by an exit of the importer's core phase, or traps: at a callout whose
  arguments do not lift, at a trap of the exporter's core activation, or where the exporter's
  results do not lift.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Outcomes after a trap -/

/-- A call outcome holding at a trapped configuration is the trap. -/
theorem holds_trapCfgD {m : Machine.Config (E3 P) σ} {out : CallOutcome} {cid : CallId}
    (ho : out.Holds (fun _ _ => false) cid (trapCfg m)) : out = .trap := by
  cases out with
  | resolved r => exact absurd ho.2.1 (by simp)
  | trap => rfl
  | deadlock => exact absurd ho.1.2.1 (by simp)

/-- A run from a configuration that traps, ending where a call outcome holds, ends in the
trap. -/
theorem TrapsFrom.out {M m' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {out : CallOutcome} {cid : CallId} (hT : TrapsFrom prof P impl M)
    (r : Steps prof (fun _ _ => false) (DI P impl) M tr m')
    (ho : out.Holds (fun _ _ => false) cid m') : out = .trap := by
  obtain ⟨tr₁, mT, rT, hrun, hlive, hu⟩ := hT
  rcases hrun.inv r with hl' | ⟨tr'', -, r''⟩
  · exact absurd ho (hl'.not_holds _ _)
  cases r'' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s' r''' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s'
    rw [steps_of_locked rfl rfl r'''] at ho
    exact holds_trapCfgD ho

theorem TrapsNextD.trapsFrom {M : Machine.Config (E3 P) σ} (h : TrapsNextD prof P impl M) :
    TrapsFrom prof P impl M := by
  obtain ⟨mT, r, h₁, h₂, h₃⟩ := h
  exact ⟨_, mT, r, h₁, h₂, h₃⟩

/-! ## Segmented runs -/

/-- A recorded nested call: the exporter's lifted function `f` (core address `a`, type `p`), the
importer's flat arguments `ys` lifted to `ws`, the importer's thread `y` at the callout, the
exporter's core activation's end `e` with flat results `zs` lifted to `us`. -/
structure LRec (P : Profile) where
  f : FuncId
  a : (E3 P).FuncAddr
  p : Silmaril.Wasm.Component.FuncTy
  ys : List Flat
  ws : List Silmaril.Wasm.Component.Val
  y : CoreSt (E3 P)
  e : CoreSt (E3 P)
  zs : List Flat
  us : List Silmaril.Wasm.Component.Val

/-- **A segmented run of the importer's core phase with nested calls**, the component
functions those of `B`. -/
inductive LSeg (B : Machine.Config (E3 P) σ) : CoreSt (E3 P) → List (LRec P) → CoreSt (E3 P) →
    Prop
  | done {x y : CoreSt (E3 P)} : Relation.ReflTransGen (CoreStep (E3 P)) x y → LSeg B x [] y
  | call {x y e z : CoreSt (E3 P)} {f : FuncId} {a : (E3 P).FuncAddr}
      {p : Silmaril.Wasm.Component.FuncTy} {ys zs : List Flat} {ws us : List Silmaril.Wasm.Component.Val}
      {rest : List (LRec P)} :
      Relation.ReflTransGen (CoreStep (E3 P)) x y →
      (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys →
      ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩) →
      p.results.length ≤ 1 → liftArgs p.params ys = some ws →
      Relation.ReflTransGen (CoreStep (E3 P))
        (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e →
      (E3 P).status e.1 e.2 = .returned (.values zs) → liftArgs p.results zs = some us →
      LSeg B (e.1, (E3 P).resume e.1 y.2 (.values (lowerArgs p.results us))) rest z →
      LSeg B x (⟨f, a, p, ys, ws, y, e, zs, us⟩ :: rest) z

/-- The callout `h ys` from `y` is to a trampoline of a lifted function of the exporter at IR
types within the flat arities, from whose lowered arguments the exporter's core runs never call
out and return flat values of the result types. -/
structure LinkSite (B : Machine.Config (E3 P) σ) (y : CoreSt (E3 P)) (h : CanonHost (E3 P))
    (ys : List Flat) : Prop where
  site : ∃ (f : FuncId) (a : (E3 P).FuncAddr) (p : Silmaril.Wasm.Component.FuncTy),
    h = .lowered f (witFt p) {} ⟨2⟩ ∧
    ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩) ∧
    floatFreeList p.params = true ∧ ys.map (·.type) = ValTy.flatList p.params ∧
    (ValTy.flatList p.params).length ≤ 16 ∧ p.results.length ≤ 1 ∧
    floatFreeList p.results = true ∧ (ValTy.flatList p.results).length ≤ 1 ∧
    ∀ ws, liftArgs p.params ys = some ws → ∀ e,
      Relation.ReflTransGen (CoreStep (E3 P))
        (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e →
      (∀ h' ys', (E3 P).status e.1 e.2 ≠ .callout h' ys') ∧
      ∀ zs, (E3 P).status e.1 e.2 = .returned (.values zs) →
        zs.map (·.type) = ValTy.flatList p.results

/-- Every callout reachable from `x` along segmented runs is a `LinkSite`. -/
def LinkOk (B : Machine.Config (E3 P) σ) (x : CoreSt (E3 P)) : Prop :=
  ∀ recs y h ys, LSeg B x recs y → (E3 P).status y.1 y.2 = .callout h ys → LinkSite B y h ys

theorem LinkOk.after {B : Machine.Config (E3 P) σ} {x y e : CoreSt (E3 P)} {f : FuncId}
    {a : (E3 P).FuncAddr} {p : Silmaril.Wasm.Component.FuncTy} {ys zs : List Flat}
    {ws us : List Silmaril.Wasm.Component.Val} (hk : LinkOk B x)
    (hy : Relation.ReflTransGen (CoreStep (E3 P)) x y)
    (hs : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) (hws : liftArgs p.params ys = some ws)
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e)
    (hst : (E3 P).status e.1 e.2 = .returned (.values zs)) (hus : liftArgs p.results zs = some us) :
    LinkOk B (e.1, (E3 P).resume e.1 y.2 (.values (lowerArgs p.results us))) :=
  fun _ _ _ _ hz hs' => hk _ _ _ _ (.call hy hs hf hr hws he hst hus hz) hs'

/-! ## The frame -/

/-- The static facts of the importer's frame `B` for thread `th`: callouts of instance `2` pass
the entry check in every extension of `B`, instance `2` may leave. -/
structure LFrame (B : Machine.Config (E3 P) σ) (th : Option ThreadId) : Prop where
  entry : ∀ f ft ιe (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))),
    calloutEntry (extN B ιe N C).store th (.lowered f ft {} ⟨2⟩) = none
  inst : ∃ ιi, B.store.insts[2]? = some ιi ∧ ιi.mayLeave = true

theorem LFrame.inst2 {B : Machine.Config (E3 P) σ} {th : Option ThreadId} (hB : LFrame B th)
    (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))) :
    ∃ ιi, ArenaField.insts.get? (extN B ιe N C).store ⟨2⟩ = some ιi ∧ ιi.mayLeave = true := by
  obtain ⟨ιi, h, hl⟩ := hB.inst
  refine ⟨ιi, ?_, hl⟩
  exact (List.getElem?_set_ne (l := B.store.insts) (a := ιe) (show (1 : Nat) ≠ 2 by decide)).trans h

theorem LFrame.len {B : Machine.Config (E3 P) σ} {th : Option ThreadId} (hB : LFrame B th) :
    1 < B.store.insts.length := by
  obtain ⟨ιi, h, -⟩ := hB.inst
  have := (List.getElem?_eq_some_iff.mp h).1
  omega

/-! ## Inversion -/

/-- How a run of the importer's core phase ends where a call outcome holds. -/
def LEnd (B : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (tr : List (Label (E3 P) σ))
    (m' : Machine.Config (E3 P) σ) (out : CallOutcome) : Prop :=
  ∃ recs y, LSeg B x recs y ∧
    ((∃ ιe' N' C' pre l m₁ tr₂, tr = pre ++ tr₂ ∧ ThreadsOk ιe' ∧
        (∀ h ys, (E3 P).status y.1 y.2 ≠ .callout h ys) ∧
        CoreExit (extN B ιe' N' C') th K segs rest y l m₁ ∧
        Steps prof (fun _ _ => false) (DI P impl) m₁ tr₂ m') ∨
      (∃ f a p ys, (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys ∧
        ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩) ∧
        p.results.length ≤ 1 ∧ out = .trap ∧
        (liftArgs p.params ys = none ∨
          ∃ ws e, liftArgs p.params ys = some ws ∧
            Relation.ReflTransGen (CoreStep (E3 P))
              (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e ∧
            ((E3 P).status e.1 e.2 = .returned .trap ∨
              ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧
                liftArgs p.results zs = none))))

theorem lend_cons {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x y e : CoreSt (E3 P)} {f : FuncId}
    {a : (E3 P).FuncAddr} {p : Silmaril.Wasm.Component.FuncTy} {ys zs : List Flat}
    {ws us : List Silmaril.Wasm.Component.Val} {pre tr'' : List (Label (E3 P) σ)}
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hy : Relation.ReflTransGen (CoreStep (E3 P)) x y)
    (hs : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) (hws : liftArgs p.params ys = some ws)
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e)
    (hst : (E3 P).status e.1 e.2 = .returned (.values zs)) (hus : liftArgs p.results zs = some us)
    (ih : LEnd (prof := prof) (impl := impl) B th K segs rest
      (e.1, (E3 P).resume e.1 y.2 (.values (lowerArgs p.results us))) tr'' m' out) :
    LEnd (prof := prof) (impl := impl) B th K segs rest x (pre ++ tr'') m' out := by
  obtain ⟨recs, z, hz, hend⟩ := ih
  refine ⟨_, z, .call hy hs hf hr hws he hst hus hz, ?_⟩
  rcases hend with ⟨ιe', N', C', pre', l, m₁, tr₂, rfl, ht, hco, hx, r⟩ | hT
  · exact .inl ⟨ιe', N', C', pre ++ pre', l, m₁, tr₂, by rw [List.append_assoc], ht, hco, hx, r⟩
  · exact .inr hT

theorem coreCfg_extN_live (B : Machine.Config (E3 P) σ) (ιe : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) :
    Live (coreCfg (extN B ιe N C) th K segs rest x) :=
  ⟨List.cons_ne_nil _ _, rfl⟩

/-- **Inversion of the importer's core phase with nested calls.** -/
theorem lsegs_inv {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {cid : CallId} (hB : LFrame B th) :
    ∀ (n : Nat) (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
      (x : CoreSt (E3 P)) (tr : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ)
      (out : CallOutcome),
      tr.length ≤ n → ThreadsOk ιe → LinkOk B x →
      Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x) tr m' →
      out.Holds (fun _ _ => false) cid m' →
      LEnd (prof := prof) (impl := impl) B th K segs rest x tr m' out := by
  intro n
  induction n with
  | zero =>
    intro ιe N C x tr m' out hn _ _ hs ho
    have htr : tr = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst htr
    cases hs
    exact absurd ho ((coreCfg_extN_live B ιe N C th K segs rest x).not_holds _ _)
  | succ n ih =>
    intro ιe N C x tr m' out hn hte hk hs ho
    rcases coreCfg_steps_inv' hs with ⟨y, -, rfl⟩ | ⟨y, pre, l, m₁, tr₂, hy, rfl, st, hx, r⟩
    · exact absurd ho ((coreCfg_extN_live B ιe N C th K segs rest y).not_holds _ _)
    by_cases hco : ∃ h ys, (E3 P).status y.1 y.2 = .callout h ys
    swap
    · exact ⟨[], y, .done hy, .inl ⟨ιe, N, C, pre ++ [l], l, m₁, tr₂, by simp, hte,
        fun h ys e => hco ⟨h, ys, e⟩, hx, r⟩⟩
    obtain ⟨h, ys, hst⟩ := hco
    obtain ⟨f, a, p, rfl, hf, hpf, hys, hmaxp, hres, hrf, hmaxr, hexp⟩ :=
      (hk [] y h ys (.done hy) hst).site
    have r' : Steps prof (fun _ _ => false) (DI P impl)
        (coreCfg (extN B ιe N C) th K segs rest y) (l :: tr₂) m' := .cons st r
    obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
    have hadd := addThread?_ok hte ⟨(extN B ιe N C).store.threads.length⟩
    have hrem := removeThread?_enter ιe ⟨(extN B ιe N C).store.threads.length⟩
    cases hws : liftArgs p.params ys with
    | none =>
      have hT := nest_trap_args (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys
        ιi hst (hB.entry _ _ _ _ _) hi hleave hf hB.len hadd hpf hys hmaxp hws
      exact ⟨[], y, .done hy, .inr ⟨f, a, p, ys, hst, hf, hres, hT.out r' ho, .inl hws⟩⟩
    | some ws =>
      obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₁, hrun, hctl, hcore, hlock, hret, htrap⟩ :=
        nest_at (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hst
          (hB.entry _ _ _ _ _) hi hleave hf hB.len hadd hrem hpf hys hmaxp hws hres hrf hmaxr
      rcases hrun.inv r' with hl' | ⟨tr'', e₁, r''⟩
      · exact absurd ho (hl'.not_holds _ _)
      have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y.1,
          Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) := by
        rw [← hcore]
        exact eq_coreCfg hctl
      rw [hM] at r''
      have hlive : ∀ z, Live (coreCfg M₁ th' K' segs' rest' z) :=
        fun z => ⟨List.cons_ne_nil _ _, hlock⟩
      rcases coreCfg_steps_inv' r'' with ⟨e, -, rfl⟩ |
          ⟨e, pre₂, l', m₂, tr₃, he, rfl, -, hx₂, r₃⟩
      · exact absurd ho ((hlive e).not_holds _ _)
      obtain ⟨hnco, hty⟩ := hexp ws hws e he
      rcases hx₂ with ⟨zs, hzs, rfl, rfl⟩ | ⟨htr, rfl, rfl⟩ | ⟨h', ys', hc'⟩
      · cases hus : liftArgs p.results zs with
        | none =>
          have hT := (htrap e zs (hty zs hzs) hus).trapsFrom
          exact ⟨[], y, .done hy, .inr ⟨f, a, p, ys, hst, hf, hres, hT.out r₃ ho,
            .inr ⟨ws, e, hws, he, .inr ⟨zs, hzs, hus⟩⟩⟩⟩
        | some us =>
          obtain ⟨tr₄, h₄⟩ := hret e zs us (hty zs hzs) hus
          rcases h₄.inv r₃ with hl' | ⟨tr₅, e₃, r₅⟩
          · exact absurd ho (hl'.not_holds _ _)
          have htr : l :: tr₂ = (tr₁ ++ (pre₂ ++ Label.tau :: tr₄)) ++ tr₅ := by
            rw [e₁, e₃]
            simp only [List.append_assoc, List.cons_append]
          have hlen : tr₅.length ≤ n := by
            have h₁ : (pre ++ l :: tr₂).length ≤ n + 1 := hn
            rw [htr] at h₁
            simp only [List.length_append, List.length_cons] at h₁
            omega
          have hend := ih (InstState.removeThread 1 (enterInst ιe
              ⟨(extN B ιe N C).store.threads.length⟩)) _ C₁ _ tr₅ m' out hlen
            (threadsOk_after _ _) (hk.after hy hst hf hres hws he hzs hus) r₅ ho
          have e' : pre ++ l :: tr₂ = (pre ++ (tr₁ ++ (pre₂ ++ Label.tau :: tr₄))) ++ tr₅ := by
            rw [htr]; simp only [List.append_assoc, List.cons_append]
          rw [e']
          exact lend_cons hy hst hf hres hws he hzs hus hend
      · rw [steps_of_locked rfl rfl r₃] at ho
        exact ⟨[], y, .done hy, .inr ⟨f, a, p, ys, hst, hf, hres, holds_trapCfgD ho,
          .inr ⟨ws, e, hws, he, .inl htr⟩⟩⟩
      · exact absurd hc' (hnco h' ys')

end Silmaril.Proofs.Wasm.Component.Reference
