module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.TrapStore

/-!
# Segmented runs of a linked call, with the core store of a trap

`lsegs_invT` is `lsegs_inv` (`LinkSegs`, same proof) with `LEndT`: when a nested call fails (its
arguments do not lift, the exporter traps, or its results do not lift), the call traps at the
core store of the callout or of the exporter's end (`nest_trap_argsT`, `nest_atT`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- How a run of the importer's core phase ends where a call outcome holds (`LEnd`), a
failing nested call with the core store `m'` holds. -/
def LEndT (B : Machine.Config (E3 P) σ) (th : Option ThreadId)
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
        ((liftArgs p.params ys = none ∧ m'.core = y.1) ∨
          ∃ ws e, liftArgs p.params ys = some ws ∧
            Relation.ReflTransGen (CoreStep (E3 P))
              (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e ∧
            ((E3 P).status e.1 e.2 = .returned .trap ∨
              ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧
                liftArgs p.results zs = none) ∧ m'.core = e.1)))

theorem lend_consT {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
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
    (ih : LEndT (prof := prof) (impl := impl) B th K segs rest
      (e.1, (E3 P).resume e.1 y.2 (.values (lowerArgs p.results us))) tr'' m' out) :
    LEndT (prof := prof) (impl := impl) B th K segs rest x (pre ++ tr'') m' out := by
  obtain ⟨recs, z, hz, hend⟩ := ih
  refine ⟨_, z, .call hy hs hf hr hws he hst hus hz, ?_⟩
  rcases hend with ⟨ιe', N', C', pre', l, m₁, tr₂, rfl, ht, hco, hx, r⟩ | hT
  · exact .inl ⟨ιe', N', C', pre ++ pre', l, m₁, tr₂, by rw [List.append_assoc], ht, hco, hx, r⟩
  · exact .inr hT


/-- **Inversion of the importer's core phase with nested calls** (`lsegs_inv`, same proof),
with the core store of a failing nested call. -/
theorem lsegs_invT {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {cid : CallId} (hB : LFrame B th) :
    ∀ (n : Nat) (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
      (x : CoreSt (E3 P)) (tr : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ)
      (out : CallOutcome),
      tr.length ≤ n → ThreadsOk ιe → LinkOk B x →
      Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x) tr m' →
      out.Holds (fun _ _ => false) cid m' →
      LEndT (prof := prof) (impl := impl) B th K segs rest x tr m' out := by
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
      have hT := nest_trap_argsT (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a
        p ys ιi hst (hB.entry _ _ _ _ _) hi hleave hf hB.len hadd hpf hys hmaxp hws
      obtain ⟨hout, hcore⟩ := hT.out r' ho
      exact ⟨[], y, .done hy, .inr ⟨f, a, p, ys, hst, hf, hres, hout, .inl ⟨hws, hcore⟩⟩⟩
    | some ws =>
      obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₁, hrun, hctl, hcore, hlock, hret, htrap⟩ :=
        nest_atT (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hst
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
          obtain ⟨hout, hcore⟩ := (htrap e zs (hty zs hzs) hus).out r₃ ho
          exact ⟨[], y, .done hy, .inr ⟨f, a, p, ys, hst, hf, hres, hout,
            .inr ⟨ws, e, hws, he, .inr ⟨zs, hzs, hus⟩, hcore⟩⟩⟩
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
          exact lend_consT hy hst hf hres hws he hzs hus hend
      · have e₃ := steps_of_locked rfl rfl r₃
        subst e₃
        exact ⟨[], y, .done hy, .inr ⟨f, a, p, ys, hst, hf, hres, holds_trapCfgD ho,
          .inr ⟨ws, e, hws, he, .inl htr, rfl⟩⟩⟩
      · exact absurd hc' (hnco h' ys')

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
