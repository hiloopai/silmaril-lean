module

public import Silmaril.Proofs.Wasm.Game.Adequacy.Runs
public import Silmaril.Proofs.Wasm.Game.Adequacy.Termination
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Progress and divergence of the composite

* `progress_hostOf`: from a well-formed invocation, every configuration
  reached under a strategy-definable host is finished or has a step (Core type
  soundness through the guarded host `guardHost`, which is `HostOk`, and
  `step_host_congr`). This needs `ThrowsBelow`: a dangling exception address
  could be caught by a `catch` clause that looks up its tag and get stuck.
* `diverges_of_no_answer` (every profile): if the composite never answers,
  the invocation diverges.
* `diverges_iff_no_answer` (deterministic profiles `profile o`): the
  invocation diverges exactly when the composite never answers. Under a
  nondeterministic profile the converse fails in general: a run may diverge
  on one branch and answer on another.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : ScalarInstance}

/-! ### Host congruence at callouts -/

/-- A host call answered at a host-call redex is a Core step. -/
theorem step_of_callout_returned {P : Profile} {host : HostSemantics Nat} {c : Config Nat}
    {E : Ctx} {a hh : Nat} {args : List Val} {s' : Store Nat} {r : Result}
    (hd : decompose? c.store c.code = some (E, a, hh, args))
    (hr : host hh c.store args (.returned s' r)) :
    Step P host c ⟨s', c.frame, E.fill r.toAdmin⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
  dsimp only at hcode hr ⊢
  subst hcode
  exact E.step_fill (fun _ => Step.callRefHost hyy hf he hn hc hr) _

/-- A divergent host call at a host-call redex is a Core self-loop step. -/
theorem step_of_callout_diverged {P : Profile} {host : HostSemantics Nat} {c : Config Nat}
    {E : Ctx} {a hh : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args))
    (hdiv : host hh c.store args .diverged) :
    Step P host c c := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
  dsimp only at hcode hdiv ⊢
  subst hcode
  exact E.step_fill (fun _ => Step.callRefHostDiv hyy hf he hn hc hdiv) _

/-- A Core step only depends on the host at the callout of its source configuration. -/
theorem step_host_congr {P : Profile} {host₁ host₂ : HostSemantics Nat} {c c' : Config Nat}
    (h : Step P host₁ c c')
    (hag : ∀ E a hh args out, decompose? c.store c.code = some (E, a, hh, args) →
      host₁ hh c.store args out → host₂ hh c.store args out) :
    Step P host₂ c c' := by
  rcases Step.split_host h with h' | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact Step.of_noHost host₂ h'
  · exact step_of_callout_returned hd (hag _ _ _ _ _ hd hr)
  · exact step_of_callout_diverged hd (hag _ _ _ _ _ hd hdiv)

/-- A result has no host-call redex. -/
theorem decompose?_toAdmin (s : Store Nat) (r : Result) : decompose? s r.toAdmin = none := by
  cases r with
  | values vs => exact decompose?_vals_nil
  | trap => exact decompose?_vals_cons_none (vs := []) (r := []) rfl (fun _ _ => decompHead_trap)
  | throw a =>
    exact decompose?_vals_cons_none (vs := [.ref (.exn a)]) (r := []) rfl
      (fun _ _ => decompHead_plain rfl)

/-! ### A typed host agreeing with `hostOf` along runs -/

/-- Stores reached from `s`: same functions, no fewer exceptions. -/
structure StoreInv (s s' : Store Nat) : Prop where
  funcs : s'.funcs = s.funcs
  exns : s.exns.length ≤ s'.exns.length

variable (I) in
/-- `hostOf` guarded by `StoreInv s`; it diverges on stores violating the invariant. -/
def guardHost (s : Store Nat) (K : Silmaril.Wasm.Game.Env I.E) : HostSemantics Nat :=
  fun h s' args out =>
    (StoreInv s s' ∧ hostOf I.imports K h s' args out) ∨ (¬ StoreInv s s' ∧ out = .diverged)

theorem guardHost_hostOf {s s' : Store Nat} {K : Silmaril.Wasm.Game.Env I.E} {h : Nat} {args : List Val}
    {out : HostOutcome Nat} (hinv : StoreInv s s') (hg : guardHost I s K h s' args out) :
    hostOf I.imports K h s' args out := by
  rcases hg with ⟨-, hg⟩ | ⟨hn, -⟩
  · exact hg
  · exact absurd hinv hn

theorem forall₂_valOk_of_hasVal {s : Store Nat} {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal ts vs) :
    List.Forall₂ (ValOk s) vs (Ty.ofList (ts.map ScalarType.toC)).toList := by
  rw [Ty.toList_ofList]
  exact List.forall₂_map_right_iff.mpr
    (h.flip.imp fun v t hv => (ScalarType.hasVal_iff_valOk s t v).mp hv)

theorem hasVal_of_forall₂_valOk {s : Store Nat} {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ (ValOk s) vs (Ty.ofList (ts.map ScalarType.toC)).toList) :
    List.Forall₂ ScalarType.HasVal ts vs := by
  rw [Ty.toList_ofList] at h
  exact (List.forall₂_map_right_iff.mp h).flip.imp
    fun t v hv => (ScalarType.hasVal_iff_valOk s t v).mpr hv

/-- An answer of an environment throwing below the store's exceptions is a typed result. -/
private theorem answer_resultTyped {ft : FnType} {s : Store Nat} {n : Nat}
    (hn : n ≤ s.exns.length) (w : Answer ft) (hb : w.ThrowsBelow n) :
    ResultTyped s w.toResult (Ty.ofList (ft.results.map ScalarType.toC)).toList := by
  cases w with
  | values vs' => exact forall₂_valOk_of_hasVal vs'.2
  | trap => trivial
  | throw a' => exact ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hb hn)⟩

/-- `guardHost` satisfies the host contract. -/
theorem guardHost_ok {s : Store Nat} (hw : I.WellFormed s) {K : Silmaril.Wasm.Game.Env I.E}
    (hK : ThrowsBelow K s.exns.length) : HostOk (guardHost I s K) := by
  intro s' fi h vs ps rs hs' hfi hcode hexp hvs
  by_cases hinv : StoreInv s s'
  swap
  · refine ⟨⟨.diverged, Or.inr ⟨hinv, rfl⟩⟩, ?_⟩
    rintro out (⟨h', -⟩ | ⟨-, rfl⟩)
    · exact absurd h' hinv
    · trivial
  obtain ⟨a, ha⟩ : ∃ a, s.funcs[a]? = some fi := by
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hfi
    exact ⟨a, hinv.1 ▸ ha⟩
  obtain ⟨hlt, hexp'⟩ := hw.host_type a fi h ha hcode
  obtain ⟨rfl, rfl⟩ : ps = Ty.ofList ((I.imports.get ⟨h, hlt⟩).params.map ScalarType.toC) ∧
      rs = Ty.ofList ((I.imports.get ⟨h, hlt⟩).results.map ScalarType.toC) := by
    simpa only [FnType.toComp, Ty.func.injEq] using Expand.func_eq hexp hexp'
  have hty : List.Forall₂ ScalarType.HasVal (I.imports.get ⟨h, hlt⟩).params vs :=
    hasVal_of_forall₂_valOk hvs
  have hop : ifaceOp? I.imports h vs = some ⟨⟨h, hlt⟩, ⟨vs, hty⟩⟩ := by
    simp only [ifaceOp?, hlt, hty, ↓reduceDIte]
  refine ⟨?_, ?_⟩
  · by_cases hans : ∃ w, K.Answers (⟨⟨h, hlt⟩, ⟨vs, hty⟩⟩ : I.E.Op) w
    · obtain ⟨w, hw'⟩ := hans
      exact ⟨_, Or.inl ⟨hinv, _, hop, Or.inl ⟨w, hw', rfl⟩⟩⟩
    · exact ⟨_, Or.inl ⟨hinv, _, hop, Or.inr ⟨fun w hw' => hans ⟨w, hw'⟩, rfl⟩⟩⟩
  · rintro out (⟨-, e, he, ⟨w, hw', rfl⟩ | ⟨-, rfl⟩⟩ | ⟨hn, -⟩)
    · obtain rfl : e = ⟨⟨h, hlt⟩, ⟨vs, hty⟩⟩ := Option.some.inj (he.symm.trans hop)
      exact ⟨hs', Extend.refl hs', answer_resultTyped hinv.2 w (hK _ w hw')⟩
    · trivial
    · exact absurd hinv hn

/-! ### The run invariant -/

/-- The invariant along runs from a well-formed store `s`: typed, with the functions of `s`
and at least its exceptions. -/
structure Good (s : Store Nat) (ts : List CValType) (c : Config Nat) : Prop where
  ok : ConfigOk c ts
  inv : StoreInv s c.store

/-- Invocations of an export from a well-formed store satisfy the invariant. -/
theorem good_invoke {s : Store Nat} (hw : I.WellFormed s) (f : I.F.Op) :
    ∃ ts, Good s ts (invoke s (I.addr f.1) f.2.1) := by
  obtain ⟨fi, hf, hexp⟩ := hw.export_type f.1
  have hinv : InvokeOk s (I.addr f.1) f.2.1 :=
    ⟨fi, _, _, hf, hexp, forall₂_valOk_of_hasVal f.2.2⟩
  obtain ⟨_, _, rs, -, -, hok⟩ := invoke_ok hw.storeOk hinv
  exact ⟨rs.toList, ⟨hok, ⟨rfl, Nat.le_refl _⟩⟩⟩

/-- `hostOf` steps preserve the invariant. -/
theorem good_step {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {ts : List CValType}
    {c c' : Config Nat} (hg : Good s ts c) (h : Step P (hostOf I.imports K) c c') :
    Good s ts c' := by
  have h' : Step P (guardHost I s K) c c' :=
    step_host_congr h fun _ _ _ _ _ _ hout => Or.inl ⟨hg.inv, hout⟩
  obtain ⟨hok, hext⟩ := Step.preservation (guardHost_ok hw hK) hg.ok h'
  refine ⟨hok, ⟨?_, Nat.le_trans hg.inv.2 hext.exns.1⟩⟩
  rcases Step.split_host h with h₀ | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨-, rfl⟩⟩
  · exact (Step.framesLocal h₀).1.trans hg.inv.1
  · obtain ⟨e, -, ⟨w, -, hout⟩ | ⟨-, hout⟩⟩ := hr
    · cases hout
      exact hg.inv.1
    · cases hout
  · exact hg.inv.1

theorem good_steps {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {ts : List CValType}
    {c c' : Config Nat} (hg : Good s ts c) (h : Steps P (hostOf I.imports K) c c') :
    Good s ts c' := by
  induction h with
  | refl => exact hg
  | tail _ hst ih => exact good_step hw hK ih hst

/-- Progress for configurations satisfying the invariant. -/
theorem good_progress {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {ts : List CValType}
    {c : Config Nat} (hg : Good s ts c) :
    (∃ r : Result, c.code = r.toAdmin) ∨ ∃ c', Step P (hostOf I.imports K) c c' := by
  rcases Config.progress (P := P) (guardHost_ok hw hK) hg.ok with ⟨r, hr⟩ | ⟨c', hc'⟩
  · exact Or.inl ⟨r, hr⟩
  · exact Or.inr ⟨c', step_host_congr hc' fun _ _ _ _ _ _ hout => guardHost_hostOf hg.inv hout⟩

/-- **Typed callouts.** Under the invariant every host-call redex is a valid import call
(read through progress of `guardHost`, which only answers valid import calls). -/
theorem good_callout_valid {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {ts : List CValType}
    {c : Config Nat} (hg : Good s ts c) {E : Ctx} {a hh : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args)) :
    ∃ e, ifaceOp? I.imports hh args = some e := by
  rcases Config.progress (P := P) (guardHost_ok hw hK) hg.ok with ⟨r, hr⟩ | ⟨c', hc'⟩
  · rw [hr, decompose?_toAdmin] at hd
    cases hd
  · rcases Step.split_host hc' with h₀ | ⟨E', a', hh', args', hd', ⟨s', r, hr, -⟩ | ⟨hdiv, -⟩⟩
    · rw [decompose?_none_of_noRedex (Step.noRedex h₀)] at hd
      cases hd
    · rw [hd] at hd'
      simp only [Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨-, -, rfl, rfl⟩ := hd'
      obtain ⟨e, he, -⟩ := guardHost_hostOf hg.inv hr
      exact ⟨e, he⟩
    · rw [hd] at hd'
      simp only [Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨-, -, rfl, rfl⟩ := hd'
      obtain ⟨e, he, -⟩ := guardHost_hostOf hg.inv hdiv
      exact ⟨e, he⟩

/-! ### Progress and divergence -/

/-- **Progress.** A configuration reached from a well-formed invocation under an induced host
(whose environment throws only existing exceptions) is finished or has a step. -/
theorem progress_hostOf {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {c : Config Nat}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c) :
    (∃ r : Result, c.code = r.toAdmin) ∨ ∃ c', Step P (hostOf I.imports K) c c' := by
  obtain ⟨ts, hg⟩ := good_invoke hw f
  exact good_progress hw hK (good_steps hw hK hg run)

/-- **No answer is divergence** (every profile). If the composite never answers, every
configuration reached is unfinished, so by progress the invocation has an infinite run. -/
theorem diverges_of_no_answer {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    (hno : ∀ w, ¬ Responds (I.closedWith P s K) f w) :
    Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) := by
  show InfiniteTrace (Step P (hostOf I.imports K)) _
  refine InfiniteTrace.coinduct
    (fun c => Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c)
    ?_ Relation.ReflTransGen.refl
  intro c run
  rcases progress_hostOf hw hK run with ⟨r, hr⟩ | ⟨c', hc'⟩
  · obtain ⟨w, -, hans⟩ := answer_of_run hw hK run hr
    exact absurd hans (hno w)
  · exact ⟨c', hc', run.tail hc'⟩

/-- **Divergence, deterministic profiles.** In `profile o` the invocation diverges exactly when
the composite never answers. -/
theorem diverges_iff_no_answer {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} :
    Diverges (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) ↔
      ∀ w, ¬ Responds (I.closedWith (profile o) s K) f w := by
  constructor
  · intro hdiv w hans
    obtain ⟨c', r, run, final, -⟩ := run_of_answer hans
    exact not_diverges_of_run run final hdiv
  · exact diverges_of_no_answer hw hK

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
