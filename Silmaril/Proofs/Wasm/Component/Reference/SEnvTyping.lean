module

public import Silmaril.Wasm.Game.StatefulEnv.Thms
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.Binaryen.LinkBehaviours

/-!
# Typed callouts of runs against a stateful host

Runs of a scalar instance's export call in product with a stateful environment `L`
(`Silmaril.Wasm.Game.SStep`) keep the Core typing invariant, so every host-call redex they reach
is a typed import question (`sstep_callout_typed`). The header `Silmaril.Wasm.Game.StatefulEnv`
proves the answer half (`sanswer_of_run`) but has no progress statement; this module supplies
the callout half.

The proof is the invariant of `progress_hostOf`, adapted from
`Silmaril.Proofs.Wasm.Game.Adequacy.Progress` (`StoreInv`, `guardHost`, `guardHost_ok`, `Good`,
`good_step`, `good_callout_valid`, `step_host_congr`), which this topic does not import: the
guarded host `anyHost I s` answers every typed import call with any answer throwing below the
exceptions of `s` (or diverges), so every product step is one of its steps, whatever the host
state.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

namespace SEnvTyping

variable {I : ScalarInstance}

/-- A host call answered at a host-call redex is a Core step. -/
theorem step_of_callout_returned {P : Profile} {host : HostSemantics Nat} {c : Config Nat}
    {E : Ctx} {a hh : Nat} {args : List Val} {s' : Store Nat} {r : Result}
    (hd : decompose? c.store c.code = some (E, a, hh, args))
    (hr : host hh c.store args (.returned s' r)) :
    Silmaril.Games.Step P host c ⟨s', c.frame, E.fill r.toAdmin⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
  dsimp only at hcode hr ⊢
  subst hcode
  exact E.step_fill (fun _ => Silmaril.Games.Step.callRefHost hyy hf he hn hc hr) _

/-- A divergent host call at a host-call redex is a Core self-loop step. -/
theorem step_of_callout_diverged {P : Profile} {host : HostSemantics Nat} {c : Config Nat}
    {E : Ctx} {a hh : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args))
    (hdiv : host hh c.store args .diverged) :
    Silmaril.Games.Step P host c c := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
  dsimp only at hcode hdiv ⊢
  subst hcode
  exact E.step_fill (fun _ => Silmaril.Games.Step.callRefHostDiv hyy hf he hn hc hdiv) _

/-- A Core step only depends on the host at the callout of its source configuration. -/
theorem step_host_congr {P : Profile} {host₁ host₂ : HostSemantics Nat} {c c' : Config Nat}
    (h : Silmaril.Games.Step P host₁ c c')
    (hag : ∀ E a hh args out, decompose? c.store c.code = some (E, a, hh, args) →
      host₁ hh c.store args out → host₂ hh c.store args out) :
    Silmaril.Games.Step P host₂ c c' := by
  rcases Silmaril.Games.Step.split_host h with h' | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact Step.of_noHost host₂ h'
  · exact step_of_callout_returned hd (hag _ _ _ _ _ hd hr)
  · exact step_of_callout_diverged hd (hag _ _ _ _ _ hd hdiv)

/-- Stores reached from `s`: same functions, no fewer exceptions. -/
structure StoreInv (s s' : Store Nat) : Prop where
  funcs : s'.funcs = s.funcs
  exns : s.exns.length ≤ s'.exns.length

variable (I) in
/-- The host answering every typed import call with any answer throwing below the exceptions
of `s`, or diverging, on stores satisfying `StoreInv s`; it diverges on the other stores. -/
def anyHost (s : Store Nat) : HostSemantics Nat :=
  fun h s' args out =>
    (StoreInv s s' ∧ ∃ e, ifaceOp? I.imports h args = some e ∧
      ((∃ w : Answer (I.imports.get e.1), w.ThrowsBelow s.exns.length ∧
          out = .returned s' w.toResult) ∨ out = .diverged)) ∨
      (¬ StoreInv s s' ∧ out = .diverged)

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

/-- An answer throwing below the store's exceptions is a typed result. -/
theorem answer_resultTyped {ft : FnType} {s : Store Nat} {n : Nat}
    (hn : n ≤ s.exns.length) (w : Answer ft) (hb : w.ThrowsBelow n) :
    ResultTyped s w.toResult (Ty.ofList (ft.results.map ScalarType.toC)).toList := by
  cases w with
  | values vs' => exact forall₂_valOk_of_hasVal vs'.2
  | trap => trivial
  | throw a' => exact ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hb hn)⟩

/-- `anyHost` satisfies the host contract. -/
theorem anyHost_ok {s : Store Nat} (hw : I.WellFormed s) : HostOk (anyHost I s) := by
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
  refine ⟨⟨_, Or.inl ⟨hinv, _, hop, Or.inr rfl⟩⟩, ?_⟩
  rintro out (⟨-, e, he, ⟨w, hb, rfl⟩ | rfl⟩ | ⟨hn, -⟩)
  · obtain rfl : e = ⟨⟨h, hlt⟩, ⟨vs, hty⟩⟩ := Option.some.inj (he.symm.trans hop)
    exact ⟨hs', Extend.refl hs', answer_resultTyped hinv.2 w hb⟩
  · trivial
  · exact absurd hinv hn

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

/-- Steps of `anyHost` preserve the invariant. -/
theorem good_step {P : Profile} {s : Store Nat} (hw : I.WellFormed s) {ts : List CValType}
    {c c' : Config Nat} (hg : Good s ts c) (h : Silmaril.Games.Step P (anyHost I s) c c') : Good s ts c' := by
  obtain ⟨hok, hext⟩ := Step.preservation (anyHost_ok hw) hg.ok h
  refine ⟨hok, ⟨?_, Nat.le_trans hg.inv.2 hext.exns.1⟩⟩
  rcases Silmaril.Games.Step.split_host h with h₀ | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨-, rfl⟩⟩
  · exact (Silmaril.Games.Step.framesLocal h₀).1.trans hg.inv.1
  · rcases hr with ⟨-, e, -, ⟨w, -, hout⟩ | hout⟩ | ⟨-, hout⟩
    · cases hout
      exact hg.inv.1
    · cases hout
    · cases hout
  · exact hg.inv.1

/-- A product step against a stateful environment throwing below the exceptions of `s` is a
step of `anyHost`, from a configuration satisfying the invariant. -/
theorem sstep_any {P : Profile} {s : Store Nat} {L : SEnv I.E} (hL : L.ThrowsBelow s.exns.length)
    {ts : List CValType} {c c' : Config Nat} {q q' : L.S} (hg : Good s ts c)
    (h : SStep P L (c, q) (c', q')) : Silmaril.Games.Step P (anyHost I s) c c' := by
  refine step_host_congr (SStep.core_step h) ?_
  rintro E a hh args out - ⟨e, he, ⟨w, q'', hans, rfl⟩ | ⟨-, rfl⟩⟩
  · exact Or.inl ⟨hg.inv, e, he, .inl ⟨w, hL q e w q'' hans, rfl⟩⟩
  · exact Or.inl ⟨hg.inv, e, he, .inr rfl⟩

/-- Product runs preserve the invariant. -/
theorem good_ssteps {P : Profile} {s : Store Nat} (hw : I.WellFormed s) {L : SEnv I.E}
    (hL : L.ThrowsBelow s.exns.length) {ts : List CValType} {x y : Config Nat × L.S}
    (hg : Good s ts x.1) (h : SSteps P L x y) : Good s ts y.1 := by
  induction h with
  | refl => exact hg
  | tail _ hst ih => exact good_step hw ih (sstep_any hL ih hst)

/-- Two host-call redexes of the same code are the same call. -/
theorem redex_eq {s : Store Nat} {code : List Admin} {E E' : Ctx} {a a' h h' : Nat}
    {args args' : List Val} (hd : decompose? s code = some (E, a, h, args))
    (hd' : decompose? s code = some (E', a', h', args')) : h' = h ∧ args' = args := by
  have e : (E', a', h', args') = (E, a, h, args) := Option.some.inj (hd'.symm.trans hd)
  simp only [Prod.mk.injEq] at e
  exact ⟨e.2.2.1, e.2.2.2⟩

/-- A host call of `anyHost` from a store satisfying the invariant is a typed import call. -/
theorem anyHost_typed {s s' : Store Nat} {h : Nat} {args : List Val} {out : HostOutcome Nat}
    (hinv : StoreInv s s') (hr : anyHost I s h s' args out) :
    ∃ e, ifaceOp? I.imports h args = some e := by
  rcases hr with ⟨-, e, he, -⟩ | ⟨hn, -⟩
  · exact ⟨e, he⟩
  · exact absurd hinv hn

/-- A configuration at a host-call redex is not a result. -/
theorem redex_not_result {c : Config Nat} {E : Ctx} {a h : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, h, args)) (r : Result) :
    c.code ≠ r.toAdmin := by
  intro hr
  have hnone : decompose? c.store c.code = none := by
    rw [hr]
    exact Silmaril.Wasm.Binaryen.LinkBehaviours.decompose?_result r
  rw [hnone] at hd
  cases hd

/-- **Typed callouts against a stateful host.** Every host-call redex reached by a product run
of an export call from a well-formed store is a typed import question. -/
theorem sstep_callout_typed {P : Profile} {s : Store Nat} (hw : I.WellFormed s) {L : SEnv I.E}
    (hL : L.ThrowsBelow s.exns.length) {f : I.F.Op} {q q' : L.S} {c : Config Nat}
    (run : SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c, q')) {E : Ctx} {a hh : Nat}
    {args : List Val} (hd : decompose? c.store c.code = some (E, a, hh, args)) :
    ∃ e, ifaceOp? I.imports hh args = some e := by
  obtain ⟨ts, hg₀⟩ := good_invoke hw f
  have hg : Good s ts c := good_ssteps (P := P) hw hL (x := (_, q)) (y := (c, q')) hg₀ run
  have hstep : ∃ c', Silmaril.Games.Step P (anyHost I s) c c' := by
    rcases Config.progress (P := P) (anyHost_ok hw) hg.ok with ⟨r, hr⟩ | hc'
    · exact absurd hr (redex_not_result hd r)
    · exact hc'
  obtain ⟨c', hc'⟩ := hstep
  rcases Silmaril.Games.Step.split_host hc' with h₀ | ⟨E', a', hh', args', hd', ⟨s', r, hr, -⟩ | ⟨hdiv, -⟩⟩
  · have hnone : decompose? c.store c.code = none := decompose?_none_of_noRedex (Silmaril.Games.Step.noRedex h₀)
    exact absurd (hd.symm.trans hnone) (by simp)
  · obtain ⟨rfl, rfl⟩ := redex_eq hd hd'
    exact anyHost_typed hg.inv hr
  · obtain ⟨rfl, rfl⟩ := redex_eq hd hd'
    exact anyHost_typed hg.inv hdiv

end SEnvTyping

end Silmaril.Proofs.Wasm.Component.Reference
