module

public import Silmaril.Wasm.Component.Reference.Start.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.MultiSeq
public import Silmaril.Wasm.Game.Start.Thms

/-!
# Start functions: the module without its start function, and runs with a hole

* `validate?_noStart`, `instantiateOnce?_noStart`: removing the start function of a module
  changes neither its validation nor its instantiation, except that no start function is
  returned; hence `NumModule.IsInstS.noStart`: an instance before the start function of `m` is an
  instance (`NumModule.IsInst`) of `m.noStart`. The IR-level and reference-level lemmas stated
  for `NumModule.IsInst` (typing of calls at well-formed stores, `CallCtxAt`, the IR rounds) are
  used through it.
* `Reaches th X p m tr m₁ Post`: the program `p` runs deterministically (in any context) from `m`
  to `m₁`, where the program `X` is in focus; once `X` has run, the rest of `p` runs as `Post`
  prescribes. Built from `Reaches.here`, `Reaches.seq` (a complete run first) and `Reaches.left`
  (the hole in the left of a bind).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## Removing the start function -/

section NoStart

variable {H : Type}

theorem allocModule?_noStart (s : Store H) (m : Module) (xas : List ExternAddr) (a b c) :
    allocModule? s { m with start := none } xas a b c = allocModule? s m xas a b c := rfl

theorem initial_noStart (s : Store H) (m : Module) (xas : List ExternAddr) :
    ModuleInst.initial s { m with start := none } xas = ModuleInst.initial s m xas := rfl

theorem initSegments?_noStart (ev : Store H → Frame → Expr → Option (Store H × Execution.Core.Val))
    (s : Store H) (f : Frame) (m : Module) :
    initSegments? ev s f { m with start := none } = initSegments? ev s f m := rfl

theorem prepare?_noStart (ev : Store H → Frame → Expr → Option (Store H × Execution.Core.Val))
    (s : Store H) (m : Module) (xas : List ExternAddr) :
    prepare? ev s { m with start := none } xas = (prepare? ev s m xas).map fun p => (p.1, none) := by
  unfold prepare?
  simp only [allocModule?_noStart, initial_noStart]
  split_ifs
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
  · rfl

/-- **Instantiation without the start function** is instantiation, returning no start
function. -/
theorem instantiateOnce?_noStart (s : Store H) (m : Module) (xas : List ExternAddr) :
    instantiateOnce? s { m with start := none } xas =
      (instantiateOnce? s m xas).map fun p => (p.1, p.2.1, none) := by
  unfold instantiateOnce? instantiateDirect? prepareDirect?
  have e : ({ m with start := none } : Module).globalResidue =
      { m.globalResidue with start := none } := rfl
  have e₂ : Module.closedGlobalTypes ({ m with start := none } : Module) =
      Module.closedGlobalTypes m := rfl
  simp only [initial_noStart, e, e₂, prepare?_noStart]
  split
  · rfl
  · cases prepare? evalConst? _ m.globalResidue _ with
    | none => rfl
    | some p =>
      dsimp only [Option.map]
      rw [initSegments?_noStart]
      split <;> rfl

/-- **Validation without the start function** succeeds with the same module type. -/
theorem validate?_noStart {m : Module} {mt : Validation.CModuleType}
    (h : Validation.validate? m = some mt) :
    Validation.validate? { m with start := none } = some mt := by
  have e₁ : ∀ dts xtI fdts, Validation.moduleCtx' ({ m with start := none } : Module) dts xtI fdts =
      Validation.moduleCtx' m dts xtI fdts := fun _ _ _ => rfl
  have e₂ : ∀ C' xtI jts gts tts rts,
      Validation.moduleCtx ({ m with start := none } : Module) C' xtI jts gts tts rts =
        Validation.moduleCtx m C' xtI jts gts tts rts := fun _ _ _ _ _ _ => rfl
  simp only [Validation.validate?, Validation.checkModule?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h ⊢
  obtain ⟨dts, h₁, xtI, h₂, fdts, h₃, jts, h₄, gts, h₅, tts, h₆, h₇⟩ := h
  refine ⟨dts, h₁, xtI, h₂, fdts, h₃, jts, h₄, gts, h₅, tts, h₆, ?_⟩
  rw [e₁, e₂]
  split_ifs at h₇ with hc hnd
  any_goals simp at h₇
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  rw [ite_eq_left_iff.mpr (fun hn => absurd (by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨hc'.1.1.1.1, hc'.1.1.1.2⟩, hc'.1.1.2⟩, hc'.1.2⟩, rfl⟩) hn)]
  simpa [hnd] using h₇

end NoStart

/-- **An instance before the start function is an instance of the module without it.** -/
theorem isInstance_noStart {m : Module} {mt : Validation.CModuleType}
    {I : Silmaril.Wasm.Game.ScalarInstance} {start : Option Nat}
    (h : Silmaril.Wasm.Game.IsInstanceStart m mt I start) :
    Silmaril.Wasm.Game.IsInstance { m with start := none } mt I where
  valid := validate?_noStart h.valid
  funcImports := h.funcImports
  importTypes := h.importTypes
  instantiated := by
    obtain ⟨f, st, hf, ha, -⟩ := h.instantiated
    exact ⟨f, by rw [instantiateOnce?_noStart, hf]; rfl, ha⟩
  exportTypes := h.exportTypes

theorem _root_.Silmaril.Wasm.Component.Reference.NumModule.IsInstS.noStart {m : NumModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} {start : Option Nat} (h : m.IsInstS I start) :
    m.noStart.IsInst I :=
  ⟨⟨h.1.choose, isInstance_noStart h.1.choose_spec⟩, h.2.1, h.2.2⟩

/-- The instance store before the start function is well formed. -/
theorem _root_.Silmaril.Wasm.Component.Reference.NumModule.IsInstS.ok {m : NumModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} {start : Option Nat} (h : m.IsInstS I start) :
    I.WellFormed I.store :=
  h.1.choose_spec.ok.1

/-- The start function has the type `[] → []`. -/
theorem _root_.Silmaril.Wasm.Component.Reference.NumModule.IsInstS.startTyped {m : NumModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} {start : Option Nat} (h : m.IsInstS I start) :
    ∀ a ∈ start, Silmaril.Wasm.Game.StartTyped I.store a :=
  h.1.choose_spec.ok.2

/-- Without a start function, an instance before the start function is an instance. -/
theorem _root_.Silmaril.Wasm.Component.Reference.NumModule.IsInstS.isInst_none {m : NumModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} (h : m.IsInstS I none) : m.IsInst I :=
  ⟨⟨h.1.choose, Silmaril.Wasm.Game.isInstanceStart_none_iff.1 h.1.choose_spec⟩, h.2.1, h.2.2⟩

/-- The simple component with the module without its start function. -/
def _root_.Silmaril.Wasm.Component.Reference.Simple.noStart (c : Simple) : Simple :=
  ⟨c.mod.noStart, c.exports⟩

/-! ## The start function as an extra export -/

section PlusStart

open Silmaril.Wasm.Game

variable {I : ScalarInstance} {s : Store Nat} {a : Nat}

/-- The instance with the start function at `a` as an extra export `0` (as
`Silmaril.Proofs.Wasm.Game.Start.plusStart`, restated here: proof modules of another topic are not
imported). -/
def plusStartI (I : ScalarInstance) (a : Nat) : ScalarInstance :=
  { I with exports := startType :: I.exports, addrs := a :: I.addrs }

/-- The call of the start function, as an export call of `plusStartI I a`. -/
def startOpI (I : ScalarInstance) (a : Nat) : (plusStartI I a).F.Op :=
  ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨[], .nil⟩⟩

theorem plusStartI_wellFormed (hw : I.WellFormed s) (ha : StartTyped s a) :
    (plusStartI I a).WellFormed s where
  storeOk := hw.storeOk
  addrs_length := congrArg (· + 1) hw.addrs_length
  export_type j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ha
    · exact hw.export_type j
  host_type := hw.host_type

theorem wellFormed_of_plusStartI (hw : (plusStartI I a).WellFormed s) : I.WellFormed s where
  storeOk := hw.storeOk
  addrs_length := Nat.succ.inj hw.addrs_length
  export_type j := hw.export_type j.succ
  host_type := hw.host_type

/-- A typed answer of the start type is `values []`, a trap or an exception. -/
theorem result_of_startTypeI {r : Result} {w : Answer startType}
    (h : Answer.ofResult? startType r = some w) :
    r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := by
  have hr : w.toResult = r := Answer.toResult_of_ofResult? h
  rcases w with ⟨vs, hvs⟩ | _ | x
  · have hvs' : vs = [] := List.forall₂_nil_left_iff.1 hvs
    exact .inl (hr.symm.trans (congrArg Result.values hvs'))
  · exact .inr (.inl hr.symm)
  · exact .inr (.inr ⟨x, hr.symm⟩)

/-- **Typed start results**, host-free: a result of the start function is `values []`, a trap
or an exception. -/
theorem start_result {P : Silmaril.Wasm.Numerics.Profile} (hw : I.WellFormed s)
    (ha : StartTyped s a) (hI : I.imports = []) {c' : Silmaril.Wasm.Execution.Core.Config Nat} {r : Result}
    (run : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a []) c')
    (final : c'.code = r.toAdmin) : r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := by
  have run' : Silmaril.Wasm.Execution.Core.Steps P (hostOf (plusStartI I a).imports (Env.silent _))
      (invoke s ((plusStartI I a).addr (startOpI I a).1) (startOpI I a).2.1) c' := by
    rw [hostOf_nil (I := plusStartI I a) hI]
    exact run
  obtain ⟨w, hw', -⟩ := ScalarInstance.answer_of_run (plusStartI_wellFormed hw ha)
    (throwsBelow_silent _ _) run' final
  exact result_of_startTypeI hw'

/-- **The start function never calls out**, host-free. -/
theorem start_no_callout {P : Silmaril.Wasm.Numerics.Profile} (hw : I.WellFormed s)
    (ha : StartTyped s a) (hI : I.imports = []) {c' : Silmaril.Wasm.Execution.Core.Config Nat}
    (run : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a []) c') :
    Silmaril.Wasm.SingleThreaded.decompose? c'.store c'.code = none := by
  have run' : Silmaril.Wasm.Execution.Core.Steps P (hostOf (plusStartI I a).imports (Env.silent _))
      (invoke s ((plusStartI I a).addr (startOpI I a).1) (startOpI I a).2.1) c' := by
    rw [hostOf_nil (I := plusStartI I a) hI]
    exact run
  rcases ScalarInstance.progress_hostOf (plusStartI_wellFormed hw ha)
    (throwsBelow_silent _ _) run' with ⟨r, hr⟩ | ⟨c'', hs⟩
  · rw [hr]
    exact Silmaril.Wasm.Binaryen.LinkBehaviours.decompose?_result r
  · rw [hostOf_nil (I := plusStartI I a) hI] at hs
    exact Silmaril.Wasm.SingleThreaded.decompose?_none_of_noRedex
      (Silmaril.Wasm.SingleThreaded.Step.noRedex hs)

/-- **The start function keeps the instance well formed.** -/
theorem start_wellFormed {P : Silmaril.Wasm.Numerics.Profile} (hw : I.WellFormed s)
    (ha : StartTyped s a) (hI : I.imports = []) {s' : Store Nat} {t' : Silmaril.Wasm.SingleThreaded.Thread} {r : Result}
    (run : Reach P (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) (s', t'))
    (final : ResultAt s' t' r) : I.WellFormed s' := by
  have steps : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a []) (t'.config s') :=
    internalP_steps (H := Nat) run
  have run' : Silmaril.Wasm.Execution.Core.Steps P (hostOf (plusStartI I a).imports (Env.silent _))
      (invoke s ((plusStartI I a).addr (startOpI I a).1) (startOpI I a).2.1) (t'.config s') := by
    rw [hostOf_nil (I := plusStartI I a) hI]
    exact steps
  obtain ⟨w, hw', -⟩ := ScalarInstance.answer_of_run (plusStartI_wellFormed hw ha)
    (throwsBelow_silent _ _) run' final
  have hpath : (plusStartI I a).Activation P s [.inr (.ask (startOpI I a)),
      .inr (.ans (startOpI I a) w)] s' :=
    .cons (.call s _) (.cons (.oret run final hw') (.nil _))
  refine wellFormed_of_plusStartI (ScalarInstance.WellFormed.activation
    (plusStartI_wellFormed hw ha) ?_ hpath).1
  intro e v hm
  simp at hm

end PlusStart

/-! ## Runs with a hole -/

section Hole

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

variable (prof hr dispatch) in
/-- **A run reaching a hole**: in every context, the program `p` runs deterministically from
`m` (labels `tr`) to `m₁`, where `X` is in focus followed by some continuation `K`; from any
`m₂` such that `Post m₂ tr' a m'`, `K ()` runs to `m'` with the context's continuation applied
to `a`. -/
def Reaches (th : Option ThreadId) (X : Canon.P E σ Unit) {α : Type} (p : Canon.P E σ α)
    (m : Silmaril.Wasm.Execution.Core.Config E σ) (tr : List (Label E σ)) (m₁ : Silmaril.Wasm.Execution.Core.Config E σ)
    (Post : Silmaril.Wasm.Execution.Core.Config E σ → List (Label E σ) → α → Silmaril.Wasm.Execution.Core.Config E σ → Prop) : Prop :=
  ∀ (f : α → Canon.P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
    m.store.lockdown = false →
    ∃ K : Unit → Canon.P E σ (Ret E),
      LRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m₁ with ctl := ⟨th, .prog (X >>= K), segs⟩ :: rest } ∧
      ∀ m₂ tr' a m', Post m₂ tr' a m' → m₂.store.lockdown = false →
        LRun prof hr dispatch { m₂ with ctl := ⟨th, .prog (K ()), segs⟩ :: rest } tr'
          { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } ∧ m'.store.lockdown = false

namespace Reaches

theorem here {th : Option ThreadId} {X : Canon.P E σ Unit} {α : Type}
    (k : Unit → Canon.P E σ α) (m : Silmaril.Wasm.Execution.Core.Config E σ) :
    Reaches prof hr dispatch th X (X >>= k) m [] m
      (fun m₂ tr' a m' => RunsQ dispatch th (k ()) m₂ tr' a m') := by
  intro f segs rest _
  refine ⟨fun u => k u >>= f, ?_, fun m₂ tr' a m' h hl =>
    ⟨h.lrun hl f segs rest, h.lock.trans hl⟩⟩
  rw [bind_assoc]
  exact .refl _

theorem seq {th : Option ThreadId} {X : Canon.P E σ Unit} {α β : Type} {p : Canon.P E σ β}
    {g : β → Canon.P E σ α} {m m₁ m₂ : Silmaril.Wasm.Execution.Core.Config E σ} {tr₁ tr₂ : List (Label E σ)} {b : β}
    {Post : Silmaril.Wasm.Execution.Core.Config E σ → List (Label E σ) → α → Silmaril.Wasm.Execution.Core.Config E σ → Prop}
    (h₁ : RunsQ dispatch th p m tr₁ b m₁) (h₂ : Reaches prof hr dispatch th X (g b) m₁ tr₂ m₂ Post) :
    Reaches prof hr dispatch th X (p >>= g) m (tr₁ ++ tr₂) m₂ Post := by
  intro f segs rest hl
  obtain ⟨K, r, hK⟩ := h₂ f segs rest (h₁.lock.trans hl)
  refine ⟨K, ?_, hK⟩
  have d := h₁.lrun (prof := prof) (hr := hr) hl (fun b => g b >>= f) segs rest
  rw [bind_assoc]
  exact d.trans r

theorem left {th : Option ThreadId} {X : Canon.P E σ Unit} {α β : Type} {p : Canon.P E σ β}
    {g : β → Canon.P E σ α} {m m₁ : Silmaril.Wasm.Execution.Core.Config E σ} {tr : List (Label E σ)}
    {Post : Silmaril.Wasm.Execution.Core.Config E σ → List (Label E σ) → β → Silmaril.Wasm.Execution.Core.Config E σ → Prop}
    (h : Reaches prof hr dispatch th X p m tr m₁ Post) :
    Reaches prof hr dispatch th X (p >>= g) m tr m₁
      (fun m₂ tr' a m' => ∃ b m₃ tr₁ tr₂, Post m₂ tr₁ b m₃ ∧
        RunsQ dispatch th (g b) m₃ tr₂ a m' ∧ tr' = tr₁ ++ tr₂) := by
  intro f segs rest hl
  obtain ⟨K, r, hK⟩ := h (fun b => g b >>= f) segs rest hl
  refine ⟨K, ?_, ?_⟩
  · rw [bind_assoc]
    exact r
  · rintro m₂ tr' a m' ⟨b, m₃, tr₁, tr₂, hP, hg, rfl⟩ hl₂
    obtain ⟨r₁, hl₃⟩ := hK m₂ tr₁ b m₃ hP hl₂
    exact ⟨r₁.trans (hg.lrun hl₃ f segs rest), hg.lock.trans hl₃⟩

end Reaches

end Hole

end Silmaril.Proofs.Wasm.Component.Reference
