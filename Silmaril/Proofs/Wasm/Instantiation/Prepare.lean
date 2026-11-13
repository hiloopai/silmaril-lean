module

public import Silmaril.Proofs.Wasm.Instantiation.Segments
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateComplete
public import Silmaril.Wasm.Execution.Core.Exec.ConstExprArity
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

/-!
# Completeness of `prepare?`, `instantiateInit?` and `instantiateDirect?` (proofs)

* `prepare?_complete`: relative to `EvalComplete`, `prepare?` finds the configuration of every
  `Instantiate` derivation, whose code is `initCode m` (silmaril-lean's `instantiate?_complete`
  and `prepare?_instantiate?`).
* `offsetCompleteAt_of_instantiate`: the offsets of an instantiated module are validated
  constant expressions, typed over the instance's types, so `evalConst?` is offset-complete at
  the instantiated frame (`evalConst?_of_exprOkConst`).
* `instantiateInit?_complete`, `instantiateDirect?_complete`: unconditional completeness in the
  host-free deterministic profile; `instantiateInit?_iff`, `instantiateDirect?_iff` combine it
  with silmaril-lean's soundness.
* `prepareDirect?_complete`, `prepareDirect?_iff`: the same for an arbitrary evaluator, relative
  to evaluator hypotheses.

Ported from an earlier development `Silmaril/Wasm/Execution/Core/Exec/{PrepareComplete,
InstantiateInitComplete,PrepareDirectComplete}.lean`. Changes: the offset argument shared by
the two unconditional theorems is one lemma (`initSegments?_of_instantiate`); the unused
hypothesis `∃ mt, ModuleOk m mt` of the source's `instantiateInit?_complete` is dropped (it
follows from `Instantiate`); `prepare?_code'` (a restatement of `prepare?_code`) and
`instantiateDirect?_complete_of` (an unused hypothesis on top of `instantiateDirect?_complete`)
are not ported.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Instantiation

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Instantiation

variable {H : Type}

theorem forall₂_exists_of_mem {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a}, a ∈ l → ∃ b, R a b
  | _, _, .nil, _, ha => by cases ha
  | _, _, .cons hr hs, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, hr⟩
    · exact forall₂_exists_of_mem hs ha

theorem withStart_store (c : Config H) (st : Option FuncIdx) :
    (c.withStart st).store = c.store := by
  cases st <;> rfl

theorem withStart_frame (c : Config H) (st : Option FuncIdx) :
    (c.withStart st).frame = c.frame := by
  cases st <;> rfl

/-- The prepared configuration is the initial store and frame with code `initCode m`. -/
theorem prepare?_eq {ev : Store H → Frame → Expr → Option (Store H × Val)} {s : Store H}
    {m : Module} {xas : List ExternAddr} {c : Config H} {st : Option FuncIdx}
    (h : prepare? ev s m xas = some (c, st)) : c = ⟨c.store, c.frame, initCode m⟩ := by
  have hc : c.code = initCode m := prepare?_code h
  obtain ⟨s₀, f₀, is₀⟩ := c
  exact congrArg (Config.mk s₀ f₀) hc

/-- **Completeness of `prepare?`** relative to `EvalComplete`. -/
theorem prepare?_complete {P : Profile} {host : HostSemantics H}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} (hev : EvalComplete P host ev)
    {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    (h : Instantiate P host s m xas c) :
    prepare? ev s m xas = some (⟨c.store, c.frame, initCode m⟩, m.start) := by
  have hi := instantiate?_complete hev h
  rw [prepare?_instantiate?] at hi
  rcases hp : prepare? ev s m xas with _ | ⟨c₀, st⟩
  · simp [hp] at hi
  · have hst : st = m.start := prepare?_start hp
    have hc : c₀.withStart st = c := by simpa [hp] using hi
    subst hst hc
    rw [withStart_store, withStart_frame, ← prepare?_eq hp]

/-- Every offset of a valid module is a validated constant expression, typed in a context whose
types are the module's allocated types. -/
theorem isOffset_exprOkConst {m : Module} {xtI xtE : List CExternType}
    (hm : ModuleOk m ⟨xtI, xtE⟩) :
    ∃ C : Context, C.types = allocTypes m.types ∧
      ∀ e, IsOffset m e → ∃ t, ExprOkConst C e t := by
  cases hm with
  | @mk dts _ _ _ _ _ _ _ _ C htypes _ hC' hC _ _ _ _ _ hdata helems _ _ _ =>
    refine ⟨C, by rw [allocTypes_eq htypes]; subst hC hC'; rfl, ?_⟩
    rintro e (⟨el, hel, y, hmode⟩ | ⟨d, hd, y, hmode⟩)
    · obtain ⟨b, ⟨-, -, -, hmo⟩⟩ := forall₂_exists_of_mem helems hel
      rw [hmode] at hmo
      cases hmo with
      | active _ _ ho => exact ⟨_, ho⟩
    · have hdo : DataOk C d := hdata d hd
      unfold DataOk at hdo
      rw [hmode] at hdo
      cases hdo with
      | active _ ho => exact ⟨_, ho⟩

/-- At the frame of an `Instantiate` derivation, `evalConst?` is complete on the offsets of the
module. -/
theorem offsetCompleteAt_of_instantiate {o : GrowOracle} {s : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} (hI : Instantiate (profile o) noHost s m xas c)
    {e : Expr} (he : IsOffset m e) : OffsetCompleteAt o (evalConst? (H := H)) c.frame e := by
  obtain ⟨xtE, xtI, hmod, -⟩ := hI.valid
  obtain ⟨C, hCT, hoff⟩ := isOffset_exprOkConst hmod
  have hft : c.frame.module.types = C.types := by
    obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, -, -, -, ha, rfl⟩ := hI.run
    obtain ⟨_, _, _, _, _, _, hmi, _⟩ := allocModule?_inv ha
    rw [hCT, hmi]
  obtain ⟨t, het⟩ := hoff e he
  exact fun _ _ _ _ hx => evalConst?_of_exprOkConst het hft hx

theorem evalConst?_evalComplete {P : Profile} {host : HostSemantics H} :
    EvalComplete P host (evalConst? (H := H)) :=
  fun _ _ _ _ _ _ hc h => evalConst?_complete hc h

/-- The executable segment initialisation after an `Instantiate` derivation computes every run
of `initCode m` to the empty code. -/
theorem initSegments?_of_instantiate {o : GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {f' : Frame}
    (hI : Instantiate (profile o) noHost s m xas c)
    (hS : Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩) :
    initSegments? evalConst? c.store c.frame m = some (s', f') :=
  initSegments?_completeAt (fun _ he => offsetCompleteAt_of_instantiate hI he) hS

/-- **Completeness of `instantiateDirect?`**, in the host-free deterministic profile. -/
theorem instantiateDirect?_complete {o : GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {f' : Frame}
    (hI : Instantiate (profile o) noHost s m xas c)
    (hS : Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩) :
    instantiateDirect? s m xas = some (s', f', m.start) := by
  unfold instantiateDirect? prepareDirect?
  rw [prepare?_complete evalConst?_evalComplete hI]
  simp only [initSegments?_of_instantiate hI hS]

/-- **Completeness of `instantiateInit?`**, in the host-free deterministic profile. -/
theorem instantiateInit?_complete {o : GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {f' : Frame}
    (hI : Instantiate (profile o) noHost s m xas c)
    (hS : Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩) :
    instantiateInit? s m xas = some ((⟨s', f', []⟩ : Config H).withStart m.start) := by
  unfold instantiateInit?
  rw [prepare?_complete evalConst?_evalComplete hI]
  simp only [initSegments?_of_instantiate hI hS]

/-- **Relative completeness of `prepareDirect?`** for an arbitrary evaluator. -/
theorem prepareDirect?_complete {o : GrowOracle}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {f' : Frame}
    (hev : EvalComplete (profile o) noHost ev)
    (hevc : ∀ s f e s' v, EvalExpr (profile o) noHost s f e s' f [v] → ev s f e = some (s', v))
    (hoff : ∀ e, IsOffset m e → ∀ (s : Store H) (f : Frame) (s' : Store H) (f' : Frame) vs,
      EvalExpr (profile o) noHost s f e s' f' vs → f' = f ∧ vs.length = 1)
    (hI : Instantiate (profile o) noHost s m xas c)
    (hS : Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩) :
    prepareDirect? ev s m xas = some (s', f', m.start) := by
  unfold prepareDirect?
  rw [prepare?_complete hev hI]
  simp only [initSegments?_complete hevc hoff hS]

/-- The soundness direction shared by the characterisations. -/
theorem prepareDirect?_sem {P : Profile} {host : HostSemantics H}
    {ev : Store H → Frame → Expr → Option (Store H × Val)}
    (hes : EvalSound P host ev) {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : prepareDirect? ev s m xas = some (s', f', st)) :
    st = m.start ∧ ∃ c, Instantiate P host s m xas c ∧
      Steps P host ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩ := by
  obtain ⟨c₀, hp, hs⟩ := prepareDirect?_steps hes h
  obtain ⟨hst, hI⟩ := prepare?_sound hes hp hvalid
  refine ⟨hst, c₀.withStart st, hI, ?_⟩
  rw [withStart_store, withStart_frame, ← prepare?_eq hp]
  exact hs

/-- `prepareDirect?` characterised by the reduction semantics, for a sound and complete
evaluator. -/
theorem prepareDirect?_iff {o : GrowOracle}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (hes : EvalSound (profile o) noHost ev)
    (hev : EvalComplete (profile o) noHost ev)
    (hevc : ∀ s f e s' v, EvalExpr (profile o) noHost s f e s' f [v] → ev s f e = some (s', v))
    (hoff : ∀ e, IsOffset m e → ∀ (s : Store H) (f : Frame) (s' : Store H) (f' : Frame) vs,
      EvalExpr (profile o) noHost s f e s' f' vs → f' = f ∧ vs.length = 1)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    prepareDirect? ev s m xas = some (s', f', st) ↔
      st = m.start ∧ ∃ c, Instantiate (profile o) noHost s m xas c ∧
        Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩ :=
  ⟨prepareDirect?_sem hes hvalid, fun ⟨hst, _, hI, hS⟩ =>
    hst ▸ prepareDirect?_complete hev hevc hoff hI hS⟩

/-- `instantiateDirect?` characterised by the reduction semantics. -/
theorem instantiateDirect?_iff {o : GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiateDirect? s m xas = some (s', f', st) ↔
      st = m.start ∧ ∃ c, Instantiate (profile o) noHost s m xas c ∧
        Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩ :=
  ⟨prepareDirect?_sem evalConst?_evalSound hvalid, fun ⟨hst, _, hI, hS⟩ =>
    hst ▸ instantiateDirect?_complete hI hS⟩

/-- `instantiateInit?` is `instantiateDirect?` followed by the start call. -/
theorem instantiateInit?_eq (s : Store H) (m : Module) (xas : List ExternAddr) :
    instantiateInit? s m xas =
      (instantiateDirect? s m xas).map fun (s', f', st) => (⟨s', f', []⟩ : Config H).withStart st := by
  unfold instantiateInit? instantiateDirect? prepareDirect?
  cases hp : prepare? evalConst? s m xas with
  | none => rfl
  | some p =>
    cases hi : initSegments? evalConst? p.1.store p.1.frame m <;> simp [hi]

/-- `instantiateInit?` characterised by the reduction semantics. -/
theorem instantiateInit?_iff {o : GrowOracle} {s : Store H} {m : Module}
    {xas : List ExternAddr} {c' : Config H}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiateInit? s m xas = some c' ↔
      ∃ c, Instantiate (profile o) noHost s m xas c ∧ ∃ (s' : Store H) (f' : Frame),
        Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩ ∧
        c' = (⟨s', f', []⟩ : Config H).withStart m.start := by
  rw [instantiateInit?_eq, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨s', f', st⟩, h, rfl⟩
    obtain ⟨rfl, c, hI, hS⟩ := (instantiateDirect?_iff (o := o) hvalid).mp h
    exact ⟨c, hI, s', f', hS, rfl⟩
  · rintro ⟨c, hI, s', f', hS, rfl⟩
    exact ⟨(s', f', m.start), instantiateDirect?_complete hI hS, rfl⟩

end Silmaril.Proofs.Wasm.Instantiation
