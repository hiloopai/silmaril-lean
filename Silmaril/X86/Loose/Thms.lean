module

public import Silmaril.X86.Loose.Defs
public import Silmaril.X86.RelIsa.Thms
import Silmaril.Proofs.X86.Loose.Machine

/-!
# `X86Loose`: what is proved

Every theorem is generic in the state type `σ` (any `Views`), the form index `Φ`, the table
`D` and the form specifications `S`. Longer proofs are in
`Silmaril/Proofs/X86/Loose/Machine.lean`.

* `X86Loose.antitone_D`: a larger table gives a smaller machine (`Le`), so proofs transfer by
  `Must.of_le`; `X86Loose.antitone_S`: so do form specifications that specify more, each
  form more tightly (`FormSpec.Tightens`);
* `X86Loose.step_stop_iff`, `X86Loose.step_stop_of_not_atSpecified`,
  `X86Loose.not_step_stop`: the machine may stop exactly where every specified entry at
  `rip` is `unspecified`;
* `X86Loose.step_ok_of_spec`, `X86Loose.step_ok_upd`: a step from a specified entry is an
  allowed success, as a view update;
* `X86Loose.must_of_spec`: the one-instruction `Must` rule;
* non-vacuity: `X86Loose.exists_step` (a successor exists where the entries at `rip` agree on
  form and length), `X86Loose.not_must_of_not_atSpecified`;
* footprint: `must_keeps_of_step`, `X86Loose.step_keeps_fs`, `X86Loose.step_keeps_ext`,
  **`X86Loose.must_keeps_fs`** and **`X86Loose.must_keeps_ext`**: along a `Must` run whose
  steps are taken from specified states, `fsBase` and every `ExtFrame` extension are kept;
* effects: `Effect.regAfter_of_not_mem`, `Effect.Admits.read_of_not_mem`,
  `FormSpec.sem_iff_of_specified`, `FormSpec.sem_of_unspecified`, `FormSpec.Tightens.refl`,
  `FormSpec.Tightens.trans`.
-/

@[expose] public section

namespace Silmaril.X86.Loose

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Views Res Must Le ExtFrame)

variable {Φ σ : Type}

/-! ## Effects and form specifications -/

/-- A register that no listed write names keeps its value. -/
theorem Effect.regAfter_of_not_mem {e : Effect} {c : State} {r : Reg}
    (h : r ∉ e.regs.map (·.1)) : e.regAfter c r = c.read r :=
  Proofs.X86.Loose.regAfter_of_not_mem h

/-- **Footprint**: a register outside `regs ∪ havocRegs` is kept. -/
theorem Effect.Admits.read_of_not_mem {e : Effect} {c c' : State} {m m' : Memory}
    (h : e.Admits c m c' m') {r : Reg} (hr : r ∉ e.regs.map (·.1)) (hh : r ∉ e.havocRegs) :
    c'.read r = c.read r := by
  rw [h.regs r hh, Effect.regAfter_of_not_mem hr]

/-- Where a form is specified, its allowed results are exactly the allowed successes. -/
theorem FormSpec.sem_iff_of_specified {F : FormSpec} {c : State} {m : Memory} {l : Nat}
    (hu : ¬ F.unspecified c m l) (res : Silmaril.X86.Ext.Result) :
    F.sem c m l res ↔ ∃ c' m', res = .ok c' m' ∧ F.allows c m l c' m' :=
  ⟨fun h => h.resolve_left hu, Or.inr⟩

/-- Where a form is unspecified, it allows every result. -/
theorem FormSpec.sem_of_unspecified {F : FormSpec} {c : State} {m : Memory} {l : Nat}
    (hu : F.unspecified c m l) (res : Silmaril.X86.Ext.Result) : F.sem c m l res :=
  Or.inl hu

theorem FormSpec.Tightens.refl (F : FormSpec) : F.Tightens F := fun _ _ _ _ h => h

theorem FormSpec.Tightens.trans {F F' F'' : FormSpec} (h₁ : F.Tightens F')
    (h₂ : F'.Tightens F'') : F.Tightens F'' :=
  fun c m l res h => h₁ c m l res (h₂ c m l res h)

/-! ## The machine -/

@[simp] theorem X86Loose.rel_step (D : DTable Φ) (S : Sigma Φ) (V : Views σ) :
    (X86Loose.rel D S V).step = X86Loose.step D S V := rfl

@[simp] theorem X86Loose.rel_toViews (D : DTable Φ) (S : Sigma Φ) (V : Views σ) :
    (X86Loose.rel D S V).toViews = V := rfl

/-- **Antitone in the table**: more entries constrain more. -/
theorem X86Loose.antitone_D {D D' : DTable Φ} {S : Sigma Φ} {V : Views σ}
    (hD : ∀ e ∈ D, e ∈ D') : Le (X86Loose.rel D' S V) (X86Loose.rel D S V) :=
  ⟨rfl, fun _ h => ⟨fun e hm => h.1 e (hD e hm), h.2⟩⟩

/-- **Antitone in the form specifications**: specifications `S'` that specify every form `S`
specifies, each more tightly, give a smaller machine. -/
theorem X86Loose.antitone_S {D : DTable Φ} {S S' : Sigma Φ} {V : Views σ}
    (hS : ∀ i F, S i = some F → ∃ F', S' i = some F' ∧ F.Tightens F') :
    Le (X86Loose.rel D S' V) (X86Loose.rel D S V) :=
  Proofs.X86.Loose.antitone_S hS

/-- **When the loose machine may stop**: exactly when every specified entry at `rip` is
`unspecified` there (in particular at every unlisted state). -/
theorem X86Loose.step_stop_iff {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s : σ} :
    X86Loose.step D S V s .stop ↔ ∀ e ∈ D, AtEntry e (V.core s) (V.mem s) → ∀ F,
      S e.form = some F → F.unspecified (V.core s) (V.mem s) e.bytes.length :=
  Proofs.X86.Loose.step_stop_iff

/-- Off `AtSpecified`, the loose machine may stop. -/
theorem X86Loose.step_stop_of_not_atSpecified {D : DTable Φ} {S : Sigma Φ} {V : Views σ}
    {s : σ} (h : ¬ AtSpecified D S V s) : X86Loose.step D S V s .stop :=
  X86Loose.step_stop_iff.2 fun e hm hat F hF =>
    Classical.byContradiction fun hu => h ⟨e, hm, hat, F, hF, hu⟩

/-- On `AtSpecified`, the loose machine cannot stop. -/
theorem X86Loose.not_step_stop {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s : σ}
    (h : AtSpecified D S V s) : ¬ X86Loose.step D S V s .stop := fun hs =>
  let ⟨e, hm, hat, F, hF, hu⟩ := h
  hu (X86Loose.step_stop_iff.1 hs e hm hat F hF)

/-- **A step from a specified entry is an allowed success**, as a view update. -/
theorem X86Loose.step_ok_of_spec {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s t : σ}
    {e : DEntry Φ} {F : FormSpec} (hm : e ∈ D) (hat : AtEntry e (V.core s) (V.mem s))
    (hF : S e.form = some F) (hu : ¬ F.unspecified (V.core s) (V.mem s) e.bytes.length)
    (h : X86Loose.step D S V s (.ok t)) :
    ∃ c' m', t = V.upd s c' m' ∧ F.allows (V.core s) (V.mem s) e.bytes.length c' m' :=
  Proofs.X86.Loose.step_ok_of_spec hm hat hF hu h

/-- A step from an `AtSpecified` state is a view update that keeps `fsBase`. -/
theorem X86Loose.step_ok_upd {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s t : σ}
    (hA : AtSpecified D S V s) (h : X86Loose.step D S V s (.ok t)) :
    ∃ c' m', t = V.upd s c' m' ∧ c'.fsBase = (V.core s).fsBase :=
  let ⟨_, hm, hat, _, hF, hu⟩ := hA
  let ⟨c', m', ht, ha⟩ := X86Loose.step_ok_of_spec hm hat hF hu h
  ⟨c', m', ht, (FormSpec.allows_fs _ ha)⟩

/-- **The one-instruction `Must` rule**: at a specified entry, if every allowed successor
must reach `Q`, so does the state. No uniqueness of the entry at `rip` is needed. -/
theorem X86Loose.must_of_spec {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {R Q : σ → Prop}
    {s : σ} {e : DEntry Φ} {F : FormSpec} (hR : R s) (hm : e ∈ D)
    (hat : AtEntry e (V.core s) (V.mem s)) (hF : S e.form = some F)
    (hu : ¬ F.unspecified (V.core s) (V.mem s) e.bytes.length)
    (h : ∀ c' m', F.allows (V.core s) (V.mem s) e.bytes.length c' m' →
      Must (X86Loose.rel D S V) R Q (V.upd s c' m')) :
    Must (X86Loose.rel D S V) R Q s :=
  .step hR (X86Loose.not_step_stop ⟨e, hm, hat, F, hF, hu⟩) fun _ ht =>
    let ⟨c', m', h1, ha⟩ := X86Loose.step_ok_of_spec hm hat hF hu ht
    h1 ▸ h c' m' ha

/-- **Non-vacuity**: where every entry at `rip` has the form and length of an entry whose
form is specified and not `unspecified` there, and `live` holds everywhere, the loose
machine has a successor. -/
theorem X86Loose.exists_step {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s : σ}
    {e : DEntry Φ} {F : FormSpec} (hlive : ∀ t, V.live t) (hF : S e.form = some F)
    (hu : ¬ F.unspecified (V.core s) (V.mem s) e.bytes.length)
    (huniq : ∀ e' ∈ D, AtEntry e' (V.core s) (V.mem s) →
      e'.form = e.form ∧ e'.bytes.length = e.bytes.length) :
    ∃ t, X86Loose.step D S V s (.ok t) :=
  Proofs.X86.Loose.exists_step hlive hF hu huniq

/-- **Non-vacuity, negative**: from a state that is not `AtSpecified` (for example an
unlisted one), the loose machine reaches nothing that does not already hold. -/
theorem X86Loose.not_must_of_not_atSpecified {D : DTable Φ} {S : Sigma Φ} {V : Views σ}
    {R Q : σ → Prop} {s : σ} (hQ : ¬ Q s) (h : ¬ AtSpecified D S V s) :
    ¬ Must (X86Loose.rel D S V) R Q s :=
  RelIsa.not_must_of_stop hQ (X86Loose.step_stop_of_not_atSpecified h)

/-! ## Footprint -/

/-- **Invariance along `Must`**: if every step from an `R'`-state keeps `f`, then a `Must`
proof whose steps are taken from `R ⊓ R'` reaches `Q` with `f` unchanged. -/
theorem must_keeps_of_step {A : RelIsa σ} {α : Type} (f : σ → α) {R R' Q : σ → Prop}
    (hf : ∀ s t, R' s → A.step s (.ok t) → f t = f s) {s : σ}
    (h : Must A (fun x => R x ∧ R' x) Q s) : Must A R (fun t => Q t ∧ f t = f s) s :=
  Proofs.X86.Loose.must_keeps_of_step f hf h

/-- A loose step from a specified state keeps `fsBase`. -/
theorem X86Loose.step_keeps_fs {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s t : σ}
    (hA : AtSpecified D S V s) (h : X86Loose.step D S V s (.ok t)) :
    (V.core t).fsBase = (V.core s).fsBase := by
  obtain ⟨c', m', rfl, hfs⟩ := X86Loose.step_ok_upd hA h
  rw [V.core_upd]; exact hfs

/-- A loose step from a specified state keeps every extension. -/
theorem X86Loose.step_keeps_ext {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {E : Type}
    (X : ExtFrame V E) {s t : σ} (hA : AtSpecified D S V s)
    (h : X86Loose.step D S V s (.ok t)) : X.ext t = X.ext s := by
  obtain ⟨c', m', rfl, _⟩ := X86Loose.step_ok_upd hA h
  exact X.ext_upd s c' m'

/-- **`fsBase` is kept** along every `Must` run whose steps are taken from specified states. -/
theorem X86Loose.must_keeps_fs {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {R Q : σ → Prop}
    {s : σ} (h : Must (X86Loose.rel D S V) (fun x => R x ∧ AtSpecified D S V x) Q s) :
    Must (X86Loose.rel D S V) R (fun t => Q t ∧ (V.core t).fsBase = (V.core s).fsBase) s :=
  must_keeps_of_step (fun x => (V.core x).fsBase)
    (fun _ _ hA ht => X86Loose.step_keeps_fs hA ht) h

/-- **The extended state is kept** along every `Must` run whose steps are taken from
specified states. -/
theorem X86Loose.must_keeps_ext {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {E : Type}
    (X : ExtFrame V E) {R Q : σ → Prop} {s : σ}
    (h : Must (X86Loose.rel D S V) (fun x => R x ∧ AtSpecified D S V x) Q s) :
    Must (X86Loose.rel D S V) R (fun t => Q t ∧ X.ext t = X.ext s) s :=
  must_keeps_of_step X.ext (fun _ _ hA ht => X86Loose.step_keeps_ext X hA ht) h

end Silmaril.X86.Loose
