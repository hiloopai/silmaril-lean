module

public import Silmaril.X86.FnContract.Must.Defs
public import Silmaril.X86.RelIsa.Thms
public import Silmaril.X86.RelIsa.Loosen.Thms
public import Silmaril.X86.FnContract.Thms
/-!
# Proofs: demonic function contracts (`FnContract.Must`)

Names are in `Silmaril.X86.FnContract`, so that the header `FnContract/Must/Thms.lean`
exports them.

* views: `Spec.resultV_ofIsa`, `returnedV_ofIsa` (and the `loosen` forms);
* bridges to the deterministic notions: `Spec.Strict.must`, `Spec.Must.strict`,
  `Spec.must_ofIsa_iff`; `Spec.TotalIn.mustInLoosen`, `Spec.TotalIn.mustLoosen`,
  `Spec.Strict.mustLoosen`;
* transfer: `Spec.MustIn.of_le`, `Spec.Must.of_le`, `Spec.Must.strict_of_le`,
  `Spec.Must.of_sim`; `ViewsRel.refl`, `Spec.comap_eq_sub`, `viewsRel_infoLe_mstate`;
* structure: `Spec.MustIn.mono`, `Spec.MustIn.sub`, `Spec.MustIn.frame`, `Spec.MustIn.call`,
  `Spec.Must.call`, `Spec.MustIn.exists_result`; `progress_loosen`.
-/

@[expose] public section

namespace Silmaril.X86.FnContract

open Silmaril.X86 (State Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Views ofIsa loosen Le Sim)

variable {σ τ : Type} {S T : Spec σ} {I : Isa σ} {A C : RelIsa σ} {P Q : σ → σ → Prop}

/-! ## Views of the deterministic machines -/

theorem Spec.resultV_ofIsa {s t : σ} : S.ResultV (Views.ofIsa I) s t ↔ S.Result I s t :=
  ⟨fun h => ⟨h.silent, h.abi, h.frame, h.post⟩, fun h => ⟨h.silent, h.abi, h.frame, h.post⟩⟩

theorem returnedV_ofIsa {s m : σ} : ReturnedV (Views.ofIsa I) s m ↔ Returned I s m := Iff.rfl

/-! ## Bridges to the deterministic notions -/

/-- **A strict (first-return) contract is a demonic one on the same deterministic machine.** -/
theorem Spec.Strict.must (h : S.Strict I) : S.Must (ofIsa I) := by
  intro s hl ha he
  obtain ⟨t, r, res⟩ := h s hl ha he
  exact RelIsa.must_ofIsa_iff.2
    ⟨t, runsIn_mono (fun m hm => ⟨hm, trivial⟩) r, Spec.resultV_ofIsa.2 res⟩

/-- **The converse**: a demonic contract on a deterministic machine is strict. -/
theorem Spec.Must.strict (h : S.Must (ofIsa I)) : S.Strict I := by
  intro s hl ha he
  obtain ⟨t, r, res⟩ := RelIsa.must_ofIsa_iff.1 (h s hl ha he)
  exact ⟨t, runsIn_mono (fun m hm => hm.1) r, Spec.resultV_ofIsa.1 res⟩

theorem Spec.must_ofIsa_iff : S.Must (ofIsa I) ↔ S.Strict I :=
  ⟨Spec.Must.strict, Spec.Strict.must⟩

/-- **Tier A, general form.** A `TotalIn` run that never passes the entry's return, satisfies
`Q` and stays inside `P` is a demonic contract of the loosening `loosen I P`. -/
theorem Spec.TotalIn.mustInLoosen {Pl : σ → Prop}
    (h : S.TotalIn I fun s m => (¬ Returned I s m ∧ Q s m) ∧ Pl m) :
    S.MustIn (loosen I Pl) Q := by
  intro s hl ha he
  obtain ⟨t, r, res⟩ := h s hl ha he
  exact RelIsa.must_loosen_of_runsIn r (Spec.resultV_ofIsa.2 res)

/-- **Tier A**: a first-return run inside `P` gives a demonic contract
of `loosen I P`. -/
theorem Spec.TotalIn.mustLoosen {Pl : σ → Prop}
    (h : S.TotalIn I fun s m => ¬ Returned I s m ∧ Pl m) : S.Must (loosen I Pl) :=
  Spec.TotalIn.mustInLoosen
    (totalIn_mono (fun _ _ hm => ⟨⟨hm.1, trivial⟩, hm.2⟩) h)

/-- **Tier A0**: a strict contract gives a demonic contract of the everywhere-loosened
machine `loosen I ⊤`. -/
theorem Spec.Strict.mustLoosen (h : S.Strict I) : S.Must (loosen I fun _ => True) :=
  Spec.TotalIn.mustLoosen (totalIn_mono (fun _ _ hm => ⟨hm, trivial⟩) h)

/-! ## Transfer -/

/-- **Transfer along refinement**: a demonic contract of `A` holds for every `C` with fewer
behaviours. -/
theorem Spec.MustIn.of_le (hle : Le C A) (h : S.MustIn A P) : S.MustIn C P := by
  intro s hl ha he
  have hv := hle.views
  have hlA : A.live s := by rw [← hle.live_iff]; exact hl
  have ha' : AbiEntry (A.core s) (A.mem s) := by
    rw [show A.core = C.core from congrArg Views.core hv.symm,
      show A.mem = C.mem from congrArg Views.mem hv.symm]
    exact ha
  have hm := h s hlA ha' he
  rw [← hv] at hm
  exact RelIsa.Must.of_le hle hl hm

theorem Spec.Must.of_le (hle : Le C A) (h : S.Must A) : S.Must C := Spec.MustIn.of_le hle h

/-- **What an existing consumer needs**: a demonic contract on `A` is a strict contract of
every deterministic machine `C` whose relational reading refines `A`. -/
theorem Spec.Must.strict_of_le {C : Isa σ} (hle : Le (ofIsa C) A) (h : S.Must A) :
    S.Strict C :=
  Spec.Must.strict (Spec.Must.of_le hle h)

/-- `Spec.Must.strict_of_le` for the loosening: every demonic contract on `loosen I P` is a
strict contract of `I`. -/
theorem Spec.Must.strict_of_loosen {Pl : σ → Prop} (h : S.Must (loosen I Pl)) : S.Strict I :=
  Spec.Must.strict_of_le RelIsa.le_loosen h

/-- **Transfer along a simulation.** A demonic contract on the abstract machine `A` gives a
demonic contract of the pulled-back spec on every concrete machine `C` simulated by `A`
along `Rel`, if `Rel` keeps the System V observations (`ViewsRel`). -/
theorem Spec.Must.of_sim {C : RelIsa τ} {A : RelIsa σ} {Rel : τ → σ → Prop} {S : Spec σ}
    (hs : Sim C A Rel) (hv : ViewsRel C.toViews A.toViews Rel) (h : S.Must A) :
    (S.comapRel Rel).Must C := by
  intro c hl ha he
  obtain ⟨a, hr, hea⟩ := he
  have hla : A.live a := hs.live hr hl
  have hcore : ∀ {c a}, Rel c a → ∀ r, (C.core c).read r = (A.core a).read r := by
    intro c a h r
    show (C.core c).regs r = (A.core a).regs r
    rw [hv.regs h]
  have hret : ∀ {c a}, Rel c a →
      FnContract.retOf (C.core c) (C.mem c) = FnContract.retOf (A.core a) (A.mem a) := by
    intro c a h
    simp only [FnContract.retOf, hcore h, hv.mem h]
  have haa : AbiEntry (A.core a) (A.mem a) := by
    refine ⟨?_, ?_⟩
    · rw [← hcore hr]; exact ha.aligned
    · rw [← hret hr, ← hcore hr, ← hv.mem hr]; exact ha.returnAddress
  have hm := RelIsa.Must.of_sim (R' := fun m => ¬ ReturnedV C.toViews c m ∧ True) hs
    (fun c' a' hr' hR => ⟨fun hret' => hR.1
      ⟨by rw [← hv.rip hr', hret'.1, hret hr], by rw [← hcore hr', hret'.2, hcore hr]⟩,
      trivial⟩)
    hr hl (h a hla haa hea)
  refine RelIsa.Must.mono (fun _ h => h) ?_ hm
  rintro t ⟨b, hrb, res⟩
  refine ⟨hv.silent hr hrb res.silent, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hv.rip hrb, res.abi.pc, hret hr]
  · rw [hcore hrb, res.abi.stack, hcore hr]
  · intro r hr'
    rw [hcore hrb, res.abi.calleeSaved r hr', hcore hr]
  · rw [hv.mem hr, hv.mem hrb]
    exact res.frame.mono fun x hx => ⟨a, hr, hea, hx⟩
  · exact ⟨a, b, hr, hea, hrb, res.post⟩

/-- The identity abstraction keeps the observations. -/
theorem ViewsRel.refl (V : Views σ) : ViewsRel V V Eq where
  regs h := by cases h; rfl
  rip h := by cases h; rfl
  mem h := by cases h; rfl
  silent h₁ h₂ hs := by cases h₁; cases h₂; exact hs

/-- Pulling back along the identity loses nothing (`S.comapRel Eq` refines `S`). -/
theorem Spec.comap_eq_sub : (S.comapRel Eq).Sub S :=
  ⟨fun s he => ⟨s, rfl, he⟩, fun _ _ _ ⟨_, e, _, hf⟩ => e ▸ hf,
    fun _ _ _ ⟨_, _, e₁, _, e₂, hp⟩ => e₁ ▸ e₂ ▸ hp⟩

/-- **The information order on `MState` keeps the System V observations** (the case where
registers, `rip` and memory are equal, only the flags may differ). -/
theorem viewsRel_infoLe_mstate :
    ViewsRel Views.mstate Views.mstate
      (fun c a => RelIsa.InfoLe (c.core, c.memory) (a.core, a.memory)) where
  regs h := h.1
  rip h := h.2.1
  mem h := h.2.2.2.1
  silent _ _ _ := rfl

/-! ## Structure -/

/-- Weaken the run predicate. -/
theorem Spec.MustIn.mono (hP : ∀ s m, P s m → Q s m) (h : S.MustIn A P) : S.MustIn A Q :=
  fun s hl ha he =>
    RelIsa.Must.mono (fun m hm => ⟨hm.1, hP s m hm.2⟩) (fun _ h => h) (h s hl ha he)

/-- **Refinement of specs** (`Spec.Sub`, as `FnContract.mono`). -/
theorem Spec.MustIn.sub (hsub : S.Sub T) (h : S.MustIn A P) : T.MustIn A P := by
  intro s hl ha he
  refine RelIsa.Must.mono (fun _ h => h) ?_ (h s hl ha (hsub.entry s he))
  intro t res
  exact ⟨res.silent, res.abi, res.frame.mono fun x hx => hsub.footprint s x he hx,
    hsub.post s t he res.post⟩

/-- **The frame rule** (as `FnContract.frame`): a memory predicate untouched by the
footprint holds after the call if it held before. -/
theorem Spec.MustIn.frame (F : Memory → Prop) (hF : ∀ s, Stable (S.footprint s) F)
    (h : S.MustIn A P) : (S.frameV A.toViews F).MustIn A P := by
  intro s hl ha he
  refine RelIsa.Must.mono (fun _ h => h) ?_ (h s hl ha he.1)
  intro t res
  exact ⟨res.silent, res.abi, res.frame, res.post, hF s _ _ res.frame he.2⟩

/-- **A contracted call inside a run.** At an entry of `S`, if every state the callee may
step from is allowed by the caller's step condition `R`, and the caller must reach `Q2`
from every result state, the caller must reach `Q2` from the entry. -/
theorem Spec.MustIn.call (h : S.MustIn A P) {s : σ} (hl : A.live s)
    (ha : AbiEntry (A.core s) (A.mem s)) (he : S.entry s) {R Q2 : σ → Prop}
    (hR : ∀ m, ¬ ReturnedV A.toViews s m → P s m → R m)
    (k : ∀ t, S.ResultV A.toViews s t → RelIsa.Must A R Q2 t) : RelIsa.Must A R Q2 s :=
  RelIsa.Must.bind (RelIsa.Must.mono (fun m hm => hR m hm.1 hm.2) (fun _ h => h)
    (h s hl ha he)) k

/-- `Spec.MustIn.call` for `Spec.Must`. -/
theorem Spec.Must.call (h : S.Must A) {s : σ} (hl : A.live s)
    (ha : AbiEntry (A.core s) (A.mem s)) (he : S.entry s) {R Q2 : σ → Prop}
    (hR : ∀ m, ¬ ReturnedV A.toViews s m → R m)
    (k : ∀ t, S.ResultV A.toViews s t → RelIsa.Must A R Q2 t) : RelIsa.Must A R Q2 s :=
  Spec.MustIn.call h hl ha he (fun m hm _ => hR m hm) k

/-- On a machine with `Progress`, a demonic contract has a run to a result state. -/
theorem Spec.MustIn.exists_result (hp : RelIsa.Progress A) (h : S.MustIn A P) {s : σ}
    (hl : A.live s) (ha : AbiEntry (A.core s) (A.mem s)) (he : S.entry s) :
    ∃ t, RelIsa.RunsInR A (fun m => ¬ ReturnedV A.toViews s m ∧ P s m) s t ∧
      S.ResultV A.toViews s t :=
  RelIsa.Must.exists_run hp hl (h s hl ha he)

/-- The loosening of a machine always has an outcome (`stop` where it is unconstrained). -/
theorem progress_loosen {Pl : σ → Prop} : RelIsa.Progress (loosen I Pl) := by
  intro s hl
  by_cases hp : Pl s
  · cases e : I.step s with
    | some t => exact ⟨.ok t, (RelIsa.loosen_step_of_step hp e hl).2 rfl⟩
    | none => exact ⟨.stop, RelIsa.loosen_step_iff.2
        ⟨fun t _ he => (by rw [e] at he; cases he), fun _ e => by cases e⟩⟩
  · exact ⟨.stop, RelIsa.loosen_step_iff.2 ⟨fun _ hp' => absurd hp' hp, fun _ e => by cases e⟩⟩

end Silmaril.X86.FnContract
