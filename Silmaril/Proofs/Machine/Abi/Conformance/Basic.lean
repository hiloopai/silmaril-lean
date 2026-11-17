module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.X86.FnContract.Thms

/-! # ABI conformance: the lens, the bridge from first-return contracts, stuck states,
faithfulness -/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState)
open Silmaril.X86.FnContract (Spec AbiEntry FirstReturn Returned RunsIn)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {c : Code} {frame : Nat} {S : CallSpec A.V p}

/-! ## The modelled/carried split: a very well-behaved lens -/

theorem cond_cond {α : Type} (b : Bool) (s u w : α) :
    (bif b then w else bif b then u else s) = bif b then w else s := by
  cases b <;> rfl

theorem overwrite_self (F : FfiField → Bool) (s : Ffi.State) : overwrite F s s = s := by
  simp only [overwrite, Bool.cond_self]

theorem overwrite_overwrite (F : FfiField → Bool) (s u w : Ffi.State) :
    overwrite F (overwrite F s u) w = overwrite F s w := by
  simp only [overwrite, cond_cond]

theorem overwrite_agree {F : FfiField → Bool} {f : FfiField} (h : F f = true) (s u : Ffi.State) :
    f.Agree (overwrite F s u) u := by
  cases f <;> simp [FfiField.Agree, overwrite, h]

theorem overwrite_carried {F : FfiField → Bool} {f : FfiField} (h : F f = false)
    (s u : Ffi.State) : f.Agree (overwrite F s u) s := by
  cases f <;> simp [FfiField.Agree, overwrite, h]

/-- Two FFI states agreeing on every field are equal. -/
theorem eq_of_agree {s t : Ffi.State} (h : ∀ f : FfiField, f.Agree s t) : s = t := by
  obtain ⟨m, v, x, d, xm, mx, xc, fs⟩ := s
  obtain ⟨m', v', x', d', xm', mx', xc', fs'⟩ := t
  have := h FfiField.machine; have := h FfiField.vectors; have := h FfiField.x87
  have := h FfiField.direction; have := h FfiField.x87Mode; have := h FfiField.mxcsr
  have := h FfiField.x87Control; have := h FfiField.fsBase
  simp_all [FfiField.Agree]

/-- `overwrite F s u = s` exactly when `u` agrees with `s` on the fields `F`. -/
theorem overwrite_eq_self {F : FfiField → Bool} {s u : Ffi.State}
    (h : ∀ f, F f = true → f.Agree u s) : overwrite F s u = s := by
  refine eq_of_agree fun f => ?_
  cases hf : F f
  · exact overwrite_carried hf s u
  · have h1 := overwrite_agree hf s u
    have h2 := h f hf
    cases f <;> exact h1.trans h2

theorem Mach.store_store (M : Mach) (s : Ffi.State) (x y : M.σ) :
    M.store (M.store s x) y = M.store s y :=
  overwrite_overwrite _ _ _ _

theorem Mach.store_fills {s : Ffi.State} {x : M.σ} (h : M.Fills s x) : M.store s x = s :=
  overwrite_eq_self (M.fills_agree h)

theorem Mach.store_carried {f : FfiField} (h : M.models f = false) (s : Ffi.State) (y : M.σ) :
    f.Agree (M.store s y) s :=
  overwrite_carried h s _

theorem Mach.store_modelled {f : FfiField} (h : M.models f = true) (s : Ffi.State) (y : M.σ) :
    f.Agree (M.store s y) (M.view y) :=
  overwrite_agree h s _

/-- The machine field of a stored state is the stored machine state's core and memory. -/
theorem Mach.machine_store (M : Mach) (s : Ffi.State) (y : M.σ) :
    (M.store s y).machine = ⟨M.isa.core y, M.isa.mem y⟩ :=
  (Mach.store_modelled (f := .machine) M.models_machine s y).trans (M.machine_view y)

theorem Mach.fills_machine {s : Ffi.State} {x : M.σ} (h : M.Fills s x) :
    (⟨M.isa.core x, M.isa.mem x⟩ : MState) = s.machine :=
  (M.machine_view x).symm.trans (M.fills_agree h .machine M.models_machine)

theorem Mach.fills_core {s : Ffi.State} {x : M.σ} (h : M.Fills s x) :
    M.isa.core x = s.machine.core :=
  congrArg MState.core (Mach.fills_machine h)

theorem Mach.fills_mem {s : Ffi.State} {x : M.σ} (h : M.Fills s x) :
    M.isa.mem x = s.machine.memory :=
  congrArg MState.memory (Mach.fills_machine h)

/-- Whether `M` has returned from a completion of `s` is whether its stored state has. -/
theorem returned_iff {s : Ffi.State} {x : M.σ} (hx : M.Fills s x) (z : M.σ) :
    Returned M.isa x z ↔ ReturnedAt s (M.store s z) := by
  unfold Returned ReturnedAt
  rw [Mach.machine_store, Mach.fills_core hx, Mach.fills_mem hx]

/-- On a call, every field `M` does not model is carried. -/
theorem callModelOf_carried_of {f : FfiField} (hf : M.models f = false) {s t : Ffi.State}
    (h : t ∈ callModelOf M s) : f.Agree t s := by
  obtain ⟨_, -, y, -, rfl⟩ := h
  exact Mach.store_carried hf s y

theorem mem_callModelOf {s : Ffi.State} {x t : M.σ} (hx : M.Fills s x)
    (h : FirstReturn M.isa x t) : M.store s t ∈ callModelOf M s :=
  ⟨x, hx, t, h, rfl⟩

/-! ## Integer machines: the old definitions -/

theorem ofInt_models {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {f : FfiField} :
    (Mach.ofInt I hc hm).models f = true ↔ f = .machine := by
  cases f <;> simp [Mach.ofInt]

/-- On an integer machine, the call relation is the old one: the first return of `s.machine`,
the rest of the FFI state carried. -/
theorem mem_callModelOf_ofInt {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s t : Ffi.State} :
    t ∈ callModelOf (Mach.ofInt I hc hm) s ↔
      FirstReturn I s.machine t.machine ∧ t = { s with machine := t.machine } := by
  constructor
  · rintro ⟨_, rfl, y, h, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, e⟩; exact ⟨_, rfl, _, h, e⟩

theorem progress_ofInt_iff {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s : Ffi.State} :
    (∀ x, (Mach.ofInt I hc hm).Fills s x → (callFrom (Mach.ofInt I hc hm) s x).Nonempty) ↔
      (callModelOf (Mach.ofInt I hc hm) s).Nonempty := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h s.machine rfl
    exact ⟨t, _, rfl, ht⟩
  · rintro ⟨t, _, rfl, ht⟩ x rfl
    exact ⟨t, ht⟩

theorem noStuck_ofInt_iff {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s : Ffi.State} :
    NoStuck (Mach.ofInt I hc hm) s ↔
      ∀ y, RunsIn I (fun z => ¬ Returned I s.machine z) s.machine y →
        ¬ Returned I s.machine y → (I.step y).isSome := by
  constructor
  · intro h; exact h s.machine rfl
  · rintro h x rfl; exact h

theorem live_ofInt_iff {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s : Ffi.State} :
    (∀ x, (Mach.ofInt I hc hm).Fills s x → I.live x) ↔ I.live s.machine := by
  constructor
  · intro h; exact h s.machine rfl
  · rintro h x rfl; exact h

/-- Two runs of a deterministic machine from one state: one extends the other. -/
theorem runsIn_prefix {σ : Type} {I : Silmaril.X86.SegVC.Isa σ} {P : σ → Prop} {s t m : σ}
    (h₁ : RunsIn I P s t) (h₂ : RunsIn I P s m) : RunsIn I P t m ∨ RunsIn I P m t := by
  induction h₁ generalizing m with
  | refl => exact .inl h₂
  | step hp hs _ ih =>
    cases h₂ with
    | refl => exact .inr (.step hp hs (by assumption))
    | step _ hs' r =>
      rw [hs] at hs'
      cases hs'
      exact ih r

/-- A first return rules out stuck states before it. -/
theorem noStuck_of_firstReturn {σ : Type} {I : Silmaril.X86.SegVC.Isa σ} {x t : σ}
    (h : FirstReturn I x t) :
    ∀ y, RunsIn I (fun z => ¬ Returned I x z) x y → ¬ Returned I x y → (I.step y).isSome := by
  intro m hm hnot
  rcases runsIn_prefix h.1 hm with r | r
  · cases r with
    | refl => exact absurd h.2 hnot
    | step hp _ _ => exact absurd h.2 hp
  · cases r with
    | refl => exact absurd h.2 hnot
    | step _ hs _ => rw [hs]; rfl

/-- **A strict function contract gives a conformance row** (either mode). `S'` is a
first-return contract of the code on `M` (`Spec.Strict`); every completion of every admitted
call meets its entry, and each of its results is a conforming return. -/
theorem conforms_of_strict {S' : Spec M.σ} (hs : S'.Strict M.isa)
    (hdecl : Declares A hdr f p) (hext : c.off + c.len ≤ c.bytes.length)
    (hnv : ∃ a s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory)
    (hen : ∀ a mem, S.pre a mem → (∀ x, S.objects a mem x → c.Outside x) →
      ∃ s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory ∧
        (∀ x, S.objects a s.machine.memory x ↔ S.objects a mem x) ∧
        ∀ x, S.objects a mem x → s.machine.memory.bytes[x]? = mem.bytes[x]?)
    (habi : ∀ a s, Admit A M p c frame S a s → AbiEntry s.machine.core s.machine.memory)
    (hentry : ∀ a s x, Admit A M p c frame S a s → S.pre a s.machine.memory → M.Fills s x →
      S'.entry x)
    (hgood : ∀ a s x t, Admit A M p c frame S a s → S.pre a s.machine.memory → M.Fills s x →
      FirstReturn M.isa x t → S'.Result M.isa x t → Good A p frame S a s (M.store s t)) :
    Conforms A M mode hdr f p c frame S := by
  have fr : ∀ a s x, Admit A M p c frame S a s → S.pre a s.machine.memory → M.Fills s x →
      ∃ t, FirstReturn M.isa x t ∧ S'.Result M.isa x t := fun a s x ad pre hx =>
    hs.firstReturn (ad.live x hx)
      (by rw [Mach.fills_core hx, Mach.fills_mem hx]; exact habi a s ad)
      (hentry a s x ad pre hx)
  refine ⟨hdecl, hext, hnv, hen, fun a s ad pre x hx => ?_, fun _ a s ad pre x hx => ?_,
    fun a s ad pre t ht => ?_⟩
  · obtain ⟨t, h, -⟩ := fr a s x ad pre hx
    exact noStuck_of_firstReturn h
  · obtain ⟨t, h, -⟩ := fr a s x ad pre hx
    exact ⟨_, t, h, rfl⟩
  · obtain ⟨x, hx, y, fr', rfl⟩ := ht
    obtain ⟨t0, h, res⟩ := fr a s x ad pre hx
    rw [Silmaril.X86.FnContract.firstReturn_unique fr' h]
    exact hgood a s x t0 ad pre hx h res

/-- An admitted entry state is not a returned state (the return address is outside the code,
`rip` is inside it), on every completion. -/
theorem not_returned_entry (hlen : 0 < c.len) (hext : c.off + c.len ≤ c.bytes.length)
    {s : Ffi.State} (hp : Placed c s) {x : M.σ} (hx : M.Fills s x) : ¬ Returned M.isa x x := by
  intro h
  have := h.1
  rw [Mach.fills_core hx, Mach.fills_mem hx] at this
  exact hp.retOutside c.off (by omega) (this.symm.trans hp.pc)

/-- **Stuck code does not conform**, in either mode: every completion of an admitted call of a
conforming function takes a step at its entry. -/
theorem Conforms.steps (h : Conforms A M mode hdr f p c frame S) (hlen : 0 < c.len)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) {x : M.σ} (hx : M.Fills s x) : (M.isa.step x).isSome :=
  h.safe a s ad pre x hx _ (.refl _) (not_returned_entry hlen h.extent ad.placed hx)

/-- Conformance is not vacuous: an admitted call has a conforming return (total mode). -/
theorem Conforms.exists_good (h : Conforms A M .total hdr f p c frame S) :
    ∃ a s t, Admit A M p c frame S a s ∧ t ∈ callModelOf M s ∧ Good A p frame S a s t := by
  obtain ⟨a, s, ad, pre⟩ := h.nonvacuous
  obtain ⟨x, hx⟩ := M.fills_total s
  obtain ⟨t, ht⟩ := h.progress rfl a s ad pre x hx
  exact ⟨a, s, t, ad, ⟨x, hx, ht⟩, h.sound a s ad pre t ⟨x, hx, ht⟩⟩

/-- A total row is a safe row. -/
theorem Conforms.toSafe (h : Conforms A M .total hdr f p c frame S) :
    Conforms A M .safe hdr f p c frame S :=
  ⟨h.declared, h.extent, h.nonvacuous, h.enterable, h.safe, (fun h => nomatch h), h.sound⟩

/-- On an integer machine, the call relation carries the rest of the FFI state. -/
theorem callModelOf_carried {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s t : Ffi.State}
    (h : t ∈ callModelOf (Mach.ofInt I hc hm) s) :
    t.vectors = s.vectors ∧ t.x87 = s.x87 ∧ t.direction = s.direction ∧ t.x87Mode = s.x87Mode ∧
      t.mxcsr = s.mxcsr ∧ t.x87Control = s.x87Control ∧ t.fsBase = s.fsBase :=
  ⟨callModelOf_carried_of (f := .vectors) rfl h, callModelOf_carried_of (f := .x87) rfl h,
    callModelOf_carried_of (f := .direction) rfl h, callModelOf_carried_of (f := .x87Mode) rfl h,
    callModelOf_carried_of (f := .mxcsr) rfl h, callModelOf_carried_of (f := .x87Control) rfl h,
    callModelOf_carried_of (f := .fsBase) rfl h⟩

/-! ## Faithfulness: rows on `M` read on a reference machine -/

/-- On an integer machine, faithfulness to a reference relation says: wherever the machine
steps from `s.machine`, the reference machine's steps from `s` are exactly that step, the rest
of the FFI state unchanged. -/
theorem faithful_ofInt_iff_rel {R : Ref} {I : Silmaril.X86.SegVC.Isa MState}
    {hc : ∀ m, I.core m = m.core} {hm : ∀ m, I.mem m = m.memory} :
    Faithful R (Mach.ofInt I hc hm) ↔
      ∀ s m', I.step s.machine = some m' → ∀ t, R.Step s t ↔ t = { s with machine := m' } := by
  constructor
  · intro h s m' hs t
    have hs0 : (Mach.ofInt I hc hm).isa.step s.machine = some m' := hs
    constructor
    · intro hr
      obtain ⟨x', y', y'', rfl, -, he, hs', rfl⟩ :=
        h.bwd (fun _ => True) s s.machine s.machine rfl (.refl _) (by rw [hs0]; rfl) t hr
      have hy : y' = s.machine := congrArg Ffi.State.machine he
      subst hy
      rw [hs0] at hs'
      cases hs'
      rfl
    · rintro rfl
      exact h.fwd s s.machine rfl s.machine m' (.refl _) hs
  · intro h
    refine ⟨fun s x _ y y' _ hs => (h { s with machine := y } y' hs _).2 rfl,
      fun Q s x y hx hr hsome t ht => ?_⟩
    obtain ⟨y'', hy''⟩ := Option.isSome_iff_exists.1 hsome
    exact ⟨x, y, y'', hx, hr, rfl, hy'', (h { s with machine := y } y'' hy'' t).1 ht⟩

/-- On an integer machine and a deterministic reference, faithfulness is the old statement:
wherever the machine steps from `s.machine`, the reference machine takes the same step from
`s`. -/
theorem faithful_ofInt_iff {r : Ffi.State → Option Ffi.State} {I : Silmaril.X86.SegVC.Isa MState}
    {hc : ∀ m, I.core m = m.core} {hm : ∀ m, I.mem m = m.memory} :
    Faithful (Ref.ofFun r) (Mach.ofInt I hc hm) ↔
      ∀ s m', I.step s.machine = some m' → r s = some { s with machine := m' } := by
  rw [faithful_ofInt_iff_rel]
  constructor
  · intro h s m' hs; exact (h s m' hs _).2 rfl
  · intro h s m' hs t
    show r s = some t ↔ _
    rw [h s m' hs]
    exact ⟨fun e => (Option.some.inj e).symm, fun e => e ▸ rfl⟩

/-- The reference machine's runs from an admitted state, under the no-stuck condition, end at
stores of `M`'s runs from some completion. -/
theorem ref_runs_lift {R : Ref} (hf : Faithful R M) {s : Ffi.State} (hns : NoStuck M s) :
    ∀ {u t : Ffi.State}, R.RunsIn (fun v => ¬ ReturnedAt s v) u t →
      (∃ x y, M.Fills s x ∧ RunsIn M.isa (fun z => ¬ Returned M.isa x z) x y ∧
        u = M.store s y) →
      ∃ x y, M.Fills s x ∧ RunsIn M.isa (fun z => ¬ Returned M.isa x z) x y ∧
        t = M.store s y := by
  intro u t r
  induction r with
  | refl => exact id
  | step hp hs _ ih =>
    rintro ⟨x, y, hx, hr, rfl⟩
    have hnr : ¬ Returned M.isa x y := fun h => hp ((returned_iff hx y).1 h)
    have hr' : RunsIn M.isa (fun z => ¬ ReturnedAt s (M.store s z)) x y :=
      Silmaril.X86.FnContract.runsIn_mono (fun z h h' => h ((returned_iff hx z).2 h')) hr
    obtain ⟨x', y', y'', hx', hr'', he, hs', rfl⟩ :=
      hf.bwd (fun v => ¬ ReturnedAt s v) s x y hx hr' (hns x hx y hr hnr) _ hs
    refine ih ⟨x', y'', hx', ?_, rfl⟩
    have run := Silmaril.X86.FnContract.runsIn_trans hr''
      (.step (P := fun z => ¬ ReturnedAt s (M.store s z)) (by rw [he]; exact hp) hs' (.refl _))
    exact Silmaril.X86.FnContract.runsIn_mono (fun z h h' => h ((returned_iff hx' z).1 h')) run

/-- `M`'s runs from a completion, before the return, lift to the reference machine. -/
theorem ref_of_runs {R : Ref} (hf : Faithful R M) {s : Ffi.State} {x : M.σ} (hx : M.Fills s x)
    {m t : M.σ} (h : RunsIn M.isa (fun z => ¬ Returned M.isa x z) m t) :
    RunsIn M.isa (fun _ => True) x m →
      R.RunsIn (fun v => ¬ ReturnedAt s v) (M.store s m) (M.store s t) := by
  induction h with
  | refl => exact fun _ => .refl _
  | step hp hs _ ih =>
    intro hm
    exact .step (fun h => hp ((returned_iff hx _).2 h)) (hf.fwd s x hx _ _ hm hs)
      (ih (Silmaril.X86.FnContract.runsIn_trans hm (.step trivial hs (.refl _))))

/-- **A row on `M` holds on any reference machine `M` is faithful to**: every first return of the
reference machine from an admitted call is a conforming return, and in total mode there is one. -/
theorem Conforms.onRef {R : Ref} (hf : Faithful R M) (h : Conforms A M mode hdr f p c frame S)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) :
    (∀ t ∈ R.callModel s, Good A p frame S a s t) ∧
      (mode = .total → (R.callModel s).Nonempty) := by
  obtain ⟨x0, hx0⟩ := M.fills_total s
  refine ⟨fun t ht => ?_, fun hm => ?_⟩
  · obtain ⟨x, y, hx, hr, rfl⟩ :=
      ref_runs_lift hf (h.safe a s ad pre) ht.1 ⟨x0, x0, hx0, .refl _, (Mach.store_fills hx0).symm⟩
    exact h.sound a s ad pre _ ⟨x, hx, y, ⟨hr, (returned_iff hx y).2 ht.2⟩, rfl⟩
  · obtain ⟨t, y, fr, rfl⟩ := h.progress hm a s ad pre x0 hx0
    have r := ref_of_runs hf hx0 fr.1 (.refl _)
    rw [Mach.store_fills hx0] at r
    exact ⟨M.store s y, r, (returned_iff hx0 y).1 fr.2⟩

end Silmaril.Proofs.Machine.Abi.Conformance

end
