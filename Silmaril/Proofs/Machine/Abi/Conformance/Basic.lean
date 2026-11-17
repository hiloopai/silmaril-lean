module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.X86.FnContract.Thms

/-! # ABI conformance: the bridge from first-return contracts, stuck states, faithfulness -/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState)
open Silmaril.X86.FnContract (Spec AbiEntry FirstReturn Returned RunsIn)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {c : Code} {frame : Nat} {S : CallSpec A.V p}

/-- The machine core of a stored state is the stored machine state's. -/
theorem core_load_store (M : Mach) (s : Ffi.State) (y : M.σ) :
    M.isa.core (M.load (M.store s y)) = M.isa.core y := by
  rw [M.core_load, M.machine_store]

/-- Whether a stored state has returned is whether the machine state has. -/
theorem returned_load_store (M : Mach) {r : M.σ} {s : Ffi.State} {y : M.σ} :
    Returned M.isa r (M.load (M.store s y)) ↔ Returned M.isa r y := by
  unfold Returned; rw [core_load_store]

theorem mem_callModelOf {s : Ffi.State} {t : M.σ} (h : FirstReturn M.isa (M.load s) t) :
    M.store s t ∈ callModelOf M s :=
  ⟨t, h, rfl⟩

/-- On an integer machine, the call relation is the old one: the first return of `s.machine`,
the rest of the FFI state carried. -/
theorem mem_callModelOf_ofInt {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s t : Ffi.State} :
    t ∈ callModelOf (Mach.ofInt I hc hm) s ↔
      FirstReturn I s.machine t.machine ∧ t = { s with machine := t.machine } := by
  constructor
  · rintro ⟨y, h, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, e⟩; exact ⟨_, h, e⟩

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
theorem noStuck_of_firstReturn {s : Ffi.State} {t : M.σ} (h : FirstReturn M.isa (M.load s) t) :
    NoStuck M s := by
  intro m hm hnot
  rcases runsIn_prefix h.1 hm with r | r
  · cases r with
    | refl => exact absurd h.2 hnot
    | step hp _ _ => exact absurd h.2 hp
  · cases r with
    | refl => exact absurd h.2 hnot
    | step _ hs _ => rw [hs]; rfl

/-- **A strict function contract gives a conformance row** (either mode). `S'` is a
first-return contract of the code on `M` (`Spec.Strict`); every admitted call meets its entry,
and each of its results is a conforming return. -/
theorem conforms_of_strict {S' : Spec M.σ} (hs : S'.Strict M.isa)
    (hdecl : Declares A hdr f p) (hext : c.off + c.len ≤ c.bytes.length)
    (hnv : ∃ a s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory)
    (hen : ∀ a mem, S.pre a mem → (∀ x, S.objects a mem x → c.Outside x) →
      ∃ s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory ∧
        (∀ x, S.objects a s.machine.memory x ↔ S.objects a mem x) ∧
        ∀ x, S.objects a mem x → s.machine.memory.bytes[x]? = mem.bytes[x]?)
    (habi : ∀ a s, Admit A M p c frame S a s →
      AbiEntry (M.isa.core (M.load s)) (M.isa.mem (M.load s)))
    (hentry : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory →
      S'.entry (M.load s))
    (hgood : ∀ a s t, Admit A M p c frame S a s → S.pre a s.machine.memory →
      FirstReturn M.isa (M.load s) t → S'.Result M.isa (M.load s) t →
      Good A p frame S a s (M.store s t)) :
    Conforms A M mode hdr f p c frame S := by
  refine ⟨hdecl, hext, hnv, hen, fun a s ad pre => ?_, fun _ a s ad pre => ?_,
    fun a s ad pre t ht => ?_⟩
  · obtain ⟨t, fr, -⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    exact noStuck_of_firstReturn fr
  · obtain ⟨t, fr, -⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    exact ⟨_, mem_callModelOf fr⟩
  · obtain ⟨t0, fr, res⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    obtain ⟨y, fr', heq⟩ := ht
    have := Silmaril.X86.FnContract.firstReturn_unique fr' fr
    rw [heq, this]
    exact hgood a s t0 ad pre fr res

/-- An admitted entry state is not a returned state (the return address is outside the code,
`rip` is inside it). -/
theorem not_returned_entry (hlen : 0 < c.len) (hext : c.off + c.len ≤ c.bytes.length)
    {s : Ffi.State} (hp : Placed c s) : ¬ Returned M.isa (M.load s) (M.load s) := by
  intro h
  have := h.1
  rw [M.core_load, M.mem_load] at this
  exact hp.retOutside c.off (by omega) (this.symm.trans hp.pc)

/-- **Stuck code does not conform**, in either mode: an admitted call of a conforming function
takes a step at its entry. -/
theorem Conforms.steps (h : Conforms A M mode hdr f p c frame S) (hlen : 0 < c.len)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) : (M.isa.step (M.load s)).isSome :=
  h.safe a s ad pre _ (.refl _) (not_returned_entry hlen h.extent ad.placed)

/-- Conformance is not vacuous: an admitted call has a conforming return (total mode). -/
theorem Conforms.exists_good (h : Conforms A M .total hdr f p c frame S) :
    ∃ a s t, Admit A M p c frame S a s ∧ t ∈ callModelOf M s ∧ Good A p frame S a s t := by
  obtain ⟨a, s, ad, pre⟩ := h.nonvacuous
  obtain ⟨t, ht⟩ := h.progress rfl a s ad pre
  exact ⟨a, s, t, ad, ht, h.sound a s ad pre t ht⟩

/-- A total row is a safe row. -/
theorem Conforms.toSafe (h : Conforms A M .total hdr f p c frame S) :
    Conforms A M .safe hdr f p c frame S :=
  ⟨h.declared, h.extent, h.nonvacuous, h.enterable, h.safe, (fun h => nomatch h), h.sound⟩

/-- On an integer machine, the call relation carries the rest of the FFI state. -/
theorem callModelOf_carried {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s t : Ffi.State}
    (h : t ∈ callModelOf (Mach.ofInt I hc hm) s) :
    t.vectors = s.vectors ∧ t.x87 = s.x87 ∧ t.direction = s.direction ∧ t.x87Mode = s.x87Mode ∧
      t.mxcsr = s.mxcsr ∧ t.x87Control = s.x87Control ∧ t.fsBase = s.fsBase := by
  obtain ⟨_, -, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Faithfulness: rows on `M` read on a reference machine -/

/-- On an integer machine, faithfulness is the old statement: wherever the machine steps from
`s.machine`, the reference machine takes the same step from `s`. -/
theorem faithful_ofInt_iff {R : Ref} {I : Silmaril.X86.SegVC.Isa MState}
    {hc : ∀ m, I.core m = m.core} {hm : ∀ m, I.mem m = m.memory} :
    Faithful R (Mach.ofInt I hc hm) ↔
      ∀ s m', I.step s.machine = some m' → R.step s = some { s with machine := m' } := by
  constructor
  · intro h s m' hs; exact h s s.machine m' hs
  · intro h s y y' hs; exact h { s with machine := y } y' hs

/-- The reference machine's runs from a stored state, under the no-stuck condition, are stores
of `M`'s runs. -/
theorem ref_runs_lift {R : Ref} (hf : Faithful R M) {s : Ffi.State} (hns : NoStuck M s) :
    ∀ {x t : Ffi.State} {m : M.σ}, x = M.store s m →
      RunsIn M.isa (fun y => ¬ Returned M.isa (M.load s) y) (M.load s) m →
      R.RunsIn (fun y => ¬ Returned M.isa (M.load s) (M.load y)) x t →
      ∃ m', t = M.store s m' ∧
        RunsIn M.isa (fun y => ¬ Returned M.isa (M.load s) y) (M.load s) m' := by
  intro x t m hx hm r
  induction r generalizing m with
  | refl => exact ⟨m, hx, hm⟩
  | step hp hs _ ih =>
    subst hx
    have hp' := mt (returned_load_store M).2 hp
    obtain ⟨m'', hm''⟩ := Option.isSome_iff_exists.1 (hns m hm hp')
    have := hf s m m'' hm''
    rw [hs] at this
    cases this
    exact ih rfl (Silmaril.X86.FnContract.runsIn_trans hm (.step hp' hm'' (.refl _)))

/-- `M`'s runs before the return lift to the reference machine. -/
theorem ref_of_runs {R : Ref} (hf : Faithful R M) {s : Ffi.State} {r : M.σ}
    {m t : M.σ} (h : RunsIn M.isa (fun y => ¬ Returned M.isa r y) m t) :
    R.RunsIn (fun y => ¬ Returned M.isa r (M.load y)) (M.store s m) (M.store s t) := by
  induction h with
  | refl => exact .refl _
  | step hp hs _ ih => exact .step (mt (returned_load_store M).1 hp) (hf _ _ _ hs) ih

/-- **A row on `M` holds on any reference machine `M` is faithful to**: every first return of the
reference machine from an admitted call is a conforming return, and in total mode there is one. -/
theorem Conforms.onRef {R : Ref} (hf : Faithful R M) (h : Conforms A M mode hdr f p c frame S)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) :
    (∀ t ∈ R.callModel M s, Good A p frame S a s t) ∧
      (mode = .total → (R.callModel M s).Nonempty) := by
  refine ⟨fun t ht => ?_, fun hm => ?_⟩
  · obtain ⟨m', rfl, hm'⟩ :=
      ref_runs_lift hf (h.safe a s ad pre) (M.store_load s).symm (.refl _) ht.1
    exact h.sound a s ad pre _ ⟨m', ⟨hm', (returned_load_store M).1 ht.2⟩, rfl⟩
  · obtain ⟨t, ⟨y, fr, rfl⟩⟩ := h.progress hm a s ad pre
    have r := ref_of_runs (s := s) hf fr.1
    rw [M.store_load] at r
    exact ⟨M.store s y, r, (returned_load_store M).2 fr.2⟩

end Silmaril.Proofs.Machine.Abi.Conformance

end
