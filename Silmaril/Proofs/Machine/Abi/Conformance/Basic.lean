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

theorem mem_callModelOf {s : Ffi.State} {t : MState} (h : FirstReturn M s.machine t) :
    { s with machine := t } ∈ callModelOf M s :=
  ⟨h, rfl⟩

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
theorem noStuck_of_firstReturn {s : Ffi.State} {t : MState} (h : FirstReturn M s.machine t) :
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
theorem conforms_of_strict {S' : Spec MState} (hs : S'.Strict M)
    (hdecl : Declares A hdr f p) (hext : c.off + c.len ≤ c.bytes.length)
    (hnv : ∃ a s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory)
    (hen : ∀ a mem, S.pre a mem → (∀ x, S.objects a mem x → c.Outside x) →
      ∃ s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory ∧
        (∀ x, S.objects a s.machine.memory x ↔ S.objects a mem x) ∧
        ∀ x, S.objects a mem x → s.machine.memory.bytes[x]? = mem.bytes[x]?)
    (habi : ∀ a s, Admit A M p c frame S a s → AbiEntry (M.core s.machine) (M.mem s.machine))
    (hentry : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory → S'.entry s.machine)
    (hgood : ∀ a s t, Admit A M p c frame S a s → S.pre a s.machine.memory →
      FirstReturn M s.machine t → S'.Result M s.machine t →
      Good A p frame S a s { s with machine := t }) :
    Conforms A M mode hdr f p c frame S := by
  refine ⟨hdecl, hext, hnv, hen, fun a s ad pre => ?_, fun _ a s ad pre => ?_,
    fun a s ad pre t ht => ?_⟩
  · obtain ⟨t, fr, -⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    exact noStuck_of_firstReturn fr
  · obtain ⟨t, fr, -⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    exact ⟨_, mem_callModelOf fr⟩
  · obtain ⟨t0, fr, res⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    obtain ⟨fr', heq⟩ := ht
    have := Silmaril.X86.FnContract.firstReturn_unique fr' fr
    rw [heq, this]
    exact hgood a s t0 ad pre fr res

/-- An admitted entry state is not a returned state (the return address is outside the code,
`rip` is inside it). -/
theorem not_returned_entry (hc : ∀ m, M.core m = m.core) (hm : ∀ m, M.mem m = m.memory)
    (hlen : 0 < c.len) (hext : c.off + c.len ≤ c.bytes.length) {s : Ffi.State} (hp : Placed c s) :
    ¬ Returned M s.machine s.machine := by
  intro h
  have := h.1
  simp only [hc, hm] at this
  exact hp.retOutside c.off (by omega) (this.symm.trans hp.pc)

/-- **Stuck code does not conform**, in either mode: on a machine whose core is the state's, an
admitted call of a conforming function takes a step at its entry. -/
theorem Conforms.steps (h : Conforms A M mode hdr f p c frame S) (hc : ∀ m, M.core m = m.core)
    (hm : ∀ m, M.mem m = m.memory) (hlen : 0 < c.len) {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) : (M.step s.machine).isSome :=
  h.safe a s ad pre s.machine (.refl _) (not_returned_entry hc hm hlen h.extent ad.placed)

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

/-! ## Faithfulness: rows on `M` read on a reference machine -/

/-- The reference machine's runs from the lift of a state, under the no-stuck condition, are
lifts of `M`'s runs. -/
theorem ref_runs_lift {R : Ref} (hf : Faithful R M) {s : Ffi.State} (hns : NoStuck M s) :
    ∀ {x t : Ffi.State} {m : MState}, x = { s with machine := m } →
      RunsIn M (fun y => ¬ Returned M s.machine y) s.machine m →
      R.RunsIn (fun y => ¬ Returned M s.machine y.machine) x t →
      ∃ m', t = { s with machine := m' } ∧
        RunsIn M (fun y => ¬ Returned M s.machine y) s.machine m' := by
  intro x t m hx hm r
  induction r generalizing m with
  | refl => exact ⟨m, hx, hm⟩
  | step hp hs _ ih =>
    subst hx
    obtain ⟨m'', hm''⟩ := Option.isSome_iff_exists.1 (hns m hm hp)
    have := hf { s with machine := m } m'' hm''
    rw [hs] at this
    cases this
    exact ih rfl (Silmaril.X86.FnContract.runsIn_trans hm (.step hp hm'' (.refl _)))

/-- `M`'s runs lift to the reference machine. -/
theorem ref_of_runs {R : Ref} (hf : Faithful R M) {s : Ffi.State} {P : MState → Prop}
    {m t : MState} (r : RunsIn M P m t) :
    R.RunsIn (fun y => P y.machine) { s with machine := m } { s with machine := t } := by
  induction r with
  | refl => exact .refl _
  | step hp hs _ ih => exact .step hp (hf _ _ hs) ih

/-- **A row on `M` holds on any reference machine `M` is faithful to**: every first return of the
reference machine from an admitted call is a conforming return, and in total mode there is one. -/
theorem Conforms.onRef {R : Ref} (hf : Faithful R M) (h : Conforms A M mode hdr f p c frame S)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) :
    (∀ t ∈ R.callModel M s, Good A p frame S a s t) ∧
      (mode = .total → (R.callModel M s).Nonempty) := by
  refine ⟨fun t ht => ?_, fun hm => ?_⟩
  · obtain ⟨m', rfl, hm'⟩ := ref_runs_lift hf (h.safe a s ad pre) rfl (.refl _) ht.1
    exact h.sound a s ad pre _ ⟨⟨hm', ht.2⟩, rfl⟩
  · obtain ⟨t, fr, -⟩ := h.progress hm a s ad pre
    have e : ({ s with machine := s.machine } : Ffi.State) = s := rfl
    exact ⟨{ s with machine := t.machine }, e ▸ ref_of_runs hf fr.1, fr.2⟩

end Silmaril.Proofs.Machine.Abi.Conformance

end
