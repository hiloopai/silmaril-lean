module

public import Silmaril.Elf.Link.Dyn.LibMod.Defs
public import Silmaril.Elf.Link.Dyn.Libc.Thms
public import Silmaril.Elf.Link.Dyn.Proc.Thms

/-!
# Library modules: the frame rule, subsets, and soundness of the C-runtime machine

PROVED (standard axioms), names in `Silmaril.Elf.Link.Dyn.LibMod`:

* `refines_relax`, `relaxSpec_le`: relaxing a contract by the scratch stack makes it looser, so a
  client proof against the relaxed contracts holds against the old ones;
* `ModRet.mono`, `LibModule.contract_preserves`, `LibModule.contract_framed`: the standard module
  contract preserves the invariant within the frame convention;
* **`sep_frame`** (the frame rule of modules): a call within `N`'s frame convention that keeps
  `M`'s ghost fields keeps `M`'s invariant when `M`'s memory is apart from `N`'s and from the
  call's scratch stack;
* `LibModule.Map.spec_le`: a module providing a subset is above it in the `LibcSpec` lattice;
* **`must_proc`**: a `Must` on the C-runtime machine is a `Must` on the process model `Proc`;
* **`must_real`**: along a stuttering simulation, a `Must` on the abstract machine is a real run
  reaching (a state related to) the goal;
* **`sim_crt`**: the C-runtime machine is simulated by a real machine as soon as the library's
  entry points realise their relaxed steps (`RealisesWorld`): the client steps (the executable's
  own code) are discharged once, by the `Open9` lens and the locality of the invariant.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.LibMod

open Silmaril.X86 (Word MState)
open Silmaril.X86.RelIsa (Res Must)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc (PState Ghost World Keeps Contract)
open Silmaril.Elf.Link.Dyn.Libc (Step Refines LibcSpec)

/-! ## Relaxation -/

theorem havoc_refl (W : World) (s t : PState) : Havoc W s t t :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

@[simp] theorem relax_stop (W : World) (k : Step) (s : PState) : relax W k s .stop = k s .stop := rfl

/-- **Relaxing is loosening**: every outcome of `k` is one of `relax W k`, which claims where `k`
does. -/
theorem refines_relax (W : World) (k : Step) : Refines k (relax W k) := by
  intro s _ r hr
  cases r with
  | stop => exact hr
  | ok t => exact ⟨t, hr, havoc_refl W s t⟩

theorem relax_congr {W : World} {k k' : Step} {s : PState} (h : k s = k' s) :
    relax W k s = relax W k' s := by
  funext r
  cases r <;> simp only [relax, h]

theorem relaxSpec_lookup (L : LibcSpec) (n : Name) :
    (relaxSpec L).lookup n = (L.lookup n).map (fun k (c : Libc.Ctx) => relax c.W (k c)) := by
  simp only [relaxSpec, LibcSpec.lookup]
  exact Libc.lookup_map (fun k (c : Libc.Ctx) => relax c.W (k c)) n L.syms

/-- **The relaxed specification is below the original one** in the `LibcSpec` lattice. -/
theorem relaxSpec_le (L : LibcSpec) : relaxSpec L ≤ L := fun c n => by
  simp only [LibcSpec.named]
  rw [relaxSpec_lookup]
  cases L.lookup n with
  | none => exact Libc.Refines.refl _
  | some k => exact refines_relax c.W (k c)

/-! ## Module contracts -/

theorem ModRet.mono {W : World} {own own' : PState → Nat → Prop} {s t : PState}
    (hown : ∀ s a, own s a → own' s a) (h : ModRet W own s t) : ModRet W own' s t := by
  obtain ⟨habi, hfs, hb, hp⟩ := h
  refine ⟨habi, hfs, fun a hr ha => hb a hr fun hw => ha ?_, fun a h1 h2 acc => hp a (fun h => h1 (hown _ _ h))
    (fun h => h2 (hown _ _ h)) acc⟩
  rcases hw with h | h | h
  · exact Or.inl (hown _ _ h)
  · exact Or.inr (Or.inl (hown _ _ h))
  · exact Or.inr (Or.inr h)

namespace LibModule

variable (M : LibModule)

theorem contract_pre {W : World} {pre : PState → Prop} {post : PState → PState → Prop} {s : PState}
    (hns : ¬ M.contract W pre post s .stop) :
    AbiEntry s.m.core s.m.memory ∧ M.Inv s ∧ pre s := by
  by_contra hp
  exact hns fun h => absurd h hp

/-- **The standard contract preserves the invariant.** -/
theorem contract_preserves (W : World) (pre : PState → Prop) (post : PState → PState → Prop) :
    M.PreservesInv (M.contract W pre post) := by
  intro s t _ hns hk
  obtain ⟨t', ht, _, hinv, _⟩ := hk (M.contract_pre hns)
  cases ht
  exact hinv

/-- **The standard contract keeps the frame convention.** -/
theorem contract_framed (W : World) (pre : PState → Prop) (post : PState → PState → Prop) :
    M.Framed W (M.contract W pre post) := by
  intro s t _ hns hk
  obtain ⟨t', ht, hret, _, _⟩ := hk (M.contract_pre hns)
  cases ht
  exact hret

end LibModule

/-! ## The frame rule of modules -/

/-- **The frame rule**: a call within `N`'s frame convention, apart from `M`'s memory and keeping
`M`'s ghost fields, keeps `M`'s invariant. -/
theorem sep_frame {W : World} {M N : LibModule} {s t : PState} (hk : ModRet W N.own s t)
    (hdis : ∀ a, M.own s a → ¬ N.own s a ∧ ¬ N.own t a ∧ ¬ (Scratch (rspOf s) a ∧ ¬ W.Kept a))
    (hg : M.gEq s.g t.g) (hi : M.Inv s) : M.Inv t := by
  obtain ⟨_, hfs, hb, hp⟩ := hk
  refine (M.local_ s t (fun a ha => ⟨fun hr => ?_, fun acc => ?_⟩) hfs hg hi).1
  · obtain ⟨h1, h2, h3⟩ := hdis a ha
    exact hb a hr fun hw => by
      rcases hw with h | h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
  · obtain ⟨h1, h2, _⟩ := hdis a ha
    exact hp a h1 h2 acc

/-! ## Subsets -/

theorem spec_lookup (M : LibModule) (n : Name) :
    M.spec.lookup n = (M.fns.lookup n).map (fun k (c : Libc.Ctx) => k c.W) := by
  simp only [LibModule.spec, LibcSpec.lookup]
  exact Libc.lookup_map (fun k (c : Libc.Ctx) => k c.W) n M.fns

/-- **A module providing a subset is above it** in the `LibcSpec` lattice: a client verified
against the subset's contracts runs against the larger module (`Libc.Thms.Verified.swap`). -/
theorem LibModule.Map.spec_le {M N : LibModule} (h : M.Map N) : M.spec ≤ N.spec := fun c n => by
  simp only [LibcSpec.named]
  rw [spec_lookup, spec_lookup]
  cases hm : M.fns.lookup n with
  | none => exact Libc.refines_stop _
  | some k =>
    obtain ⟨k', hk', hr⟩ := h.fns n k hm
    rw [hk']
    exact hr c.W

/-! ## The C-runtime machine and the process model -/

/-- Where the C-runtime machine claims something, every `Proc` outcome is one of its outcomes. -/
theorem crt_of_proc {M : LibModule} {W : World} {s : PState} {r : Res PState}
    (hns : ¬ crtStep M W s .stop) (h : Proc.step W s r) : crtStep M W s r := by
  unfold crtStep at hns ⊢
  unfold Proc.step at h
  cases hd : s.g.done with
  | some _ => simp [hd] at hns
  | none =>
    simp only [hd] at hns h ⊢
    by_cases hi : W.InImage s.m.core.rip.toNat
    · simp only [hi, ↓reduceIte] at hns h ⊢
      cases ho : Silmaril.X86.Open9.step s.m with
      | none => simp [ho] at hns
      | some m' =>
        simp only [ho] at hns h ⊢
        refine Or.inl ⟨?_, h⟩
        by_contra hk
        exact hns (Or.inr ⟨hk, trivial⟩)
    · simp only [hi, ↓reduceIte] at hns h ⊢
      exact refines_relax W _ s hns r h

/-- **A `Must` on the C-runtime machine is a `Must` on the process model.** -/
theorem must_proc {M : LibModule} {W : World} {Q : PState → Prop} {s : PState}
    (h : MustC M W Q s) : Proc.MustQ W Q s :=
  Libc.Must.of_refines (A := crt M W) (C := Proc.proc W) (fun _ _ hns hr => crt_of_proc hns hr) h

/-! ## Soundness against a real machine -/

/-- **Transfer along a stuttering simulation**: from a related real state, the real machine
reaches a state related to an abstract state satisfying the goal. -/
theorem must_real {σ τ : Type} {A : Silmaril.X86.RelIsa σ} {step : τ → Option τ}
    {R : τ → σ → Prop} (hs : Sim A step R) {P Q : σ → Prop} {a : σ} (hm : Must A P Q a) :
    ∀ c, R c a → ∃ c', Reaches step c c' ∧ ∃ a', R c' a' ∧ Q a' := by
  induction hm with
  | done hq => exact fun c hc => ⟨c, Reaches.refl _ _, _, hc, hq⟩
  | step _ hns _ ih =>
    intro c hc
    obtain ⟨a', ha', c', hr, hc'⟩ := hs c _ hc hns
    obtain ⟨c'', hr', a'', h1, h2⟩ := ih a' ha' c' hc'
    exact ⟨c'', hr.trans hr', a'', h1, h2⟩

/-- The library step at a state outside the image is the gate's, the resolver's, a bound
function's, or a stop. -/
theorem extStep_cases (W : World) (s : PState) :
    (s.m.core.rip = W.gate ∧ Proc.extStep W s = Proc.gateStep W s) ∨
    (∃ res slots, W.lazy = some (res, slots) ∧ s.m.core.rip = res ∧ res ≠ W.gate ∧
      Proc.extStep W s = Proc.resolveStep W slots s) ∨
    (∃ f, (s.m.core.rip, f) ∈ W.fns ∧ s.m.core.rip ≠ W.gate ∧
      Proc.extStep W s = Proc.fnStep W f s) ∨
    Proc.extStep W s = fun r => r = .stop := by
  by_cases hg : s.m.core.rip = W.gate
  · exact Or.inl ⟨hg, by funext r; simp [Proc.extStep, hg]⟩
  · refine Or.inr ?_
    have hfns : (∃ f, (s.m.core.rip, f) ∈ W.fns ∧ s.m.core.rip ≠ W.gate ∧
        (match W.fns.find? (·.1 == s.m.core.rip) with
          | some (_, f) => Proc.fnStep W f s
          | none => fun r => r = .stop) = Proc.fnStep W f s) ∨
        (match W.fns.find? (·.1 == s.m.core.rip) with
          | some (_, f) => Proc.fnStep W f s
          | none => fun r => r = .stop) = (fun r => r = .stop) := by
      cases hf : W.fns.find? (·.1 == s.m.core.rip) with
      | some e =>
        obtain ⟨e1, f⟩ := e
        have hm := List.mem_of_find?_eq_some hf
        have he : e1 = s.m.core.rip := by simpa using List.find?_some hf
        subst he
        exact Or.inl ⟨f, hm, hg, rfl⟩
      | none => exact Or.inr rfl
    cases hl : W.lazy with
    | some p =>
      obtain ⟨res, slots⟩ := p
      by_cases hr : s.m.core.rip = res
      · subst hr
        exact Or.inl ⟨_, slots, rfl, rfl, hg, by funext r; simp [Proc.extStep, hg, hl]⟩
      · refine Or.inr ?_
        have he : Proc.extStep W s = (match W.fns.find? (·.1 == s.m.core.rip) with
            | some (_, f) => Proc.fnStep W f s
            | none => fun r => r = .stop) := by
          funext r
          simp only [Proc.extStep, hg, hl, hr, ↓reduceIte]
          cases W.fns.find? (·.1 == s.m.core.rip) <;> rfl
        rw [he]
        rcases hfns with ⟨f, hm, hg', e⟩ | e
        · exact Or.inl ⟨f, hm, hg', e⟩
        · exact Or.inr e
    | none =>
      refine Or.inr ?_
      have he : Proc.extStep W s = (match W.fns.find? (·.1 == s.m.core.rip) with
          | some (_, f) => Proc.fnStep W f s
          | none => fun r => r = .stop) := by
        funext r
        simp only [Proc.extStep, hg, hl, ↓reduceIte]
        cases W.fns.find? (·.1 == s.m.core.rip) <;> rfl
      rw [he]
      rcases hfns with ⟨f, hm, hg', e⟩ | e
      · exact Or.inl ⟨f, hm, hg', e⟩
      · exact Or.inr e

/-- **The C-runtime machine is simulated by the real machine** once the library realises its
entry points: the executable's own steps are matched by the `Open9` lens (one real step each),
and keep the invariant by locality, since the C-runtime machine stops on any step that changes
owned memory or the thread pointer. -/
theorem sim_crt {X : Real} {M : LibModule} {W : World} (h : RealisesWorld X M W) :
    Sim (crt M W) X.J.step (Rel X M) := by
  intro c a hc hns
  change ¬ crtStep M W a .stop at hns
  show ∃ a', crtStep M W a (.ok a') ∧ ∃ c', Reaches X.J.step c c' ∧ Rel X M c' a'
  unfold crtStep at hns ⊢
  cases hd : a.g.done with
  | some _ => simp [hd] at hns
  | none =>
    simp only [hd] at hns ⊢
    by_cases hi : W.InImage a.m.core.rip.toNat
    · simp only [hi, ↓reduceIte] at hns ⊢
      cases ho : Silmaril.X86.Open9.step a.m with
      | none => simp [ho] at hns
      | some m' =>
        simp only [ho] at hns ⊢
        have hk : OwnKept M a m' := by
          by_contra hk
          exact hns (Or.inr ⟨hk, trivial⟩)
        obtain ⟨hv, hinv, hobs⟩ := hc
        have hstep : X.J.step c = some (X.L.put c m') := X.L.step (by rw [hv]; exact ho)
        refine ⟨⟨m', a.g⟩, Or.inl ⟨hk, rfl⟩, X.L.put c m', ⟨1, by simp [hstep]⟩, X.L.view_put c m', ?_,
          (X.obs_put c m' a.g).mpr hobs⟩
        exact (M.local_ a ⟨m', a.g⟩ hk.1 hk.2 (M.gEq_refl a.g) hinv).1
    · simp only [hi, ↓reduceIte] at hns ⊢
      rcases extStep_cases W a with ⟨hg, he⟩ | ⟨res, slots, hl, hr, hg, he⟩ | ⟨f, hm, hg, he⟩ | he
      · rw [relax_congr he] at hns ⊢
        exact h.gate c a hc hg hd hns
      · rw [relax_congr he] at hns ⊢
        exact h.lazy res slots hl hg c a hc hr hd hns
      · rw [relax_congr he] at hns ⊢
        exact h.fns _ f hm hg c a hc rfl hd hns
      · exfalso
        apply hns
        rw [relax_congr (k' := fun _ r => r = .stop) he]
        rfl

/-- **Soundness of the C-runtime machine** (`must_real` along `sim_crt`): when the library
realises the world and the real state represents `a`, every `Must` on the C-runtime machine is
a real run reaching a state that represents a goal state. -/
theorem crt_sound {X : Real} {M : LibModule} {W : World} (h : RealisesWorld X M W)
    {Q : PState → Prop} {a : PState} (hm : MustC M W Q a) {c : X.τ} (hc : Rel X M c a) :
    ∃ c', Reaches X.J.step c c' ∧ ∃ a', Rel X M c' a' ∧ Q a' :=
  must_real (sim_crt h) hm c hc

end Silmaril.Elf.Link.Dyn.LibMod
