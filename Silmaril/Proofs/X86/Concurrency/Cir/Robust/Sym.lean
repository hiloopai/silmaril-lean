module

public import Silmaril.X86.Concurrency.Cir.Robust.Sym.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Robust.Witness

/-!
# Thread-symmetry reduction: soundness

The TSO machine `Csl.OStep` names threads only through the index of the
step, so renaming the threads of a configuration by a permutation of `0 … N-1` maps steps to
steps (`ostep_perm`, `taus_perm`). The canonical form of a configuration is a renaming of it
(`canon_ocfg`). A set closed under "canonical form of a fused successor" therefore covers every
reachable configuration **up to a renaming** (`fusedSym_reach`), and a finished one is a renaming
of an element (`symCheck_sound`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl (Heap Ent TStep OStep upd OCfg Cfg Star)

end Silmaril.Proofs.X86.Concurrency.Cir.Robust

/-! ## Thread permutations -/

namespace Silmaril.X86.Concurrency.Cir.Robust.TPerm

theorem g_lt {N : Nat} (σ : TPerm N) {x : Nat} (h : x < N) : σ.g x < N :=
  (σ.lt (σ.g x)).mpr (by rw [σ.fg]; exact h)

theorem f_lt {N : Nat} (σ : TPerm N) {x : Nat} (h : x < N) : σ.f x < N := (σ.lt x).mp h

/-- The identity. -/
def id (N : Nat) : TPerm N := ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl, fun _ => Iff.rfl⟩

/-- Composition: first `τ`, then `σ` (thread `t` of the result is thread `σ.f (τ.f t)`). -/
def comp {N : Nat} (σ τ : TPerm N) : TPerm N where
  f x := σ.f (τ.f x)
  g x := τ.g (σ.g x)
  fg x := by simp [σ.fg, τ.fg]
  gf x := by simp [σ.gf, τ.gf]
  lt x := (τ.lt x).trans (σ.lt (τ.f x))

/-- The inverse. -/
def inv {N : Nat} (σ : TPerm N) : TPerm N where
  f := σ.g
  g := σ.f
  fg := σ.gf
  gf := σ.fg
  lt x := by rw [σ.lt (σ.g x), σ.fg]

end Silmaril.X86.Concurrency.Cir.Robust.TPerm

namespace Silmaril.Proofs.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl (Heap Ent TStep OStep upd OCfg Cfg Star)

theorem permCfg_comp (C : OCfg) (f g : Nat → Nat) :
    permCfg (permCfg C f) g = permCfg C (fun x => f (g x)) := rfl

theorem permCfg_inv {N : Nat} (C : OCfg) (σ : TPerm N) : permCfg (permCfg C σ.f) σ.g = C := by
  simp only [permCfg_comp, σ.fg]; rfl

/-- Renaming commutes with a point update. -/
theorem upd_perm {α : Type} {N : Nat} (σ : TPerm N) (F : Nat → α) (t : Nat) (x : α) :
    (fun u => upd F t x (σ.f u)) = upd (fun u => F (σ.f u)) (σ.g t) x := by
  funext u
  simp only [upd]
  by_cases h : u = σ.g t
  · subst h; simp [σ.fg]
  · have : σ.f u ≠ t := fun e => h (by rw [← e, σ.gf])
    simp [h, this]

/-! ## The machine is symmetric -/

/-- **A renamed step is a step.** -/
theorem ostep_perm {M : Csl.OModel} {N : Nat} (σ : TPerm N) {C C' : OCfg} (h : OStep M N C C') :
    OStep M N (permCfg C σ.f) (permCfg C' σ.f) := by
  have hts : ∀ t, (permCfg C σ.f).ts (σ.g t) = C.ts t := fun t => by simp [permCfg, σ.fg]
  have hbuf : ∀ t, (permCfg C σ.f).buf (σ.g t) = C.buf t := fun t => by simp [permCfg, σ.fg]
  cases h with
  | tau ht hs =>
    rename_i t s' rs'
    have := OStep.tau (M := M) (C := permCfg C σ.f) (σ.g_lt ht) (by rw [hts]; exact hs)
    simpa only [permCfg, upd_perm σ] using this
  | buffered ht hs hm hd hc hok =>
    rename_i t l s' rs'
    have := OStep.buffered (M := M) (C := permCfg C σ.f) (σ.g_lt ht) (by rw [hts]; exact hs) hm hd
      hc (by rw [hbuf]; exact hok)
    rw [hbuf] at this
    simpa only [permCfg, upd_perm σ] using this
  | drained ht hs hm hd he hc hok =>
    rename_i t l s' rs'
    have := OStep.drained (M := M) (C := permCfg C σ.f) (σ.g_lt ht) (by rw [hts]; exact hs) hm hd
      (by rw [hbuf]; exact he) hc hok
    simpa only [permCfg, upd_perm σ] using this
  | flush ht hb hp hmod =>
    rename_i t pre e post
    have := OStep.flush (M := M) (C := permCfg C σ.f) (σ.g_lt ht) (by rw [hbuf]; exact hb) hp hmod
    simpa only [permCfg, upd_perm σ] using this

theorem oreach_perm {M : Csl.OModel} {N : Nat} (σ : TPerm N) {C C' : OCfg}
    (h : Csl.OReach M N C C') : Csl.OReach M N (permCfg C σ.f) (permCfg C' σ.f) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (ostep_perm σ h) ih

theorem tau_perm {N : Nat} (σ : TPerm N) {C D : OCfg} (h : TauStep N C D) :
    TauStep N (permCfg C σ.f) (permCfg D σ.f) := by
  obtain ⟨t, ht, s', rs', hs, rfl⟩ := h
  refine ⟨σ.g t, σ.g_lt ht, s', rs', by simpa [permCfg, σ.fg] using hs, ?_⟩
  simp only [permCfg, upd_perm σ]

/-- **A renamed silent path is a silent path.** -/
theorem taus_perm {N : Nat} (σ : TPerm N) {C D : OCfg} (h : Star (TauStep N) C D) :
    Star (TauStep N) (permCfg C σ.f) (permCfg D σ.f) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (tau_perm σ h) ih

/-! ## Canonical forms are renamings -/

theorem insKey_perm (x : Nat × Nat) : ∀ l : List (Nat × Nat), (insKey x l).Perm (x :: l)
  | [] => .refl _
  | y :: l => by
    simp only [insKey]
    split
    · exact .refl _
    · exact ((insKey_perm x l).cons y).trans (.swap x y l)

theorem sortKey_perm : ∀ l : List (Nat × Nat), (sortKey l).Perm l
  | [] => .refl _
  | x :: l => (insKey_perm x _).trans ((sortKey_perm l).cons x)

theorem canonOrder_perm (N : Nat) (c : CSt) : (canonOrder N c).Perm (List.range N) := by
  have := (sortKey_perm ((List.range N).map fun i =>
    (thKey (c.ts.getD i (.skip, [])) (c.buf.getD i []), i))).map (·.2)
  simpa [canonOrder, List.map_map, Function.comp_def] using this

/-- The renaming of a permutation `p` of `0 … N-1`. -/
def ofPerm (N : Nat) (p : List Nat) (hp : p.Perm (List.range N)) : TPerm N where
  f x := if x < N then p.getD x 0 else x
  g x := if x < N then p.idxOf x else x
  fg x := by
    have hl : p.length = N := by simpa using hp.length_eq
    by_cases hx : x < N
    · have hm : x ∈ p := hp.mem_iff.mpr (List.mem_range.mpr hx)
      have hi := List.idxOf_lt_length_of_mem hm
      simp only [hx, ite_true, hl ▸ hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some, List.getElem_idxOf hi]
    · simp [hx]
  gf x := by
    have hl : p.length = N := by simpa using hp.length_eq
    have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range
    by_cases hx : x < N
    · have hi : x < p.length := hl ▸ hx
      have hlt : p[x] < N := List.mem_range.mp (hp.mem_iff.mp (List.getElem_mem hi))
      simp only [hx, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some, hlt, hnd.idxOf_getElem x hi]
    · simp [hx]
  lt x := by
    have hl : p.length = N := by simpa using hp.length_eq
    by_cases hx : x < N
    · have hi : x < p.length := hl ▸ hx
      have hlt : p[x] < N := List.mem_range.mp (hp.mem_iff.mp (List.getElem_mem hi))
      simp only [hx, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some, hlt]
    · simp [hx]

theorem permute_ocfg {N : Nat} {c : CSt} (hl : c.ts.length = N) (hb : c.buf.length = N)
    (p : List Nat) (hp : p.Perm (List.range N)) :
    (c.permute p).ocfg = permCfg c.ocfg (ofPerm N p hp).f := by
  have hpl : p.length = N := by simpa using hp.length_eq
  have hlt : ∀ i (h : i < p.length), p[i] < N :=
    fun i h => List.mem_range.mp (hp.mem_iff.mp (List.getElem_mem h))
  simp only [CSt.ocfg, permCfg, CSt.permute, ofPerm]
  congr 1
  · funext t
    simp only [CSt.th]
    by_cases ht : t < N
    · have hi : t < p.length := hpl ▸ ht
      have hq : p[t] < c.ts.length := hl ▸ hlt t hi
      simp [ht, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hq,
        List.getD_eq_getElem?_getD]
    · have h1 : ¬ t < c.ts.length := hl ▸ ht
      have h2 : ¬ t < p.length := hpl ▸ ht
      simp [ht, List.getElem?_eq_none (Nat.le_of_not_lt h1),
        List.getElem?_eq_none (Nat.le_of_not_lt h2)]
  · funext t
    by_cases ht : t < N
    · have hi : t < p.length := hpl ▸ ht
      have hq : p[t] < c.buf.length := hb ▸ hlt t hi
      simp [ht, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD]
    · have h1 : ¬ t < c.buf.length := hb ▸ ht
      have h2 : ¬ t < p.length := hpl ▸ ht
      simp [ht, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h1),
        List.getElem?_eq_none (Nat.le_of_not_lt h2)]

/-- **The canonical form is a renaming.** -/
theorem canon_ocfg {N : Nat} {c : CSt} (hl : c.ts.length = N) (hb : c.buf.length = N) :
    ∃ σ : TPerm N, (c.canon N).ocfg = permCfg c.ocfg σ.f :=
  ⟨_, permute_ocfg hl hb _ (canonOrder_perm N c)⟩

/-! ## One fused step -/

/-- From a TSO step of a well-shaped `d`'s configuration to a fused successor. -/
theorem succ_of_step {N : Nat} {d : CSt} (hok : d.okB N = true) {D' : OCfg}
    (hst : OStep .tso N d.ocfg D') : ∃ e ∈ ftsoSucc N d, Star (TauStep N) D' e.ocfg := by
  obtain ⟨t, ht, e, he, rfl⟩ := tsoStepT_complete hok hst
  refine ⟨tauNF t tauFuel e, ?_, tauNF_tau ht tauFuel e⟩
  simp only [ftsoSucc, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨t, ht, e, he, rfl⟩

/-- **A TSO step from anything that completes silently to a normal, well-shaped `d`** lands on
something that completes silently to a fused successor of `d` (`cov_step`, without the
closed set). -/
theorem step_succ {N : Nat} {d : CSt} (hok : d.okB N = true) (hn : d.normalB N = true)
    {C C' : OCfg} (hpath : Star (TauStep N) C d.ocfg) (hst : OStep .tso N C C') :
    Star (TauStep N) C' d.ocfg ∨ ∃ e ∈ ftsoSucc N d, Star (TauStep N) C' e.ocfg := by
  have hD := normal_of_normalB hn
  obtain ⟨hmem, hbuf⟩ := taus_mb hpath
  cases hst with
  | tau ht hs => exact .inl (tau_into_normal hpath hD ⟨_, ht, _, _, hs, rfl⟩)
  | buffered ht hs hm hdr hc hok' =>
    rename_i t l s' rs'
    have hn' : ∀ s₂ rs₂, ¬ TStep (C.ts t).1 (C.ts t).2 none s₂ rs₂ :=
      fun _ _ h => tstep_tau_excl h hs
    have hkeep := taus_keep hpath hn'
    have hst' : OStep .tso N d.ocfg
        ⟨upd d.ocfg.ts t (s', rs'), d.ocfg.mem, upd d.ocfg.buf t (d.ocfg.buf t ++ l.ents)⟩ := by
      refine .buffered ht (by rw [hkeep]; exact hs) hm hdr (by rw [hmem]; exact hc)
        (by rw [hmem, hbuf]; exact hok')
    obtain ⟨d', hd', hp'⟩ := succ_of_step hok hst'
    refine .inr ⟨d', hd', star_trans ?_ hp'⟩
    have := taus_lift hpath hn' (s', rs') C.mem (upd C.buf t (C.buf t ++ l.ents))
    rw [hmem, hbuf]; exact this
  | drained ht hs hm hdr he hc hok' =>
    rename_i t l s' rs'
    have hn' : ∀ s₂ rs₂, ¬ TStep (C.ts t).1 (C.ts t).2 none s₂ rs₂ :=
      fun _ _ h => tstep_tau_excl h hs
    have hkeep := taus_keep hpath hn'
    have hst' : OStep .tso N d.ocfg ⟨upd d.ocfg.ts t (s', rs'), l.updH d.ocfg.mem, d.ocfg.buf⟩ := by
      refine .drained ht (by rw [hkeep]; exact hs) hm hdr (by rw [hbuf]; exact he)
        (by rw [hmem]; exact hc) (by rw [hmem]; exact hok')
    obtain ⟨d', hd', hp'⟩ := succ_of_step hok hst'
    refine .inr ⟨d', hd', star_trans ?_ hp'⟩
    have := taus_lift hpath hn' (s', rs') (l.updH C.mem) C.buf
    rw [hmem, hbuf]; exact this
  | flush ht hb hp hmod =>
    rename_i t pre e post
    have hst' : OStep .tso N d.ocfg
        ⟨d.ocfg.ts, e.apply d.ocfg.mem, upd d.ocfg.buf t (pre ++ post)⟩ :=
      .flush ht (by rw [hbuf]; exact hb) hp hmod
    obtain ⟨d', hd', hp'⟩ := succ_of_step hok hst'
    refine .inr ⟨d', hd', star_trans ?_ hp'⟩
    have := taus_lift_mb hpath (e.apply C.mem) (upd C.buf t (pre ++ post))
    rw [hmem, hbuf]; exact this

/-! ## The closed set covers every reachable configuration up to renaming -/

/-- `C`, renamed, completes by silent steps to an element of `S`. -/
def CovSym (N : Nat) (S : List CSt) (C : OCfg) : Prop :=
  ∃ d ∈ S, ∃ σ : TPerm N, Star (TauStep N) (permCfg C σ.f) d.ocfg

theorem closedSymB_parts {N : Nat} {S : List CSt} (h : closedSymB N S = true) {d : CSt}
    (hd : d ∈ S) : d.okB N = true ∧ d.normalB N = true ∧
      ∀ e ∈ ftsoSucc N d, e.ts.length = N ∧ e.buf.length = N ∧ e.canon N ∈ S := by
  simp only [closedSymB, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h d hd
  refine ⟨h1, h2, fun e he => ?_⟩
  obtain ⟨⟨h4, h5⟩, h6⟩ := h3 e he
  exact ⟨by simpa using h4, by simpa using h5, memB_ofList h6⟩

/-- **One TSO step keeps the cover.** -/
theorem covSym_step {N : Nat} {S : List CSt} (hcl : closedSymB N S = true) {C C' : OCfg}
    (hc : CovSym N S C) (hst : OStep .tso N C C') : CovSym N S C' := by
  obtain ⟨d, hd, σ, hpath⟩ := hc
  obtain ⟨hok, hn, hsucc⟩ := closedSymB_parts hcl hd
  rcases step_succ hok hn hpath (ostep_perm σ hst) with h | ⟨e, he, hp⟩
  · exact ⟨d, hd, σ, h⟩
  · obtain ⟨hl, hb, hS⟩ := hsucc e he
    obtain ⟨τ, hτ⟩ := canon_ocfg hl hb
    refine ⟨e.canon N, hS, σ.comp τ, ?_⟩
    rw [hτ]
    exact taus_perm τ hp

theorem fusedSym_reach {N : Nat} {S : List CSt} (hcl : closedSymB N S = true) {C C' : OCfg}
    (h : Csl.OReach .tso N C C') (hc : CovSym N S C) : CovSym N S C' := by
  induction h with
  | refl => exact hc
  | step h _ ih => exact ih (covSym_step hcl hc h)

/-! ## The check -/

theorem permCfg_drained {N : Nat} {C : OCfg} (σ : TPerm N) (h : C.Drained) :
    (permCfg C σ.f).Drained := fun t => h (σ.f t)

theorem permCfg_fin {N : Nat} {C : OCfg} (σ : TPerm N) (h : ∀ t < N, (C.ts t).1 = .skip) :
    ∀ t < N, ((permCfg C σ.f).ts t).1 = .skip := fun t ht => h (σ.f t) (σ.f_lt ht)

/-- **The symmetry-reduced TSO final-state check is sound**: every finished, drained
TSO-reachable configuration is a renaming of an element satisfying `P`. -/
theorem symCheck_sound {N fuel : Nat} {c0 : CSt} {P : CSt → Bool}
    (h : symCheck N fuel c0 P = true) {C : OCfg} (hr : Csl.OReach .tso N c0.cfg.toO C)
    (hd : C.Drained) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ d, P d = true ∧ ∃ σ : TPerm N, d.ocfg = permCfg C σ.f := by
  simp only [symCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hcl, h0⟩, hb⟩, hl⟩, hbl⟩, hP⟩ := h
  rw [List.all_eq_true] at hP
  rw [toO_ocfg hb] at hr
  obtain ⟨τ, hτ⟩ := canon_ocfg hl hbl
  have hc : CovSym N (symStates N fuel c0) c0.ocfg := by
    refine ⟨_, memB_ofList h0, τ, ?_⟩
    simp only [symStart]
    rw [hτ]
    exact taus_perm τ (normAll_tau tauFuel (List.range N) (fun t ht => List.mem_range.mp ht) c0)
  obtain ⟨d, hd', σ, hp⟩ := fusedSym_reach hcl hr hc
  have he := taus_done hp (permCfg_fin σ hfin)
  obtain ⟨h1, h2⟩ := done_drained he (permCfg_drained σ hd) (permCfg_fin σ hfin)
  have := hP d hd'
  simp only [h1, h2, Bool.and_self, Bool.not_true, Bool.false_or] at this
  exact ⟨d, this, σ, he⟩

/-- **For a property of memory alone**, the check gives the property of every finished, drained
TSO-reachable configuration. -/
theorem symCheck_mem {N fuel : Nat} {c0 : CSt} {Q : Heap → Prop}
    {P : CSt → Bool} (hPQ : ∀ d, P d = true → Q d.ocfg.mem)
    (h : symCheck N fuel c0 P = true) {C : OCfg} (hr : Csl.OReach .tso N c0.cfg.toO C)
    (hd : C.Drained) (hfin : ∀ t < N, (C.ts t).1 = .skip) : Q C.mem := by
  obtain ⟨d, hP, σ, he⟩ := symCheck_sound h hr hd hfin
  have := hPQ d hP
  rw [he] at this
  exact this

/-! ## Explored configurations are reachable up to renaming -/

theorem canon_len {N : Nat} {c : CSt} : (c.canon N).buf.length = N := by
  simp [CSt.canon, CSt.permute, (canonOrder_perm N c).length_eq]

theorem canon_tslen {N : Nat} {c : CSt} : (c.canon N).ts.length = N := by
  simp [CSt.canon, CSt.permute, (canonOrder_perm N c).length_eq]

theorem tauNF_tslen (t : Nat) : ∀ (f : Nat) (c : CSt), (tauNF t f c).ts.length = c.ts.length
  | 0, _ => rfl
  | f + 1, c => by
    simp only [tauNF]
    split
    · rw [tauNF_tslen t f]; simp [CSt.setTh]
    · rfl

theorem tsoStepT_tslen {c : CSt} {t : Nat} {d : CSt} (h : d ∈ tsoStepT c t) :
    d.ts.length = c.ts.length := by
  simp only [tsoStepT, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨⟨o, s', rs'⟩, -, hd⟩ | h
  · cases o with
    | none => simp only [Option.some.injEq] at hd; subst hd; simp [CSt.setTh]
    | some l =>
      simp only at hd
      split at hd
      · split at hd
        · split at hd
          · simp only [Option.some.injEq] at hd; subst hd; simp [CSt.setTh]
          · cases hd
        · simp only [Option.some.injEq] at hd; subst hd; simp [CSt.setTh]
      · cases hd
  · split at h
    · simp only [List.mem_singleton] at h; subst h; rfl
    · simp at h

/-- **Every explored configuration is, renamed, TSO-reachable.** -/
theorem symStates_reach {N fuel : Nat} {c0 : CSt}
    (hl : (normAll N tauFuel c0).ts.length = N) (hbl : (normAll N tauFuel c0).buf.length = N)
    {e : CSt} (he : e ∈ symStates N fuel c0) :
    ∃ σ : TPerm N, Csl.OReach .tso N c0.ocfg (permCfg e.ocfg σ.f) := by
  have h0 : Csl.OReach .tso N c0.ocfg (normAll N tauFuel c0).ocfg :=
    tauStep_ostep (normAll_tau tauFuel (List.range N) (fun t ht => List.mem_range.mp ht) c0)
  have hstart : ∃ σ : TPerm N, Csl.OReach .tso N c0.ocfg (permCfg (symStart N c0).ocfg σ.f) := by
    obtain ⟨τ, hτ⟩ := canon_ocfg hl hbl
    refine ⟨τ.inv, ?_⟩
    simp only [symStart]
    rw [hτ]
    show Csl.OReach .tso N c0.ocfg (permCfg (permCfg _ τ.f) τ.g)
    rw [permCfg_inv]
    exact h0
  refine (explore_inv (symSucc N)
    (fun x => (∃ σ : TPerm N, Csl.OReach .tso N c0.ocfg (permCfg x.ocfg σ.f)) ∧
      x.ts.length = N ∧ x.buf.length = N) ?_ fuel _ _ _
    (fun x hx => by simp at hx; subst hx; exact ⟨hstart, canon_tslen, canon_len⟩)
    (fun x hx => by simp at hx; subst hx; exact ⟨hstart, canon_tslen, canon_len⟩) e he).1
  intro x ⟨⟨σ, hx⟩, hxt, hxl⟩ y hy
  simp only [symSucc, ftsoSucc, List.mem_map, List.mem_flatMap, List.mem_range] at hy
  obtain ⟨z, ⟨t, ht, w, hw, rfl⟩, rfl⟩ := hy
  refine ⟨?_, canon_tslen, canon_len⟩
  have hzl : (tauNF t tauFuel w).buf.length = N := by rw [tauNF_len, tsoStepT_len hw, hxl]
  have hzt : (tauNF t tauFuel w).ts.length = N := by rw [tauNF_tslen, tsoStepT_tslen hw, hxt]
  have hstep : Csl.OReach .tso N x.ocfg (tauNF t tauFuel w).ocfg :=
    star_trans (.step (tsoStepT_sound ht (hxl ▸ ht) hw) .refl)
      (tauStep_ostep (tauNF_tau ht tauFuel w))
  obtain ⟨τ, hτ⟩ := canon_ocfg hzt hzl
  refine ⟨τ.inv.comp σ, ?_⟩
  rw [hτ, permCfg_comp]
  have : (fun x => τ.f ((τ.inv.comp σ).f x)) = σ.f := by
    funext x; simp [TPerm.comp, TPerm.inv, τ.fg]
  rw [this]
  exact star_trans hx (oreach_perm σ hstep)

/-- **A witness up to renaming**: a finished, drained explored configuration satisfying `P` is,
renamed, TSO-reachable. -/
theorem symWitness_of_any {N fuel : Nat} {c0 : CSt} (he : c0.buf.all List.isEmpty = true)
    (hl : (normAll N tauFuel c0).ts.length = N) (hbl : (normAll N tauFuel c0).buf.length = N)
    {P : CSt → Bool}
    (h : ((symStates N fuel c0).any fun c => c.doneB N && c.drainedB && P c) = true) :
    ∃ d, P d = true ∧ ∃ σ : TPerm N, Csl.OReach .tso N c0.cfg.toO (permCfg d.ocfg σ.f) ∧
      (permCfg d.ocfg σ.f).Drained ∧ ∀ t < N, ((permCfg d.ocfg σ.f).ts t).1 = .skip := by
  simp only [List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨d, hd, ⟨h1, h2⟩, h3⟩ := h
  obtain ⟨σ, hr⟩ := symStates_reach hl hbl hd
  refine ⟨d, h3, σ, ?_, permCfg_drained σ (drained_of h2), permCfg_fin σ (done_of h1)⟩
  rw [toO_ocfg he]
  exact hr

end Silmaril.Proofs.X86.Concurrency.Cir.Robust
