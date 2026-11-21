module

public import Silmaril.X86.MemoryModel.Xl.Thms

/-!
# Localisation: carrying consistency along a partial map of units

A candidate `x'` whose units are partly **kept** units of a candidate
`x` (a partial map `κ` from the units of `x'` to those of `x`), with the same fields up to
thread and position (`Same`), the same `po`, `sm`, `rf`, `co`, `fr` and locked pairs between kept units, and
closed in the sense of `Emb` (fences, locked units, units of a kept access and units sharing a
byte with a kept unit are kept). Then:

* `Emb.scRel`, `Emb.uniproc`, `Emb.ghb`, `Emb.uniprocXl`, `Emb.thinAir`, `Emb.ghbXl`: every
  edge of a model relation of `x'` between kept units is the same edge of `x`;
* `Emb.atomic`: locked-RMW atomicity carries over;
* `acyclic_of_shortcut`: a relation whose kept edges are old paths, whose edges between
  non-kept units increase a rank, and whose detours through non-kept units are short-cut by old
  paths, is acyclic when the old relation is.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Relation

/-! ## Units up to position -/

/-- Two units agree on every field except the thread and the position. -/
def Same (e e' : Ev) : Prop := { e with tid := 0, pos := 0 } = { e' with tid := 0, pos := 0 }

theorem Same.refl (e : Ev) : Same e e := rfl

theorem Same.symm {e e' : Ev} (h : Same e e') : Same e' e := Eq.symm h

theorem Same.app {α : Sort _} {g : Ev → α} (hg : ∀ e, g e = g { e with tid := 0, pos := 0 })
    {e e' : Ev}
    (h : Same e e') : g e = g e' := by
  rw [hg e, hg e']; exact congrArg g h

theorem Same.act {e e' : Ev} (h : Same e e') : e.act = e'.act := Same.app (g := Ev.act) (fun _ => rfl) h
theorem Same.isR {e e' : Ev} (h : Same e e') : e.isR = e'.isR := Same.app (g := Ev.isR) (fun _ => rfl) h
theorem Same.isW {e e' : Ev} (h : Same e e') : e.isW = e'.isW := Same.app (g := Ev.isW) (fun _ => rfl) h
theorem Same.isM {e e' : Ev} (h : Same e e') : e.isM = e'.isM := Same.app (g := Ev.isM) (fun _ => rfl) h
theorem Same.isA {e e' : Ev} (h : Same e e') : e.isA = e'.isA := Same.app (g := Ev.isA) (fun _ => rfl) h
theorem Same.weak {e e' : Ev} (h : Same e e') : e.weak = e'.weak := Same.app (g := Ev.weak) (fun _ => rfl) h
theorem Same.isFence {e e' : Ev} (k) (h : Same e e') : e.isFence k = e'.isFence k :=
  Same.app (g := fun e => Ev.isFence k e) (fun _ => rfl) h
theorem Same.covers {e e' : Ev} (h : Same e e') : e.covers = e'.covers :=
  Same.app (g := Ev.covers) (fun _ => rfl) h
theorem Same.bytes {e e' : Ev} (h : Same e e') : e.bytes = e'.bytes :=
  Same.app (g := Ev.bytes) (fun _ => rfl) h
theorem Same.byte {e e' : Ev} (h : Same e e') : e.byte = e'.byte :=
  Same.app (g := Ev.byte) (fun _ => rfl) h
theorem Same.singleCopy {e e' : Ev} (h : Same e e') : e.singleCopy = e'.singleCopy :=
  Same.app (g := Ev.singleCopy) (fun _ => rfl) h
theorem Same.accAddr {e e' : Ev} (h : Same e e') : e.accAddr = e'.accAddr :=
  Same.app (g := Ev.accAddr) (fun _ => rfl) h
theorem Same.accSize {e e' : Ev} (h : Same e e') : e.accSize = e'.accSize :=
  Same.app (g := Ev.accSize) (fun _ => rfl) h
theorem Same.accOverlap {e e' f f' : Ev} (h : Same e e') (h' : Same f f') :
    e.accOverlap f = e'.accOverlap f' := by
  simp only [Ev.accOverlap, h.accAddr, h.accSize, h'.accAddr, h'.accSize]

/-! ## Partial embeddings -/

/-- `κ` maps the kept units of `x'` to units of `x`, preserving everything the models see. -/
structure Emb (x x' : Exec) (κ : Fin x'.n → Option (Fin x.n)) : Prop where
  same : ∀ a a0, κ a = some a0 → Same (x'.ev a) (x.ev a0)
  po : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → x'.po a b = x.po a0 b0
  sm : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → x'.sm a b = x.sm a0 b0
  ext : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → x'.ext a b = x.ext a0 b0
  rf : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → x'.rfR a b = x.rfR a0 b0
  co : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → x'.coR a b = x.coR a0 b0
  fr : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → x'.frR a b = x.frR a0 b0
  rmw : ∀ a b, x'.rmwR a b = true → ∃ a0 b0, κ a = some a0 ∧ κ b = some b0 ∧ x.rmwR a0 b0 = true
  fence : ∀ f, (x'.ev f).isM = false → (κ f).isSome
  locked : ∀ l, (x'.ev l).isA = true → (κ l).isSome
  smK : ∀ c b, (κ b).isSome → x'.sm c b = true → (κ c).isSome
  locK : ∀ a c, (κ a).isSome → x'.loc a c = true → (κ c).isSome
  tear : ∀ a a0, κ a = some a0 → x.tearable a0 = true → x'.tearable a = true

namespace Emb

variable {x x' : Exec} {κ : Fin x'.n → Option (Fin x.n)} (E : Emb x x' κ)
include E

omit E in
theorem some_of {a : Fin x'.n} (h : (κ a).isSome) : ∃ a0, κ a = some a0 :=
  Option.isSome_iff_exists.mp h

theorem loc {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) : x'.loc a b = x.loc a0 b0 := by
  simp only [Exec.loc, (E.same a a0 ha).isM, (E.same b b0 hb).isM, (E.same a a0 ha).bytes,
    (E.same b b0 hb).covers]

theorem com {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) : x'.com a b = x.com a0 b0 := by
  simp only [Exec.com, BRel.union, E.rf a b a0 b0 ha hb, E.co a b a0 b0 ha hb, E.fr a b a0 b0 ha hb]

theorem poLoc {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) :
    x'.poLoc a b = x.poLoc a0 b0 := by
  simp only [Exec.poLoc, BRel.inter, E.po a b a0 b0 ha hb, E.loc ha hb]

theorem ppo {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) : x'.ppo a b = x.ppo a0 b0 := by
  simp only [Exec.ppo, E.po a b a0 b0 ha hb, (E.same a a0 ha).isW, (E.same b b0 hb).isW,
    (E.same a a0 ha).isR, (E.same b b0 hb).isM]

theorem ppoXl {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) :
    x'.ppoXl a b = x.ppoXl a0 b0 := by
  simp only [Exec.ppoXl, E.ppo ha hb, (E.same a a0 ha).weak, (E.same b b0 hb).weak]

theorem implied {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) :
    x'.implied a b = x.implied a0 b0 := by
  simp only [Exec.implied, E.po a b a0 b0 ha hb, (E.same a a0 ha).isW, (E.same b b0 hb).isR,
    (E.same a a0 ha).isA, (E.same b b0 hb).isA]

theorem rfe {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) : x'.rfe a b = x.rfe a0 b0 := by
  simp only [Exec.rfe, BRel.inter, E.rf a b a0 b0 ha hb, E.ext a b a0 b0 ha hb]

theorem fre {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) : x'.fre a b = x.fre a0 b0 := by
  simp only [Exec.fre, BRel.inter, E.fr a b a0 b0 ha hb, E.ext a b a0 b0 ha hb]

theorem coe {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) : x'.coe a b = x.coe a0 b0 := by
  simp only [Exec.coe, BRel.inter, E.co a b a0 b0 ha hb, E.ext a b a0 b0 ha hb]

/-- An `sm`-lifted relation: the middle unit is kept. -/
theorem seq_sm {r' : BRel x'.n} {r : BRel x.n}
    (hr : ∀ a c a0 c0, κ a = some a0 → κ c = some c0 → r' a c = true → r a0 c0 = true)
    {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) (h : r'.seq x'.sm a b = true) :
    r.seq x.sm a0 b0 = true := by
  obtain ⟨c, h1, h2⟩ := BRel.seq_elim h
  obtain ⟨c0, hc⟩ := Emb.some_of (E.smK c b (by simp [hb]) h2)
  simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
  exact ⟨c0, List.mem_finRange _, hr a c a0 c0 ha hc h1, by rw [← E.sm c b c0 b0 hc hb]; exact h2⟩

theorem smT {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) (h : x'.smT a b = true) :
    x.smT a0 b0 = true := by
  simp only [Exec.smT, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true']
    at h ⊢
  rcases h with rfl | ⟨h1, h2⟩
  · rw [ha] at hb; cases hb; exact .inl rfl
  · refine .inr ⟨by rw [← E.sm a b a0 b0 ha hb]; exact h1, ?_⟩
    cases ht : x.tearable a0
    · rfl
    · rw [E.tear a a0 ha ht] at h2; cases h2

theorem seq_smT {r' : BRel x'.n} {r : BRel x.n}
    (hr : ∀ a c a0 c0, κ a = some a0 → κ c = some c0 → r' a c = true → r a0 c0 = true)
    {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0) (h : r'.seq x'.smT a b = true) :
    r.seq x.smT a0 b0 = true := by
  obtain ⟨c, h1, h2⟩ := BRel.seq_elim h
  have hcs : (κ c).isSome := by
    simp only [Exec.smT, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h2
    rcases h2 with rfl | ⟨h2, -⟩
    · simp [hb]
    · exact E.smK c b (by simp [hb]) h2
  obtain ⟨c0, hc⟩ := Emb.some_of hcs
  simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
  exact ⟨c0, List.mem_finRange _, hr a c a0 c0 ha hc h1, E.smT hc hb h2⟩

theorem fencerel {k} {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.fencerel k a b = true) : x.fencerel k a0 b0 = true := by
  simp only [Exec.fencerel, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨f, -, ⟨hf, h1⟩, h2⟩ := h
  have hfM : (x'.ev f).isM = false := by
    simp only [Ev.isFence, beq_iff_eq] at hf
    simp [Ev.isM, Ev.isR, Ev.isW, hf]
  obtain ⟨f0, hf0⟩ := Emb.some_of (E.fence f hfM)
  refine ⟨f0, List.mem_finRange _, ⟨?_, ?_⟩, ?_⟩
  · rw [← (E.same f f0 hf0).isFence]; exact hf
  · rw [← E.po a f a0 f0 ha hf0]; exact h1
  · rw [← E.po f b f0 b0 hf0 hb]; exact h2

theorem mfence {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.mfence a b = true) : x.mfence a0 b0 = true := E.fencerel ha hb h

theorem lockXl {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.lockXl a b = true) : x.lockXl a0 b0 = true := by
  simp only [Exec.lockXl, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨⟨by rw [← (E.same a a0 ha).isM]; exact h1, by rw [← (E.same b b0 hb).isM]; exact h2⟩,
    by rw [← E.po a b a0 b0 ha hb]; exact h3⟩, ?_⟩
  rcases h4 with (h4 | h4) | ⟨l, -, ⟨hl, h5⟩, h6⟩
  · exact .inl (.inl (by rw [← (E.same a a0 ha).isA]; exact h4))
  · exact .inl (.inr (by rw [← (E.same b b0 hb).isA]; exact h4))
  · obtain ⟨l0, hl0⟩ := Emb.some_of (E.locked l hl)
    exact .inr ⟨l0, List.mem_finRange _, ⟨by rw [← (E.same l l0 hl0).isA]; exact hl,
      by rw [← E.po a l a0 l0 ha hl0]; exact h5⟩, by rw [← E.po l b l0 b0 hl0 hb]; exact h6⟩

theorem sfenceXl {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.sfenceXl a b = true) : x.sfenceXl a0 b0 = true := by
  simp only [Exec.sfenceXl, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨⟨by rw [← (E.same a a0 ha).isW]; exact h1, by rw [← (E.same b b0 hb).isW]; exact h2⟩,
    E.fencerel ha hb h3⟩

/-- `rfe | fr | co` on kept units. -/
theorem comGhbPart {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : (x'.rfe.union (x'.frR.union x'.coR)) a b = true) :
    (x.rfe.union (x.frR.union x.coR)) a0 b0 = true := by
  simp only [BRel.union, E.rfe ha hb, E.fr a b a0 b0 ha hb, E.co a b a0 b0 ha hb] at h ⊢
  exact h

/-! ## The model relations on kept units -/

theorem scRel {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.scRel a b = true) : x.scRel a0 b0 = true := by
  simp only [Exec.scRel, BRel.union_iff] at h ⊢
  rcases h with h | h
  · exact .inl (by rw [← E.po a b a0 b0 ha hb]; exact h)
  · exact .inr (E.seq_sm (fun a c a0 c0 ha hc h => by rw [← E.com ha hc]; exact h) ha hb h)

theorem uniproc {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.uniproc a b = true) : x.uniproc a0 b0 = true := by
  simp only [Exec.uniproc, BRel.union_iff] at h ⊢
  rcases h with h | h
  · exact .inl (by rw [← E.poLoc ha hb]; exact h)
  · exact .inr (E.seq_sm (fun a c a0 c0 ha hc h => by rw [← E.com ha hc]; exact h) ha hb h)

theorem ghb {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.ghb a b = true) : x.ghb a0 b0 = true := by
  simp only [Exec.ghb, BRel.union_iff] at h ⊢
  rcases h with h | h | h | h
  · exact .inl (E.mfence ha hb h)
  · exact .inr (.inl (by rw [← E.implied ha hb]; exact h))
  · exact .inr (.inr (.inl (by rw [← E.ppo ha hb]; exact h)))
  · exact .inr (.inr (.inr (E.seq_sm (fun a c a0 c0 ha hc h => E.comGhbPart ha hc h) ha hb h)))

theorem uniprocXl {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.uniprocXl a b = true) : x.uniprocXl a0 b0 = true := by
  simp only [Exec.uniprocXl, BRel.union_iff] at h ⊢
  rcases h with h | h
  · exact .inl (by rw [← E.poLoc ha hb]; exact h)
  · exact .inr (E.seq_smT (fun a c a0 c0 ha hc h => by rw [← E.com ha hc]; exact h) ha hb h)

theorem thinAir {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.thinAir a b = true) : x.thinAir a0 b0 = true := by
  simp only [Exec.thinAir, BRel.union_iff] at h ⊢
  rcases h with h | h
  · exact .inl (by rw [← E.po a b a0 b0 ha hb]; exact h)
  · exact .inr (by rw [← E.rf a b a0 b0 ha hb]; exact h)

theorem ghbXl {a b a0 b0} (ha : κ a = some a0) (hb : κ b = some b0)
    (h : x'.ghbXl a b = true) : x.ghbXl a0 b0 = true := by
  simp only [Exec.ghbXl, BRel.union_iff] at h ⊢
  rcases h with h | h | h | h | h
  · exact .inl (E.mfence ha hb h)
  · exact .inr (.inl (by rw [← E.ppoXl ha hb]; exact h))
  · exact .inr (.inr (.inl (E.lockXl ha hb h)))
  · exact .inr (.inr (.inr (.inl (E.sfenceXl ha hb h))))
  · exact .inr (.inr (.inr (.inr
      (E.seq_smT (fun a c a0 c0 ha hc h => E.comGhbPart ha hc h) ha hb h))))

/-- **Atomicity carries over.** -/
theorem atomic (h : x.atomicB = true) : x'.atomicB = true := by
  simp only [Exec.atomicB, BRel.emptyB_iff, BRel.Empty] at h ⊢
  intro a b
  cases hab : (x'.rmwR.inter (x'.fre.seq x'.coe)) a b
  · rfl
  · exfalso
    obtain ⟨h1, h2⟩ := BRel.inter_iff.mp hab
    obtain ⟨a0, b0, ha, hb, h1'⟩ := E.rmw a b h1
    obtain ⟨c, hac, hcb⟩ := BRel.seq_elim h2
    have hloc : x'.loc a c = true := by
      simp only [Exec.fre, BRel.inter_iff, Exec.frR, Bool.and_eq_true] at hac
      obtain ⟨⟨⟨hR, hW⟩, hb'⟩, -⟩ := hac
      simp only [Exec.loc, Ev.isM, hR, hW, Bool.true_or, Bool.or_true, Bool.true_and]
      simp only [List.any_eq_true, Bool.and_eq_true] at hb' ⊢
      obtain ⟨y, hy, hc, -⟩ := hb'
      exact ⟨y, hy, hc⟩
    obtain ⟨c0, hc⟩ := Emb.some_of (E.locK a c (by simp [ha]) hloc)
    have := h a0 b0
    simp only [BRel.inter, Bool.and_eq_false_iff] at this
    rcases this with h3 | h3
    · rw [h1'] at h3; cases h3
    · have : (x.fre.seq x.coe) a0 b0 = true := by
        simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
        exact ⟨c0, List.mem_finRange _, by rw [← E.fre ha hc]; exact hac,
          by rw [← E.coe hc hb]; exact hcb⟩
      rw [this] at h3; cases h3

end Emb

/-! ## Acyclicity through short-cuts -/

section Shortcut

variable {n n' : Nat} (R : BRel n) (R' : BRel n') (κ : Fin n' → Option (Fin n))

/-- A path of `R'` through non-kept units only. -/
def BPath : Fin n' → Fin n' → Prop :=
  ReflTransGen fun u v => κ u = none ∧ κ v = none ∧ R'.Holds u v

variable {R R' κ}

theorem path_kept
    (hkk : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → R' a b = true → TransGen R.Holds a0 b0)
    (hsh : ∀ a b b' c a0 c0, κ a = some a0 → κ c = some c0 → κ b = none → κ b' = none →
      R' a b = true → BPath R' κ b b' → R' b' c = true → TransGen R.Holds a0 c0)
    {u v : Fin n'} (h : TransGen R'.Holds u v) :
    ∀ u0, κ u = some u0 →
      (∀ v0, κ v = some v0 → TransGen R.Holds u0 v0) ∧
      (κ v = none → ∃ c c0, κ c = some c0 ∧ ReflTransGen R.Holds u0 c0 ∧
        ∃ b, κ b = none ∧ R' c b = true ∧ BPath R' κ b v) := by
  induction h with
  | single h =>
    intro u0 hu
    refine ⟨fun v0 hv => hkk _ _ _ _ hu hv h, fun hv => ⟨_, u0, hu, .refl, _, hv, h, .refl⟩⟩
  | @tail w v _ hwv ih =>
    intro u0 hu
    obtain ⟨ih1, ih2⟩ := ih u0 hu
    cases hw : κ w with
    | some w0 =>
      refine ⟨fun v0 hv => (ih1 w0 hw).trans (hkk _ _ _ _ hw hv hwv), fun hv => ?_⟩
      exact ⟨w, w0, hw, (ih1 w0 hw).to_reflTransGen, v, hv, hwv, .refl⟩
    | none =>
      obtain ⟨c, c0, hc, hrc, b, hb, hcb, hbw⟩ := ih2 hw
      refine ⟨fun v0 hv => ?_, fun hv => ⟨c, c0, hc, hrc, b, hb, hcb, hbw.tail ⟨hw, hv, hwv⟩⟩⟩
      exact Relation.TransGen.trans_right hrc (hsh c b w v c0 v0 hc hv hb hw hcb hbw hwv)

theorem path_block (rank : Fin n' → Nat)
    (hbb : ∀ a b, κ a = none → κ b = none → R' a b = true → rank a < rank b)
    {u v : Fin n'} (h : TransGen R'.Holds u v) :
    κ u = none → (κ v = none ∧ rank u < rank v) ∨
      ∃ c, (κ c).isSome ∧ TransGen R'.Holds u c ∧ ReflTransGen R'.Holds c v := by
  induction h with
  | @single v h =>
    intro hu
    cases hv : κ v with
    | none => exact .inl ⟨rfl, hbb _ _ hu hv h⟩
    | some v0 => exact .inr ⟨v, by simp [hv], .single h, .refl⟩
  | @tail w v huw hwv ih =>
    intro hu
    rcases ih hu with ⟨hw, hlt⟩ | ⟨c, hc, h1, h2⟩
    · cases hv : κ v with
      | none => exact .inl ⟨rfl, hlt.trans (hbb _ _ hw hv hwv)⟩
      | some v0 => exact .inr ⟨v, by simp [hv], huw.tail hwv, .refl⟩
    · exact .inr ⟨c, hc, h1, h2.tail hwv⟩

/-- **Acyclicity through short-cuts.** -/
theorem acyclic_of_shortcut (hR : R.Acyclic)
    (hkk : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → R' a b = true → TransGen R.Holds a0 b0)
    (rank : Fin n' → Nat)
    (hbb : ∀ a b, κ a = none → κ b = none → R' a b = true → rank a < rank b)
    (hsh : ∀ a b b' c a0 c0, κ a = some a0 → κ c = some c0 → κ b = none → κ b' = none →
      R' a b = true → BPath R' κ b b' → R' b' c = true → TransGen R.Holds a0 c0) :
    R'.Acyclic := by
  intro z hz
  cases hzk : κ z with
  | some z0 => exact hR z0 ((path_kept hkk hsh hz z0 hzk).1 z0 hzk)
  | none =>
    rcases path_block rank hbb hz hzk with ⟨-, hlt⟩ | ⟨c, hc, h1, h2⟩
    · exact Nat.lt_irrefl _ hlt
    · obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hc
      exact hR c0 ((path_kept hkk hsh (Relation.TransGen.trans_right h2 h1) c0 hc0).1 c0 hc0)

/-- With every unit kept, acyclicity carries over edge by edge. -/
theorem acyclic_of_total (hR : R.Acyclic) (htot : ∀ a, (κ a).isSome)
    (hkk : ∀ a b a0 b0, κ a = some a0 → κ b = some b0 → R' a b = true → R a0 b0 = true) :
    R'.Acyclic :=
  acyclic_of_shortcut hR (fun a b a0 b0 ha hb h => .single (hkk a b a0 b0 ha hb h)) (fun _ => 0)
    (fun a _ ha _ _ => by have := htot a; simp [ha] at this)
    (fun _ b _ _ _ _ _ _ hb _ _ _ => by have := htot b; simp [hb] at this)

end Shortcut

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
