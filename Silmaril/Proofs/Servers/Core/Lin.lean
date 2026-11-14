module

public import Silmaril.Servers.Core.Defs

/-!
# Proofs: linearizability, atomic sentences and the atomic-handler server

The proofs behind `Silmaril.Servers.Core.Thms`: the atomic-handler server of a machine has
exactly the linearizable traces; linearizable traces are well formed; for stateless machines,
linearizability is the atomic sentence; morphisms map linearizable traces.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Core

open Silmaril.Servers

variable {A : Sig}

/-! ## The atomic-handler server -/

theorem server_steps {σ : Type} {M : Machine A σ} {x y : σ × LMon A} {t' : List (LEvent A)}
    (h : Steps (Machine.serverStep M) x t' y) :
    Steps LMon.Step x.2 t' y.2 ∧ M.Run x.1 (LEvent.lins t') y.1 := by
  induction h with
  | nil s => exact ⟨.nil _, .nil _⟩
  | @cons s s' s'' e es hs _ ih =>
    obtain ⟨q, m⟩ := s
    obtain ⟨q', m'⟩ := s'
    cases e with
    | ev e =>
      simp only [Machine.serverStep] at hs
      obtain ⟨rfl, hm⟩ := hs
      exact ⟨.cons hm ih.1, ih.2⟩
    | lin i r s =>
      simp only [Machine.serverStep] at hs
      exact ⟨.cons hs.2 ih.1, .cons hs.1 ih.2⟩

theorem server_of_steps {σ : Type} {M : Machine A σ} {m m' : LMon A} {t' : List (LEvent A)}
    (h : Steps LMon.Step m t' m') :
    ∀ {q q' : σ}, M.Run q (LEvent.lins t') q' → Steps (Machine.serverStep M) (q, m) t' (q', m') := by
  induction h with
  | nil =>
    intro q q' hr
    have hr : M.Run q [] q' := hr
    cases hr
    exact .nil _
  | @cons m₁ m₂ m₃ e es hs _ ih =>
    intro q q' hr
    cases e with
    | ev e => exact .cons (s' := (q, m₂)) ⟨rfl, hs⟩ (ih hr)
    | lin i r s =>
      have hr : M.Run q ((r, s) :: LEvent.lins es) q' := hr
      cases hr with
      | cons hq hr' => exact .cons (s' := (_, m₂)) ⟨hq, hs⟩ (ih hr')

theorem server_tr_iff {σ : Type} (M : Machine A σ) (q₀ : σ) (t : Trace A) :
    (M.server q₀).Tr t ↔ Sen.lin (M.Hist q₀) t := by
  constructor
  · rintro ⟨t', fin, hs, he⟩
    have H := server_steps hs
    exact ⟨t', ⟨fin.2, H.1⟩, he, ⟨fin.1, H.2⟩⟩
  · rintro ⟨t', ⟨m, hm⟩, he, ⟨q, hq⟩⟩
    exact ⟨t', (q, m), server_of_steps hm hq, he⟩

/-! ## Stateless machines -/

theorem hist_ofRel (R : A.Req → A.Resp → Prop) :
    (Machine.ofRel R).Hist () = SeqSpec.pointwise R := by
  funext h
  apply propext
  induction h with
  | nil => exact ⟨fun _ p hp => (nomatch hp), fun _ => ⟨(), .nil _⟩⟩
  | cons p h ih =>
    obtain ⟨r, s⟩ := p
    constructor
    · rintro ⟨q, hr⟩
      cases hr with
      | @cons _ q' _ _ _ _ hq hr' =>
        cases q'
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hq
        · exact ih.1 ⟨q, hr'⟩ p hp
    · intro H
      obtain ⟨q, hr⟩ := ih.2 (fun p hp => H p (List.mem_cons_of_mem _ hp))
      exact ⟨q, .cons (q' := ()) (H (r, s) (by simp)) hr⟩

/-! ## Linearizable traces are well formed -/

/-- The well-formedness monitor a linearization monitor stands for: a request is open while it
is pending or its response is ready. -/
def toW (m : LMon A) : WMon A :=
  ⟨m.req, fun i => match m.pending i, m.ready i with
    | some r, _ => some r
    | none, some _ => m.req i
    | none, none => none⟩

/-- The invariant of the linearization monitor. -/
abbrev LInv (m : LMon A) : Prop := m.Inv

theorem lInv_init : LInv (LMon.init A) :=
  ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem wf_of_lsteps {m m' : LMon A} {t' : List (LEvent A)} (h : Steps LMon.Step m t' m') :
    LInv m → ∃ w', Steps WMon.Step (toW m) (LEvent.erase t') w' := by
  induction h with
  | nil => exact fun _ => ⟨_, .nil _⟩
  | @cons m₁ m₂ m₃ e es hs _ ih =>
    intro hI
    obtain ⟨hP, hR⟩ := hI
    cases hs with
    | @recv i r hreq =>
      have hpi : m₁.pending i = none := by
        cases hp : m₁.pending i with
        | none => rfl
        | some r' => rw [(hP i r' hp).1] at hreq; cases hreq
      have hri : m₁.ready i = none := by
        cases hr : m₁.ready i with
        | none => rfl
        | some s' => obtain ⟨r', hr'⟩ := hR i s' hr; rw [hr'] at hreq; cases hreq
      have hI' : LInv (⟨Function.update m₁.req i (some r), Function.update m₁.pending i (some r),
          m₁.ready⟩ : LMon A) := by
        refine ⟨fun j r' hj => ?_, fun j s' hj => ?_⟩
        · by_cases hji : j = i
          · subst hji; simp at hj; subst hj; simp [hri]
          · simp [hji] at hj ⊢; exact hP j r' hj
        · by_cases hji : j = i
          · subst hji; rw [hri] at hj; cases hj
          · simp [hji]; exact hR j s' hj
      obtain ⟨w', hw'⟩ := ih hI'
      have heq : toW (⟨Function.update m₁.req i (some r), Function.update m₁.pending i (some r),
          m₁.ready⟩ : LMon A) = ⟨Function.update (toW m₁).req i (some r),
          Function.update (toW m₁).open_ i (some r)⟩ := by
        simp only [toW, WMon.mk.injEq, true_and]
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji]
      rw [heq] at hw'
      exact ⟨w', .cons (WMon.Step.recv hreq) hw'⟩
    | @lin i r s hp =>
      obtain ⟨hreq, hrdy⟩ := hP i r hp
      have hI' : LInv (⟨m₁.req, Function.update m₁.pending i none,
          Function.update m₁.ready i (some s)⟩ : LMon A) := by
        refine ⟨fun j r' hj => ?_, fun j s' hj => ?_⟩
        · by_cases hji : j = i
          · subst hji; simp at hj
          · simp [hji] at hj ⊢; exact hP j r' hj
        · by_cases hji : j = i
          · subst hji; exact ⟨r, hreq⟩
          · simp [hji] at hj; exact hR j s' hj
      obtain ⟨w', hw'⟩ := ih hI'
      have heq : toW (⟨m₁.req, Function.update m₁.pending i none,
          Function.update m₁.ready i (some s)⟩ : LMon A) = toW m₁ := by
        simp only [toW, WMon.mk.injEq, true_and]
        funext j
        by_cases hji : j = i
        · subst hji; simp [hp, hreq]
        · simp [hji]
      rw [heq] at hw'
      exact ⟨w', hw'⟩
    | @send i s hr =>
      have hpi : m₁.pending i = none := by
        cases hp : m₁.pending i with
        | none => rfl
        | some r' => rw [(hP i r' hp).2] at hr; cases hr
      obtain ⟨r, hreq⟩ := hR i s hr
      have hI' : LInv (⟨m₁.req, m₁.pending, Function.update m₁.ready i none⟩ : LMon A) := by
        refine ⟨fun j r' hj => ?_, fun j s' hj => ?_⟩
        · by_cases hji : j = i
          · subst hji; rw [hpi] at hj; cases hj
          · simp [hji]; exact hP j r' hj
        · by_cases hji : j = i
          · subst hji; simp at hj
          · simp [hji] at hj; exact hR j s' hj
      obtain ⟨w', hw'⟩ := ih hI'
      have hopen : (toW m₁).open_ i = some r := by simp [toW, hpi, hr, hreq]
      have heq : toW (⟨m₁.req, m₁.pending, Function.update m₁.ready i none⟩ : LMon A) =
          ⟨(toW m₁).req, Function.update (toW m₁).open_ i none⟩ := by
        simp only [toW, WMon.mk.injEq, true_and]
        funext j
        by_cases hji : j = i
        · subst hji; simp [hpi]
        · simp [hji]
      rw [heq] at hw'
      exact ⟨w', .cons (WMon.Step.send (s := s) hopen) hw'⟩

theorem wf_of_lin {S : SeqSpec A} {t : Trace A} (h : Sen.lin S t) : Sen.WF t := by
  obtain ⟨t', ⟨m, hm⟩, rfl, _⟩ := h
  exact wf_of_lsteps hm lInv_init

/-! ## Stateless machines: linearizable iff atomic -/

/-- The invariant of a linearization monitor run whose history `R` allows. -/
def AInv (R : A.Req → A.Resp → Prop) (m : LMon A) : Prop :=
  (∀ i s, m.ready i = some s → ∃ r, m.req i = some r ∧ R r s) ∧
  (∀ i r, m.pending i = some r → m.req i = some r)

theorem atomic_of_lsteps {R : A.Req → A.Resp → Prop} {m m' : LMon A} {t' : List (LEvent A)}
    (h : Steps LMon.Step m t' m') : AInv R m → SeqSpec.pointwise R (LEvent.lins t') →
    (∀ i r, m.req i = some r → m'.req i = some r) ∧
    (∀ i r, Event.recv i r ∈ LEvent.erase t' → m'.req i = some r) ∧
    (∀ i s, Event.send i s ∈ LEvent.erase t' → ∃ r, m'.req i = some r ∧ R r s) := by
  induction h with
  | nil => exact fun _ _ => ⟨fun _ _ h => h, fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | @cons m₁ m₂ m₃ e es hs _ ih =>
    intro hI hL
    obtain ⟨hR, hP⟩ := hI
    cases hs with
    | @recv i r hreq =>
      have hI' : AInv R (⟨Function.update m₁.req i (some r),
          Function.update m₁.pending i (some r), m₁.ready⟩ : LMon A) := by
        refine ⟨fun j s' hj => ?_, fun j r' hj => ?_⟩
        · obtain ⟨r', hr', hR'⟩ := hR j s' hj
          have hji : j ≠ i := by rintro rfl; rw [hr'] at hreq; cases hreq
          exact ⟨r', by simp [hji, hr'], hR'⟩
        · by_cases hji : j = i
          · subst hji; simp at hj ⊢; exact hj
          · simp [hji] at hj ⊢; exact hP j r' hj
      obtain ⟨ih1, ih2, ih3⟩ := ih hI' hL
      refine ⟨fun j r' hj => ih1 j r' ?_, fun j r' hj => ?_, fun j s' hj => ?_⟩
      · have hji : j ≠ i := by rintro rfl; rw [hj] at hreq; cases hreq
        simp [hji, hj]
      · rcases List.mem_cons.1 hj with hj | hj
        · cases hj; exact ih1 _ _ (by simp)
        · exact ih2 j r' hj
      · rcases List.mem_cons.1 hj with hj | hj
        · cases hj
        · exact ih3 j s' hj
    | @lin i r s hp =>
      have hrs : R r s := hL (r, s) (by simp [LEvent.lins])
      have hL' : SeqSpec.pointwise R (LEvent.lins es) :=
        fun p hp' => hL p (List.mem_cons_of_mem _ hp')
      have hI' : AInv R (⟨m₁.req, Function.update m₁.pending i none,
          Function.update m₁.ready i (some s)⟩ : LMon A) := by
        refine ⟨fun j s' hj => ?_, fun j r' hj => ?_⟩
        · by_cases hji : j = i
          · subst hji; simp at hj; subst hj; exact ⟨r, hP _ _ hp, hrs⟩
          · simp [hji] at hj; exact hR j s' hj
        · by_cases hji : j = i
          · subst hji; simp at hj
          · simp [hji] at hj; exact hP j r' hj
      obtain ⟨ih1, ih2, ih3⟩ := ih hI' hL'
      exact ⟨ih1, ih2, ih3⟩
    | @send i s hr =>
      have hI' : AInv R (⟨m₁.req, m₁.pending, Function.update m₁.ready i none⟩ : LMon A) := by
        refine ⟨fun j s' hj => ?_, hP⟩
        by_cases hji : j = i
        · subst hji; simp at hj
        · simp [hji] at hj; exact hR j s' hj
      obtain ⟨ih1, ih2, ih3⟩ := ih hI' hL
      refine ⟨ih1, fun j r' hj => ?_, fun j s' hj => ?_⟩
      · rcases List.mem_cons.1 hj with hj | hj
        · cases hj
        · exact ih2 j r' hj
      · rcases List.mem_cons.1 hj with hj | hj
        · cases hj
          obtain ⟨r', hr', hR'⟩ := hR _ _ hr
          exact ⟨r', ih1 _ _ hr', hR'⟩
        · exact ih3 j s' hj

theorem atomic_of_lin {R : A.Req → A.Resp → Prop} {t : Trace A}
    (h : Sen.lin (SeqSpec.pointwise R) t) : Sen.atomic R t := by
  obtain ⟨t', ⟨m, hm⟩, rfl, hL⟩ := h
  obtain ⟨_, h2, h3⟩ := atomic_of_lsteps hm ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩ hL
  intro i r s hr hs
  obtain ⟨r', hr', hR⟩ := h3 i s hs
  rw [h2 i r hr] at hr'
  cases hr'
  exact hR

/-- The linearization monitor of a well-formedness monitor: nothing computed and unsent. -/
def toL (w : WMon A) : LMon A := ⟨w.req, w.open_, fun _ => none⟩

theorem lin_of_wsteps {R : A.Req → A.Resp → Prop} {w w' : WMon A} {t : Trace A}
    (h : Steps WMon.Step w t w') :
    (∀ i r, w.open_ i = some r → w.req i = some r) →
    (∀ i r s, (w.req i = some r ∨ Event.recv i r ∈ t) → Event.send i s ∈ t → R r s) →
    ∃ t' m', Steps LMon.Step (toL w) t' m' ∧ LEvent.erase t' = t ∧
      SeqSpec.pointwise R (LEvent.lins t') := by
  induction h with
  | nil w => exact fun _ _ => ⟨[], _, .nil _, rfl, fun _ h => (nomatch h)⟩
  | @cons w₁ w₂ w₃ e es hs _ ih =>
    intro hO hA
    cases hs with
    | @recv i r hreq =>
      have hO' : ∀ j r', (Function.update w₁.open_ i (some r)) j = some r' →
          (Function.update w₁.req i (some r)) j = some r' := by
        intro j r' hj
        by_cases hji : j = i
        · subst hji; simp at hj ⊢; exact hj
        · simp [hji] at hj ⊢; exact hO j r' hj
      have hA' : ∀ j r' s, ((Function.update w₁.req i (some r)) j = some r' ∨
          Event.recv j r' ∈ es) → Event.send j s ∈ es → R r' s := by
        intro j r' s hj hs
        refine hA j r' s ?_ (List.mem_cons_of_mem _ hs)
        rcases hj with hj | hj
        · by_cases hji : j = i
          · subst hji; simp at hj; subst hj; exact Or.inr (by simp)
          · simp [hji] at hj; exact Or.inl hj
        · exact Or.inr (List.mem_cons_of_mem _ hj)
      obtain ⟨t', m', ht', he, hL⟩ := ih hO' hA'
      exact ⟨.ev (.recv i r) :: t', m', .cons (LMon.Step.recv hreq) ht', by simp [LEvent.erase, ← he],
        hL⟩
    | @send i r s hopen =>
      have hreq := hO i r hopen
      have hrs : R r s := hA i r s (Or.inl hreq) (by simp)
      have hO' : ∀ j r', (Function.update w₁.open_ i none) j = some r' → w₁.req j = some r' := by
        intro j r' hj
        by_cases hji : j = i
        · subst hji; simp at hj
        · simp [hji] at hj; exact hO j r' hj
      have hA' : ∀ j r' s', (w₁.req j = some r' ∨ Event.recv j r' ∈ es) →
          Event.send j s' ∈ es → R r' s' := by
        intro j r' s' hj hs
        refine hA j r' s' ?_ (List.mem_cons_of_mem _ hs)
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr (List.mem_cons_of_mem _ hj)
      obtain ⟨t', m', ht', he, hL⟩ := ih hO' hA'
      have hlin : LMon.Step (toL w₁) (.lin i r s)
          ⟨w₁.req, Function.update w₁.open_ i none, Function.update (fun _ => none) i (some s)⟩ :=
        LMon.Step.lin hopen
      have hsend : LMon.Step
          ⟨w₁.req, Function.update w₁.open_ i none, Function.update (fun _ => none) i (some s)⟩
          (.ev (.send i s)) (toL ⟨w₁.req, Function.update w₁.open_ i none⟩) := by
        have heq : (⟨w₁.req, Function.update w₁.open_ i none,
            Function.update (Function.update (fun _ => none) i (some s)) i none⟩ : LMon A) =
            toL ⟨w₁.req, Function.update w₁.open_ i none⟩ := by
          simp only [toL]
          congr 1
          funext j
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
        rw [← heq]
        exact LMon.Step.send (by simp)
      refine ⟨.lin i r s :: .ev (.send i s) :: t', m', .cons hlin (.cons hsend ht'), ?_, ?_⟩
      · simp [LEvent.erase, ← he]
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hrs
        · exact hL p hp

theorem lin_of_atomic {R : A.Req → A.Resp → Prop} {t : Trace A} (hw : Sen.WF t)
    (h : Sen.atomic R t) : Sen.lin (SeqSpec.pointwise R) t := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t', m', ht', he, hL⟩ := lin_of_wsteps (R := R) hw (fun _ _ h => (nomatch h))
    (fun i r s hr hs => by
      rcases hr with hr | hr
      · exact (nomatch hr)
      · exact h i r s hr hs)
  exact ⟨t', ⟨m', ht'⟩, he, hL⟩

/-! ## Monotonicity -/

theorem run_mono {σ : Type} {M M' : Machine A σ} (hM : ∀ q r s q', M q r s q' → M' q r s q')
    {q q' : σ} {h : History A} (hr : M.Run q h q') : M'.Run q h q' := by
  induction hr with
  | nil => exact .nil _
  | cons hq _ ih => exact .cons (hM _ _ _ _ hq) ih

theorem lin_mono {S S' : SeqSpec A} (hS : S ≤ S') : Sen.lin S ≤ Sen.lin S' :=
  fun _ ⟨t', hv, he, hs⟩ => ⟨t', hv, he, hS _ hs⟩

theorem server_mono {σ : Type} {M M' : Machine A σ} (hM : ∀ q r s q', M q r s q' → M' q r s q')
    (q₀ : σ) : M.server q₀ ≤ M'.server q₀ := by
  intro t ht
  exact (server_tr_iff M' q₀ t).2
    (lin_mono (fun _ ⟨q, hq⟩ => ⟨q, run_mono hM hq⟩) t ((server_tr_iff M q₀ t).1 ht))

/-! ## Morphisms -/

section Hom

variable {B : Sig} (h : Hom A B)

/-- What `A` sees of an annotated event of `B`. -/
def lmap : LEvent B → LEvent A
  | .ev e => .ev (h.event e)
  | .lin i r s => .lin i (h.req r) (h.resp s)

/-- What `A` sees of a linearization monitor of `B`. -/
def mmap (m : LMon B) : LMon A :=
  ⟨fun i => (m.req i).map h.req, fun i => (m.pending i).map h.req,
    fun i => (m.ready i).map h.resp⟩

theorem map_update {α β : Type} (f : ReqId → Option α) (g : α → β) (i : ReqId) (a : Option α) :
    (fun j => (Function.update f i a j).map g) = Function.update (fun j => (f j).map g) i (a.map g) := by
  funext j
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

theorem erase_lmap (t' : List (LEvent B)) :
    LEvent.erase (t'.map (lmap h)) = h.trace (LEvent.erase t') := by
  induction t' with
  | nil => rfl
  | cons e t' ih =>
    cases e with
    | ev e => simp only [List.map_cons, lmap, LEvent.erase, List.filterMap_cons, Hom.trace,
        List.map_cons] at ih ⊢; rw [ih]
    | lin i r s => simp only [List.map_cons, lmap, LEvent.erase, List.filterMap_cons] at ih ⊢
                   exact ih

theorem lins_lmap (t' : List (LEvent B)) :
    LEvent.lins (t'.map (lmap h)) = h.history (LEvent.lins t') := by
  induction t' with
  | nil => rfl
  | cons e t' ih =>
    cases e with
    | ev e => simp only [List.map_cons, lmap, LEvent.lins, List.filterMap_cons] at ih ⊢
              exact ih
    | lin i r s => simp only [List.map_cons, lmap, LEvent.lins, List.filterMap_cons, Hom.history,
        List.map_cons] at ih ⊢; rw [ih]

theorem steps_lmap {m m' : LMon B} {t' : List (LEvent B)} (hs : Steps LMon.Step m t' m') :
    Steps LMon.Step (mmap h m) (t'.map (lmap h)) (mmap h m') := by
  induction hs with
  | nil => exact .nil _
  | @cons m₁ m₂ m₃ e es hs _ ih =>
    refine .cons ?_ ih
    cases hs with
    | @recv i r hreq =>
      have heq : mmap h (⟨Function.update m₁.req i (some r), Function.update m₁.pending i (some r),
          m₁.ready⟩ : LMon B) = ⟨Function.update (mmap h m₁).req i (some (h.req r)),
          Function.update (mmap h m₁).pending i (some (h.req r)), (mmap h m₁).ready⟩ := by
        simp only [mmap]
        congr 1
        · exact map_update _ _ _ _
        · exact map_update _ _ _ _
      rw [heq]
      exact LMon.Step.recv (by simp [mmap, hreq])
    | @lin i r s hp =>
      have heq : mmap h (⟨m₁.req, Function.update m₁.pending i none,
          Function.update m₁.ready i (some s)⟩ : LMon B) = ⟨(mmap h m₁).req,
          Function.update (mmap h m₁).pending i none,
          Function.update (mmap h m₁).ready i (some (h.resp s))⟩ := by
        simp only [mmap]
        congr 1
        · exact map_update _ _ _ _
        · exact map_update _ _ _ _
      rw [heq]
      exact LMon.Step.lin (by simp [mmap, hp])
    | @send i s hr =>
      have heq : mmap h (⟨m₁.req, m₁.pending, Function.update m₁.ready i none⟩ : LMon B) =
          ⟨(mmap h m₁).req, (mmap h m₁).pending, Function.update (mmap h m₁).ready i none⟩ := by
        simp only [mmap]
        congr 1
        exact map_update _ _ _ _
      rw [heq]
      exact LMon.Step.send (by simp [mmap, hr])

theorem lin_trace {S : SeqSpec A} {t : Trace B} (hl : Sen.lin (h.seq S) t) :
    Sen.lin S (h.trace t) := by
  obtain ⟨t', ⟨m, hm⟩, rfl, hS⟩ := hl
  refine ⟨t'.map (lmap h), ⟨mmap h m, ?_⟩, erase_lmap h t', ?_⟩
  · exact steps_lmap h hm
  · rw [lins_lmap]; exact hS

theorem sen_atomic (R : A.Req → A.Resp → Prop) :
    h.sen (Sen.atomic R) = Sen.atomic fun r s => R (h.req r) (h.resp s) := by
  funext t
  apply propext
  constructor
  · intro H i r s hr hs
    exact H i (h.req r) (h.resp s) (List.mem_map_of_mem hr) (List.mem_map_of_mem hs)
  · intro H i r s hr hs
    obtain ⟨e, he, hee⟩ := List.mem_map.1 hr
    obtain ⟨e', he', hee'⟩ := List.mem_map.1 hs
    cases e with
    | send => cases hee
    | recv i₁ r₁ =>
      cases e' with
      | recv => cases hee'
      | send i₂ s₂ =>
        simp only [Hom.event, Event.recv.injEq, Event.send.injEq] at hee hee'
        obtain ⟨rfl, rfl⟩ := hee
        obtain ⟨rfl, rfl⟩ := hee'
        exact H _ _ _ he he'

end Hom

end Silmaril.Proofs.Servers.Core
