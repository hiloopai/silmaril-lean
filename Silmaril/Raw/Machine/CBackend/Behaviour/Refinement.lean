module

public import Silmaril.Machine.Behaviour.Semantics

/-!
# Refinement and the compilation relation

`Refines mode tgt src Init ob` says: for every pair of initial states related by
`Init` whose source state is safe, every behaviour of the target state
implements (`Outcome.Rel mode`) some behaviour of the source state. The
observation is indexed by the initial pair, because ABI guarantees mention entry
values (callee-saved registers, the return address).

With the identity observation and the strict mode this is behaviour inclusion
on safe states, `P ⊑ Q ↔ Beh P ⊆ Beh Q` (`refines_id_iff`).

Source undefined behaviour is handled by the `Safe` premise: an unsafe source
state constrains nothing, as in CompCert. Since target `undefined` relates only
to source `undefined`, a safe source forces a safe target (`Refines.safe`),
and this is what makes refinement transitive (`Refines.trans`).

`Implements mode src tgt entry Represents ob` is the compilation relation
for one source program: `entry c` is the source state of the call `c`,
and `Represents c t` says that the target state `t` represents it (arguments
in ABI locations, memory mapped, code loaded). It is `Refines` with the
initial relation factored through calls, so that the observation may mention
the call.

A compiler error is never an instance of `Implements`: an instance is a
theorem about one target semantics and one `Represents`. It holds trivially in
two ways: when `Represents` is empty, and when every run from a represented
state gets stuck, since a stuck run has no behaviour (`Semantics.Beh`) and
`Implements` only constrains target behaviours. A target stuck everywhere
therefore implements every source in every mode. `Implements.Nonvacuous tgt
Admissible Represents` excludes both: every admissible call has a representing
target state (`Implements.Represented`), and no run from a represented state
gets stuck (`Implements.Live`, from `Semantics.ProgressFrom`; it follows from
`Semantics.Progress` by `Nonvacuous.of_progress`). `Implements.exists_beh` is
what a nonvacuous instance delivers for an admissible call with a safe entry
state: a represented target state that has a behaviour, each of whose
behaviours implements a source behaviour. The same caveat applies to `Refines`
and to `Refinement`: a stuck target refines anything. The closure rules
(`Implements.close`, `Refines.trans`) do not transfer liveness; it is proved for
each target semantics separately.

Proved here: reflexivity, monotonicity, transitivity (vertical composition,
in the join of the modes), the backward direction from forward simulation and
target determinism (`Refines.of_forward`), the two-sided
`Refines.Exactly` and `Implements.Exactly` (the latter from liveness and source
determinism, `Implements.exactly_of_live`), and closure of `Implements` under target refinement
(`Implements.close`, the `Implements ∘ Equiv ⊆ Implements` rule). Not provided: horizontal composition (linking), open semantics with
calls to unknown code, and event traces or host I/O.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

open Relation Semantics

variable {S S' S'' R R' R'' T T' T'' F F' F'' : Type*}

/-- Target `tgt` refines source `src` from initial pairs in `Init`, observing
payloads by `ob`. Oriented target to source. -/
def Refines (mode : Mode) (tgt : Semantics S' R' T' F') (src : Semantics S R T F)
    (Init : S' → S → Prop) (ob : S' → S → Obs R' R T' T F' F) : Prop :=
  ∀ t s, Init t s → src.Safe s → ∀ o, tgt.Beh t o →
    ∃ o', src.Beh s o' ∧ Outcome.Rel mode (ob t s) o o'

namespace Refines

variable {m m' m₁ m₂ : Mode}

/-- A safe source state forces a safe target state. -/
theorem safe {tgt : Semantics S' R' T' F'} {src : Semantics S R T F} {I : S' → S → Prop}
    {ob : S' → S → Obs R' R T' T F' F} (h : Refines m tgt src I ob) {t : S'} {s : S}
    (hI : I t s) (hs : src.Safe s) : tgt.Safe t := fun hu => by
  obtain ⟨o', hb, hr⟩ := h t s hI hs _ hu
  rw [Outcome.Rel.undefined_left] at hr
  subst hr
  exact hs hb

theorem refl (m : Mode) (P : Semantics S R T F) {ob : S → S → Obs R R T T F F}
    (hob : ∀ s, (ob s s).IsRefl) : Refines m P P Eq ob := by
  rintro t s rfl - o h
  exact ⟨o, h, Outcome.Rel.refl (hob t) m o⟩

/-- Weakening: a larger mode, a smaller initial relation, a larger observation. -/
theorem mono {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
    {I I' : S' → S → Prop} {ob ob' : S' → S → Obs R' R T' T F' F}
    (hm : m ≤ m') (hI : ∀ t s, I' t s → I t s) (hob : ∀ t s, I' t s → ob t s ≤ ob' t s)
    (h : Refines m tgt src I ob) : Refines m' tgt src I' ob' := by
  intro t s hI' hs o hb
  obtain ⟨o', hb', hr⟩ := h t s (hI t s hI') hs o hb
  exact ⟨o', hb', hr.mono hm (hob t s hI')⟩

/-- Vertical composition. The composite is in the join of the two modes; the
middle initial state is supplied by `hI`, and the composite observation must be
covered by `ob`. -/
theorem trans {A : Semantics S R T F} {B : Semantics S' R' T' F'}
    {C : Semantics S'' R'' T'' F''} {I₁ : S → S' → Prop} {I₂ : S' → S'' → Prop}
    {I : S → S'' → Prop} {ob₁ : S → S' → Obs R R' T T' F F'}
    {ob₂ : S' → S'' → Obs R' R'' T' T'' F' F''} {ob : S → S'' → Obs R R'' T T'' F F''}
    (h₁ : Refines m₁ A B I₁ ob₁) (h₂ : Refines m₂ B C I₂ ob₂)
    (hI : ∀ a c, I a c → ∃ b, I₁ a b ∧ I₂ b c)
    (hob : ∀ a b c, I a c → I₁ a b → I₂ b c → (ob₁ a b).comp (ob₂ b c) ≤ ob a c) :
    Refines (m₁ ⊔ m₂) A C I ob := by
  intro a c hac hc o ho
  obtain ⟨b, hab, hbc⟩ := hI a c hac
  have hb : B.Safe b := h₂.safe hbc hc
  obtain ⟨p, hp, hop⟩ := h₁ a b hab hb o ho
  obtain ⟨q, hq, hpq⟩ := h₂ b c hbc hc p hp
  exact ⟨q, hq, (hop.trans hpq).mono le_rfl (hob a b c hac hab hbc)⟩

/-- The backward direction from a forward simulation and target determinism
. `htot` asks that every safe related source state have a behaviour, for
instance by `Beh.exists`. -/
theorem of_forward {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
    {I : S' → S → Prop} {ob : S' → S → Obs R' R T' T F' F}
    (hdet : tgt.Deterministic) (htot : ∀ t s, I t s → src.Safe s → ∃ o', src.Beh s o')
    (fwd : ∀ t s, I t s → src.Safe s → ∀ o', src.Beh s o' →
      ∃ o, tgt.Beh t o ∧ Outcome.Rel m (ob t s) o o') :
    Refines m tgt src I ob := by
  intro t s hI hs o ho
  obtain ⟨o', ho'⟩ := htot t s hI hs
  obtain ⟨o₁, ho₁, hr⟩ := fwd t s hI hs o' ho'
  exact ⟨o', ho', Beh.unique hdet ho₁ ho ▸ hr⟩

/-- Refinement in both directions: every target behaviour implements a source
behaviour and every source behaviour is implemented by a target behaviour
(`ImplementsExactly`). -/
def Exactly (mode : Mode) (tgt : Semantics S' R' T' F') (src : Semantics S R T F)
    (Init : S' → S → Prop) (ob : S' → S → Obs R' R T' T F' F) : Prop :=
  Refines mode tgt src Init ob ∧
    ∀ t s, Init t s → src.Safe s → ∀ o', src.Beh s o' →
      ∃ o, tgt.Beh t o ∧ Outcome.Rel mode (ob t s) o o'

theorem Exactly.refines {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
    {I : S' → S → Prop} {ob : S' → S → Obs R' R T' T F' F}
    (h : Exactly m tgt src I ob) : Refines m tgt src I ob := h.1

theorem Exactly.of_forward {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
    {I : S' → S → Prop} {ob : S' → S → Obs R' R T' T F' F}
    (hdet : tgt.Deterministic) (htot : ∀ t s, I t s → src.Safe s → ∃ o', src.Beh s o')
    (fwd : ∀ t s, I t s → src.Safe s → ∀ o', src.Beh s o' →
      ∃ o, tgt.Beh t o ∧ Outcome.Rel m (ob t s) o o') :
    Exactly m tgt src I ob :=
  ⟨Refines.of_forward hdet htot fwd, fwd⟩

/-! ### What refinement preserves -/

section Preservation

variable {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
  {I : S' → S → Prop} {ob : S' → S → Obs R' R T' T F' F} {t : S'} {s : S}

/-- A target return is matched by a source return with a related value. -/
theorem returned (h : Refines m tgt src I ob) (hI : I t s) (hs : src.Safe s) {a : R'}
    (ha : tgt.Beh t (.returned a)) : ∃ b, src.Beh s (.returned b) ∧ (ob t s).ret a b := by
  obtain ⟨o', ho', hr⟩ := h t s hI hs _ ha
  obtain ⟨b, rfl, hb⟩ := hr.returned_left
  exact ⟨b, ho', hb⟩

/-- Termination: for `failure ≤ divergeToTrap`, target divergence forces source
divergence. Contrapositively, a source that cannot diverge yields a target
that cannot diverge. -/
theorem diverges (hm : m.failure ≤ .divergeToTrap) (h : Refines m tgt src I ob) (hI : I t s)
    (hs : src.Safe s) (hd : tgt.Beh t .diverges) : src.Beh s .diverges := by
  obtain ⟨o', ho', hr⟩ := h t s hI hs _ hd
  rwa [hr.diverges_left hm] at ho'

/-- Trap-freedom: in the strict failure mode a target trap is matched by a
source trap with a related payload. -/
theorem trapped (hm : m.failure = .strict) (h : Refines m tgt src I ob) (hI : I t s)
    (hs : src.Safe s) {a : T'} (ha : tgt.Beh t (.trapped a)) :
    ∃ b, src.Beh s (.trapped b) ∧ (ob t s).trap a b := by
  obtain ⟨o', ho', hr⟩ := h t s hI hs _ ha
  obtain ⟨b, rfl, hb⟩ := hr.trapped_left hm
  exact ⟨b, ho', hb⟩

end Preservation

end Refines

/-- `P ⊑ Q` iff `Beh P ⊆ Beh Q` on safe states: strict refinement with
the identity initial relation and the identity observation is behaviour
inclusion. -/
theorem refines_id_iff {P Q : Semantics S R T F} :
    Refines Mode.strict P Q Eq (fun _ _ => Obs.id) ↔
      ∀ s, Q.Safe s → ∀ o, P.Beh s o → Q.Beh s o := by
  constructor
  · intro h s hs o ho
    obtain ⟨o', ho', hr⟩ := h s s rfl hs o ho
    rwa [Outcome.Rel.strict_id_iff.mp hr]
  · rintro h t s rfl hs o ho
    exact ⟨o, h t hs o ho, Outcome.Rel.strict_id_iff.mpr rfl⟩

/-! ## The compilation relation -/

/-- `tgt` implements `src` on calls: every target state representing a call
whose source entry state is safe has only behaviours that implement a
behaviour of that entry state. -/
def Implements (mode : Mode) (src : Semantics S R T F) (tgt : Semantics S' R' T' F')
    {Call : Type*} (entry : Call → S) (Represents : Call → S' → Prop)
    (ob : Call → S' → Obs R' R T' T F' F) : Prop :=
  ∀ c t, Represents c t → src.Safe (entry c) → ∀ o, tgt.Beh t o →
    ∃ o', src.Beh (entry c) o' ∧ Outcome.Rel mode (ob c t) o o'

namespace Implements

variable {Call : Type*} {m m' : Mode}

/-- Every admissible call has a representing target state. Without this an
`Implements` fact may hold because `Represents` is empty. -/
def Represented (Admissible : Call → Prop) (Represents : Call → S' → Prop) : Prop :=
  ∀ c, Admissible c → ∃ t, Represents c t

/-- No run from a represented target state gets stuck. Without this an
`Implements` fact may hold because the target gets stuck: a stuck run has no
behaviour, so it is never checked against the source. -/
def Live (tgt : Semantics S' R' T' F') (Represents : Call → S' → Prop) : Prop :=
  ∀ c t, Represents c t → tgt.ProgressFrom t

/-- The guard against the two ways an `Implements` fact can hold trivially:
an empty `Represents`, and a target that gets stuck. -/
structure Nonvacuous (tgt : Semantics S' R' T' F') (Admissible : Call → Prop)
    (Represents : Call → S' → Prop) : Prop where
  represented : Represented Admissible Represents
  live : Live tgt Represents

theorem Live.of_progress {tgt : Semantics S' R' T' F'} {Rep : Call → S' → Prop}
    (hp : tgt.Progress) : Live tgt Rep :=
  fun _ t _ => hp.progressFrom t

theorem Nonvacuous.of_progress {tgt : Semantics S' R' T' F'} {Adm : Call → Prop}
    {Rep : Call → S' → Prop} (hp : tgt.Progress) (h : Represented Adm Rep) :
    Nonvacuous tgt Adm Rep :=
  ⟨h, Live.of_progress hp⟩

theorem safe {src : Semantics S R T F} {tgt : Semantics S' R' T' F'} {entry : Call → S}
    {Rep : Call → S' → Prop} {ob : Call → S' → Obs R' R T' T F' F}
    (h : Implements m src tgt entry Rep ob) {c : Call} {t : S'} (hr : Rep c t)
    (hs : src.Safe (entry c)) : tgt.Safe t := fun hu => by
  obtain ⟨o', hb, hr⟩ := h c t hr hs _ hu
  rw [Outcome.Rel.undefined_left] at hr
  subst hr
  exact hs hb

/-- What a nonvacuous instance delivers: an admissible call with a safe entry
state has a represented target state, that state has a behaviour, and each of
its behaviours implements a behaviour of the entry state. -/
theorem exists_beh {src : Semantics S R T F} {tgt : Semantics S' R' T' F'} {entry : Call → S}
    {Adm : Call → Prop} {Rep : Call → S' → Prop} {ob : Call → S' → Obs R' R T' T F' F}
    (h : Implements m src tgt entry Rep ob) (hn : Nonvacuous tgt Adm Rep) {c : Call}
    (hc : Adm c) (hs : src.Safe (entry c)) :
    ∃ t, Rep c t ∧ (∃ o, tgt.Beh t o) ∧
      ∀ o, tgt.Beh t o → ∃ o', src.Beh (entry c) o' ∧ Outcome.Rel m (ob c t) o o' := by
  obtain ⟨t, ht⟩ := hn.represented c hc
  exact ⟨t, ht, Beh.exists_of_progressFrom (hn.live c t ht), h c t ht hs⟩

/-- Implementation in both directions (`ImplementsExactly`): in addition,
every behaviour of a safe entry state is implemented by a behaviour of each
state representing the call. -/
def Exactly (mode : Mode) (src : Semantics S R T F) (tgt : Semantics S' R' T' F')
    (entry : Call → S) (Represents : Call → S' → Prop)
    (ob : Call → S' → Obs R' R T' T F' F) : Prop :=
  Implements mode src tgt entry Represents ob ∧
    ∀ c t, Represents c t → src.Safe (entry c) → ∀ o', src.Beh (entry c) o' →
      ∃ o, tgt.Beh t o ∧ Outcome.Rel mode (ob c t) o o'

/-- A live target implementing a deterministic source implements it exactly:
the represented state has a behaviour, it implements some source behaviour,
and the source has only one. Target determinism is not needed. -/
theorem exactly_of_live {src : Semantics S R T F} {tgt : Semantics S' R' T' F'}
    {entry : Call → S} {Rep : Call → S' → Prop} {ob : Call → S' → Obs R' R T' T F' F}
    (h : Implements m src tgt entry Rep ob) (hlive : Live tgt Rep) (hdet : src.Deterministic) :
    Exactly m src tgt entry Rep ob := by
  refine ⟨h, fun c t hr hs o' ho' => ?_⟩
  obtain ⟨o, ho⟩ := Beh.exists_of_progressFrom (hlive c t hr)
  obtain ⟨o'', ho'', hrel⟩ := h c t hr hs o ho
  exact ⟨o, ho, Beh.unique hdet ho'' ho' ▸ hrel⟩

/-- Weakening: a larger mode, fewer represented states, a larger observation. -/
theorem mono {src : Semantics S R T F} {tgt : Semantics S' R' T' F'} {entry : Call → S}
    {Rep Rep' : Call → S' → Prop} {ob ob' : Call → S' → Obs R' R T' T F' F}
    (hm : m ≤ m') (hRep : ∀ c t, Rep' c t → Rep c t)
    (hob : ∀ c t, Rep' c t → ob c t ≤ ob' c t)
    (h : Implements m src tgt entry Rep ob) : Implements m' src tgt entry Rep' ob' := by
  intro c t hr hs o hb
  obtain ⟨o', hb', hrel⟩ := h c t (hRep c t hr) hs o hb
  exact ⟨o', hb', hrel.mono hm (hob c t hr)⟩

/-- A refinement whose initial relation contains every represented call is an
implementation. -/
theorem of_refines {src : Semantics S R T F} {tgt : Semantics S' R' T' F'} {entry : Call → S}
    {Rep : Call → S' → Prop} {I : S' → S → Prop} {ob : S' → S → Obs R' R T' T F' F}
    (h : Refines m tgt src I ob) (hRep : ∀ c t, Rep c t → I t (entry c)) :
    Implements m src tgt entry Rep (fun c t => ob t (entry c)) :=
  fun c t hr hs o hb => h t (entry c) (hRep c t hr) hs o hb

/-- The backward direction from a forward simulation and target determinism. -/
theorem of_forward {src : Semantics S R T F} {tgt : Semantics S' R' T' F'}
    {entry : Call → S} {Rep : Call → S' → Prop} {ob : Call → S' → Obs R' R T' T F' F}
    (hdet : tgt.Deterministic)
    (htot : ∀ c t, Rep c t → src.Safe (entry c) → ∃ o', src.Beh (entry c) o')
    (fwd : ∀ c t, Rep c t → src.Safe (entry c) → ∀ o', src.Beh (entry c) o' →
      ∃ o, tgt.Beh t o ∧ Outcome.Rel m (ob c t) o o') :
    Implements m src tgt entry Rep ob := by
  intro c t hr hs o ho
  obtain ⟨o', ho'⟩ := htot c t hr hs
  obtain ⟨o₁, ho₁, hrel⟩ := fwd c t hr hs o' ho'
  exact ⟨o', ho', Beh.unique hdet ho₁ ho ▸ hrel⟩

/-- Closure under target refinement: if `tgt'` refines `tgt` and `tgt`
implements `src`, then `tgt'` implements `src`, in the join of the modes. With
one half of an `Equiv`  for `he` this is `Implements ∘ Equiv ⊆
Implements`. Safety of the intermediate target state is derived from source
safety. Liveness of `tgt'` (`Implements.Live`) is not transferred: a stuck
`tgt'` refines `tgt`, so it is proved for `tgt'` separately. -/
theorem close {src : Semantics S R T F} {tgt : Semantics S' R' T' F'}
    {tgt' : Semantics S'' R'' T'' F''} {entry : Call → S}
    {Rep : Call → S' → Prop} {Rep' : Call → S'' → Prop} {I : S'' → S' → Prop}
    {ob : Call → S' → Obs R' R T' T F' F} {ob' : S'' → S' → Obs R'' R' T'' T' F'' F'}
    {ob'' : Call → S'' → Obs R'' R T'' T F'' F}
    (hi : Implements m src tgt entry Rep ob) (he : Refines m' tgt' tgt I ob')
    (hRep : ∀ c t', Rep' c t' → ∃ t, Rep c t ∧ I t' t)
    (hob : ∀ c t' t, Rep' c t' → Rep c t → I t' t → (ob' t' t).comp (ob c t) ≤ ob'' c t') :
    Implements (m ⊔ m') src tgt' entry Rep' ob'' := by
  intro c t' hr' hs o ho
  obtain ⟨t, hr, hI⟩ := hRep c t' hr'
  obtain ⟨p, hp, hop⟩ := he t' t hI (hi.safe hr hs) o ho
  obtain ⟨q, hq, hpq⟩ := hi c t hr hs p hp
  refine ⟨q, hq, ?_⟩
  rw [sup_comm]
  exact (hop.trans hpq).mono le_rfl (hob c t' t hr' hr hI)

/-- Composition with a source-side refinement: if `src` refines `src'` at the
entry states, an implementation of `src` implements `src'`. This is how a
compiler pass chain is extended at the source end (for instance down to a
reference semantics). -/
theorem trans_refines {src : Semantics S R T F} {src' : Semantics S'' R'' T'' F''}
    {tgt : Semantics S' R' T' F'} {entry : Call → S} {entry' : Call → S''}
    {Rep : Call → S' → Prop} {I : S → S'' → Prop}
    {ob : Call → S' → Obs R' R T' T F' F} {ob' : S → S'' → Obs R R'' T T'' F F''}
    {ob'' : Call → S' → Obs R' R'' T' T'' F' F''}
    (hi : Implements m src tgt entry Rep ob) (hs : Refines m' src src' I ob')
    (hentry : ∀ c, I (entry c) (entry' c))
    (hob : ∀ c t, Rep c t → (ob c t).comp (ob' (entry c) (entry' c)) ≤ ob'' c t) :
    Implements (m ⊔ m') src' tgt entry' Rep ob'' := by
  intro c t hr hsafe o ho
  have hsafe₀ : src.Safe (entry c) := hs.safe (hentry c) hsafe
  obtain ⟨p, hp, hop⟩ := hi c t hr hsafe₀ o ho
  obtain ⟨q, hq, hpq⟩ := hs (entry c) (entry' c) (hentry c) hsafe p hp
  exact ⟨q, hq, (hop.trans hpq).mono le_rfl (hob c t hr)⟩

end Implements

end Silmaril.Machine.Behaviour
