module

public import Silmaril.Logic.Consequence.Shape.Defs
public import Silmaril.Logic.Consequence.Accept.Thms
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Set.Finite.Basic

/-!
# Shapes of consequence systems: laws

**Acceptors and rejectors.** `acceptorEquiv_symm_eq_liftTTC`, `acceptorEquiv_symm_eq_liftCAll`:
over a single context, the `tt`-lift and the every-context lift are the same acceptor.
`rejectorEquiv_symm_eq_liftAxFF`, `rejectorEquiv_symm_eq_liftAxAll`: over a single conclusion,
the `ff`-lift and the everything-lift are the same rejector.

**Whole systems from slices.** Each of these needs exactly the stated condition, and nothing
about empty types:
* `eq_liftTTC_iff`: `S = liftTTC tt (ttSlice S tt) ↔ SupportedAx S tt`.
* `eq_liftAxFF_iff`: `S = liftAxFF (ffSlice S ff) ff ↔ SupportedC S ff`.
* `exists_liftCAll_iff`: `S` is some `liftCAll L` iff `ContextFree S`.
* `exists_liftAxAll_iff`: `S` is some `liftAxAll L` iff `ConclusionFree S`.

The language is unique for `liftAxAll` only when `C` is nonempty (`liftAxAll_injective`); with
`C` empty every `liftAxAll L` is the same system (`liftAxAll_empty_eq`). In general a slice does
not determine the system: `slice_counterexample` gives two systems with the same `tt`-slice.

**Checker predicates.**
* `SetInv.permInv`; `permInv_not_setInv` is a permutation-invariant predicate that is not
  set-invariant (`length = 1`).
* `UpClosed.setInv`; `upClosed_iff`: closure under weakening is set-invariance plus
  `AppendExtensive`.
* `appendClosed_not_appendExtensive`: `AppendClosed` (concatenation-closed) does not give it.
* `setInv_iff_finset`: set-invariance is exactly factoring through `List.toFinset`.
* `finExt_ofList`: the finitary extension agrees with `P` on member sets of lists;
  `not_finExt_of_infinite`: it is false on infinite sets.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v

variable {Ax : Type u} {C : Type v}

theorem acceptorEquiv_symm_eq_liftTTC (L : Set C) : acceptorEquiv.symm L = liftTTC () L :=
  funext₂ fun _ _ => propext ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

theorem acceptorEquiv_symm_eq_liftCAll (L : Set C) : acceptorEquiv.symm L = liftCAll L := rfl

theorem rejectorEquiv_symm_eq_liftAxFF (L : Set Ax) : rejectorEquiv.symm L = liftAxFF L () :=
  funext₂ fun _ _ => propext ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩

theorem rejectorEquiv_symm_eq_liftAxAll (L : Set Ax) : rejectorEquiv.symm L = liftAxAll L := rfl

theorem eq_liftTTC_iff (S : System Ax C) (tt : Ax) :
    S = liftTTC tt (ttSlice S tt) ↔ SupportedAx S tt :=
  ⟨fun h a c hs => (h ▸ hs : liftTTC tt _ a c).1, fun h => funext₂ fun a c =>
    propext ⟨fun hs => ⟨h a c hs, h a c hs ▸ hs⟩, fun ⟨e, hc⟩ => e ▸ hc⟩⟩

theorem eq_liftAxFF_iff (S : System Ax C) (ff : C) :
    S = liftAxFF (ffSlice S ff) ff ↔ SupportedC S ff :=
  ⟨fun h a c hs => (h ▸ hs : liftAxFF _ ff a c).2, fun h => funext₂ fun a c =>
    propext ⟨fun hs => ⟨h a c hs ▸ hs, h a c hs⟩, fun ⟨ha, e⟩ => e ▸ ha⟩⟩

theorem exists_liftCAll_iff (S : System Ax C) : (∃ L, S = liftCAll L) ↔ ContextFree S :=
  ⟨fun ⟨L, h⟩ a _ c hs => h ▸ (h ▸ hs : liftCAll L a c), fun h =>
    ⟨{c | ∃ a, S a c}, funext₂ fun a c => propext ⟨fun hs => ⟨a, hs⟩, fun ⟨a', hs⟩ => h a' a c hs⟩⟩⟩

theorem exists_liftAxAll_iff (S : System Ax C) : (∃ L, S = liftAxAll L) ↔ ConclusionFree S :=
  ⟨fun ⟨L, h⟩ a c _ hs => h ▸ (h ▸ hs : liftAxAll L a c), fun h =>
    ⟨{a | ∃ c, S a c}, funext₂ fun a c => propext ⟨fun hs => ⟨c, hs⟩, fun ⟨c', hs⟩ => h a c' c hs⟩⟩⟩

theorem liftAxAll_injective [Nonempty C] :
    Function.Injective (liftAxAll : Set Ax → System Ax C) := fun L L' h => Set.ext fun a => by
  simpa [liftAxAll] using congrFun₂ h a (Classical.arbitrary C)

theorem liftAxAll_empty_eq [IsEmpty C] (L L' : Set Ax) :
    (liftAxAll L : System Ax C) = liftAxAll L' := funext₂ fun _ c => isEmptyElim c

/-- Two systems with the same slice at `true`: everything from every context, and everything from
`true` only. -/
theorem slice_counterexample :
    ttSlice (liftCAll Set.univ : System Bool Unit) true = ttSlice (liftTTC true Set.univ) true ∧
      (liftCAll Set.univ : System Bool Unit) ≠ liftTTC true Set.univ :=
  ⟨Set.ext fun _ => by simp [ttSlice, liftCAll, liftTTC], fun h => by
    simpa [liftCAll, liftTTC] using congrFun₂ h false ()⟩

namespace ListPred

variable {P : List C → Prop}

theorem SetInv.permInv (h : SetInv P) : PermInv P := fun _ _ hp => h _ _ fun _ => hp.mem_iff

theorem permInv_not_setInv :
    PermInv (fun l : List Unit => l.length = 1) ∧ ¬ SetInv (fun l : List Unit => l.length = 1) :=
  ⟨fun _ _ hp => by simp only [hp.length_eq], fun h => by simpa using h [()] [(), ()] (by simp)⟩

theorem UpClosed.setInv (h : UpClosed P) : SetInv P := fun l l' hm =>
  ⟨h l l' fun x hx => (hm x).1 hx, h l' l fun x hx => (hm x).2 hx⟩

theorem upClosed_iff : UpClosed P ↔ SetInv P ∧ AppendExtensive P :=
  ⟨fun h => ⟨h.setInv, fun l l' hl => h l _ (List.subset_append_left l l') hl⟩,
   fun ⟨hs, ha⟩ l l' hsub hl => (hs (l ++ l') l' fun x => by
     simpa using fun hx => hsub hx).1 (ha l l' hl)⟩

theorem appendClosed_not_appendExtensive [Inhabited C] :
    AppendClosed (fun l : List C => l = []) ∧ ¬ AppendExtensive (fun l : List C => l = []) :=
  ⟨fun _ _ h h' => by simp [h, h'], fun h => by simpa using h [] [default] rfl⟩

theorem setInv_iff_finset [DecidableEq C] :
    SetInv P ↔ ∃ Q : Finset C → Prop, ∀ l, P l ↔ Q l.toFinset := by
  constructor
  · intro h
    refine ⟨fun s => ∃ l, l.toFinset = s ∧ P l, fun l => ⟨fun hl => ⟨l, rfl, hl⟩, ?_⟩⟩
    rintro ⟨l', he, hl'⟩
    exact (h l' l fun x => by simpa using congrArg (x ∈ ·) he).1 hl'
  · rintro ⟨Q, hQ⟩ l l' hm
    rw [hQ, hQ, show l.toFinset = l'.toFinset from Finset.ext fun x => by simpa using hm x]

theorem finExt_ofList (h : SetInv P) (l : List C) : finExt P {x | x ∈ l} ↔ P l :=
  ⟨fun ⟨l', hm, hl'⟩ => (h l' l hm).1 hl', fun hl => ⟨l, fun _ => Iff.rfl, hl⟩⟩

theorem not_finExt_of_infinite {s : Set C} (hs : s.Infinite) : ¬ finExt P s :=
  fun ⟨l, hm, _⟩ => hs (l.finite_toSet.subset fun x hx => (hm x).2 hx)

end ListPred

end Silmaril.Consequence
