module

public import Silmaril.Logic.Consequence.Accept.Defs
public import Silmaril.Logic.Consequence.Thms

/-!
# Acceptors as consequence systems: laws

**Least systems (Galois connections).** `liftAxFF_le_iff`: `liftAxFF L ff ≤ S` iff every
accepted context proves `ff` in `S`; `liftTTC_le_iff`, `liftAxAll_le_iff` (every accepted
context is inconsistent, `ProvesAll`), `liftCAll_le_iff`. Hence each lift is monotone in `L`
(`liftAxFF_mono`, …).

**Recovering the language.** `liftAxFF_ff`, `liftTTC_tt`, `liftCAll_apply`: the language is the
set of contexts proving `ff`, of conclusions following from `tt`, of conclusions following from
a (any) context. `provesAll_liftAxAll_iff` needs `Nonempty C`; `provesAll_liftAxAll_of_isEmpty`
shows why.

**Coordinates do not collapse.** `liftAxFF_not_explosive`: an accepted context proves `ff` but,
when some `c ≠ ff` exists, not `c`; so `liftAxFF` and `liftAxAll` differ, and
`ProvesFalse`/`ProvesAll` are distinct here.

**Checkers.** `liftAxFF_ofBool`, `liftCAll_ofBool`: for a Bool checker, the lift's judgements are
the checker's verdicts.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v

variable {Ax : Type u} {C : Type v} {S : System Ax C}

theorem liftAxFF_le_iff (L : Set Ax) (ff : C) : liftAxFF L ff ≤ S ↔ ∀ a ∈ L, S a ff :=
  ⟨fun h a ha => h a ff ⟨ha, rfl⟩, fun h a _ ⟨ha, e⟩ => e ▸ h a ha⟩

theorem liftTTC_le_iff (tt : Ax) (L : Set C) : liftTTC tt L ≤ S ↔ ∀ c ∈ L, S tt c :=
  ⟨fun h c hc => h tt c ⟨rfl, hc⟩, fun h _ c ⟨e, hc⟩ => e ▸ h c hc⟩

theorem liftAxAll_le_iff (L : Set Ax) : liftAxAll L ≤ S ↔ ∀ a ∈ L, S.ProvesAll a :=
  ⟨fun h a ha c => h a c ha, fun h a c ha => h a ha c⟩

theorem liftCAll_le_iff (L : Set C) : liftCAll L ≤ S ↔ ∀ a, ∀ c ∈ L, S a c :=
  ⟨fun h a c hc => h a c hc, fun h a c hc => h a c hc⟩

theorem liftAxFF_mono {L L' : Set Ax} (h : L ⊆ L') (ff : C) : liftAxFF L ff ≤ liftAxFF L' ff :=
  fun _ _ ⟨ha, e⟩ => ⟨h ha, e⟩
theorem liftTTC_mono (tt : Ax) {L L' : Set C} (h : L ⊆ L') : liftTTC tt L ≤ liftTTC tt L' :=
  fun _ _ ⟨e, hc⟩ => ⟨e, h hc⟩
theorem liftAxAll_mono {L L' : Set Ax} (h : L ⊆ L') : (liftAxAll L : System Ax C) ≤ liftAxAll L' :=
  fun _ _ ha => h ha
theorem liftCAll_mono {L L' : Set C} (h : L ⊆ L') : (liftCAll L : System Ax C) ≤ liftCAll L' :=
  fun _ _ hc => h hc

@[simp] theorem liftAxFF_ff (L : Set Ax) (ff : C) (a : Ax) : liftAxFF L ff a ff ↔ a ∈ L :=
  ⟨And.left, fun h => ⟨h, rfl⟩⟩

@[simp] theorem liftTTC_tt (tt : Ax) (L : Set C) (c : C) : liftTTC tt L tt c ↔ c ∈ L :=
  ⟨And.right, fun h => ⟨rfl, h⟩⟩

@[simp] theorem liftCAll_apply (L : Set C) (a : Ax) (c : C) : liftCAll L a c ↔ c ∈ L := Iff.rfl

theorem provesAll_liftAxAll_iff [Nonempty C] (L : Set Ax) (a : Ax) :
    (liftAxAll L : System Ax C).ProvesAll a ↔ a ∈ L :=
  ⟨fun h => h (Classical.arbitrary C), fun h _ => h⟩

/-- With no conclusions, `liftAxAll L` cannot see `L`: every context proves everything. -/
theorem provesAll_liftAxAll_of_isEmpty [IsEmpty C] (L : Set Ax) (a : Ax) :
    (liftAxAll L : System Ax C).ProvesAll a := System.provesAll_of_isEmpty a

theorem liftAxFF_not_explosive {L : Set Ax} {ff c : C} (hc : c ≠ ff) {a : Ax} :
    ¬ (liftAxFF L ff).ProvesAll a := fun h => hc (h c).2

theorem liftAxFF_ofBool (check : Ax → Bool) (ff : C) (a : Ax) :
    liftAxFF (Accept.ofBool check) ff a ff ↔ check a = true := liftAxFF_ff _ _ a

theorem liftCAll_ofBool (check : C → Bool) (a : Ax) (c : C) :
    (liftCAll (Accept.ofBool check) : System Ax C) a c ↔ check c = true := Iff.rfl

end Silmaril.Consequence
