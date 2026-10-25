module

public import Silmaril.Compile.Category.Pass
public import Silmaril.Compile.PassAPI.Checked

@[expose] public section

/-!
# Behavioural endo-passes and invariant contracts

`EndoPass L` is exactly the shared pass API with the contract `L.Refines` and
the invariant `True`. `EndoPass.passAPIEquiv` records this as a monoid
equivalence, preserving the executable function and left-to-right sequencing.

A shared contract can instead require an invariant or express a relation other
than behavioural refinement. `EndoPass.ofInvariantPass` handles that case only
when the client proves that its relation implies refinement in an existing
language. The resulting language restricts programs to the invariant and keeps
the original interfaces and observable behaviours. No semantic interpretation
is supplied by the adapter itself.
-/

namespace Silmaril.Compile.Category

universe u

namespace Language

/-- The all-input behavioural-refinement contract of a language. -/
def refinementContract (L : Language.{u}) : PassAPI.Contract L.Prog where
  Rel := L.Refines
  refl := L.refines_refl
  trans := L.refines_trans
  Inv := fun _ => True

@[simp] theorem refinementContract_rel (L : Language.{u}) (p q : L.Prog) :
    L.refinementContract.Rel p q ↔ L.Refines p q := Iff.rfl

@[simp] theorem refinementContract_inv (L : Language.{u}) (p : L.Prog) :
    L.refinementContract.Inv p := trivial

/-- Restrict the programs of a language, retaining their actual interfaces and
observable behaviours. The invariant need not be decidable. -/
def onInvariant (L : Language.{u}) (Inv : L.Prog → Prop) : Language.{u} where
  Iface := L.Iface
  Prog := {p : L.Prog // Inv p}
  iface p := L.iface p.val
  Obs := L.Obs
  beh p := L.beh p.val

@[simp] theorem onInvariant_iface (L : Language.{u}) (Inv : L.Prog → Prop)
    (p : (L.onInvariant Inv).Prog) :
    (L.onInvariant Inv).iface p = L.iface p.val := rfl

@[simp] theorem onInvariant_beh (L : Language.{u}) (Inv : L.Prog → Prop)
    (p : (L.onInvariant Inv).Prog) :
    (L.onInvariant Inv).beh p = L.beh p.val := rfl

@[simp] theorem onInvariant_refines_iff (L : Language.{u}) (Inv : L.Prog → Prop)
    (p q : (L.onInvariant Inv).Prog) :
    (L.onInvariant Inv).Refines p q ↔ L.Refines p.val q.val := Iff.rfl

@[simp] theorem onInvariant_sat_iff (L : Language.{u}) (Inv : L.Prog → Prop)
    (p : (L.onInvariant Inv).Prog) (specification : Set L.Obs) :
    (L.onInvariant Inv).Sat p specification ↔ L.Sat p.val specification := Iff.rfl

end Language

namespace EndoPass

variable {L : Language.{u}}

/-- An all-input behavioural optimization as a shared contract pass. -/
def toPassAPI (E : EndoPass L) : PassAPI.Pass L.refinementContract where
  run := E.run
  inv_run _ := trivial
  sound {p} _ := E.refines p

/-- A shared pass for the all-input behavioural-refinement contract. -/
def ofPassAPI (P : PassAPI.Pass L.refinementContract) : EndoPass L where
  run := P.run
  refines _ := P.sound trivial

@[simp] theorem toPassAPI_run (E : EndoPass L) : E.toPassAPI.run = E.run := rfl

@[simp] theorem ofPassAPI_run (P : PassAPI.Pass L.refinementContract) :
    (ofPassAPI P).run = P.run := rfl

/-- The two endo-pass APIs agree exactly for the all-input behavioural-refinement
contract. Both monoids sequence their left factor before their right factor. -/
def passAPIEquiv (L : Language.{u}) :
    EndoPass L ≃* PassAPI.Pass L.refinementContract where
  toFun := toPassAPI
  invFun := ofPassAPI
  left_inv E := by apply EndoPass.ext; rfl
  right_inv P := by apply PassAPI.Pass.ext; rfl
  map_mul' _ _ := by apply PassAPI.Pass.ext; rfl

@[simp] theorem passAPIEquiv_run (E : EndoPass L) :
    (passAPIEquiv L E).run = E.run := rfl

@[simp] theorem passAPIEquiv_symm_run (P : PassAPI.Pass L.refinementContract) :
    ((passAPIEquiv L).symm P).run = P.run := rfl

@[simp] theorem passAPIEquiv_one :
    passAPIEquiv L (1 : EndoPass L) = 1 := by apply PassAPI.Pass.ext; rfl

@[simp] theorem passAPIEquiv_seq (E F : EndoPass L) :
    passAPIEquiv L (E.seq F) = (passAPIEquiv L E).seq (passAPIEquiv L F) := by
  apply PassAPI.Pass.ext
  rfl

/-- Pipeline translation preserves the complete executable sequence. -/
theorem passAPIEquiv_pipeline (Es : List (EndoPass L)) :
    passAPIEquiv L (pipeline Es) =
      PassAPI.Pass.pipeline (Es.map (passAPIEquiv L)) := by
  induction Es with
  | nil => rfl
  | cons E Es ih =>
    change passAPIEquiv L (E * pipeline Es) =
      passAPIEquiv L E * PassAPI.Pass.pipeline (Es.map (passAPIEquiv L))
    rw [map_mul, ih]

/-- The checker of a behavioural endo-pass as a shared checked contract. -/
def checkedPassAPI (f : L.Prog → L.Prog) (check : L.Prog → L.Prog → Bool)
    (hcheck : ∀ p q, check p q = true → L.Refines p q) :
    PassAPI.CheckedPass L.refinementContract where
  transform := f
  check := check
  check_sound {p q} h _ := ⟨hcheck p q h, trivial⟩

/-- Checked transformations retain the same identity fallback in both APIs. -/
theorem passAPIEquiv_checked (f : L.Prog → L.Prog) (check : L.Prog → L.Prog → Bool)
    (hcheck : ∀ p q, check p q = true → L.Refines p q) :
    passAPIEquiv L (checked f check hcheck) = (checkedPassAPI f check hcheck).checked := by
  apply PassAPI.Pass.ext
  rfl

variable {C : PassAPI.Contract L.Prog}

/-- Restrict a shared pass to invariant-satisfying programs of an existing
language. The client must prove both interface preservation and behavioural
refinement, as expressed by `L.Refines`. Invariant preservation comes from `P`.

In particular, the adapter does not assume that an arbitrary contract relation
already means behavioural refinement. -/
def ofInvariantPass (P : PassAPI.Pass C)
    (hrefines : ∀ {p q}, C.Inv p → C.Rel p q → L.Refines p q) :
    EndoPass (L.onInvariant C.Inv) where
  run p := ⟨P.run p.val, P.inv_run p.property⟩
  refines p := hrefines p.property (P.sound p.property)

@[simp] theorem ofInvariantPass_run_val (P : PassAPI.Pass C)
    (hrefines : ∀ {p q}, C.Inv p → C.Rel p q → L.Refines p q)
    (p : (L.onInvariant C.Inv).Prog) :
    ((ofInvariantPass P hrefines).run p).val = P.run p.val := rfl

/-- Restricting invariant passes respects identity and sequencing. -/
def invariantPassHom (L : Language.{u}) (C : PassAPI.Contract L.Prog)
    (hrefines : ∀ {p q}, C.Inv p → C.Rel p q → L.Refines p q) :
    PassAPI.Pass C →* EndoPass (L.onInvariant C.Inv) where
  toFun P := ofInvariantPass P hrefines
  map_one' := by
    apply EndoPass.ext
    funext p
    apply Subtype.ext
    rfl
  map_mul' P Q := by
    apply EndoPass.ext
    funext p
    apply Subtype.ext
    rfl

/-- Restriction preserves a whole invariant-preserving pipeline. -/
theorem ofInvariantPass_pipeline (Ps : List (PassAPI.Pass C))
    (hrefines : ∀ {p q}, C.Inv p → C.Rel p q → L.Refines p q) :
    ofInvariantPass (PassAPI.Pass.pipeline Ps) hrefines =
      pipeline (Ps.map fun P => ofInvariantPass P hrefines) := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
    change ofInvariantPass (P * PassAPI.Pass.pipeline Ps) hrefines =
      ofInvariantPass P hrefines * pipeline (Ps.map fun Q => ofInvariantPass Q hrefines)
    rw [← ih]
    apply EndoPass.ext
    funext p
    apply Subtype.ext
    rfl

end EndoPass

end Silmaril.Compile.Category
