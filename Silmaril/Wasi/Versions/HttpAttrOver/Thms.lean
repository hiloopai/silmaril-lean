module

public import Silmaril.Wasi.Versions.HttpAttrOver.Defs
public import Silmaril.Wasi.Versions.HttpAttr.Thms

@[expose] public section

/-!
# HTTP attributes across versions: theorems

PROVED (standard axioms):

* `fwdAttr_model`: for every sound table, over every host of the imported attribute theory,
  the forwarding composite is a model of the exported one. Invariant: the two theory states
  are equal.
* **`attr2Over3_model`**, **`attr3Over2_model`**: the two instances.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- `errTo` keeps `ok`-ness. -/
theorem isOkAns_errTo (e : Option Val) (r : Option (List Val)) : isOkAns (errTo e r) = isOkAns r := by
  unfold errTo; split <;> simp_all [isOkAns]

/-- The answer translation does not change the step of the exported operation. -/
theorem trA_step (e : Option Val) {o : AOp} (q : AttrSt) (a : List Val) (r : Option (List Val)) :
    aOk o q a (trA e (some o) r) = aOk o q a r ∧ aNext o q a (trA e (some o) r) = aNext o q a r := by
  cases o with
  | set k =>
    by_cases hk : k ∈ optKeys
    · simp only [trA, hk, ↓reduceIte]
      refine ⟨?_, by simp only [aNext, isOkAns_errTo]⟩
      rcases a with _ | ⟨v, a'⟩
      · rfl
      · cases v <;> simp only [aOk, isOkAns_errTo]
    · simp [trA, hk]
  | _ => exact ⟨rfl, rfl⟩

/-- **The invariant of a forwarding adapter**: the two theory states are equal. -/
theorem fwdAttr_inv {N N' : AttrFns} {P : List (FnName × FnName)} (e : Option Val)
    (hP : TabOk N N' P) :
    WpInv (fwdAttr N N' P e hP) () (attrTh N') (attrTh N) (fun _ q' q => q = q') where
  init := rfl
  call := by
    intro _ q' q c hJ r q'' hs
    obtain ⟨hs1, hs2⟩ := tabOk_find hP c.1.2
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hs1
    refine ⟨q'', ?_, rfl⟩
    have hs' := hs
    rw [attrTh_step N' (hs2.trans ho)] at hs'
    show (attrTh N).step q (.imp c.1.1 c.2 (trA e (N.op c.1.1) r)) = some q''
    rw [attrTh_step N ho, ho, (trA_step e q c.2 r).1, (trA_step e q c.2 r).2, hJ]
    exact hs'

/-- **A forwarding adapter of a sound table**: over every host of `attrTh N'`, the composite is
a model of `attrTh N`. -/
theorem fwdAttr_model {N N' : AttrFns} {P : List (FnName × FnName)} (e : Option Val)
    (hP : TabOk N N' P) {Y : Sig.{0}} {η : Host Y N'.fns}
    (hη : (hostSat (attrTh N').Accepts).holds η) :
    (hostSat (attrTh N).Accepts).holds (link η (ofSBody (fwdAttr N N' P e hP) ())) :=
  link_model (ag_of_wpInv (fwdAttr_inv e hP)) hη

/-- **Attributes, 0.2 over 0.3**: over every host of the 0.3 attribute theory, the composite is
a model of the 0.2 one. -/
theorem attr2Over3_model {Y : Sig.{0}} {η : Host Y attrFns3.fns}
    (hη : (hostSat (attrTh attrFns3).Accepts).holds η) :
    (hostSat (attrTh attrFns2).Accepts).holds (link η (ofSBody attr2Over3 ())) :=
  fwdAttr_model _ tab23_ok hη

/-- **Attributes, 0.3 over 0.2**: over every host of the 0.2 attribute theory, the composite is
a model of the 0.3 one. -/
theorem attr3Over2_model {Y : Sig.{0}} {η : Host Y attrFns2.fns}
    (hη : (hostSat (attrTh attrFns2).Accepts).holds η) :
    (hostSat (attrTh attrFns3).Accepts).holds (link η (ofSBody attr3Over2 ())) :=
  fwdAttr_model _ tab32_ok hη

end Silmaril.Wasi.Versions.Net
