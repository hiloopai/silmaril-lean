module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Defs

/-!
# Round 7, the whole-evaluator erasure: the syntactic check is monotone (unrefined)

`xExp_mono` (and its siblings): enlarging the sets `gr`, `gd` of allowed relations and
definitions keeps every expression, path, argument and premise checked. One case per constructor,
by structural recursion along `xExp`'s own definition.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

theorem bt_and {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by simpa using h

theorem bt_mk {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by simp [ha, hb]

section
variable {gr gd gr' gd' : String → Bool} (hr : ∀ x, gr x = true → gr' x = true)
  (hd : ∀ x, gd x = true → gd' x = true)
include hr hd

mutual
theorem xExp_mono : ∀ e : Exp, xExp gr gd e = true → xExp gr' gd' e = true
  | .varE _, _ => rfl
  | .boolE _, _ => rfl
  | .numE _, _ => rfl
  | .textE _, _ => rfl
  | .unE _ _ e, h => xExp_mono e h
  | .binE _ _ e₁ e₂, h => bt_mk (xExp_mono e₁ (bt_and h).1) (xExp_mono e₂ (bt_and h).2)
  | .cmpE _ _ e₁ e₂, h => bt_mk (xExp_mono e₁ (bt_and h).1) (xExp_mono e₂ (bt_and h).2)
  | .tupE es, h => xExps_mono es h
  | .projE e _, h => xExp_mono e h
  | .caseE _ e, h => xExp_mono e h
  | .uncaseE e _, h => xExp_mono e h
  | .optE eo, h => xOExp_mono eo h
  | .theE e, h => xExp_mono e h
  | .strE fs, h => xFields_mono fs h
  | .dotE e _, h => bt_mk (bt_and h).1 (xExp_mono e (bt_and h).2)
  | .compE e₁ e₂, h =>
    bt_mk (bt_mk (bt_and (bt_and h).1).1 (xExp_mono e₁ (bt_and (bt_and h).1).2))
      (xExp_mono e₂ (bt_and h).2)
  | .listE es, h => xExps_mono es h
  | .liftE e, h => xExp_mono e h
  | .memE e₁ e₂, h => bt_mk (xExp_mono e₁ (bt_and h).1) (xExp_mono e₂ (bt_and h).2)
  | .lenE e, h => xExp_mono e h
  | .catE e₁ e₂, h => bt_mk (xExp_mono e₁ (bt_and h).1) (xExp_mono e₂ (bt_and h).2)
  | .idxE e₁ e₂, h => bt_mk (xExp_mono e₁ (bt_and h).1) (xExp_mono e₂ (bt_and h).2)
  | .sliceE e₁ e₂ e₃, h =>
    bt_mk (bt_mk (xExp_mono e₁ (bt_and (bt_and h).1).1) (xExp_mono e₂ (bt_and (bt_and h).1).2))
      (xExp_mono e₃ (bt_and h).2)
  | .updE e₁ p e₂, h =>
    bt_mk (bt_mk (bt_mk (bt_and (bt_and (bt_and h).1).1).1
        (xExp_mono e₁ (bt_and (bt_and (bt_and h).1).1).2)) (xPath_mono p (bt_and (bt_and h).1).2))
      (xExp_mono e₂ (bt_and h).2)
  | .extE e₁ p e₂, h =>
    bt_mk (bt_mk (bt_mk (bt_and (bt_and (bt_and h).1).1).1
        (xExp_mono e₁ (bt_and (bt_and (bt_and h).1).1).2)) (xPath_mono p (bt_and (bt_and h).1).2))
      (xExp_mono e₂ (bt_and h).2)
  | .callE x args, h => bt_mk (hd x (bt_and h).1) (xArgs_mono args (bt_and h).2)
  | .iterE e (.mk it ds), h =>
    bt_mk (bt_mk (xExp_mono e (bt_and (bt_and h).1).1) (xIter_mono it (bt_and (bt_and h).1).2))
      (xDoms_mono ds (bt_and h).2)
  | .cvtE e _ _, h => xExp_mono e h
  | .subE e _ _, h => xExp_mono e h

theorem xExps_mono : ∀ es : List Exp, xExps gr gd es = true → xExps gr' gd' es = true
  | [], _ => rfl
  | e :: es, h => bt_mk (xExp_mono e (bt_and h).1) (xExps_mono es (bt_and h).2)

theorem xOExp_mono : ∀ eo : Option Exp, xOExp gr gd eo = true → xOExp gr' gd' eo = true
  | none, _ => rfl
  | some e, h => xExp_mono e h

theorem xFields_mono : ∀ fs : List ExpField, xFields gr gd fs = true → xFields gr' gd' fs = true
  | [], _ => rfl
  | .mk _ e :: fs, h =>
    bt_mk (bt_mk (bt_and (bt_and h).1).1 (xExp_mono e (bt_and (bt_and h).1).2))
      (xFields_mono fs (bt_and h).2)

theorem xPath_mono : ∀ p : Path, xPath gr gd p = true → xPath gr' gd' p = true
  | .rootP, _ => rfl
  | .idxP p e, h => bt_mk (xPath_mono p (bt_and h).1) (xExp_mono e (bt_and h).2)
  | .sliceP p e₁ e₂, h =>
    bt_mk (bt_mk (xPath_mono p (bt_and (bt_and h).1).1) (xExp_mono e₁ (bt_and (bt_and h).1).2))
      (xExp_mono e₂ (bt_and h).2)
  | .dotP p _, h => bt_mk (bt_and h).1 (xPath_mono p (bt_and h).2)

theorem xIter_mono : ∀ it : Iter, xIter gr gd it = true → xIter gr' gd' it = true
  | .listN e _, h => xExp_mono e h
  | .opt, _ => rfl
  | .list, _ => rfl
  | .list1, _ => rfl

theorem xDoms_mono : ∀ ds : List Dom, xDoms gr gd ds = true → xDoms gr' gd' ds = true
  | [], _ => rfl
  | .mk _ e :: ds, h => bt_mk (xExp_mono e (bt_and h).1) (xDoms_mono ds (bt_and h).2)

theorem xArg_mono : ∀ a : Arg, xArg gr gd a = true → xArg gr' gd' a = true
  | .expA e, h => xExp_mono e h
  | .typA _, _ => rfl
  | .defA x, h => hd x h
  | .gramA _, _ => rfl

theorem xArgs_mono : ∀ l : List Arg, xArgs gr gd l = true → xArgs gr' gd' l = true
  | [], _ => rfl
  | a :: l, h => bt_mk (xArg_mono a (bt_and h).1) (xArgs_mono l (bt_and h).2)

theorem xPrem_mono : ∀ pr : Prem, xPrem gr gd pr = true → xPrem gr' gd' pr = true
  | .rulePr x args _ e, h =>
    bt_mk (bt_mk (hr x (bt_and (bt_and h).1).1) (xArgs_mono args (bt_and (bt_and h).1).2))
      (xExp_mono e (bt_and h).2)
  | .ifPr e, h => xExp_mono e h
  | .letPr e₁ e₂, h => bt_mk (xExp_mono e₁ (bt_and h).1) (xExp_mono e₂ (bt_and h).2)
  | .elsePr, _ => rfl
  | .iterPr pr (.mk it ds), h =>
    bt_mk (bt_mk (xPrem_mono pr (bt_and (bt_and h).1).1) (xIter_mono it (bt_and (bt_and h).1).2))
      (xDoms_mono ds (bt_and h).2)

theorem xPrems_mono : ∀ prs : List Prem, xPrems gr gd prs = true → xPrems gr' gd' prs = true
  | [], _ => rfl
  | pr :: prs, h => bt_mk (xPrem_mono pr (bt_and h).1) (xPrems_mono prs (bt_and h).2)
end

theorem xClause_mono (c : Clause) (h : xClause gr gd c = true) : xClause gr' gd' c = true := by
  obtain ⟨_, args, e, prems⟩ := c
  simp only [xClause, Bool.and_eq_true] at h ⊢
  exact ⟨⟨xArgs_mono hr hd args h.1.1, xExp_mono hr hd e h.1.2⟩, xPrems_mono hr hd prems h.2⟩

theorem xRule_mono (r : Rule) (h : xRule gr gd r = true) : xRule gr' gd' r = true := by
  obtain ⟨_, _, _, e, prems⟩ := r
  simp only [xRule, Bool.and_eq_true] at h ⊢
  exact ⟨xExp_mono hr hd e h.1, xPrems_mono hr hd prems h.2⟩
end

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
