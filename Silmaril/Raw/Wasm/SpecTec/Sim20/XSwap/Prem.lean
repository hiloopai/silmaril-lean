module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.TypFwd

/-!
# premises across the re-encoding (unrefined)

Round 8's `Raw/…/Round8/FiresC/Prem.lean` for `swapX` in `utf8Env20T B`. `premW_erase`: a premise
that holds under `ρ` (read by `Sim.PremW`) holds under `eraseScope ρ`, given that its relation
premises move (`D` to `D'` at re-encoded arguments, for `gr20` relations) and its `otherwise`
premise does (`els → els'`). `if` and `let` premises and the domains of iterations move by the
evaluator-level re-encoding (`EraseAll.eraseAt`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll (Hyps SG ER ArgIn gr20 gd20 xExp xPrem xPrems
  xArgs xIter xDoms eraseAt eraseP)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T)
open Silmaril.Wasm.SpecTec.Sim (PremW Interp domSomes domLists EvalDoms)

variable {B : Builtins} (H : Hyps QT gr20 gd20 (utf8Env20T B))
include H

theorem evalExp_erase {ρ : VarEnv} {e : Exp} {v : Value} (hρ : SG QT gd20 ρ)
    (hx : xExp gr20 gd20 e = true) (h : EvalExp (utf8Env20T B) ρ e v) :
    EvalExp (utf8Env20T B) (eraseScope ρ) e (swapX v) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, EraseAll.ER.eq_ok ((eraseAt H n).exp ρ e hρ hx) hn⟩

theorem evalArgs_erase {ρ : VarEnv} {l : List Arg} {ws : List ArgV} (hρ : SG QT gd20 ρ)
    (hx : xArgs gr20 gd20 l = true) (h : EvalArgs (utf8Env20T B) ρ l ws) :
    EvalArgs (utf8Env20T B) (eraseScope ρ) l (ws.map eraseA) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, EraseAll.ER.eq_ok ((eraseAt H n).args ρ l hρ hx) hn⟩

theorem evalDoms_erase {ρ : VarEnv} {ds : List Dom} {xvs : List (IL.Id × Value)}
    (hρ : SG QT gd20 ρ) (hx : xDoms gr20 gd20 ds = true) (h : EvalDoms (utf8Env20T B) ρ ds xvs) :
    EvalDoms (utf8Env20T B) (eraseScope ρ) ds (xvs.map eraseP) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, EraseAll.ER.eq_ok ((eraseAt H n).doms ρ ds hρ hx) hn⟩

omit H in
theorem mapM_map_comm {α β γ δ : Type} (f : α → Option β) (g : γ → Option δ) (φ : α → γ)
    (ψ : β → δ) (hfg : ∀ a, g (φ a) = (f a).map ψ) :
    ∀ xs : List α, (xs.map φ).mapM g = (xs.mapM f).map (List.map ψ)
  | [] => rfl
  | a :: xs => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, hfg a, mapM_map_comm f g φ ψ hfg xs]
    cases f a <;> cases xs.mapM f <;> rfl

omit H in
theorem domSomes_erase (xvs : List (IL.Id × Value)) :
    domSomes (xvs.map eraseP) = (domSomes xvs).map (List.map eraseP) := by
  unfold domSomes
  refine mapM_map_comm _ _ _ _ (fun p => ?_) xvs
  obtain ⟨x, v⟩ := p
  rcases v with _ | _ | _ | _ | _ | _ | _ | (_ | w) <;> rfl

omit H in
theorem domLists_erase (xvs : List (IL.Id × Value)) :
    domLists (xvs.map eraseP) =
      (domLists xvs).map (List.map fun p => (p.1, p.2.map swapX)) :=
  EraseAll.mapM_asList_erase xvs

omit H in
theorem mem_map_eraseP_rows {rows : List (List (IL.Id × Value))} {r : List (IL.Id × Value)}
    (h : r ∈ rows.map (List.map eraseP)) : ∃ r₀ ∈ rows, r = r₀.map eraseP := by
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 h
  exact ⟨r₀, hr₀, rfl⟩

omit H in
theorem sg_bindVals {ρ : VarEnv} (hρ : SG QT gd20 ρ) (xs : List (IL.Id × Value)) :
    SG QT gd20 (ρ.bindVals xs) :=
  hρ.bindVals fun p _ => EraseAll.allIn_true p.2

/-- **A premise moves across erasure.** -/
theorem premW_erase {D D' : Interp} {els' : Prop} :
    ∀ {els : Prop} {ρ : VarEnv} {pr : Prem}, PremW (utf8Env20T B) D els ρ pr → SG QT gd20 ρ →
      xPrem gr20 gd20 pr = true →
      (∀ x op avs w, gr20 x = true → D x op avs w → D' x op (avs.map eraseA) (swapX w)) →
      (els → els') →
      PremW (utf8Env20T B) D' els' (eraseScope ρ) pr := by
  intro els ρ pr h
  induction h with
  | ifPr he =>
    intro hρ hx _ _
    exact .ifPr (by simpa using evalExp_erase H hρ (by simpa [xPrem] using hx) he)
  | elsePr hels =>
    intro _ _ _ hE
    exact .elsePr (hE hels)
  | letPr he₂ he₁ =>
    intro hρ hx _ _
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .letPr (evalExp_erase H hρ hx.2 he₂) (evalExp_erase H hρ hx.1 he₁)
  | @rulePr ρ x args op e avs w hargs he hD =>
    intro hρ hx hR _
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .rulePr (evalArgs_erase H hρ hx.1.2 hargs) (evalExp_erase H hρ hx.2 he)
      (hR x op avs w hx.1.1 hD)
  | iterOptNone hdoms hne hall =>
    intro hρ hx _ _
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterOptNone (evalDoms_erase H hρ hx.2 hdoms) hne ?_
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    simp [eraseP, hall q hq]
  | @iterOptSome ρ pr ds xvs row hdoms hne hsome hpr ih =>
    intro hρ hx hR hE
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterOptSome (row := row.map eraseP) (evalDoms_erase H hρ hx.2 hdoms) hne
      (by rw [domSomes_erase, hsome]; rfl) ?_
    rw [← EraseAll.eraseScope_bindVals]
    exact ih (sg_bindVals hρ row) hx.1.1 (fun x op avs w hx' => hR x op avs w hx')
      (fun he => hE he)
  | @iterList ρ pr it ds xvs dls k hit hdoms hne hdl hlen hrows ih =>
    intro hρ hx hR hE
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterList (dls := dls.map fun p => (p.1, p.2.map swapX)) (k := k) hit
      (evalDoms_erase H hρ hx.2 hdoms) hne (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ (sg_bindVals hρ r₀) hx.1.1 (fun x op avs w hx' => hR x op avs w hx')
        (fun he => hE he)
  | @iterListN ρ pr eₙ ido ds xvs dls kv k hdoms hn hk hdl hlen hrows ih =>
    intro hρ hx hR hE
    simp only [xPrem, Bool.and_eq_true] at hx
    have hxn : xExp gr20 gd20 eₙ = true := by simpa [xIter] using hx.1.2
    refine .iterListN (dls := dls.map fun p => (p.1, p.2.map swapX)) (kv := swapX kv) (k := k)
      (evalDoms_erase H hρ hx.2 hdoms) (evalExp_erase H hρ hxn hn) (by rw [asNat?_eraseC]; exact hk)
      (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ (sg_bindVals hρ r₀) hx.1.1 (fun x op avs w hx' => hR x op avs w hx')
        (fun he => hE he)

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ
