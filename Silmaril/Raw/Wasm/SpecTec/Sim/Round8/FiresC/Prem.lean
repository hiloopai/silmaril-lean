module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.FiresC.TypFwd

/-!
# Round 8, firing across code erasure: premises (unrefined)

`premW_erase`: a premise that holds under `ρ` (read by `Sim.PremW`) holds under `eraseScope ρ`,
given that its relation premises move (`D` to `D'` at erased arguments) and its `otherwise`
premise does (`els → els'`). `if` and `let` premises and the domains of iterations move by round
8's evaluator-level erasure (`CodeErase.EraseAll.eraseAt`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps SG ER ArgIn grC gdC xExp xPrem xPrems
  xArgs xIter xDoms eraseAt eraseP)

variable {B : Builtins} (H : Hyps QT grC gdC (simEnv B))
include H

theorem evalExp_erase {ρ : VarEnv} {e : Exp} {v : Value} (hρ : SG QT gdC ρ)
    (hx : xExp grC gdC e = true) (h : EvalExp (simEnv B) ρ e v) :
    EvalExp (simEnv B) (eraseScope ρ) e (eraseC v) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, CodeErase.EraseAll.ER.eq_ok ((eraseAt H n).exp ρ e hρ hx) hn⟩

theorem evalArgs_erase {ρ : VarEnv} {l : List Arg} {ws : List ArgV} (hρ : SG QT gdC ρ)
    (hx : xArgs grC gdC l = true) (h : EvalArgs (simEnv B) ρ l ws) :
    EvalArgs (simEnv B) (eraseScope ρ) l (ws.map eraseA) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, CodeErase.EraseAll.ER.eq_ok ((eraseAt H n).args ρ l hρ hx) hn⟩

theorem evalDoms_erase {ρ : VarEnv} {ds : List Dom} {xvs : List (IL.Id × Value)}
    (hρ : SG QT gdC ρ) (hx : xDoms grC gdC ds = true) (h : EvalDoms (simEnv B) ρ ds xvs) :
    EvalDoms (simEnv B) (eraseScope ρ) ds (xvs.map eraseP) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, CodeErase.EraseAll.ER.eq_ok ((eraseAt H n).doms ρ ds hρ hx) hn⟩

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
      (domLists xvs).map (List.map fun p => (p.1, p.2.map eraseC)) :=
  CodeErase.EraseAll.mapM_asList_erase xvs

omit H in
theorem mem_map_eraseP_rows {rows : List (List (IL.Id × Value))} {r : List (IL.Id × Value)}
    (h : r ∈ rows.map (List.map eraseP)) : ∃ r₀ ∈ rows, r = r₀.map eraseP := by
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 h
  exact ⟨r₀, hr₀, rfl⟩

omit H in
theorem sg_bindVals {ρ : VarEnv} (hρ : SG QT gdC ρ) (xs : List (IL.Id × Value)) :
    SG QT gdC (ρ.bindVals xs) :=
  hρ.bindVals fun p _ => CodeErase.EraseAll.allIn_true p.2

/-- **A premise moves across erasure.** -/
theorem premW_erase {D D' : Interp} {els' : Prop} :
    ∀ {els : Prop} {ρ : VarEnv} {pr : Prem}, PremW (simEnv B) D els ρ pr → SG QT gdC ρ →
      xPrem grC gdC pr = true →
      (∀ x op avs w, x ∈ premRelsC pr → D x op avs w → D' x op (avs.map eraseA) (eraseC w)) →
      (premElse pr = true → els → els') →
      PremW (simEnv B) D' els' (eraseScope ρ) pr := by
  intro els ρ pr h
  induction h with
  | ifPr he =>
    intro hρ hx _ _
    exact .ifPr (by simpa using evalExp_erase H hρ (by simpa [xPrem] using hx) he)
  | elsePr hels =>
    intro _ _ _ hE
    exact .elsePr (hE rfl hels)
  | letPr he₂ he₁ =>
    intro hρ hx _ _
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .letPr (evalExp_erase H hρ hx.2 he₂) (evalExp_erase H hρ hx.1 he₁)
  | @rulePr ρ x args op e avs w hargs he hD =>
    intro hρ hx hR _
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .rulePr (evalArgs_erase H hρ hx.1.2 hargs) (evalExp_erase H hρ hx.2 he)
      (hR x op avs w (by simp [premRelsC]) hD)
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
    rw [← CodeErase.EraseAll.eraseScope_bindVals]
    exact ih (sg_bindVals hρ row) hx.1.1 (fun x op avs w hx' => hR x op avs w hx')
      (fun he => hE he)
  | @iterList ρ pr it ds xvs dls k hit hdoms hne hdl hlen hrows ih =>
    intro hρ hx hR hE
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterList (dls := dls.map fun p => (p.1, p.2.map eraseC)) (k := k) hit
      (evalDoms_erase H hρ hx.2 hdoms) hne (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [CodeErase.EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← CodeErase.EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ (sg_bindVals hρ r₀) hx.1.1 (fun x op avs w hx' => hR x op avs w hx')
        (fun he => hE he)
  | @iterListN ρ pr eₙ ido ds xvs dls kv k hdoms hn hk hdl hlen hrows ih =>
    intro hρ hx hR hE
    simp only [xPrem, Bool.and_eq_true] at hx
    have hxn : xExp grC gdC eₙ = true := by simpa [xIter] using hx.1.2
    refine .iterListN (dls := dls.map fun p => (p.1, p.2.map eraseC)) (kv := eraseC kv) (k := k)
      (evalDoms_erase H hρ hx.2 hdoms) (evalExp_erase H hρ hxn hn) (by rw [asNat?_eraseC]; exact hk)
      (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [CodeErase.EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← CodeErase.EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ (sg_bindVals hρ r₀) hx.1.1 (fun x op avs w hx' => hR x op avs w hx')
        (fun he => hE he)

omit H in
theorem relPrem_else {pr : Prem} (h : relPrem pr = true) : premElse pr = false := by
  simp only [relPrem, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact h.1

omit H in
theorem relPrem_rels {pr : Prem} (h : relPrem pr = true) : ∀ x ∈ premRelsC pr, relG.contains x = true := by
  simp only [relPrem, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
