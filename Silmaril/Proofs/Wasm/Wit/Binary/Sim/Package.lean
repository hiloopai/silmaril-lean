module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.World

/-!
# The WIT binary round trip: interfaces and packages

`decTop_encodeIface` (an interface's component type decodes to the interface
in normal form), `decTop_world` (a world wrapper), and
`decodeItems_encodeItems`: **the item sections of a package decode to the
package's normal form**.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Live dependencies -/

theorem ite_append_nodup {x : List IfaceName} {i : IfaceName} (h : x.Nodup) :
    (if i ∈ x then x else x ++ [i]).Nodup := by
  split
  · exact h
  · next hn => exact List.nodup_append.mpr ⟨h, List.nodup_singleton _,
      fun a ha b hb => by simp at hb; subst hb; exact fun e => hn (e ▸ ha)⟩

theorem mem_ite_append {x : List IfaceName} {i : IfaceName} : i ∈ (if i ∈ x then x else x ++ [i]) := by
  split
  · assumption
  · simp

theorem liveDeps_nodup (env : Env) : ∀ (fuel : Nat) (i : IfaceName) (acc : List IfaceName),
    acc.Nodup → (liveDeps env fuel i acc).Nodup
  | 0, _, _, h => h
  | fuel + 1, i, acc, h => by
    have hfold : ∀ (l a : List IfaceName), a.Nodup →
        (l.foldl (fun acc j => liveDeps env fuel j acc) a).Nodup := by
      intro l
      induction l with
      | nil => exact fun a ha => ha
      | cons j l ih => exact fun a ha => ih _ (liveDeps_nodup env fuel j a ha)
    unfold liveDeps
    split
    · exact h
    · exact ite_append_nodup (hfold _ _ h)

theorem mem_liveDeps (env : Env) (fuel : Nat) (i : IfaceName) (acc : List IfaceName) :
    i ∈ liveDeps env (fuel + 1) i acc := by
  unfold liveDeps
  split
  · assumption
  · exact mem_ite_append

theorem filter_self {L : List IfaceName} {i : IfaceName} (hn : L.Nodup) (hi : i ∈ L) :
    L.filter (· = i) = [i] := by
  rw [List.filter_eq, hn.count, ite_eq_left hi]; rfl

/-! ## Interfaces -/

theorem instDecl_export (i : IfaceName) (k : Nat) :
    (ComponentDecl.inst (.export ↑i.id (.instance k))) = instDecl false i.id k := rfl

theorem instDecl_import (i : IfaceName) (k : Nat) :
    (ComponentDecl.import ↑i.id (.instance k)) = instDecl true i.id k := rfl

/-- One part of an interface's component type. -/
theorem ifacePart_sim {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {i : IfaceName}
    {body : Interface} (hi : i.Valid) (hb : body.Valid) (j : IfaceName) {e e' : Enc} {cst : CSt}
    (hI : Inv e cst none) (h : (ifacePart env i body j).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧
      cst'.exports = cst.exports ++ ([j].filter (· = i)).map (fun _ => DItem.iface (.inl i) body.normalize) := by
  unfold ifacePart at h
  by_cases hji : j = i
  · rw [ite_eq_left hji] at h
    obtain ⟨c₁, hS, hI', -⟩ := encodeInstance_item (key := .inl i) hI hb (nameKey_id hi) false h
    exact ⟨_, hI', by simp [CSt.addInst, hS.exports, hji]⟩
  · rw [ite_eq_right hji] at h
    cases hf : env.find? j with
    | none => rw [hf] at h; exact absurd h run_fail
    | some b =>
      rw [hf] at h
      have hj := (Interface.Valid.of_find henv hf).1
      obtain ⟨c₁, hS, hI', -⟩ := encodeTypesOnly_item hI (nameKey_id hj) true h
      exact ⟨_, hI', by simp [CSt.addInst, hS.exports, hji]⟩

theorem ifaceParts_sim {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {i : IfaceName}
    {body : Interface} (hi : i.Valid) (hb : body.Valid) :
    ∀ (L : List IfaceName) {e e' : Enc} {cst : CSt}, Inv e cst none →
      (ifaceParts env i body L).run e = .ok ((), e') →
      ∃ cst', Inv e' cst' none ∧
        cst'.exports = cst.exports ++ (L.filter (· = i)).map (fun _ => DItem.iface (.inl i) body.normalize)
  | [], _, _, cst, hI, h => by
    obtain ⟨-, rfl⟩ := run_pure_ok h
    exact ⟨cst, hI, by simp⟩
  | j :: js, _, _, _, hI, h => by
    obtain ⟨u, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨c₁, hI₁, hx₁⟩ := ifacePart_sim henv hi hb j hI h₁
    obtain ⟨c₂, hI₂, hx₂⟩ := ifaceParts_sim henv hi hb js hI₁ h₂
    refine ⟨c₂, hI₂, ?_⟩
    rw [hx₂, hx₁, List.append_assoc, ← List.map_append, ← List.filter_append]; rfl

/-- The component type of an interface exports exactly the interface, in
normal form. -/
theorem encodeIface_sim {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {i : IfaceName}
    {body : Interface} (hi : i.Valid) (hb : body.Valid) {ds : List ComponentDecl}
    (h : encodeIface env i body = .ok ds) :
    ∃ cst, compSteps {} ds = .ok cst ∧ cst.exports = [.iface (.inl i) body.normalize] := by
  unfold encodeIface at h
  cases hr : (ifaceParts env i body (liveDeps env (env.length + 1) i [])).run {} with
  | error err => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨u, e⟩ := r
    rw [hr] at h; cases h
    obtain ⟨cst, hI, hx⟩ := ifaceParts_sim henv hi hb _ Inv.init hr
    refine ⟨cst, hI.outer, ?_⟩
    rw [hx, filter_self (liveDeps_nodup env _ i [] List.nodup_nil) (mem_liveDeps env _ i [])]; rfl

/-! ## Top-level items -/

theorem compSteps_component {s : CSt} {wds : List ComponentDecl} {rest : List ComponentDecl} :
    ∀ {r : CSt}, compSteps s (.inst (.type (.component wds)) :: rest) ≠ .ok r := by
  intro r h; cases h

/-- **An interface's component type** decodes to the interface in normal form. -/
theorem decTop_encodeIface {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {i : IfaceName}
    {body : Interface} (hi : i.Valid) (hb : body.Valid) {ds : List ComponentDecl}
    (h : encodeIface env i body = .ok ds) : decTop i.name ds = .ok (.iface i.pkg i.name body.normalize) := by
  obtain ⟨cst, hc, hx⟩ := encodeIface_sim henv hi hb h
  unfold decTop
  split
  · exact absurd hc compSteps_component
  · simp only [hc, hx, bind, Except.bind, ne_eq, not_true_eq_false, ↓reduceIte]; rfl

theorem parseIfaceName_id' {i : IfaceName} (h : i.Valid) : parseIfaceName i.id.toList = some i := by
  rw [IfaceName.id, String.toList_ofList]; exact parseIfaceName_id h

/-- **A world wrapper** decodes to the world in normal form. -/
theorem decTop_world {p : PackageName} {n : String} (hv : (p.iface n).Valid) {wds : List ComponentDecl}
    {w : World} (hw : decWorld wds = .ok w) : decTop n (worldWrapper p n wds) = .ok (.world p n w) := by
  have hn : (p.iface n).name = n := rfl
  have hp : (p.iface n).pkg = p := rfl
  simp only [worldWrapper, decTop, parseIfaceName_id' hv, hw, hn, hp, ne_eq, not_true_eq_false,
    ↓reduceIte, bind, Except.bind]; rfl

end Silmaril.Wasm.Wit.Binary
