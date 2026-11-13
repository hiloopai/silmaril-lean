module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Package

/-!
# The WIT binary round trip: packages

`decodeItems_encodeItems`: the item sections the encoder writes for a valid
package decode to the package's normal form.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

theorem mapM_forall₂ {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by
    have : l' = [] := by simpa [List.mapM_nil, pure, Except.pure] using h.symm
    subst this; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hf : f a with
    | error err => rw [hf] at h; cases h
    | ok b =>
      rw [hf] at h
      cases hl : l.mapM f with
      | error err => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        have : l' = b :: bs := (Except.ok.inj h).symm
        subst this; exact .cons hf (mapM_forall₂ hl)

theorem decTops_items {L : List (String × List ComponentDecl)} {tops : List Top}
    (h : List.Forall₂ (fun x t => decTop x.1 x.2 = .ok t) L tops) :
    ∀ k, decTops k (allItemSections L k) = .ok tops := by
  induction h with
  | nil => intro k; rfl
  | @cons x t L tops hx _ ih =>
    intro k
    have hs : allItemSections (x :: L) k = itemSections k x.1 x.2 ++ allItemSections L (k + 1) := by
      simp [allItemSections, List.zipIdx_cons]
    rw [hs]
    simp only [itemSections, List.cons_append, List.nil_append, decTops, ne_eq, not_true_eq_false,
      ↓reduceIte, hx, ih (k + 1), bind, Except.bind]; rfl

/-- The decoded item of an interface of `p`. -/
def ifaceTop (p : PackageName) (nb : String × Interface) : Top := .iface p nb.1 nb.2.normalize

/-- The decoded item of a world of `p`. -/
def worldTop (p : PackageName) (nw : String × World) : Top := .world p nw.1 nw.2.normalize

theorem assemble_tops {p : PackageName} {is : List (String × Interface)} {ws : List (String × World)}
    (hne : is ≠ [] ∨ ws ≠ []) :
    assemble (is.map (ifaceTop p) ++ ws.map (worldTop p)) =
      .ok { name := p, interfaces := is.map fun nb => (nb.1, nb.2.normalize),
            worlds := ws.map fun nw => (nw.1, nw.2.normalize) } := by
  have hpkg : ∀ t ∈ is.map (ifaceTop p) ++ ws.map (worldTop p), t.pkg = p := by
    intro t ht
    rcases List.mem_append.mp ht with h | h <;>
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h; rfl
  have hfi : (is.map (ifaceTop p) ++ ws.map (worldTop p)).filterMap Top.iface? =
      is.map fun nb => (nb.1, nb.2.normalize) := by
    simp [List.filterMap_append, List.filterMap_map, ifaceTop, worldTop, Top.iface?, Function.comp_def]
  have hfw : (is.map (ifaceTop p) ++ ws.map (worldTop p)).filterMap Top.world? =
      ws.map fun nw => (nw.1, nw.2.normalize) := by
    simp [List.filterMap_append, List.filterMap_map, ifaceTop, worldTop, Top.world?, Function.comp_def]
  cases hl : is.map (ifaceTop p) ++ ws.map (worldTop p) with
  | nil => rcases hne with h | h <;> simp_all
  | cons t ts =>
    rw [hl] at hpkg hfi hfw
    have ht : t.pkg = p := hpkg t (by simp)
    have hany : ts.any (fun s => decide (s.pkg ≠ p)) = false := by
      simp only [List.any_eq_false, decide_eq_true_eq, not_not]
      intro s hs; exact hpkg s (by simp [hs])
    simp only [assemble, hany, Bool.false_eq_true, ↓reduceIte, ht, hfi, hfw]; rfl

/-- **The item sections of a package decode to its normal form.** -/
theorem decodeItems_encodeItems {deps : Env} {p : Package} (hv : p.Valid deps) {ss : List Section}
    (h : encodeItems deps p = .ok ss) : decodeItems ss = .ok p.normalize := by
  unfold encodeItems at h
  dsimp only at h
  cases hi : p.interfaces.mapM (encodeIfaceItem (p.env deps) p.name) with
  | error err => rw [hi] at h; cases h
  | ok ifs =>
    rw [hi] at h
    cases hw : p.worlds.mapM (encodeWorldItem (p.env deps) p.name) with
    | error err => rw [hw] at h; cases h
    | ok ws =>
      rw [hw] at h
      have hss : ss = allItemSections (ifs ++ ws) := (Except.ok.inj h).symm
      rw [hss]; exact decodeItems_of hv hi hw
where
  decodeItems_of {deps : Env} {p : Package} (hv : p.Valid deps) {ifs ws : List (String × List ComponentDecl)}
      (hi : p.interfaces.mapM (encodeIfaceItem (p.env deps) p.name) = .ok ifs)
      (hw : p.worlds.mapM (encodeWorldItem (p.env deps) p.name) = .ok ws) :
      decodeItems (allItemSections (ifs ++ ws)) = .ok p.normalize := by
    obtain ⟨hne, hiv, hwv, henv, hww⟩ := hv
    have hbv : ∀ nb ∈ p.interfaces, nb.2.Valid := fun nb hnb =>
      (henv (p.name.iface nb.1, nb.2) (List.mem_append_left _ (List.mem_map.mpr ⟨nb, hnb, rfl⟩))).2
    have fi : List.Forall₂ (fun x t => decTop x.1 x.2 = .ok t) ifs (p.interfaces.map (ifaceTop p.name)) :=
      ifaces_tops henv hiv hbv (mapM_forall₂ hi)
    have fw : List.Forall₂ (fun x t => decTop x.1 x.2 = .ok t) ws (p.worlds.map (worldTop p.name)) :=
      worlds_tops henv hwv hww (mapM_forall₂ hw)
    rw [decodeItems, decTops_items (List.rel_append fi fw) 0]
    exact assemble_tops hne
  ifaces_tops {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {pn : PackageName}
      {is : List (String × Interface)} (hiv : ∀ nb ∈ is, (pn.iface nb.1).Valid) (hbv : ∀ nb ∈ is, nb.2.Valid)
      {ifs : List (String × List ComponentDecl)}
      (hf : List.Forall₂ (fun a b => encodeIfaceItem env pn a = .ok b) is ifs) :
      List.Forall₂ (fun x t => decTop x.1 x.2 = .ok t) ifs (is.map (ifaceTop pn)) := by
    induction hf with
    | nil => exact .nil
    | @cons a b is ifs hab _ ih =>
      refine .cons ?_ (ih (fun nb h => hiv nb (by simp [h])) (fun nb h => hbv nb (by simp [h])))
      unfold encodeIfaceItem at hab
      cases hd : encodeIface env (pn.iface a.1) a.2 with
      | error err => rw [hd] at hab; cases hab
      | ok ds =>
        rw [hd] at hab
        have hb : b = (a.1, ds) := (Except.ok.inj hab).symm
        rw [hb]
        exact decTop_encodeIface henv (hiv a (by simp)) (hbv a (by simp)) hd
  worlds_tops {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {pn : PackageName}
      {ws : List (String × World)} (hwv : ∀ nw ∈ ws, (pn.iface nw.1).Valid) (hww : ∀ nw ∈ ws, nw.2.Valid)
      {wss : List (String × List ComponentDecl)}
      (hf : List.Forall₂ (fun a b => encodeWorldItem env pn a = .ok b) ws wss) :
      List.Forall₂ (fun x t => decTop x.1 x.2 = .ok t) wss (ws.map (worldTop pn)) := by
    induction hf with
    | nil => exact .nil
    | @cons a b ws wss hab _ ih =>
      refine .cons ?_ (ih (fun nw h => hwv nw (by simp [h])) (fun nw h => hww nw (by simp [h])))
      unfold encodeWorldItem at hab
      cases hd : encodeWorld env a.2 with
      | error err => rw [hd] at hab; cases hab
      | ok ds =>
        rw [hd] at hab
        have hb : b = (a.1, worldWrapper pn a.1 ds) := (Except.ok.inj hab).symm
        rw [hb]
        exact decTop_world (hwv a (by simp)) (decWorld_encodeWorld henv (hww a (by simp)) hd)

end Silmaril.Wasm.Wit.Binary
