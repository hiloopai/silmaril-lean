module

public import Silmaril.Project.Shapes.Component.WacElab.Defs
public import Silmaril.Project.Shapes.Component.Wac.Thms
public import Silmaril.Wasm.Wac.World.Thms
public import Silmaril.Wasm.Component.Passes.Flatten.Thms

/-!
# Standard problem shapes: WAC compositions, elaborated and typed (laws)

* `wacHasTypedWorld_iff`: the decision procedure of `WacHasTypedWorld`;
  `WacHasTypedWorld.of_value`, `WacHasTypedWorld.not_of_value`: rows on registered values.
* `WacHasTypedWorld.wacHasWorld`: **typed implies untyped**. A composition whose typed world
  is a subtype of `W` fits the names-and-sorts world `w` that `W`'s kinds erase to
  (`Wac.World.fits_of_sat`).
* `WacHasTypedWorld.sub`: the shape is closed under supertypes of the target world
  (`Wac.Sub` is transitive).
* `WacComposes.src_parses`, `WacComposes.out_parses`: a row of `wac_composes` gives both
  parses.
* `eq_of_linkedEq`: `linkedEq` is sound; `flattenNodesF_sound`, `flattenF_sound`: the
  fuelled flattening agrees with `flatten` when it answers; `wacDen_eq_of_sameFlat`: two components whose IRs
  flatten to the same flat component have the same denotation under every core semantics and
  names (`Silmaril.Wasm.Component.denU_flatten'`); `DigestBehaviourEq.of_sameFlat`, the row of
  `digest_behaviour_eq` on two registered values.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open Silmaril.Project (Value)
open Silmaril.Wasm Silmaril.Wasm.Wac
open Silmaril.Wasm.Component.Binary (Ast)

/-! ## Typed targets -/

theorem wacHasTypedWorld_iff (imps : Externs) (c : Ast) (W : World.WorldK) :
    wacHasTypedWorld imps c W = true ↔ WacHasTypedWorld imps c W := by
  unfold wacHasTypedWorld WacHasTypedWorld
  cases h : typedWorld imps c with
  | ok cw =>
    simp only [Bool.and_eq_true, World.sat_iff]
    exact ⟨fun ⟨hp, hs⟩ => ⟨hp, cw, rfl, hs⟩,
      fun ⟨hp, cw', hcw, hs⟩ => ⟨hp, by cases hcw; exact hs⟩⟩
  | error e =>
    simp only [Bool.and_false, Bool.false_eq_true, false_iff]
    rintro ⟨_, _, hcw, _⟩
    cases hcw

/-- A row of `wac_has_typed_world` on a registered value, from one kernel `Bool`. -/
theorem WacHasTypedWorld.of_value {X : Value Ast} {imps : Externs} {W : World.WorldK}
    (h : (X.parse.any fun c => wacHasTypedWorld imps c W) = true) :
    X.Satisfies fun c => WacHasTypedWorld imps c W := by
  cases hx : X.parse with
  | none => rw [hx] at h; cases h
  | some c =>
    rw [hx] at h
    exact ⟨c, hx, (wacHasTypedWorld_iff imps c W).mp h⟩

/-- A refutation of `wac_has_typed_world` on a registered value that parses. -/
theorem WacHasTypedWorld.not_of_value {X : Value Ast} {imps : Externs} {W : World.WorldK}
    (h : (X.parse.any fun c => !wacHasTypedWorld imps c W) = true) :
    ¬ X.Satisfies fun c => WacHasTypedWorld imps c W := by
  rintro ⟨c, hx, hc⟩
  rw [hx] at h
  simp only [Option.any_some, Bool.not_eq_true'] at h
  rw [(wacHasTypedWorld_iff imps c W).mpr hc] at h
  cases h

/-- **Typed implies untyped**: if the typed world of `c` is a subtype of `W`, and `W`'s
kinds erase to the names and sorts of `w`, then `c` has the world `w` by names and sorts. -/
theorem WacHasTypedWorld.wacHasWorld {imps : Externs} {c : Ast} {W : World.WorldK}
    {w : Wit.Project.WorldType} (h : WacHasTypedWorld imps c W)
    (hi : World.erase (World.promoteEx W.1) = Targets.imports w)
    (he : World.erase (World.promoteEx W.2) = Targets.exports w) : WacHasWorld c w := by
  obtain ⟨hp, cw, hcw, hs⟩ := h
  unfold typedWorld at hcw
  cases hk : pkgKinds c with
  | error e => rw [hk] at hcw; cases hcw
  | ok ks =>
    rw [hk] at hcw
    exact ⟨hp, World.fits_of_sat hcw hi he hs⟩

/-- The shape is closed under supertypes of the world. -/
theorem WacHasTypedWorld.sub {imps : Externs} {c : Ast} {W W' : World.WorldK}
    (h : WacHasTypedWorld imps c W)
    (hW : Sub (.comp none (World.promoteEx W.1) (World.promoteEx W.2))
      (.comp none (World.promoteEx W'.1) (World.promoteEx W'.2))) :
    WacHasTypedWorld imps c W' := by
  obtain ⟨hp, cw, hcw, hs⟩ := h
  exact ⟨hp, cw, hcw, Sub.trans hs hW⟩

/-! ## Elaboration -/

theorem WacComposes.src_parses {pkgs : List (String × Value Ast)}
    {src : Value Wac.Text.Document} {out : Value Ast} (h : WacComposes pkgs src out) :
    src.Parses := by
  obtain ⟨d, _, _, hd, _⟩ := h
  simp [Silmaril.Project.Value.Parses, hd]

theorem WacComposes.out_parses {pkgs : List (String × Value Ast)}
    {src : Value Wac.Text.Document} {out : Value Ast} (h : WacComposes pkgs src out) :
    out.Parses := by
  obtain ⟨_, _, c, _, _, hc, _⟩ := h
  simp [Silmaril.Project.Value.Parses, hc]

/-! ## Equal flattenings, equal denotations -/

theorem eq_of_tgtEq : ∀ {a b : Silmaril.Wasm.Component.Target}, tgtEq a b = true → a = b
  | .call a, .call b, h => by
    simp only [tgtEq, beq_iff_eq] at h
    rw [h]
  | .call _, .const _, h | .const _, _, h => by simp [tgtEq] at h

theorem eq_of_implEq {a b : Silmaril.Wasm.Component.Impl} (h : implEq a b = true) : a = b := by
  obtain ⟨c, t⟩ := a
  obtain ⟨c', t'⟩ := b
  simp only [implEq, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1, eq_of_tgtEq h.2]

theorem eq_of_listEq {α : Type} {f : α → α → Bool} (hf : ∀ {a b : α}, f a b = true → a = b) :
    ∀ {as bs : List α}, listEq f as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [listEq, Bool.and_eq_true] at h
    rw [hf h.1, eq_of_listEq hf h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [listEq] at h

theorem eq_of_exportEq {a b : Silmaril.Wasm.Component.Export} (h : exportEq a b = true) :
    a = b := by
  obtain ⟨n, t, i⟩ := a
  obtain ⟨n', t', i'⟩ := b
  simp only [exportEq, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1.1, h.1.2, eq_of_implEq h.2]

theorem eq_of_coreEq {a b : Silmaril.Wasm.Component.Binary.CoreMod} (h : coreEq a b = true) :
    a = b := by
  obtain ⟨b₁, n₁, i₁, e₁⟩ := a
  obtain ⟨b₂, n₂, i₂, e₂⟩ := b
  simp only [coreEq, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1.1.1, h.1.1.2, h.1.2, h.2]

theorem eq_of_nodeEq {a b : Silmaril.Wasm.Component.Binary.CoreMod × List Silmaril.Wasm.Component.Impl}
    (h : nodeEq a b = true) : a = b := by
  obtain ⟨m, is⟩ := a
  obtain ⟨m', is'⟩ := b
  simp only [nodeEq, Bool.and_eq_true] at h
  rw [eq_of_coreEq h.1, eq_of_listEq eq_of_implEq h.2]

/-- `linkedEq` is sound. -/
theorem eq_of_linkedEq {a b : Silmaril.Wasm.Component.Linked Silmaril.Wasm.Component.Binary.CoreMod}
    (h : linkedEq a b = true) : a = b := by
  obtain ⟨i, ns, xs⟩ := a
  obtain ⟨i', ns', xs'⟩ := b
  simp only [linkedEq, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1.1, eq_of_listEq eq_of_nodeEq h.1.2, eq_of_listEq eq_of_exportEq h.2]

section Fuel

open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- `flattenNodesF` agrees with `flattenNodes` whenever it answers. -/
theorem flattenNodesF_sound : ∀ (f : Nat) (σ : List Impl) (eB : Nat) (ns : List (Node M))
    (r : List Impl × Nat × List (M × List Impl)),
    flattenNodesF f σ eB ns = some r → flattenNodes σ eB ns = r
  | 0, _, _, _, _, h => by cases h
  | _ + 1, σ, eB, [], r, h => by
    simp only [flattenNodesF, Option.some.injEq] at h
    rw [flattenNodes, h]
  | f + 1, σ, eB, .core m args :: ns, r, h => by
    simp only [flattenNodesF, Option.map_eq_some_iff] at h
    obtain ⟨r', h', rfl⟩ := h
    simp only [flattenNodes]
    rw [flattenNodesF_sound f _ _ ns r' h']
  | f + 1, σ, eB, .inst (.mk I ns' xs') args :: ns, r, h => by
    simp only [flattenNodesF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨rc, hc, r', h', rfl⟩ := h
    simp only [flattenNodes]
    rw [flattenNodesF_sound f _ _ ns' rc hc, flattenNodesF_sound f _ _ ns r' h']

/-- `flattenF` agrees with `flatten` whenever it answers. -/
theorem flattenF_sound {f : Nat} {c : Comp M} {l : Linked M} (h : flattenF f c = some l) :
    flatten c = l := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [flattenF, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  simp only [flatten, flattenNodesF_sound f _ _ ns r hr]

end Fuel

/-- **Equal flattenings, equal denotations**, under every core semantics and names. -/
theorem wacDen_eq_of_sameFlat {a b : Ast} (h : sameFlat a b = true)
    (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) : wacDen C L a = wacDen C L b := by
  unfold sameFlat at h
  unfold wacDen
  split at h
  · rename_i p q ha hb
    split at h
    · rename_i x y hx hy
      rw [ha, hb]
      simp only [Silmaril.Wasi.Layout.compModel]
      rw [← Silmaril.Wasm.Component.denU_flatten' C p, ← Silmaril.Wasm.Component.denU_flatten' C q,
        flattenF_sound hx, flattenF_sound hy, eq_of_linkedEq h]
    · cases h
  · cases h

/-- A row of `digest_behaviour_eq` under `wacDen`: both values parse, to components with the
same flattening. -/
theorem DigestBehaviourEq.of_sameFlat {X Y : Value Ast} {a b : Ast} (hX : X.Is a) (hY : Y.Is b)
    (h : sameFlat a b = true) (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) : DigestBehaviourEq (wacDen C L) X Y :=
  ⟨a, b, hX, hY, wacDen_eq_of_sameFlat h C L⟩

end Silmaril.Project.Shapes.Component

end

silmaril group silmaril.shapes.component.wac_elab
  (title := "Standard problem shapes: WAC compositions, elaborated and typed")
  (children := [silmaril.shapes.component.wac_composes, silmaril.shapes.component.wac_has_typed_world])

/-! Detached, as the other component shapes (`Silmaril.Project.Shapes.Component.Example.Thms`). -/
silmaril detached silmaril.shapes.component.wac_elab (reason := "shape library")
silmaril detached silmaril.shapes.component.wac_composes (reason := "shape library")
silmaril detached silmaril.shapes.component.wac_has_typed_world (reason := "shape library")
