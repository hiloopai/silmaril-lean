module

public import Silmaril.Wasm.Component.Passes.Fusion.Defs
public import Silmaril.Wasm.Component.Contract.Defs

/-!
# Adapter fusion: soundness

* `runChain_fuseChain`: a fused chain runs exactly as the original one, for
  any continuation, by the fusion laws of `Silmaril.Wasm.Component.Adapter.Thms`
  (canonical ABI round trip; lifted values are well typed;
  `canonFlat_trivial`).
* `denU_fuseComponent`: **adapter fusion preserves the denotation** of every
  component (equality of strategies), for every core semantics.
* `fusePass C : Pass (contract C)` and `fuseLinkedPass C`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Compile.PassAPI

variable {M : Type} [CoreModule M]

theorem runChain_cons_congr {E : Sig.{0}} (a : Adapter) {c c' : List Adapter}
    {k : Payload → Prog E (Option Payload)} (h : runChain c k = runChain c' k) :
    runChain (a :: c) k = runChain (a :: c') k := by
  funext x
  simp only [runChain, h]

/-- A check below a lift is redundant. -/
theorem fuse_check_lift {E : Sig.{0}} (ft : FuncTy) (c : List Adapter)
    (k : Payload → Prog E (Option Payload)) :
    runChain (.check ft :: .lift ft :: c) k = runChain (.lift ft :: c) k := by
  apply runChain_fuse
  · rintro (xs | vs)
    · rfl
    · simp only [Adapter.down, Option.bind_map]
      unfold checkVals checkLower
      split_ifs with h <;> simp [Adapter.down, checkLower, h]
  · rintro (ys | ws)
    · simp only [Adapter.up, Option.bind_map]
      cases e : liftArgs ft.results ys with
      | none => rfl
      | some ws => simp [Adapter.up, checkVals, checkList_of_liftArgs e]
    · rfl

/-- A check above a lower is redundant. -/
theorem fuse_lower_check {E : Sig.{0}} (ft : FuncTy) (c : List Adapter)
    (k : Payload → Prog E (Option Payload)) :
    runChain (.lower ft :: .check ft :: c) k = runChain (.lower ft :: c) k := by
  apply runChain_fuse
  · rintro (xs | vs)
    · simp only [Adapter.down, Option.bind_map]
      cases e : liftArgs ft.params xs with
      | none => rfl
      | some vs => simp [Adapter.down, checkVals, checkList_of_liftArgs e]
    · rfl
  · rintro (ys | ws)
    · rfl
    · simp only [Adapter.up, Option.bind_map]
      unfold checkVals checkLower
      split_ifs with h <;> simp [Adapter.up, checkLower, h]

/-- **A fused chain runs as the original one.** -/
theorem runChain_fuseChain {E : Sig.{0}} (c : List Adapter)
    (k : Payload → Prog E (Option Payload)) : runChain (fuseChain c) k = runChain c k := by
  fun_induction fuseChain c with
  | case1 ft c ih => rw [ih, fuse_lower_lift]
  | case2 ft ft' c _ ih => exact runChain_cons_congr _ ih
  | case3 ft c ih => rw [ih, fuse_lift_lower]
  | case4 ft ft' c _ ih => exact runChain_cons_congr _ ih
  | case5 ft c ih => rw [ih, fuse_check_lift]
  | case6 ft ft' c _ ih => exact runChain_cons_congr _ ih
  | case7 ft c ih => rw [ih, fuse_lower_check]
  | case8 ft ft' c _ ih => exact runChain_cons_congr _ ih
  | case9 ft c h ih =>
    simp only [Bool.and_eq_true] at h
    rw [canon_trivial ft h.1 h.2]
    exact runChain_cons_congr _ ih
  | case10 ft c _ ih => exact runChain_cons_congr _ ih
  | case11 a c _ _ _ _ _ ih => exact runChain_cons_congr _ ih
  | case12 => rfl

/-- Fusion preserves the program of a wiring `Impl`. -/
theorem Impl.prog_fuse (e : Nat) (im : Impl) : im.fuse.prog e = im.prog e :=
  runChain_fuseChain im.chain _

/-- **Adapter fusion preserves the denotation**, at every nesting depth and for
every core semantics. -/
theorem denU_fuseComponent (C : CoreSem M) (c : Comp M) :
    (fuseComponent c).denU C = c.denU C :=
  denU_mapImpls C Impl.prog_fuse c

omit [CoreModule M] in
theorem imports_mapImpls (f : Impl → Impl) (c : Comp M) :
    (c.mapImpls f).imports = c.imports := by
  cases c; rfl

omit [CoreModule M] in
theorem exports_length_mapImpls (f : Impl → Impl) (c : Comp M) :
    (c.mapImpls f).exports.length = c.exports.length := by
  cases c; simp [Comp.mapImpls]

/-- The adapter fusion pass. -/
def fusePass (C : CoreSem M) : Pass (contract C) where
  run := fuseComponent
  inv_run _ := trivial
  sound {c} _ := ⟨congrArg List.length (imports_mapImpls _ c),
    exports_length_mapImpls _ c, (denU_fuseComponent C c).le⟩

omit [CoreModule M] in
theorem toComponent_fuseLinked (l : Linked M) :
    (fuseLinked l).toComponent = fuseComponent l.toComponent := by
  obtain ⟨I, ns, xs⟩ := l
  simp only [fuseLinked, Linked.toComponent, fuseComponent, Comp.mapImpls, List.map_map]
  congr 1
  induction ns with
  | nil => simp [Comp.mapImplsNodes]
  | cons n ns ih =>
    simp only [List.map_cons, Comp.mapImplsNodes, Comp.mapImplsNode] at ih ⊢
    rw [ih]
    rfl

/-- Adapter fusion preserves the denotation of a flat component. -/
theorem denU_fuseLinked (C : CoreSem M) (l : Linked M) : (fuseLinked l).denU C = l.denU C := by
  rw [← Linked.denU_toComponent, toComponent_fuseLinked, denU_fuseComponent,
    Linked.denU_toComponent]

/-- The adapter fusion pass on the flat IR. -/
def fuseLinkedPass (C : CoreSem M) : Pass (linkedIR C).contract where
  run := fuseLinked
  inv_run _ := trivial
  sound {l} _ := ⟨rfl, List.length_map _, (denU_fuseLinked C l).le⟩

end Silmaril.Wasm.Component
