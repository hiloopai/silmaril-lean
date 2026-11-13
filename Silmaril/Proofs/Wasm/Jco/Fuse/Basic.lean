module

public import Silmaril.Wasm.Jco.Fuse.Defs
public import Silmaril.Wasm.Component.Env.Thms
public import Silmaril.Wasm.Component.Passes.Flatten.Thms

/-!
# Fusing an adaptor and a core module: proofs

The wrapper-style component (one fused instance) is related to the
adaptor-style component (two instances) through the nested component
`.mk I [.inst (inner m g) args] _`:

* `coreNode_fused`: a fused instance is the nested instance of `inner m g`
  (the interface-size conversions `widenH`/`narrowH` are absorbed by the
  masks of the nested component);
* `flatten_nested`: flattening that nested component gives the adaptor-style
  component (a computation of `flatten`, under the hypotheses that the import
  wiring is scoped and complete, the adaptor imports at most `m`'s exports and
  the world exports at most the adaptor's);
* `denU_flatten'` (flattening preserves the denotation) closes the chain.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Fuse

local notation "ofH" => Strategy.ofHandler

variable {M : Type} [CoreModule M]

/-! ## Handler identities at the interface boundary -/

theorem implsN_comp_widenH (e : Nat) (args : List Impl) (p : Nat) :
    (implsN e args p).comp (widenH p) = (implsH e args).comp (maskH p) := by
  funext q
  by_cases hq : q.1 < p
  · simp [Handler.comp, widenH, maskH, Target.prog, hq, Prog.interp_call, implsN]
  · simp [Handler.comp, widenH, maskH, Target.prog, hq]

theorem narrowH_comp_widenH (k : Nat) : (narrowH k).comp (widenH k) = maskH k := by
  funext q
  by_cases hq : q.1 < k
  · simp [Handler.comp, widenH, maskH, Target.prog, hq, Prog.interp_call, narrowH]
  · simp [Handler.comp, widenH, maskH, Target.prog, hq]

/-! ## The nested component of a fused module -/

theorem inner_exports_length (m : M) (g : Glue) : (inner m g).exports.length = g.exports.length := by
  simp [inner]

theorem inner_mask_left (C : CoreSem (JMod M)) (m : M) (g : Glue) :
    (ofH (maskH (CoreModule.imports m).length)).comp ((inner m g).denU C) = (inner m g).denU C := by
  have hl : (anonIface (CoreModule.imports m).length).length = (CoreModule.imports m).length := by
    simp [anonIface]
  unfold inner
  rw [Comp.denU, ← Strategy.comp_assoc, denNodes_comp, ← Strategy.ofHandler_comp, hl,
    maskH_comp_maskH]

theorem inner_mask_right (C : CoreSem (JMod M)) (m : M) (g : Glue) :
    ((inner m g).denU C).comp (ofH (maskH g.exports.length)) = (inner m g).denU C := by
  have hx := exportsH_comp_maskH (envAfter (anonIface (CoreModule.imports m).length).length
    (inner m g).nodes) (inner m g).exports
  rw [inner_exports_length] at hx
  revert hx
  unfold inner
  intro hx
  rw [Comp.denU, Strategy.comp_assoc, ← Strategy.ofHandler_comp]
  exact congrArg _ (congrArg _ hx)

/-- The nested component does not contain fused modules. -/
theorem inner_fuseSem (C : CoreSem M) (m : M) (g : Glue) :
    (inner m g).denU (fuseSem C) = (inner m g).denU (baseSem C) := by
  unfold inner
  simp only [Comp.denU, denNodes, Node.den]
  rfl

/-- **A fused instance is the nested instance of its parts.** -/
theorem coreNode_fused (C : CoreSem M) (e : Nat) (m : M) (g : Glue) (args : List Impl) :
    coreNode (fuseSem C) e (.fused m g) args =
      (ofH (implsH e args)).comp ((inner m g).denU (fuseSem C)) := by
  rw [inner_fuseSem]
  set U := (inner m g).denU (baseSem C)
  show (ofH (implsN e args (CoreModule.imports m).length)).comp
      ((((ofH (widenH (CoreModule.imports m).length)).comp U).comp
        (ofH (narrowH g.exports.length))).comp (ofH (widenH g.exports.length))) = _
  rw [Strategy.comp_assoc, Strategy.comp_assoc, ← Strategy.comp_assoc (ofH (implsN _ _ _)),
    ← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp, implsN_comp_widenH,
    narrowH_comp_widenH, Strategy.ofHandler_comp, Strategy.comp_assoc, ← Strategy.comp_assoc _ U,
    inner_mask_left, inner_mask_right]

/-- The nested form of the wrapper-style component. -/
def nested (I W : Iface) (m : M) (g : Glue) (args : List Impl) : Comp (JMod M) :=
  .mk I [.inst (inner m g) args] (liftExports W I.length)

/-- **The wrapper-style component is its nested form.** -/
theorem wrapper_nested (C : CoreSem M) (I W : Iface) (m : M) (g : Glue) (args : List Impl) :
    (wrapperComp I W m g args).denU (fuseSem C) = (nested I W m g args).denU (fuseSem C) := by
  have hw : (Node.inst (inner m g) args).width = (Node.core (M := JMod M) (.fused m g) args).width :=
    inner_exports_length m g
  simp only [wrapperComp, nested, Comp.denU, denNodes, envAfter, Node.den, hw]
  rw [coreNode_fused]

/-! ## Flattening the nested form -/

theorem fwd_subst (i : Nat) (σ : List Impl) : (Impl.fwd i).subst σ = σ[i]?.getD Impl.trap := by
  cases h : σ[i]? with
  | none => simp [Impl.subst, h]
  | some im => simp [Impl.subst, h]

theorem subst_range_fwd {n : Nat} {im : Impl} (h : im.Scoped n) :
    im.subst ((List.range n).map Impl.fwd) = im := by
  obtain ⟨c, t⟩ := im
  cases t with
  | const r => rfl
  | call r =>
    have hr : r < n := h
    simp [Impl.subst, List.getElem?_range hr]

theorem range_map_getD (l : List Impl) :
    (List.range l.length).map (fun i => l[i]?.getD Impl.trap) = l := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [List.getElem?_eq_getElem h₂]

theorem map_fwd_subst (σ : List Impl) :
    ((List.range σ.length).map Impl.fwd).map (Impl.subst σ) = σ := by
  rw [List.map_map]
  conv => rhs; rw [← range_map_getD σ]
  exact List.map_congr_left fun i _ => fwd_subst i σ

/-- Scoped wiring is unchanged by the identity substitution. -/
theorem args_subst (n : Nat) (args : List Impl) (hsc : ScopedList n args) (i : Nat) :
    (args[i]?.getD Impl.trap).subst ((List.range n).map Impl.fwd) = args[i]?.getD Impl.trap := by
  cases h : args[i]? with
  | none => rfl
  | some im => exact subst_range_fwd (hsc im (List.mem_of_getElem? h))

theorem sigmaC_eq (n : Nat) (args : List Impl) (hsc : ScopedList n args) (p : Nat)
    (hlen : args.length = p) :
    (List.range p).map (fun i => (args[i]?.getD Impl.trap).subst ((List.range n).map Impl.fwd)) =
      args := by
  subst hlen
  conv => rhs; rw [← range_map_getD args]
  exact List.map_congr_left fun i _ => args_subst n args hsc i

theorem fwdFrom_subst_append (σ : List Impl) (n w kA : Nat) (hk : kA ≤ w) :
    (fwdFrom σ.length kA).map (Impl.subst (σ ++ (List.range w).map fun i => Impl.fwd (n + i))) =
      fwdFrom n kA := by
  simp only [fwdFrom, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < w := lt_of_lt_of_le (List.mem_range.mp hi) hk
  simp [fwd_subst, List.getElem?_append_right, List.getElem?_range hi']

theorem liftExports_subst (σ : List Impl) (d : Nat) :
    ∀ (W : Iface) (b : Nat), (∀ j, j < W.length → σ[b + j]? = some (Impl.fwd (b + d + j))) →
      (liftExports W b).map (fun x => { x with impl := x.impl.subst σ }) = liftExports W (b + d)
  | [], _, _ => rfl
  | x :: W, b, h => by
    have h0 : σ[b]? = some (Impl.fwd (b + d)) := h 0 (by simp)
    have hs : ∀ j, j < W.length → σ[b + 1 + j]? = some (Impl.fwd (b + 1 + d + j)) := by
      intro j hj
      have := h (j + 1) (by simp; omega)
      rwa [show b + (j + 1) = b + 1 + j by omega, show b + d + (j + 1) = b + 1 + d + j by omega]
        at this
    have ih := liftExports_subst σ d W (b + 1) hs
    simp only [liftExports, List.map_cons, ih, show b + 1 + d = b + d + 1 by omega]
    simp [Impl.subst, h0]

/-- The substitution of the outer environment after flattening the nested
form: export `j` of the fused module is export `j` of the adaptor. -/
theorem sigmaO_get (n p w k : Nat) (args : List Impl) (hp : args.length = p) (j : Nat)
    (hj : j < k) :
    ((List.range n).map Impl.fwd ++
      ((List.range k).map fun j => (⟨"", default, Impl.fwd (p + w + j)⟩ : Export)).map
        (fun x => x.impl.subst (args ++ (List.range w).map (fun i => Impl.fwd (n + i)) ++
          (List.range k).map (fun i => Impl.fwd (n + w + i)))))[n + j]? =
      some (Impl.fwd (n + w + j)) := by
  have h₁ : ((List.range n).map Impl.fwd).length = n := by simp
  rw [List.getElem?_append_right (by omega), h₁, Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_map, List.getElem?_range hj]
  have h₂ : (args ++ (List.range w).map (fun i => Impl.fwd (n + i))).length = p + w := by simp [hp]
  show some ((Impl.fwd (p + w + j)).subst _) = _
  rw [fwd_subst, List.getElem?_append_right (by omega), h₂, Nat.add_sub_cancel_left,
    List.getElem?_map, List.getElem?_range hj]
  rfl

theorem flatten_nested (I W : Iface) (m : M) (g : Glue) (args : List Impl)
    (hlen : args.length = (CoreModule.imports m).length) (hsc : ScopedList I.length args)
    (hg : g.imports.length ≤ (CoreModule.exports m).length) (hW : W.length ≤ g.exports.length) :
    (flatten (nested I W m g args)).toComponent = adaptorComp I W m g args := by
  have hp : (anonIface (CoreModule.imports m).length).length = (CoreModule.imports m).length := by
    simp [anonIface]
  have hσc : (List.range (anonIface (CoreModule.imports m).length).length).map
      (fun i => (args[i]?.getD Impl.trap).subst ((List.range I.length).map Impl.fwd)) = args := by
    rw [hp]
    exact sigmaC_eq _ args hsc _ hlen
  have h2 := fwdFrom_subst_append args I.length (CoreModule.exports (JMod.base m)).length
    g.imports.length hg
  simp only [flatten, nested, inner, flattenNodes, Linked.toComponent, adaptorComp, hσc]
  rw [← hlen, map_fwd_subst, h2, liftExports_subst _ (CoreModule.exports m).length W I.length]
  · rfl
  · intro j hj
    exact sigmaO_get I.length args.length _ g.exports.length args rfl j (lt_of_lt_of_le hj hW)

/-! ## The theorems -/

/-- The adaptor-style component does not contain fused modules. -/
theorem adaptor_fuseSem (C : CoreSem M) (I W : Iface) (m : M) (g : Glue) (args : List Impl) :
    (adaptorComp I W m g args).denU (fuseSem C) = (adaptorComp I W m g args).denU (baseSem C) := by
  unfold adaptorComp
  simp only [Comp.denU, denNodes, Node.den]
  rfl

/-- **Fusion is correct**: the wrapper-style component over the fused module
denotes as the adaptor-style component. -/
theorem wrapper_adaptor (C : CoreSem M) (I W : Iface) (m : M) (g : Glue) (args : List Impl)
    (hlen : args.length = (CoreModule.imports m).length) (hsc : ScopedList I.length args)
    (hg : g.imports.length ≤ (CoreModule.exports m).length) (hW : W.length ≤ g.exports.length) :
    (wrapperComp I W m g args).denU (fuseSem C) = (adaptorComp I W m g args).denU (baseSem C) := by
  rw [wrapper_nested, ← denU_flatten' (fuseSem C) (nested I W m g args),
    ← Linked.denU_toComponent, flatten_nested I W m g args hlen hsc hg hW, adaptor_fuseSem]

/-! ## The simple FFI style -/

theorem findFn_lt : ∀ (I : Iface) (n : String) (i : Nat) (ft : FuncTy),
    findFn I n = some (i, ft) → i < I.length
  | [], _, _, _, h => nomatch h
  | x :: I, n, i, ft, h => by
    by_cases hx : x.1 = n
    · have h' : some ((0 : Nat), x.2) = some (i, ft) := by simpa [findFn, hx] using h
      cases h'
      simp
    · have h' : (findFn I n).map (fun r => (r.1 + 1, r.2)) = some (i, ft) := by
        simpa [findFn, hx] using h
      obtain ⟨⟨i', ft'⟩, hr, he⟩ := Option.map_eq_some_iff.mp h'
      cases he
      simpa using findFn_lt I n i' ft' hr

theorem simpleImports_scoped (I : Iface) (E : CoreIface) : ScopedList I.length (simpleImports I E) := by
  intro im him
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp him
  cases h : findFn I x.1 with
  | none => trivial
  | some r =>
    obtain ⟨i, ft⟩ := r
    exact findFn_lt I x.1 i ft h

/-- **Fusion is correct for the simple FFI style** (no hypotheses). -/
theorem simpleWrapper_simpleComp (C : CoreSem M) (I W : Iface) (m : M) :
    (simpleWrapper I W m).denU (fuseSem C) = (simpleComp I W m).denU (baseSem C) :=
  wrapper_adaptor C I W m _ _ (by simp [simpleImports]) (simpleImports_scoped I _) le_rfl
    (by simp [simpleAdaptor])

end Silmaril.Proofs.Wasm.Jco.Fuse
