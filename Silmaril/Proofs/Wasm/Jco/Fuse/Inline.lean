module

public import Silmaril.Wasm.Jco.Fuse.Inline.Defs
public import Silmaril.Wasm.Jco.Fuse.Glue.Thms
public import Silmaril.Wasm.Component.Env.Thms
import Silmaril.Proofs.Wasm.Jco.Fuse.Basic

/-!
# Fusion of glue modules is inlining: proofs

When both parts are glue code, every instance of `inner g₁ g₂` is a handler,
so the environment strategies collapse to handlers (`ext_ofH`, by the pairing
law `cp`), and the denotation of `inner g₁ g₂` is a composite handler. The
right projection of an environment extension is then a handler computation
(`case_split_fwdFrom`), and the masks at the interface boundaries are
idempotent; what remains is `glueH_inline`.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Fuse

local notation "ofH" => Strategy.ofHandler

/-! ## Handlers in environments -/

theorem ext_ofH (e : Nat) (hD hN : Handler sigU sigU) :
    ext e (ofH hD) (ofH hN) =
      ofH (hD.comp ((Handler.case (Handler.id sigU) hN).comp (splitH e))) := by
  rw [ext, ← Strategy.ofHandler_id, pairLaws.cp, ← Strategy.ofHandler_comp,
    ← Strategy.ofHandler_comp]

theorem case_inr_call (H : Handler sigU sigU) (q : sigU.Op) :
    (Prog.call (E := sigU ⊕ₛ sigU) (.inr q) fun n => .pure n).interp
      (Handler.case (Handler.id sigU) H) = H q := by
  exact Prog.bind_pure (H q)

/-- The right side of an extension at `e`, used by forwarding wiring. -/
theorem case_split_fwdFrom (H : Handler sigU sigU) (e n k : Nat) (hk : e + k ≤ n) :
    ((Handler.case (Handler.id sigU) H).comp (splitH e)).comp (implsH n (fwdFrom e k)) =
      H.comp (maskH k) := by
  funext q
  obtain ⟨j, x⟩ := q
  by_cases hj : j < k
  · have h₁ : (fwdFrom e k)[j]? = some (Impl.fwd (e + j)) := by
      simp [fwdFrom, List.getElem?_range hj]
    have h₂ : e + j < n := by omega
    have h₃ : ¬ e + j < e := by omega
    simp only [Handler.comp, implsH, h₁, Impl.prog, runChain, Target.prog, h₂, ↓reduceIte,
      Prog.interp_call, Prog.interp_pure, Prog.bind_pure, splitH, h₃, maskH, hj]
    have h₄ : e + j - e = j := by omega
    rw [h₄]
    exact case_inr_call H (j, x)
  · have h₁ : (fwdFrom e k)[j]? = none := by simp [fwdFrom]; omega
    simp [Handler.comp, implsH, h₁, maskH, Target.prog, hj]

theorem glueH_comp_maskH (c : List Code) (n : Nat) (h : c.length ≤ n) :
    (glueH c).comp (maskH n) = glueH c := by
  funext q
  obtain ⟨j, x⟩ := q
  by_cases hj : j < n
  · simp [Handler.comp, maskH, Target.prog, hj, Prog.interp_call]
  · have h₁ : c[j]? = none := by simp; omega
    simp [Handler.comp, maskH, Target.prog, hj, glueH, h₁]

theorem maskH_comp_narrowH (k : Nat) : (maskH k).comp (narrowH k) = narrowH k := by
  funext q
  simp [Handler.comp, maskH, Target.prog, narrowH, q.1.isLt, Prog.interp_call]

/-! ## The denotation of `inner` for glue parts -/

theorem coreNode_base_glue (e : Nat) (g : Glue) (args : List Impl) :
    coreNode (baseSem glueSem) e (.base g) args =
      ofH ((implsN e args g.imports.length).comp (g.handler.comp (widenH g.exports.length))) := by
  rw [Strategy.ofHandler_comp, Strategy.ofHandler_comp]
  rfl

theorem coreNode_glue {M : Type} [CoreModule M] (C : CoreSem M) (e : Nat) (g : Glue)
    (args : List Impl) :
    coreNode (baseSem C) e (.glue g) args =
      ofH ((implsN e args g.imports.length).comp (g.handler.comp (widenH g.exports.length))) := by
  rw [Strategy.ofHandler_comp, Strategy.ofHandler_comp]
  rfl

theorem inner_glue (g₁ g₂ : Glue) :
    (inner g₁ g₂).denU (baseSem glueSem) = ofH (
      (((maskH g₁.imports.length).comp
        ((Handler.case (Handler.id sigU)
          ((implsN g₁.imports.length ((List.range g₁.imports.length).map Impl.fwd)
            g₁.imports.length).comp (g₁.handler.comp (widenH g₁.exports.length)))).comp
          (splitH g₁.imports.length))).comp
      ((Handler.case (Handler.id sigU)
          ((implsN (g₁.imports.length + g₁.exports.length)
            (fwdFrom g₁.imports.length g₂.imports.length) g₂.imports.length).comp
            (g₂.handler.comp (widenH g₂.exports.length)))).comp
        (splitH (g₁.imports.length + g₁.exports.length)))).comp
      (implsH (g₁.imports.length + g₁.exports.length + g₂.exports.length)
        (fwdFrom (g₁.imports.length + g₁.exports.length) g₂.exports.length))) := by
  have hp : (anonIface (CoreModule.imports g₁).length).length = (CoreModule.imports g₁).length := by
    simp [anonIface]
  unfold inner
  simp only [Comp.denU, denNodes, Node.den, coreNode_base_glue, coreNode_glue, ext_ofH, hp,
    envAfter, Node.width, exportsH, List.map_map]
  rw [← Strategy.ofHandler_comp]
  rfl

/-! ## Right-associated forms of the handler identities -/

section Assoc

variable {E F G H : Sig.{0}}

theorem comp_r {a : Handler E F} {b : Handler F G} {c : Handler E G} (h : a.comp b = c)
    (r : Handler G H) : a.comp (b.comp r) = c.comp r := by
  rw [← Handler.comp_assoc', h]

theorem widenH_maskH_r (n : Nat) (r : Handler sigU H) :
    (widenH n).comp ((maskH n).comp r) = (widenH n).comp r := comp_r (widenH_comp_maskH n) r

theorem maskH_maskH_r (n : Nat) (r : Handler sigU H) :
    (maskH n).comp ((maskH n).comp r) = (maskH n).comp r := comp_r (maskH_comp_maskH n) r

theorem implsN_widenH_r (e : Nat) (args : List Impl) (n : Nat) (r : Handler sigU H) :
    (implsN e args n).comp ((widenH n).comp r) = (implsH e args).comp ((maskH n).comp r) := by
  rw [comp_r (implsN_comp_widenH e args n) r, Handler.comp_assoc']

theorem glueH_maskH_r (c : List Code) (n : Nat) (h : c.length ≤ n) (r : Handler sigU H) :
    (glueH c).comp ((maskH n).comp r) = (glueH c).comp r := comp_r (glueH_comp_maskH c n h) r

theorem glueH_glueH_r (lib code : List Code) (r : Handler sigU H) :
    (glueH lib).comp ((glueH code).comp r) = (glueH (code.map (Code.inline lib))).comp r :=
  comp_r (glueH_inline lib code).symm r

theorem case_split_r (K : Handler sigU sigU) (e n k : Nat) (hk : e + k ≤ n) (r : Handler sigU H) :
    (Handler.case (Handler.id sigU) K).comp ((splitH e).comp ((implsH n (fwdFrom e k)).comp r)) =
      K.comp ((maskH k).comp r) := by
  rw [← Handler.comp_assoc', ← Handler.comp_assoc', case_split_fwdFrom K e n k hk,
    Handler.comp_assoc']

end Assoc

/-- **The handler of a fused glue module is that of the inlined module.** -/
theorem fused_glue_handler (g₁ g₂ : Glue) (hg : g₂.imports.length ≤ g₁.exports.length)
    (hk : g₁.code.length ≤ g₂.imports.length) (hc : g₁.code.length ≤ g₁.exports.length) :
    (fuseSem glueSem).sem (.fused g₁ g₂) = (fuseSem glueSem).sem (.glue (Glue.inline g₁ g₂)) := by
  show atSizes _ _ ((inner g₁ g₂).denU (baseSem glueSem)) = ofH (Glue.inline g₁ g₂).handler
  rw [inner_glue, atSizes, ← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp]
  congr 1
  have h₁ : g₁.imports.length + g₂.imports.length ≤ g₁.imports.length + g₁.exports.length := by
    omega
  simp only [Glue.handler, Glue.inline, Handler.comp_assoc', narrowH_comp_widenH,
    glueH_comp_maskH _ _ hc, implsN_widenH_r, implsH_fwd, maskH_maskH_r,
    case_split_r _ _ _ _ (le_refl (g₁.imports.length + g₁.exports.length + g₂.exports.length)),
    maskH_comp_narrowH, case_split_r _ _ _ _ h₁, glueH_maskH_r _ _ hk,
    glueH_glueH_r, widenH_maskH_r]

/-- An instance of the inlined glue module is an instance of the fused module. -/
theorem coreNode_inline (g₁ g₂ : Glue) (hg : g₂.imports.length ≤ g₁.exports.length)
    (hk : g₁.code.length ≤ g₂.imports.length) (hc : g₁.code.length ≤ g₁.exports.length)
    (e : Nat) (args : List Impl) :
    coreNode (fuseSem glueSem) e (.glue (Glue.inline g₁ g₂)) args =
      coreNode (fuseSem glueSem) e (.fused g₁ g₂) args := by
  show (ofH (implsN e args g₁.imports.length)).comp
      (((fuseSem glueSem).sem (.glue (Glue.inline g₁ g₂))).comp (ofH (widenH g₂.exports.length))) =
    (ofH (implsN e args g₁.imports.length)).comp
      (((fuseSem glueSem).sem (.fused g₁ g₂)).comp (ofH (widenH g₂.exports.length)))
  rw [fused_glue_handler g₁ g₂ hg hk hc]
  rfl

/-- **Fusion by inlining is correct**: the component with one instance of the
inlined glue module denotes as the adaptor-style component. -/
theorem inlined_adaptor (I W : Iface) (g₁ g₂ : Glue) (args : List Impl)
    (hlen : args.length = g₁.imports.length) (hsc : ScopedList I.length args)
    (hg : g₂.imports.length ≤ g₁.exports.length) (hW : W.length ≤ g₂.exports.length)
    (hk : g₁.code.length ≤ g₂.imports.length) (hc : g₁.code.length ≤ g₁.exports.length) :
    (Comp.mk I [.core (.glue (Glue.inline g₁ g₂)) args] (liftExports W I.length)).denU
        (fuseSem glueSem) =
      (adaptorComp I W g₁ g₂ args).denU (baseSem glueSem) := by
  rw [← wrapper_adaptor glueSem I W g₁ g₂ args hlen hsc hg hW]
  simp only [wrapperComp, Comp.denU, denNodes, Node.den, coreNode_inline g₁ g₂ hg hk hc]
  rfl

end Silmaril.Proofs.Wasm.Jco.Fuse
