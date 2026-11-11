module

public import Silmaril.Wasm.FnInst.Peephole.Defs
public import Silmaril.Logic.Inst.Core.Thms

/-!
# The peephole (segment-rewrite) theorem

A rewrite `b ⟶ b'` proved once, at a hole signature `(C₀, τ)` (typically the minimal one,
`Ctx.empty`) and in every model (every handler: the least informative choice for all other
functions), holds:

* at every hole of type `τ` in every larger context, in every model (`hole_valid_transfer`:
  this is the satisfaction condition, through `Valid.map`);
* when `τ` puts no requirement on configurations (`SegTy.Free`), inside every context of every
  body, as segment equivalence at every type and as body equivalence at every function type
  (`peephole`, `peephole_seg`, `peephole_fn`), and as a valid sentence of the all-function
  institution about any function index (`peephole_all`).

No property of the rewrite is used beyond its validity at `(C₀, τ)`: the transfer is generic
in the language (`Lang`) and its contexts (`Plug`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

open CategoryTheory Silmaril.Inst

variable {L : Lang} {W : Type}

/-- The hole signature morphism of an embedding. -/
def HoleSig.ofEmb {C₀ C : Ctx} (σ : C₀ ⟶ C) (τ : SegTy) :
    (⟨C₀, τ⟩ : HoleSig) ⟶ ⟨C, τ⟩ :=
  (⟨σ, rfl⟩ : HoleSig.Hom ⟨C₀, τ⟩ ⟨C, τ⟩)

/-- Transfer of a hole rewrite along an embedding: the satisfaction condition. -/
theorem hole_valid_transfer {C₀ C : Ctx} (σ : C₀ ⟶ C) {τ : SegTy} {b b' : L.Code C₀}
    (hv : (holeInst L W).Valid (S := ⟨C₀, τ⟩) (Formula.atom (b, b'))) (h : Handler L W C) :
    SegEq h τ (L.rename σ b) (L.rename σ b') := by
  have hv' : (holeInst L W).Valid
      ((holeInst L W).map (HoleSig.ofEmb σ τ) (Formula.atom (b, b'))) :=
    Institution.Valid.map (HoleSig.ofEmb σ τ) hv
  exact hv' h

/-- **The peephole theorem**: a rewrite valid at `(C₀, τ)`, for a free `τ`, gives equal
execution functions inside every context of every larger module, under every handler. -/
theorem peephole (P : Plug L) {C₀ C : Ctx} (σ : C₀ ⟶ C) {τ : SegTy} (hτ : SegTy.Free L τ)
    {b b' : L.Code C₀} (hv : (holeInst L W).Valid (S := ⟨C₀, τ⟩) (Formula.atom (b, b')))
    (h : Handler L W C) (K : P.Hole C) :
    L.exec h (P.plug K (L.rename σ b)) = L.exec h (P.plug K (L.rename σ b')) :=
  P.congr h K _ _ (funext fun c => funext fun w => hole_valid_transfer σ hv h c w (hτ c))

theorem peephole_seg (P : Plug L) {C₀ C : Ctx} (σ : C₀ ⟶ C) {τ : SegTy} (hτ : SegTy.Free L τ)
    {b b' : L.Code C₀} (hv : (holeInst L W).Valid (S := ⟨C₀, τ⟩) (Formula.atom (b, b')))
    (h : Handler L W C) (K : P.Hole C) (τ' : SegTy) :
    SegEq h τ' (P.plug K (L.rename σ b)) (P.plug K (L.rename σ b')) := fun c w _ => by
  rw [peephole P σ hτ hv h K]

theorem peephole_fn (P : Plug L) {C₀ C : Ctx} (σ : C₀ ⟶ C) {τ : SegTy} (hτ : SegTy.Free L τ)
    {b b' : L.Code C₀} (hv : (holeInst L W).Valid (S := ⟨C₀, τ⟩) (Formula.atom (b, b')))
    (h : Handler L W C) (K : P.Hole C) (t : FnTy) :
    FnEq h t (P.plug K (L.rename σ b)) (P.plug K (L.rename σ b')) := fun a w _ => by
  rw [peephole P σ hτ hv h K]

/-- The peephole theorem in the all-function institution: the body of any function `i` that
contains the left-hand side is equivalent to the rewritten body, in every model. -/
theorem peephole_all (P : Plug L) {C₀ C : Ctx} (σ : C₀ ⟶ C) {τ : SegTy}
    (hτ : SegTy.Free L τ) {b b' : L.Code C₀}
    (hv : (holeInst L W).Valid (S := ⟨C₀, τ⟩) (Formula.atom (b, b'))) (K : P.Hole C)
    (i : C.Idx .func) :
    (allInst L W).Valid (S := C)
      (Formula.atom (FnAtom.fn i (P.plug K (L.rename σ b)) (P.plug K (L.rename σ b')))) :=
  fun h => peephole_fn P σ hτ hv (show Handler L W C from h) K _

/-- The minimal-signature form: a rewrite proved over the empty context holds inside every
function of every module. -/
theorem peephole_empty (P : Plug L) {τ : SegTy} (hτ : SegTy.Free L τ)
    {b b' : L.Code Ctx.empty}
    (hv : (holeInst L W).Valid (S := ⟨Ctx.empty, τ⟩) (Formula.atom (b, b'))) (C : Ctx)
    (K : P.Hole C) (i : C.Idx .func) :
    (allInst L W).Valid (S := C) (Formula.atom (FnAtom.fn i
      (P.plug K (L.rename (Ctx.ofEmpty C) b)) (P.plug K (L.rename (Ctx.ofEmpty C) b')))) :=
  peephole_all P (Ctx.ofEmpty C) hτ hv K i

/-- **Congruence as entailment** in the all-function institution: a segment equivalence at a
free type entails, in every model, the equivalence of any bodies that differ by plugging. -/
theorem congr_entails (P : Plug L) {C : Ctx} {τ : SegTy} (hτ : SegTy.Free L τ)
    (b b' : L.Code C) (K : P.Hole C) (i : C.Idx .func) :
    (allInst L W).Entails {Formula.atom (FnAtom.seg τ b b')}
      (Formula.atom (FnAtom.fn i (P.plug K b) (P.plug K b'))) := by
  intro h hΓ
  have hseg : SegEq (show Handler L W C from h) τ b b' := hΓ _ rfl
  have hexec : L.exec (show Handler L W C from h) (P.plug K b) =
      L.exec (show Handler L W C from h) (P.plug K b') :=
    P.congr _ K b b' (funext fun c => funext fun w => hseg c w (hτ c))
  intro a w _
  rw [hexec]

end Silmaril.Wasm.FnInst
