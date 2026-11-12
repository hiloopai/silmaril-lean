module

public import Silmaril.Wasm.FnInst.IR.Lang.Thms
public import Silmaril.Wasm.SSA.Fragment.Defs

/-!
# Two signature frames for the body institutions

* `holeFrame`: the minimal signatures. A signature is a hole type and nothing else; the only
  morphisms are identities; contexts are trivial. A sentence here is about a function body with
  nothing around it.
* `modFrame`: a focus function of hole type `h` in a module with `n` other functions whose
  bodies may be unspecified (`Ctx = Fin n → Option FragFunc`, `none` = unknown body).
  Morphisms `(h, n) ⟶ (h, n')` for `n ≤ n'` embed the module as a prefix of a bigger one; the
  reduct forgets the added functions. `Ctx.Info` orders contexts by information (more bodies
  specified).

`modFrame.fromMinimal h n : (h, 0) ⟶ (h, n)` is the embedding of the minimal signature
(no other functions) into every module signature with the same focus type, so by
`Lang.valid_transfer` a sentence valid at `(h, 0)` is valid in every such module
(`valid_in_every_module`). These frames are local to the `ir` track; the `core` track's
signature category plugs in through `Frame` in the same way.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open CategoryTheory
open Silmaril.Inst
open Silmaril.Wasm.SSA (FragFunc)

/-- The minimal frame: signatures are hole types, morphisms are equalities. -/
def holeFrame : Frame (Disc Hole) where
  hole h := h
  hole_hom σ := σ.down
  Ctx _ := Unit
  red _ c := c
  red_id _ _ := rfl
  red_comp _ _ _ := rfl

/-- A focus of hole type `hole` among `n` other functions. -/
structure ModSig where
  hole : Hole
  n : Nat

instance ModSig.category : Category.{0} ModSig where
  Hom S S' := PLift (S.hole = S'.hole ∧ S.n ≤ S'.n)
  id S := ⟨rfl, Nat.le_refl _⟩
  comp f g := ⟨f.down.1.trans g.down.1, Nat.le_trans f.down.2 g.down.2⟩

/-- Contexts of a module signature: the bodies of the other functions, each possibly unknown. -/
abbrev ModSig.Ctx (S : ModSig) : Type := Fin S.n → Option FragFunc

/-- `c'` knows at least what `c` knows. -/
def ModSig.Info {S : ModSig} (c c' : S.Ctx) : Prop := ∀ i f, c i = some f → c' i = some f

/-- The module frame. -/
def modFrame : Frame ModSig where
  hole S := S.hole
  hole_hom σ := σ.down.1
  Ctx S := S.Ctx
  red σ c i := c (Fin.castLE σ.down.2 i)
  red_id _ _ := rfl
  red_comp _ _ _ := rfl

/-- The embedding of the minimal module signature into any module signature. -/
def ModSig.fromMinimal (h : Hole) (n : Nat) : (⟨h, 0⟩ : ModSig) ⟶ ⟨h, n⟩ :=
  ⟨rfl, Nat.zero_le n⟩

/-- **A sentence proved with no other functions around holds in every module** (with the
same focus type), whatever the other bodies are. -/
theorem valid_in_every_module (L : Lang) (h : Hole) (n : Nat)
    {φ : (L.inst modFrame).Sen ⟨h, 0⟩} (hv : (L.inst modFrame).Valid φ) :
    (L.inst modFrame).Valid ((L.inst modFrame).map (ModSig.fromMinimal h n) φ) :=
  L.valid_transfer modFrame _ hv

/-- Satisfaction is monotone along `Info`: specifying more of the other bodies keeps every
satisfied sentence satisfied (and, for these call-free languages, also reflects it). -/
theorem sat_info_mono (L : Lang) {S : ModSig} {c c' : S.Ctx} (hi : ModSig.Info c c')
    (e : L.Env) (φ : (L.inst modFrame).Sen S) :
    ((c, e) : (L.inst modFrame).Mod S) ⊨[L.inst modFrame] φ ↔
      ((c', e) : (L.inst modFrame).Mod S) ⊨[L.inst modFrame] φ :=
  L.sat_mono modFrame ModSig.Info hi e φ

end Silmaril.Wasm.FnInst.IR
