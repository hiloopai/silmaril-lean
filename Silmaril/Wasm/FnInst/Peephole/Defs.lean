module

public import Silmaril.Wasm.FnInst.Core.Defs

/-!
# Plugging segments into bodies

A `Plug L` gives one-hole contexts of a body language and plugging, with the congruence law:
segments with the same outcome from *every* configuration (under a handler) stay so when
plugged into any context. `Silmaril.Wasm.FnInst.Frag.Thms` proves it for the fragment by
induction on contexts.

Plugging is **not** a signature morphism of the hole institution: a context can identify
segments that differ (`Frag.plug_not_reflect`), so no model reduct makes the satisfaction
condition hold in the reflecting direction. It is a congruence, used one way by the peephole
theorem (`Silmaril.Wasm.FnInst.Peephole.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

/-- One-hole contexts of a body language, with congruence of plugging. -/
structure Plug (L : Lang) where
  /-- Contexts with one hole. -/
  Hole : Ctx → Type
  /-- Plugging a segment into a context. -/
  plug : ∀ {C : Ctx}, Hole C → L.Code C → L.Code C
  /-- Congruence: equal execution functions stay equal under plugging. -/
  congr : ∀ {C : Ctx} {W : Type} (h : Handler L W C) (K : Hole C) (b b' : L.Code C),
    L.exec h b = L.exec h b' → L.exec h (plug K b) = L.exec h (plug K b')

/-- Segment types that every configuration fits (no operand or local requirement). -/
def SegTy.Free (L : Lang) (τ : SegTy) : Prop := ∀ c, L.fits τ c

end Silmaril.Wasm.FnInst
