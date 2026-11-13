module

public import Silmaril.Wasm.Jco.Thin.Canon.Thms
public import Silmaril.Wasm.Jco.Example.Thms

/-!
# Thin wrappers over the canonical ABI: the litmus instance

* `recognizeThin_exMeta`: the litmus world (`add`, `echo`) is not recognized.
  `echo` returns a string through a C out-pointer, so an adaptor is needed.
* `addMeta` is the world with `add` only. It is memory-free and recognized
  (`recognizeThin_addMeta`).
* `addThin_agrees`: its thin wrapper behaves as `wrap addMeta` on the litmus
  instance, on every export.
* `add_thin`: export `add` of the thin wrapper returns `a + b` from every
  state, with no other outcome.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Example

open Silmaril.Wasm.Component (Flat ValTy Val)

theorem recognizeThin_exMeta : recognizeThin exMeta = none := rfl

/-- The world with `add` only. -/
def addMeta : Meta where
  world := [⟨"add", [.val .u32, .val .u32], some (.val .u32)⟩]

theorem addMeta_memFree : addMeta.memFree = true := rfl

theorem recognizeThin_addMeta : recognizeThin addMeta = some (thinComp addMeta "cabi_realloc") :=
  rfl

theorem addConforms : addMeta.Conforms exInst where
  alloc := alloc_returns
  outPtr := by
    intro s hs hm _
    simp only [addMeta, List.mem_singleton] at hs
    subst hs
    simp [inMem] at hm

/-- The thin wrapper of `add` and the monadic construction agree. -/
theorem addThin_agrees :
    (thinComp addMeta "cabi_realloc").callExport exInst = (wrap addMeta).callExport exInst :=
  recognizeThin_agrees_memFree exInst addMeta recognizeThin_addMeta addMeta_memFree addConforms

theorem add_thin (a b : BitVec 32) :
    (thinComp addMeta "cabi_realloc").callExport exInst "add" [.val (.u32 a), .val (.u32 b)] =
      pure (some (.val (.u32 (a + b)))) := by
  have hadd : exAdd [Flat.i32 a, Flat.i32 b] = pure [Flat.i32 (a + b)] := rfl
  rw [thinComp_callExport, canonSpec_eq_spec_memFree exInst addMeta _ addMeta_memFree]
  simp [Meta.spec, addMeta, Meta.specCall, Meta.specParams, Meta.specParam, ValTy.check,
    ValTy.lower, inMem, exCall_add, hadd, liftResult, ValTy.lift]

end Silmaril.Wasm.Jco.Example
