module

public import Silmaril.Wasm.Binaryen.InlUnwrap
public import Silmaril.Wasm.Execution.Core.Sim.CodeRel

@[expose] public section

/-! # The recursive unwrap relation contains its Core closure

These structural embeddings reconnect exact selected-step store transport to
`UL`, including related callees. They are relation laws, not execution laws.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim

variable {R : List Instr}

mutual
/-- The unwrap instruction relation is closed under the Core instruction closure. -/
theorem UI.of_core {i j : Instr} : InstrRel (UIL R) i j → UI R i j
  | .refl i => .flat i
  | .block _ h => .block (UIL.of_core h)
  | .loop _ h => .loop (UIL.of_core h)
  | .if_ _ h₁ h₂ => .if_ (UIL.of_core h₁) (UIL.of_core h₂)
  | .tryTable _ _ h => .tryTable (UIL.of_core h)
/-- Nested source-sequence closure introduces no new unwrap pairs. -/
theorem UIL.of_core {x y : List Instr} : InstrsRel (UIL R) x y → UIL R x y
  | .nil => .nil
  | .cons h t => .cons (UI.of_core h) (UIL.of_core t)
  | .base h => h
  | .append h t => (UIL.of_core h).append (UIL.of_core t)
end

mutual
/-- The runtime relation contains the Core closure, including changed callees. -/
theorem UA.of_core {a b : Admin} : AdminRel (UIL R) (UL R) a b → UA R a b
  | .refl a => .refl a
  | .plain h => .plain (UI.of_core h)
  | .label _ hc hb => .label (UIL.of_core hc) (UL.of_core hb)
  | .handler _ _ hb => .handler (UL.of_core hb)
  | .frame _ _ hb => .frame (UL.of_core hb)
/-- Sequence concatenation and related function entry remain inside `UL`. -/
theorem UL.of_core {x y : List Admin} : AdminsRel (UIL R) (UL R) x y → UL R x y
  | .nil => .nil
  | .cons h t => .cons (UA.of_core h) (UL.of_core t)
  | .base h => h
  | .src h => .of_UIL (UIL.of_core h)
  | .append h t => (UL.of_core h).append (UL.of_core t)
end

/-- Core's converse closure embeds in the converse runtime unwrap relation. -/
theorem UL.of_core_reverse {x y : List Admin}
    (related : AdminsRel (fun x y => UIL R y x) (fun x y => UL R y x) x y) :
    UL R y x := UL.of_core related.flip

end Silmaril.Wasm.Binaryen.Unwrap
