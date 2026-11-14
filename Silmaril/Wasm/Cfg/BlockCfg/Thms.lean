module

public import Silmaril.Wasm.Cfg.BlockCfg.Defs
public import Silmaril.Wasm.Cfg.BlockTree.Thms
public import Silmaril.Wasm.Cfg.Examples.Defs
import Silmaril.Proofs.Wasm.Cfg.BlockCfg

@[expose] public section

/-!
# The basic-block CFG of a function body: theorems

The one-pass builder `blockCfg` realizes the declarative edge relation `Edge`. It lists each
block that `lookup` names exactly once, with the successors `succOf` gives it.

These are statements about the syntactic graph: they say the builder computes `Edge`, not that
`Edge` describes execution (see the scope note in `Defs`).
-/

namespace Silmaril.Wasm.Cfg

/-- **The builder is the declarative CFG**: it pairs every block with its `succOf`. -/
theorem blockCfg_eq (body : Expr) :
    blockCfg body = (blocks body).map fun x => (x.1, succOf body x.1 x.2) :=
  Proofs.BlockCfg.blockCfg_eq body

/-- The builder lists block `b` with successors `ts` exactly when `lookup` names `b` and `ts` is
its `succOf`. -/
theorem mem_blockCfg (body : Expr) (b : BlockId) (ts : List Target) :
    (b, ts) ∈ blockCfg body ↔ ∃ s, lookup body b = some s ∧ ts = succOf body b s := by
  simp only [blockCfg_eq, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨b', s⟩, h, rfl, rfl⟩; exact ⟨s, (mem_blocks body b' s).1 h, rfl⟩
  · rintro ⟨s, h, rfl⟩; exact ⟨(b, s), (mem_blocks body b s).2 h, rfl, rfl⟩

/-- **The builder realizes `Edge`.** -/
theorem edge_iff (body : Expr) (b : BlockId) (t : Target) :
    Edge body b t ↔ ∃ ts, (b, ts) ∈ blockCfg body ∧ t ∈ ts := by
  simp only [Edge, mem_blockCfg]
  constructor
  · rintro ⟨s, h, ht⟩; exact ⟨_, ⟨s, h, rfl⟩, ht⟩
  · rintro ⟨_, ⟨s, h, rfl⟩, ht⟩; exact ⟨s, h, ht⟩

/-- Every block `lookup` names has exactly one successor list in the builder's output. -/
theorem existsUnique_succ (body : Expr) (b : BlockId) (h : (lookup body b).isSome) :
    ∃! ts, (b, ts) ∈ blockCfg body := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  refine ⟨succOf body b s, (mem_blockCfg body b _).2 ⟨s, hs, rfl⟩, fun ts hts => ?_⟩
  obtain ⟨s', hs', rfl⟩ := (mem_blockCfg body b ts).1 hts
  rw [hs] at hs'; cases hs'; rfl

/-- The builder lists each block identity once. -/
theorem blockCfg_ids_nodup (body : Expr) : ((blockCfg body).map (·.1)).Nodup := by
  rw [blockCfg_eq, List.map_map]
  exact blocks_ids_nodup body

/-- The effect edges are those of the blocks `blocks` lists. -/
theorem effectEdge_iff (body : Expr) (b : BlockId) (t : Target) :
    EffectEdge body b t ↔ ∃ s, (b, s) ∈ blocks body ∧ t ∈ effectSucc body b s := by
  simp only [EffectEdge, mem_blocks]

/-- `EffectEdge` as a Boolean check. -/
theorem effectEdge_iff_any (body : Expr) (b : BlockId) (t : Target) :
    EffectEdge body b t ↔ ((lookup body b).any fun s => (effectSucc body b s).contains t) = true := by
  unfold EffectEdge
  cases lookup body b <;> simp

/-! ## Examples, checked by the kernel

`sum` (`Verified.prog` function 3): the inner loop's first block branches out of the enclosing
`block` (`br_if 1`, to the body's final block) or falls through; the second branches back to the
loop head (`br 0`). The `br_table` of `dispatch` has an edge to each of its three targets. -/

theorem sum_blockCfg : blockCfg Examples.sum =
    [(⟨[], 0⟩, [.block ⟨[(0, 0)], 0⟩]),
     (⟨[(0, 0)], 0⟩, [.block ⟨[(0, 0), (0, 0)], 0⟩]),
     (⟨[(0, 0), (0, 0)], 0⟩, [.block ⟨[], 1⟩, .block ⟨[(0, 0), (0, 0)], 1⟩]),
     (⟨[(0, 0), (0, 0)], 1⟩, [.block ⟨[(0, 0), (0, 0)], 0⟩]),
     (⟨[], 1⟩, [.exit])] := by decide +kernel

theorem dispatch_br_table_edges :
    Edge Examples.dispatch ⟨[(0, 0), (0, 0), (0, 0)], 0⟩ (.block ⟨[(0, 0), (0, 0)], 1⟩) ∧
    Edge Examples.dispatch ⟨[(0, 0), (0, 0), (0, 0)], 0⟩ (.block ⟨[(0, 0)], 1⟩) ∧
    Edge Examples.dispatch ⟨[(0, 0), (0, 0), (0, 0)], 0⟩ (.block ⟨[], 1⟩) := by
  have h : (⟨[(0, 0), (0, 0), (0, 0)], 0⟩,
      [.block ⟨[(0, 0), (0, 0)], 1⟩, .block ⟨[(0, 0)], 1⟩, .block ⟨[], 1⟩]) ∈
        blockCfg Examples.dispatch := by decide +kernel
  simp only [edge_iff]
  exact ⟨⟨_, h, by simp⟩, ⟨_, h, by simp⟩, ⟨_, h, by simp⟩⟩

/-- `guarded`: the block before the `if` inside the `try_table` body divides and calls, so it is
marked `mayTrap`, `call` and `unresolvedHandler` and has effect edges to `trap` and `raise`;
the `throw` block is marked `unresolvedHandler`. The final block's load is marked `mayTrap`. -/
theorem guarded_effects :
    (blocks Examples.guarded).map (fun x => (x.1, blockEffects Examples.guarded x.1 x.2)) =
      [(⟨[], 0⟩, []), (⟨[(0, 0)], 0⟩, []),
       (⟨[(0, 0), (0, 0)], 0⟩, [.mayTrap, .call, .unresolvedHandler]),
       (⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [.unresolvedHandler]),
       (⟨[], 1⟩, [.mayTrap])] := by decide +kernel

theorem guarded_effect_edges :
    EffectEdge Examples.guarded ⟨[(0, 0), (0, 0)], 0⟩ .trap ∧
      EffectEdge Examples.guarded ⟨[(0, 0), (0, 0)], 0⟩ .raise := by
  simp only [effectEdge_iff_any]
  decide +kernel

end Silmaril.Wasm.Cfg
