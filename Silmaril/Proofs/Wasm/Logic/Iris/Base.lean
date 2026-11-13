module

public import Silmaril.Proofs.Wasm.Logic.Iris.Heap
public import Silmaril.Proofs.Wasm.Logic.Iris.Lifting

/-!
# The Iris logic of Wasm Core 3.0: head rules with owned cells

`wp_head_read` and `wp_head_change` specialise the head rule `wp_head` to an
instruction whose head steps are determined by owned cells `ps`: a read keeps the
store, the frame and the cells; a change updates the owned cells to `ps'` and
allocates the fresh cells `qs s` (which may depend on the store, e.g. the address
of a new structure). Every instruction rule is an instance of one of them, or of
`wp_head` directly for nondeterministic instructions (`memory.grow`).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H} {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- The head rule with owned cells: the cells give some head step, and every head
step is handled with the cells and the state interpretation. -/
theorem wp_head_cells {E : CoPset} {W : List Val} {i : Instr} {rest : List Admin}
    {Φ : Res H → IProp GF} (ps : List (ILoc × ICell)) (hi : Hoare.Inert i)
    (hp : ∀ s f, Cells ps s f → ∃ (vs args : List Val) (c₀ : Config H), W = vs ++ args ∧
      SingleThreaded.Det.Head P s f args (.plain i) c₀) :
    ownCells ps ∗ ▷ (∀ (s : Store H) (f : Frame) (vs args : List Val) (c₀ : Config H),
      ⌜Cells ps s f ∧ W = vs ++ args ∧ SingleThreaded.Det.Head P s f args (.plain i) c₀⌝ -∗
      wasmInterp (s, f) -∗ ownCells ps ={E}=∗
      wasmInterp (c₀.store, c₀.frame) ∗
      WP (IExpr.run (vals vs ++ c₀.code ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals W ++ .plain i :: rest) : IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hc, H⟩
  iapply wp_head hi
  iintro %s %f Hσ
  ihave %hc : ⌜Cells ps s f⌝ $$ [Hσ Hc]
  · icases interp_lookup_cells $$ [$Hσ $Hc] with >%h
    ipureintro
    exact h
  imodintro
  isplitr
  · ipureintro
    exact hp s f hc
  inext
  iintro %vs %args %c₀ %hh
  iapply H $$ %s %f %vs %args %c₀ %⟨hc, hh⟩ Hσ Hc

/-- **Reads.** Every head step keeps the store and the frame and continues with
`code'`. -/
theorem wp_head_read {E : CoPset} {W : List Val} {i : Instr} {rest code' : List Admin}
    {Φ : Res H → IProp GF} (ps : List (ILoc × ICell)) (hi : Hoare.Inert i)
    (hp : ∀ s f, Cells ps s f → ∃ (vs args : List Val) (c₀ : Config H), W = vs ++ args ∧
      SingleThreaded.Det.Head P s f args (.plain i) c₀)
    (hinv : ∀ s f vs args (c₀ : Config H), Cells ps s f → W = vs ++ args →
      SingleThreaded.Det.Head P s f args (.plain i) c₀ →
      c₀.store = s ∧ c₀.frame = f ∧ vals vs ++ c₀.code ++ rest = code') :
    ownCells ps ∗ ▷ (ownCells ps -∗ WP (IExpr.run code' : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals W ++ .plain i :: rest) : IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hc, H⟩
  iapply wp_head_cells ps hi hp
  iframe Hc
  inext
  iintro %s %f %vs %args %c₀ %⟨hc, hW, hh⟩ Hσ Hc
  obtain ⟨hs, hf, hcode⟩ : c₀.store = s ∧ c₀.frame = f ∧ vals vs ++ c₀.code ++ rest = code' :=
    hinv s f vs args c₀ hc hW hh
  rw [hs, hf, hcode]
  imodintro
  iframe Hσ
  iapply H $$ Hc

/-- **Changes.** Every head step changes the store and the frame along a `Change`
of the owned cells `ps` to `ps'` that allocates `qs s`, and continues with
`code' s`. -/
theorem wp_head_change {E : CoPset} {W : List Val} {i : Instr} {rest : List Admin}
    {Φ : Res H → IProp GF} (ps ps' : List (ILoc × ICell)) (qs : Store H → List (ILoc × ICell))
    (code' : Store H → List Admin) (hi : Hoare.Inert i)
    (hp : ∀ s f, Cells ps s f → ∃ (vs args : List Val) (c₀ : Config H), W = vs ++ args ∧
      SingleThreaded.Det.Head P s f args (.plain i) c₀)
    (hinv : ∀ s f vs args (c₀ : Config H), Cells ps s f → W = vs ++ args →
      SingleThreaded.Det.Head P s f args (.plain i) c₀ →
      vals vs ++ c₀.code ++ rest = code' s ∧ Change s f c₀.store c₀.frame ps ps' (qs s)) :
    ownCells ps ∗ ▷ (∀ s, ownCells ps' -∗ ownCells (qs s) -∗
      WP (IExpr.run (code' s) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals W ++ .plain i :: rest) : IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hc, H⟩
  iapply wp_head_cells ps hi hp
  iframe Hc
  inext
  iintro %s %f %vs %args %c₀ %⟨hc, hW, hh⟩ Hσ Hc
  obtain ⟨hcode, hch⟩ : vals vs ++ c₀.code ++ rest = code' s ∧
      Change s f c₀.store c₀.frame ps ps' (qs s) := hinv s f vs args c₀ hc hW hh
  rw [hcode]
  imod interp_change hch.fst hch.nodup hch.fresh hch.new hch.old $$ [$Hσ $Hc] with ⟨Hσ, Hc, Hq⟩
  imodintro
  iframe Hσ
  iapply H $$ %s Hc Hq

end Silmaril.Wasm.Logic.IrisWasm
