module

public import Silmaril.Compiler.Semantics.RTL.Defs
public import Silmaril.Machine.CompilerSemantics.RTLOfLir.Defs
public import Silmaril.Compiler.Semantics.CopyProp.Defs
public import Silmaril.Compiler.Category.RoundTripComp.Defs
@[expose] public section

/-!
# Mir ⇄ Lir ⇄ RTL ⇄ RTL.SSA: SSA optimizations of Mir with local lemmas only

`liftPass : Pass (lirLang ⟶ rtlLang)` lifts a closed Lir program of the register-only
fragment to RTL, one node per instruction (`RTL.Prog.ofLir`, sound by the lock-step
simulation of `RTLOfLir.lean` and determinism). With `lowerLir` it is a round trip
`lirRoundTrip : RoundTrip lirLang rtlLang`; composed with the SSA round trip
(`RoundTrip.trans`) it gives `lirSsa : RoundTrip lirLang ssaLang`.

Mir means the Lir semantics of its link (`Mir.beh`), so Mir reaches RTL.SSA through its link:
`mirOptimize cfg E` links, lifts to RTL, constructs SSA, runs **any** `E : EndoPass ssaLang`,
erases, and lowers to Lir. `mirOptimize_sound` is its end-to-end theorem at the link's
convention, for every `E`: a new SSA pass needs only its own refinement lemma
(`EndoPass.refines`) to be a verified Mir → Lir optimization. Mir itself has no lowering back
from RTL (Mir keeps symbols and data that RTL lacks), so the round trip is anchored at Lir,
the meaning of Mir.
-/

namespace Silmaril.Compile.Semantics

open Silmaril.Machine
open Silmaril.Compile.Category
open Silmaril.Compile.Mir (LirOutcome ubClose lirLang ubClose_mono ubClose_of_undefined)
open CategoryTheory

/-! ## Lifting Lir to RTL -/

/-- The RTL program of a closed Lir program. -/
def ofLirProg (q : Mir.LirProgram) : RtlProg :=
  ⟨.nat, RTL.Prog.ofLir q.prog, q.entry, q.args, q.mem⟩

/-- The lift, on the register-only fragment. -/
def ofLir? (q : Mir.LirProgram) : Option RtlProg :=
  if RTL.Prog.RegOnly q.prog then some (ofLirProg q) else none

theorem obsRtl_liftBehavior (b : Lir.Behavior) : obsRtl (RTL.liftBehavior b) = b.toOutcome := by
  cases b <;> rfl

/-- **Lifting refines**: an RTL behaviour of the lifted program is a Lir behaviour, unless the
Lir run gets stuck and allows every outcome. -/
theorem beh_ofLir_subset {q : Mir.LirProgram} (hp : RTL.Prog.RegOnly q.prog) :
    (ofLirProg q).beh ⊆ q.beh := by
  unfold RtlProg.beh Mir.LirProgram.beh ofLirProg
  simp only
  rw [RTL.ofLir_start hp]
  cases hs : q.prog.start q.entry q.args q.mem with
  | none => exact fun _ h => h
  | some s =>
    simp only [Option.map_some]
    by_cases hst : Lir.Behaves q.prog s .stuck
    · rw [ubClose_of_undefined (B := {o | (Lir.sem q.prog).Beh s o})
        (Lir.beh_iff_behaves (b := .stuck).mpr hst)]
      exact Set.subset_univ _
    · refine ubClose_mono ?_
      rintro o ⟨b, hb, rfl⟩
      rcases RTL.behaves_of_ofLir hp hb with h | ⟨b', hb', rfl⟩
      · exact absurd h hst
      · show (Lir.sem q.prog).Beh s (obsRtl (RTL.liftBehavior b'))
        rw [obsRtl_liftBehavior]
        exact Lir.beh_iff_behaves.mpr hb'

/-- Lir → RTL. -/
def liftConv : lirLang ⟶ rtlLang := ⟨id, Eq⟩

theorem liftConv_lowerConv : liftConv ≫ lowerConv = 𝟙 lirLang :=
  Convention.ext rfl Relation.eq_comp

/-- **Lifting Lir to RTL**, a pass at the identity of observations; it fails on programs with
stack slots. -/
def liftPass : Pass liftConv where
  run := ofLir?
  sound q q' h := by
    unfold ofLir? at h
    split at h
    · cases h
      exact (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, beh_ofLir_subset ‹_› ho, rfl⟩⟩
    · cases h

/-- Lir → RTL → Lir is a round trip. -/
def lirRoundTrip : RoundTrip lirLang rtlLang where
  lift := liftPass
  lower := lowerLir
  le_id := le_of_eq liftConv_lowerConv

/-- Lir → RTL → RTL.SSA → RTL → Lir is a round trip. -/
def lirSsa : RoundTrip lirLang ssaLang := lirRoundTrip.trans roundTrip

/-- An SSA optimization as an optimization of closed Lir programs (identity on failure). -/
def lirOptimize (E : EndoPass ssaLang) : EndoPass lirLang := lirSsa.endo E

/-! ## Copy propagation, a real SSA optimization -/

/-- Copy propagation of a closed RTL.SSA program. -/
def SsaProg.copyProp (q : SsaProg) : SsaProg :=
  ⟨q.ty, RTL.SSA.CopyProp.copyProp q.prog, q.entry, q.args, q.mem⟩

/-- Copy propagation preserves behaviours exactly, by its local lemma
`RTL.SSA.CopyProp.behaves_copyProp_iff`. -/
theorem SsaProg.beh_copyProp (q : SsaProg) : q.copyProp.beh = q.beh := by
  unfold SsaProg.beh SsaProg.copyProp
  simp only
  rw [RTL.SSA.CopyProp.start_copyProp]
  cases hs : q.prog.start q.entry q.args q.mem with
  | none => rfl
  | some s =>
    simp only
    congr 1
    ext o
    exact exists_congr fun b =>
      and_congr (RTL.SSA.CopyProp.behaves_copyProp_iff (RTL.SSA.CopyProp.Inv.start hs)) Iff.rfl

/-- **Copy propagation as an endo-pass** of the zoo's RTL.SSA. -/
def copyPropPass : EndoPass ssaLang :=
  ⟨SsaProg.copyProp, fun q => ⟨rfl, (SsaProg.beh_copyProp q).subset⟩⟩

/-- The SSA optimizer: copy propagation, then sequentialization (so that erasure accepts
every result). -/
def ssaOptimizer : EndoPass ssaLang := copyPropPass * sequentializePass

/-! ## Mir -/

/-- **An SSA optimization of Mir**: link, lift to RTL, construct SSA, run `E`, erase, lower
to Lir. -/
def mirOptimize (cfg : Mir.Config) (E : EndoPass ssaLang) :
    Pass ((Mir.linkCompiler cfg).conv ≫ 𝟙 lirLang) :=
  Pass.ofCompiler (Mir.linkCompiler cfg) ≫ₚ lirSsa.conj E

/-- **End-to-end validity of every SSA optimization of Mir.** Whatever the endo-pass `E` on
RTL.SSA does, linking, lifting into RTL.SSA, running `E`, erasing and lowering is a valid
compilation of Mir to Lir at the link's convention; nothing about `E` is used beyond its own
refinement lemma. -/
theorem mirOptimize_sound (cfg : Mir.Config) (E : EndoPass ssaLang) {us : Array Mir.Unit}
    {q : Mir.LirProgram} (h : (mirOptimize cfg E).run us = some q) :
    Valid (Mir.linkCompiler cfg).conv us q := by
  have := (mirOptimize cfg E).sound us q h
  rwa [Category.comp_id] at this

/-- The instance at the SSA optimizer: copy propagation, then sequentialization. -/
theorem mirOptimize_ssaOptimizer_sound (cfg : Mir.Config) {us : Array Mir.Unit}
    {q : Mir.LirProgram} (h : (mirOptimize cfg ssaOptimizer).run us = some q) :
    Valid (Mir.linkCompiler cfg).conv us q :=
  mirOptimize_sound cfg _ h

end Silmaril.Compile.Semantics
