module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CtrlLabG

/-!
# The five unrestricted control leaves are false, in `simEnv10` and in `simEnv10T`

Round 3 proved the control leaves `br-zero`, `br-succ`, `return-label`, `return-frame` and
`trap-vals` only at a plain suffix (`Plain10`), and round 5 refuted the unrestricted `br-zero`
leaf in `simEnv10` (`not_labelBranchField10`). This module refutes all five, in `simEnv10` and in
the corrected `simEnv10T`, at every builtins. Each witness puts a `TRAP` where the rule's
`instr*` tail is, over the empty store and frame:

| leaf | V1 step | witness code |
| --- | --- | --- |
| `br-zero` | `labelBranch` | `LABEL_ 0 {ε} (BR 0; TRAP)` |
| `br-succ` | `labelBranchOuter` | `LABEL_ 0 {ε} (BR 1; TRAP)` |
| `return-label` | `labelReturn` | `LABEL_ 0 {ε} (RETURN; TRAP)` |
| `return-frame` | `frameReturn` | `FRAME_ 0 {f} (RETURN; TRAP)` |
| `trap-vals` | `trapTail` | `TRAP; TRAP` |

Both images of each step are IL-typed in `simEnv10` (kernel evaluation of the type checker), hence
in `simEnv10T` (`typed10T_of_typed10`), V1 steps, and the script is stuck in both environments
(`CtrlStuckG`, `CtrlLabG`, at `like10_simEnv10` and `like10_simEnv10T`). So each unrestricted
obligation (`…Field10`, stated with `FwdAt10`; `…Field10T`, stated with `FwdAt10T`) is false.
Round 3's restatements at `Plain10` code (`fwdAt10_labelBranchP`, `fwdAt10_labelBranchOuterP`,
`fwdAt10_labelReturnP`, `fwdAt10_frameReturnP`, `fwdAt10_trapTailP`) and their `simEnv10T` forms
's `FwdCtrl10T` are the documented fix; `Plain10` holds along every V1 run from an
invocation (`plain10_steps`, `plain10_invoke`).

Not refuted here: `trap-vals` with a non-empty value prefix (V1's `trapValues`). At
`CONST; TRAP; TRAP` the script is not stuck (`trap-vals` fires on `CONST; TRAP` inside
`Step/ctxt-instrs`), so a refutation would have to rule out the particular step to `TRAP`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression lowerLabel)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T sstepB10T_iff)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (typed10T_of_typed10)

set_option maxRecDepth 100000

variable {B : Builtins} {E : Env}

/-! ## Stuck codes, in every environment like `simEnv10` -/

/-- `z; BR k TRAP` is stuck. -/
theorem not_sstepG_brTrap (hL : Like10 B E) (k : Nat) (z w : Value) :
    ¬ SStep E (cfgV z [.case "BR" (pctV k), trapV10]) w :=
  not_sstepG_xTrap hL (by decide) (by decide) (by decide) (by decide) (by decide)
    (not_sstepG_one hL (by decide) (by decide) (by decide)) z w

/-- `z; RETURN TRAP` is stuck. -/
theorem not_sstepG_returnTrap (hL : Like10 B E) (z w : Value) :
    ¬ SStep E (cfgV z [caseNilV "RETURN", trapV10]) w :=
  not_sstepG_xTrap hL (by decide) (by decide) (by decide) (by decide) (by decide)
    (not_sstepG_one hL (by decide) (by decide) (by decide)) z w

/-- `z; LABEL_ 0 {ε} (BR l; TRAP)` is stuck. -/
theorem not_sstepG_labBr (hL : Like10 B E) (l : LabelIdx) (z w : Value) :
    ¬ SStep E (cfgV z [labX (.source (.br l))]) w :=
  not_sstepG_labX hL (a := .source (.br l)) (fun _ h => by simp [adminToV, instrToV] at h)
    (fun z w => not_sstepG_brTrap hL l.toNat z w) z w

/-- `z; LABEL_ 0 {ε} (RETURN; TRAP)` is stuck. -/
theorem not_sstepG_labReturn (hL : Like10 B E) (z w : Value) :
    ¬ SStep E (cfgV z [labX (.source .return_)]) w :=
  not_sstepG_labX hL (a := .source .return_)
    (fun _ h => by simp [adminToV, instrToV, caseNilV] at h)
    (not_sstepG_returnTrap hL) z w

/-- `z; FRAME_ 0 {fr} (RETURN; TRAP)` is stuck. -/
theorem not_sstepG_frmReturn (hL : Like10 B E) (fr : Frame) (z w : Value) :
    ¬ SStep E (cfgV z [frmX fr (.source .return_)]) w :=
  not_sstepG_frmX hL (a := .source .return_)
    (fun _ h => by simp [adminToV, instrToV, caseNilV] at h)
    (not_sstepG_returnTrap hL) z w

/-! ## From stuckness to a false forward obligation -/

variable {H : Type} (hn : H → String)

/-- A step whose source is stuck in `simEnv10`, between typed images, has no `FwdAt10`. -/
theorem not_fwdAt10_of_stuck {c c' : Config H} (hc : Typed10 (simEnv10 B) hn c)
    (hc' : Typed10 (simEnv10 B) hn c')
    (hs : ∀ z w, ¬ SStep (simEnv10 B) (cfgV z (adminsToV c.code)) w) : ¬ FwdAt10 B hn c c' := by
  intro F
  have h := (sstepB10_iff B).1 (F (typedV_state_of_typed10 hc) (typedV_state_of_typed10 hc')
    (typedV_code_of_typed10 hc) (typedV_code_of_typed10 hc'))
  exact hs _ _ h

/-- A step whose source is stuck in `simEnv10T`, between typed images, has no `FwdAt10T`. -/
theorem not_fwdAt10T_of_stuck {c c' : Config H} (hc : Typed10 (simEnv10T B) hn c)
    (hc' : Typed10 (simEnv10T B) hn c')
    (hs : ∀ z w, ¬ SStep (simEnv10T B) (cfgV z (adminsToV c.code)) w) :
    ¬ FwdAt10T B hn c c' := by
  intro F
  have h := (sstepB10T_iff B).1 (F (typedV_state_of_typed10T hc) (typedV_state_of_typed10T hc')
    (typedV_code_of_typed10T hc) (typedV_code_of_typed10T hc'))
  exact hs _ _ h

/-! ## The witnesses -/

/-- A configuration over the empty store and frame. -/
def cfgE10 (H : Type) (code : List Admin) : Config H := ⟨emptyStore10 H, emptyFrame10, code⟩

/-- `LABEL_ 0 {ε} (BR 1; TRAP)`. -/
def brSuccCode10 : List Admin := [.label 0 [] [.source (.br ⟨1⟩), .trap]]
/-- What V1 steps it to: `BR 0`. -/
def brSuccCode10' : List Admin := values [] ++ [.source (.br (lowerLabel ⟨1⟩))]
/-- `LABEL_ 0 {ε} (RETURN; TRAP)`. -/
def retLabCode10 : List Admin := [.label 0 [] [.source .return_, .trap]]
/-- What V1 steps it to: `RETURN`. -/
def retLabCode10' : List Admin := values [] ++ [.source .return_]
/-- `FRAME_ 0 {f} (RETURN; TRAP)`, `f` the empty frame. -/
def retFrmCode10 : List Admin := [.frame 0 emptyFrame10 [.source .return_, .trap]]
/-- `TRAP; TRAP`. -/
def trapTrapCode10 : List Admin := [.trap, .trap]

theorem step_brSucc10 {H : Type} (host : HostSemantics H) :
    Step host (cfgE10 H brSuccCode10) (cfgE10 H brSuccCode10') :=
  .pure _ _ (.labelBranchOuter 0 [] [] [.trap] ⟨1⟩ (by decide))

theorem step_retLab10 {H : Type} (host : HostSemantics H) :
    Step host (cfgE10 H retLabCode10) (cfgE10 H retLabCode10') :=
  .pure _ _ (.labelReturn 0 [] [] [.trap])

theorem step_retFrm10 {H : Type} (host : HostSemantics H) :
    Step host (cfgE10 H retFrmCode10) (cfgE10 H []) :=
  .pure _ _ (.frameReturn 0 emptyFrame10 [] [] [.trap] rfl)

theorem step_trapTrap10 {H : Type} (host : HostSemantics H) :
    Step host (cfgE10 H trapTrapCode10) (cfgE10 H [.trap]) :=
  .pure _ _ (.trapTail .trap [])

set_option maxHeartbeats 4000000 in
theorem typed10_brSucc : Typed10 (simEnv10 B) hn (cfgE10 H brSuccCode10) :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_brSucc' : Typed10 (simEnv10 B) hn (cfgE10 H brSuccCode10') :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_retLab : Typed10 (simEnv10 B) hn (cfgE10 H retLabCode10) :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_retLab' : Typed10 (simEnv10 B) hn (cfgE10 H retLabCode10') :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_retFrm : Typed10 (simEnv10 B) hn (cfgE10 H retFrmCode10) :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_empty : Typed10 (simEnv10 B) hn (cfgE10 H []) :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_trapTrap : Typed10 (simEnv10 B) hn (cfgE10 H trapTrapCode10) :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_trap : Typed10 (simEnv10 B) hn (cfgE10 H [.trap]) :=
  ⟨100, by with_unfolding_all rfl⟩

/-! ## The unrestricted obligations -/

/-- **The unrestricted `br-succ` obligation**: round 3's `fwdAt10_labelBranchOuter` for every
tail. -/
def LabelBranchOuterField10 (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) (vs : List Execution.Runtime.Value)
    (tail : List Admin) (l : LabelIdx), l.toNat ≠ 0 →
    FwdAt10 B hn ⟨s, f, [.label n cont (values vs ++ [.source (.br l)] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source (.br (lowerLabel l))]⟩

/-- **The unrestricted `return-label` obligation.** -/
def LabelReturnField10 (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) (vs : List Execution.Runtime.Value)
    (tail : List Admin),
    FwdAt10 B hn ⟨s, f, [.label n cont (values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source .return_]⟩

/-- **The unrestricted `return-frame` obligation.** -/
def FrameReturnField10 (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (fr : Frame) (extra vs : List Execution.Runtime.Value)
    (tail : List Admin), vs.length = n →
    FwdAt10 B hn ⟨s, f, [.frame n fr (values extra ++ values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs⟩

/-- **The unrestricted `trap-vals` obligation**, V1's `trapTail` form. -/
def TrapTailField10 (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (i : Admin) (tail : List Admin),
    FwdAt10 B hn ⟨s, f, .trap :: i :: tail⟩ ⟨s, f, [.trap]⟩

/-- `br-zero` in `simEnv10T`. -/
def LabelBranchField10T (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) (extra vs : List Execution.Runtime.Value)
    (tail : List Admin), vs.length = n →
    FwdAt10T B hn ⟨s, f, [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)]⟩
      ⟨s, f, values vs ++ expression cont⟩

/-- `br-succ` in `simEnv10T`. -/
def LabelBranchOuterField10T (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) (vs : List Execution.Runtime.Value)
    (tail : List Admin) (l : LabelIdx), l.toNat ≠ 0 →
    FwdAt10T B hn ⟨s, f, [.label n cont (values vs ++ [.source (.br l)] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source (.br (lowerLabel l))]⟩

/-- `return-label` in `simEnv10T`. -/
def LabelReturnField10T (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) (vs : List Execution.Runtime.Value)
    (tail : List Admin),
    FwdAt10T B hn ⟨s, f, [.label n cont (values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source .return_]⟩

/-- `return-frame` in `simEnv10T`. -/
def FrameReturnField10T (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (fr : Frame) (extra vs : List Execution.Runtime.Value)
    (tail : List Admin), vs.length = n →
    FwdAt10T B hn ⟨s, f, [.frame n fr (values extra ++ values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs⟩

/-- `trap-vals` (`trapTail`) in `simEnv10T`. -/
def TrapTailField10T (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (i : Admin) (tail : List Admin),
    FwdAt10T B hn ⟨s, f, .trap :: i :: tail⟩ ⟨s, f, [.trap]⟩

/-! ## The refutations in `simEnv10` -/

/-- **The unrestricted `br-succ` obligation is false**, at every builtins. -/
theorem not_labelBranchOuterField10 : ¬ LabelBranchOuterField10 hn B := fun F =>
  not_fwdAt10_of_stuck hn (typed10_brSucc hn) (typed10_brSucc' hn)
    (not_sstepG_labBr (like10_simEnv10 B) ⟨1⟩)
    (F (emptyStore10 H) emptyFrame10 0 [] [] [.trap] ⟨1⟩ (by decide))

/-- **The unrestricted `return-label` obligation is false**, at every builtins. -/
theorem not_labelReturnField10 : ¬ LabelReturnField10 hn B := fun F =>
  not_fwdAt10_of_stuck hn (typed10_retLab hn) (typed10_retLab' hn)
    (not_sstepG_labReturn (like10_simEnv10 B))
    (F (emptyStore10 H) emptyFrame10 0 [] [] [.trap])

/-- **The unrestricted `return-frame` obligation is false**, at every builtins. -/
theorem not_frameReturnField10 : ¬ FrameReturnField10 hn B := fun F =>
  not_fwdAt10_of_stuck hn (typed10_retFrm hn) (typed10_empty hn)
    (not_sstepG_frmReturn (like10_simEnv10 B) emptyFrame10)
    (F (emptyStore10 H) emptyFrame10 0 emptyFrame10 [] [] [.trap] rfl)

/-- **The unrestricted `trap-vals` obligation (`trapTail`) is false**, at every builtins. -/
theorem not_trapTailField10 : ¬ TrapTailField10 hn B := fun F =>
  not_fwdAt10_of_stuck hn (typed10_trapTrap hn) (typed10_trap hn)
    (not_sstepG_trapTrap (like10_simEnv10 B)) (F (emptyStore10 H) emptyFrame10 .trap [])

/-! ## The refutations in `simEnv10T` -/

/-- **The unrestricted `br-zero` obligation is false in `simEnv10T`**, at every builtins. -/
theorem not_labelBranchField10T : ¬ LabelBranchField10T hn B := fun F =>
  not_fwdAt10T_of_stuck hn (typed10T_of_typed10 (typed10_brTrap B hn))
    (typed10T_of_typed10 (typed10_brTrap' B hn))
    (not_sstepG_labBr (like10_simEnv10T B) ⟨0⟩)
    (F (emptyStore10 H) emptyFrame10 0 [] [] [] [.trap] rfl)

/-- **The unrestricted `br-succ` obligation is false in `simEnv10T`.** -/
theorem not_labelBranchOuterField10T : ¬ LabelBranchOuterField10T hn B := fun F =>
  not_fwdAt10T_of_stuck hn (typed10T_of_typed10 (typed10_brSucc hn))
    (typed10T_of_typed10 (typed10_brSucc' hn)) (not_sstepG_labBr (like10_simEnv10T B) ⟨1⟩)
    (F (emptyStore10 H) emptyFrame10 0 [] [] [.trap] ⟨1⟩ (by decide))

/-- **The unrestricted `return-label` obligation is false in `simEnv10T`.** -/
theorem not_labelReturnField10T : ¬ LabelReturnField10T hn B := fun F =>
  not_fwdAt10T_of_stuck hn (typed10T_of_typed10 (typed10_retLab hn))
    (typed10T_of_typed10 (typed10_retLab' hn)) (not_sstepG_labReturn (like10_simEnv10T B))
    (F (emptyStore10 H) emptyFrame10 0 [] [] [.trap])

/-- **The unrestricted `return-frame` obligation is false in `simEnv10T`.** -/
theorem not_frameReturnField10T : ¬ FrameReturnField10T hn B := fun F =>
  not_fwdAt10T_of_stuck hn (typed10T_of_typed10 (typed10_retFrm hn))
    (typed10T_of_typed10 (typed10_empty hn))
    (not_sstepG_frmReturn (like10_simEnv10T B) emptyFrame10)
    (F (emptyStore10 H) emptyFrame10 0 emptyFrame10 [] [] [.trap] rfl)

/-- **The unrestricted `trap-vals` obligation (`trapTail`) is false in `simEnv10T`.** -/
theorem not_trapTailField10T : ¬ TrapTailField10T hn B := fun F =>
  not_fwdAt10T_of_stuck hn (typed10T_of_typed10 (typed10_trapTrap hn))
    (typed10T_of_typed10 (typed10_trap hn)) (not_sstepG_trapTrap (like10_simEnv10T B))
    (F (emptyStore10 H) emptyFrame10 .trap [])

end Silmaril.Wasm.SpecTec.Sim10.Whole
