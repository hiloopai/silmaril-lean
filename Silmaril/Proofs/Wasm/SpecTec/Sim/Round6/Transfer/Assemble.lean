module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Transfer.Inst
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Transfer.Dead
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Thms

/-!
# Round 6: the transfer lemma at the backend reading

**Away from cast redexes, the backend reading of SpecTec's `Step` is the declarative one**, at
the image of every Core configuration, for every choice of primitives and every encoding
(`sstepB_iff_of_not_castRedex`). By recursion on the size of the code, rule by rule of `Step`:

* rules 0 and 6–35: `firesB_step_iff` (they consult only `Step_pure` and
  `Expand`, on which the readings agree everywhere);
* rule 1 (`read`): its premise is `Step_read` at the same left-hand side, where the readings
  agree (`sReadB_iff_noCast`: every cast rule is dead there, every other rule plain);
* rules 2–5 (`ctxt-instrs`, `ctxt-label`, `ctxt-handler`, `ctxt-frame`): their premise is `Step`
  at a configuration with smaller code and no cast redex (`SubInst`), where the readings agree by
  the recursion (`firesB_iff_swap`).

So `Round6.Target.Transfer backend B hn` holds outright (`transfer_backend`), for every `B` and
`hn`: none of its hypotheses (`ConfigOk`, `BoundedSel`, `SimRel`) is needed beyond the absence of
a cast redex. `Round6.Task.wholeStepValidR backend` is thereby reduced to the cast leaf alone
(`wholeStepValidR_backend_of_casts`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Reading
open Bwd (codeSize)
open Target (CastRedex)

variable {H : Type}

/-- The premises after `ctxt-instrs`' leading one: its side condition. -/
theorem tailFree_single {pr : Prem} (h : Reading.premRels pr = [] ∧ Reading.noElsePr pr = true) :
    TailFree [pr] := fun _ hp => (List.mem_singleton.1 hp) ▸ h

/-- No premise after the leading one. -/
theorem tailFree_nil : TailFree [] := fun _ hp => absurd hp List.not_mem_nil

/-- A `SubInst` premise instance, read by the recursion. -/
theorem sub_iff {B : Builtins} {hn : H → String} {c : Config H} (hc : ¬ CastRedex c.code)
    (ih : ∀ (c' : Config H) (w : Value), codeSize c'.code < codeSize c.code →
      ¬ CastRedex c'.code →
        (SStepB (simEnv B) (configV hn c') w ↔ SStep (simEnv B) (configV hn c') w))
    {w : Value} (h : SubInst hn c w) :
    DDerivesB (simEnv B) (otherwiseB (simEnv B)) "Step" "%~>%" [] w ↔
      DDerives (simEnv B) (otherwise (simEnv B)) "Step" "%~>%" [] w := by
  obtain ⟨c', u, rfl, hlt, hcc⟩ := h
  exact ih c' u hlt (hcc hc)

/-- `read`'s premise instance, at the image of a configuration without a cast redex. -/
theorem read_inst_iff {B : Builtins} {hn : H → String} {c : Config H} (hc : ¬ CastRedex c.code)
    {D : Interp} {els : Prop} {w w' : Value}
    (hi : Inst (simEnv B) D els Equiv.ExecStepRules.readRule (.tuple [configV hn c, w]) w') :
    DDerivesB (simEnv B) (otherwiseB (simEnv B)) "Step_read" "%~>%" [] w' ↔
      DDerives (simEnv B) (otherwise (simEnv B)) "Step_read" "%~>%" [] w' := by
  obtain ⟨u, hu⟩ := inst_read hi
  rw [hu]
  exact sReadB_iff_noCast hc

/-- **One rule of `Step` at the image of a configuration without a cast redex**, given the
transfer at smaller code. -/
theorem firesStep_iff_noCast {B : Builtins} {hn : H → String} {c : Config H}
    (hc : ¬ CastRedex c.code)
    (ih : ∀ (c' : Config H) (w : Value), codeSize c'.code < codeSize c.code →
      ¬ CastRedex c'.code →
        (SStepB (simEnv B) (configV hn c') w ↔ SStep (simEnv B) (configV hn c') w))
    (i : Nat) {w : Value} :
    FiresB (simEnv B) "Step" i (.tuple [configV hn c, w]) ↔
      Fires (simEnv B) "Step" i (.tuple [configV hn c, w]) := by
  have R : Equiv.ExecStepRules.HasStepRules (simEnv B) := hasStepRules_simEnv B
  have SD : Bwd.StructDecode (simEnv B) := Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv B)
  match i with
  | 0 => exact firesB_step_iff B (.inl rfl)
  | 1 => exact firesB_iff_swap R.read rfl tailFree_nil (fun _ hi => read_inst_iff hc hi)
  | 2 =>
    exact firesB_iff_swap R.ctxtInstrs rfl (tailFree_single ⟨rfl, rfl⟩)
      (fun _ hi => sub_iff hc ih (inst_ctxtInstrs SD hi))
  | 3 =>
    exact firesB_iff_swap R.ctxtLabel rfl tailFree_nil
      (fun _ hi => sub_iff hc ih (inst_ctxtLabel SD hi))
  | 4 =>
    exact firesB_iff_swap R.ctxtHandler rfl tailFree_nil
      (fun _ hi => sub_iff hc ih (inst_ctxtHandler SD hi))
  | 5 =>
    exact firesB_iff_swap R.ctxtFrame rfl tailFree_nil
      (fun _ hi => sub_iff hc ih (inst_ctxtFrame SD hi))
  | k + 6 => exact firesB_step_iff B (.inr (Nat.le_add_left 6 k))

/-- The recursion on the size of the code. -/
theorem sstepB_iff_lt (B : Builtins) (hn : H → String) :
    ∀ (n : Nat) (c : Config H) (w : Value), codeSize c.code < n → ¬ CastRedex c.code →
      (SStepB (simEnv B) (configV hn c) w ↔ SStep (simEnv B) (configV hn c) w)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, c, w, hlt, hc => by
    obtain ⟨t, rules, hrel⟩ := Bwd.findRel_of_ruleAt (hasStepRules_simEnv B).pure
    have ih : ∀ (c' : Config H) (w' : Value), codeSize c'.code < codeSize c.code →
        ¬ CastRedex c'.code →
          (SStepB (simEnv B) (configV hn c') w' ↔ SStep (simEnv B) (configV hn c') w') :=
      fun c' w' h' hc' => sstepB_iff_lt B hn n c' w' (Nat.lt_of_lt_of_le h' (Nat.le_of_lt_succ hlt)) hc'
    have hB : SStepB (simEnv B) (configV hn c) w ↔
        ∃ i, FiresB (simEnv B) "Step" i (.tuple [configV hn c, w]) := dderivesB_iff_firesB hrel
    have hD : SStep (simEnv B) (configV hn c) w ↔
        ∃ i, Fires (simEnv B) "Step" i (.tuple [configV hn c, w]) := dderives_iff_fires hrel
    exact hB.trans ((exists_congr fun i => firesStep_iff_noCast hc ih i).trans hD.symm)

/-- **The backend reading is the declarative one away from cast redexes**: at the image of a
Core configuration whose redex is not a cast, `SStepB` and `SStep` have the same successors, for
every `B` and every encoding. -/
theorem sstepB_iff_of_not_castRedex (B : Builtins) (hn : H → String) {c : Config H}
    (hc : ¬ CastRedex c.code) (w : Value) :
    SStepB (simEnv B) (configV hn c) w ↔ SStep (simEnv B) (configV hn c) w :=
  sstepB_iff_lt B hn _ c w (Nat.lt_succ_self _) hc

/-- **The transfer lemma at the backend reading**, for every `B` and every encoding. -/
theorem transfer_backend (B : Builtins) (hn : H → String) : Target.Transfer Int.backend B hn where
  fwd _ _ _ w _ _ _ hd hs := (sstepB_iff_of_not_castRedex B hn hd w).2 hs
  bwd _ _ _ w _ _ _ hd hs := (sstepB_iff_of_not_castRedex B hn hd w).1 hs

/-- **The transfer lemma at the backend reading, at the concrete builtins**: the instance the
round-6 target asks for (`Target.OpenR.transfer`). It needs none of the hypotheses an injective
encoding, a finite `HostOk` host or `Profile.spec` would provide. -/
theorem transfer_backend_BI (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Target.Transfer Int.backend (Round4Int.BI P hn host) hn :=
  transfer_backend _ hn

/-- **`Round6.Task.wholeStepValidR backend` from the cast leaf alone**: the transfer half of
`Target.OpenR backend` is `transfer_backend_BI`. -/
theorem wholeStepValidR_backend_of_casts
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          Target.Casts Int.backend (Round4Int.BI (Profile.spec nd r) hn host) hn
            (Profile.spec nd r) host) :
    Round6.Task.wholeStepValidR Int.backend :=
  Int.wholeStepValidR_backend_of_open fun H hn hinj host hf hok nd r =>
    ⟨transfer_backend_BI hn _ host, h H hn hinj host hf hok nd r⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Transfer
