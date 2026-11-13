module

public import Silmaril.Compiler.C.Sem.Targets.Defs
public import Init.Internal.Order.While
public import Init.Data.Range.Lemmas

@[expose] public section

/-!
# Counterexamples to the unrestricted Mir interpreter adequacy targets

The linked image need not fit in `Config.memSize`. `Mir.initMem` retains its bytes
outside the memory bound, whereas `Interp.Mem.ofImage` discards them. Outcomes
observe the entire memory function, including those inaccessible bytes. Even an
immediate return or trap therefore disproves the frozen unrestricted targets.

The image below is one byte at address 4095, and the memory has size zero. Choosing
the last byte of a page keeps the link's aligned image to a single byte.
-/

namespace Silmaril.Compile.Mir.InterpCounterexample

open Silmaril.Machine

attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'

def cfg : Config := ⟨⟨4095, 0⟩, 0⟩

def units (t : Lir.Term Nat) : Array Unit :=
  #[{ funcs := #[⟨"main", [], 0, #[⟨#[], t⟩], true, false⟩],
      data := #[⟨"byte", 1, 1, ⟨#[1]⟩, [], true, false, false⟩] }]

def linked (t : Lir.Term Nat) : Linked := {
  prog := ⟨[⟨[], 0, [⟨[], t⟩]⟩]⟩
  funcs := ({} : Std.HashMap Symbol Nat).insert "main" 0
  data := (({} : Std.HashMap Symbol Nat).insert "byte" 4095).insert dataEndSymbol 4096
  dataBase := 4095
  dataEnd := 4096
  image := ⟨#[1]⟩
}

theorem link_eq (t : Lir.Term Nat) : link cfg.layout (units t) = .ok (linked t) := by
  cbv
  change Except.ok { linked t with
    funcs := ({} : Std.HashMap Symbol Nat).insert "main" ({} : Std.HashMap Symbol Nat).size } = _
  rw [Std.HashMap.size_empty]
  rfl

def mem : Interp.Mem := ⟨0, #[]⟩

theorem initMem_ne (t : Lir.Term Nat) : mem.toLir ≠ initMem cfg (linked t) := by
  intro h
  have hb := congrArg (fun m : Lir.Memory => m.bytes 4095) h
  change (0 : BitVec 8) = 1 at hb
  exact (by decide : (0 : BitVec 8) ≠ 1) hb

theorem run_returned : run cfg 1 (units (.ret [])) = .ok (.returned [] mem) := by
  rw [run, link_eq]
  cbv

theorem run_trapped : run cfg 1 (units .trap) = .ok (.trapped mem) := by
  rw [run, link_eq]
  cbv

private def state (t : Lir.Term Nat) : Lir.State Nat :=
  ⟨⟨0, 0, 0⟩, .empty, [], initMem cfg (linked t)⟩

private theorem beh_returned (o : LirOutcome) (h : o ∈ beh cfg (units (.ret []))) :
    o = .returned ([], initMem cfg (linked (.ret []))) := by
  have hf : (Lir.sem (linked (.ret [])).prog).Beh (state (.ret []))
      (.returned ([], initMem cfg (linked (.ret [])))) := by
    exact Behaviour.Semantics.Beh.of_final rfl (by intro h; cases h)
  rw [beh_eq_link cfg _ _ (link_eq _)] at h
  change (Lir.sem (linked (.ret [])).prog).Beh (state (.ret [])) o ∨
    (Lir.sem (linked (.ret [])).prog).Beh (state (.ret [])) .undefined at h
  rcases h with h | h
  · exact Behaviour.Semantics.Beh.unique (Lir.sem_deterministic _) h hf
  · have bad := Behaviour.Semantics.Beh.unique (Lir.sem_deterministic _) h hf
    cases bad

private theorem beh_trapped (o : LirOutcome) (h : o ∈ beh cfg (units .trap)) :
    o = .trapped (initMem cfg (linked .trap)) := by
  have hf : (Lir.sem (linked .trap).prog).Beh (state .trap)
      (.trapped (initMem cfg (linked .trap))) := by
    exact Behaviour.Semantics.Beh.of_final rfl (by intro h; cases h)
  rw [beh_eq_link cfg _ _ (link_eq _)] at h
  change (Lir.sem (linked .trap).prog).Beh (state .trap) o ∨
    (Lir.sem (linked .trap).prog).Beh (state .trap) .undefined at h
  rcases h with h | h
  · exact Behaviour.Semantics.Beh.unique (Lir.sem_deterministic _) h hf
  · have bad := Behaviour.Semantics.Beh.unique (Lir.sem_deterministic _) h hf
    cases bad

/-- The frozen return adequacy target is false without a memory-image condition. -/
theorem not_mir_run_returned : ¬ Targets.mir_run_returned := by
  intro h
  have he := beh_returned _ (h cfg 1 (units (.ret [])) [] mem run_returned)
  have hm : mem.toLir = initMem cfg (linked (.ret [])) := by
    injection he with hp
    exact congrArg Prod.snd hp
  exact initMem_ne _ hm

/-- The frozen trap adequacy target is false without a memory-image condition. -/
theorem not_mir_run_trapped : ¬ Targets.mir_run_trapped := by
  intro h
  have he := beh_trapped _ (h cfg 1 (units .trap) mem run_trapped)
  have hm : mem.toLir = initMem cfg (linked .trap) := by
    injection he
  exact initMem_ne _ hm

end Silmaril.Compile.Mir.InterpCounterexample
