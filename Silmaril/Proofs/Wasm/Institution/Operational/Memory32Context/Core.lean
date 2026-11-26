module

public import Silmaril.Wasm.Institution.Operational.Memory32Context.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
import Silmaril.Wasm.Execution.Core.Sim.Context

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Context.Proofs

open Execution Core Numerics
open Silmaril.Wasm.SingleThreaded.Det

private theorem core_args {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {q : Access} {args : List Val} {dst : Config H}
    (move : MemoryStep P ⟨s, f, vals args ++ [q.coreOp]⟩ dst) :
    args.length = q.args.length := by
  generalize he : (⟨s, f, vals args ++ [q.coreOp]⟩ : Config H) = src at move
  have eq := congrArg (fnv ∘ Config.code) he
  cases move <;> cases q <;> simp [Access.coreOp, Access.args, fnv, Admin.val?, aconst] at eq ⊢
  all_goals grind

private theorem core_cut {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {q : Access} {saved : List Val} {rest : List Admin} {dst : Config H}
    (step : Step P noHost ⟨s, f, vals (saved ++ q.args.map Runtime.Value.toCore) ++ q.coreOp :: rest⟩ dst) :
    ∃ mid, Step P noHost ⟨s, f, vals (q.args.map Runtime.Value.toCore) ++ [q.coreOp]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, vals saved ++ mid.code ++ rest⟩ := by
  have nonval : q.coreOp.val? = none := by cases q <;> rfl
  have family : famOf q.coreOp = .memory := by cases q <;> rfl
  have front := fnv_vals_append (saved ++ q.args.map Runtime.Value.toCore) (q.coreOp :: rest)
  simp only [fnv_cons_of_none nonval, List.append_nil] at front
  rcases Step.decomp step with head | bubble
  · obtain ⟨kept, args, op, tail, mid, split, _, leaf, rfl⟩ := fnv_headDec head
    obtain ⟨stack, rfl, rfl⟩ := (Prod.mk.inj (split.symm.trans front)).imp id List.cons.inj
    have mem := leaf.fam_inv (by rw [family]; decide)
    rw [family] at mem
    have length := core_args (q := q) (show MemoryStep P _ _ from mem)
    obtain ⟨rfl, rfl⟩ := List.append_inj' stack (by simpa using length)
    exact ⟨mid, .memory mem, rfl⟩
  · obtain ⟨_, _, _, _, _, ⟨seen, _, _⟩ | ⟨_, seen, _, _⟩⟩ := fnv_bubble bubble <;>
      have bad := (List.cons.inj (Prod.mk.inj (seen.symm.trans front)).2).1 <;>
      cases q <;> cases bad

theorem core_iff {H : Type} {P : Profile} {s : Store H} {f : Frame} {a : Nat} {m : MemInst}
    {q : Access} {saved : List Val} {rest : List Admin} {dst : Config H}
    (lookup : s.mem? f MemoryQuery.index = some (a, m)) (is32 : m.type.address = .i32) :
    Step P noHost ⟨s, f, vals (saved ++ q.args.map Runtime.Value.toCore) ++ q.coreOp :: rest⟩ dst ↔
      ∃ out, Edge m.bytes q out ∧
        dst = ⟨out.coreStore s a m, f, vals saved ++ out.code (Val.toAdmin ∘ Runtime.Value.toCore) .trap ++ rest⟩ := by
  constructor
  · intro move
    obtain ⟨mid, head, rfl⟩ := core_cut move
    cases q with
    | load address =>
      obtain ⟨out, rule, rfl⟩ := MemoryQuery.core_readback lookup is32 (query := .load address) head
      cases MemoryQuery.invert rule with
      | load => exact ⟨.value _, .load rule, rfl⟩
      | loadTrap => exact ⟨.trap, .loadTrap rule, rfl⟩
    | store address word =>
      obtain ⟨out, rule, rfl⟩ := (MemoryWrite.core_step_iff (P := P)
        (a := .store address word) ⟨lookup, is32⟩).mp head
      cases MemoryWrite.invert rule with
      | write => exact ⟨.written _, .store rule, rfl⟩
      | trap => exact ⟨.trap, .storeTrap rule, rfl⟩
  · rintro ⟨out, rule, rfl⟩
    have wrap {q : Access} {out : Outcome} (move : Step P noHost
        ⟨s, f, vals (q.args.map Runtime.Value.toCore) ++ [q.coreOp]⟩
        ⟨out.coreStore s a m, f, out.code (Val.toAdmin ∘ Runtime.Value.toCore) .trap⟩) :
        Step P noHost ⟨s, f, vals (saved ++ q.args.map Runtime.Value.toCore) ++ q.coreOp :: rest⟩
          ⟨out.coreStore s a m, f, vals saved ++ out.code (Val.toAdmin ∘ Runtime.Value.toCore) .trap ++ rest⟩ := by
      simpa only [vals_append, List.append_assoc, List.singleton_append] using
        Core.Sim.Step.vals_left (Core.Sim.Step.append_right move rest) saved
    cases rule with
    | load e => exact wrap (MemoryQuery.core_sound lookup is32 e)
    | loadTrap e => exact wrap (MemoryQuery.core_sound lookup is32 e)
    | store e => exact wrap (MemoryWrite.core_sound ⟨lookup, is32⟩ e)
    | storeTrap e => exact wrap (MemoryWrite.core_sound ⟨lookup, is32⟩ e)

end Silmaril.Wasm.Institution.Operational.Memory32Context.Proofs
