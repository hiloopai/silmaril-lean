module

public import Silmaril.Problems.Models.X86.Defs
public import Silmaril.Problems.Core.Defs
public import Silmaril.X86.Loose.Thms
public import Silmaril.X86.Loose.Decode.Thms
public import Silmaril.X86.Loose.Listing.Thms
public import Silmaril.X86.Stack

/-!
# Proofs: the loose top, and step lemmas for function proofs

The longer proofs behind `Silmaril/Problems/Models/X86/Thms.lean`.

* `looseRel_progress`: the loose machine over a prefix-free, functional table has
  `RelIsa.Progress` (for any form specifications, on views with `live = True`), and
  `str9Part_prefixFree`, so the loose top over a listing has it (`looseSv1_progress`);
* `mem_str9Part_int`, `mem_str9Part_str`: table membership of one listed byte string, by
  `classify`;
* `admits_regs`, `jcc_admits`, `jmp_admits`, `ret_admits`, `wordAt_of_abiEntry`: what an
  admitted successor of a register-only, branch or `ret` form is.
-/

@[expose] public section

namespace Silmaril.Proofs.Problems.Models.X86

open Silmaril.X86 (MState State Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Must Views)
open Silmaril.X86.Loose
open Silmaril.X86.Loose.Listing

/-! ## `Progress` of the loose machine -/

/-- The loose machine over a prefix-free, functional table has `Progress`: at a specified
entry the entries at `rip` agree on bytes and form, so `X86Loose.exists_step` gives a
successor; elsewhere `stop` is allowed. -/
theorem looseRel_progress {Φ σ : Type} [DecidableEq Φ] (D : DTable Φ) (S : Sigma Φ)
    (V : Views σ) (hp : D.prefixFree = true) (hf : D.functional = true)
    (hl : ∀ t, V.live t) : (X86Loose.rel D S V).Progress := by
  intro s _
  by_cases h : AtSpecified D S V s
  · obtain ⟨e, he, hat, F, hF, hu⟩ := h
    obtain ⟨t, ht⟩ := X86Loose.exists_step hl hF hu fun e' he' hat' => by
      obtain ⟨hb, hform⟩ := atEntry_unique hp hf he' he hat' hat
      exact ⟨hform, by rw [hb]⟩
    exact ⟨.ok t, ht⟩
  · exact ⟨.stop, X86Loose.step_stop_of_not_atSpecified h⟩

/-- `str9Part` of a prefix-free table is prefix-free. -/
theorem str9Part_prefixFree {D : DTable LForm} (hp : D.prefixFree = true) :
    (str9Part D).prefixFree = true := by
  unfold DTable.prefixFree at hp ⊢
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hp ⊢
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨e', he', hb, -⟩ := mem_str9Part he
    rw [← hb]; exact hp.1 e' he'
  · obtain ⟨e', he', hb, -⟩ := mem_str9Part he
    rw [List.all_eq_true]
    intro f hf
    obtain ⟨f', hf', hb', -⟩ := mem_str9Part hf
    have := hp.2 e' he'
    rw [List.all_eq_true] at this
    have := this f' hf'
    rw [← hb, ← hb']; exact this

/-! ## Table membership -/

theorem mem_str9Part_int {bs : List (List Nat)} {b : List Nat} {i : Silmaril.X86.Ext9.Instr}
    (hb : b ∈ bs) (hc : classify (toBytes b) = .loose (.int i)) :
    (⟨toBytes b, .ext9 i⟩ : DEntry Silmaril.X86.Str9.Instr) ∈ str9Part (table bs) := by
  unfold str9Part table
  rw [List.mem_filterMap]
  exact ⟨entryOf b, List.mem_map.2 ⟨_, hb, rfl⟩, by simp [entryOf, hc]⟩

theorem mem_str9Part_str {bs : List (List Nat)} {b : List Nat} {s : Silmaril.X86.Str9.Str}
    (hb : b ∈ bs) (hc : classify (toBytes b) = .str s) :
    (⟨toBytes b, .str s⟩ : DEntry Silmaril.X86.Str9.Instr) ∈ str9Part (table bs) := by
  unfold str9Part table
  rw [List.mem_filterMap]
  exact ⟨entryOf b, List.mem_map.2 ⟨_, hb, rfl⟩, by simp [entryOf, hc]⟩

/-! ## Effects -/

/-- An admitted successor of an effect that havocs nothing and writes no memory. -/
theorem admits_regs {e : Effect} {c c' : State} {m m' : Memory}
    (h : e.Admits c m c' m') (hh : e.havocRegs = []) (hw : e.writes = []) :
    m' = m ∧ c'.rip = e.rip ∧ e.flags.Allows c.flags c'.flags ∧
      ∀ r, c'.read r = e.regAfter c r := by
  refine ⟨?_, h.rip, h.flags, fun r => h.regs r (by simp [hh])⟩
  have := h.mem
  rw [hw] at this
  simp only [writeAll, Option.some.injEq] at this
  exact this.symm

theorem jcc_admits {cc : Silmaril.X86.Ext.Cond} {d : Word} {c c' : State} {m m' : Memory}
    {l : Nat} (h : ((Ctl.jccSpec cc d).eff c m l).Admits c m c' m') :
    m' = m ∧ c'.rip = (if cc.eval c.flags = some true then c.rip + BitVec.ofNat 64 l + d
      else c.rip + BitVec.ofNat 64 l) ∧ ∀ r, c'.read r = c.read r := by
  obtain ⟨hm, hr, -, hregs⟩ := admits_regs h rfl rfl
  exact ⟨hm, hr, fun r => by rw [hregs]; rfl⟩

theorem jmp_admits {d : Word} {c c' : State} {m m' : Memory} {l : Nat}
    (h : ((Ctl.jmpSpec d).eff c m l).Admits c m c' m') :
    m' = m ∧ c'.rip = c.rip + BitVec.ofNat 64 l + d ∧ ∀ r, c'.read r = c.read r := by
  obtain ⟨hm, hr, -, hregs⟩ := admits_regs h rfl rfl
  exact ⟨hm, hr, fun r => by rw [hregs]; rfl⟩

theorem ret_admits {c c' : State} {m m' : Memory} {l : Nat}
    (h : (Ctl.retSpec.eff c m l).Admits c m c' m') :
    m' = m ∧ c'.rip = (Ctl.wordAt m (c.read .rsp)).getD 0 ∧
      c'.read .rsp = c.read .rsp + 8#64 ∧ ∀ r, r ≠ .rsp → c'.read r = c.read r := by
  obtain ⟨hm, hr, -, hregs⟩ := admits_regs h rfl rfl
  refine ⟨hm, hr, by rw [hregs]; simp [Effect.regAfter, Ctl.retSpec, Ctl.popSpec, Ctl.retPost],
    fun r hr => ?_⟩
  rw [hregs]
  simp [Effect.regAfter, Ctl.retSpec, Ctl.popSpec, Ctl.retPost, Ne.symm hr]

theorem wordAt_of_abiEntry {c : State} {m : Memory}
    (h : Silmaril.X86.FnContract.AbiEntry c m) :
    Ctl.wordAt m (c.read .rsp) = some (Silmaril.X86.FnContract.retOf c m) := by
  unfold Ctl.wordAt
  rw [h.returnAddress]
  simp

end Silmaril.Proofs.Problems.Models.X86
