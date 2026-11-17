module

public import Silmaril.Machine.Abi.OpenMachine.Defs
public import Silmaril.Proofs.Machine.Abi.OpenMachine.Runs
/-!
# The System V comorphism on the open machine: the generic satisfaction theorem

* `abiEntry_of_entry`, `retOf_of_entry`: a System V `Entry` state (track C) meets A's
  `FnContract.AbiEntry`, and its return address is A's `FnContract.retOf`;
* `return_of_result`: A's `Spec.Result` from such a state is a System V `Return` (track C);
* `callModel_eq`: the first-return call relation has at most one outcome;
* `sat_of_firstReturn`: **a contract whose runs end at the first return, and whose
  postcondition determines the C result, satisfies `within ((sysv o).translate p c) room`
  for the call relation `callModel`**;
* `bytes4_inj`, `chunk32_iff`: four little-endian bytes determine a 32-bit value, so a 32-bit
  scalar in the low half of a register is read back exactly.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.OpenMachine

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options CallSite callOf intPlan)
open Silmaril.Machine.Abi.OpenMachine

variable {o : Options} {p : Proto}

/-- A System V entry state gives the return address it holds. -/
theorem retAddr_of_entry {a : vocab.Args p} {s : Ffi.State} (entry : (sysv o).Entry p a s) :
    ∃ exit, s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [exit]) ∧
      FnContract.retOf s.machine.core s.machine.memory = exit ∧
      s.direction = false ∧ s.x87Mode = true := by
  obtain ⟨exit, e⟩ := entry
  exact ⟨exit, e.returnAddress, FnContract.retOf_of_readBytes e.returnAddress, e.direction,
    e.x87Mode⟩

/-- A System V entry state meets A's `AbiEntry`. -/
theorem abiEntry_of_entry {a : vocab.Args p} {s : Ffi.State} (entry : (sysv o).Entry p a s) :
    FnContract.AbiEntry s.machine.core s.machine.memory := by
  obtain ⟨exit, e⟩ := entry
  have align := e.alignment
  change ((s.machine.core.read .rsp).toNat + 8) % 16 = 0 at align
  have ra : s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) := e.returnAddress
  refine ⟨by omega, ?_⟩
  rw [FnContract.retOf_of_readBytes ra]
  exact ra

/-- A's call result from a System V entry state is a System V return. -/
theorem return_of_result {S : FnContract.Spec MState} {a : vocab.Args p} {s : Ffi.State}
    {t : MState} (entry : (sysv o).Entry p a s) (res : S.Result Open.isa s.machine t) :
    (sysv o).Return p s { s with machine := t } := by
  obtain ⟨exit, ra, hret, dir, x87⟩ := retAddr_of_entry entry
  refine ⟨exit, ra, ?_⟩
  have pc := res.abi.pc
  simp only at pc
  exact ⟨pc.trans hret, res.abi.stack, res.abi.calleeSaved, dir, x87, rfl, rfl, rfl⟩

/-- The outcomes of `callModel` from `s` are the first return of `s`'s run. -/
theorem mem_callModel {s t : Ffi.State} {u : MState} (first : FirstReturn s.machine u)
    (h : t ∈ callModel s) : t = { s with machine := u } := by
  obtain ⟨first', eq⟩ := h
  rw [eq, firstReturn_unique first' first]

theorem callModel_subsingleton (s : Ffi.State) {t t' : Ffi.State} (h : t ∈ callModel s)
    (h' : t' ∈ callModel s) : t = t' :=
  (mem_callModel h.1 h).trans (mem_callModel h.1 h').symm

/-- **ABI correctness on the open machine.** If every room-admitted System V entry state of
`p` runs to a first return that meets A's `Spec.Result` of `S`, and `S`'s postcondition makes
the System V read-back of the result exist and satisfy the C postcondition, then `callModel`
satisfies the System V translation of `c` on room-admitted states. -/
theorem sat_of_firstReturn {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))}
    {S : FnContract.Spec MState} {room : Ffi.State → Prop}
    (total : ∀ a s, (sysv o).Entry p a s → c.pre a → room s →
      ∃ t, FirstReturn s.machine t ∧ S.Result Open.isa s.machine t)
    (post : ∀ a s t, (sysv o).Entry p a s → c.pre a → room s → S.post s.machine t →
      (∃ r, (sysv o).ResultAt p s { s with machine := t } r) ∧
        ∀ r, (sysv o).ResultAt p s { s with machine := t } r → c.post a (some r)) :
    Contracts.Sat callModel (within ((sysv o).translate p c) room) := by
  rintro s ⟨⟨a, entry, pre⟩, roomy⟩
  obtain ⟨t, first, res⟩ := total a s entry pre roomy
  refine ⟨⟨{ s with machine := t }, first, rfl⟩, ?_⟩
  intro t' ran a' entry' pre' ob observed
  rw [mem_callModel first ran] at observed
  have ret := return_of_result entry' res
  obtain ⟨⟨r, at_⟩, reflect⟩ := post a' s t entry' pre' roomy res.post
  cases ob with
  | none => exact absurd ⟨ret, r, at_⟩ observed
  | some r' => exact reflect r' observed.2

/-! ## 32-bit scalars in registers -/

/-- `Ffi.bytes4_inj` (one copy, in `Machine.SystemV.Abi.Ffi`). -/
theorem bytes4_inj {x y : BitVec 32}
    (h : Ffi.bytesOfNat x.toNat 0 4 = Ffi.bytesOfNat y.toNat 0 4) : x = y :=
  Ffi.bytes4_inj h

/-- `Ffi.chunk32_iff` (one copy, in `Machine.SystemV.Abi.Ffi`). -/
theorem chunk32_iff (s : Ffi.State) (r : Reg) (v : BitVec 32) :
    Ffi.ChunksAt s (Ffi.bytesOfNat (v.setWidth 64).toNat 0 4) [⟨0, 4, .gp r⟩] ↔
      (s.machine.core.read r).setWidth 32 = v :=
  Ffi.chunk32_iff s r v

end Silmaril.Proofs.Machine.Abi.OpenMachine
