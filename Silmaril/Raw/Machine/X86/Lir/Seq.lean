module

public import Silmaril.Machine.X86.Lir.Rel.Defs

/-!
# Sequences of stack loads and stores

`run_stQs` executes a list of 64-bit stores `mov [rsp + dₖ], rₖ` to pairwise
disjoint words of the stack, and `run_ldQs` a list of 64-bit loads
`mov rₖ, [rsp + dₖ]` into pairwise distinct registers. They are the building
blocks of the save, reload, argument and staging sequences of calls and
prologues.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine

def stQ (x : Reg × Nat) : Ext.Instr := .mov .q (.mem (spMem x.2)) x.1
def ldQ (x : Reg × Nat) : Ext.Instr := .load .q x.1 (spMem x.2)

section

variable {S : Space} {n : Nat} (hv : S.Valid n)
include hv

theorem stack_store {s : State} {m : Memory} (hreg : m.regions = S.regions n) {B d : Nat}
    (hB : s.read .rsp = BitVec.ofNat 64 B) (hd : d < 2 ^ 31) (hlo : S.stackLo ≤ B + d)
    (hhi : B + d + 8 ≤ S.stackHi) (r : Reg) :
    ∃ m', Ext.exec (.mov .q (.mem (spMem d)) r) s m =
        .ok { s with rip := s.rip + BitVec.ofNat 64 (Ext.encode (.mov .q (.mem (spMem d)) r)).length } m' ∧
      WordAt m' (B + d) (s.read r) ∧ Memory.WritesOnly m m' (B + d) 8 := by
  have hs : B + d < 2 ^ 64 := by have := hv.stack_end; omega
  obtain ⟨m', hm'⟩ := storeN_some hs (s.read r)
    (permitted_stack hreg hv .write (by decide) hlo hhi)
  exact ⟨m', exec_stQ_sp s m r hB hd hm', wordAt_storeN hs hm', storeN_writesOnly' hs hm'⟩

theorem stack_load {s : State} {m : Memory} (hreg : m.regions = S.regions n) {B d : Nat}
    (hB : s.read .rsp = BitVec.ofNat 64 B) (hd : d < 2 ^ 31) (hlo : S.stackLo ≤ B + d)
    (hhi : B + d + 8 ≤ S.stackHi) (r : Reg) {v : Word} (hw : WordAt m (B + d) v) :
    Ext.exec (.load .q r (spMem d)) s m =
      .ok { s.write r v with rip := s.rip + BitVec.ofNat 64 (Ext.encode (.load .q r (spMem d))).length } m := by
  have hs : B + d < 2 ^ 64 := by have := hv.stack_end; omega
  exact exec_ldQ_sp s m r hB hd hs hw (permitted_stack hreg hv .read (by decide) hlo hhi)

/-- A list of stores to disjoint stack words. -/
theorem run_stQs {B : Nat} :
    ∀ (L : List (Reg × Nat)) (s : State) (m : Memory),
    s.read .rsp = BitVec.ofNat 64 B → m.regions = S.regions n →
    (∀ x ∈ L, x.2 < 2 ^ 31 ∧ S.stackLo ≤ B + x.2 ∧ B + x.2 + 8 ≤ S.stackHi) →
    L.Pairwise (fun a b => a.2 + 8 ≤ b.2 ∨ b.2 + 8 ≤ a.2) →
    ∃ s' m', runSeq (L.map stQ) s m = some (s', m') ∧ (∀ r, s'.read r = s.read r) ∧
      m'.regions = m.regions ∧ (∀ x ∈ L, WordAt m' (B + x.2) (s.read x.1)) ∧
      (∀ a, (∀ x ∈ L, a < B + x.2 ∨ B + x.2 + 8 ≤ a) → m'.bytes.get? a = m.bytes.get? a)
  | [], s, m, _, _, _, _ => ⟨s, m, rfl, fun _ => rfl, rfl, by simp, fun _ _ => rfl⟩
  | x :: L, s, m, hB, hreg, hb, hp => by
    obtain ⟨hd, hlo, hhi⟩ := hb x (by simp)
    obtain ⟨m₁, he, hw, hwo⟩ := stack_store hv hreg hB hd hlo hhi x.1
    rw [List.map_cons, show stQ x = .mov .q (.mem (spMem x.2)) x.1 from rfl,
      runSeq_cons_of he (by intro h; cases h) rfl]
    obtain ⟨s', m', hr, hs', hreg', hws, hout⟩ :=
      run_stQs L { s with rip := (s.rip + BitVec.ofNat 64
        (Ext.encode (.mov .q (.mem (spMem x.2)) x.1)).length) } m₁ (by simpa using hB) (hwo.1.trans hreg) (fun y hy => hb y (by simp [hy]))
        (List.pairwise_cons.mp hp).2
    refine ⟨s', m', hr, fun r => by rw [hs']; rfl, hreg'.trans hwo.1, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · refine hw.congr fun i hi => hout _ fun z hz => ?_
        have := (List.pairwise_cons.mp hp).1 z hz
        omega
      · have := hws y hy
        simpa using this
    · intro a ha
      rw [hout a (fun z hz => ha z (by simp [hz])), hwo.2 a (by have := ha x (by simp); omega)]

/-- A list of loads of stack words into distinct registers other than RSP. -/
theorem run_ldQs {B : Nat} :
    ∀ (L : List (Reg × Nat)) (s : State) (m : Memory),
    s.read .rsp = BitVec.ofNat 64 B → m.regions = S.regions n →
    (∀ x ∈ L, x.1 ≠ .rsp ∧ x.2 < 2 ^ 31 ∧ S.stackLo ≤ B + x.2 ∧ B + x.2 + 8 ≤ S.stackHi ∧
      ∃ v, WordAt m (B + x.2) v) →
    L.Pairwise (fun a b => a.1 ≠ b.1) →
    ∃ s', runSeq (L.map ldQ) s m = some (s', m) ∧
      (∀ x ∈ L, ∀ v, WordAt m (B + x.2) v → s'.read x.1 = v) ∧
      (∀ r, (∀ x ∈ L, r ≠ x.1) → s'.read r = s.read r)
  | [], s, m, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ => rfl⟩
  | x :: L, s, m, hB, hreg, hb, hp => by
    obtain ⟨hr, hd, hlo, hhi, v₀, hw⟩ := hb x (by simp)
    have he := stack_load hv hreg hB hd hlo hhi x.1 hw
    rw [List.map_cons, show ldQ x = .load .q x.1 (spMem x.2) from rfl,
      runSeq_cons_of he (by intro h; cases h) rfl]
    obtain ⟨s', h', hvals, hkeep⟩ :=
      run_ldQs L { s.write x.1 v₀ with rip := (s.rip + BitVec.ofNat 64
        (Ext.encode (.load .q x.1 (spMem x.2))).length) } m
        (by simpa [State.read_write_other _ _ _ _ (Ne.symm hr)] using hB) hreg
        (fun y hy => hb y (by simp [hy])) (List.pairwise_cons.mp hp).2
    refine ⟨s', h', ?_, ?_⟩
    · intro y hy v hv'
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hkeep _ fun z hz => (List.pairwise_cons.mp hp).1 z hz, WordAt.unique hv' hw]
        simp
      · exact hvals y hy v hv'
    · intro r hr'
      rw [hkeep r fun z hz => hr' z (by simp [hz])]
      simp [State.read_write_other _ _ _ _ (hr' x (by simp))]

end

end Silmaril.X86.Backend
