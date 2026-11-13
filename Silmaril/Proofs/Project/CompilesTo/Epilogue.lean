module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.SeqReach.Defs
public import Silmaril.X86.Open.Thms

/-!
# The return-label segment of a gcc `-O0` leaf, once for every function

`FnData.segment_ret`: at a `ret` point whose Core fragment is the return label's body
`pure(sym)` and whose machine code is `pop %rbp; ret`, the segment is simulated on `Open.isa`.
The Core side takes three steps (enter the pure expression, read the label's parameter, leave the
diagnostic frame) to the procedure's return; the machine side pops the caller's `rbp` from the
frame and returns. Every hypothesis is a decidable fact about the generated `FnData`.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

/-- A Core step from a `.next` request. -/
theorem coreStep {file : Program} {labels : Labels} {c c' : Control} {k k' : List Frame}
    {m : Mem.Concrete.State} (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ = .next c' k') :
    ∃ a, Step file labels ⟨c, k, m⟩ a ⟨c', k', m⟩ :=
  ⟨.tau, Step.respond live (h ▸ Respond.next)⟩

/-- Entering an unannotated pure expression pushes its diagnostic frame. -/
theorem request_effect_pure {file : Program} {labels : Labels} (p : PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    request file labels ⟨.effectExpr (.mk [] (.pure p)) env, k, m⟩ =
      .next (.pureExpr p env) (.diagnosticLocation m.currentLocation :: k) := by
  simp [request, requestAux, awaitsScheduling]

/-- A bound symbol evaluates to its value. -/
theorem request_pure_sym {file : Program} {labels : Labels} (r : Sym) (env : Env) (v : Val)
    (h : env.lookup r = some v) (k : List Frame) (m : Mem.Concrete.State) :
    request file labels ⟨.pureExpr (.mk [] () (.sym r)) env, k, m⟩ = .next (.value v) k := by
  simp [request, requestAux, awaitsScheduling, h]

/-- A value leaves the diagnostic frame of its own location. -/
theorem request_value_diag {file : Program} {labels : Labels} (v : Val) (k : List Frame)
    (m : Mem.Concrete.State) :
    request file labels ⟨.value v, .diagnosticLocation m.currentLocation :: k, m⟩ =
      .next (.value v) k := by
  simp [request, requestAux, awaitsScheduling]


/-! ## The machine side: `pop %rbp; ret` -/

section Machine

open Silmaril.X86 (State Reg)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- The state after `pop %rbp` (one byte). -/
def afterPop (m : MState) (v : BitVec 64) : MState :=
  ⟨{ (m.core.write .rsp (m.core.read .rsp + 8#64)).write .rbp v with
      rip := m.core.rip + BitVec.ofNat 64 1 }, m.memory⟩

/-- The state after `ret`. -/
def afterRet (m : MState) (v : BitVec 64) : MState :=
  ⟨{ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := v }, m.memory⟩

theorem step_pop_rbp {m : MState} {base : BitVec 64} {code : List Byte} {o : Nat} {v : BitVec 64}
    (hl : Silmaril.X86.Ext.Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + 1 ≤ code.length)
    (hb : (code.drop o).take 1 = [0x5d])
    (hread : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [v])) :
    Silmaril.X86.Open.step m = some (afterPop m v) := by
  refine Silmaril.X86.Open.step_of_listed (i := .base (.pop .rbp)) hl hrip hfit
    (by rw [hb]; decide) ?_
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.popWord_of_readBytes hread, Silmaril.X86.Ext.retire]

theorem step_ret {m : MState} {base : BitVec 64} {code : List Byte} {o : Nat} {v : BitVec 64}
    (hl : Silmaril.X86.Ext.Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + 1 ≤ code.length)
    (hb : (code.drop o).take 1 = [0xc3])
    (hread : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [v])) :
    Silmaril.X86.Open.step m = some (afterRet m v) := by
  refine Silmaril.X86.Open.step_of_listed (i := .base .ret) hl hrip hfit
    (by rw [hb]; decide) ?_
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.popWord_of_readBytes hread]

end Machine

/-! ## The segment -/

open Silmaril.Machine.LittleEndian (encodeWords) in
/-- **The return-label segment of a gcc `-O0` leaf is simulated.** At point `k`, of kind
`ret r`, whose fragment is the return label's body `pure(r)` and whose code is
`pop %rbp; ret`: the Core reads `r` and returns to the caller's continuation, and the machine
restores the caller's `rbp` from the frame and returns to the caller with the value still in
`rax`. The other hypotheses are decidable facts about `F` (the byte after `pop %rbp` is no
point, the code fits below `2^64`, the frame holds at least the saved `rbp`). -/
theorem FnData.segment_ret (F : FnData) {k : Nat} {r : Sym} {p : Point}
    (hp : F.points[k]? = some p) (hkind : p.kind = .ret r)
    (hfrag : p.frag = .mk [] (.pure (.mk [] () (.sym r))))
    (hpop : (F.code.drop p.off).take 1 = [0x5d])
    (hret : (F.code.drop (p.off + 1)).take 1 = [0xc3])
    (hfit : p.off + 2 ≤ F.code.length) (haddr : F.addr + F.code.length < 2 ^ 64)
    (hnext : ∀ q ∈ F.points, q.off ≠ p.off + 1)
    (hpts : ∀ q ∈ F.points, q.off < F.code.length)
    (hfr : 8 ≤ F.frame) :
    F.Segment Silmaril.X86.Open.isa k := by
  intro k0 x0 s x hs hx hr hsafe
  obtain ⟨p1, hp1, env1, hctl⟩ := hs
  obtain ⟨p3, hp3, hrip⟩ := hx
  obtain ⟨p2, hp2, hholds⟩ := hr
  rw [hp, Option.some.injEq] at hp1 hp2 hp3
  subst hp1 hp2 hp3
  rw [hkind] at hholds
  obtain ⟨hframe, hstack, E, env, hctl', kind, n, hres, hlook, hword⟩ := hholds
  rcases s with ⟨c, st, mem⟩
  simp only at hctl hstack hctl'
  subst hctl hstack
  rw [hfrag] at hctl'
  injection hctl' with hE henv
  subst henv
  -- The Core run: enter `pure(r)`, read `r`, leave the diagnostic frame.
  have h01 : (F.source k0).step ⟨.effectExpr p.frag env1, .procedureReturn F.bodyLabels :: k0, mem⟩
      ⟨.pureExpr (.mk [] () (.sym r)) env1,
        .diagnosticLocation mem.currentLocation :: .procedureReturn F.bodyLabels :: k0, mem⟩ := by
    rw [hfrag]; exact coreStep (by intro o h; cases h) (request_effect_pure _ _ _ _)
  have h12 : (F.source k0).step
      ⟨.pureExpr (.mk [] () (.sym r)) env1,
        .diagnosticLocation mem.currentLocation :: .procedureReturn F.bodyLabels :: k0, mem⟩
      ⟨.value (.loaded (.specified (.integer n))),
        .diagnosticLocation mem.currentLocation :: .procedureReturn F.bodyLabels :: k0, mem⟩ :=
    coreStep (by intro o h; cases h) (request_pure_sym r env1 _ hlook _ _)
  have h23 : (F.source k0).step
      ⟨.value (.loaded (.specified (.integer n))),
        .diagnosticLocation mem.currentLocation :: .procedureReturn F.bodyLabels :: k0, mem⟩
      ⟨.value (.loaded (.specified (.integer n))), .procedureReturn F.bodyLabels :: k0, mem⟩ :=
    coreStep (by intro o h; cases h) (request_value_diag _ _ mem)
  -- The machine run: `pop %rbp`, then `ret`.
  have hrsp0 : 8 ≤ (x0.core.read .rsp).toNat := le_trans hfr hframe.room
  have hsub : (x0.core.read .rsp - 8#64).toNat = (x0.core.read .rsp).toNat - 8 := by
    rw [BitVec.toNat_sub]; have := (x0.core.read .rsp).isLt; simp; omega
  have hread1 : x.memory.readBytes (x.core.read .rsp).toNat 8 =
      some (encodeWords [x0.core.read .rbp]) := by
    rw [hframe.rsp, hsub]; exact hframe.savedRbp
  have hrip0 : x.core.rip = BitVec.ofNat 64 F.addr + BitVec.ofNat 64 p.off := by
    simpa [BitVec.ofNat_add] using hrip
  have hs1 := step_pop_rbp (v := x0.core.read .rbp) hframe.loaded hrip0 (by omega) hpop hread1
  have hy1rsp : (afterPop x (x0.core.read .rbp)).core.read .rsp = x0.core.read .rsp := by
    simp [afterPop, hframe.rsp]
  have hread2 : (afterPop x (x0.core.read .rbp)).memory.readBytes
      ((afterPop x (x0.core.read .rbp)).core.read .rsp).toNat 8 =
      some (encodeWords [Silmaril.X86.FnContract.retOf x0.core x0.memory]) := by
    rw [hy1rsp]
    show x.memory.readBytes _ 8 = _
    rw [hframe.writes.readBytes (fun o _ h => by unfold StackBelow at h; omega)]
    exact hframe.abi.returnAddress
  have hrip1 : (afterPop x (x0.core.read .rbp)).core.rip =
      BitVec.ofNat 64 F.addr + BitVec.ofNat 64 (p.off + 1) := by
    simp [afterPop, hrip0, BitVec.ofNat_add, BitVec.add_assoc]
  have hs2 := step_ret (m := afterPop x (x0.core.read .rbp))
    (v := Silmaril.X86.FnContract.retOf x0.core x0.memory) hframe.loaded hrip1 (by omega) hret hread2
  refine ⟨⟨.value (.loaded (.specified (.integer n))), .procedureReturn F.bodyLabels :: k0, mem⟩,
    afterRet (afterPop x (x0.core.read .rbp)) (Silmaril.X86.FnContract.retOf x0.core x0.memory),
    ⟨.head h01 (.head h12 (.single h23)), Or.inr ⟨_, rfl, rfl⟩⟩,
    ⟨.more hs1 ?_ (.one hs2), ?_⟩, ?_⟩
  · -- the state after `pop` is no cut point
    intro h
    simp only [Corr.tgtCut, FnData.corr, Returned] at h
    rcases h with ⟨j, q, hq, hqrip⟩ | ⟨_, hret1⟩
    · have hmem : q ∈ F.points := List.mem_of_getElem? hq
      have hlt := hpts q hmem
      have hne := hnext q hmem
      have h1 : ((afterPop x (x0.core.read .rbp)).core.rip).toNat = F.addr + p.off + 1 := by
        rw [hrip1, ← BitVec.ofNat_add, BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (F.addr + q.off)).toNat = F.addr + q.off := by
        rw [BitVec.toNat_ofNat]; omega
      have hq' : (afterPop x (x0.core.read .rbp)).core.rip = BitVec.ofNat 64 (F.addr + q.off) :=
        hqrip
      rw [hq', h2] at h1
      omega
    · rw [hy1rsp] at hret1
      have h3 := congrArg BitVec.toNat hret1
      rw [BitVec.toNat_add] at h3
      have := (x0.core.read .rsp).isLt
      have h8 : (8#64).toNat = 8 := rfl
      rw [h8] at h3
      omega
  · exact Or.inr ⟨rfl, by simp [afterRet, hy1rsp]⟩
  · refine Or.inr ⟨_, ⟨rfl, rfl⟩, ⟨rfl, by simp [afterRet, hy1rsp]⟩, ⟨?_, hframe.writes⟩, ?_⟩
    · intro reg hreg
      have hcs := hframe.calleeSaved
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
        at hreg hcs
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [afterRet, afterPop] using hcs .rbx (by simp)
      · simp [afterRet, afterPop]
      · simpa [afterRet, afterPop] using hcs .r12 (by simp)
      · simpa [afterRet, afterPop] using hcs .r13 (by simp)
      · simpa [afterRet, afterPop] using hcs .r14 (by simp)
      · simpa [afterRet, afterPop] using hcs .r15 (by simp)
    · rw [hres]
      exact ⟨_, rfl, by simpa [afterRet, afterPop] using hword⟩

end Silmaril.Project.CompilesTo

end
