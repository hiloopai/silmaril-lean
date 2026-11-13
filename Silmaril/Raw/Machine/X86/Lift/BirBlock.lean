-- Imported from an earlier development
-- Source: Silmaril/X86/Lift/BirBlock.lean; sha256=960984d7b200c42dfc20e59025cdd788a1287ad6814e4765e690b460b1be8903
-- Reproduce with tools/mor/examples/import_x86_lift.rs; declaration namespaces retained.
module

public import Silmaril.Raw.Machine.X86.Lift.BirSound

/-!
# The block theorem over `XState`

`BirSound` relates one symbolic step of an `Ext` or extension integer
instruction to `Ext.exec` on the core state. This module adds the XMM
registers: `XRel` extends `Rel` with them, `lift_core_step` carries a core
step over (those instructions leave the XMM registers alone), the SSE moves
are proved directly, and `symExec_sound` is the block simulation theorem for
the lifting machine `XState`:

```
symExec instrs = some b → execBlock instrs s mem = b.run s mem
```
-/

@[expose] public section

namespace Silmaril.X86.Lift.Bir

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)

/-! ## 128-bit halves -/

theorem lo64_append (h l : Word) : lo64 (h ++ l) = l := BitVec.setWidth_append_eq_right

theorem hi64_append (h l : Word) : hi64 (h ++ l) = h := BitVec.extractLsb'_append_eq_left

theorem hi64_append_lo64 (v : BitVec 128) : hi64 v ++ lo64 v = v := by
  rw [lo64, hi64, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_append_extractLsb' (x := v) (w := 64) (len := 64)

/-! ## The relation with XMM registers -/

/-- `Rel` does not look at the symbolic XMM registers. -/
theorem Rel.xmm_irrel {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (X : Fin 16 → E × E) : Rel { σ with xmm := X } env s mem :=
  ⟨h.mem, h.len, h.regs, h.flags, h.rip, h.fs, h.wf⟩

structure XRel (σ : SState) (env : Env) (s : XState) (mem : Memory) : Prop where
  core : Rel σ env s.core mem
  xmm : ∀ i, s.xmm i = (σ.xmm i).2.den env ++ (σ.xmm i).1.den env
  xwf : ∀ i, (σ.xmm i).1.wf σ.n ∧ (σ.xmm i).2.wf σ.n

def XStepRel (r : XResult) (x : Except Fault Env) (σ' : SState) : Prop :=
  match r, x with
  | .ok s' m', .ok env' => XRel σ' env' s' m'
  | r, .error f => r = f.toX
  | _, _ => False

theorem XStepRel.fault {env : Env} {sts : List Stmt} {σ' : SState} {f : Fault}
    (h : runStmts sts env = .error f) : XStepRel f.toX (runStmts sts env) σ' := by
  rw [h]; cases f <;> rfl

theorem XStepRel.prepend {env env1 : Env} {s1 s2 : List Stmt} {r : XResult} {σ' : SState}
    (h1 : runStmts s1 env = .ok env1) (h : XStepRel r (runStmts s2 env1) σ') :
    XStepRel r (runStmts (s1 ++ s2) env) σ' := by
  rw [runStmts_append, h1]; exact h

/-- Integer instructions leave the XMM registers alone: a core step lifts. -/
theorem lift_core_step {σ σ' : SState} {env : Env} {s : XState} {mem : Memory} {r : Result}
    {sts : List Stmt} (h : XRel σ env s mem) (hs : StepRel r (runStmts sts env) σ')
    (hx : σ'.xmm = σ.xmm) : XStepRel (liftR s.xmm r) (runStmts sts env) σ' := by
  revert hs
  cases hrun : runStmts sts env with
  | error f =>
    intro hs
    have : r = f.toResult := by cases r <;> exact hs
    subst this
    simp only [XStepRel, Fault.liftR_toResult]
  | ok env' =>
    intro hs
    cases r with
    | ok s' m' =>
      have hext := runStmts_ext hrun
      have hrel : Rel σ' env' s' m' := hs
      have hlen : σ.n ≤ σ'.n := by
        rw [← h.core.len, ← hrel.len]; exact hext.2.2.length_le
      refine ⟨hrel, fun i => ?_, fun i => ?_⟩
      · rw [h.xmm i, hx, E.den_ext (e := (σ.xmm i).1) hext (by rw [h.core.len]; exact (h.xwf i).1),
          E.den_ext (e := (σ.xmm i).2) hext (by rw [h.core.len]; exact (h.xwf i).2)]
      · rw [hx]; exact ⟨E.wf_mono hlen (h.xwf i).1, E.wf_mono hlen (h.xwf i).2⟩
    | _ => exact hs.elim

/-! ## The integer steps do not touch the XMM registers -/

@[simp] theorem sRead_xmm (σ : SState) (nx : E) (k : Nat) (op : RM) :
    (sRead σ nx k op).2.2.xmm = σ.xmm := by cases op <;> rfl
@[simp] theorem sWriteRM_xmm (σ : SState) (nx : E) (sz : Sz) (op : RM) (e : E) :
    (sWriteRM σ nx sz op e).2.xmm = σ.xmm := by cases op <;> rfl
@[simp] theorem sWriteN_xmm (σ : SState) (nx : E) (n : Narrow) (op : RM) (e : E) :
    (sWriteN σ nx n op e).2.xmm = σ.xmm := by cases op <;> rfl
@[simp] theorem SState.setReg_xmm (σ : SState) (r : Reg) (e : E) : (σ.setReg r e).xmm = σ.xmm := rfl
@[simp] theorem SState.fresh_xmm (σ : SState) : σ.fresh.xmm = σ.xmm := rfl

theorem symStep_xmm_ext (σ : SState) (i : Ext.Instr) (len : Nat) (p : List Stmt × SState)
    (hs : symStep σ (.ext i) len = some p) : p.2.xmm = σ.xmm := by
  cases i
  case unary sz op dst => cases op <;> cases hs <;> simp [sRMW]
  case cxe sz => cases sz <;> cases hs <;> rfl
  case aluR sz op dst src =>
    by_cases hop : op = .cmp
    · simp only [symStep, hop, ite_true] at hs; cases hs; simp [sReadF]
    · simp only [symStep, hop, ite_false] at hs; cases hs; simp [sReadSetF]
  case div => cases hs
  case test8 | testI8 | testA8 | cmpI8 | cmpA8 | mul | cmov => cases hs
  all_goals
    simp only [symStep] at hs
    cases hs
    first
    | rfl
    | (unfold sAlu; split <;> simp)
    | simp [sMov, sMovN, sReadSet, sReadSetF, sReadF, sRMW, sPushState]

theorem symStep_xmm_x (σ : SState) (i : XInstr) (len : Nat) (p : List Stmt × SState)
    (hs : symStep σ (.x i) len = some p) : p.2.xmm = σ.xmm := by
  cases i
  case alu8 op dst src =>
    simp only [symStep] at hs
    split at hs <;> cases hs <;> simp
  case aluHi op r imm =>
    simp only [symStep] at hs
    split at hs <;> cases hs <;> simp
  all_goals
    simp only [symStep] at hs
    cases hs
    first | rfl | simp [sReadF, sPushState]

/-! ## SSE moves -/

variable {σ : SState} {env : Env} {s : XState} {mem : Memory}

theorem xsetS_apply (x : Fin 16 → E × E) (d i : Fin 16) (v : E × E) :
    xsetS x d v i = if i = d then v else x i := rfl

theorem Xmm.set_apply (x : Xmm) (d i : Fin 16) (v : BitVec 128) :
    x.set d v i = if i = d then v else x i := rfl

theorem alignChk_run (_h : Rel σ env s.core mem) (al : Bool) {a : E} {addr : Word}
    (ha : a.den env = addr) :
    runStmts (alignChk al a) env = if misaligned al addr then .error .data else .ok env := by
  cases al
  · rfl
  · simp only [alignChk, ite_true, runStmts, Stmt.run, ha, misaligned, Bool.true_and,
      bne_iff_ne, ne_eq]
    by_cases hm : addr.toNat % 16 = 0 <;> simp [hm]

@[simp] theorem Env.push_mem (env : Env) (w : Word) : (env.push w).mem = env.mem := rfl

set_option maxHeartbeats 1000000 in
theorem symStep_sound_sse (h : XRel σ env s mem) (i : SInstr) (len : Nat) (p : List Stmt × SState)
    (hs : symStep σ (.sse i) len = some p) :
    XStepRel (SInstr.exec i s mem len) (runStmts p.1 env) p.2 := by
  have hc := h.core
  have hnx := nxOf_den hc len
  have hnxw := nxOf_wfn hc len
  cases i with
  | zero d =>
    cases hs
    refine ⟨(hc.xmm_irrel (xsetS σ.xmm d (.imm 0, .imm 0))).setRip' hnxw hnx.symm,
      fun i => ?_, fun i => ?_⟩
    · simp only [Xmm.set_apply, xsetS_apply]
      split
      · show (0 : BitVec 128) = 0#64 ++ 0#64; decide
      · exact h.xmm i
    · simp only [xsetS_apply]; split
      · exact ⟨trivial, trivial⟩
      · exact h.xwf i
  | mov d src =>
    cases hs
    refine ⟨(hc.xmm_irrel (xsetS σ.xmm d (σ.xmm src))).setRip' hnxw hnx.symm,
      fun i => ?_, fun i => ?_⟩
    · simp only [Xmm.set_apply, xsetS_apply]
      split
      · exact h.xmm src
      · exact h.xmm i
    · simp only [xsetS_apply]; split
      · exact h.xwf src
      · exact h.xwf i
  | load128 al d m =>
    cases hs
    have ha := sAddr_den hc hnx m
    simp only [SInstr.exec]
    rw [runStmts_append, alignChk_run hc al ha]
    by_cases hmis : misaligned al (m.addr s.core (s.core.rip + BitVec.ofNat 64 len))
    · simp only [hmis, ite_true]; rfl
    · simp only [hmis, Bool.false_eq_true, ite_false]
      rw [← hc.mem]
      cases hl : loadN env.mem (m.addr s.core (s.core.rip + BitVec.ofNat 64 len)) 8 with
      | none =>
        have hr : runStmts [.load 8 (sAddr σ (nxOf σ len) m),
            .load 8 (.add (sAddr σ (nxOf σ len) m) (.imm 8#64))] env = .error .data := by
          simp only [runStmts, Stmt.run, ha, hl]
        exact XStepRel.fault hr
      | some l =>
        dsimp only
        have ha1 : (sAddr σ (nxOf σ len) m).den (env.push l) =
            m.addr s.core (s.core.rip + BitVec.ofNat 64 len) := by
          rw [E.den_ext (env.ext_push l) (wf_lift hc (sAddr_wf hc.wf hnxw m))]; exact ha
        cases hh : loadN env.mem (m.addr s.core (s.core.rip + BitVec.ofNat 64 len) + 8#64) 8 with
        | none =>
          have hr : runStmts [.load 8 (sAddr σ (nxOf σ len) m),
              .load 8 (.add (sAddr σ (nxOf σ len) m) (.imm 8#64))] env = .error .data := by
            simp only [runStmts, Stmt.run, ha, hl, E.den, ha1, Env.push_mem, hh]
          exact XStepRel.fault hr
        | some hv =>
          dsimp only
          have hr : runStmts [.load 8 (sAddr σ (nxOf σ len) m),
              .load 8 (.add (sAddr σ (nxOf σ len) m) (.imm 8#64))] env = .ok ((env.push l).push hv) := by
            simp only [runStmts, Stmt.run, ha, hl, E.den, ha1, Env.push_mem, hh]
          rw [hr]
          have hp2 := (hc.push l).push hv
          have hx2 : env.Ext ((env.push l).push hv) :=
            (env.ext_push l).trans ((env.push l).ext_push hv)
          have hnx2 : (nxOf σ len).den ((env.push l).push hv) = s.core.rip + BitVec.ofNat 64 len := by
            rw [E.den_ext hx2 (nxOf_wf hc len)]; exact hnx
          rw [hc.mem]
          refine ⟨(hp2.xmm_irrel (xsetS σ.xmm d (.v σ.n, .v (σ.n + 1)))).setRip'
              (E.wf_mono (by simp only [SState.fresh]; omega) hnxw) hnx2.symm, fun i => ?_, fun i => ?_⟩
          · simp only [Xmm.set_apply, xsetS_apply]
            split
            · simp [E.den, Env.push, hc.len]
            · rw [h.xmm i, E.den_ext (e := (σ.xmm i).2) hx2 (by rw [hc.len]; exact (h.xwf i).2),
                E.den_ext (e := (σ.xmm i).1) hx2 (by rw [hc.len]; exact (h.xwf i).1)]
          · simp only [xsetS_apply, SState.fresh]; split
            · simp only [E.wf]; omega
            · exact ⟨E.wf_mono (by omega) (h.xwf i).1, E.wf_mono (by omega) (h.xwf i).2⟩
  | store128 al m src =>
    cases hs
    have ha := sAddr_den hc hnx m
    simp only [SInstr.exec]
    rw [runStmts_append, alignChk_run hc al ha]
    by_cases hmis : misaligned al (m.addr s.core (s.core.rip + BitVec.ofNat 64 len))
    · simp only [hmis, ite_true]; rfl
    · simp only [hmis, Bool.false_eq_true, ite_false]
      have hlo : lo64 (s.xmm src) = (σ.xmm src).1.den env := by rw [h.xmm src, lo64_append]
      have hhi : hi64 (s.xmm src) = (σ.xmm src).2.den env := by rw [h.xmm src, hi64_append]
      rw [hlo, hhi]
      have hm : ∀ (m' : Memory) (e : E), e.den { env with mem := m' } = e.den env := fun m' e => by
        induction e <;> simp_all [E.den]
      rw [← hc.mem]
      cases hs1 : storeN env.mem (m.addr s.core (s.core.rip + BitVec.ofNat 64 len)) 8
          ((σ.xmm src).1.den env) with
      | none =>
        have hr : runStmts [.store 8 (sAddr σ (nxOf σ len) m) (σ.xmm src).1,
            .store 8 (.add (sAddr σ (nxOf σ len) m) (.imm 8#64)) (σ.xmm src).2] env = .error .data := by
          simp only [runStmts, Stmt.run, ha, hs1]
        exact XStepRel.fault hr
      | some m1 =>
        dsimp only
        cases hs2 : storeN m1 (m.addr s.core (s.core.rip + BitVec.ofNat 64 len) + 8#64) 8
            ((σ.xmm src).2.den env) with
        | none =>
          have hr : runStmts [.store 8 (sAddr σ (nxOf σ len) m) (σ.xmm src).1,
              .store 8 (.add (sAddr σ (nxOf σ len) m) (.imm 8#64)) (σ.xmm src).2] env = .error .data := by
            simp only [runStmts, Stmt.run, ha, hs1, E.den, hm, hs2]
          exact XStepRel.fault hr
        | some m2 =>
          dsimp only
          have hr : runStmts [.store 8 (sAddr σ (nxOf σ len) m) (σ.xmm src).1,
              .store 8 (.add (sAddr σ (nxOf σ len) m) (.imm 8#64)) (σ.xmm src).2] env =
              .ok { env with mem := m2 } := by
            simp only [runStmts, Stmt.run, ha, hs1, E.den, hm, hs2]
          rw [hr]
          have hr2 : Rel σ { env with mem := m2 } s.core m2 := hc.store
          refine ⟨hr2.setRip' hnxw (by rw [hm]; exact hnx.symm), fun i => ?_, h.xwf⟩
          simp only [hm]; exact h.xmm i

theorem symStep_sound (h : XRel σ env s mem) (i : LInstr) (len : Nat) (p : List Stmt × SState)
    (hs : symStep σ i len = some p) : XStepRel (i.exec s mem len) (runStmts p.1 env) p.2 := by
  cases i with
  | ext i => exact lift_core_step h (symStep_sound_ext h.core i len p hs) (symStep_xmm_ext σ i len p hs)
  | x i => exact lift_core_step h (symStep_sound_x h.core i len p hs) (symStep_xmm_x σ i len p hs)
  | sse i => exact symStep_sound_sse h i len p hs

/-! ## Blocks -/

/-- Symbolically execute a straight-line list of instructions. -/
def symGo : List (LInstr × Nat) → SState → Option (List Stmt × SState)
  | [], σ => some ([], σ)
  | (i, len) :: rest, σ =>
    match symStep σ i len with
    | none => none
    | some (s1, σ1) =>
      match symGo rest σ1 with
      | none => none
      | some (s2, σ2) => some (s1 ++ s2, σ2)

theorem XStepRel.append_err {r : XResult} (hr : ∀ s m, r ≠ .ok s m) {s1 s2 : List Stmt}
    {σ1 σ2 : SState} (h : XStepRel r (runStmts s1 env) σ1) :
    XStepRel r (runStmts (s1 ++ s2) env) σ2 := by
  rw [runStmts_append]
  cases hrun : runStmts s1 env with
  | error f => rw [hrun] at h; cases r <;> exact h
  | ok env1 =>
    rw [hrun] at h
    cases r with
    | ok s m => exact absurd rfl (hr s m)
    | _ => exact h.elim

theorem symGo_sound : ∀ (instrs : List (LInstr × Nat)) (σ : SState) (env : Env) (s : XState)
    (mem : Memory) (p : List Stmt × SState), XRel σ env s mem → symGo instrs σ = some p →
    XStepRel (execBlock instrs s mem) (runStmts p.1 env) p.2
  | [], σ, env, s, mem, p, h, hs => by cases hs; exact h
  | (i, len) :: rest, σ, env, s, mem, p, h, hs => by
    simp only [symGo] at hs
    split at hs
    · cases hs
    rename_i s1 σ1 h1
    split at hs
    · cases hs
    rename_i s2 σ2 h2
    cases hs
    have hstep := symStep_sound h i len (s1, σ1) h1
    simp only [execBlock]
    cases hr : i.exec s mem len with
    | ok s' m' =>
      rw [hr] at hstep
      simp only
      cases hrun : runStmts s1 env with
      | error f =>
        rw [hrun] at hstep
        exact absurd hstep (by cases f <;> simp [XStepRel, Fault.toX])
      | ok env1 =>
        rw [hrun] at hstep
        rw [runStmts_append, hrun]
        exact symGo_sound rest σ1 env1 s' m' (s2, σ2) hstep h2
    | dataFault => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep
    | divideError => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep
    | undefinedCondition c => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep
    | trap => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep

/-- The sixteen registers, in hardware order. -/
def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

def SState.init : SState := { regs := .reg, flags := .entry, rip := .rip, n := 0 }

/-- The changed entries of a total map, as an association list. -/
def changed {α β : Type} [DecidableEq β] (keys : List α) (f d : α → β) : List (α × β) :=
  keys.filterMap fun q => if f q = d q then none else some (q, f q)

theorem lookup_changed {α β : Type} [DecidableEq α] [DecidableEq β] (f d : α → β) (r : α) :
    ∀ l : List α, ((changed l f d).lookup r).getD (d r) = if r ∈ l then f r else d r
  | [] => by simp [changed]
  | q :: t => by
    have ih := lookup_changed f d r t
    simp only [changed] at ih ⊢
    by_cases hq : q = r
    · subst hq
      by_cases he : f q = d q
      · simp only [List.filterMap_cons, he, ite_true]
        rw [ih]; simp [he]
      · simp [he]
    · by_cases he : f q = d q
      · simp only [List.filterMap_cons, he, ite_true]
        rw [ih]; simp [List.mem_cons, Ne.symm hq]
      · simp only [List.filterMap_cons, he, ite_false, List.lookup]
        have : (r == q) = false := by simpa using Ne.symm hq
        rw [this]; simp only; rw [ih]; simp [List.mem_cons, Ne.symm hq]

def SState.toBlock (sts : List Stmt) (σ : SState) : Block :=
  { stmts := sts, regs := changed allRegs σ.regs .reg, flags := σ.flags, rip := σ.rip,
    xmm := changed (List.finRange 16) σ.xmm (fun i => (.xmm i false, .xmm i true)) }

theorem SState.toBlock_reg (sts : List Stmt) (σ : SState) (r : Reg) :
    (σ.toBlock sts).reg r = σ.regs r := by
  simp only [Block.reg, SState.toBlock, lookup_changed, mem_allRegs, ite_true]

theorem SState.toBlock_xreg (sts : List Stmt) (σ : SState) (i : Fin 16) :
    (σ.toBlock sts).xreg i = σ.xmm i := by
  simp only [Block.xreg, SState.toBlock, lookup_changed, List.mem_finRange, ite_true]

/-- Lift a straight-line block into Bir. -/
def symExec (instrs : List (LInstr × Nat)) : Option Block :=
  (symGo instrs SState.init).map fun p => SState.toBlock p.1 p.2

/-- **The block simulation theorem.** If the symbolic executor accepts a block,
the machine and the Bir block agree on every entry state and memory. -/
theorem symExec_sound {instrs : List (LInstr × Nat)} {b : Block} (hb : symExec instrs = some b)
    (s : XState) (mem : Memory) : execBlock instrs s mem = b.run s mem := by
  simp only [symExec, Option.map_eq_some_iff] at hb
  obtain ⟨⟨sts, σ⟩, hgo, rfl⟩ := hb
  have h0 : XRel SState.init ⟨s.core, [], mem, s.xmm⟩ s mem :=
    { core := { mem := rfl, len := rfl, regs := fun _ => rfl, flags := rfl, rip := rfl, fs := rfl,
                wf := ⟨fun _ => trivial, trivial, trivial⟩ }
      xmm := fun i => by simp [SState.init, E.den, hi64_append_lo64]
      xwf := fun _ => ⟨trivial, trivial⟩ }
  have hrel := symGo_sound instrs _ _ s mem _ h0 hgo
  simp only [Block.run, SState.toBlock]
  revert hrel
  cases hx : execBlock instrs s mem <;> cases hrun : runStmts sts ⟨s.core, [], mem, s.xmm⟩ <;>
    intro hrel <;> simp only [XStepRel] at hrel
  case ok.ok s' m' env' =>
    obtain ⟨⟨hm, -, hregs, hflags, hrip, hfs, -⟩, hxmm, -⟩ := hrel
    subst hm
    congr 1
    obtain ⟨core, xmm⟩ := s'
    simp only [Block.state, XState.mk.injEq]
    constructor
    · cases core
      simp only [State.mk.injEq]
      refine ⟨funext fun r => ?_, hrip, hflags, hfs⟩
      have := SState.toBlock_reg sts σ r
      simp only [SState.toBlock] at this
      rw [this]
      exact hregs r
    · funext i
      have := SState.toBlock_xreg sts σ i
      simp only [SState.toBlock] at this
      rw [this]
      exact hxmm i
  case ok.error f => cases f <;> cases hrel
  all_goals exact hrel

end Silmaril.X86.Lift.Bir
