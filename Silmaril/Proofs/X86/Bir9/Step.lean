module

public import Silmaril.Proofs.X86.Bir9.Exec

/-!
# The symbolic step, instruction by instruction

`symStep σ i len` is the symbolic counterpart of `LInstr.exec i s mem len`;
`symStep_sound` relates them. Each instruction's symbolic form is assembled
from the helpers of `Exec.lean` (`sRead`, `sWriteRM`, `sWriteN`) in the same
order `Silmaril.X86.Ext.exec` calls `readRM`, `writeRM`, `writeNarrow`, so each case of
the proof is the corresponding composition of their lemmas.
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## Width lemmas -/

theorem setWidth_64_setWidth {w : Nat} (hw : w ≤ 64) (x : BitVec w) :
    (x.setWidth 64).setWidth w = x := by
  rw [BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]

theorem Sz.bits_le (sz : Sz) : sz.bits ≤ 64 := by cases sz <;> decide

theorem Narrow.bits_le (n : Narrow) : n.bits ≤ 64 := by cases n <;> decide

theorem setWidth_signExtend_of_le {w k l : Nat} (x : BitVec w) (h : k ≤ l) :
    (x.signExtend l).setWidth k = x.signExtend k := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getElem_signExtend, BitVec.getLsbD_signExtend]
  split <;> simp_all <;> omega

/-! ## Small state lemmas -/

theorem nxOf_den {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (len : Nat) : (nxOf σ len).den env = s.rip + BitVec.ofNat 64 len := by
  rw [nxOf, addImm_den, h.rip]

theorem nxOf_wf {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (len : Nat) : (nxOf σ len).wf env.vals.length := by
  rw [h.len]; exact addImm_wf h.wf.2.2 _

theorem Rel.setReg' {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (r : Reg) {e : E} (he : e.wf σ.n) {v : Word} (hv : v = e.den env) :
    Rel (σ.setReg r e) env (s.write r v) mem := hv ▸ h.setReg r e he

theorem Rel.setFlags' {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {f : F} (hf : f.wf σ.n) {fl : Flags} (hfl : fl = f.den env) :
    Rel { σ with flags := f } env { s with flags := fl } mem := hfl ▸ h.setFlags f hf

theorem Rel.setRip' {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {e : E} (he : e.wf σ.n) {v : Word} (hv : v = e.den env) :
    Rel { σ with rip := e } env { s with rip := v } mem := hv ▸ h.setRip e he

theorem StepRel.ok_of {env env' : Env} {sts : List Stmt} {σ' : SState} {s' : State} {m' : Memory}
    (hrun : runStmts sts env = .ok env') (h : Rel σ' env' s' m') :
    StepRel (.ok s' m') (runStmts sts env) σ' := by
  rw [hrun]; exact h

theorem wf_lift {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {e : E} (he : e.wf σ.n) : e.wf env.vals.length := h.len ▸ he

/-- The general shape: a read then a continuation that is sound. -/
theorem read_then {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {nx : E} {next : Word} (hnx : nx.den env = next) (op : RM) (k : Nat) (sts : List Stmt)
    (σ' : SState) (fault : Result) (hfault : fault = .dataFault)
    (cont : Word → Result)
    (hcont : ∀ x env1, runStmts (sRead σ nx k op).1 env = .ok env1 →
      ReadOK σ (sRead σ nx k op).2.2 env env1 s mem (sRead σ nx k op).2.1 →
      x = (sRead σ nx k op).2.1.den env1 → StepRel (cont x) (runStmts sts env1) σ') :
    StepRel (match rawRead op s mem next k with
      | none => fault
      | some x => cont x) (runStmts ((sRead σ nx k op).1 ++ sts) env) σ' := by
  cases hr : rawRead op s mem next k with
  | none =>
    subst hfault
    rw [runStmts_append, sRead_none h hnx hr]
    rfl
  | some x =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    exact StepRel.prepend hrun (hcont x env1 hrun hok hx)

theorem ReadOK.den_eq {σ σ1 : SState} {env env1 : Env} {s : State} {mem : Memory} {e : E}
    (hok : ReadOK σ σ1 env env1 s mem e) (h : Rel σ env s mem) {y : E} (hy : y.wf σ.n) :
    y.den env1 = y.den env := E.den_ext hok.ext (wf_lift h hy)

theorem ReadOK.fden_eq {σ σ1 : SState} {env env1 : Env} {s : State} {mem : Memory} {e : E}
    (hok : ReadOK σ σ1 env env1 s mem e) (h : Rel σ env s mem) {f : F} (hf : f.wf σ.n) :
    f.den env1 = f.den env := F.den_ext hok.ext (h.len ▸ hf)

theorem ReadOK.mono {σ σ1 : SState} {env env1 : Env} {s : State} {mem : Memory} {e : E}
    (hok : ReadOK σ σ1 env env1 s mem e) (h : Rel σ env s mem) : σ.n ≤ σ1.n := by
  rw [← hok.rel.len, ← h.len]; exact hok.len

theorem ReadOK.wf_of {σ σ1 : SState} {env env1 : Env} {s : State} {mem : Memory} {e : E}
    (hok : ReadOK σ σ1 env env1 s mem e) (h : Rel σ env s mem) {y : E} (hy : y.wf σ.n) :
    y.wf σ1.n := E.wf_mono (hok.mono h) hy

theorem ReadOK.fwf_of {σ σ1 : SState} {env env1 : Env} {s : State} {mem : Memory} {e : E}
    (hok : ReadOK σ σ1 env env1 s mem e) (h : Rel σ env s mem) {f : F} (hf : f.wf σ.n) :
    f.wf σ1.n := F.wf_mono (hok.mono h) hf

theorem ReadOK.nx {σ σ1 : SState} {env env1 : Env} {s : State} {mem : Memory} {e : E}
    (hok : ReadOK σ σ1 env env1 s mem e) (h : Rel σ env s mem) (len : Nat) :
    (nxOf σ len).den env1 = s.rip + BitVec.ofNat 64 len := by
  rw [E.den_ext hok.ext (nxOf_wf h len)]; exact nxOf_den h len

theorem ReadOK.nxw {σ σ1 : SState} {env env1 : Env} {s : State} {mem : Memory} {e : E}
    (hok : ReadOK σ σ1 env env1 s mem e) (h : Rel σ env s mem) (len : Nat) :
    (nxOf σ len).wf σ1.n := hok.wf_of h (addImm_wf h.wf.2.2 _)

theorem nxOf_wfn {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (len : Nat) : (nxOf σ len).wf σ.n := addImm_wf h.wf.2.2 _

/-! ## ALU -/

theorem sAlu_sound {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (len : Nat) (sz : Sz) (op : AluOp) (dst : RM) {y : E} (hy : y.wf σ.n)
    {yv : BitVec sz.bits} (hyv : yv = (y.den env).setWidth sz.bits) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len)
        (aluStep sz op dst yv s mem (s.rip + BitVec.ofNat 64 len)))
      (runStmts (sAlu σ len sz op dst y).1 env) (sAlu σ len sz op dst y).2 := by
  have hnx := nxOf_den h len
  simp only [aluStep, readRM_eq]
  cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
  | none =>
    simp only [Option.map_none, retire, sAlu]
    split <;> (rw [runStmts_append, sRead_none h hnx hr]; rfl)
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    have hyd := hok.den_eq h hy
    have hfl : AluOp.flagsN op (xw.setWidth sz.bits) yv =
        (F.alu sz.bits op (sRead σ (nxOf σ len) sz.bytes dst).2.1 y).den env1 := by
      simp only [F.den, ← hx, hyd, hyv]
    have hflw : (F.alu sz.bits op (sRead σ (nxOf σ len) sz.bytes dst).2.1 y).wf env1.vals.length := by
      rw [hok.rel.len]; exact ⟨hok.wf, hok.wf_of h hy⟩
    simp only [Option.map_some, sAlu]
    by_cases hop : op = .cmp
    · simp only [hop, ite_true]
      apply StepRel.prepend hrun
      subst hop
      exact (ORel.pure (hok.rel.setFlags' (f := .alu sz.bits .cmp _ y) (by rw [← hok.rel.len]; exact hflw) hfl)).retire
        (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)
    · simp only [hop, ite_false]
      apply StepRel.prepend hrun
      have hv : AluOp.resultN op (xw.setWidth sz.bits) yv =
          ((E.alu sz.bits op (sRead σ (nxOf σ len) sz.bytes dst).2.1 y).den env1).setWidth sz.bits := by
        simp only [E.den, ← hx, hyd, hyv, setWidth_64_setWidth (Sz.bits_le sz)]
      rw [hv, hfl]
      have hw := sWriteRM_sound hok.rel (hok.nx h len) (hok.nxw h len) sz dst
        (e := .alu sz.bits op (sRead σ (nxOf σ len) sz.bytes dst).2.1 y) ⟨hok.wf, hok.wf_of h hy⟩
      have := (hw.flags _ hflw).retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)
      simpa using this

/-! ## Generic shapes -/

theorem ORel.jump {env : Env} {o : Option (State × Memory)} {sts : List Stmt} {σ' : SState}
    (h : ORel env o sts σ') {t : E} {X : Word} (hX : t.den env = X) (hw : t.wf env.vals.length) :
    StepRel (match o with
      | none => .dataFault
      | some (u, m) => .ok { u with rip := X } m) (runStmts sts env) { σ' with rip := t } := by
  cases o with
  | none => exact StepRel.fault h
  | some p =>
    obtain ⟨u, m⟩ := p
    obtain ⟨env', h2, hr⟩ := h
    have hx := runStmts_ext h2
    simp only [StepRel, h2]
    have := hr.setRip t (hr.len ▸ E.wf_mono hx.len hw)
    rwa [E.den_ext hx hw, hX] at this

/-- Pure instructions: one new state, no statements. -/
theorem pure_sound {σ σ' : SState} {env : Env} {s s' : State} {mem : Memory}
    (h : Rel σ env s mem) (len : Nat) (h' : Rel σ' env s' mem) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len) (some (s', mem))) (runStmts [] env)
      { σ' with rip := nxOf σ len } :=
  (ORel.pure h').retire (nxOf_den h len) (nxOf_wf h len)

theorem sPush_sound {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {val : E} {v : Word} (hv : v = val.den env) :
    ORel env (pushWord s mem v) [sPushStmt σ val] (sPushState σ) := by
  simp only [pushWord, ORel, sPushStmt]
  have ha : (E.sub (σ.regs .rsp) (.imm 8#64)).den env = s.read .rsp - 8#64 := by
    simp only [E.den, h.regs]
  cases hw : mem.writeBytes (s.read .rsp - 8#64).toNat (encodeWords [v]) with
  | none => simp only [Option.map_none, runStmts, Stmt.run, ha, h.mem, ← hv, hw]
  | some m' =>
    refine ⟨{ env with mem := m' }, by simp only [runStmts, Stmt.run, ha, h.mem, ← hv, hw], ?_⟩
    refine (h.store (m' := m')).setReg' .rsp (by simp [E.wf, h.wf.1 .rsp]) ?_
    simp only [E.den, ← (h.store (m' := m')).regs]

theorem popWord_eq (s : State) (mem : Memory) :
    popWord s mem = ((mem.readBytes (s.read .rsp).toNat 8).bind wordOfBytes?).map
      fun v => (v, s.write .rsp (s.read .rsp + 8#64)) := by
  unfold popWord
  cases mem.readBytes (s.read .rsp).toNat 8 with
  | none => rfl
  | some b => cases hb : wordOfBytes? b <;> simp [hb]

theorem sPop_none {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (hp : popWord s mem = none) : runStmts [.pop (σ.regs .rsp)] env = .error .data := by
  rw [popWord_eq] at hp
  simp only [Option.map_eq_none_iff] at hp
  simp [runStmts, Stmt.run, ← h.regs, h.mem, hp]

theorem sPop_some {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {v : Word} {t : State} (hp : popWord s mem = some (v, t)) :
    runStmts [.pop (σ.regs .rsp)] env = .ok (env.push v) ∧
      Rel (sPopState σ) (env.push v) t mem ∧ v = (E.v σ.n).den (env.push v) := by
  rw [popWord_eq] at hp
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hp
  obtain ⟨w, hw, rfl, rfl⟩ := hp
  refine ⟨by simp [runStmts, Stmt.run, ← h.regs, h.mem, hw], ?_, ?_⟩
  · refine (h.push w).setReg' .rsp (by simp [E.wf, SState.fresh]; exact E.wf_mono (Nat.le_succ _) (h.wf.1 .rsp)) ?_
    simp only [E.den]
    rw [E.den_ext (env.ext_push w) (wf_lift h (h.wf.1 .rsp)), ← h.regs]
  · simp [E.den, Env.push, h.len]

theorem sCond_none {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {c : Cond} (hc : c.eval s.flags = none) :
    runStmts [.cond c σ.flags] env = .error (.undef c) := by
  simp [runStmts, Stmt.run, ← h.flags, hc]

theorem sCond_some {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {c : Cond} {b : Bool} (hc : c.eval s.flags = some b) :
    runStmts [.cond c σ.flags] env = .ok (env.push (if b then 1#64 else 0#64)) := by
  simp [runStmts, Stmt.run, ← h.flags, hc]

theorem cond_den (b : Bool) (n : Nat) (env : Env) (hn : env.vals.length = n) :
    (E.v n).den (env.push (if b then 1#64 else 0#64)) = if b then 1#64 else 0#64 := by
  simp [E.den, Env.push, hn]

end Silmaril.X86.Bir9
