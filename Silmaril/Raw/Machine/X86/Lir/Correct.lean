module

public import Silmaril.Machine.X86.Lir.Sim.Defs

/-!
# Correctness of the Lir-to-x86-64 backend

`Env.load lm main args init` is the loaded machine: its memory has exactly the
three regions of the space, holds the compiled code at `codeBase`, the return
address `exit` in the eight bytes at `E0`, and the Lir linear memory `lm` at
`memBase`; RSP is `E0`, `r14`/`r15` hold the stack limit and the linear-memory
base, `rbx rbp r12 r13` hold the `saved` values, the arguments are in
`rdi rsi rdx rcx r8 r9`, RIP is the entry of `main`, and every other register
and the flags are those of an arbitrary `init`.

`compile_correct`: if `compile` succeeds, the layout conditions hold, and the
Lir program started at `main` with arguments `args` and linear memory `lm`

* returns values `vs` and memory `m`, then the machine reaches a RET that pops
  `exit` into a state satisfying `Env.Final vs m` (values in `rax rdx`,
  callee-saved registers restored, `m` represented), or stops at the UD2 of a
  stack-limit check;
* traps with memory `m`, then the machine reaches a UD2 with `m` represented,
  or stops at a stack-limit check;
* diverges, then the machine runs forever, or stops at a stack-limit check.

The stack-limit alternative is the only difference between the finite machine
stack and the unbounded Lir stack. Nothing is claimed for Lir executions that
get stuck (undefined behaviour). The machine steps are those of the local
handwritten model `X86.Ext`; `Ext.step` is a function, so the execution these
theorems describe is the execution of the loaded machine.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

/-- The position of an argument register. -/
def argIndex : Reg → Option Nat
  | .rdi => some 0 | .rsi => some 1 | .rdx => some 2 | .rcx => some 3 | .r8 => some 4
  | .r9 => some 5 | _ => none

theorem argIndex_argRegN {j : Nat} (hj : j < 6) : argIndex (argRegN j) = some j := by
  rw [argRegN_lt hj]
  have : ∀ i : Fin 6, argIndex (argReg i) = some i.val := by decide
  exact this ⟨j, hj⟩

namespace Env

variable {P : Type} (E : Env P) [DecidableEq P]

/-- The bytes of the loaded memory. -/
def loadBytes (lm : Lir.Memory) : Process.ByteMemory :=
  Memory.install
    (Memory.install (Memory.install ∅ E.S.codeBase E.code) E.E0 (Ext.leBytes E.exit 8))
    E.S.memBase (List.ofFn fun i : Fin lm.size => lm.bytes i)

/-- The loaded memory: the regions of the space and the loaded bytes. -/
def loadMemory (lm : Lir.Memory) : Memory := ⟨E.S.regions E.code.length, E.loadBytes lm⟩

/-- The initial registers. -/
def loadRegs (args : List Word) (init : State) (r : Reg) : Word :=
  if r = .rsp then BitVec.ofNat 64 E.E0
  else if r = .r14 then BitVec.ofNat 64 E.S.stackLo
  else if r = .r15 then BitVec.ofNat 64 E.S.memBase
  else if r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 then E.saved r
  else match argIndex r with
    | some j => args.getD j 0
    | none => init.read r

/-- The loaded machine at the entry of `main`. -/
def load (lm : Lir.Memory) (main : Lir.FuncId) (args : List Word) (init : State) : MState where
  core := { regs := E.loadRegs args init, rip := BitVec.ofNat 64 (E.L.func main), flags := init.flags }
  memory := E.loadMemory lm

omit [DecidableEq P] in
theorem load_entry (hok : E.Ok) {lm : Lir.Memory} (hsize : lm.size = E.S.memSize)
    (main : Lir.FuncId) {args : List Word} (hargs : args.length ≤ 6) (init : State) :
    E.Entry main args [] lm (E.load lm main args init) E.E0 := by
  have hv := hok.valid
  have hstack := hv.stack_mem
  have hcs := hv.code_stack
  have hcm := hv.code_mem
  have hhi := hok.e0_hi
  have hlo := hok.e0_lo
  have hm := hv.mem_end
  have hread : ∀ r, (E.load lm main args init).core.read r = E.loadRegs args init r := fun _ => rfl
  refine ⟨⟨rfl, fun i hi => ?_⟩, ?_, ?_, ?_, hok.e0_align, hlo, rfl, ⟨hsize, fun a ha => ?_⟩,
    fun j hj => ?_, ⟨rfl, fun i hi => ?_, ?_, ?_, ?_, ?_⟩⟩
  · show (E.loadBytes lm).get? (E.S.codeBase + i) = some E.code[i]
    unfold loadBytes
    rw [Memory.install_outside _ _ _ _ (by simp; omega), Memory.install_outside _ _ _ _ (by simp; omega),
      Memory.install_get _ _ _ _ hi]
  · rw [hread]; simp [loadRegs]
  · rw [hread]; simp [loadRegs]
  · rw [hread]; simp [loadRegs]
  · show (E.loadBytes lm).get? (E.S.memBase + a) = some (lm.bytes a)
    unfold loadBytes
    rw [Memory.install_get _ _ _ _ (by simpa using ha)]
    simp
  · rw [hread]
    have hj6 : j < 6 := by omega
    have hne : ∀ i : Fin 6, argReg i ≠ .rsp ∧ argReg i ≠ .r14 ∧ argReg i ≠ .r15 ∧
        argReg i ≠ .rbx ∧ argReg i ≠ .rbp ∧ argReg i ≠ .r12 ∧ argReg i ≠ .r13 := by decide
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hne ⟨j, hj6⟩
    rw [← argRegN_lt hj6] at h1 h2 h3 h4 h5 h6 h7
    simp only [loadRegs, h1, h2, h3, h4, h5, h6, h7, ite_false, or_self, argIndex_argRegN hj6]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · show (E.loadBytes lm).get? (E.E0 + i) = _
    unfold loadBytes
    rw [Memory.install_outside _ _ _ _ (by simp; omega), Memory.install_get _ _ _ _ (by simpa using hi),
      leBytes_getElem]
  · rw [hread]; simp [loadRegs]
  · rw [hread]; simp [loadRegs]
  · rw [hread]; simp [loadRegs]
  · rw [hread]; simp [loadRegs]

theorem start_match (hok : E.Ok) {lm : Lir.Memory} (hsize : lm.size = E.S.memSize)
    {main : Lir.FuncId} {args : List Word} {s₀ : Lir.State P}
    (hs : E.p.start main args lm = some s₀) (init : State) :
    ∃ t₁, TransGen (RStep E.exit) (E.load lm main args init) t₁ ∧ E.Match s₀ t₁ := by
  simp only [Lir.Prog.start, Option.map_eq_some_iff] at hs
  obtain ⟨⟨pt, fr⟩, he, rfl⟩ := hs
  obtain ⟨fn, hfn, hfr, rfl⟩ := E.enter_eq he
  have hargs : args.length ≤ 6 := by
    rw [writeAll_length _ _ _ hfr]; exact (funcOk hok.errors hfn).params
  obtain ⟨t₁, st, h⟩ := E.sim_entry hok hfn (E.load_entry hok hsize main hargs init) hfr
  rcases h with hov | hb
  · exact ⟨t₁, st, .inr hov⟩
  · exact ⟨t₁, st, .inl ⟨_, hb⟩⟩

theorem transGen_infinite {R : MState → MState → Prop} {a b : MState} (h : TransGen R a b)
    (hb : InfiniteTrace R b) : InfiniteTrace R a := by
  induction h with
  | single hs => exact InfiniteTrace.fold hs hb
  | tail _ hs ih => exact ih (InfiniteTrace.fold hs hb)

/-- The three preserved behaviours, for the loaded machine. -/
theorem behaviours (hok : E.Ok) {lm : Lir.Memory} (hsize : lm.size = E.S.memSize)
    {main : Lir.FuncId} {args : List Word} {s₀ : Lir.State P}
    (hs : E.p.start main args lm = some s₀) (init : State) :
    (∀ vs m, Lir.Behaves E.p s₀ (.returned vs m) →
      ∃ t', ReflTransGen (RStep E.exit) (E.load lm main args init) t' ∧ E.Returned vs m t') ∧
    (∀ m, Lir.Behaves E.p s₀ (.trapped m) →
      ∃ t', ReflTransGen (RStep E.exit) (E.load lm main args init) t' ∧ E.Trapped m t') ∧
    (Lir.Behaves E.p s₀ .diverges →
      InfiniteTrace (RStep E.exit) (E.load lm main args init) ∨
        ∃ t', ReflTransGen (RStep E.exit) (E.load lm main args init) t' ∧ E.Overflow t') := by
  obtain ⟨t₁, st, hm⟩ := E.start_match hok hsize hs init
  refine ⟨fun vs m hb => ?_, fun m hb => ?_, fun hb => ?_⟩
  · obtain ⟨t', h, r⟩ := (E.simulation hok).toForward.returns hm hb
    exact ⟨t', st.to_reflTransGen.trans (E.tsteps_rsteps h), r⟩
  · obtain ⟨t', h, r⟩ := (E.simulation hok).toForward.traps hm hb
    exact ⟨t', st.to_reflTransGen.trans (E.tsteps_rsteps h), r⟩
  · rcases E.tdiverges ((E.simulation hok).toForward.diverges hm hb) with hd | ⟨t', h, hov⟩
    · exact .inl (transGen_infinite st hd)
    · exact .inr ⟨t', st.to_reflTransGen.trans h, hov⟩

end Env

theorem compile_ok {P : Type} {A : Assign P} {p : Lir.Prog P} {codeBase : Nat} {img : Image}
    (h : compile A p codeBase = .ok img) :
    progErrors A p = [] ∧ img.code = encodeAt (layout A p codeBase) codeBase (progCode A p) ∧
      img.layout = layout A p codeBase := by
  unfold compile at h
  split at h
  · rename_i he
    cases h
    exact ⟨he, rfl, rfl⟩
  · cases h

/-- **Correctness of the backend.** If `compile` succeeds on a Lir program, the
memory layout is valid for the produced code, the initial stack pointer `E0`
is in the stack with the System V alignment and `exit` is outside the code,
then every returning, trapping or diverging Lir run from `main` is matched by
the loaded machine holding exactly the compiled bytes, up to a stop at a
stack-limit check. -/
theorem compile_correct {P : Type} [DecidableEq P] (A : Assign P) (p : Lir.Prog P) (S : Space)
    {img : Image} (hc : compile A p S.codeBase = .ok img) (hvalid : S.Valid img.code.length)
    (exit : Word) (E0 : Nat) (saved : Reg → Word) (hhi : E0 + 8 ≤ S.stackHi) (hlo : S.stackLo ≤ E0)
    (halign : E0 % 16 = 8)
    (hexit : exit.toNat < S.codeBase ∨ S.codeBase + img.code.length ≤ exit.toNat)
    {lm : Lir.Memory} (hsize : lm.size = S.memSize) {main : Lir.FuncId} {args : List Word}
    {s₀ : Lir.State P} (hs : p.start main args lm = some s₀) (init : State) :
    let E : Env P := ⟨A, p, S, exit, E0, saved⟩
    (E.load lm main args init).memory.bytes = E.loadBytes lm ∧
    E.code = img.code ∧
    (∀ vs m, Lir.Behaves p s₀ (.returned vs m) →
      ∃ t', ReflTransGen (RStep exit) (E.load lm main args init) t' ∧ E.Returned vs m t') ∧
    (∀ m, Lir.Behaves p s₀ (.trapped m) →
      ∃ t', ReflTransGen (RStep exit) (E.load lm main args init) t' ∧ E.Trapped m t') ∧
    (Lir.Behaves p s₀ .diverges →
      InfiniteTrace (RStep exit) (E.load lm main args init) ∨
        ∃ t', ReflTransGen (RStep exit) (E.load lm main args init) t' ∧ E.Overflow t') := by
  intro E
  obtain ⟨herr, hcode, -⟩ := compile_ok hc
  have hcode' : E.code = img.code := hcode.symm
  have hok : E.Ok := ⟨herr, hcode' ▸ hvalid, hhi, hlo, halign, hcode' ▸ hexit⟩
  exact ⟨rfl, hcode', E.behaviours hok hsize hs init⟩

end Silmaril.X86.Backend
