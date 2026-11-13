module

public import Silmaril.Machine.CBackend.RTL.ToLir.Defs
public import Silmaril.Machine.CBackend.RTL.Behaviour.Defs
public import Silmaril.Machine.CBackend.Lir.Alloc.Defs
public import Silmaril.Machine.X86.Lir.Correct.Defs
public import Silmaril.X86.CallingConvention

/-!
# Compiled RTL implements its source at `sysv64`

The composition of the three passes this repository has between an RTL
control-flow graph and an x86-64 image,

```
RTL.Prog Nat  --toLir-->  Lir.Prog Nat  --Alloc.spill (firstK k)-->
    Lir.Prog (Fin (k+2))  --X86.Backend.compile-->  Image
```

restated as a single instance of the compilation relation
`Silmaril.Machine.Behaviour.Implements`, at the System V AMD64 calling
convention `Silmaril.X86.sysv64`.

**No existing statement changes.** `implements_sysv64` is proved from
`RTL.toLir_behaves`, `Lir.Alloc.spill_behaves` and
`X86.Backend.compile_correct`, each used as it stands.

## The shape of the instance

* **Source.** `RTL.sem p` (`Silmaril/Machine/RTL/Behaviour.lean`): RTL as a
  `Behaviour.Semantics`, with stuck mapped to the `undefined` outcome, so
  `Safe` is "does not get stuck" (`safe_iff_not_stuck`). Deterministic, and
  every state has a behaviour.
* **Target.** `tgtSem E`: the machine stepping by `RStep E.exit`, with three
  kinds of final state — a RET to `exit` (`returned`), a UD2 that is not the
  stack-limit check (`trapped`), and the UD2 *of* the stack-limit check
  (`exhausted`). Every other outcome of `Silmaril.X86.Ext.step` — `undefinedCondition`,
  `divideFault`, `dataFault`, `fetchFault`, `undecodable` — is left non-final,
  hence stuck, hence without behaviour; `live` is the theorem that the compiled
  code never reaches such a state.
* **Call data.** A `CallData` is a function identifier, argument words, an
  initial linear memory, the RTL start state, and the machine registers
  `Env.load` does not set. Carrying the start state in the call datum is what
  makes `entryState` a *total* function, which `Implements` requires, with no
  junk state for calls to missing functions.
* **Mode.** `⟨.strict, .allowed⟩`, for the reason
  `Silmaril/Wasm/Compile/ImplementsX86.lean` gives: strict on the failure axis,
  because the backend turns no divergence into a trap and no trap into a
  divergence; `allowed` on the exhaustion axis, because the finite machine
  stack can stop a run that RTL's unbounded stack would have continued, and
  that stop — the stack-limit UD2 — is a *resource* outcome that may stand for
  any source outcome.
* **Observation.** A return is observed by `Env.Final`: the returned words in
  `sysv64.intRetRegs`, the callee-saved registers restored, the stack pointer
  popped by `sysv64.linkSize`, and the final RTL memory at `memBase`.
  `final_retReg`, `final_preserved` and `final_rsp` below read those three
  clauses back in `sysv64`'s own vocabulary. A trap is observed by `MemRel`:
  the memory at the trap. RTL has no faults, so the fault payload is `Empty`.

## Where `sysv64` enters

`halign` is stated as `Silmaril.X86.sysv64.EntryAligned E0` rather than
`E0 % 16 = 8`. The two are definitionally equal (`sysv64_entryAligned_iff` is
`Iff.rfl`), so the hypothesis is passed unchanged to `compile_correct`; what
changes is that the constant `16` and the residue `8` come from
`sysv64.stackAlign` and `sysv64.entryResidue` instead of being written out.

## Why `Admissible` asks for a safe source, and why that is not a weakening

`Admissible` carries a third conjunct, `¬ Behaves p c.start .stuck`: the call
must not get stuck. `Silmaril/Wasm/Compile/ImplementsX86.lean` needs no such
conjunct because its source subset is safe everywhere (`srcSem_safe`). **RTL
has undefined behaviour by design** — division by zero, out-of-bounds memory
accesses and reads of unwritten registers are all stuck, deliberately, so that
backends need no checks for them — and a source that may go wrong has no claim
on its target. `Implements.Live` carries no safety premise of its own, so the
condition has to live in `Admissible`; without it `live` is simply false, since
`compile_correct` says nothing about a stuck Lir run and the machine may sit at
any state at all.

**`implements_sysv64` is not weakened by this.** `Implements` already carries
`src.Safe (entry c)` as a hypothesis of its own, so the headline theorem has
exactly the strength it would have had with the original `Admissible`. The
conjunct changes only which calls `nonvacuous_sysv64` certifies, and that is
the honest scope: the instance is non-vacuous *for safe calls*, and an RTL
program with undefined behaviour is outside it.

## Why the vacuity machinery matters here

`Implements` constrains only the behaviours a target *has*, so it holds
trivially of a target that always gets stuck and of an empty `Represents`. Both
escapes are closed: `represented` — every admissible call has a representing
machine state, namely `Env.load` — and `live` — no state reachable from
`Env.load` is stuck, which is what rules out the five fault outcomes above.
`nonvacuous_sysv64` bundles the two, `exists_beh_sysv64` is what the instance
then delivers for a concrete call, and, since RTL is deterministic,
`exactly_sysv64` upgrades the instance to `Implements.Exactly`.
`Silmaril/Machine/RTL/ToLirExamples.lean` instantiates `exists_beh_sysv64` on
the compiled factorial with every hypothesis discharged, so that the hypothesis
set is visibly inhabited rather than taken on faith.

## RISC-V

Not provided. `Silmaril/RiscV/Lir/Loader.lean` has the matching
`spill_compile_correct`, so the *correctness* half would compose as cheaply as
the x86 one; what does not come for free is the `Implements` packaging, which
needs an RV64 `tgtSem` whose three final program counters are provably distinct
(the RV64 machine always stops the same way and discriminates on the program
counter) and an RV64 `live`. That is a file of its own, not a few lines here.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.X86

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.Behaviour (Semantics Obs Mode Implements Outcome)
open Silmaril.X86 (MState Reg)
open Silmaril.X86.Backend (Space Env RStep MemRel Assign Image compile compile_correct)
open Relation

variable {V : Type} [DecidableEq V]

/-! ## The pipeline -/

/-- The Lir program compiled for an RTL program: lowered one block per node,
then allocated onto `k + 2` physical registers by `a`.

The allocation is a parameter rather than `Lir.Alloc.firstK`, and the source
register type is arbitrary rather than `Nat`, because
`Silmaril/Machine/Pipeline.lean` feeds this pipeline a program over `Nat ⊕ Nat`:
`RTL.SSA.sequentialize` needs a supply of fresh registers and takes one by
widening the register type. `Lir.Alloc.Allocation` was already generic in both
types and `Lir.Alloc.spill_behaves` already quantifies over them, so this is a
change of signature and not of proof. `Lir.Alloc.firstK k` is the instance
`Silmaril/Machine/RTL/ToLirExamples.lean` uses. -/
def lirOf {k : Nat} (a : Lir.Alloc.Allocation V (Fin (k + 2))) (p : Prog V) :
    Lir.Prog (Fin (k + 2)) :=
  Lir.Alloc.spill a (toLir p)

/-- The environment of a compiled run: the canonical register assignment, the
compiled Lir program, the memory layout, the designated return address `exit`,
the entry stack pointer `E0` and the callee-saved values at entry. -/
def env {k : Nat} (hk : k + 2 ≤ 9) (a : Lir.Alloc.Allocation V (Fin (k + 2))) (p : Prog V)
    (S : Space) (exit : Silmaril.X86.Word) (E0 : Nat) (saved : Reg → Silmaril.X86.Word) :
    Env (Fin (k + 2)) :=
  ⟨Assign.fin (k + 2) hk, lirOf a p, S, exit, E0, saved⟩

omit [DecidableEq V] in
@[simp] theorem env_exit {k : Nat} {hk : k + 2 ≤ 9} {a : Lir.Alloc.Allocation V (Fin (k + 2))}
    {p : Prog V} {S : Space} {exit : Silmaril.X86.Word} {E0 : Nat}
    {saved : Reg → Silmaril.X86.Word} :
    (env hk a p S exit E0 saved).exit = exit := rfl

/-! ## The call data -/

/-- Everything that varies from one call of a compiled RTL program to the next:
the function, its arguments, the initial linear memory, the RTL state the call
starts from, and the machine registers `Env.load` does not set. -/
structure CallData (V : Type) where
  /-- The RTL function being called. -/
  f : FuncId
  /-- The argument words. -/
  args : List Word
  /-- The initial linear memory. -/
  mem : Memory
  /-- The RTL state the call starts from. -/
  start : State V
  /-- Registers and flags not set by `Env.load`. -/
  init : Silmaril.X86.State

/-- The source state a call starts from. -/
def entryState (c : CallData V) : State V := c.start

/-- A call the compiled program is contracted to run: `start` really is the
start state of the call, the linear memory has the size the layout declares,
and **the call does not get stuck**.

The third conjunct is what distinguishes this from
`Silmaril/Wasm/Compile/ImplementsX86.lean`, whose source subset is safe
everywhere and therefore needs no such condition. RTL has undefined behaviour
by design — division by zero, out-of-bounds memory and reads of unwritten
registers are stuck, deliberately, so that backends need no checks for them —
and a source that may go wrong has no claim on its target. `Implements.Live`
has no safety premise of its own, so the condition lives here; without it
`live` is false. It does not weaken `implements_sysv64`, which carries
`src.Safe (entry c)` already. -/
def Admissible (p : Prog V) (msize : Nat) (c : CallData V) : Prop :=
  p.start c.f c.args c.mem = some c.start ∧ c.mem.size = msize ∧
    ¬ Behaves p c.start .stuck

/-- The loaded machine of a call: the compiled code at `codeBase`, `exit` in
the eight bytes at `E0`, the RTL linear memory at `memBase`, the arguments in
the System V argument registers and RIP at the entry of the called function. -/
def loaded {k : Nat} (hk : k + 2 ≤ 9) (a : Lir.Alloc.Allocation V (Fin (k + 2))) (p : Prog V)
    (S : Space) (exit : Silmaril.X86.Word) (E0 : Nat) (saved : Reg → Silmaril.X86.Word)
    (c : CallData V) : MState :=
  (env hk a p S exit E0 saved).load c.mem c.f c.args c.init

/-! ## The target semantics -/

/-- The compiled program as a small-step semantics with behaviours. A state is
final in exactly three ways: the RET to `exit`, a UD2 that is not the
stack-limit check, and the UD2 of the stack-limit check, which is the
*resource* outcome `exhausted`. Fault outcomes are not final, so a state that
faults is stuck and has no behaviour; `live` shows the compiled code never
reaches one. -/
def tgtSem {P : Type} (E : Env P) : Semantics MState MState MState Empty where
  step := RStep E.exit
  final t o :=
    (∃ u, Silmaril.X86.Ext.step E.exit t = .returned u ∧ o = .returned u) ∨
      (Silmaril.X86.Ext.step E.exit t = .trapped ∧ ¬ E.Overflow t ∧ o = .trapped t) ∨
      (E.Overflow t ∧ o = .exhausted)

@[simp] theorem tgtSem_step {P : Type} (E : Env P) : (tgtSem E).step = RStep E.exit := rfl

/-- One retiring machine step has at most one successor: `Silmaril.X86.Ext.step` is a
function and `.retired` is injective. -/
theorem rstep_rightUnique (exit : Silmaril.X86.Word) : Relator.RightUnique (RStep exit) := by
  intro a b c hb hc
  unfold RStep at hb hc
  rw [hb] at hc
  cases hc
  rfl

/-- A machine state whose outcome is not `.retired` cannot step. -/
theorem no_step {exit : Silmaril.X86.Word} {t : MState} {o : Silmaril.X86.Ext.Outcome}
    (h : Silmaril.X86.Ext.step exit t = o) (hn : ∀ x, o ≠ .retired x) : ∀ x, ¬ RStep exit t x :=
  fun x hx => hn x (h ▸ hx)

/-- A final state cannot step: each of the three cases pins `Silmaril.X86.Ext.step` to
`.returned` or `.trapped`, neither of which is `.retired`. -/
theorem tgtSem_final_stop {P : Type} {E : Env P} {t : MState} {o : Outcome MState MState Empty}
    (h : (tgtSem E).final t o) : ∀ x, ¬ RStep E.exit t x := by
  rcases h with ⟨u, hs, -⟩ | ⟨hs, -, -⟩ | ⟨hov, -⟩
  · exact no_step hs (by intro x e; cases e)
  · exact no_step hs (by intro x e; cases e)
  · exact no_step hov.1 (by intro x e; cases e)

/-- The target is deterministic: `RStep` is right-unique, the three final cases
are mutually exclusive, and a final state does not step. -/
theorem tgtSem_deterministic {P : Type} (E : Env P) : (tgtSem E).Deterministic where
  step_unique := rstep_rightUnique E.exit
  final_unique t o o' h h' := by
    have hno : ∀ {u : MState}, Silmaril.X86.Ext.step E.exit t = .returned u → ¬ E.Overflow t := fun hs hov => by
      have h1 : Silmaril.X86.Ext.step E.exit t = .trapped := hov.1
      rw [hs] at h1; cases h1
    have htr : ∀ {u : MState}, Silmaril.X86.Ext.step E.exit t = .returned u →
        Silmaril.X86.Ext.step E.exit t ≠ .trapped := fun hs hs' => by rw [hs] at hs'; cases hs'
    rcases h with ⟨u, hs, rfl⟩ | ⟨hs, hnov, rfl⟩ | ⟨hov, rfl⟩
    · rcases h' with ⟨u', hs', rfl⟩ | ⟨hs', -, rfl⟩ | ⟨hov', rfl⟩
      · rw [hs] at hs'; cases hs'; rfl
      · exact absurd hs' (htr hs)
      · exact absurd hov' (hno hs)
    · rcases h' with ⟨u', hs', rfl⟩ | ⟨-, -, rfl⟩ | ⟨hov', rfl⟩
      · exact absurd hs (htr hs')
      · rfl
      · exact absurd hov' hnov
    · rcases h' with ⟨u', hs', rfl⟩ | ⟨-, hnov', rfl⟩ | ⟨-, rfl⟩
      · exact absurd hov (hno hs')
      · exact absurd hov hnov'
      · rfl
  final_stop _ _ h := tgtSem_final_stop h

/-! ## The instance -/

/-- The machine state representing a call: the one `Env.load` produces, for an
admissible call. -/
def Represents {k : Nat} (hk : k + 2 ≤ 9) (a : Lir.Alloc.Allocation V (Fin (k + 2)))
    (p : Prog V) (S : Space) (exit : Silmaril.X86.Word) (E0 : Nat)
    (saved : Reg → Silmaril.X86.Word) (msize : Nat) (c : CallData V) (t : MState) : Prop :=
  Admissible p msize c ∧ t = loaded hk a p S exit E0 saved c

/-- How payloads are compared. A return is observed by `Env.Final`: the
returned words in the System V result registers, the callee-saved registers
restored, the stack pointer popped by `sysv64.linkSize` and the final RTL
memory at `memBase`. A trap is observed by `MemRel`: the memory at the trap.
RTL has no faults. -/
def obs {k : Nat} (hk : k + 2 ≤ 9) (a : Lir.Alloc.Allocation V (Fin (k + 2))) (p : Prog V)
    (S : Space) (exit : Silmaril.X86.Word) (E0 : Nat) (saved : Reg → Silmaril.X86.Word)
    (_c : CallData V) (_t : MState) : Obs MState Ret MState Memory Empty Empty where
  ret final r := (env hk a p S exit E0 saved).Final r.1 r.2 final
  trap u mem' := MemRel S mem' u.memory
  fault e _ := e.elim

section Instance

variable {k : Nat} {hk : k + 2 ≤ 9} {a : Lir.Alloc.Allocation V (Fin (k + 2))}
  (hv : a.Valid) {p : Prog V} {S : Space} {img : Image}
  (hc : compile (Assign.fin (k + 2) hk) (lirOf a p) S.codeBase = .ok img)
  (hS : S.Valid img.code.length) {exit : Silmaril.X86.Word} {E0 : Nat}
  {saved : Reg → Silmaril.X86.Word} (hhi : E0 + 8 ≤ S.stackHi) (hlo : S.stackLo ≤ E0)
  (halign : Silmaril.X86.sysv64.EntryAligned E0)
  (hexit : exit.toNat < S.codeBase ∨ S.codeBase + img.code.length ≤ exit.toNat)
include hv hc hS hhi hlo halign hexit

/-- **The three preserved behaviours of a compiled RTL program.** The
composition of `toLir_behaves`, `Lir.Alloc.spill_behaves` and `compile_correct`:
every returning, trapping and diverging RTL run of an admissible call is matched
by the loaded machine, up to a stop at the stack-limit check. -/
theorem compiled_behaviours {c : CallData V} (hadm : Admissible p S.memSize c) :
    (∀ vs m, Behaves p c.start (.returned vs m) →
      ∃ t', ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) t' ∧
        (env hk a p S exit E0 saved).Returned vs m t') ∧
    (∀ m, Behaves p c.start (.trapped m) →
      ∃ t', ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) t' ∧
        (env hk a p S exit E0 saved).Trapped m t') ∧
    (Diverges p c.start →
      InfiniteTrace (RStep exit) (loaded hk a p S exit E0 saved c) ∨
        ∃ t', ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) t' ∧
          (env hk a p S exit E0 saved).Overflow t') := by
  obtain ⟨hstart, hsize, -⟩ := hadm
  have hlir : (toLir p).start c.f c.args c.mem = some (toState c.start) := toLir_start hstart
  obtain ⟨t₀, ht₀, -⟩ := Lir.Alloc.spill_start hv hlir
  have hspill : (lirOf a p).start c.f c.args c.mem = some t₀ := ht₀
  have same : ∀ {b : Behavior}, Behaves p c.start b → b ≠ .stuck →
      Lir.Behaves (lirOf a p) t₀ (toLirBehavior b) := by
    intro b hb hns
    have hns' : toLirBehavior b ≠ .stuck := by cases b <;> simp_all [toLirBehavior]
    obtain ⟨t, ht, hb'⟩ :=
      Lir.Alloc.spill_behaves hv hlir (toLir_behaves hb hns) hns'
    have : t = t₀ := Option.some.inj ((ht.symm.trans hspill))
    exact this ▸ hb'
  obtain ⟨-, -, hret, htrap, hdiv⟩ :=
    compile_correct (Assign.fin (k + 2) hk) (lirOf a p) S hc hS exit E0 saved hhi hlo halign
      hexit hsize hspill c.init
  refine ⟨fun vs m hb => hret vs m (same hb (by intro e; cases e)),
    fun m hb => htrap m (same hb (by intro e; cases e)),
    fun hb => hdiv (same (b := .diverges) hb (by intro e; cases e))⟩

omit hv hc hS hhi hlo halign hexit in
/-- Every admissible call is represented, by `Env.load`. -/
theorem represented :
    Implements.Represented (Admissible p S.memSize) (Represents hk a p S exit E0 saved S.memSize) :=
  fun _ hadm => ⟨_, hadm, rfl⟩

/-- **Where the machine run of an admissible call ends up.** One of: at the
RET to `exit` with the returned words and the final memory; at a UD2
with the memory at the trap; at the UD2 of a stack-limit check; or nowhere,
running forever. This is `compiled_behaviours` read through the source
behaviour, which exists and is not stuck because the call is admissible, and it
is the single fact `live` and `implements_sysv64` both consume. -/
theorem fate {c : CallData V} (hadm : Admissible p S.memSize c) :
    (∃ vs m fin w, Behaves p c.start (.returned vs m) ∧
        ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) w ∧
        Silmaril.X86.Ext.step exit w = .returned fin ∧
        (env hk a p S exit E0 saved).Final vs m fin) ∨
      (∃ m w, Behaves p c.start (.trapped m) ∧
        ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) w ∧
        Silmaril.X86.Ext.step exit w = .trapped ∧ MemRel S m w.memory) ∨
      (∃ w, ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) w ∧
        (env hk a p S exit E0 saved).Overflow w) ∨
      (Diverges p c.start ∧ InfiniteTrace (RStep exit) (loaded hk a p S exit E0 saved c)) := by
  obtain ⟨hr, htr, hd⟩ := compiled_behaviours hv hc hS hhi hlo halign hexit hadm
  obtain ⟨b, hbeh⟩ := Behaves.exists p c.start
  cases b with
  | returned vs m =>
    obtain ⟨w, hw, r⟩ := hr vs m hbeh
    rcases r with ⟨fin, hfs, hfinal⟩ | hov
    · exact .inl ⟨vs, m, fin, w, hbeh, hw, hfs, hfinal⟩
    · exact .inr (.inr (.inl ⟨w, hw, hov⟩))
  | trapped m =>
    obtain ⟨w, hw, r⟩ := htr m hbeh
    rcases r with ⟨hts, hmr⟩ | hov
    · exact .inr (.inl ⟨m, w, hbeh, hw, hts, hmr⟩)
    · exact .inr (.inr (.inl ⟨w, hw, hov⟩))
  | stuck => exact absurd hbeh hadm.2.2
  | diverges =>
    rcases hd hbeh with hinf | ⟨w, hw, hov⟩
    · exact .inr (.inr (.inr ⟨hbeh, hinf⟩))
    · exact .inr (.inr (.inl ⟨w, hw, hov⟩))

/-- **The compiled program never gets stuck.** No state reachable from a
represented machine state is stuck: it either steps, or it is one of the three
final states. This is what makes `implements_sysv64` a statement with content
rather than a vacuous truth about a machine that halts into the void; in
particular it rules out every fault outcome of `Ext.step`. -/
theorem live :
    Implements.Live (tgtSem (env hk a p S exit E0 saved))
      (Represents hk a p S exit E0 saved S.memSize) := by
  classical
  rintro c t ⟨hadm, rfl⟩ u hu
  by_cases hret : ∃ v, Silmaril.X86.Ext.step exit u = .retired v
  · exact .inl hret
  have fu : ∀ x, ¬ RStep exit u x := fun x hx => hret ⟨x, hx⟩
  have key : (∃ v, Silmaril.X86.Ext.step exit u = .returned v) ∨
      Silmaril.X86.Ext.step exit u = .trapped := by
    have step_of : ∀ w : MState, ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) w →
        ((∃ v, Silmaril.X86.Ext.step exit w = .returned v) ∨
          Silmaril.X86.Ext.step exit w = .trapped) →
        ((∃ v, Silmaril.X86.Ext.step exit u = .returned v) ∨
          Silmaril.X86.Ext.step exit u = .trapped) := by
      intro w hw hwo
      have fw : ∀ x, ¬ RStep exit w x := by
        rcases hwo with ⟨v, hv⟩ | hv <;> exact no_step hv (by intro x e; cases e)
      exact Silmaril.RightUnique.reach_final_eq (rstep_rightUnique exit) hu hw fu fw ▸ hwo
    rcases fate (saved := saved) hv hc hS hhi hlo halign hexit hadm with
      ⟨_, _, fin, w, _, hw, hfs, _⟩ | ⟨_, w, _, hw, hts, _⟩ | ⟨w, hw, hov⟩ | ⟨_, hinf⟩
    · exact step_of w hw (.inl ⟨fin, hfs⟩)
    · exact step_of w hw (.inr hts)
    · exact step_of w hw (.inr hov.1)
    · exact absurd hinf
        (Silmaril.RightUnique.not_infinite_of_final (rstep_rightUnique exit) hu fu)
  refine .inr ?_
  rcases key with ⟨v, hv⟩ | hv
  · exact ⟨.returned v, .inl ⟨v, hv, rfl⟩, by simp⟩
  · by_cases hov : (env hk a p S exit E0 saved).Overflow u
    · exact ⟨.exhausted, .inr (.inr ⟨hov, rfl⟩), by simp⟩
    · exact ⟨.trapped u, .inr (.inl ⟨hv, hov, rfl⟩), by simp⟩

/-- **Compiled RTL implements its source at `sysv64`.** Every behaviour of the
compiled machine state representing a call implements a behaviour of the RTL
call, in the mode `⟨strict, allowed⟩`: a RET comes from a returning run with
the results in the System V result registers, a UD2 from a trapping run with
the same memory, an infinite run from a diverging run, and the stack-limit UD2
— the *resource* outcome — may stand for any of the three. -/
theorem implements_sysv64 :
    Implements ⟨.strict, .allowed⟩ (sem p) (tgtSem (env hk a p S exit E0 saved))
      entryState (Represents hk a p S exit E0 saved S.memSize)
      (obs hk a p S exit E0 saved) := by
  classical
  rintro c t ⟨hadm, rfl⟩ - o hb
  have hfate := fate (saved := saved) hv hc hS hhi hlo halign hexit hadm
  by_cases hdiv : o = .diverges
  · subst hdiv
    have hinf : InfiniteTrace (RStep exit) (loaded hk a p S exit E0 saved c) := hb
    have stop : ∀ w : MState, ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) w →
        (∀ x, ¬ RStep exit w x) → False := fun w hw fw =>
      Silmaril.RightUnique.not_infinite_of_final (rstep_rightUnique exit) hw fw hinf
    refine ⟨.diverges, ?_, trivial⟩
    rcases hfate with ⟨_, _, _, w, _, hw, hfs, _⟩ | ⟨_, w, _, hw, hts, _⟩ | ⟨w, hw, hov⟩ |
        ⟨hdv, _⟩
    · exact (stop w hw (no_step hfs (by intro x e; cases e))).elim
    · exact (stop w hw (no_step hts (by intro x e; cases e))).elim
    · exact (stop w hw (no_step hov.1 (by intro x e; cases e))).elim
    · exact beh_diverges_iff.mpr hdv
  obtain ⟨v, hv, hfin⟩ := (Semantics.beh_of_ne hdiv).mp hb
  have ident : ∀ w : MState, ReflTransGen (RStep exit) (loaded hk a p S exit E0 saved c) w →
      (∀ x, ¬ RStep exit w x) → (∀ x, ¬ RStep exit v x) → w = v := fun w hw fw fv =>
    Silmaril.RightUnique.reach_final_eq (rstep_rightUnique exit) hw hv fw fv
  have noinf : (∀ x, ¬ RStep exit v x) →
      ¬ InfiniteTrace (RStep exit) (loaded hk a p S exit E0 saved c) := fun fv =>
    Silmaril.RightUnique.not_infinite_of_final (rstep_rightUnique exit) hv fv
  rcases hfin with ⟨w₀, hs, rfl⟩ | ⟨hs, hnov, rfl⟩ | ⟨hov₀, rfl⟩
  -- The machine executed the RET to `exit`: the source returned, and `Env.Final`
  -- holds of the state after the RET.
  · have hs' : Silmaril.X86.Ext.step exit v = .returned w₀ := hs
    have fv : ∀ x, ¬ RStep exit v x := no_step hs' (by intro x e; cases e)
    rcases hfate with ⟨vs, m, fin, w, hbr, hw, hfs, hfinal⟩ | ⟨_, w, _, hw, hts, _⟩ |
        ⟨w, hw, hov⟩ | ⟨_, hinf⟩
    · have hwv : w = v := ident w hw (no_step hfs (by intro x e; cases e)) fv
      rw [hwv, hs'] at hfs
      cases hfs
      exact ⟨.returned (vs, m), beh_returned_iff.mpr hbr, hfinal⟩
    · have hwv : w = v := ident w hw (no_step hts (by intro x e; cases e)) fv
      rw [hwv, hs'] at hts
      cases hts
    · have hwv : w = v := ident w hw (no_step hov.1 (by intro x e; cases e)) fv
      have h1 : Silmaril.X86.Ext.step exit w = .trapped := hov.1
      rw [hwv, hs'] at h1
      cases h1
    · exact absurd hinf (noinf fv)
  -- The machine stopped at a UD2 that is not the stack-limit check: the source
  -- trapped, with the same memory.
  · have hs' : Silmaril.X86.Ext.step exit v = .trapped := hs
    have fv : ∀ x, ¬ RStep exit v x := no_step hs' (by intro x e; cases e)
    rcases hfate with ⟨_, _, fin, w, _, hw, hfs, _⟩ | ⟨m, w, hbt, hw, hts, hmr⟩ |
        ⟨w, hw, hov⟩ | ⟨_, hinf⟩
    · have hwv : w = v := ident w hw (no_step hfs (by intro x e; cases e)) fv
      rw [hwv, hs'] at hfs
      cases hfs
    · have hwv : w = v := ident w hw (no_step hts (by intro x e; cases e)) fv
      rw [hwv] at hmr
      exact ⟨.trapped m, beh_trapped_iff.mpr hbt, .inr hmr⟩
    · have hwv : w = v := ident w hw (no_step hov.1 (by intro x e; cases e)) fv
      rw [hwv] at hov
      exact absurd hov hnov
    · exact absurd hinf (noinf fv)
  -- The machine stopped at the stack-limit check: a resource outcome, which may
  -- stand for any source outcome.
  · obtain ⟨b, hbeh⟩ := Behaves.exists p c.start
    cases b with
    | returned vs m => exact ⟨.returned (vs, m), beh_returned_iff.mpr hbeh, rfl⟩
    | trapped m => exact ⟨.trapped m, beh_trapped_iff.mpr hbeh, rfl⟩
    | stuck => exact absurd hbeh hadm.2.2
    | diverges => exact ⟨.diverges, beh_diverges_iff.mpr hbeh, rfl⟩

/-- **The instance is not vacuous, for safe calls.** Every admissible call is
represented and the compiled code never gets stuck.

`Admissible` includes "the call does not get stuck", so the guarantee is
scoped: an RTL program with undefined behaviour is outside it, and that is the
honest scope, because `compile_correct` claims nothing about a stuck Lir run.
`Silmaril/Wasm/Compile/ImplementsX86.lean` needs no such restriction only
because its source subset is safe everywhere. `implements_sysv64` itself is not
weakened — `Implements` already carries `src.Safe (entry c)`. -/
theorem nonvacuous_sysv64 :
    Implements.Nonvacuous (tgtSem (env hk a p S exit E0 saved)) (Admissible p S.memSize)
      (Represents hk a p S exit E0 saved S.memSize) where
  represented := represented
  live := live hv hc hS hhi hlo halign hexit

/-- What the nonvacuous instance delivers for a concrete admissible call: a
machine state representing it, which *has* a behaviour, each of whose
behaviours implements a behaviour of the RTL call. The safety premise is the
third conjunct of `Admissible`, read through `safe_iff_not_stuck`. -/
theorem exists_beh_sysv64 {c : CallData V} (hadm : Admissible p S.memSize c) :
    ∃ t, Represents hk a p S exit E0 saved S.memSize c t ∧
      (∃ o, (tgtSem (env hk a p S exit E0 saved)).Beh t o) ∧
      ∀ o, (tgtSem (env hk a p S exit E0 saved)).Beh t o →
        ∃ o', (sem p).Beh (entryState c) o' ∧
          Outcome.Rel ⟨.strict, .allowed⟩ (obs hk a p S exit E0 saved c t) o o' :=
  (implements_sysv64 hv hc hS hhi hlo halign hexit).exists_beh
    (nonvacuous_sysv64 hv hc hS hhi hlo halign hexit) hadm (safe_iff_not_stuck.mpr hadm.2.2)

/-- Both directions: RTL is deterministic and the target is live, so every
behaviour of a safe RTL call is also *realised* by the compiled machine state,
not merely over-approximated. -/
theorem exactly_sysv64 :
    Implements.Exactly ⟨.strict, .allowed⟩ (sem p) (tgtSem (env hk a p S exit E0 saved))
      entryState (Represents hk a p S exit E0 saved S.memSize)
      (obs hk a p S exit E0 saved) :=
  (implements_sysv64 hv hc hS hhi hlo halign hexit).exactly_of_live
    (live hv hc hS hhi hlo halign hexit) (sem_deterministic p)

end Instance

/-! ## The System V return contract, in `sysv64`'s vocabulary

`Env.Final` — the `ret` component of `obs` — states the three clauses of the
System V return contract with the registers written out. These theorems read
them back as facts about `Silmaril.X86.sysv64`. -/

/-- The returned words are in `sysv64.intRetRegs`, in order: `rax`, then
`rdx`. -/
theorem final_retReg {P : Type} {E : Env P} {vals : List Word} {lm : Memory} {t : MState}
    (h : E.Final vals lm t) (i : Nat) (hi : i < vals.length) :
    ∃ r, Silmaril.X86.sysv64.intRetReg? i = some r ∧ t.core.read r = vals[i] := by
  have h2 := h.vals_len
  have : i < 2 := by omega
  interval_cases i
  · exact ⟨.rax, rfl, h.vals 0 hi⟩
  · exact ⟨.rdx, rfl, h.vals 1 hi⟩

/-- Every register of `sysv64.calleeSaved` has, after the return, the value it
had in the loaded machine: the callee-saved registers are preserved across the
whole compiled call. -/
theorem final_preserved {P : Type} {E : Env P} {vals : List Word} {lm : Memory} {t : MState}
    (h : E.Final vals lm t) (lm₀ : Memory) (main : Lir.FuncId) (args : List Word)
    (init : Silmaril.X86.State) :
    Silmaril.X86.sysv64.Preserved (E.load lm₀ main args init).core.read t.core.read := by
  intro r hr
  have hload : ∀ q, (E.load lm₀ main args init).core.read q = E.loadRegs args init q :=
    fun _ => rfl
  rw [Silmaril.X86.sysv64_mem_calleeSaved] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hload] <;>
    simp only [Env.loadRegs, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15] <;> rfl

/-- The stack pointer after the return is the entry stack pointer popped by
`sysv64.linkSize`. -/
theorem final_rsp {P : Type} {E : Env P} {vals : List Word} {lm : Memory} {t : MState}
    (h : E.Final vals lm t) :
    t.core.read Silmaril.X86.sysv64.stackPointer =
      BitVec.ofNat 64 (E.E0 + Silmaril.X86.sysv64.linkSize) := h.rsp

/-- The System V entry alignment the backend assumes is `sysv64.EntryAligned`,
definitionally: `stackAlign = 16` and `entryResidue = 8`. -/
theorem sysv64_entryAligned_eq {E0 : Nat} : Silmaril.X86.sysv64.EntryAligned E0 ↔ E0 % 16 = 8 :=
  Iff.rfl

end Silmaril.Machine.RTL.X86
