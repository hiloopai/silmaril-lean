module

public import Silmaril.Machine.Abi.CrossAbi.Thms
public import Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc
public import Silmaril.X86.Ext.SymExec
public import Silmaril.X86.Ext.Lemmas
/-!
# GCC's `call_ms`, run from fetched bytes and tied to its call target

Proofs for the round-4 part of `Silmaril.Machine.Abi.CrossAbi.Gcc.Thms`.

* `run_loaded`: straight-line `Ext` code laid out in a loaded image (`Layout`, checked by
  `decide`), whose instructions before the last keep memory and fall through (`Plain`), runs
  under the fetching machine exactly as under `Gcc.run` of the decoded list. This holds for
  `Ext.stepOpt` (code without `ret`) and for `stepAny` (retire or return).
* `fetch_enter`, `fetch_leave`: the two segments of `call_ms`.
* `enter_rip`: the decoded enter code ends at `rip + 21 + sext rel`; from `callMsAddr` with
  the linked `callMsRel` that is `msMixAddr`.
* `implements_linked`, `progress_linked`, `lands_linked`: the fetched thunk `callMsLinked`
  under `CallMsAt.Room`/`CallMsAt.Guar` implements `SysvToMs` and progresses (transported
  from the decoded thunk), and enters the callee at `msMixAddr`.
* `room_inhabited`: a concrete state meets `CallMsAt.Room` (review, round 4).
* `sound_at`: the composition theorem of `Thunk.Simulates.sound` with a callee contract that
  only holds on callee entry states meeting `land`, for thunks that always land there.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch

open Silmaril.Logic.Institution.Bridges
open Silmaril.X86 (MState State Word Byte)
open Silmaril.X86.Ext (Instr Loaded decode exec stepOpt step)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.Convention (Thunk Strict)
open Silmaril.Machine.Abi.CrossAbi
open Silmaril.Machine.Abi.CrossAbi.Gcc
open Silmaril.Machine.Abi.Win64 (win64)
open Silmaril.Machine.Abi.SystemV (sysv Options Proto)

/-! ## Straight-line code from a loaded image -/

/-- `code` is laid out in `bytes` from offset `off`, each instruction decoding from its
slice at its canonical length. -/
def Layout (bytes : List Byte) : Nat → List Instr → Prop
  | _, [] => True
  | off, i :: rest => off + i.length ≤ bytes.length ∧
      decode ((bytes.drop off).take i.length) = some (i, i.length) ∧
      Layout bytes (off + i.length) rest

instance instDecidableLayout (bytes : List Byte) : ∀ off code, Decidable (Layout bytes off code)
  | _, [] => isTrue trivial
  | off, i :: rest =>
    haveI := instDecidableLayout bytes (off + i.length) rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- An instruction that, when it executes, keeps memory and falls through. -/
def Plain (i : Instr) : Prop :=
  ∀ c mem c' mem', exec i c mem = .ok c' mem' →
    mem' = mem ∧ c'.rip = c.rip + BitVec.ofNat 64 i.length

theorem stepOpt_loaded {exit base : Word} {bytes : List Byte} {m : MState} {off : Nat}
    {i : Instr} (loaded : Loaded m.memory base bytes)
    (at_ : m.core.rip = base + BitVec.ofNat 64 off) (fits : off + i.length ≤ bytes.length)
    (dec : decode ((bytes.drop off).take i.length) = some (i, i.length)) (nr : i ≠ .ret) :
    stepOpt exit m = match exec i m.core m.memory with
      | .ok c mm => some ⟨c, mm⟩
      | _ => none := by
  unfold stepOpt
  rw [Silmaril.X86.Ext.step_of_loaded loaded at_ fits dec]
  cases exec i m.core m.memory <;> simp [nr]

theorem stepAny_loaded {exit base : Word} {bytes : List Byte} {m : MState} {off : Nat}
    {i : Instr} (loaded : Loaded m.memory base bytes)
    (at_ : m.core.rip = base + BitVec.ofNat 64 off) (fits : off + i.length ≤ bytes.length)
    (dec : decode ((bytes.drop off).take i.length) = some (i, i.length)) :
    stepAny exit m = match exec i m.core m.memory with
      | .ok c mm => some ⟨c, mm⟩
      | _ => none := by
  unfold stepAny
  rw [Silmaril.X86.Ext.step_of_loaded loaded at_ fits dec]
  cases exec i m.core m.memory with
  | ok c mm =>
    by_cases h : (i = .ret ∧ c.rip = exit)
    · simp only [h, and_self, ite_true]
    · simp only [h, ite_false]
  | _ => rfl

/-- **Fetched straight-line code runs as the decoded list.** -/
theorem run_loaded (f : MState → Option MState) (P : Instr → Prop) {base : Word}
    {bytes : List Byte}
    (hf : ∀ (m : MState) off i, Loaded m.memory base bytes →
      m.core.rip = base + BitVec.ofNat 64 off → off + i.length ≤ bytes.length →
      decode ((bytes.drop off).take i.length) = some (i, i.length) → P i →
      f m = match exec i m.core m.memory with | .ok c mm => some ⟨c, mm⟩ | _ => none) :
    ∀ (code : List Instr) (off : Nat) (m : MState), Loaded m.memory base bytes →
      m.core.rip = base + BitVec.ofNat 64 off → Layout bytes off code → (∀ i ∈ code, P i) →
      (∀ i ∈ code.dropLast, Plain i) →
      Silmaril.Machine.Execution.run f code.length m = run code m := by
  intro code
  induction code with
  | nil => intro off m _ _ _ _ _; rfl
  | cons i rest ih =>
    intro off m loaded at_ lay hp plain
    obtain ⟨fits, dec, lay'⟩ := lay
    simp only [List.length_cons, Silmaril.Machine.Execution.run_succ]
    rw [hf m off i loaded at_ fits dec (hp i (by simp))]
    simp only [run]
    cases hx : exec i m.core m.memory with
    | ok c mm =>
      simp only [Option.bind_some]
      cases rest with
      | nil => rfl
      | cons j rest' =>
        obtain ⟨hmem, hrip⟩ := plain i (by simp) _ _ _ _ hx
        subst hmem
        refine ih (off + i.length) ⟨c, m.memory⟩ loaded ?_ lay'
          (fun k hk => hp k (List.mem_cons_of_mem _ hk)) ?_
        · show c.rip = _
          rw [hrip, at_, Silmaril.X86.Ext.rip_advance base rfl]
        · intro k hk
          exact plain k (by simp only [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hk)
    | _ => rfl

theorem plain_mov (d r : Silmaril.X86.Reg) : Plain (.mov .q (.reg d) r) := by
  intro c mem c' mem' h
  rw [Silmaril.X86.Ext.exec_mov_reg] at h
  cases h
  exact ⟨rfl, rfl⟩

theorem plain_aluI8 (op : Silmaril.X86.AluOp) (d : Silmaril.X86.Reg) (imm : BitVec 8)
    (hop : op ≠ .cmp) : Plain (.aluI8 .q op (.reg d) imm) := by
  intro c mem c' mem' h
  rw [Silmaril.X86.Ext.exec_aluI8_reg _ _ _ _ _ _ hop] at h
  cases h
  exact ⟨rfl, rfl⟩

/-! ## The two segments of `call_ms` -/

theorem callMsEnter_layout : Layout callMsBytes 0 (callMsEnter callMsRel) := by decide

theorem callMsLeave_layout : Layout callMsLeaveBytes 0 callMsLeave := by decide

theorem callMsPre_plain : ∀ i ∈ callMsPre, Plain i := by
  intro i hi
  simp only [callMsPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h <;> subst h
  · exact plain_aluI8 _ _ _ (by decide)
  all_goals exact plain_mov _ _

/-- The enter segment, fetched at any address where its bytes are loaded. -/
theorem fetch_enter (exit : Word) {m : MState}
    (loaded : Loaded m.memory m.core.rip callMsBytes) :
    Silmaril.Machine.Execution.run (stepOpt exit) 6 m = run (callMsEnter callMsRel) m := by
  have hdrop : (callMsEnter callMsRel).dropLast = callMsPre := by simp [callMsEnter]
  exact run_loaded (stepOpt exit) (· ≠ .ret)
    (fun _ _ _ l a f d nr => stepOpt_loaded l a f d nr) (callMsEnter callMsRel) 0 m loaded
    (by simp) callMsEnter_layout (by decide) (by rw [hdrop]; exact callMsPre_plain)

/-- The leave segment, fetched at the return point. -/
theorem fetch_leave (exit : Word) {m : MState}
    (loaded : Loaded m.memory m.core.rip callMsLeaveBytes) :
    Silmaril.Machine.Execution.run (stepAny exit) 2 m = run callMsLeave m := by
  exact run_loaded (stepAny exit) (fun _ => True)
    (fun _ _ _ l a f d _ => stepAny_loaded l a f d) callMsLeave 0 m loaded
    (by simp) callMsLeave_layout (fun _ _ => trivial) (by
      intro i hi
      simp only [callMsLeave, List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      subst hi
      exact plain_aluI8 _ _ _ (by decide))

/-! ## The call target -/

theorem enter_rip {rel : BitVec 32} {m m₁ : MState} (h : run (callMsEnter rel) m = some m₁) :
    m₁.core.rip = (Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.pre m.core).rip +
      BitVec.ofNat 64 (Silmaril.X86.Insn.call rel).length + rel.signExtend 64 := by
  have h' : run (callMsPre ++ [.call rel]) m = some m₁ := h
  rw [Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.run_pre] at h'
  simp only [run, Silmaril.X86.Ext.exec_call, Silmaril.X86.Insn.exec] at h'
  cases hp : Silmaril.X86.pushWord (Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.pre m.core) m.memory
      ((Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.pre m.core).rip +
        BitVec.ofNat 64 (Silmaril.X86.Insn.call rel).length) with
  | none => simp [hp] at h'
  | some r =>
    obtain ⟨t, mem⟩ := r
    simp only [hp] at h'
    cases h'
    rfl

theorem enter_lands {m m₁ : MState} (pc : m.core.rip = callMsAddr)
    (h : run (callMsEnter callMsRel) m = some m₁) : m₁.core.rip = msMixAddr := by
  rw [enter_rip h]
  simp only [Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.pre, pc]
  decide

/-! ## The fetched thunk -/

variable {p : Proto}

theorem enter_eq (options : Options) (exit : Word) {s : Ffi.State} (room : CallMsAt.Room s) :
    (callMsLinked (sysv options) win64 p exit).enter s =
      (callMs (sysv options) win64 p callMsRel).enter s := by
  have loaded : Loaded s.machine.memory s.machine.core.rip callMsBytes := by
    rw [room.pc]; exact room.code
  ext s₁
  simp only [callMsLinked, callMs, onMachine, Set.mem_ofPred_eq]
  rw [fetch_enter exit loaded]

theorem leave_eq (options : Options) (exit : Word) {s s₁ s₂ : Ffi.State}
    (guar : CallMsAt.Guar s₁ s₂) :
    (callMsLinked (sysv options) win64 p exit).leave s s₂ =
      (callMs (sysv options) win64 p callMsRel).leave s s₂ := by
  have loaded : Loaded s₂.machine.memory s₂.machine.core.rip callMsLeaveBytes := by
    rw [guar.pc]; exact guar.code
  ext s₃
  simp only [callMsLinked, callMs, onMachine, Set.mem_ofPred_eq]
  rw [fetch_leave exit loaded]

theorem implements_linked (options : Options) (exit : Word) :
    Implements (callMsLinked (sysv options) win64 p exit) SysvToMs.Enter SysvToMs.Leave
      CallMsAt.Room CallMsAt.Guar where
  enter a s entry room s₁ entered := by
    rw [enter_eq options exit room] at entered
    exact (Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.implements options).enter a s entry room.room
      s₁ entered
  leave a s entry room s₁ entered s₂ proper guar s₃ left := by
    rw [enter_eq options exit room] at entered
    rw [leave_eq options exit guar] at left
    exact (Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.implements options).leave a s entry room.room
      s₁ entered s₂ proper guar.slot s₃ left

theorem progress_linked (options : Options) (exit : Word) :
    Progress (callMsLinked (sysv options) win64 p exit) CallMsAt.Room CallMsAt.Guar where
  enter a s entry room := by
    rw [enter_eq options exit room]
    exact (Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.progress options).enter a s entry room.room
  leave a s entry room s₁ entered s₂ proper guar := by
    rw [enter_eq options exit room] at entered
    rw [leave_eq options exit guar]
    exact (Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.progress options).leave a s entry room.room
      s₁ entered s₂ proper guar.slot

theorem lands_linked (options : Options) (exit : Word) {s s₁ : Ffi.State}
    (room : CallMsAt.Room s) (entered : s₁ ∈ (callMsLinked (sysv options) win64 p exit).enter s) :
    s₁.machine.core.rip = msMixAddr := by
  rw [enter_eq options exit room] at entered
  obtain ⟨m₁, hrun, rfl⟩ := Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.mem_enter options entered
  exact enter_lands room.pc hrun

/-! ## `CallMsAt.Room` is inhabited -/

/-- A witness memory: one read/write/execute region `[0x8000, 0x402000)` holding
`callMsBytes` at `callMsAddr`. -/
def roomRegion : Silmaril.Process.Region := ⟨0x8000, 0x402000 - 0x8000, ⟨true, true, true⟩⟩

def roomMemory : Silmaril.Process.Memory :=
  ⟨[roomRegion], Silmaril.Process.Memory.install ∅ 0x4013c0 callMsBytes⟩

/-- A witness state: `rip = callMsAddr`, `rsp = 0x8ff8`, the bytes loaded. -/
def roomState : Ffi.State where
  machine := ⟨⟨fun r => match r with | .rsp => 0x8ff8 | _ => 0, callMsAddr,
    ⟨none, none, none, none, none, none⟩, 0⟩, roomMemory⟩
  vectors := fun _ => 0
  x87 := fun _ => 0
  direction := false
  x87Mode := true
  mxcsr := 0x1f80
  x87Control := 0x37f
  fsBase := 0

theorem room_inhabited : CallMsAt.Room roomState := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_⟩
  any_goals decide +kernel
  refine Silmaril.Process.Memory.readWith_eq _ _ _ callMsBytes (by decide +kernel)
    fun i hi => ?_
  exact Silmaril.Process.Memory.install_get _ _ _ _ hi

/-! ## Composition with a callee contract at the landing point -/

section
variable {V : Vocab} {St D : Type}

theorem proper_at {B : Convention V St D} {p : V.Proto}
    {c : Contracts.Contract (V.Args p) (Option (V.Ret p))} (strict : Strict c)
    {land : St → Prop} {model : Contracts.Model St St}
    (callee : Contracts.Sat model (within (B.translate p c) land))
    {a : V.Args p} {s₁ : St} (entry : B.Entry p a s₁) (hl : land s₁) (pre : c.pre a) {s₂ : St}
    (ran : s₂ ∈ model s₁) : B.Proper p s₁ s₂ := by
  by_contra improper
  exact strict a pre ((callee s₁ ⟨⟨a, entry, pre⟩, hl⟩).2 s₂ ran a entry pre none improper)

/-- `Thunk.Simulates.sound` for a callee whose contract (and guarantee) is only assumed on
entry states meeting `land`, given that the thunk always enters the callee there. -/
theorem sound_at {A B : Convention V St D} {p : V.Proto} {t : Thunk A B p}
    {room : St → Prop} {guar : St → St → Prop} (sim : t.Simulates room guar)
    {land : St → Prop} (lands : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, land s₁)
    {c : Contracts.Contract (V.Args p) (Option (V.Ret p))} (strict : Strict c)
    {model : Contracts.Model St St} (callee : Contracts.Sat model (within (B.translate p c) land))
    (guaranteed : ∀ a s₁, B.Entry p a s₁ → land s₁ → c.pre a → ∀ s₂ ∈ model s₁, guar s₁ s₂) :
    Contracts.Sat (t.wrap model) (within (A.translate p c) room) := by
  rintro s ⟨⟨a, entry, pre⟩, roomy⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨s₁, entered⟩ := sim.enter_progress a s entry roomy
    have entry₁ := sim.enter_entry a s entry roomy s₁ entered
    have hl := lands a s entry roomy s₁ entered
    obtain ⟨s₂, ran⟩ := (callee s₁ ⟨⟨a, entry₁, pre⟩, hl⟩).1
    have proper := proper_at strict callee entry₁ hl pre ran
    obtain ⟨s₃, left⟩ := sim.leave_progress a s entry roomy s₁ entered s₂ proper
      (guaranteed a s₁ entry₁ hl pre s₂ ran)
    exact ⟨s₃, s₁, entered, s₂, ran, left⟩
  · rintro s₃ ⟨s₁, entered, s₂, ran, left⟩ a' entry' pre' o observed
    have entry₁ := sim.enter_entry a' s entry' roomy s₁ entered
    have hl := lands a' s entry' roomy s₁ entered
    have proper := proper_at strict callee entry₁ hl pre' ran
    have g := guaranteed a' s₁ entry₁ hl pre' s₂ ran
    have ret := sim.leave_return a' s entry' roomy s₁ entered s₂ proper g s₃ left
    obtain ⟨⟨r, at_⟩, reflect⟩ := sim.leave_result a' s entry' roomy s₁ entered s₂ proper g s₃ left
    have post := (callee s₁ ⟨⟨a', entry₁, pre'⟩, hl⟩).2 s₂ ran a' entry₁ pre'
    cases o with
    | none => exact absurd ⟨ret, r, at_⟩ observed
    | some r' => exact post (some r') ⟨proper.1, reflect r' observed.2⟩

end

end Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch
