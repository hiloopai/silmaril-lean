module

public import Silmaril.Machine.RiscV.Lir.Correct.Defs
/-!
# Loading a compiled program and the end-to-end theorems

`loadState` constructs the machine state that runs function `f` of a compiled
program on arguments `args` and a Lir linear memory `lm`:

* the memory has exactly the three regions of `Space.regions`: the encoded
  code at `codeBase` (readable and executable), a zero-filled stack
  `[stackLo, stackHi)` and the bytes of `lm` at `memBase` (both readable and
  writable);
* `sp = stackHi`, `ra` is the halt stub, `s10 = stackLo`, `s11 = memBase`,
  `a0 …` hold the arguments, every other register is zero, and the PC is the
  prologue of `f`.

`compile_correct` is the end-to-end statement: for a program accepted by
`compile` and a layout satisfying `Space.Valid`, every returned result, trap and
divergence of the Lir run of `f` is matched by the machine run from
`loadState`, unless that machine run reaches the stack-overflow stub. Returned
values are in `a0 …` at the halt stub, and the final Lir memory is the machine
memory at `memBase`. The halt, trap and overflow stubs are `EBREAK`, so the
machine stops there (`Returned.stopped`, `Trapped.stopped`,
`Overflowed.stopped`).

`compile_correct_bounded` removes the overflow alternative: if every Lir state
reachable from the start has at most `D` suspended activations and the stack
region holds `D + 1` frames, each outcome is matched exactly.
`depthBounded_of_no_calls` gives `D = 0` for programs without calls.

`spill_compile_correct` composes `compile_correct` with `Lir.Alloc.spill` and
the `firstK` allocation, starting from a Lir program over unboundedly many
virtual registers.

Nothing is claimed about Lir executions that get stuck (undefined behaviour),
about programs rejected by `compile`, or about machine states outside the
simulation relation. The machine is the handwritten `RiscV.Ext` model.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.Process (Memory)
open Silmaril.RiscV.Ext (Compute MState)
open Machine.Lir (Prog Func Block Point Loc Op Term Frame Activation)
open Relation

/-! ## The loaded state -/

/-- Data bytes of the loaded image: the Lir memory and a zero-filled stack. -/
def dataBytes (S : Space) (lm : Machine.Lir.Memory) : Process.ByteMemory :=
  Memory.install (Memory.install ∅ S.memBase ((List.range lm.size).map lm.bytes))
    S.stackLo (List.replicate (S.stackHi - S.stackLo) 0)

/-- Bytes of the loaded image: the data bytes and the encoded code. -/
def imageBytes (S : Space) (code : List Ext.Instr) (lm : Machine.Lir.Memory) : Process.ByteMemory :=
  Memory.install (dataBytes S lm) S.codeBase (Ext.byteDecoder.encodeBlock code)

def loadMemory (S : Space) (code : List Ext.Instr) (lm : Machine.Lir.Memory) : Memory where
  regions := S.regions code.length
  bytes := imageBytes S code lm

/-- Initial registers: stack pointer, return address, stack limit, memory
base and arguments; zero elsewhere. -/
def initRegs (S : Space) (retTo : Word) (args : List Word) : Machine.RegisterFile Reg Word :=
  fun r =>
    if r = sp then BitVec.ofNat 64 S.stackHi
    else if r = ra then retTo
    else if r = s10 then BitVec.ofNat 64 S.stackLo
    else if r = s11 then BitVec.ofNat 64 S.memBase
    else if 10 ≤ r.toNat ∧ r.toNat < 18 then args.getD (r.toNat - 10) 0
    else 0

variable {P : Type}

/-- The machine state running function `f` of the compiled program `code` of `p`. -/
def loadState (S : Space) (code : List Ext.Instr) (p : Prog P) (f : Machine.Lir.FuncId)
    (args : List Word) (lm : Machine.Lir.Memory) : MState :=
  ⟨⟨initRegs S (addrOf S.codeBase haltIdx) args, addrOf S.codeBase (funcStart p f)⟩,
    loadMemory S code lm⟩

/-! ## Properties of the loaded state -/

section Load

variable {S : Space} {code : List Ext.Instr} (hv : S.Valid code.length)
include hv

omit hv in
theorem imageBytes_code (i : Nat) (hi : i < 4 * code.length) (lm : Machine.Lir.Memory) :
    (imageBytes S code lm).get? (S.codeBase + i) = some ((Ext.byteDecoder.encodeBlock code)[i]'
      (by rw [Ext.encodeBlock_length]; exact hi)) :=
  Memory.install_get _ _ _ _ _

theorem imageBytes_stack {a : Nat} (ha : S.InStack a) (lm : Machine.Lir.Memory) :
    (imageBytes S code lm).get? a = some 0 := by
  have := hv.code_stack
  unfold imageBytes dataBytes
  rw [Memory.install_outside _ _ _ _ (by rw [Ext.encodeBlock_length]; simp only [Space.InStack] at ha; omega)]
  have h := Memory.install_get (Memory.install ∅ S.memBase ((List.range lm.size).map lm.bytes))
    S.stackLo (List.replicate (S.stackHi - S.stackLo) (0 : Process.Byte)) (a - S.stackLo)
    (by simp only [List.length_replicate, Space.InStack] at ha ⊢; omega)
  simp only [Space.InStack] at ha
  rw [Nat.add_sub_cancel' ha.1] at h
  rw [h]; simp

theorem imageBytes_mem {lm : Machine.Lir.Memory} (hs : lm.size = S.memSize) {a : Nat}
    (ha : a < lm.size) : (imageBytes S code lm).get? (S.memBase + a) = some (lm.bytes a) := by
  have := hv.code_mem; have := hv.stack_mem; have := hv.stack_le
  unfold imageBytes dataBytes
  rw [Memory.install_outside _ _ _ _ (by rw [Ext.encodeBlock_length]; omega),
    Memory.install_outside _ _ _ _ (by simp; omega),
    Memory.install_get _ _ _ _ (by simpa using ha)]
  simp

theorem load_good (p : Prog P) (f : Machine.Lir.FuncId) (args : List Word)
    (lm : Machine.Lir.Memory) : Good S code (loadState S code p f args lm) where
  regions := rfl
  code := by
    have := hv.code_end
    have h := Ext.fetchBytes_install ⟨S.regions code.length, dataBytes S lm⟩
      ⟨S.codeBase, 4 * code.length, codePerm⟩
      (by simp [Space.regions]) rfl S.codeBase (Ext.byteDecoder.encodeBlock code) le_rfl
      (by rw [Ext.encodeBlock_length]) (by simp [Process.addressLimit]; omega)
      (by simp [Process.addressLimit]; omega)
    rw [Ext.encodeBlock_length] at h
    exact h
  backed := fun a ha => by
    show ((imageBytes S code lm).get? a).isSome = true
    rw [imageBytes_stack hv ha]; rfl

theorem load_memRel (p : Prog P) (f : Machine.Lir.FuncId) (args : List Word)
    {lm : Machine.Lir.Memory} (hs : lm.size = S.memSize) :
    MemRel S.memBase lm (loadState S code p f args lm).memory :=
  fun _ ha => imageBytes_mem hv hs ha

end Load

theorem initRegs_read (S : Space) (retTo : Word) (args : List Word) (pc : Word) :
    let s : State := ⟨initRegs S retTo args, pc⟩
    s.read sp = BitVec.ofNat 64 S.stackHi ∧ s.read ra = retTo ∧
      s.read s10 = BitVec.ofNat 64 S.stackLo ∧ s.read s11 = BitVec.ofNat 64 S.memBase ∧
      ∀ k < 8, s.read (argRegN k) = args.getD k 0 := by
  refine ⟨rfl, rfl, rfl, rfl, fun k hk => ?_⟩
  have hne := argRegN_ne_zero hk
  have ht : (argRegN k).toNat = 10 + k := by
    simp only [argRegN, BitVec.toNat_ofNat]; omega
  show (if argRegN k = 0#5 then 0#64 else initRegs S retTo args (argRegN k)) = _
  rw [ite_false_of hne]
  unfold initRegs
  rw [ite_false_of (argRegN_ne_sp hk), ite_false_of (argRegN_ne_ra hk),
    ite_false_of (argRegN_ne_s10 hk), ite_false_of (argRegN_ne_s11 hk),
    ite_true_of (by rw [ht]; omega), ht]
  congr 1; omega

/-! ## Stopping at the stubs -/

section Stubs

variable {A : Assign P} {p : Prog P} {S : Space} {N : Nat}
  (hv : S.Valid (emitProg A.reg N p).length)
include hv

theorem stub_stopped {m : MState} (hg : Good S (emitProg A.reg N p) m) {k : Nat} (hk : k < 3)
    (hpc : m.core.pc = addrOf S.codeBase k) : m.step = .stopped := by
  have hi : (emitProg A.reg N p)[k]? = some .ebreak := by
    unfold emitProg
    rw [List.getElem?_append_left (by simpa using hk)]
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  rw [step_at hv hg hpc hi]
  rfl

theorem Returned.stopped {vs : List Word} {mem : Machine.Lir.Memory} {m : MState}
    (h : Returned A p S N vs mem m) : m.step = .stopped :=
  stub_stopped hv h.1 (by decide) h.2.1

theorem Trapped.stopped {mem : Machine.Lir.Memory} {m : MState} (h : Trapped A p S N mem m) :
    m.step = .stopped :=
  stub_stopped hv h.1 (by decide) h.2.1

theorem Overflowed.stopped {m : MState} (h : Overflowed A p S N m) : m.step = .stopped :=
  stub_stopped hv h.1 (by decide) h.2

/-- The halt, trap and overflow stubs have distinct addresses. -/
theorem stubs_distinct :
    addrOf S.codeBase haltIdx ≠ addrOf S.codeBase trapIdx ∧
      addrOf S.codeBase haltIdx ≠ addrOf S.codeBase overflowIdx ∧
      addrOf S.codeBase trapIdx ≠ addrOf S.codeBase overflowIdx := by
  have hl : 3 ≤ (emitProg A.reg N p).length := by simp [emitProg]
  have := hv.code_end
  have e : ∀ k, k < 3 → (addrOf S.codeBase k).toNat = S.codeBase + 4 * k := fun k hk => by
    simp only [addrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    have := congrArg BitVec.toNat h <;>
    simp only [haltIdx, trapIdx, overflowIdx] at this <;>
    rw [e _ (by decide), e _ (by decide)] at this <;> omega

end Stubs

/-! ## The start of a run -/

section Start

variable [DecidableEq P] {A : Assign P} {p : Prog P} {S : Space} {N : Nat}
  (hc : checkProg p N = none) (hv : S.Valid (emitProg A.reg N p).length)
include hc hv

theorem start_match {f : Machine.Lir.FuncId} {args : List Word} {lm : Machine.Lir.Memory}
    {s : Machine.Lir.State P} (hs : p.start f args lm = some s) (hsize : lm.size = S.memSize) :
    ∃ t, TransGen TStep (loadState S (emitProg A.reg N p) p f args lm) t ∧
      (Match A p S N s t ∨
        (Overflowed A p S N t ∧ S.stackHi < S.stackLo + frameSize N)) := by
  unfold Prog.start at hs
  cases he : p.enter f args with
  | none => simp [he] at hs
  | some r =>
    obtain ⟨pt, fr⟩ := r
    simp only [he, Option.map_some, Option.some.injEq] at hs
    subst hs
    obtain ⟨fn, hfn, hwp, rfl⟩ := enter_some he
    have hch := check_head hc hfn
    simp only [checkFuncHead] at hch
    have hpl : fn.params.length ≤ 8 := by
      split at hch
      · cases hch
      · omega
    have hal := writeAll_length hwp
    obtain ⟨hsp₀, hra₀, hs10₀, hs11₀, hargs₀⟩ :=
      initRegs_read S (addrOf S.codeBase haltIdx) args (addrOf S.codeBase (funcStart p f))
    have hlo := hv.stack_le
    obtain ⟨t, tg, hg, hout⟩ := prologue_run hc hv hfn hwp (load_good hv p f args lm)
      (t := loadState S (emitProg A.reg N p) p f args lm) rfl (d := 0) (by simpa using hlo)
      (by simp only [Nat.zero_mul, Nat.sub_zero]; exact hsp₀) hs10₀
      (fun k hk => by
        have := hargs₀ k (by omega)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this
        exact this)
    rcases hout with ⟨ho, hlt⟩ | ⟨hpc, hdepth, hsp, hregs, hslots, hra, wi, hfix⟩
    · exact ⟨t, tg, .inr ⟨ho, by simpa using hlt⟩⟩
    refine ⟨t, tg, .inl {
      good := hg
      pc := hpc
      depth := hdepth
      sp := hsp
      base := by
        rw [hfix s11 (fun q e => A.reg_ne_s11 q e.symm) (by decide)]; exact hs11₀
      limit := by
        rw [hfix s10 (fun q e => A.reg_ne_s10 q e.symm) (by decide)]; exact hs10₀
      regs := hregs
      slots := hslots
      ra := hra
      stack := trivial
      mem := (load_memRel hv p f args hsize).of_writesIn S wi hsize fun a ha => by
        have := hv.stack_mem
        have := (spAt_frame S N hv (check_frame hc) hdepth).lo
        have := (spAt_frame S N hv (check_frame hc) hdepth).hi
        simp only [Space.InMem] at ha; omega
      size := hsize }⟩

end Start

/-! ## End-to-end correctness -/

variable [DecidableEq P]

/-- **Correctness of the Lir-to-RV64 backend.** For a program accepted by
`compile` and a memory layout satisfying `Space.Valid`, started on function `f`
with arguments `args` and linear memory `lm` (of the layout's size):

* if the Lir run returns `vs` with final memory `mem`, the machine run from
  `loadState` reaches the halt stub with `vs` in `a0 …` and `mem` at
  `memBase`, or reaches the stack-overflow stub;
* if the Lir run traps with memory `mem`, the machine reaches the trap stub with
  `mem` at `memBase`, or the overflow stub;
* if the Lir run diverges, the machine run is infinite or reaches the overflow
  stub. -/
theorem compile_correct {A : Assign P} {p : Prog P} {img : Image} (hcomp : compile A p = .ok img)
    {S : Space} (hv : S.Valid img.code.length) {f : Machine.Lir.FuncId} {args : List Word}
    {lm : Machine.Lir.Memory} (hsize : lm.size = S.memSize) {s : Machine.Lir.State P}
    (hs : p.start f args lm = some s) :
    (∀ vs mem, Machine.Lir.Behaves p s (.returned vs mem) →
      ∃ m, ReflTransGen TStep (loadState S img.code p f args lm) m ∧
        (Returned A p S img.slots vs mem m ∨ Overflowed A p S img.slots m)) ∧
    (∀ mem, Machine.Lir.Behaves p s (.trapped mem) →
      ∃ m, ReflTransGen TStep (loadState S img.code p f args lm) m ∧
        (Trapped A p S img.slots mem m ∨ Overflowed A p S img.slots m)) ∧
    (Machine.Lir.Diverges p s →
      InfiniteTrace TStep (loadState S img.code p f args lm) ∨
        ∃ m, ReflTransGen TStep (loadState S img.code p f args lm) m ∧
          Overflowed A p S img.slots m) := by
  obtain ⟨hcode, hc⟩ := compile_ok hcomp
  rw [hcode] at hv ⊢
  obtain ⟨t, tg, ht | ⟨ho, -⟩⟩ := start_match hc hv hs hsize
  · refine ⟨fun vs mem hb => ?_, fun mem hb => ?_, fun hd => ?_⟩
    · obtain ⟨m, hm, r⟩ := returns hc hv ht hb
      exact ⟨m, tg.to_reflTransGen.trans hm, r⟩
    · obtain ⟨m, hm, r⟩ := traps hc hv ht hb
      exact ⟨m, tg.to_reflTransGen.trans hm, r⟩
    · rcases diverges hc hv ht hd with h | ⟨m, hm, r⟩
      · exact .inl (InfiniteTrace.of_steps tg.to_reflTransGen h)
      · exact .inr ⟨m, tg.to_reflTransGen.trans hm, r⟩
  · exact ⟨fun _ _ _ => ⟨t, tg.to_reflTransGen, .inr ho⟩, fun _ _ => ⟨t, tg.to_reflTransGen, .inr ho⟩,
      fun _ => .inr ⟨t, tg.to_reflTransGen, ho⟩⟩

/-- **Exact correctness under a call-depth bound.** If every Lir state
reachable from the start has at most `D` suspended activations and the stack
region holds `D + 1` frames, then returned results, traps and divergence are
matched with no overflow alternative. -/
theorem compile_correct_bounded {A : Assign P} {p : Prog P} {img : Image}
    (hcomp : compile A p = .ok img) {S : Space} (hv : S.Valid img.code.length)
    {f : Machine.Lir.FuncId} {args : List Word} {lm : Machine.Lir.Memory}
    (hsize : lm.size = S.memSize) {s : Machine.Lir.State P} (hs : p.start f args lm = some s)
    {D : Nat} (hb : DepthBounded p s D) (hD : S.stackLo + (D + 1) * frameSize img.slots ≤ S.stackHi) :
    (∀ vs mem, Machine.Lir.Behaves p s (.returned vs mem) →
      ∃ m, ReflTransGen TStep (loadState S img.code p f args lm) m ∧
        Returned A p S img.slots vs mem m) ∧
    (∀ mem, Machine.Lir.Behaves p s (.trapped mem) →
      ∃ m, ReflTransGen TStep (loadState S img.code p f args lm) m ∧
        Trapped A p S img.slots mem m) ∧
    (Machine.Lir.Diverges p s → InfiniteTrace TStep (loadState S img.code p f args lm)) := by
  obtain ⟨hcode, hc⟩ := compile_ok hcomp
  rw [hcode] at hv ⊢
  obtain ⟨t, tg, ht | ⟨_, hlt⟩⟩ := start_match hc hv hs hsize
  · refine ⟨fun vs mem h => ?_, fun mem h => ?_, fun h => ?_⟩
    · obtain ⟨m, hm, r⟩ := returns_bounded hc hv hD ht hb h
      exact ⟨m, tg.to_reflTransGen.trans hm, r⟩
    · obtain ⟨m, hm, r⟩ := traps_bounded hc hv hD ht hb h
      exact ⟨m, tg.to_reflTransGen.trans hm, r⟩
    · exact InfiniteTrace.of_steps tg.to_reflTransGen (diverges_bounded hc hv hD ht hb h)
  · have : frameSize img.slots ≤ (D + 1) * frameSize img.slots :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- In a program without calls, no step pushes an activation. -/
theorem stack_length_step_le {p : Prog P}
    (hnc : ∀ pt f args results, p.fetch pt ≠ some (.instr (.call f args results)))
    {s s' : Machine.Lir.State P} (h : Machine.Lir.Step p s s') : s'.stack.length ≤ s.stack.length := by
  have tr := Machine.Lir.Transition.of_step h (by intro e; cases e)
  generalize hr : Machine.Lir.Result.running s' = r at tr
  cases tr with
  | op => cases hr; exact le_rfl
  | call hf => exact absurd hf (hnc _ _ _ _)
  | fop => cases hr; exact le_rfl
  | jump => cases hr; exact le_rfl
  | branch => cases hr; exact le_rfl
  | ret _ _ hst => cases hr; rw [hst]; simp
  | halt => cases hr
  | trap => cases hr

theorem depthBounded_of_no_calls {p : Prog P}
    (hnc : ∀ pt f args results, p.fetch pt ≠ some (.instr (.call f args results)))
    (s : Machine.Lir.State P) : DepthBounded p s s.stack.length := by
  intro s' h
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (stack_length_step_le hnc hs).trans ih

/-! ## From virtual registers: spilling, then code generation -/

/-- **Spilling followed by code generation.** A Lir program over virtual
registers (`Nat`) is spilled with `Lir.Alloc.firstK k` onto `k + 2 ≤ 14`
physical registers and compiled. Every returned result, trap and divergence of
the source run of `f` is matched by the machine run from `loadState` of the
compiled spilled program, unless that run reaches the stack-overflow stub. -/
theorem spill_compile_correct (k : Nat) (hk : k + 2 ≤ 14) {p : Prog Nat} {img : Image}
    (hcomp : compile (Assign.fin (k + 2) hk) (Machine.Lir.Alloc.spill (Machine.Lir.Alloc.firstK k) p) =
      .ok img)
    {S : Space} (hv : S.Valid img.code.length) {f : Machine.Lir.FuncId} {args : List Word}
    {lm : Machine.Lir.Memory} (hsize : lm.size = S.memSize) {s : Machine.Lir.State Nat}
    (hs : p.start f args lm = some s) :
    let q := Machine.Lir.Alloc.spill (Machine.Lir.Alloc.firstK k) p
    let A := Assign.fin (k + 2) hk
    (∀ vs mem, Machine.Lir.Behaves p s (.returned vs mem) →
      ∃ m, ReflTransGen TStep (loadState S img.code q f args lm) m ∧
        (Returned A q S img.slots vs mem m ∨ Overflowed A q S img.slots m)) ∧
    (∀ mem, Machine.Lir.Behaves p s (.trapped mem) →
      ∃ m, ReflTransGen TStep (loadState S img.code q f args lm) m ∧
        (Trapped A q S img.slots mem m ∨ Overflowed A q S img.slots m)) ∧
    (Machine.Lir.Diverges p s →
      InfiniteTrace TStep (loadState S img.code q f args lm) ∨
        ∃ m, ReflTransGen TStep (loadState S img.code q f args lm) m ∧
          Overflowed A q S img.slots m) := by
  intro q A
  have hva := Machine.Lir.Alloc.firstK_valid k
  obtain ⟨t, ht, _⟩ := Machine.Lir.Alloc.spill_start hva hs
  obtain ⟨hret, htrap, hdiv⟩ := compile_correct hcomp hv hsize ht
  have same : ∀ {b : Machine.Lir.Behavior}, Machine.Lir.Behaves p s b → b ≠ .stuck →
      Machine.Lir.Behaves q t b := by
    intro b hb hns
    obtain ⟨t', ht', hb'⟩ := Machine.Lir.Alloc.spill_behaves hva hs hb hns
    rw [ht] at ht'
    cases ht'
    exact hb'
  exact ⟨fun vs mem hb => hret vs mem (same hb (by intro h; cases h)),
    fun mem hb => htrap mem (same hb (by intro h; cases h)),
    fun hd => hdiv (same (b := .diverges) hd (by intro h; cases h))⟩

end Silmaril.RiscV.Backend
