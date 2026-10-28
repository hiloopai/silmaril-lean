module

public import Silmaril.Process.CLI.Sha256Cli.HexLookup
public import Silmaril.Process.CLI.Sha256Cli.OutputFrame

/-! # The actual compiled hexadecimal loop

`iteration` executes the nine lookups, two stores and three real loop-control
instructions. `loop_to` maintains exact output bytes and an output-only memory
frame through at most 32 iterations. Code, digest state and table reads survive
the stores by the shared memory frame lemmas.

`empty` starts at the compression return address and reaches the real newline
store with the first 64 output bytes equal to the already specified empty
answer. The existing compression and reference-digest theorems are reused.
This is a bounded internal machine segment with explicit entry premises; it
neither assumes nor proves that every driver launch reaches that entry.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.HexLoop

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext

def advanced (c : Core) (index : Fin 32) : Core :=
  { c.write .rax (BitVec.ofNat 64 (index.val + 1)) with rip := 0x40026b, flags := addFlagsN (BitVec.ofNat 64 index.val) 1 }

def compared (c : Core) (index : Fin 32) : Core :=
  { advanced c index with rip := 0x40026f, flags := subFlagsN (BitVec.ofNat 64 (index.val + 1)) 32 }

def nextPc (index : Fin 32) : Word := if index.val + 1 = 32 then 0x400271 else 0x400230

def branched (c : Core) (index : Fin 32) : Core := { compared c index with rip := nextPc index }

private theorem advance_value (index : Fin 32) :
    BitVec.ofNat 64 index.val + 1 = BitVec.ofNat 64 (index.val + 1) := by
  have all : ∀ i : Fin 32, BitVec.ofNat 64 i.val + 1 = BitVec.ofNat 64 (i.val + 1) := by decide
  exact all index

private theorem branch_condition (index : Fin 32) :
    Cond.ne.eval (subFlagsN (BitVec.ofNat 64 (index.val + 1)) 32) =
      some (decide (index.val + 1 ≠ 32)) := by
  have all : ∀ i : Fin 32,
      Cond.ne.eval (subFlagsN (BitVec.ofNat 64 (i.val + 1)) 32) =
        some (decide (i.val + 1 ≠ 32)) := by decide
  exact all index

set_option maxRecDepth 10000 in
theorem control (c : Core) (s : Syscall.State) (index : Fin 32)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400267) (rax : c.read .rax = BitVec.ofNat 64 index.val) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨branched c index, s⟩ := by
  have a : Proc.Step X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨advanced c index, s⟩ := by
    apply Output.retire (entry := Binary.i_400267) (by simp [Binary.transcript]) intact running
    · simp [Binary.i_400267, pc]
    · simp [Entry.denote, Binary.i_400267, exec, Sz.read, Sz.write, writeRM, readRM,
        retire, aluStep, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
        advanced, rax, pc, X86Linux.execResult]
      exact congrArg (fun value : Word => (c.write .rax value).regs) (advance_value index)
  have b : Proc.Step X86Linux.isa Env.linux ⟨advanced c index, s⟩ [] ⟨compared c index, s⟩ := by
    apply Output.retire (entry := Binary.i_40026b) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, Binary.i_40026b, exec, Sz.read, readRM, retire, aluStep,
        Silmaril.X86.Ext.AluOp.flagsN, advanced, compared, X86Linux.execResult,
        Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write]
  have d : Proc.Step X86Linux.isa Env.linux ⟨compared c index, s⟩ [] ⟨branched c index, s⟩ := by
    apply Output.retire (entry := Binary.i_40026f) (by simp [Binary.transcript]) intact running
    · rfl
    · change X86Linux.execResult (exec (.jcc8 .ne 0xbf) (compared c index) s.memory 2) = _
      simp only [exec, show (compared c index).flags =
        subFlagsN (BitVec.ofNat 64 (index.val + 1)) 32 from rfl, branch_condition]
      simp only [show (compared c index).rip = 0x40026f from rfl]
      unfold branched nextPc
      by_cases last : index.val + 1 = 32
      · have selected : (if index.val + 1 = 32 then (0x400271 : Word) else 0x400230) = 0x400271 := by simp [last]
        have notTaken : decide (index.val + 1 ≠ 32) = false := decide_eq_false (by omega)
        simp only [selected, notTaken, X86Linux.execResult]
        rfl
      · have selected : (if index.val + 1 = 32 then (0x400271 : Word) else 0x400230) = 0x400230 := by simp [last]
        have taken : decide (index.val + 1 ≠ 32) = true := decide_eq_true last
        simp only [selected, taken, X86Linux.execResult]
        rfl
  exact .cons a (.cons b (.single d))

/-- Recover the image bound from the already checked transcription. -/
theorem code_below_output (entry : Entry) (member : entry ∈ Binary.transcript) :
    entry.address + entry.bytes.length ≤ 0x4015c0 :=
  (Output.code_end entry member).trans (by decide)

theorem intact_after_pair {before after : Memory} (intact : Output.Intact before)
    (index : Fin 32)
    (frame : Memory.WritesWithin before after
      (fun a => 0x4015c0 + 2 * index.val ≤ a ∧ a < 0x4015c0 + 2 * index.val + 2)) :
    Output.Intact after := by
  intro entry member
  have upper := code_below_output entry member
  exact (frame.fetchBytes (by intro offset bound inside; omega)).trans (intact entry member)

set_option maxRecDepth 10000 in
/-- All fourteen real instructions of one hexadecimal loop iteration. -/
theorem iteration (c : Core) (s : Syscall.State) (index : Fin 32) (bytes : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400230) (rax : c.read .rax = BitVec.ofNat 64 index.val)
    (stateRead : s.memory.readBytes 0x401660 32 = some bytes)
    (tableRead : s.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits)
    (writable : s.memory.Permitted .write (0x4015c0 + 2 * index.val) 2)
    (readable : s.memory.Permitted .read (0x4015c0 + 2 * index.val) 2) :
    ∃ (next : Core) (after : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨next, { s with memory := after }⟩ ∧
      next.rip = nextPc index ∧ next.read .rax = BitVec.ofNat 64 (index.val + 1) ∧
      after.readBytes (0x4015c0 + 2 * index.val) 2 =
        some (Sha256.hexByte (UInt8.ofBitVec (bytes.getD (HexLookup.sourceIndex index) 0))) ∧
      Memory.WritesWithin s.memory after
        (fun a => 0x4015c0 + 2 * index.val ≤ a ∧ a < 0x4015c0 + 2 * index.val + 2) := by
  let byte := bytes.getD (HexLookup.sourceIndex index) 0
  obtain ⟨after, pairRun, pairRead, frame⟩ := HexLookup.lookup_store c s index bytes
    running intact pc rax stateRead tableRead writable readable
  let pairCore : Core := { HexLookup.ninth c index byte with rip := 0x400267 }
  have indexValue : pairCore.read .rax = BitVec.ofNat 64 index.val := by
    simp [pairCore, HexLookup.ninth, HexLookup.eighth, HexLookup.seventh, HexLookup.sixth,
      HexLookup.fifth, HexLookup.fourth, HexLookup.third, HexLookup.second, HexLookup.first,
      Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write]
    exact rax
  have controls := control pairCore { s with memory := after } index running
    (intact_after_pair intact index frame) rfl indexValue
  exact ⟨branched pairCore index, after, pairRun.append controls, rfl, by simp [branched, compared, advanced],
    pairRead, frame⟩

def pairAt (bytes : List Byte) (index : Nat) : List Byte :=
  Sha256.hexByte (UInt8.ofBitVec
    (bytes.getD (((BitVec.ofNat 64 index) ^^^ 3).toNat) 0))

def formattedPrefix (bytes : List Byte) (count : Nat) : List Byte :=
  (List.range count).flatMap (pairAt bytes)

theorem formattedPrefix_succ (bytes : List Byte) (count : Nat) :
    formattedPrefix bytes (count + 1) = formattedPrefix bytes count ++ pairAt bytes count := by
  simp [formattedPrefix, List.range_succ]

theorem formattedPrefix_length (bytes : List Byte) (count : Nat) :
    (formattedPrefix bytes count).length = 2 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [formattedPrefix_succ, List.length_append, ih]
    simp [pairAt, Sha256.hexByte]
    omega

def Footprint (count address : Nat) : Prop :=
  0x4015c0 ≤ address ∧ address < 0x4015c0 + 2 * count

theorem intact_after_output {before after : Memory} (intact : Output.Intact before)
    {count : Nat} (frame : Memory.WritesWithin before after (Footprint count)) :
    Output.Intact after := by
  intro entry member
  have upper := code_below_output entry member
  exact (frame.fetchBytes (by intro offset bound inside; dsimp [Footprint] at inside; omega)).trans
    (intact entry member)

set_option maxRecDepth 10000 in
theorem loop_to (c : Core) (s : Syscall.State) (bytes : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400230) (rax : c.read .rax = 0)
    (stateRead : s.memory.readBytes 0x401660 32 = some bytes)
    (tableRead : s.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits)
    (writable : s.memory.Permitted .write 0x4015c0 64)
    (readable : s.memory.Permitted .read 0x4015c0 64) (count : Nat) :
    count ≤ 32 → ∃ (next : Core) (after : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨next, { s with memory := after }⟩ ∧
      next.rip = (if count = 32 then 0x400271 else 0x400230) ∧
      next.read .rax = BitVec.ofNat 64 count ∧
      after.readBytes 0x4015c0 (2 * count) = some (formattedPrefix bytes count) ∧
      Memory.WritesWithin s.memory after (Footprint count) := by
  induction count with
  | zero =>
    intro _
    refine ⟨c, s.memory, .refl _, ?_, rax, ?_, .refl _ _⟩
    · exact pc
    · simp [formattedPrefix, Memory.readBytes, Memory.readWith, Memory.checkSpan,
        Memory.readBacking, Silmaril.Process.addressLimit]
  | succ count ih =>
    intro bound
    have countBound : count < 32 := by omega
    obtain ⟨middleCore, middle, previous, atMiddle, valueMiddle, outputMiddle, frame⟩ := ih (by omega)
    have intactMiddle := intact_after_output intact frame
    have stateMiddle : middle.readBytes 0x401660 32 = some bytes := by
      exact (frame.readBytes (by intro offset ho inside; dsimp [Footprint] at inside; omega)).trans stateRead
    have tableMiddle : middle.readBytes 0x4004b0 16 = some EmptySupport.hexDigits := by
      exact (frame.readBytes (by intro offset ho inside; dsimp [Footprint] at inside; omega)).trans tableRead
    have writableMiddle : middle.Permitted .write (0x4015c0 + 2 * count) 2 :=
      (frame.permitted_iff .write _ _).mpr
        (Silmaril.X86.Ext.Memory.Permitted.sub writable (by decide) (by omega) (by omega))
    have readableMiddle : middle.Permitted .read (0x4015c0 + 2 * count) 2 :=
      (frame.permitted_iff .read _ _).mpr
        (Silmaril.X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by omega))
    have pcMiddle : middleCore.rip = 0x400230 := by
      simpa only [show ¬count = 32 by omega, ↓reduceIte] using atMiddle
    obtain ⟨next, after, stepRun, nextRip, nextValue, pairRead, pairFrame⟩ :=
      iteration middleCore { s with memory := middle } ⟨count, countBound⟩ bytes
        running intactMiddle pcMiddle valueMiddle stateMiddle tableMiddle writableMiddle readableMiddle
    change Memory.WritesWithin middle after
      (fun a => 0x4015c0 + 2 * count ≤ a ∧ a < 0x4015c0 + 2 * count + 2) at pairFrame
    have previousOutput : after.readBytes 0x4015c0 (2 * count) = some (formattedPrefix bytes count) :=
      (pairFrame.readBytes (by intro offset ho inside; omega)).trans outputMiddle
    have outputAfter := Memory.readBytes_append previousOutput pairRead
    refine ⟨next, after, previous.append stepRun, nextRip, nextValue, ?_, ?_⟩
    · simpa only [formattedPrefix_succ, pairAt, HexLookup.sourceIndex,
        show 2 * (count + 1) = 2 * count + 2 by omega] using outputAfter
    · exact (frame.mono (by intro a ha; dsimp [Footprint] at ha ⊢; omega)).trans
        (pairFrame.mono (by intro a ha; dsimp [Footprint]; omega))

theorem formattedPrefix_empty :
    formattedPrefix EmptySupport.emptyStateBytes 32 = (Sha256.expected []).take 64 := by
  have range : (List.finRange 32).map (fun i : Fin 32 => i.val) = List.range 32 := by decide
  have normalized : formattedPrefix EmptySupport.emptyStateBytes 32 =
      ((List.finRange 32).map (fun i => UInt8.ofBitVec
        (EmptySupport.emptyStateBytes.getD (HexLookup.sourceIndex i) 0))).flatMap Sha256.hexByte := by
    rw [formattedPrefix, ← range, List.flatMap_map, List.flatMap_map]
    rfl
  rw [normalized, HexLookup.empty_permutation]
  have length : (Silmaril.Crypto.SHA256.digest [] |>.flatMap Sha256.hexByte).length = 64 := by
    rw [Sha256.flatMap_hexByte_length, Silmaril.Crypto.SHA256.digest_length]
  change (Silmaril.Crypto.SHA256.digest []).flatMap Sha256.hexByte =
    (((Silmaril.Crypto.SHA256.digest []).flatMap Sha256.hexByte) ++ [0x0a]).take 64
  rw [← length, List.take_left]

def zeroCore (c : Core) : Core :=
  { c.write .rax 0 with rip := 0x400230, flags := logicFlagsN (0 : BitVec 32) }

set_option maxRecDepth 10000 in
theorem start (c : Core) (s : Syscall.State) (running : s.exited = none)
    (intact : Output.Intact s.memory) (pc : c.rip = 0x40022e) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨zeroCore c, s⟩ := by
  apply Silmaril.Machine.Trace.Runs.single
  apply Output.retire (entry := Binary.i_40022e) (by simp [Binary.transcript]) intact running
  · simp [Binary.i_40022e, pc]
  · simp [Entry.denote, Binary.i_40022e, exec, Sz.read, Sz.write, writeRM, readRM,
      retire, aluStep, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
      zeroCore, pc, X86Linux.execResult]
    constructor
    · exact congrArg (fun w : Word => (c.write .rax w).regs)
        (show ((((c.read .rax).setWidth 32) ^^^ ((c.read .rax).setWidth 32)).setWidth 64) = 0 by simp)
    · exact congrArg (fun w : BitVec 32 => logicFlagsN w)
        (show ((c.read .rax).setWidth 32) ^^^ ((c.read .rax).setWidth 32) = 0 by simp)

theorem empty (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40022e)
    (stateRead : s.memory.readBytes 0x401660 32 = some EmptySupport.emptyStateBytes)
    (tableRead : s.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits)
    (writable : s.memory.Permitted .write 0x4015c0 64)
    (readable : s.memory.Permitted .read 0x4015c0 64) :
    ∃ (next : Core) (after : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨next, { s with memory := after }⟩ ∧
      next.rip = 0x400271 ∧ next.read .rax = 32 ∧
      after.readBytes 0x4015c0 64 = some ((Sha256.expected []).take 64) ∧
      Memory.WritesWithin s.memory after (Footprint 32) := by
  obtain ⟨next, after, loopRun, nextRip, nextValue, answer, frame⟩ :=
    loop_to (zeroCore c) s EmptySupport.emptyStateBytes running intact rfl (by simp [zeroCore])
      stateRead tableRead writable readable 32 (by decide)
  exact ⟨next, after, (start c s running intact pc).append loopRun, nextRip, nextValue,
    formattedPrefix_empty ▸ answer, frame⟩

end Silmaril.Process.CLI.Sha256Cli.HexLoop
