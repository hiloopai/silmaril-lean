module

public import Silmaril.Process.CLI.Sha256Cli.Spec
public import Silmaril.Process.CLI.Sha256Cli.Compress
public import Silmaril.Process.CLI.X86Linux.Call
public import Silmaril.Process.CLI.X86Linux.SilentTransport
public import Silmaril.Crypto.X86.Sha256O2.Reference

/-! # A concrete empty-input compression call in the retained filter

This is an executable-byte call-site instance, not launch reachability. Starting
from the filter's mapped image, checked writes prepare SHA's initial state and
the empty message's one padded block. The actual CALL at `0x400229` pushes its
return slot, the proved compression callee returns to `0x40022e`, and the whole
segment is silent. The driver's path from launch/EOF to this preparation and
its later hex/write loops remain separate obligations.
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Process.CLI.Sha256Cli.EmptyCall

open Silmaril.Process (Memory Byte Region Access)
open Silmaril.X86 (Word MState sysv64)
open Silmaril.Crypto.X86.Sha256O2
open Silmaril.Process.CLI.X86Linux

def stateAddress : Word := 0x401660
def blockAddress : Word := 0x401620
def callerSP : Word := BitVec.ofNat 64 (sp - 32)
def calleeSP : Word := BitVec.ofNat 64 (sp - 40)

/-- The C `uint32_t H[8]`, in x86 little-endian byte order. -/
def initialHashBytes : List Byte :=
  [0x67, 0xe6, 0x09, 0x6a, 0x85, 0xae, 0x67, 0xbb,
   0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5,
   0x7f, 0x52, 0x0e, 0x51, 0x8c, 0x68, 0x05, 0x9b,
   0xab, 0xd9, 0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b]

/-- `0x80`, 55 zero padding bytes and the eight-byte zero bit length. -/
def emptyBlock : List Byte := 0x80 :: List.replicate 63 0

theorem initialHashBytes_length : initialHashBytes.length = 32 := rfl
theorem emptyBlock_length : emptyBlock.length = 64 := by simp [emptyBlock]
theorem initialHashBytes_state :
    stateOf initialHashBytes = Silmaril.Crypto.SHA256.Kernel.initHash := by decide +kernel

/-- The prepared machine block is the canonical reference padding of empty input. -/
theorem emptyBlock_padding :
    emptyBlock.map UInt8.ofBitVec = Silmaril.Crypto.paddingMD [] := by decide +kernel

theorem initialHashBytes_reference :
    (stateOf initialHashBytes).toState = Silmaril.Crypto.SHA256.H0 := by
  rw [initialHashBytes_state]
  rfl

theorem empty_reference_hash :
    Silmaril.Crypto.SHA256.processBlock Silmaril.Crypto.SHA256.H0
      (Silmaril.Crypto.SHA256.parseBlock (emptyBlock.map UInt8.ofBitVec)) =
        Silmaril.Crypto.SHA256.hash [] := by
  unfold Silmaril.Crypto.SHA256.hash
  rw [← emptyBlock_padding]
  simp only [List.length_map, emptyBlock_length, Nat.reduceDiv, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_cons, List.foldl_nil,
    Nat.mul_zero, List.drop_zero]
  rw [List.take_of_length_le (by simp only [List.length_map, emptyBlock_length]; omega)]

/-- The published empty-message SHA-256 value, as the callee's eight words. -/
def emptyHash : Silmaril.Crypto.SHA256.Kernel.InitHash :=
  ⟨0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
   0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855⟩

theorem empty_compression :
    compressBlock Silmaril.Crypto.SHA256.Kernel.initHash emptyBlock = emptyHash := by
  decide +kernel

def stateMemory : Memory :=
  { memory₀ with bytes := Memory.install memory₀.bytes stateAddress.toNat initialHashBytes }

def preparedMemory : Memory :=
  { stateMemory with bytes := Memory.install stateMemory.bytes blockAddress.toNat emptyBlock }

def callerCore : Core :=
  Silmaril.X86.EntryState.sysvCore (Silmaril.X86.EntryState.blankCore 0x400229)
    0x400229 stateAddress blockAddress callerSP

def caller : MState := ⟨callerCore, preparedMemory⟩

def calleeMemory : Memory :=
  { preparedMemory with bytes := (Memory.install preparedMemory.bytes calleeSP.toNat
      (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress])) }

def callee : MState := directCallState caller 0xb2 calleeMemory

theorem state_write : memory₀.writeBytes stateAddress.toNat initialHashBytes = some stateMemory := by
  unfold Memory.writeBytes
  rw [show memory₀.checkSpan .write stateAddress.toNat initialHashBytes.length = true by decide]
  rfl

theorem block_write : stateMemory.writeBytes blockAddress.toNat emptyBlock = some preparedMemory := by
  unfold Memory.writeBytes
  rw [show stateMemory.checkSpan .write blockAddress.toNat emptyBlock.length = true by decide]
  rfl

theorem return_write : preparedMemory.writeBytes calleeSP.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress]) = some calleeMemory := by
  unfold Memory.writeBytes
  rw [show preparedMemory.checkSpan .write calleeSP.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress]).length = true by decide]
  rfl

/-- Only these three concrete regions were prepared, retaining all mappings. -/
def Preparation (address : Nat) : Prop :=
  (stateRegion stateAddress).Contains address ∨ (blockRegion blockAddress).Contains address ∨
    (returnSlot calleeSP).Contains address

private theorem write_frame {before after : Memory} {address : Nat} {bytes : List Byte}
    (written : before.writeBytes address bytes = some after)
    (inside : ∀ location, address ≤ location ∧ location < address + bytes.length →
      Preparation location) : Memory.WritesWithin before after Preparation :=
  ((Memory.writesOnly_iff_writesWithin _ _ _ _).mp
    (Memory.writeBytes_writesOnly written)).mono inside

theorem prepared_frame : Memory.WritesWithin memory₀ calleeMemory Preparation := by
  have first := write_frame state_write (by
    intro location h
    exact Or.inl (by simpa only [stateRegion, Region.Contains, initialHashBytes_length] using h))
  have second := write_frame block_write (by
    intro location h
    exact Or.inr (Or.inl (by simpa only [blockRegion, Region.Contains, emptyBlock_length] using h)))
  have third := write_frame return_write (by
    intro location h
    exact Or.inr (Or.inr (by simpa only [returnSlot, Region.Contains,
      Silmaril.X86.length_encodeWords_singleton] using h)))
  exact first.trans (second.trans third)

theorem callee_state_bytes : callee.memory.readBytes stateAddress.toNat 32 = some initialHashBytes := by
  apply Memory.readWith_eq callee.memory .read stateAddress.toNat initialHashBytes (by decide)
  intro index bound
  change (Memory.install preparedMemory.bytes calleeSP.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress])).get?
      (stateAddress.toNat + index) = _
  rw [Memory.install_outside _ _ _ _ (Or.inl (by
    rw [initialHashBytes_length] at bound
    change 0x401660 + index < 0x7ffeffd8
    omega))]
  change (Memory.install stateMemory.bytes blockAddress.toNat emptyBlock).get?
    (stateAddress.toNat + index) = _
  rw [Memory.install_outside _ _ _ _ (Or.inr (by
    rw [emptyBlock_length]
    change 0x401620 + 64 ≤ 0x401660 + index
    omega))]
  exact Memory.install_get _ stateAddress.toNat initialHashBytes index bound

theorem callee_block_bytes : callee.memory.readBytes blockAddress.toNat 64 = some emptyBlock := by
  apply Memory.readWith_eq callee.memory .read blockAddress.toNat emptyBlock (by decide)
  intro index bound
  change (Memory.install preparedMemory.bytes calleeSP.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress])).get?
      (blockAddress.toNat + index) = _
  rw [Memory.install_outside _ _ _ _ (Or.inl (by
    rw [emptyBlock_length] at bound
    change 0x401620 + index < 0x7ffeffd8
    omega))]
  exact Memory.install_get _ blockAddress.toNat emptyBlock index bound

theorem actual_push : Silmaril.X86.pushWord caller.core caller.memory (caller.core.rip + 5) =
    some (caller.core.write .rsp (caller.core.read .rsp - 8), calleeMemory) := by
  unfold Silmaril.X86.pushWord
  change (preparedMemory.writeBytes calleeSP.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress])).map _ = _
  rw [return_write]
  rfl

theorem callee_return_slot : callee.memory.readBytes calleeSP.toNat 8 =
    some (Silmaril.X86.Ext.leBytes Compress.returnAddress 8) := by
  rw [Silmaril.X86.Ext.leBytes_eight]
  apply Memory.readWith_eq callee.memory .read calleeSP.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress]) (by decide)
  exact Memory.install_get _ calleeSP.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [Compress.returnAddress])

theorem callee_entry : SysVEntry (Compress.layout Compress.returnAddress)
    stateAddress blockAddress calleeSP frameSize callee := by
  have constants := Compress.constants_of_loaded_writesWithin (loaded []).1 prepared_frame
    (by intro address code h; norm_num [Preparation, codeRegion, Compress.layout,
      Compress.textBase, stateRegion, blockRegion, returnSlot, stateAddress, blockAddress,
      calleeSP, sp, Region.Contains, size] at code h; omega)
    (by intro address table h; norm_num [Preparation, kTableRegion, Compress.layout,
      Compress.rodataBase, stateRegion, blockRegion, returnSlot, stateAddress, blockAddress,
      calleeSP, sp, Region.Contains, kSize] at table h; omega)
  refine {
    rip := rfl
    code := constants.1
    relocFits := Compress.layout_relocFits _
    kTable := constants.2
    argState := by decide
    argBlock := by decide
    rsp := rfl
    aligned := by rw [Silmaril.X86.sysv64_entryAligned_iff]; decide
    returnAddress := callee_return_slot
    stateReads := ⟨_, callee_state_bytes⟩
    stateWritable := by decide
    blockReads := ⟨_, callee_block_bytes⟩
    frameMapped := by decide
    frameFits := by decide
    noWrap := by decide
    disjoint := by decide
    stateAligned := by decide }

/-- The exact checked CALL bytes survive preparation of the driver data. -/
theorem call_code : caller.memory.fetchBytes caller.core.rip.toNat 5 =
    some (Silmaril.X86.Ext.encode (.call 0xb2)) := by
  have code := X86Linux.fetch_of_codeAt Binary.image_wf (loaded []).1
    Binary.ok_400229.2 (by decide)
  have hstate := Memory.writeBytes_writesOnly state_write
  have hblock := Memory.writeBytes_writesOnly block_write
  rw [show caller.core.rip.toNat = Binary.i_400229.address from rfl]
  change preparedMemory.readWith .execute Binary.i_400229.address 5 = _
  rw [Silmaril.X86.Memory.readWith_writesOnly hblock .execute _ _ (Or.inl (by decide)),
    Silmaril.X86.Memory.readWith_writesOnly hstate .execute _ _ (Or.inl (by decide))]
  exact code

/-- A concrete actual CALL plus the completed compression execution produces
the certified SHA state with no process events. All entry hypotheses are proved. -/
theorem compress_call (s : Silmaril.Process.Syscall.State)
    (running : s.exited = none) (memory : s.memory = caller.memory) :
    ∃ final, Silmaril.X86.Ext.Returns Compress.returnAddress callee final ∧
      Post (Compress.layout Compress.returnAddress) stateAddress blockAddress calleeSP
        frameSize callee final ∧
      StateHolds final.memory stateAddress
        (compressBlock Silmaril.Crypto.SHA256.Kernel.initHash emptyBlock) ∧
      Proc.Runs isa Env.linux ⟨caller.core, s⟩ []
        ⟨final.core, Env.linux.withMemory s final.memory⟩ := by
  obtain ⟨final, returned⟩ := sha256_compress_O2_live (Compress.layout Compress.returnAddress)
    _ _ _ _ callee_entry
  have post := Compress.compress_contract Compress.returnAddress _ _ _ _ _ callee_entry returned
  have compressed := post.compressed _ _ callee_state_bytes callee_block_bytes
  rw [initialHashBytes_state] at compressed
  exact ⟨final, returned, post, compressed,
    runs_of_direct_call_returns Env.linux_memoryLens running memory call_code actual_push returned⟩

/-- A concrete standard-descriptor environment witnesses the running/memory
premises; this is a prepared call-site state, not a claim about launch reachability. -/
def environment : Silmaril.Process.Syscall.State :=
  ⟨caller.memory, fun fd =>
    if fd = 0 then some ⟨true, false, .ofList [], 0, []⟩
    else if fd = 1 ∨ fd = 2 then some ⟨false, true, .ofList [], 0, []⟩ else none, none⟩

/-- The complete caller-visible footprint includes CALL's return-slot store. -/
def CallerFootprint (address : Nat) : Prop :=
  Footprint stateAddress calleeSP frameSize address ∨ (returnSlot calleeSP).Contains address

/-- An inhabited supported-byte instance with the published empty hash, caller
RSP restored, caller callee-saved registers restored and the full CALL frame.
Every machine/ABI/buffer hypothesis is proved from the prepared mapped image. -/
theorem empty_call_result :
    ∃ final, Silmaril.X86.Ext.Returns Compress.returnAddress callee final ∧
      final.core.rip = Compress.returnAddress ∧
      StateHolds final.memory stateAddress emptyHash ∧
      final.core.read .rsp = callerSP ∧
      sysv64.Preserved caller.core.read final.core.read ∧
      Memory.WritesWithin caller.memory final.memory CallerFootprint ∧
      Proc.Runs isa Env.linux ⟨caller.core, environment⟩ []
        ⟨final.core, Env.linux.withMemory environment final.memory⟩ := by
  obtain ⟨final, returned, post, value, segment⟩ := compress_call environment rfl rfl
  rw [empty_compression] at value
  refine ⟨final, returned, ext_returns_target returned, value, post.rsp, ?_, ?_, segment⟩
  · intro reg saved
    exact (post.saved reg saved).trans (directCallCore_read caller.core 0xb2 reg (by
      intro same
      exact Silmaril.X86.sysv64_rsp_not_calleeSaved (same ▸ saved)))
  · exact direct_call_frame actual_push post.untouched

/-- The actual byte-level call establishes the SHA driver's canonical hash
state for empty input. This connects representations, not the later output loop. -/
theorem empty_call_reference :
    ∃ (final : MState) (bytes : List Byte),
      Proc.Runs isa Env.linux ⟨caller.core, environment⟩ []
        ⟨final.core, Env.linux.withMemory environment final.memory⟩ ∧
      final.memory.readBytes stateAddress.toNat 32 = some bytes ∧
      (stateOf bytes).toState = Silmaril.Crypto.SHA256.hash [] := by
  obtain ⟨final, _, post, _, segment⟩ := compress_call environment rfl rfl
  obtain ⟨bytes, read, reference⟩ :=
    post.compressed_reference callee_state_bytes callee_block_bytes emptyBlock_length
  rw [initialHashBytes_reference, empty_reference_hash] at reference
  exact ⟨final, bytes, segment, read, reference⟩

/-- A wrong first hash word cannot satisfy the same concrete result readback. -/
theorem wrong_hash_rejected {memory : Memory}
    (correct : StateHolds memory stateAddress emptyHash) :
    ¬ StateHolds memory stateAddress { emptyHash with h0 := 0 } := by
  intro wrong
  have equal := correct.unique wrong
  have different : emptyHash ≠ { emptyHash with h0 := 0 } := by decide
  exact different equal

/-- A concrete compression call reduces every completed-observation contract
to its continuation, with an actual certified hash result. This is the local
contract interface consumed by an institutional interpretation; it assumes no
global successful execution or output statement. -/
theorem empty_completed_contract (accepted : List Syscall.Event → Outcome → Prop) :
    ∃ final : MState, StateHolds final.memory stateAddress emptyHash ∧
      ((∀ events target outcome,
        Proc.Runs isa Env.linux ⟨caller.core, environment⟩ events target →
        Proc.Stop isa Env.linux target outcome → accepted events outcome) ↔
      (∀ events target outcome,
        Proc.Runs isa Env.linux
          ⟨final.core, Env.linux.withMemory environment final.memory⟩ events target →
        Proc.Stop isa Env.linux target outcome → accepted events outcome)) := by
  obtain ⟨final, _, _, value, _, _, _, segment⟩ := empty_call_result
  exact ⟨final, value,
    Proc.completed_contract_iff_of_silent instruction_deterministic segment accepted⟩

/-- Optional prefix contracts transport separately, accounting for a finite
execution ending inside the callee through the explicit empty-trace premise. -/
theorem empty_prefix_contract (permitted : List Syscall.Event → Prop) (empty : permitted []) :
    ∃ final : MState, StateHolds final.memory stateAddress emptyHash ∧
      ((∀ events target, Proc.Runs isa Env.linux
        ⟨caller.core, environment⟩ events target → permitted events) ↔
      (∀ events target, Proc.Runs isa Env.linux
        ⟨final.core, Env.linux.withMemory environment final.memory⟩ events target →
          permitted events)) := by
  obtain ⟨final, _, _, value, _, _, _, segment⟩ := empty_call_result
  exact ⟨final, value,
    Proc.prefix_policy_iff_of_silent instruction_deterministic segment permitted empty⟩

end Silmaril.Process.CLI.Sha256Cli.EmptyCall
