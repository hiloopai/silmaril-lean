module

public import Silmaril.Elf.Corpus.SqliteOneByteVarint.Defs
import Silmaril.Elf.BindEq.Thms
import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Thms
import Silmaril.X86.Ext.Store
import Silmaril.X86.MemEvent.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint

open Silmaril.Elf.Corpus.SqliteOneByteVarint
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So
open Silmaril.Elf.Staged.Reader
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Machine (RegisterFile)
open Silmaril.X86

theorem file_codeAt (window : Window) : Silmaril.Elf.CodeAt F window.va window.code := by
  cases window <;> exact codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

theorem symbol_at (w : Window) : ∃ symbol,
    Silmaril.Elf.SymbolAt F .symtab w.symbolIndex symbol ∧
    symbol.name = w.symbolName.toUTF8.data.toList.map UInt8.toBitVec ∧
    symbol.binding = 0 ∧ symbol.kind = 2 ∧ symbol.raw.sectionIndex ≠ 0 ∧
    symbol.raw.value = w.va ∧ w.code.length ≤ symbol.raw.size := by
  cases w
  · exact ⟨s26_74, ⟨_, parses, by decide +kernel⟩, by decide +kernel⟩
  · exact ⟨s26_27, ⟨_, parses, by decide +kernel⟩, by decide +kernel⟩

private theorem initialLoaded {bias : Word} {memory : Memory}
    (placement : Silmaril.Elf.Placement F bias.toNat)
    (image : Silmaril.Elf.Link.ElfBind.RoLoaded F bias memory) (window : Window) :
    Ext.Loaded memory (bias + BitVec.ofNat 64 window.va) window.code := by
  have loaded := Silmaril.Proofs.Elf.BindEq.directCall_of_roLoaded'
    parses rfl rfl (file_codeAt window) placement image
  exact loaded.1

private theorem imageStable {bias : Word} {entry : MState} {byte : Byte} {memory : Memory}
    (admit : Entry bias entry byte)
    (loaded : ∀ w : Window, Ext.Loaded entry.memory (bias + BitVec.ofNat 64 w.va) w.code)
    (frame : entry.memory.WritesWithin memory (writable entry)) (w : Window) :
    Ext.Loaded memory (bias + BitVec.ofNat 64 w.va) w.code := by
  unfold Ext.Loaded
  rw [frame.fetchBytes (admit.codeSeparate w)]
  exact loaded w

private theorem Trace.runsIn {bias : Word} {entry s t : MState} {ev : List MemEvent.Event}
    (trace : Trace bias entry s ev t) :
    FnContract.RunsIn Open9.isa (fun m => ¬ FnContract.Returned Open9.isa entry m) s t := by
  induction trace with
  | nil state => exact .refl state
  | cons _ _ _ _ loaded pc fits dec exec before _ ih =>
    exact .step before (Open9.step_of_listed loaded pc fits dec exec) ih

/-- A fixed program path. Offsets are relative to the corresponding ELF window. -/
private abbrev Site := Window × Nat × Ext.Instr × Nat

private def operand (r : Reg) (disp : BitVec 32 := 0) : Ext.Mem :=
  ⟨.reg r, none, disp, fun _ => rfl⟩

private def path : List Site :=
  [(.caller, 0, .lea .q .rdi (operand .rsi 4), 4),
   (.caller, 4, .mov .q (.reg .rsi) .rdx, 3),
   (.caller, 7, .mov .q (.reg .r9) .rdx, 3),
   (.caller, 10, .call 0xfffff281, 5),
   (.callee, 0, .movx false .d .b .rax (.mem (operand .rdi)), 3),
   (.callee, 3, .mov .q (.reg .rcx) .rsi, 3),
   (.callee, 6, .mov .q (.reg .rdx) .rdi, 3),
   (.callee, 9, .movI32 .rsi 1, 5),
   (.callee, 14, .aluI8 .q .cmp (.reg .rax) 0x7f, 4),
   (.callee, 18, .jcc8 .be 0x1e, 2),
   (.callee, 50, .mov .q (.mem (operand .rcx)) .rax, 3),
   (.callee, 53, .mov .d (.reg .rax) .rsi, 2),
   (.callee, 55, .ret, 1),
   (.caller, 15, .movI .d (.mem (operand .r9 16)) 0, 8),
   (.caller, 23, .aluI8 .d .add (.reg .rax) 4, 3),
   (.caller, 26, .movI .q (.mem (operand .r9 8)) 0, 8),
   (.caller, 34, .movx false .d .b .rax (.reg .rax), 3),
   (.caller, 37, .store .w (.mem (operand .r9 22)) .rax, 5),
   (.caller, 42, .alu .d .xor (.reg .rax) .rax, 2),
   (.caller, 44, .store .w (.mem (operand .r9 20)) .rax, 5),
   (.caller, 49, .ret, 1)]

private def Site.valid : Site → Prop
  | (w, offset, i, len) => offset + len ≤ w.code.length ∧
      Open9.decode ((w.code.drop offset).take len) = some (.ext8 (.base i), len)

private instance (site : Site) : Decidable site.valid := by
  rcases site with ⟨w, offset, i, len⟩
  unfold Site.valid
  infer_instance

private theorem pathValid : ∀ site ∈ path, Site.valid site := by
  have checked : path.all (fun site => decide site.valid) = true := by decide +kernel
  exact fun site mem => of_decide_eq_true ((List.all_eq_true.mp checked) site mem)

/-- Execute the proposed path with the decoded instruction semantics. The
checked listing and preservation of the executable bytes connect it to Open9. -/
private def follow (bias stopSP : Word) : List Site → MState → Option (MState × List MemEvent.Event)
  | [], s => some (s, [])
  | (w, o, i, len) :: rest, s =>
    if s.core.rip = (bias + BitVec.ofNat 64 w.va) + BitVec.ofNat 64 o ∧
        s.core.read .rsp ≠ stopSP then
      match Ext.exec i s.core s.memory len with
      | .ok c m => (follow bias stopSP rest ⟨c, m⟩).map fun (t, ev) =>
          (t, MemEvent.extAccesses i s.core len ++ ev)
      | _ => none
    else none

private theorem setSub_append_left {front rest : List MemEvent.Event} {W : Nat → Prop}
    (bound : ∀ a, MemEvent.writeSet (front ++ rest) a → W a) :
    ∀ a, MemEvent.writeSet front a → W a := by
  intro a h
  obtain ⟨ev, mem, writes, covers⟩ := h
  exact bound a ⟨ev, List.mem_append_left _ mem, writes, covers⟩

private theorem setSub_append_right {front rest : List MemEvent.Event} {W : Nat → Prop}
    (bound : ∀ a, MemEvent.writeSet (front ++ rest) a → W a) :
    ∀ a, MemEvent.writeSet rest a → W a := by
  intro a h
  obtain ⟨ev, mem, writes, covers⟩ := h
  exact bound a ⟨ev, List.mem_append_right _ mem, writes, covers⟩

private theorem follow_sound {bias : Word} {entry : MState} {byte : Byte}
    (admit : Entry bias entry byte)
    (loaded : ∀ w : Window, Ext.Loaded entry.memory (bias + BitVec.ofNat 64 w.va) w.code)
    {sites : List Site} (valid : ∀ site ∈ sites, Site.valid site)
    {s t : MState} {ev : List MemEvent.Event}
    (running : follow bias (entry.core.read .rsp + 8) sites s = some (t, ev))
    (frame : entry.memory.WritesWithin s.memory (writable entry))
    (bound : ∀ a, MemEvent.writeSet ev a → writable entry a) :
    Trace bias entry s ev t := by
  induction sites generalizing s ev with
  | nil =>
    simp only [follow, Option.some.injEq, Prod.mk.injEq] at running
    obtain ⟨rfl, rfl⟩ := running
    exact .nil _
  | cons site rest ih =>
    obtain ⟨w, off, instr, len⟩ := site
    simp only [follow] at running
    split at running
    next hp =>
      split at running
      next c m exec =>
        obtain ⟨⟨u, tail⟩, run, hh⟩ := Option.map_eq_some_iff.mp running
        simp only [Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        have localStep := (MemEvent.ext_local instr s.core len).frame
          (m := s.memory) (m₁ := m) (a := c) (by rw [exec]; rfl)
        have frameStep : s.memory.WritesWithin m (writable entry) :=
          ⟨localStep.regions, fun a hout => localStep.outside a
            (fun hin => hout (setSub_append_left bound a hin))⟩
        obtain ⟨fit, dec⟩ := valid (w, off, instr, len) (List.mem_cons_self)
        refine .cons w off len (.ext8 (.base instr)) (imageStable admit loaded frame w)
          hp.1 fit dec exec (fun h => hp.2 h.2) ?_
        exact ih (fun site h => valid site (List.mem_cons_of_mem _ h)) run
          (frame.trans frameStep) (setSub_append_right bound)
      contradiction
    next => contradiction

private theorem allowedEvents (s : MState) (a : Nat)
    (h : MemEvent.writeSet (events s) a) : writable s a := by
  obtain ⟨event, mem, writes, covers⟩ := h
  simp only [events, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [MemEvent.Kind.writes, MemEvent.Event.Covers, writable, within] <;> omega

private theorem outputAddress {bias : Word} {s : MState} {byte : Byte} (admit : Entry bias s byte)
    {off : Nat} (h : off < 24) :
    (s.core.read .rdx + BitVec.ofNat 64 off).toNat = output s + off := by
  have limit := admit.outputBound
  change output s + 24 ≤ 2 ^ 64 at limit
  have offLt : off < 2 ^ 64 := by omega
  have offNat : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt offLt
  have sumLt : (s.core.read .rdx).toNat + (BitVec.ofNat 64 off).toNat < 2 ^ 64 := by
    rw [offNat]
    change output s + off < 2 ^ 64
    omega
  rw [BitVec.toNat_add_of_lt sumLt, offNat]
  rfl

private theorem outputStore {bias : Word} {s : MState} {byte : Byte} (admit : Entry bias s byte)
    {mem : Memory} (frame : s.memory.WritesWithin mem (writable s))
    {off size : Nat} (positive : 0 < size) (fit : off + size ≤ 24) (value : Word) :
    ∃ after, Ext.storeN mem (s.core.read .rdx + BitVec.ofNat 64 off) size value = some after ∧
      Ext.Stored mem after (output s + off) (Ext.leBytes value size) ∧
      s.memory.WritesWithin after (writable s) := by
  have addr := outputAddress admit (off := off) (by omega)
  have allowed : mem.Permitted .write (output s + off) size := by
    apply (frame.permitted_iff ..).mpr
    have initial := (Memory.checkSpan_iff ..).mp admit.outputWrite
    apply (Memory.checkSpan_iff ..).mpr
    refine ⟨by omega, by omega, fun i hi => ?_⟩
    simpa only [Nat.add_assoc] using initial.2.2 (off + i) (by omega)
  obtain ⟨after, write, stored⟩ := Ext.storeN_isSome (v := value) (by rwa [addr])
  rw [addr] at stored
  exact ⟨after, write, stored, frame.step stored (by
    intro i hi
    simp only [Ext.length_leBytes] at hi
    exact .inr ⟨by omega, by omega⟩)⟩

private theorem compareByte (b : Byte) (h : b.toNat < 128) :
    Ext.Cond.be.eval (Ext.AluOp.flagsN .cmp (b.setWidth 64) (0x7f#64)) = some true := by
  change Ext.Cond.be.eval (Ext.subFlagsN (b.setWidth 64) (0x7f#64)) = some true
  rw [Ext.eval_subFlagsN]
  simp only [Ext.Cond.afterCmp, Option.some.injEq, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

private theorem inputLoad {s : MState} {byte : Byte} {memory : Memory}
    (read : memory.readBytes (cellByte s) 1 = some [byte]) :
    Ext.loadN memory (s.core.read .rsi + 4) 1 = some (byte.setWidth 64) := by
  rw [Ext.loadN, show memory.readBytes (s.core.read .rsi + 4).toNat 1 = _ from read]
  simp only [Option.map_some, Ext.leValue, Nat.mul_zero, Nat.add_zero]
  exact congrArg some (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]))

private theorem stackDepth (sp : Word) : sp ≠ sp + 8 ∧ sp - 8 ≠ sp + 8 := by
  constructor
  · intro h
    exact (by decide : (8 : Word) ≠ 0) (BitVec.add_right_eq_self.mp h.symm)
  · intro h
    have add := congrArg (fun w : Word => w + 8) h
    rw [BitVec.sub_add_cancel, BitVec.add_assoc] at add
    exact (by decide : (8 : Word) + 8 ≠ 0) (BitVec.add_right_eq_self.mp add.symm)

private theorem outsideCalleeSaved (r : Reg) (h : r ∈ sysv64.calleeSaved) :
    r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r9 ∧ r ≠ .rsp := by
  simp [sysv64] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem writtenRegs (core : State) (reg : Reg) (value : Word) :
    (core.write reg value).regs = Silmaril.Machine.RegisterFile.write core.regs reg value := rfl

private theorem readWritten (regs : RegisterFile Reg Word) (reg dest : Reg) (value : Word) :
    RegisterFile.write regs dest value reg = (if reg = dest then value else regs reg) := rfl

set_option maxRecDepth 4096 in
private theorem runPath {bias : Word} {s : MState} {byte : Byte} (admit : Entry bias s byte) :
    ∃ final, follow bias (s.core.read .rsp + 8) path s = some (final, events s) ∧
      FnContract.AbiReturn s.core s.memory final.core ∧
      s.memory.WritesWithin final.memory (writable s) ∧
      ∀ i : Fin 24, final.memory.bytes.get? (output s + i.val) =
        some (if i.val = 0 then byte else if i.val = 22 then 5 else 0) := by
  obtain ⟨pushMem, push, wrotePush⟩ := Ext.pushWord_isSome (v := bias + 0x117bf) admit.callWrite
  have pushWrite : s.memory.writeBytes (privateSlot s) (encodeWords [bias + 0x117bf]) =
      some pushMem := by
    obtain ⟨w, write, eq⟩ := Option.map_eq_some_iff.mp push
    have h : w = pushMem := congrArg Prod.snd eq
    rw [← h]
    exact write
  have framePush : s.memory.WritesWithin pushMem (writable s) := wrotePush.writesWithin (by
    intro offset h
    simp only [length_encodeWords_singleton] at h
    change writable s (privateSlot s + offset)
    exact .inl ⟨by omega, by omega⟩)
  have readByte : Ext.loadN pushMem (s.core.read .rsi + 4) 1 = some (byte.setWidth 64) := by
    apply inputLoad
    rw [framePush.readBytes (fun i hi => by
      have : i = 0 := by omega
      simpa [this] using admit.inputSeparate)]
    exact admit.input
  obtain ⟨keyMem, writeKey, wroteKey, frameKey⟩ :=
    outputStore admit framePush (off := 0) (size := 8) (by decide) (by decide) (byte.setWidth 64)
  obtain ⟨payloadMem, writePayload, wrotePayload, framePayload⟩ :=
    outputStore admit frameKey (off := 16) (size := 4) (by decide) (by decide) 0
  obtain ⟨pointerMem, writePointer, wrotePointer, framePointer⟩ :=
    outputStore admit framePayload (off := 8) (size := 8) (by decide) (by decide) 0
  obtain ⟨sizeMem, writeSize, wroteSize, frameSize⟩ :=
    outputStore admit framePointer (off := 22) (size := 2) (by decide) (by decide) 5
  obtain ⟨localMem, writeLocal, wroteLocal, frameLocal⟩ :=
    outputStore admit frameSize (off := 20) (size := 2) (by decide) (by decide) 0
  have readInner : keyMem.readBytes (privateSlot s) 8 = some (encodeWords [bias + 0x117bf]) := by
    have keyFrame : pushMem.WritesWithin keyMem (within (output s) 24) := wroteKey.writesWithin (by
      intro offset h
      simp only [Ext.length_leBytes] at h
      exact ⟨by omega, by omega⟩)
    rw [keyFrame.readBytes admit.callSeparate]
    exact wrotePush.readWith_self (by rw [length_encodeWords_singleton]; exact admit.callRead)
  have readOuter : localMem.readBytes (savedSlot s) 8 =
      some (encodeWords [FnContract.retOf s.core s.memory]) := by
    rw [frameLocal.readBytes admit.outerReturnSeparate]
    exact admit.abi.returnAddress
  simp only [BitVec.add_zero] at writeKey
  change s.memory.writeBytes (s.core.read .rsp - 8).toNat _ = _ at pushWrite
  change keyMem.readBytes (s.core.read .rsp - 8).toNat 8 = _ at readInner
  change localMem.readBytes (s.core.read .rsp).toNat 8 = _ at readOuter
  have cmp := compareByte byte admit.canonical
  obtain ⟨spNot, privateNot⟩ := stackDepth (s.core.read .rsp)
  simp only [BitVec.ofNat_eq_ofNat, State.read] at spNot privateNot readByte pushWrite readInner readOuter writeKey writePayload writePointer writeSize writeLocal cmp
  have pow : 8 ≤ 64 := by decide
  have widened : (byte.setWidth 32).setWidth 64 = byte.setWidth 64 :=
    BitVec.setWidth_setWidth (by decide)
  have byteBound : byte.toNat < 2 ^ 64 := by
    have := byte.isLt
    omega
  have addr8 := outputAddress admit (by decide : 8 < 24)
  have addr16 := outputAddress admit (by decide : 16 < 24)
  have addr20 := outputAddress admit (by decide : 20 < 24)
  have addr22 := outputAddress admit (by decide : 22 < 24)
  simp only [State.read] at addr8 addr16 addr20 addr22
  let input := s.core.read .rsi + 4
  let out := s.core.read .rdx
  let sp := s.core.read .rsp
  let core :=
    let c := ((s.core.write .rdi input).write .rsi out).write .r9 out
    let c := (c.write .rsp (sp - 8)).write .rax (byte.setWidth 64)
    let c := ((c.write .rcx out).write .rdx input).write .rsi 1
    let c := (c.write .rax 1).write .rsp sp
    ((c.write .rax 5).write .rax 5).write .rax 0
  let finalCore := { core.write .rsp (sp + 8) with
    rip := FnContract.retOf s.core s.memory
    flags := Ext.AluOp.flagsN .xor (5#32) 5 }
  refine ⟨⟨finalCore, localMem⟩, ?_, ?_, frameLocal, ?_⟩
  · simp only [finalCore, core, input, out, sp, path, follow, Window.va, admit.pc, Ext.exec, Ext.retire, Ext.writeRM,
      Ext.readRM, Ext.readNarrow, Ext.writeNarrow, Ext.Mem.addr, Ext.Base.value_reg, operand,
      Ext.Sz.bits, Ext.Sz.bytes, Ext.Narrow.bits, Ext.Narrow.bytes, Ext.Sz.write, Ext.Sz.read,
      Ext.aluStep, Ext.AluOp.resultN, reduceCtorEq, State.read, writtenRegs, readWritten,
      State.write_rip, State.write_flags, State.write_fsBase, Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Bool.false_eq_true,
      ↓reduceIte, true_and, eq_self, Option.map_none,
      Option.getD_none, pushWord, popWord, pushWrite,
      readByte, writeKey, writePayload, writePointer, writeSize, writeLocal, readInner, readOuter,
      wordOfBytes?_encodeWords, cmp, ite_eq_left spNot, ite_eq_left privateNot,
      widened, BitVec.add_assoc, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.reduceAdd, BitVec.reduceSignExtend,
      BitVec.reduceSetWidth, BitVec.reduceXOr, BitVec.reduceOfNat,
      BitVec.sub_add_cancel, BitVec.setWidth_setWidth_of_le _ pow,
      BitVec.setWidth_eq, events, MemEvent.extAccesses, MemEvent.memEv, MemEvent.rmEv,
      MemEvent.pushEv, MemEvent.popEv, privateSlot, cellByte, output, savedSlot,
      addr8, addr16, addr20, addr22, List.nil_append, List.cons_append]
  · refine ⟨rfl, by simp [finalCore, sp], ?_⟩
    intro r h
    obtain ⟨a, b, c, d, e, f, g⟩ := outsideCalleeSaved r h
    simp [finalCore, core, a, b, c, d, e, f, g]
  · intro i
    have hi := i.isLt
    let idx := i.val
    change localMem.bytes.get? (output s + idx) =
      some (if idx = 0 then byte else if idx = 22 then 5 else 0)
    have outside {before after : Memory} {off n : Nat} {v : Word}
        (stored : Ext.Stored before after (output s + off) (Ext.leBytes v n))
        (h : idx < off ∨ off + n ≤ idx) :
        after.bytes.get? (output s + idx) = before.bytes.get? (output s + idx) := by
      apply stored.frame.2
      simp only [Ext.length_leBytes]
      omega
    have installed {before after : Memory} {off n : Nat} {v : Word}
        (stored : Ext.Stored before after (output s + off) (Ext.leBytes v n))
        (lo : off ≤ idx) (hi : idx < off + n) :
        after.bytes.get? (output s + idx) =
          some (Silmaril.Machine.LittleEndian.wordByte v (idx - off)) := by
      have valid : idx - off < (Ext.leBytes v n).length := by simpa using (show idx - off < n by omega)
      have get := stored.installed (idx - off) valid
      rw [show output s + off + (idx - off) = output s + idx by omega] at get
      simpa only [Ext.leBytes, List.getElem_ofFn] using get
    have idxLt : idx < 24 := hi
    by_cases k : idx < 8
    · rw [outside wroteLocal (.inl (by omega)), outside wroteSize (.inl (by omega)),
        outside wrotePointer (.inl (by omega)), outside wrotePayload (.inl (by omega)),
        installed wroteKey (by omega) k]
      simp only [Nat.sub_zero, ite_eq_right (show idx ≠ 22 by omega)]
      by_cases hz : idx = 0
      · simp only [hz, ite_true, Silmaril.Machine.LittleEndian.wordByte, Nat.mul_zero,
          BitVec.ushiftRight_zero, BitVec.setWidth_setWidth_of_le _ pow, BitVec.setWidth_eq]
      · simp only [ite_eq_right hz, Option.some.injEq]
        apply BitVec.eq_of_toNat_eq
        simp only [Silmaril.Machine.LittleEndian.wordByte, BitVec.toNat_setWidth,
          BitVec.toNat_ushiftRight]
        rw [Nat.mod_eq_of_lt byteBound, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt (lt_of_lt_of_le byte.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]
        simp
    · by_cases p : idx < 16
      · rw [outside wroteLocal (.inl (by omega)), outside wroteSize (.inl (by omega)),
          installed wrotePointer (by omega) p]
        simp [Silmaril.Machine.LittleEndian.wordByte, show idx ≠ 0 by omega, show idx ≠ 22 by omega]
      · by_cases n : idx < 20
        · rw [outside wroteLocal (.inl (by omega)), outside wroteSize (.inl (by omega)),
            outside wrotePointer (.inr (by omega)), installed wrotePayload (by omega) n]
          simp [Silmaril.Machine.LittleEndian.wordByte, show idx ≠ 0 by omega, show idx ≠ 22 by omega]
        · by_cases l : idx < 22
          · rw [installed wroteLocal (by omega) l]
            simp [Silmaril.Machine.LittleEndian.wordByte, show idx ≠ 0 by omega, show idx ≠ 22 by omega]
          · rw [outside wroteLocal (.inr (by omega)), installed wroteSize (by omega) (by omega)]
            have : idx = 22 ∨ idx = 23 := by omega
            rcases this with h | h <;> simp [h, Silmaril.Machine.LittleEndian.wordByte]

theorem firstReturn_of_loaded {bias : Word} {entry : MState} {byte : Byte}
    (loaded : ∀ w : Window, Ext.Loaded entry.memory (bias + BitVec.ofNat 64 w.va) w.code)
    (admit : Entry bias entry byte) :
    ∃ final, Result bias entry final byte := by
  obtain ⟨final, running, abi, frame, contents⟩ := runPath admit
  have trace := follow_sound admit loaded pathValid running
    (Memory.WritesWithin.refl ..) (allowedEvents entry)
  exact ⟨final, trace, ⟨Trace.runsIn trace, abi.pc, abi.stack⟩, abi, frame, contents⟩

theorem firstReturn {bias : Word} {entry : MState} {byte : Byte}
    (placement : Silmaril.Elf.Placement F bias.toNat)
    (image : Silmaril.Elf.Link.ElfBind.RoLoaded F bias entry.memory)
    (admit : Entry bias entry byte) :
    ∃ final, Result bias entry final byte :=
  firstReturn_of_loaded (initialLoaded placement image) admit

end Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint
