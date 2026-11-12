module

public import Silmaril.X86.Str9Fs.Defs
public import Silmaril.X86.Str9.Thms
public import Silmaril.X86.Ext9.Thms

/-!
# `Str9Fs`: conservative extension of `Str9`, the listing law, the machine

* `step_of_str9`: **every `Str9` step is a step** (the new forms are tried only where
  `Ext8`, `Ext9` and the string forms all reject the fetch window), hence `extendsStr9 :
  Str9.isa.Extends isa` (identity lens), and `extendsOpen9`, `extendsOpen` by composition. So
  every generic transfer along `Isa.Extends` applies (`FnContract.lift`, `Spec.Strict.lift`,
  `Sep.Triple.lift`, ...): **every `Str9`/`Open9`/`Open` proof lifts unchanged.**
* `good_pNewAtomic` (`Atomic9.pNew`, which silmaril defines without its decoder laws) and
  `good_pFs`: the parsers have the prefix laws, so `decodeNew_append`: a decoded new form keeps
  its reading whatever bytes follow.
* `step_of_fetch_new`, `step_of_listed_new`, `step_of_listed`: the listing law; `isa`: the
  machine as a `SegVC.Isa MState`.
* Vectors: `decode_errno_store`, `decode_lock_cmpxchg`, `decode_canary` (the base-less canary
  stays `Str9`'s), `decode_fs_rip_none`, and `exec_errno_store` (the `errno` write lands at
  `fsBase + rdx`).

Proved with the standard axioms only. What is **not** claimed: that the handwritten FS and
atomic semantics match hardware (`Atomic9`'s were differentially tested by silmaril; the FS
forms reuse `Ext9`'s semantics at a shifted base and are not tested here).
-/

@[expose] public section

namespace Silmaril.X86.Str9Fs

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded PResult ByteParser)
open Silmaril.X86.Ext.ByteParser
open Silmaril.Process (Memory)

/-! ## Decoder laws -/

theorem good_memP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (Silmaril.X86.Atomic9.memP rex mp) := by
  unfold Silmaril.X86.Atomic9.memP; split
  · exact good_pure _
  · exact good_fail

theorem good_rmP (l : Bool) (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (Silmaril.X86.Atomic9.rmP l rex mp) := by
  unfold Silmaril.X86.Atomic9.rmP
  exact good_ite (good_map _ (good_memP _ _)) (good_pure _)

theorem good_rm8P (l : Bool) (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (Silmaril.X86.Atomic9.rm8P l rex mp) := by
  unfold Silmaril.X86.Atomic9.rm8P
  refine good_ite ?_ (good_pure _)
  split
  · exact good_pure _
  · exact good_fail

theorem good_fsMemP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (fsMemP rex mp) := by
  unfold fsMemP; split
  · exact good_ite good_fail (good_pure _)
  · exact good_fail

/-- Discharge `Good` goals of the parsers built from the combinators. -/
macro "good_tac" : tactic => `(tactic| repeat (first
  | exact good_fail | exact good_byte | exact Silmaril.X86.Ext8.good_pM
  | exact Silmaril.X86.Ext.good_pImm32 | exact Silmaril.X86.Ext9.good_pIb32
  | exact good_pure _ | exact Silmaril.X86.Ext8.good_optP _
  | exact good_memP _ _ | exact good_rmP _ _ _ | exact good_rm8P _ _ _ | exact good_fsMemP _ _
  | apply good_ite | apply good_map | apply good_bind | intro _))

theorem good_pBodyAtomic (l : Bool) (rex : Option Silmaril.X86.Ext.Rex)
    (opc : Silmaril.X86.Ext.Opc) : Good (Silmaril.X86.Atomic9.pBody l rex opc) := by
  cases opc <;> simp only [Silmaril.X86.Atomic9.pBody] <;> good_tac

theorem good_pLocked : Good Silmaril.X86.Atomic9.pLocked := by
  unfold Silmaril.X86.Atomic9.pLocked
  exact good_bind Silmaril.X86.Ext.good_pHead fun _ => good_ite (good_pBodyAtomic _ _ _) good_fail

/-- **`Atomic9`'s parser has the prefix laws.** -/
theorem good_pNewAtomic : Good Silmaril.X86.Atomic9.pNew := by
  unfold Silmaril.X86.Atomic9.pNew
  refine good_bind Silmaril.X86.Ext.good_pHead fun h => good_ite good_fail ?_
  split
  · exact good_ite good_pLocked (good_pBodyAtomic _ _ _)
  · exact good_ite (good_pure _) good_fail
  · exact good_fail

theorem good_pFsBody (rex : Option Silmaril.X86.Ext.Rex) (opc : Silmaril.X86.Ext.Opc) :
    Good (pFsBody rex opc) := by
  cases opc <;> simp only [pFsBody] <;> good_tac

/-- **The FS parser has the prefix laws.** -/
theorem good_pFs : Good pFs :=
  good_bind Silmaril.X86.Ext.good_pHead fun _ => good_ite (good_pFsBody _ _) good_fail

/-- An FS form is never an atomic form: both parsers read the head, and `Atomic9` refuses
the FS override. -/
theorem atomic_bad_of_pFs {w : List Byte} {i : New} {rest : List Byte}
    (h : pFs w = .ok i rest) : Silmaril.X86.Atomic9.pNew w = .bad := by
  unfold pFs at h
  cases hh : Silmaril.X86.Ext.pHead w with
  | ok hd tail =>
    rw [bind_ok hh] at h
    unfold Silmaril.X86.Atomic9.pNew
    rw [bind_ok hh]
    by_cases c : hd.1 = true ∧ hd.2.1 = .none
    · simp [c.1]
    · simp only [c, ite_false] at h; cases h
  | eof => simp [ByteParser.bind, hh] at h
  | bad => simp [ByteParser.bind, hh] at h

theorem atomicDecode_none_of_pFs {w : List Byte} {i : New} {rest : List Byte}
    (h : pFs w = .ok i rest) (more : List Byte) :
    Silmaril.X86.Atomic9.decodeNew (w ++ more) = none := by
  unfold Silmaril.X86.Atomic9.decodeNew
  rw [good_pNewAtomic.bad (atomic_bad_of_pFs h) more]

/-- **A decoded new form keeps its reading whatever bytes follow.** -/
theorem decodeNew_append {w : List Byte} {i : New} {n : Nat} (h : decodeNew w = some (i, n))
    (more : List Byte) : decodeNew (w ++ more) = some (i, n) := by
  unfold decodeNew at h ⊢
  split at h
  · rename_i j k hj
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold Silmaril.X86.Atomic9.decodeNew at hj ⊢
    split at hj
    · rename_i a rest hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      obtain ⟨-, ext⟩ := good_pNewAtomic.ok hp
      rw [ext more]
      simp only [List.length_append, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · cases hj
  · split at h
    · rename_i a rest hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [atomicDecode_none_of_pFs hp more]
      obtain ⟨-, ext⟩ := good_pFs.ok hp
      simp only [ext more, List.length_append, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · cases h

/-- No string form starts with bytes `strBad` accepts. -/
theorem decodeStr_none_of_strBad {w : List Byte} (h : strBad w = true) (more : List Byte) :
    Silmaril.X86.Str9.decodeStr (w ++ more) = none := by
  match w, h with
  | [b], h =>
    simp only [strBad, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    unfold Silmaril.X86.Str9.decodeStr
    split <;> simp_all
  | [b, c], h =>
    simp only [strBad, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
      Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
    unfold Silmaril.X86.Str9.decodeStr
    split <;> simp_all
  | b :: c :: d :: rest, h =>
    simp only [strBad, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
      Bool.and_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    unfold Silmaril.X86.Str9.decodeStr
    split <;> simp_all

theorem decodeL_spec {w : List Byte} {i : New} {n : Nat} (h : decodeL w = some (i, n)) :
    Silmaril.X86.Ext.decode w = none ∧ Silmaril.X86.Open9.newBad w = true ∧
      Silmaril.X86.Open9.rawNotEof w = true ∧ Silmaril.X86.Str9.ext9Bad w = true ∧
      strBad w = true ∧ decodeNew w = some (i, n) ∧ 0 < n ∧ n ≤ maxInstrLength := by
  unfold decodeL at h
  split at h
  · rename_i j k hj
    split at h
    · rename_i c
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, hj, c.2.2.2.2.2⟩
    · cases h
  · cases h

/-! ## Conservative extension -/

/-- **Every `Str9` step is a step.** -/
theorem step_of_str9 {m t : MState} (h : Silmaril.X86.Str9.step m = some t) : step m = some t := by
  unfold Silmaril.X86.Str9.step at h
  unfold step
  split at h
  · rename_i h8
    rw [h8]
    simp only
    split at h
    · rename_i i n h9; rw [h9]; exact h
    · cases h
    · rename_i h9
      rw [h9]
      simp only
      split at h
      · rename_i i n hs; rw [hs]; exact h
      · cases h
  · rename_i h8
    split
    · rename_i h8'; exact absurd h8' h8
    · exact h

/-! ## The listing law -/

/-- **The fetch form of the new-form law**: bytes `w` fetched with execute permission at the
program counter that `decodeL` reads as a new form of length `l`, and that execute, are one
step. -/
theorem step_of_fetch_new {m : MState} {l : Nat} {w : List Byte} {i : New} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l)) (hx : execNew i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨hnone, hbad, hne, hbad9, hstr, hdn, -, h15⟩ := decodeL_spec hdec
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Silmaril.X86.Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr m.memory m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, decodeStr_none_of_strBad hstr more]
    rfl
  have hnew : fetchNew m.memory m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchNew
    rw [hmore, decodeNew_append hdn more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hfs, hnew, hx, Silmaril.X86.Open.ofResult]

/-- **The new-form listing law.** -/
theorem step_of_listed_new {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : New}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execNew i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  have h1 : 0 < l := (decodeL_spec hdec).2.2.2.2.2.2.1
  have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_new fetched hdec hx

/-- **The listing law of the whole machine.** -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  unfold decode at hdec
  split at hdec
  · rename_i j n hj
    simp only [Option.some.injEq, Prod.mk.injEq] at hdec
    obtain ⟨rfl, rfl⟩ := hdec
    exact step_of_str9 (Silmaril.X86.Str9.step_of_listed hl hrip hfit hj hx)
  · cases hs : decodeL ((code.drop o).take l) with
    | none => rw [hs] at hdec; cases hdec
    | some p =>
      obtain ⟨j, n⟩ := p
      rw [hs] at hdec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl⟩ := hdec
      exact step_of_listed_new hl hrip hfit hs hx

/-! ## The machine -/

/-- **`Str9Fs` as a segment-VC instance.** -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa MState where
  Instr := Instr
  instDecEq := inferInstance
  decode := decode
  exec := exec
  core := MState.core
  mem := MState.memory
  upd := fun _ c m => ⟨c, m⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_listed hl hrip hfit hdec hx

@[simp] theorem isa_step : isa.step = step := rfl

/-- **`Str9Fs` extends `Str9`** on the same states (identity lens): every `Str9` contract,
triple or run lifts. -/
@[reducible] def extendsStr9 : Silmaril.X86.Str9.isa.Extends isa :=
  .ofStep (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ h => h) step_of_str9

/-- `Str9Fs` extends the open machine over `Ext9`. -/
@[reducible] def extendsOpen9 : Silmaril.X86.Open9.isa.Extends isa :=
  Silmaril.X86.Str9.extendsOpen9.trans extendsStr9

/-- `Str9Fs` extends the open machine over `Ext8`. -/
@[reducible] def extendsOpen : Silmaril.X86.Open.isa.Extends isa :=
  Silmaril.X86.Str9.extendsOpen.trans extendsStr9

/-! ## Decoding vectors (kernel-checked) -/

/-- `mov %eax, %fs:(%rdx)`: the `errno` store. -/
theorem decode_errno_store : decode [0x64, 0x89, 0x02] =
    some (.new (.fs (ext (.mov .d (.mem fs0) .rax)) (Silmaril.X86.Ext.Mem.ofReg .rdx none 0)), 3) := by
  decide

/-- `lock cmpxchg %edx, (%rbx)`. -/
theorem decode_lock_cmpxchg : (decode [0xF0, 0x0F, 0xB1, 0x13]).map (·.2) = some 4 := by decide

/-- `mov %fs:0x28, %rax` (the canary) stays a `Str9` instruction. -/
theorem decode_canary : (decode [0x64, 0x48, 0x8B, 0x04, 0x25, 0x28, 0, 0, 0]).map
    (fun p => match p.1 with | .str9 _ => true | .new _ => false) = some true := by decide

/-- `mov %fs:0x0(%rip), %eax` (RIP-relative under FS) is not read. -/
theorem decode_fs_rip_none : decode [0x64, 0x8B, 0x05, 0, 0, 0, 0] = none := by decide

/-! ## A semantic vector -/

open Silmaril.X86 in
/-- **The `errno` store** `mov %eax, %fs:(%rdx)` writes the low four bytes of `rax` at the
linear address `fsBase + rdx` and changes nothing else but `rip`. -/
theorem exec_errno_store (s : State) (mem : Memory) :
    execNew (.fs (ext (.mov .d (.mem fs0) .rax)) (Ext.Mem.ofReg .rdx none 0)) s mem 3 =
      match Ext.storeN mem (s.fsBase + s.read .rdx) 4 ((s.read .rax).setWidth 32 |>.setWidth 64) with
      | some mem' => .ok { s with rip := s.rip + 3 } mem'
      | none => .dataFault := by
  simp [execNew, execFs, ext, Ext9.exec, Ext8.exec, Ext.exec, Ext.writeRM, Ext.retire, fs0,
    Ext.Mem.fsAt, Ext.Mem.ofFs, Ext.Mem.ofReg, Ext.Mem.addr, Ext.Base.value]
  simp only [Ext.Sz.bytes, Ext.Sz.read, State.read]
  cases h : Ext.storeN mem (s.fsBase + s.regs Reg.rdx) 4
    (BitVec.setWidth 64 (BitVec.setWidth 32 (s.regs Reg.rax))) <;> simp [h]

end Silmaril.X86.Str9Fs
