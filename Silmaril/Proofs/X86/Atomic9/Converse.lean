module

public import Silmaril.Proofs.X86.Atomic9.Step
public import Silmaril.X86.MemEvent.Defs

/-!
# `Atomic9`: the converse of the listing law (proofs)

`exec_of_step_base`, `exec_of_step_new`: a step of `Atomic9.step` from a program counter at a
listed `Ext` base form or a listed atomic form is the executor of that form on the one memory
(header `Silmaril.X86.Atomic9.Converse.Thms`). The forward law is `step_of_listed`
(`Atomic9/Step.lean`); these follow its fetch computation and read off the executor's result
instead of assuming it.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Atomic9

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Atomic9

/-- A listed `Ext` base form that steps executed with `.ok`. -/
theorem exec_of_step_base {m m' : MState} {base : Word} {code : List Byte} {o l : Nat}
    {b : Silmaril.X86.Ext.Instr} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.open9 (.ext8 (.base b)), l))
    (hs : step m = some m') : exec (.open9 (.ext8 (.base b))) m.core m.memory l = .ok m'.core m'.memory := by
  have hd : Silmaril.X86.Ext.decode ((code.drop o).take l) = some (b, l) := by
    rcases decode_cases hdec with ⟨j, hj, hd⟩ | ⟨j, hj, -, -⟩
    · cases hj
      have h1 := Open9.decode_ext8 hd
      unfold Open.decode at h1
      split at h1
      · rename_i i' n' he
        simp only [Option.some.injEq, Prod.mk.injEq, Silmaril.X86.Ext8.Instr.base.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact Silmaril.X86.Ext8.decode_base_iff.mp he
      · split at h1
        · cases h1
        · split at h1 <;> cases h1
      · cases h1
    · cases hj
  obtain ⟨hlen, pos, -, -⟩ := Silmaril.X86.Ext.decode_length hd
  have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  have hf : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .decoded b l :=
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨_, fetched, hd⟩
  have h8 : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl (.decoded b l) := by
    rw [Silmaril.X86.Ext8.fetch_of_ne_undecodable (by rw [hf]; simp), hf]
  unfold step at hs
  rw [h8] at hs
  simp only [Open.step, h8] at hs
  subst hlen
  simp only [exec, Ext9.exec, Silmaril.X86.Ext8.exec]
  cases hx : Silmaril.X86.Ext.exec b m.core m.memory <;>
    simp only [hx, Open.ofResult, reduceCtorEq, Option.some.injEq] at hs
  subst hs
  exact hx

/-- A listed atomic form that steps executed with `.ok`. -/
theorem exec_of_step_new {m m' : MState} {base : Word} {code : List Byte} {o l : Nat}
    {j : New} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.new j, l))
    (hs : step m = some m') : exec (.new j) m.core m.memory l = .ok m'.core m'.memory := by
  have hL : decodeL ((code.drop o).take l) = some (j, l) := by
    rcases decode_cases hdec with ⟨j', hj, -⟩ | ⟨j', hj, -, hd⟩
    · cases hj
    · cases hj; exact hd
  obtain ⟨hnone, hbad, hne, hbad9, hnew, h1, h15⟩ := decodeL_spec hL
  have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  obtain ⟨more, hmore, hf8⟩ := Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [hmore, ext9_decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : fetchNew m.memory m.core.rip.toNat = some (some (j, l)) := by
    unfold fetchNew
    rw [hmore, decodeNew_append hnew more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hfs] at hs
  simp only [exec]
  cases hx : execNew j m.core m.memory (m.core.rip + BitVec.ofNat 64 l) <;>
    simp only [hx, Open.ofResult, reduceCtorEq, Option.some.injEq] at hs
  subst hs
  rfl

/-! ## The fetch of a listed form -/

/-- **The fetch of a listed `Ext` base form**: on a loaded image, `MemEvent.atomic9Fetch` at the
form's address returns it with its length. -/
theorem fetch_of_listed_base {mem : Memory} {base pc : Word} {code : List Byte} {o l : Nat}
    {b : Silmaril.X86.Ext.Instr} (hl : Loaded mem base code) (hrip : pc = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.open9 (.ext8 (.base b)), l)) :
    MemEvent.atomic9Fetch mem pc.toNat = some (.open9 (.ext8 (.base b)), l) := by
  have hd : Silmaril.X86.Ext.decode ((code.drop o).take l) = some (b, l) := by
    rcases decode_cases hdec with ⟨j, hj, hd⟩ | ⟨j, hj, -, -⟩
    · cases hj
      have h1 := Open9.decode_ext8 hd
      unfold Open.decode at h1
      split at h1
      · rename_i i' n' he
        simp only [Option.some.injEq, Prod.mk.injEq, Silmaril.X86.Ext8.Instr.base.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact Silmaril.X86.Ext8.decode_base_iff.mp he
      · split at h1
        · cases h1
        · split at h1 <;> cases h1
      · cases h1
    · cases hj
  obtain ⟨hlen, pos, -, -⟩ := Silmaril.X86.Ext.decode_length hd
  have hA : pc.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : mem.fetchBytes pc.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  have hf : Silmaril.X86.Ext.fetch mem pc.toNat = .decoded b l :=
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨_, fetched, hd⟩
  have h8 : Silmaril.X86.Ext8.fetch mem pc.toNat = .inl (.decoded b l) := by
    rw [Silmaril.X86.Ext8.fetch_of_ne_undecodable (by rw [hf]; simp), hf]
  simp only [MemEvent.atomic9Fetch, MemEvent.openFetch, h8, Option.map_some,
    Silmaril.X86.Ext.Instr.length, ← hlen]

/-- **The fetch of a listed atomic form**: on a loaded image, `MemEvent.atomic9Fetch` at the
form's address returns it with its length. -/
theorem fetch_of_listed_new {mem : Memory} {base pc : Word} {code : List Byte} {o l : Nat}
    {j : New} (hl : Loaded mem base code) (hrip : pc = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : decode ((code.drop o).take l) = some (.new j, l)) :
    MemEvent.atomic9Fetch mem pc.toNat = some (.new j, l) := by
  have hL : decodeL ((code.drop o).take l) = some (j, l) := by
    rcases decode_cases hdec with ⟨j', hj, -⟩ | ⟨j', hj, -, hd⟩
    · cases hj
    · cases hj; exact hd
  obtain ⟨hnone, hbad, hne, hbad9, hnew, h1, h15⟩ := decodeL_spec hL
  have hA : pc.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : mem.fetchBytes pc.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  obtain ⟨more, hmore, hf8⟩ := Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Ext9.fetchNew mem pc.toNat = none := by
    unfold Ext9.fetchNew
    rw [hmore, ext9_decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : fetchNew mem pc.toNat = some (some (j, l)) := by
    unfold fetchNew
    rw [hmore, decodeNew_append hnew more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [MemEvent.atomic9Fetch, hf8, hfn, hfs]

end Silmaril.Proofs.X86.Atomic9
