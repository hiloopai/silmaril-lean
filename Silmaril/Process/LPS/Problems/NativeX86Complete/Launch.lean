module

public import Silmaril.Process.LPS.Machines.X86RealisticLaunch
public import Silmaril.Process.LPS.Problems.NativeX86

/-!
# The realistic x86-64 launch domain is inhabited

On a well-formed snapshot (`NativeX86.ImageWf`) every realistic valid input has an exact
realistic launch (`imageWf_realistic_entry`): no vDSO, no vsyscall page, real credentials, no
rseq entries, the stack top at `STACK_TOP` and the one-byte filename `"a"`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.NativeX86Complete

open Silmaril.Process.LPS Silmaril.Process.LPS.Shapes Silmaril.Process.LPS.Machines

abbrev Snapshot := X86Launch.Snapshot
abbrev Choices := X86RealisticLaunch.Choices
abbrev HwcapDomain := Problems.NativeX86.HwcapDomain

/-! ## The realistic launch domain is inhabited -/

section Inhabited

theorem uns_sub_of_le {a b : Word} (h : uns b ≤ uns a) : uns (a - b) = uns a - uns b := by
  unfold uns at *
  rw [BitVec.toNat_sub]
  omega

theorem uns_natToWord {n : Nat} (h : n < 2 ^ 64) : uns (natToWord n) = n :=
  uns_zw_of_bounds (Int.natCast_nonneg n) (by exact_mod_cast h)

theorem uns_sub_natToWord {a : Word} {n : Nat} (h : (n : Int) ≤ uns a) :
    uns (a - natToWord n) = uns a - n := by
  have lt : uns a < 2 ^ 64 := by unfold uns; omega
  have hn : uns (natToWord n) = n := uns_natToWord (by omega)
  rw [uns_sub_of_le (by rw [hn]; exact h), hn]

theorem uns_alignDown16 (w : Word) :
    uns (X86RealisticLaunch.alignDown16 w) = uns w - uns w % 16 := by
  unfold X86RealisticLaunch.alignDown16
  have disj : (w &&& ~~~(15 : Word)) &&& (w &&& 15) = 0#64 := by
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    generalize w[i] = x
    generalize (15 : Word)[i] = y
    cases x <;> cases y <;> rfl
  have cover : (w &&& ~~~(15 : Word)) + (w &&& 15) = w := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ disj]
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    generalize w[i] = x
    generalize (15 : Word)[i] = y
    cases x <;> cases y <;> rfl
  have low : (w &&& (15 : Word)).toNat = w.toNat % 16 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod w.toNat 4
  have sum := BitVec.toNat_add_of_and_eq_zero disj
  rw [cover] at sum
  unfold uns
  omega

/-- The witness launch choice: no vDSO, no vsyscall page, real credentials, no rseq entries,
the stack top at `STACK_TOP`, the one-byte filename `"a"`, and no `arch_align_stack` gap
beyond the 16-byte rounding. -/
def witnessChoices (inp : ProcInput) : Choices :=
  let L := (flattenStrings inp.argv ++ flattenStrings inp.envp ++ flattenStrings [[97]] ++
    List.replicate 8 0).length
  { vdso := none, minSigStkSz := 2048, hwcap2 := 0, euid := inp.uid, egid := inp.gid,
    secure := 0, rseq := none, execfn := [97], stackTop := 0x7ffffffff000,
    alignedTop := 0x7ffffffff000 - natToWord (L + (16 - L % 16) % 16), vsyscall := false }

/-- The witness entry: the realistic stack pointer of the witness choice, a valid break, and the
highest mmap base. -/
def witnessEntry (snap : Snapshot) (brk : Word) (inp : ProcInput) : ExecEntry :=
  ⟨X86RealisticLaunch.entrySp snap.image (witnessChoices inp) inp, brk, 0x7ffff7fff000,
    ⟨0, fun _ => 0⟩⟩

theorem witness_exact (inp : ProcInput) : X86RealisticLaunch.Exact inp (witnessChoices inp) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem witness_auxiliaryEntries_length (img : Image) (inp : ProcInput) :
    (X86RealisticLaunch.auxiliaryEntries img (witnessChoices inp) inp).length = 20 := rfl

/-! ### Facts about the witness -/

theorem witness_stringArea (inp : ProcInput) :
    X86RealisticLaunch.stringArea (witnessChoices inp) inp =
      flattenStrings inp.argv ++ flattenStrings inp.envp ++ [97, 0] ++ List.replicate 8 0 := rfl

theorem witness_area_length (inp : ProcInput) :
    ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) =
      (flattenStrings inp.argv).length + (flattenStrings inp.envp).length + 10 := by
  rw [witness_stringArea]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  push_cast
  omega

theorem uns_stackTopMax_word : uns (0x7ffffffff000 : Word) = 0x7ffffffff000 := by decide

theorem witness_stackTop (inp : ProcInput) :
    (witnessChoices inp).stackTop = 0x7ffffffff000 := rfl

theorem witness_alignedTop (inp : ProcInput) :
    (witnessChoices inp).alignedTop = 0x7ffffffff000 -
      natToWord ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length +
        (16 - (X86RealisticLaunch.stringArea (witnessChoices inp) inp).length % 16) % 16) := rfl

theorem witness_uns_alignedTop (inp : ProcInput)
    (small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30) :
    uns (witnessChoices inp).alignedTop = 0x7ffffffff000 -
      (((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length +
        (16 - (X86RealisticLaunch.stringArea (witnessChoices inp) inp).length % 16) % 16 : Nat) :
          Int) := by
  rw [witness_alignedTop, uns_sub_natToWord (by rw [uns_stackTopMax_word]; omega),
    uns_stackTopMax_word]

theorem witness_uns_stringBase (inp : ProcInput)
    (small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30) :
    uns (X86RealisticLaunch.stringBase (witnessChoices inp) inp) = 0x7ffffffff000 -
      ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) := by
  unfold X86RealisticLaunch.stringBase
  rw [witness_stackTop, uns_sub_natToWord (by rw [uns_stackTopMax_word]; omega),
    uns_stackTopMax_word]

theorem uns_23 : uns (23 : Word) = 23 := by decide

theorem witness_uns_randomPtr (inp : ProcInput)
    (small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30) :
    uns (X86RealisticLaunch.randomPtr (witnessChoices inp)) =
      uns (witnessChoices inp).alignedTop - 23 := by
  unfold X86RealisticLaunch.randomPtr
  rw [uns_sub_of_le (by rw [witness_uns_alignedTop inp small, uns_23]; omega), uns_23]

theorem witness_tableWords (img : Image) (inp : ProcInput) :
    X86RealisticLaunch.tableWords img (witnessChoices inp) inp =
      43 + inp.argv.length + inp.envp.length := by
  unfold X86RealisticLaunch.tableWords
  rw [witness_auxiliaryEntries_length]
  omega

theorem witness_uns_sp (snap : Snapshot) (brk : Word) (inp : ProcInput)
    (small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30)
    (few : inp.argv.length + inp.envp.length ≤ 2 ^ 20) :
    uns (witnessEntry snap brk inp).sp =
      (uns (X86RealisticLaunch.randomPtr (witnessChoices inp)) -
        ((8 * X86RealisticLaunch.tableWords snap.image (witnessChoices inp) inp : Nat) : Int)) -
      (uns (X86RealisticLaunch.randomPtr (witnessChoices inp)) -
        ((8 * X86RealisticLaunch.tableWords snap.image (witnessChoices inp) inp : Nat) : Int)) % 16 := by
  have e : (witnessEntry snap brk inp).sp = X86RealisticLaunch.alignDown16
      (X86RealisticLaunch.randomPtr (witnessChoices inp) -
        natToWord (8 * X86RealisticLaunch.tableWords snap.image (witnessChoices inp) inp)) := rfl
  have below := uns_sub_natToWord
    (a := X86RealisticLaunch.randomPtr (witnessChoices inp))
    (n := 8 * X86RealisticLaunch.tableWords snap.image (witnessChoices inp) inp) (by
      rw [witness_uns_randomPtr inp small, witness_uns_alignedTop inp small,
        witness_tableWords]
      omega)
  rw [e, uns_alignDown16, below]

theorem witness_stackBytes_length (snap : Snapshot) (brk : Word) (inp : ProcInput)
    (small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30)
    (few : inp.argv.length + inp.envp.length ≤ 2 ^ 20) :
    ((X86RealisticLaunch.stackBytes snap.image (witnessChoices inp)
      (witnessEntry snap brk inp).sp (witnessEntry snap brk inp).draw.random inp).length : Int) =
      0x7ffffffff000 - uns (witnessEntry snap brk inp).sp := by
  have sp := witness_uns_sp snap brk inp small few
  have base := witness_uns_stringBase inp small
  have rnd := witness_uns_randomPtr inp small
  have top := witness_uns_alignedTop inp small
  have words := witness_tableWords snap.image inp
  have aux := witness_auxiliaryEntries_length snap.image inp
  unfold X86RealisticLaunch.stackBytes
  simp only [List.length_append, List.length_replicate, Problems.NativeX86.flatMap_wordLe8_length,
    Problems.NativeX86.stringAddrs_length, Problems.NativeX86.buildAuxv_length, aux,
    X86RealisticLaunch.wordLe8_length, atRandomBytes, List.length_map, List.length_range,
    X86Launch.platformBytes, List.length_cons, List.length_nil]
  rw [base, rnd, top]
  rw [rnd, top, words] at sp
  omega

theorem witness_validChoices (inp : ProcInput) (hw32 : uns inp.hwcap < 2 ^ 32)
    (creds : ValidCreds inp)
    (small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30) :
    X86RealisticLaunch.ValidChoices inp (witnessChoices inp) := by
  have top := witness_uns_alignedTop inp small
  have base := witness_uns_stringBase inp small
  have vdso : X86RealisticLaunch.ValidVdso (witnessChoices inp).vdso := trivial
  have rseq : X86RealisticLaunch.ValidRseq (witnessChoices inp).rseq := trivial
  have secure : uns (witnessChoices inp).secure ≤ 1 := show uns (0 : Word) ≤ 1 by decide
  have features : X86RealisticLaunch.ValidFeatures inp (witnessChoices inp) :=
    ⟨hw32, show uns (0 : Word) < 4 by decide, show 512 ≤ uns (2048 : Word) by decide,
      show uns (2048 : Word) ≤ 0x10000 by decide, show uns (2048 : Word) % 16 = 0 by decide⟩
  have vcreds : X86RealisticLaunch.ValidCreds inp (witnessChoices inp) :=
    ⟨creds.1, creds.2, .inl ⟨rfl, rfl⟩⟩
  have e1 : 0 < (witnessChoices inp).execfn.length := show 0 < [(97 : Byte)].length by decide
  have e2 : (witnessChoices inp).execfn.length < X86RealisticLaunch.maxArgStrlen :=
    show [(97 : Byte)].length < X86RealisticLaunch.maxArgStrlen by decide
  have e3 : (0 : Byte) ∉ (witnessChoices inp).execfn := show (0 : Byte) ∉ [(97 : Byte)] by decide
  have t1 : uns (witnessChoices inp).stackTop % pageSize = 0 :=
    show uns (0x7ffffffff000 : Word) % pageSize = 0 by decide
  have t2 : X86RealisticLaunch.stackTopMax - X86RealisticLaunch.stackTopRandomPages * pageSize ≤
      uns (witnessChoices inp).stackTop :=
    show X86RealisticLaunch.stackTopMax - X86RealisticLaunch.stackTopRandomPages * pageSize ≤
      uns (0x7ffffffff000 : Word) by decide
  have t3 : uns (witnessChoices inp).stackTop ≤ X86RealisticLaunch.stackTopMax :=
    show uns (0x7ffffffff000 : Word) ≤ X86RealisticLaunch.stackTopMax by decide
  have t4 : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) <
      uns (witnessChoices inp).stackTop := by
    rw [witness_stackTop, uns_stackTopMax_word]; omega
  exact ⟨vdso, rseq, secure, features, vcreds, e1, e2, e3, t1, t2, t3, t4,
    by rw [top]; omega, by rw [top, base]; omega, by rw [top, base]; omega⟩

theorem witness_mmapBase (snap : Snapshot) (brk : Word) (inp : ProcInput) :
    x86LaunchBounds.mmapBaseMin ≤ uns (witnessEntry snap brk inp).mmapBase ∧
      uns (witnessEntry snap brk inp).mmapBase ≤ x86LaunchBounds.mmapBaseMax ∧
      uns (witnessEntry snap brk inp).mmapBase % pageSize = 0 :=
  show x86LaunchBounds.mmapBaseMin ≤ uns (0x7ffff7fff000 : Word) ∧
    uns (0x7ffff7fff000 : Word) ≤ x86LaunchBounds.mmapBaseMax ∧
    uns (0x7ffff7fff000 : Word) % pageSize = 0 by decide

theorem spWindowLo_eq : x86LaunchBounds.spWindowLo =
    0x7ffffffff000 - (0x3fffff + 2) * 4096 - 2 * 1024 * 1024 * 1024 := by decide

theorem taskSize_eq : x86AddressSpace.taskSize = 0x7ffffffff000 := rfl

section Conjuncts

variable (snap : Snapshot) (brk : Word) (inp : ProcInput)
  (small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30)
  (few : inp.argv.length + inp.envp.length ≤ 2 ^ 20)

include small few in
theorem witness_table_fits :
    uns (witnessEntry snap brk inp).sp +
        8 * (X86RealisticLaunch.tableWords snap.image (witnessChoices inp) inp : Int) ≤
      uns (X86RealisticLaunch.randomPtr (witnessChoices inp)) := by
  have sp := witness_uns_sp snap brk inp small few
  have nn := Int.emod_nonneg (uns (X86RealisticLaunch.randomPtr (witnessChoices inp)) -
    ((8 * X86RealisticLaunch.tableWords snap.image (witnessChoices inp) inp : Nat) : Int))
    (by decide : (16 : Int) ≠ 0)
  push_cast at sp nn
  omega

include small few in
theorem witness_table_below_top :
    23 + 8 * (X86RealisticLaunch.tableWords snap.image (witnessChoices inp) inp : Int) <
      uns (witnessChoices inp).alignedTop := by
  have top := witness_uns_alignedTop inp small
  have words := witness_tableWords snap.image inp
  rw [words, top]
  omega

include small few in
theorem witness_pageTop :
    entryPageTop (witnessEntry snap brk inp).sp
        (X86RealisticLaunch.stackBytes snap.image (witnessChoices inp)
          (witnessEntry snap brk inp).sp (witnessEntry snap brk inp).draw.random inp) ≤
      x86AddressSpace.taskSize := by
  have len := witness_stackBytes_length snap brk inp small few
  unfold entryPageTop entryBlockTop pageRoundUp pageSize
  rw [len, taskSize_eq]
  omega

include small few in
theorem witness_sp_low : x86LaunchBounds.spWindowLo ≤ uns (witnessEntry snap brk inp).sp := by
  have sp := witness_uns_sp snap brk inp small few
  have rnd := witness_uns_randomPtr inp small
  have top := witness_uns_alignedTop inp small
  have words := witness_tableWords snap.image inp
  rw [rnd, top, words] at sp
  rw [spWindowLo_eq]
  omega

end Conjuncts

end Inhabited


end Silmaril.Process.LPS.Problems.NativeX86Complete
