module

public import Silmaril.Process.LPS.NativeX86Refusal
public import Silmaril.Process.LPS.NativeX86Statements

/-! # x86-64 statements over the complete native table, and their input/entry domain

`profile isa features` is #3492's native statement profile (x86 launch, x86 stack, native
allocation classifier) with the complete native system `NativeX86.All.system` and an explicit
**feature profile** for the auxiliary vector.

## The auxiliary vector

The x86 launch (`Machines.X86Launch.auxiliaryEntries`) advertises:

* `AT_HWCAP` = `input.hwcap`. On x86-64 Linux this is CPUID leaf 1 `EDX`
  (`boot_cpu_data.x86_capability[CPUID_1_EDX]`), a CPU fact. `ValidInputFor none` leaves it
  **quantified** (any value: a statement then holds on every CPU); `ValidInputFor (some f)`
  pins it to the declared profile `f.hwcap`. #3492's `Statements.ValidInput` is the profile
  `minimal` (`hwcap = 0`, `validInputFor_minimal`). A statement over the quantified domain
  implies the one over any declared profile (`agreement_of_quantified`).
* `AT_PLATFORM` points into the entry block at `platformOffset`, where the launch writes
  `"x86_64\0"` (`platform_entry`, `X86Launch.stackBytes`).
* `AT_SYSINFO_EHDR` = 0 and `AT_HWCAP2` = 0: **declared absent** (a kernel booted with
  `vdso=0`, and no `HWCAP2_FSGSBASE`/`HWCAP2_RING3MWAIT` advertisement). Linux omits
  `AT_SYSINFO_EHDR` instead of writing 0 when the vDSO is off; `getauxval` reads both as
  absent. This is a declared launch profile, recorded, not a claim about default kernels.

The entry-stack layout itself is the launch's (as LPS's riscv64 layout is LPS's), not Linux's
`create_elf_tables` order; x86-64's `AT_MINSIGSTKSZ` and the rseq entries are not advertised.

**Fidelity gap.** No supported kernel produces this auxiliary vector: Linux x86-64 v6.13-v6.18
always emits `AT_MINSIGSTKSZ`, sets `HWCAP2_FSGSBASE` on most CPUs, and omits (rather than
zeroes) `AT_SYSINFO_EHDR` when the vDSO is off. Only `AT_HWCAP` is quantified. The statements
therefore cover programs launched with this declared auxiliary vector and stack; a program
whose behaviour depends on `AT_HWCAP2`, `AT_MINSIGSTKSZ`, the vDSO entry or the entry order is
not covered for Linux's actual launch. Quantifying `AT_HWCAP2` and `AT_MINSIGSTKSZ` (input
chosen values) is the next variant.

## The entry domain is inhabited

`validEntry_witness` builds a valid entry for **every** valid input and every entry draw, for
any valid snapshot whose segments lie below the stack reservation; the agreement statements'
entry premises are therefore not vacuous (`domain_nonempty`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.All

open Silmaril.Process.LPS Machines

/-! ## Feature profiles and input domains -/

/-- An x86-64 CPU feature profile, as advertised in `AT_HWCAP` (CPUID.01H:EDX). -/
structure X86Features where
  hwcap : Word
  deriving DecidableEq, Repr

/-- #3492's minimal profile: nothing advertised. -/
def minimal : X86Features := ⟨0⟩

/-- The valid inputs: LPS's core checks, the declared abort stance, and `AT_HWCAP` either
quantified (`none`) or pinned to a declared profile. -/
def ValidInputFor (features : Option X86Features) (abortModelled : Bool) (input : ProcInput) :
    Prop :=
  ValidInputCore input ∧ input.abortTerminal = abortModelled ∧
    match features with
    | none => True
    | some f => input.hwcap = f.hwcap

theorem validInputFor_quantified {f : X86Features} {abortModelled : Bool} {input : ProcInput}
    (h : ValidInputFor (some f) abortModelled input) : ValidInputFor none abortModelled input :=
  ⟨h.1, h.2.1, trivial⟩

theorem validInputFor_minimal (abortModelled : Bool) (input : ProcInput) :
    Statements.ValidInput abortModelled input ↔ ValidInputFor (some minimal) abortModelled input := by
  simp only [Statements.ValidInput, X86Launch.ValidInput, ValidInputFor, minimal]
  tauto

/-- The declared `AT_HWCAP` is what the launch advertises. -/
theorem hwcap_entry (img : Image) (sp : Word) (f : X86Features) (abortModelled : Bool)
    (input : ProcInput) (valid : ValidInputFor (some f) abortModelled input) :
    (AT_HWCAP, f.hwcap) ∈ X86Launch.auxiliaryEntries img sp input := by
  have h : input.hwcap = f.hwcap := valid.2.2
  simp [X86Launch.auxiliaryEntries, h]

theorem platform_entry (img : Image) (sp : Word) (input : ProcInput) :
    (X86Launch.AT_PLATFORM, sp + natToWord (X86Launch.platformOffset input.argv input.envp)) ∈
      X86Launch.auxiliaryEntries img sp input := by
  simp [X86Launch.auxiliaryEntries]

theorem vdso_declared_absent (img : Image) (sp : Word) (input : ProcInput) :
    (X86Launch.AT_SYSINFO_EHDR, 0) ∈ X86Launch.auxiliaryEntries img sp input :=
  X86Launch.no_vdso_advertised img sp input

/-! ## Entry-stack lengths -/

theorem wordLe8_length (v : Word) : (wordLe8 v).length = 8 := by simp [wordLe8]

theorem flatMap_wordLe8_length (l : List Word) : (l.flatMap wordLe8).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons v r ih => simp only [List.flatMap_cons, List.length_append, wordLe8_length, ih,
      List.length_cons]; omega

theorem buildAuxv_length (e : List (Word × Word)) : (buildAuxv e).length = 16 * e.length := by
  induction e with
  | nil => rfl
  | cons v r ih =>
    simp only [buildAuxv] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, wordLe8_length, ih, List.length_cons]
    omega

theorem stringAddrs_length (b : Word) (l : List (List Byte)) :
    (stringAddrs b l).1.length = l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons s r ih => simp [stringAddrs, ih]

theorem flattenStrings_length (l : List (List Byte)) :
    ((flattenStrings l).length : Int) = totalArgBytes l := by
  unfold flattenStrings totalArgBytes
  induction l with
  | nil => rfl
  | cons s r ih =>
    rw [List.flatMap_cons, List.length_append, List.foldr_cons, ← ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    push_cast; omega

theorem atRandomBytes_length (r : BitVec 128) : (atRandomBytes r).length = 16 := by
  simp [atRandomBytes]

/-- The length of the x86 entry block. -/
theorem stackBytes_length (img : Image) (en : ExecEntry) (input : ProcInput) :
    ((X86Launch.stackBytes img en input).length : Int) =
      X86Launch.structureSize input.argv input.envp + totalArgBytes input.argv +
        totalArgBytes input.envp + 7 + X86Launch.randomPadding input.argv input.envp + 16 := by
  have fa := flattenStrings_length input.argv
  have fe := flattenStrings_length input.envp
  simp only [X86Launch.stackBytes, List.length_append, wordLe8_length, flatMap_wordLe8_length,
    stringAddrs_length, buildAuxv_length, X86Launch.auxiliaryEntries_length,
    List.length_replicate, atRandomBytes_length, X86Launch.structureSize,
    X86Launch.auxiliarySize, X86Launch.auxiliaryCount, X86Launch.platformBytes,
    List.length_cons, List.length_nil]
  push_cast
  omega

theorem randomPadding_lt (argv envp : List (List Byte)) :
    X86Launch.randomPadding argv envp < 16 := by
  unfold X86Launch.randomPadding; omega

/-- A valid input's entry block is at most a few MiB. -/
theorem stackBytes_length_le (img : Image) (en : ExecEntry) (input : ProcInput)
    (valid : ValidInputCore input) :
    ((X86Launch.stackBytes img en input).length : Int) ≤ 2 ^ 30 := by
  obtain ⟨⟨-, argc, argBytes, -⟩, ⟨envc, envBytes, -⟩, -⟩ := valid
  rw [stackBytes_length]
  have := randomPadding_lt input.argv input.envp
  simp only [X86Launch.structureSize, X86Launch.auxiliarySize, X86Launch.auxiliaryCount]
  push_cast
  omega

/-! ## A valid entry exists -/

/-- The witness stack level: 2 GiB below `TASK_SIZE` (the bottom of the stack window before it
was widened to Linux's 16-GiB x86-64 stack randomization). Keeping the witness here leaves the
image-placement premise of `validEntry_witness` as weak as before the widening. -/
def spWitnessLevel : Int := x86LaunchBounds.spWindowHi - 2 * 1024 * 1024 * 1024

/-- The witness stack pointer. -/
def spWitness : Word := zw spWitnessLevel

def brkWitness (segments : List Segment) : Word :=
  zw (pageRoundUp (reservedTop (segmentsReserved segments)))

/-- The witness entry: stack 2 GiB below `TASK_SIZE`, first page above the image, lowest mmap base. -/
def witnessEntry (snapshot : X86Launch.Snapshot) (draw : EntryDraw) : ExecEntry :=
  ⟨spWitness, brkWitness snapshot.image.segments, zw x86LaunchBounds.mmapBaseMin, draw⟩

theorem reservedTop_nonneg (l : List (Word × Word)) : 0 ≤ reservedTop l := by
  induction l with
  | nil => exact le_refl 0
  | cons p r ih => exact le_trans ih (le_max_right _ _)

/-- Every valid input and every entry draw has a valid x86 entry, for a valid snapshot whose
image lies below the witness stack reservation. -/
theorem validEntry_witness (isa : UserIsa) (snapshot : X86Launch.Snapshot) (input : ProcInput)
    (draw : EntryDraw) (validSnapshot : X86Launch.ValidSnapshot isa snapshot)
    (validInput : ValidInputCore input)
    (low : ∀ segment ∈ snapshot.image.segments,
      (segment.base : Int) + segment.size ≤ spWitnessLevel - stackMaxSize)
    (reserved : reservedTop (segmentsReserved snapshot.image.segments) ≤ 2 ^ 62) :
    X86Launch.ValidEntry isa snapshot (witnessEntry snapshot draw) input := by
  have sp : uns spWitness = spWitnessLevel := by decide
  have rt0 := reservedTop_nonneg (segmentsReserved snapshot.image.segments)
  have brk : uns (brkWitness snapshot.image.segments) =
      pageRoundUp (reservedTop (segmentsReserved snapshot.image.segments)) := by
    unfold brkWitness
    apply uns_zw <;> simp only [pageRoundUp, pageSize, twoPow64] <;> omega
  have len := stackBytes_length_le snapshot.image (witnessEntry snapshot draw) input validInput
  refine ⟨validSnapshot, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [witnessEntry, sp]; decide
  · simp only [witnessEntry, sp]; decide
  · simp only [witnessEntry, sp]; decide
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [witnessEntry, brk] <;>
      simp only [pageRoundUp, pageSize, brkAslrMax] <;> omega
  · simp only [witnessEntry]; decide
  · simp only [witnessEntry]; decide
  · simp only [witnessEntry]; decide
  · simp only [entryPageTop, entryBlockTop, pageRoundUp, pageSize]
    simp only [witnessEntry] at len ⊢
    rw [sp]
    simp only [spWitnessLevel, x86LaunchBounds, x86AddressSpace] at len ⊢
    omega
  · intro segment mem
    simp only [witnessEntry, sp]
    exact low segment mem

/-! ## Statements -/

/-- The native statement profile with the complete native system and a feature profile. -/
def profile (isa : UserIsa) (features : Option X86Features) :
    StatementProfile X86Launch.Snapshot :=
  { Statements.profile isa system with validInput := ValidInputFor features }

theorem profile_syscalls (isa : UserIsa) (features : Option X86Features) (reading : Reading) :
    (profile isa features).syscalls reading = dispatch nativeTable := rfl

theorem profile_allocClassifier (isa : UserIsa) (features : Option X86Features) :
    (profile isa features).allocClassifier = NativeX86.allocBudgetRefusedB := rfl

/-- Both artifacts of an agreement statement have valid entries for every valid input. -/
theorem domain_nonempty (isa : UserIsa) (features : Option X86Features)
    (plain sanitized : X86Launch.Snapshot)
    (plainValid : X86Launch.ValidSnapshot isa plain)
    (sanitizedValid : X86Launch.ValidSnapshot isa sanitized)
    (plainLow : ∀ segment ∈ plain.image.segments,
      (segment.base : Int) + segment.size ≤ spWitnessLevel - stackMaxSize)
    (sanitizedLow : ∀ segment ∈ sanitized.image.segments,
      (segment.base : Int) + segment.size ≤ spWitnessLevel - stackMaxSize)
    (plainReserved : reservedTop (segmentsReserved plain.image.segments) ≤ 2 ^ 62)
    (sanitizedReserved : reservedTop (segmentsReserved sanitized.image.segments) ≤ 2 ^ 62)
    (abortModelled : Bool) (input : ProcInput)
    (valid : (profile isa features).validInput abortModelled input) (draw : EntryDraw) :
    ∃ plainEntry sanitizedEntry,
      (profile isa features).validEntry plain plainEntry input ∧
        (profile isa features).validEntry sanitized sanitizedEntry input ∧
        plainEntry.draw = draw ∧ sanitizedEntry.draw = draw :=
  ⟨witnessEntry plain draw, witnessEntry sanitized draw,
    validEntry_witness isa plain input draw plainValid valid.1 plainLow plainReserved,
    validEntry_witness isa sanitized input draw sanitizedValid valid.1 sanitizedLow
      sanitizedReserved, rfl, rfl⟩

/-- A statement over the quantified `AT_HWCAP` domain implies it for every declared profile. -/
theorem agreement_of_quantified (plainIsa sanitizedIsa : UserIsa) (f : X86Features)
    (reading : Reading) (abortModelled : Bool) (plainLimit sanitizedLimit : Int)
    (plain sanitized : X86Launch.Snapshot)
    (h : StatementProfile.agreement (profile plainIsa none) (profile sanitizedIsa none) reading
      abortModelled plainLimit sanitizedLimit plain sanitized) :
    StatementProfile.agreement (profile plainIsa (some f)) (profile sanitizedIsa (some f)) reading
      abortModelled plainLimit sanitizedLimit plain sanitized :=
  fun plainEntry sanitizedEntry input plainValid sanitizedValid valid notRefused =>
    h plainEntry sanitizedEntry input plainValid sanitizedValid
      (validInputFor_quantified valid) notRefused

end Silmaril.Process.LPS.NativeX86.All
