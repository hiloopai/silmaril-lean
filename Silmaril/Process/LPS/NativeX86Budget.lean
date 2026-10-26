module

public import Silmaril.Process.LPS.NativeX86
public import Silmaril.Process.LPS.Sys.MmRunX86

/-! # Architecture-aware allocation-budget diagnostics

The literal `BudgetRefusedAt` remains reference-numbered. These additive
predicates take a classifier explicitly, then instantiate it through the
native x86 input adapter. Instruction and syscall-access materialization are
the same actual LPS operations; only the allocation-refusal diagnostic changes.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS

abbrev AllocBudgetClassifier := SyscallInput → Model → Bool

def BudgetRefusedAtUsing (isa : UserIsa) (classify : AllocBudgetClassifier)
    (segments : List Segment) (spec : Sys SyscallEffect) (configuration : Config isa) : Prop :=
  configuration.model.halted = none ∧
    ((isa.svcPending configuration.ms = none ∧ ∃ report,
        isa.step segments configuration.ms = .ok report ∧
        materializeModelAccesses configuration.model report.accessed = none) ∨
      ∃ number, isa.svcPending configuration.ms = some number ∧
        (classify (sysInput isa segments configuration.ms number) configuration.model = true ∨
          ∃ effect model events,
            spec (sysInput isa segments configuration.ms number) configuration.model
              (.ok effect model events) ∧ model.halted = none ∧
            materializeModelAccesses model (syscallEffectAccesses effect) = none))

theorem BudgetRefusedAtUsing_reference (isa : UserIsa) (segments : List Segment)
    (spec : Sys SyscallEffect) (configuration : Config isa) :
    BudgetRefusedAtUsing isa allocBudgetRefusedB segments spec configuration ↔
      BudgetRefusedAt isa segments spec configuration := Iff.rfl

/-- Reachability from an explicit initialized configuration supports arbitrary
loader/stack choices, without silently switching back to legacy initialization. -/
def RunBudgetRefusedFromUsing (isa : UserIsa) (classify : AllocBudgetClassifier)
    (segments : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (initial : Config isa) : Prop :=
  ∃ trace configuration, Star segments spec refused initial trace configuration ∧
    BudgetRefusedAtUsing isa classify segments spec configuration

def RunBudgetRefusedWithStackUsing (isa : UserIsa) (classify : AllocBudgetClassifier)
    (stack : EntryStackBuilder) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (image : Image) (limit : Int) (entry : ExecEntry) (input : ProcInput) : Prop :=
  RunBudgetRefusedFromUsing isa classify image.segments spec refused
    (initConfigWithStack isa stack image entry limit input)

namespace NativeX86

def allocBudgetRefusedB (input : SyscallInput) (model : Model) : Bool :=
  match referenceInput input with
  | some reference => Silmaril.Process.LPS.allocBudgetRefusedB reference model
  | none => false

def BudgetRefusedAt (isa : UserIsa) (segments : List Segment)
    (spec : Sys SyscallEffect) (configuration : Config isa) : Prop :=
  BudgetRefusedAtUsing isa allocBudgetRefusedB segments spec configuration

def RunBudgetRefusedFrom (isa : UserIsa) (segments : List Segment)
    (spec : Sys SyscallEffect) (refused : RefusalFilter) (initial : Config isa) : Prop :=
  RunBudgetRefusedFromUsing isa allocBudgetRefusedB segments spec refused initial

def RunBudgetRefusedWithStack (isa : UserIsa) (stack : EntryStackBuilder)
    (spec : Sys SyscallEffect) (refused : RefusalFilter) (image : Image)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Prop :=
  RunBudgetRefusedWithStackUsing isa allocBudgetRefusedB stack spec refused image limit entry input

theorem allocBudgetRefusedB_brk (input : SyscallInput) (model : Model)
    (number : input.sysno = 12) :
    allocBudgetRefusedB input model = brkBudgetRefusedB model (input.arg 0) := by
  simp only [allocBudgetRefusedB, referenceInput, number]
  rfl

theorem allocBudgetRefusedB_mmap (input : SyscallInput) (model : Model)
    (number : input.sysno = 9) :
    allocBudgetRefusedB input model =
      mmapBudgetRefusedB (input.arg 0) (input.arg 1) (input.arg 2)
        (input.arg 3) (input.arg 4) (input.arg 5) model := by
  simp only [allocBudgetRefusedB, referenceInput, number]
  rfl

/-- Native x86 `mremap` (25) reaches LPS's `mremap` mark (`Run.v:1451`, arm 216). -/
theorem allocBudgetRefusedB_mremap (input : SyscallInput) (model : Model)
    (number : input.sysno = 25) :
    allocBudgetRefusedB input model =
      mremapBudgetRefusedB (input.arg 0) (input.arg 1) (input.arg 2)
        (input.arg 3) model := by
  simp only [allocBudgetRefusedB, referenceInput, number]
  rfl

/-- Native x86 `mprotect` (10) reaches LPS's `mprotect` mark (`Run.v:1451`, arm 226). -/
theorem allocBudgetRefusedB_mprotect (input : SyscallInput) (model : Model)
    (number : input.sysno = 10) :
    allocBudgetRefusedB input model =
      mprotectBudgetRefusedB (input.arg 0) (input.arg 1) (input.arg 2) model := by
  have row : byNative 10 = some ⟨226, 10, "mprotect"⟩ := by decide
  have mapped : referenceInput input = some { input with sysno := zw 226 } := by
    simp only [referenceInput, number]
    rw [show (10 : Word).toNat = 10 from rfl, row]
    rfl
  have h226 : (zw 226 : Word).toNat = 226 := by decide
  simp only [allocBudgetRefusedB, mapped, Silmaril.Process.LPS.allocBudgetRefusedB, h226,
    Nat.reduceEqDiff, ↓reduceIte]
  rfl

theorem allocBudgetRefusedB_unmapped (input : SyscallInput) (model : Model)
    (unknown : referenceInput input = none) : allocBudgetRefusedB input model = false := by
  rw [allocBudgetRefusedB, unknown]

/-- Off the four allocation arms (`brk`, `mremap`, `mmap`, `mprotect`; LPS `Run.v:1449`
`alloc_mark_sysnos`) the classifier is `false`. -/
theorem allocBudgetRefusedB_other (input reference : SyscallInput) (model : Model)
    (mapped : referenceInput input = some reference)
    (notBrk : reference.sysno.toNat ≠ 214) (notMremap : reference.sysno.toNat ≠ 216)
    (notMmap : reference.sysno.toNat ≠ 222) (notMprotect : reference.sysno.toNat ≠ 226) :
    allocBudgetRefusedB input model = false := by
  simp only [allocBudgetRefusedB, mapped, Silmaril.Process.LPS.allocBudgetRefusedB,
    ite_eq_right notBrk, ite_eq_right notMremap, ite_eq_right notMmap, ite_eq_right notMprotect]

/-- Pending clone is not spuriously diagnosed as an allocation-budget failure. -/
theorem clone_not_budget_refused (input : SyscallInput) (model : Model)
    (number : input.sysno = 56) : allocBudgetRefusedB input model = false := by
  simp only [allocBudgetRefusedB, referenceInput, number]
  rfl

theorem archPrctl_not_budget_refused (input : SyscallInput) (model : Model)
    (number : input.sysno = 158) : allocBudgetRefusedB input model = false := by
  simp only [allocBudgetRefusedB, referenceInput, number]
  rfl

theorem unknown_not_budget_refused (input : SyscallInput) (model : Model)
    (number : input.sysno = 999) : allocBudgetRefusedB input model = false := by
  simp only [allocBudgetRefusedB, referenceInput, number]
  rfl

/-- The two x86-64 allocation-budget dispatchers agree everywhere: the hard-coded
`allocBudgetRefusedBX86` of `Sys/MmRunX86.lean` (marks at 12, 25, 9, 10) is this module's
classifier, which renumbers through the native table and calls LPS `Run.v:1451`
`alloc_budget_refused_b`. Every native row whose LPS number is an alloc mark
(`Run.v:1449` `alloc_mark_sysnos`) has one of those four native numbers. -/
theorem allocBudgetRefusedBX86_eq (input : SyscallInput) (model : Model) :
    allocBudgetRefusedBX86 input model = allocBudgetRefusedB input model := by
  have word {k : Nat} (hk : k < 2 ^ 64) (h : input.sysno.toNat = k) :
      input.sysno = BitVec.ofNat 64 k :=
    BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk])
  by_cases h12 : input.sysno.toNat = 12
  · rw [allocBudgetRefusedB_brk input model (word (by decide) h12)]
    simp [allocBudgetRefusedBX86, h12]
  by_cases h25 : input.sysno.toNat = 25
  · rw [allocBudgetRefusedB_mremap input model (word (by decide) h25)]
    simp [allocBudgetRefusedBX86, h25]
  by_cases h9 : input.sysno.toNat = 9
  · rw [allocBudgetRefusedB_mmap input model (word (by decide) h9)]
    simp [allocBudgetRefusedBX86, h9]
  by_cases h10 : input.sysno.toNat = 10
  · rw [allocBudgetRefusedB_mprotect input model (word (by decide) h10)]
    simp [allocBudgetRefusedBX86, h10]
  rw [allocBudgetRefusedBX86_outside input model (by simp [allocMarkSysnosX86, *])]
  cases hrow : byNative input.sysno.toNat with
  | none => exact (allocBudgetRefusedB_unmapped input model (by simp [referenceInput, hrow])).symm
  | some row =>
    have hmem : row ∈ numbers := List.mem_of_find?_eq_some hrow
    have hno : row.nativeNo = input.sysno.toNat := by simpa using List.find?_some hrow
    have key : ∀ r ∈ numbers, r.referenceNo < 2 ^ 64 ∧
        (r.referenceNo ∈ [214, 216, 222, 226] → r.nativeNo ∈ [12, 25, 9, 10]) := by decide +kernel
    obtain ⟨hlt, hk⟩ := key row hmem
    have hz : (zw row.referenceNo).toNat = row.referenceNo := by
      simp only [zw, BitVec.toNat_ofInt]
      omega
    have off : ∀ k ∈ [214, 216, 222, 226], (referenceInputFor row input).sysno.toNat ≠ k := by
      intro k hkm heq
      simp only [referenceInputFor, hz] at heq
      subst heq
      have := hk hkm
      simp only [List.mem_cons, List.not_mem_nil, or_false, hno] at this
      omega
    exact (allocBudgetRefusedB_other input _ model (by simp [referenceInput, hrow])
      (off 214 (by simp)) (off 216 (by simp)) (off 222 (by simp)) (off 226 (by simp))).symm

end NativeX86
end Silmaril.Process.LPS
