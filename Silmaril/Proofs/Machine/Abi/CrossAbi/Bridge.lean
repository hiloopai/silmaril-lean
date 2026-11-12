module

public import Silmaril.Machine.Abi.CrossAbi.Defs
public import Silmaril.Machine.Abi.Win64.Thms
public import Silmaril.Proofs.Machine.Abi.SystemV.Basic
import Mathlib.Tactic.IntervalCases

/-!
# System V ↔ Microsoft x64 bridges: entry and return transfer

Proofs for `Silmaril.Machine.Abi.CrossAbi.Thms`.

* `args_transfer`: register-only argument placements transfer between two
  register assignments when the registers carry equal words.
* `sysvToMs_entry`, `msToSysv_entry`: a bridging `Enter` turns a caller entry
  into a callee entry (prototypes with at most four parameters).
* `sysvToMs_return`, `msToSysv_return`: a bridging `Leave` turns a callee
  return into a caller return.
* `raxResult_congr`: results are read from RAX only.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.CrossAbi

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV
open Silmaril.Machine.Abi.Win64 (reg msArg msArgs msArguments win64 RaxResult)
open Silmaril.Machine.Abi.CrossAbi
open Silmaril.X86 (Reg)

/-- A one-register argument placement. -/
def regArgument (o : Object) (r : Reg) : Argument := ⟨o, [⟨0, o.size, .gp r⟩], none⟩

def listWith (f : Object → Nat → Argument) : List Object → Nat → List Argument
  | [], _ => []
  | o :: rest, i => f o i :: listWith f rest (i + 1)

theorem intArgs_eq : ∀ (l : List Object) (i : Nat), SystemV.intArgs l i = listWith SystemV.intArg l i
  | [], _ => rfl
  | _ :: rest, i => by simp [SystemV.intArgs, listWith, intArgs_eq rest (i + 1)]

theorem msArgs_eq : ∀ (l : List Object) (i : Nat), msArgs l i = listWith msArg l i
  | [], _ => rfl
  | _ :: rest, i => by simp [msArgs, listWith, msArgs_eq rest (i + 1)]

/-- System V argument register `i`. -/
def sysvReg (i : Nat) : Reg := gpArguments.getD i .rax
/-- Microsoft x64 argument register `i`. -/
def msReg (i : Nat) : Reg := msArguments.getD i .rax

theorem intArg_small (o : Object) (i : Nat) (h : i < 4) :
    SystemV.intArg o i = regArgument o (sysvReg i) := by
  unfold SystemV.intArg regArgument sysvReg
  rw [List.getElem?_eq_getElem (by simp [gpArguments]; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < gpArguments.length by
    simp [gpArguments]; omega)]

theorem msArg_small (o : Object) (i : Nat) (h : i < 4) :
    msArg o i = regArgument o (msReg i) := by
  unfold msArg regArgument msReg
  rw [List.getElem?_eq_getElem (by simp [msArguments]; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < msArguments.length by
    simp [msArguments]; omega)]

theorem locationBytes_congr {s s₁ : Ffi.State} {r r' : Reg} (h : reg s₁ r' = reg s r) (n : Nat) :
    Ffi.locationBytes s₁ (.gp r') n = Ffi.locationBytes s (.gp r) n := by
  simp [Ffi.locationBytes, h]

theorem argument_transfer {s s₁ : Ffi.State} {r r' : Reg} (h : reg s₁ r' = reg s r)
    (spec : Ffi.ObjectSpec) (v : spec.representation.Value) (o : Object) :
    Ffi.ArgumentAt s spec v (regArgument o r) → Ffi.ArgumentAt s₁ spec v (regArgument o r') := by
  rintro ⟨obj, bytes, enc, chunks⟩
  refine ⟨obj, bytes, enc, ?_⟩
  intro chunk mem
  obtain ⟨len, at_⟩ := chunks _ (List.mem_singleton_self _)
  simp only [regArgument, List.mem_singleton] at mem
  subst mem
  exact ⟨len, by rw [locationBytes_congr h]; exact at_⟩

/-- Register-only placements transfer between register assignments that carry
equal words. -/
theorem args_transfer {s s₁ : Ffi.State} (f g : Object → Nat → Argument) (R R' : Nat → Reg)
    (hf : ∀ o i, i < 4 → f o i = regArgument o (R i))
    (hg : ∀ o i, i < 4 → g o i = regArgument o (R' i))
    (hreg : ∀ i, i < 4 → reg s₁ (R' i) = reg s (R i)) :
    ∀ (ks : List Scalar) (vals : Ffi.Values (ks.map Kind.spec)) (i : Nat), i + ks.length ≤ 4 →
      Ffi.ArgumentsAt s (ks.map Kind.spec) vals (listWith f (ks.map Kind.object) i) →
      Ffi.ArgumentsAt s₁ (ks.map Kind.spec) vals (listWith g (ks.map Kind.object) i)
  | [], _, _, _, _ => trivial
  | k :: ks, (v, vs), i, bound, ⟨head, tail⟩ => by
    have hi : i < 4 := by simp at bound; omega
    refine ⟨?_, args_transfer f g R R' hf hg hreg ks vs (i + 1) (by simp at bound; omega) tail⟩
    have head' : Ffi.ArgumentAt s (Kind.spec k) v (regArgument (Kind.object k) (R i)) := by
      rw [← hf _ i hi]; exact head
    show Ffi.ArgumentAt s₁ (Kind.spec k) v (g (Kind.object k) i)
    rw [hg _ i hi]
    exact argument_transfer (hreg i hi) _ v _ head'

theorem sysvReg_eq : ∀ i, i < 4 → sysvReg i = [Reg.rdi, .rsi, .rdx, .rcx].getD i .rax := by decide
theorem msReg_eq : ∀ i, i < 4 → msReg i = [Reg.rcx, .rdx, .r8, .r9].getD i .rax := by decide

theorem outgoing_small (n : Nat) (h : n ≤ 4) : Win64.outgoingSize n = 32 := by
  simp only [Win64.outgoingSize, alignUp]
  rw [show max n 4 = 4 by omega]
  rfl

theorem sysv_stack_small (n : Nat) (h : n ≤ 4) : alignUp (8 * (n - 6)) 16 = 0 := by
  rw [show n - 6 = 0 by omega]
  rfl

/-- A System V entry and a bridging `Enter` give a Microsoft x64 entry. -/
theorem sysvToMs_entry (options : Options) {p : Proto} (small : Small p)
    {a : Arguments p.signature.arguments} {s s₁ : Ffi.State}
    (entry : (sysv options).Entry p a s) (enter : SysvToMs.Enter s s₁) :
    win64.Entry p a s₁ := by
  obtain ⟨exit, h⟩ := entry
  have hargs : Ffi.ArgumentsAt s (p.signature.arguments.map Kind.spec) (toValues a)
      (listWith SystemV.intArg (p.signature.arguments.map Kind.object) 0) := by
    rw [← intArgs_eq]; exact h.argumentsAt
  have dir : s.direction = false := h.direction
  have x87 : s.x87Mode = true := h.x87Mode
  refine ⟨?_, enter.frame.alignment, ?_, enter.frame.returnAddress, ?_, ?_⟩
  · show Ffi.ArgumentsAt s₁ _ (toValues a) (msArgs (p.signature.arguments.map Kind.object) 0)
    rw [msArgs_eq]
    refine args_transfer SystemV.intArg msArg sysvReg msReg intArg_small msArg_small ?_ _ _ 0
      (by have hs : p.signature.arguments.length ≤ 4 := small; simpa using hs) hargs
    intro i hi
    rw [sysvReg_eq i hi, msReg_eq i hi]
    interval_cases i
    · exact enter.rcx
    · exact enter.rdx
    · exact enter.r8
    · exact enter.r9
  · rw [outgoing_small _ (show p.signature.arguments.length ≤ 4 from small)]
    exact enter.frame.stackNoWrap
  · rw [enter.control.direction]; exact dir
  · rw [enter.control.x87Mode]; exact x87

/-- A Microsoft x64 entry and a bridging `Enter` give a System V entry. -/
theorem msToSysv_entry (options : Options) {p : Proto} (small : Small p)
    {a : Arguments p.signature.arguments} {s s₁ : Ffi.State}
    (entry : win64.Entry p a s) (enter : MsToSysv.Enter s s₁) :
    (sysv options).Entry p a s₁ := by
  obtain ⟨exit, ra⟩ := enter.frame.returnAddress
  have hargs : Ffi.ArgumentsAt s (p.signature.arguments.map Kind.spec) (toValues a)
      (listWith msArg (p.signature.arguments.map Kind.object) 0) := by
    rw [← msArgs_eq]; exact entry.argumentsAt
  refine ⟨exit, ?_⟩
  constructor
  · rfl
  · show Ffi.ArgumentsAt s₁ _ (toValues a)
      (SystemV.intArgs (p.signature.arguments.map Kind.object) 0)
    rw [intArgs_eq]
    refine args_transfer msArg SystemV.intArg msReg sysvReg msArg_small intArg_small ?_ _ _ 0
      (by have hs : p.signature.arguments.length ≤ 4 := small; simpa using hs) hargs
    intro i hi
    rw [sysvReg_eq i hi, msReg_eq i hi]
    interval_cases i
    · exact enter.rdi
    · exact enter.rsi
    · exact enter.rdx
    · exact enter.rcx
  · exact enter.frame.alignment
  · show (reg s₁ .rsp).toNat + 8 + alignUp (8 * (p.objects.length - 6)) 16 ≤ 2 ^ 64
    have hs : p.signature.arguments.length ≤ 4 := small
    have : p.objects.length ≤ 4 := by simpa [SystemV.Proto.objects] using hs
    rw [sysv_stack_small _ this]
    simpa using enter.frame.stackNoWrap
  · exact ra
  · unfold Ffi.SretAt
    split
    · rename_i size align hres
      exact absurd hres (Silmaril.Proofs.Machine.Abi.SystemV.intReturn_not_indirect
        p.signature.result size align)
    · rfl
  · show s₁.direction = false
    rw [enter.control.direction]; exact entry.direction
  · show s₁.x87Mode = true
    rw [enter.control.x87Mode]; exact entry.x87Mode
  · intro count h
    cases h

theorem sysv_saved_ms : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ∈ Win64.ms64.calleeSaved :=
  Win64.sysv_calleeSaved_sub

/-- A Microsoft x64 callee return and the bridging specification give a System V
return of the caller. -/
theorem sysvToMs_return (options : Options) (p : Proto) {s s₁ s₂ s₃ : Ffi.State}
    (enter : SysvToMs.Enter s s₁) (ret : win64.Return p s₁ s₂) (leave : SysvToMs.Leave s s₂ s₃) :
    (sysv options).Return p s s₃ := by
  obtain ⟨_e, -, back⟩ := ret
  obtain ⟨exit, ra, pc⟩ := leave.pc
  refine ⟨exit, ra, ?_⟩
  constructor
  · exact pc
  · exact leave.stack
  · intro r mem
    show reg s₃ r = reg s r
    rw [leave.saved r mem, back.calleeSaved r (sysv_saved_ms r mem), enter.saved r mem]
  · show s₃.direction = false
    rw [leave.control.direction]; exact back.direction
  · show s₃.x87Mode = true
    rw [leave.control.x87Mode]; exact back.x87Mode
  · show s₃.mxcsr &&& 0xffc0 = s.mxcsr &&& 0xffc0
    rw [leave.control.mxcsr, back.mxcsrControl, enter.control.mxcsr]
  · show s₃.x87Control = s.x87Control
    rw [leave.control.x87Control, back.x87Control, enter.control.x87Control]
  · show s₃.fsBase = s.fsBase
    rw [leave.control.fsBase, back.threadPointer, enter.control.fsBase]

/-- A System V callee return and the bridging specification give a Microsoft x64
return of the caller. -/
theorem msToSysv_return (options : Options) (p : Proto) {s s₁ s₂ s₃ : Ffi.State}
    (enter : MsToSysv.Enter s s₁) (ret : (sysv options).Return p s₁ s₂)
    (leave : MsToSysv.Leave s s₂ s₃) :
    win64.Return p s s₃ := by
  obtain ⟨_e, -, back⟩ := ret
  obtain ⟨exit, ra, pc⟩ := leave.pc
  refine ⟨exit, ra, ?_⟩
  constructor
  · exact pc
  · exact leave.stack
  · intro r mem
    have hsv : r ∈ Silmaril.X86.sysv64.calleeSaved ∨ r = .rsi ∨ r = .rdi := by
      revert r; decide
    rcases hsv with hsv | rfl | rfl
    · rw [leave.saved r hsv]
      exact (back.calleeSaved r hsv).trans (enter.saved r hsv)
    · exact leave.rsi
    · exact leave.rdi
  · exact leave.vectors
  · rw [leave.control.direction]; exact back.direction
  · rw [leave.control.x87Mode]; exact back.x87Mode
  · have h := back.mxcsrControl
    simp only [callOf] at h
    rw [leave.control.mxcsr, h, enter.control.mxcsr]
  · have h := back.x87Control
    simp only [callOf] at h
    rw [leave.control.x87Control, h, enter.control.x87Control]
  · have h := back.threadPointer
    simp only [callOf] at h
    rw [leave.control.fsBase, h, enter.control.fsBase]

/-- Results are read from RAX only. -/
theorem raxResult_congr : ∀ (res : Option Scalar) (r : ReturnValue res) {s s' : Ffi.State},
    reg s' .rax = reg s .rax → (RaxResult res r s' ↔ RaxResult res r s)
  | none, _, _, _, _ => Iff.rfl
  | some _, _, _, _, h => by
    simp only [RaxResult, Ffi.ChunksAt, List.mem_singleton, forall_eq,
      locationBytes_congr h]

end Silmaril.Proofs.Machine.Abi.CrossAbi
