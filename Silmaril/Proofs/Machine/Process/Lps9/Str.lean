module

public import Silmaril.Machine.Process.Lps9.Str.Defs
public import Silmaril.Machine.Process.Lps9.Thms
public import Silmaril.Machine.X86.Str9.Thms
public import Silmaril.Machine.X86.Ext9.Thms

/-!
# Proofs: `Str9.step` agrees with the LPS `Ext9` + string machine

Names in `Silmaril.Proofs.Machine.Process.Lps9.Str`.

* `str9_step_trap`: `Str9.step` is stuck at `0F 05` (neither `Ext9` nor `decodeStr` reads
  `0F 05`).
* `nativeStr_of_ne`: where `Ext8.fetch` is not `undecodable` (off `0F 05`),
  `x86NativeStep9Str = x86NativeStep8`.
* **`agrees_str9 : Agrees x86NativeStep9Str Str9.step`**.
* `stos_str9`, `stos_native9`, **`not_agrees_native9_str9`**, `stos_nativeStr` (mutation
  probe): on a concrete `rep stosq` state (`rcx = 0`) `Str9.step` steps while P7's
  `x86NativeStep9` is `unmodeled`, so
  `Agrees x86NativeStep9 Str9.step` is false: `agrees_str9` depends on the string arm.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.Lps9.Str

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.Lps9
open Silmaril.Machine.Process.Lps9.Str
open Silmaril.Machine.X86

/-- `decodeStr` rejects `0F 05`, whatever follows. -/
theorem decodeStr_syscall (more : List Silmaril.X86.Byte) :
    Str9.decodeStr (0x0f :: 0x05 :: more) = none :=
  rfl

/-- **`Str9.step` is stuck at a `syscall`.** -/
theorem str9_step_trap {m : MState} (h : AtSyscall m) : Str9.step m = none := by
  obtain ⟨more, window⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow h
    (limit := Silmaril.X86.maxInstrLength) (by decide)
  have hnew : Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [← window, List.cons_append, List.cons_append, List.nil_append,
      Silmaril.Proofs.Machine.Process.Lps9.ext9_decodeNew_syscall]
    rfl
  have hstr : Str9.fetchStr m.memory m.core.rip.toNat = none := by
    unfold Str9.fetchStr
    rw [← window, List.cons_append, List.cons_append, List.nil_append, decodeStr_syscall]
    rfl
  have ho := Silmaril.Proofs.Machine.Process.LpsBridge.open_step_trap h
  unfold Str9.step
  split
  · rw [hnew]; dsimp only; rw [hstr]
  · exact ho

/-- Off `0F 05`, where `Ext8.fetch` is not `undecodable`, the string step is the `Ext8` step. -/
theorem nativeStr_of_ne {s : X86State}
    (nt : ¬ s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05])
    (hf : Silmaril.X86.Ext8.fetch s.m.memory s.m.core.rip.toNat ≠ .inl .undecodable) :
    x86NativeStep9Str s = x86NativeStep8 s := by
  unfold x86NativeStep9Str
  rw [ite_eq_right nt]
  split
  · rename_i h; exact absurd h hf
  · rfl

/-- `x86ExecResult` retires exactly what `Open.ofResult` retires. -/
theorem execResult_of_ofResult {acc : List (Silmaril.X86.Word × Nat)}
    {r : Silmaril.X86.Ext.Result} {m' : MState} (h : Open.ofResult r = some m') :
    x86ExecResult acc r = .ok ⟨⟨m', none⟩, acc⟩ := by
  cases r <;> simp only [Open.ofResult, reduceCtorEq, Option.some.injEq] at h
  subst h; rfl

/-- **`Str9.step` agrees with LPS's native `Ext9` + string step.** -/
theorem agrees_str9 : Agrees x86NativeStep9Str Str9.step where
  stuck ht := str9_step_trap ht
  step {m m'} hs := by
    have nt : ¬ AtSyscall m := fun ht => by rw [str9_step_trap ht] at hs; cases hs
    have nt' : ¬ m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05] := nt
    by_cases hf : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable
    · have hs' := hs
      unfold Str9.step at hs'
      rw [hf] at hs'
      dsimp only at hs'
      unfold x86NativeStep9Str
      dsimp only
      rw [ite_eq_right nt', hf]
      dsimp only
      split at hs'
      · rename_i i n hfn
        rw [hfn]
        exact ⟨_, execResult_of_ofResult hs'⟩
      · cases hs'
      · rename_i hfn
        rw [hfn]
        dsimp only
        split at hs'
        · rename_i i n hfs
          rw [hfs]
          exact ⟨_, execResult_of_ofResult hs'⟩
        · cases hs'
    · have ho : Open.step m = some m' := by
        have := hs
        unfold Str9.step at this
        split at this
        · rename_i h; exact absurd h hf
        · exact this
      obtain ⟨acc, h⟩ := Silmaril.Proofs.Machine.Process.LpsBridge.native8_open ho nt
      exact ⟨acc, by rw [nativeStr_of_ne (s := ⟨m, none⟩) nt' hf]; exact h⟩
  trap s w ht hw := by
    unfold x86NativeStep9Str
    rw [ite_eq_left (show s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] from ht)]
    exact Silmaril.Proofs.Machine.Process.LpsBridge.agrees_open8.trap s w ht hw

/-- `x86WithFlagOracle9Str` is the flag-oracle machine over `x86NativeStep9Str`. -/
theorem x86WithFlagOracle9Str_eq (oracle : Oracle) :
    x86WithFlagOracle9Str oracle = flagMachine oracle x86NativeStep9Str :=
  rfl

/-! ## Mutation probe: `x86NativeStep9` does not agree with `Str9.step`

A concrete state with `rep stosq` (`F3 48 AB`) at `rip` and `rcx = 0`: `Str9.step` retires it
(RIP advances), `x86NativeStep9` (P7's machine, no string arm) reports `unmodeled`. So
`Agrees x86NativeStep9 Str9.step` is false, and `agrees_str9` depends on the string arm. -/

/-- Three executable bytes `F3 48 AB` at `0x1000`. -/
def stosMem : Silmaril.Process.Memory :=
  { regions := [⟨0x1000, 3, ⟨true, false, true⟩⟩]
    bytes := Silmaril.Process.Memory.install ∅ 0x1000 [0xf3, 0x48, 0xab] }

/-- `rip = 0x1000`, every register `0` (so `rcx = 0`), over `stosMem`. -/
def stosState : MState :=
  { core := { regs := fun _ => 0, rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }
    memory := stosMem }

theorem stos_fetch3 :
    stosState.memory.fetchBytes stosState.core.rip.toNat 3 = some [0xf3, 0x48, 0xab] :=
  Silmaril.Process.Memory.readWith_eq stosMem .execute 0x1000 [0xf3, 0x48, 0xab] (by decide)
    (fun i hi => Silmaril.Process.Memory.install_get _ 0x1000 _ i hi)

theorem stos_fetch2 : stosState.memory.fetchBytes stosState.core.rip.toNat 2 = some [0xf3, 0x48] :=
  Silmaril.Process.Memory.readWith_eq stosMem .execute 0x1000 [0xf3, 0x48] (by decide)
    (fun i hi => by
      have := Silmaril.Process.Memory.install_get ∅ 0x1000 [0xf3, 0x48, 0xab] i
        (by simp at hi ⊢; omega)
      simp only [stosMem]; rw [this]; match i, hi with | 0, _ => rfl | 1, _ => rfl)

/-- `Str9.step` retires the `rep stosq` (with `rcx = 0`). -/
theorem stos_str9 : (Str9.step stosState).isSome = true := by
  rw [Str9.rep_stosq_zero (c := stosState.core) (mem := stosState.memory) stos_fetch3 rfl]; rfl

/-- P7's `Ext9` native step does not model it. -/
theorem stos_native9 : x86NativeStep9 ⟨stosState, none⟩ = .unmodeled := by
  obtain ⟨more, window, hf⟩ := Open9.fetch8_undecodable_of stos_fetch3 (by decide) (by decide)
    (by decide) (by decide)
  have hnew : Ext9.fetchNew stosState.memory stosState.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    have h : Str9.ext9Bad [0xf3, 0x48, 0xab] = true := by decide
    unfold Str9.ext9Bad at h
    split at h
    · rename_i hb
      rw [window]
      unfold Ext9.decodeNew
      rw [Ext9.good_pNew.bad hb more]
      rfl
    · cases h
  unfold x86NativeStep9
  rw [ite_eq_right (by rw [stos_fetch2]; decide)]
  dsimp only
  rw [hf]
  dsimp only
  rw [hnew]

/-- **Mutation probe**: `Str9.step` does not agree with P7's `x86NativeStep9`. -/
theorem not_agrees_native9_str9 : ¬ Agrees x86NativeStep9 Str9.step := by
  intro h
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp stos_str9
  obtain ⟨acc, e⟩ := h.step hm'
  rw [stos_native9] at e
  cases e

/-- The string machine does (by `agrees_str9`). -/
theorem stos_nativeStr : ∃ s acc, x86NativeStep9Str ⟨stosState, none⟩ = .ok ⟨s, acc⟩ := by
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp stos_str9
  obtain ⟨acc, e⟩ := agrees_str9.step hm'
  exact ⟨_, acc, e⟩

end Silmaril.Proofs.Machine.Process.Lps9.Str
