module

public import Silmaril.Machine.Process.Lps9.Defs
public import Silmaril.Machine.Process.LpsBridge.Rel.Thms
public import Silmaril.Machine.X86.Open9.Thms
public import Silmaril.Machine.X86.RelIsa.Thms
public import Silmaril.Machine.X86.RelIsa.Safe.Thms

/-!
# Proofs: `Open9.step` agrees with the LPS `Ext9` machine

Names in `Silmaril.Proofs.Machine.Process.Lps9`.

* `x86WithFlagOracle9_eq`: `x86WithFlagOracle9 oracle = flagMachine oracle x86NativeStep9`
  (by definition).
* `ext9_decodeNew_syscall`, `open9_step_trap`: the `Ext9` parser rejects `0F 05` whatever
  follows, so `Open9.step` is stuck at a `syscall`.
* `native9_of_ne_undecodable`: where `Ext8.fetch` decodes (or truncates), off `0F 05`,
  `x86NativeStep9` is `x86NativeStep8`.
* **`agrees_open9 : Agrees x86NativeStep9 Open9.step`**.
* `le_open9`: `Le (ofFun Open9.step) (loosen Open9.isa ⊤)`.
* `safeNR_open9_of_open`, `must_open9_of_run`: an `Open.step` (`Ext8`) safe or terminating run
  is a `SafeNR`/`Must` run on `loosen Open9.isa ⊤`.
* **`psafe9_of_safeNR`**, **`mustExit9_of_must`**, `processSafe9_of_launchR`,
  `mustExit9_of_launchR`: the bridge on `x86WithFlagOracle9`, for every `A` above
  `ofFun Open9.step` (in particular `loosen Open9.isa ⊤`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.Lps9

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.Lps9
open Silmaril.Machine.X86

/-- `x86WithFlagOracle9` is the flag-oracle machine over `x86NativeStep9`. -/
theorem x86WithFlagOracle9_eq (oracle : Oracle) :
    x86WithFlagOracle9 oracle = flagMachine oracle x86NativeStep9 :=
  rfl

/-- The `Ext9` parser rejects `0F 05`, whatever follows. -/
theorem ext9_decodeNew_syscall (more : List Silmaril.X86.Byte) :
    Ext9.decodeNew (0x0f :: 0x05 :: more) = none :=
  rfl

/-- **`Open9.step` is stuck at a `syscall`.** -/
theorem open9_step_trap {m : MState} (h : AtSyscall m) : Open9.step m = none := by
  obtain ⟨more, window⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow h
    (limit := Silmaril.X86.maxInstrLength) (by decide)
  have hnew : Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [← window, List.cons_append, List.cons_append, List.nil_append, ext9_decodeNew_syscall]
    rfl
  have ho := Silmaril.Proofs.Machine.Process.LpsBridge.open_step_trap h
  unfold Open9.step
  split
  · rw [hnew]
  · exact ho

/-- Off `0F 05`, where `Ext8.fetch` is not `undecodable`, the `Ext9` step is the `Ext8` step. -/
theorem native9_of_ne_undecodable {s : X86State}
    (nt : ¬ s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05])
    (hf : Silmaril.X86.Ext8.fetch s.m.memory s.m.core.rip.toNat ≠ .inl .undecodable) :
    x86NativeStep9 s = x86NativeStep8 s := by
  unfold x86NativeStep9
  rw [ite_eq_right nt]
  split
  · rename_i h; exact absurd h hf
  · rfl

/-- **`Open9.step` agrees with LPS's native `Ext9` step.** -/
theorem agrees_open9 : Agrees x86NativeStep9 Open9.step where
  stuck ht := open9_step_trap ht
  step {m m'} hs := by
    have nt : ¬ AtSyscall m := fun ht => by rw [open9_step_trap ht] at hs; cases hs
    have nt' : ¬ m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05] := nt
    by_cases hf : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable
    · have hs' := hs
      unfold Open9.step at hs'
      rw [hf] at hs'
      dsimp only at hs'
      unfold x86NativeStep9
      dsimp only
      rw [ite_eq_right nt', hf]
      dsimp only
      split at hs'
      · rename_i i n hfn
        rw [hfn]
        dsimp only
        cases e : Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n) <;>
          rw [e] at hs' <;> simp only [Open.ofResult, reduceCtorEq, Option.some.injEq] at hs'
        subst hs'
        exact ⟨_, rfl⟩
      · cases hs'
    · have ho : Open.step m = some m' := by
        rw [← Open9.step_eq_open hf]; exact hs
      obtain ⟨acc, h⟩ := Silmaril.Proofs.Machine.Process.LpsBridge.native8_open ho nt
      exact ⟨acc, by rw [native9_of_ne_undecodable (s := ⟨m, none⟩) nt' hf]; exact h⟩
  trap s w ht hw := by
    unfold x86NativeStep9
    rw [ite_eq_left (show s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] from ht)]
    exact Silmaril.Proofs.Machine.Process.LpsBridge.agrees_open8.trap s w ht hw

/-! ## Mutation probe: `Ext8`'s native step does not agree with `Open9.step`

A concrete state with `bt eax, ecx` (`0F A3 C8`, an `Ext9`-only form) at `rip`: `Open9.step`
retires it, `x86NativeStep8` reports `unmodeled`, so `Agrees x86NativeStep8 Open9.step` is
false and `agrees_open9` depends on `x86NativeStep9`'s `Ext9` arm. (Added in review.) -/

/-- Three executable bytes `0F A3 C8` at `0x1000`. -/
def btMem : Silmaril.Process.Memory :=
  { regions := [⟨0x1000, 3, ⟨true, false, true⟩⟩]
    bytes := Silmaril.Process.Memory.install ∅ 0x1000 [0x0f, 0xa3, 0xc8] }

/-- `rip = 0x1000` over `btMem`. -/
def btState : MState :=
  { core := { regs := fun _ => 0, rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }
    memory := btMem }

theorem bt_fetch3 :
    btState.memory.fetchBytes btState.core.rip.toNat 3 = some [0x0f, 0xa3, 0xc8] :=
  Silmaril.Process.Memory.readWith_eq btMem .execute 0x1000 [0x0f, 0xa3, 0xc8] (by decide)
    (fun i hi => Silmaril.Process.Memory.install_get _ 0x1000 _ i hi)

theorem bt_fetch2 : btState.memory.fetchBytes btState.core.rip.toNat 2 = some [0x0f, 0xa3] :=
  Silmaril.Process.Memory.readWith_eq btMem .execute 0x1000 [0x0f, 0xa3] (by decide)
    (fun i hi => by
      have := Silmaril.Process.Memory.install_get ∅ 0x1000 [0x0f, 0xa3, 0xc8] i
        (by simp at hi ⊢; omega)
      simp only [btMem]; rw [this]; match i, hi with | 0, _ => rfl | 1, _ => rfl)

/-- `Open9.step` retires the `bt`. -/
theorem bt_open9 : (Open9.step btState).isSome = true := by
  rw [Open9.step_of_fetch_new bt_fetch3 (i := .bt .d .rax .rcx) (by decide) rfl]; rfl

/-- LPS's `Ext8` native step does not model it. -/
theorem bt_native8 : x86NativeStep8 ⟨btState, none⟩ = .unmodeled := by
  obtain ⟨_, -, hf⟩ := Open9.fetch8_undecodable_of bt_fetch3 (by decide) (by decide) (by decide)
    (by decide)
  unfold x86NativeStep8
  rw [ite_eq_right (by rw [bt_fetch2]; decide)]
  dsimp only
  rw [hf]

/-- The `Ext9` native step does (by `agrees_open9`). -/
theorem bt_native9 : ∃ s acc, x86NativeStep9 ⟨btState, none⟩ = .ok ⟨s, acc⟩ := by
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp bt_open9
  obtain ⟨acc, e⟩ := agrees_open9.step hm'
  exact ⟨_, acc, e⟩

/-- **Mutation probe**: `Open9.step` does not agree with `x86NativeStep8`. -/
theorem not_agrees_native8_open9 : ¬ Agrees x86NativeStep8 Open9.step := by
  intro h
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp bt_open9
  obtain ⟨acc, e⟩ := h.step hm'
  rw [bt_native8] at e
  cases e

/-! ## The bridge on `x86WithFlagOracle9` -/

open Silmaril.Machine.X86.RelIsa (Le Must SafeNR ofFun loosen)
open Silmaril.Proofs.Machine.Process.LpsBridge (ExitReq)

/-- The `Ext9` open machine refines its everywhere-loosening. -/
theorem le_open9 : Le (ofFun Open9.step) (loosen Open9.isa (fun _ => True)) := by
  rw [← Silmaril.Machine.X86.RelIsa.ofIsa_open9]; exact Silmaril.Machine.X86.RelIsa.le_loosen

/-- A safe `Open.step` run is a safe run of `loosen Open9.isa ⊤`. -/
theorem safeNR_open9_of_open {Q : MState → Prop} {m : MState}
    (h : ∀ n, Silmaril.Machine.X86.Safe.SafeN Open.step Q n m) :
    ∀ n, SafeNR (loosen Open9.isa (fun _ => True)) Q n m := fun n =>
  Silmaril.Machine.X86.RelIsa.safeNR_loosen_of_safeN (I := Open9.isa)
    (Silmaril.Machine.X86.Safe.safeN_of_refines (fun hs => Open9.step_of_open hs) (h n))

/-- A terminating `Open.step` run is a `Must` run of `loosen Open9.isa ⊤`. -/
theorem must_open9_of_run {Q : MState → Prop} {k : Nat} {m m' : MState}
    (hr : Silmaril.Machine.Execution.run Open.step k m = some m') (hq : Q m') :
    Must (loosen Open9.isa (fun _ => True)) (fun _ => True) Q m :=
  Silmaril.Machine.X86.RelIsa.must_loosen_of_reaches (I := Open9.isa) ⟨k, Open9.run_of_open k hr⟩ hq

variable {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}

/-- **Process safety on `x86WithFlagOracle9`** from demonic safety on any `A` above
`ofFun Open9.step`. -/
theorem psafe9_of_safeNR {A : Silmaril.Machine.X86.RelIsa MState} (hle : Le (ofFun Open9.step) A)
    {Q : MState → Prop} {Allowed : List Event → Prop} {model : Model} (hA : Allowed [])
    (hQ : ∀ (c' : Config (flagMachine oracle x86NativeStep9)) m', AlignedF c' m' →
      c'.model = model → Q m' → PSafeF segs refused Allowed c')
    {cfg : Config (x86WithFlagOracle9 oracle)} {m : MState}
    (al : AlignedF (oracle := oracle) (nstep := x86NativeStep9) cfg m)
    (hm : cfg.model = model) (h : ∀ n, SafeNR A Q n m) :
    PSafeF (oracle := oracle) (nstep := x86NativeStep9) segs refused Allowed cfg :=
  Silmaril.Proofs.Machine.Process.LpsBridge.psafe_of_safeNR agrees_open9 hle hA hQ al hm h

/-- **Must-exit on `x86WithFlagOracle9`** from a total demonic run on any `A` above
`ofFun Open9.step`. -/
theorem mustExit9_of_must {A : Silmaril.Machine.X86.RelIsa MState} (hle : Le (ofFun Open9.step) A)
    {code : Silmaril.X86.Word} {cfg : Config (x86WithFlagOracle9 oracle)} {m : MState}
    (al : AlignedF (oracle := oracle) (nstep := x86NativeStep9) cfg m)
    (h : Must A (fun _ => True) (fun m' => ExitReq m' ∧ m'.core.read .rdi &&& 255 = code) m) :
    MustExitInAt segs spec refused [code] cfg :=
  Silmaril.Proofs.Machine.Process.LpsBridge.mustExit_of_must agrees_open9 hle al h

/-- The whole-process schema on `x86WithFlagOracle9`. -/
theorem processSafe9_of_launchR {A : Silmaril.Machine.X86.RelIsa MState}
    (hle : Le (ofFun Open9.step) A) {snapshot : X86Launch.Snapshot} {refusals : SpuriousCfg}
    {limit : Int} {en : ExecEntry} {inp : ProcInput} {Allowed : List Event → Prop}
    {Q : MState → Prop} (hA : Allowed [])
    (hrun : ∀ n, SafeNR A Q n (launchState snapshot en inp))
    (hQ : ∀ oracle (c' : Config (flagMachine oracle x86NativeStep9)) m, AlignedF c' m →
      c'.model = (X86Launch.init (x86WithFlagOracle9 oracle) snapshot en limit inp).model →
      Q m → PSafeF snapshot.image.segments (NativeX86.defaultRefusalFilter refusals) Allowed c') :
    ProcessSafeF x86NativeStep9 snapshot refusals limit en inp Allowed :=
  Silmaril.Proofs.Machine.Process.LpsBridge.processSafeF_of_launchR agrees_open9 hle hA hrun hQ

/-- The must-exit tier of a launch on `x86WithFlagOracle9`. -/
theorem mustExit9_of_launchR {A : Silmaril.Machine.X86.RelIsa MState}
    (hle : Le (ofFun Open9.step) A) {snapshot : X86Launch.Snapshot} {en : ExecEntry}
    {inp : ProcInput} {limit : Int} {code : Silmaril.X86.Word}
    (h : Must A (fun _ => True) (fun m' => ExitReq m' ∧ m'.core.read .rdi &&& 255 = code)
      (launchState snapshot en inp))
    (oracle : Oracle) (refused : RefusalFilter) :
    MustExitInAt snapshot.image.segments spec refused [code]
      (X86Launch.init (x86WithFlagOracle9 oracle) snapshot en limit inp) :=
  Silmaril.Proofs.Machine.Process.LpsBridge.mustExitF_of_launchR agrees_open9 hle h oracle refused

end Silmaril.Proofs.Machine.Process.Lps9
