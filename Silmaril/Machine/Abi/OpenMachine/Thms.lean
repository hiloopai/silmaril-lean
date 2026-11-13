module

public import Silmaril.Machine.Abi.OpenMachine.Defs
public import Silmaril.X86.Ladder.LeafArith.Thms
public import Silmaril.X86.Cert.Kinds.Thms
import Silmaril.Proofs.Machine.Abi.OpenMachine.Runs
import Silmaril.Proofs.Machine.Abi.OpenMachine.Sat
import Silmaril.Proofs.Machine.Abi.OpenMachine.LeafArith
import Silmaril.Proofs.Machine.Abi.OpenMachine.NonVacuity
import Silmaril.Proofs.Machine.Abi.OpenMachine.Strict
import Silmaril.Proofs.Machine.Abi.OpenMachine.Word64
/-! # ABI comorphisms on the open x86 machine: theorems

PROVED (standard axioms):

* `firstReturn_unique`, `callModel_subsingleton`: the first-return call relation has at most
  one outcome per entry state (the open machine is a function);
* `firstReturn_of_runsIn`: a run that stays inside the code and ends returned is the first
  return, when the return address lies outside the code;
* `totalIn_of_funCert`: **A's `FunCert.total`, strengthened**: a function certificate's run
  takes every step inside the function's code;
* `abiEntry_of_entry`, `return_of_result`: track C's System V `Entry` gives A's `AbiEntry`, and
  A's `Spec.Result` gives track C's System V `Return`;
* `sat_of_firstReturn`: the generic bridge from a contract on the open machine to
  `Contracts.Sat callModel (within ((sysv o).translate p c) room)`;
* `clamp_i32_sat`, `sat_add_u32_sat`: **ABI correctness of real decoded x86.** gcc -O2's
  `clamp_i32` and `sat_add_u32` (rung 01) satisfy the System V translation of their exact C
  contracts (`clampC`, `satC`: every call returns the C function's value), for every System V
  profile, on entry states with the code loaded, the entry at the function and the return
  address outside the code (`Room`);
* `clamp_i32_ffiRealizes`, `sat_add_u32_ffiRealizes`: concrete instances of A's
  `FnContract.toFfiRealizes` (the ABI model's typed `Ffi.Realizes`), with track C's `int32`/`uint32`
  object specifications `SystemV.Kind.spec` and the planned signature `Proto.ffi`;
* `clamp_i32_nonvacuous`: a concrete entry state meets the room and the translated
  precondition, and its `callModel` outcome is observed as `clamp_i32(5, 0, 3) = 3`;
* `clamp_i32_rejects_id`: the same bridge refutes a mutated contract ("return the first
  argument"), so `clamp_i32_sat` discriminates contracts;
* `runsIn_iff`, `firstReturn_iff`: `RunsIn`/`FirstReturn` here are the generic
  `FnContract.RunsIn Open.isa`/`FnContract.FirstReturn Open.isa`;
* `callModel_of_strict`: **a strict (first-return) spec is what `callModel` reads**: an
  outcome exists and every outcome is a `Spec.Result`; `sat_of_strict`: `sat_of_firstReturn`
  from a `Spec.Strict` proof;
* `clamp_strict`, `sat_strict`: rung 01 as strict specs (entries with the return address
  outside the code) through the generic `BlockCert.FunCert.strict`; `clamp_i32_sat_strict`,
  `sat_add_u32_sat_strict`: `clamp_i32_sat`/`sat_add_u32_sat` re-derived from them;
* `bytes4_inj`, `chunk32_iff`, `resultAt_int32`, `resultAt_uint32`: 32-bit scalars in
  registers are read back exactly (the 32-bit case of track C's pending decoding
  functionality lemma);
* round 4 (F7): `bytes8_inj`, `chunk64_iff`, `resultAt_word64`: the 64-bit case (moved from
  `tests/machine/Abi.lean` into the library): `long`, `unsigned long` and pointer results
  are read back exactly as `rax`.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.OpenMachine

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.C.Api (Scalar)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Ladder.LeafArith
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options)

theorem runsIn_mono {P Q : MState → Prop} (h : ∀ m, P m → Q m) {s t : MState}
    (r : RunsIn P s t) : RunsIn Q s t :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.runsIn_mono h r

theorem runsIn_trans {P : MState → Prop} {s t u : MState} (r₁ : RunsIn P s t)
    (r₂ : RunsIn P t u) : RunsIn P s u :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.runsIn_trans r₁ r₂

theorem runsIn_reaches {P : MState → Prop} {s t : MState} (r : RunsIn P s t) :
    Silmaril.Machine.Execution.Reaches Open.step s t :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.runsIn_reaches r

theorem firstReturn_unique {s t t' : MState} (h : FirstReturn s t) (h' : FirstReturn s t') :
    t = t' :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.firstReturn_unique h h'

theorem callModel_subsingleton (s : Ffi.State) {t t' : Ffi.State} (h : t ∈ callModel s)
    (h' : t' ∈ callModel s) : t = t' :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.callModel_subsingleton s h h'

theorem firstReturn_of_runsIn {base : Word} {len : Nat} {s t : MState}
    (r : RunsIn (InCode base len) s t) (ret : Returned s t) (outside : RetOutside base len s) :
    FirstReturn s t :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.firstReturn_of_runsIn r ret outside

/-- A's `FunCert.total` with runs inside the code. -/
theorem totalIn_of_funCert {F : BlockCert.FunCert} (S : FnContract.Spec MState)
    {entry : BlockCert.Blk} (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Silmaril.X86.Ext.Loaded m.memory F.base F.code ∧
        m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧ F.ann entry.off m m) :
    TotalIn S fun _ => InCode F.base F.code.length :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.totalIn_of_funCert S hentry hc hvc hpre

variable {o : Options} {p : Proto}

theorem abiEntry_of_entry {a : vocab.Args p} {s : Ffi.State} (entry : (sysv o).Entry p a s) :
    FnContract.AbiEntry s.machine.core s.machine.memory :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.abiEntry_of_entry entry

theorem return_of_result {S : FnContract.Spec MState} {a : vocab.Args p} {s : Ffi.State}
    {t : MState} (entry : (sysv o).Entry p a s) (res : S.Result Open.isa s.machine t) :
    (sysv o).Return p s { s with machine := t } :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.return_of_result entry res

/-- **The generic bridge**: contracts on the open machine with first-return runs meet the
System V translation of a C contract under `callModel`. -/
theorem sat_of_firstReturn {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))}
    {S : FnContract.Spec MState} {room : Ffi.State → Prop}
    (total : ∀ a s, (sysv o).Entry p a s → c.pre a → room s →
      ∃ t, FirstReturn s.machine t ∧ S.Result Open.isa s.machine t)
    (post : ∀ a s t, (sysv o).Entry p a s → c.pre a → room s → S.post s.machine t →
      (∃ r, (sysv o).ResultAt p s { s with machine := t } r) ∧
        ∀ r, (sysv o).ResultAt p s { s with machine := t } r → c.post a (some r)) :
    Contracts.Sat callModel (within ((sysv o).translate p c) room) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.sat_of_firstReturn total post

theorem bytes4_inj {x y : BitVec 32}
    (h : Ffi.bytesOfNat x.toNat 0 4 = Ffi.bytesOfNat y.toNat 0 4) : x = y :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.bytes4_inj h

theorem chunk32_iff (s : Ffi.State) (r : Reg) (v : BitVec 32) :
    Ffi.ChunksAt s (Ffi.bytesOfNat (v.setWidth 64).toNat 0 4) [⟨0, 4, .gp r⟩] ↔
      (s.machine.core.read r).setWidth 32 = v :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.chunk32_iff s r v

theorem resultAt_int32 (args : List Scalar) (h : args.length ≤ SystemV.maxArity)
    (s s' : Ffi.State) (r : BitVec 32) :
    (sysv o).ResultAt ⟨⟨args, some .int32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.resultAt_int32 args h s s' r

theorem resultAt_uint32 (args : List Scalar) (h : args.length ≤ SystemV.maxArity)
    (s s' : Ffi.State) (r : BitVec 32) :
    (sysv o).ResultAt ⟨⟨args, some .uint32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.resultAt_uint32 args h s s' r

theorem bytes8_inj {x y : BitVec 64}
    (h : Ffi.bytesOfNat x.toNat 0 8 = Ffi.bytesOfNat y.toNat 0 8) : x = y :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.bytes8_inj h

theorem chunk64_iff (s : Ffi.State) (r : Reg) (v : BitVec 64) :
    Ffi.ChunksAt s (Ffi.bytesOfNat v.toNat 0 8) [⟨0, 8, .gp r⟩] ↔
      s.machine.core.read r = v :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.chunk64_iff s r v

/-- The System V read-back of a 64-bit (`long`, `unsigned long`, pointer) result is `rax`. -/
theorem resultAt_word64 (args : List Scalar) (k : Scalar)
    (hk : k = .uint64 ∨ k = .int64 ∨ k = .pointer) (h : args.length ≤ SystemV.maxArity)
    (s s' : Ffi.State) (r : vocab.Ret ⟨⟨args, some k⟩, h⟩) :
    (sysv o).ResultAt ⟨⟨args, some k⟩, h⟩ s s' r ↔
      s'.machine.core.read .rax = SystemV.Kind.word k r :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.resultAt_word64 args k hk h s s' r

/-! ## Strict (first-return) contracts -/

theorem runsIn_iff {P : MState → Prop} {s t : MState} :
    RunsIn P s t ↔ FnContract.RunsIn Open.isa P s t :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.runsIn_iff

theorem firstReturn_iff {s t : MState} :
    FirstReturn s t ↔ FnContract.FirstReturn Open.isa s t :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.firstReturn_iff

/-- **A strict spec is read by `callModel` exactly**: from an entry state `callModel` has an
outcome, and every outcome is a call result. -/
theorem callModel_of_strict {S : FnContract.Spec MState} (h : S.Strict Open.isa)
    {s : Ffi.State} (ha : FnContract.AbiEntry s.machine.core s.machine.memory)
    (he : S.entry s.machine) :
    (∃ t, t ∈ callModel s) ∧ ∀ t ∈ callModel s, S.Result Open.isa s.machine t.machine :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.callModel_of_strict h ha he

/-- `sat_of_firstReturn` from a strict spec. -/
theorem sat_of_strict {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))}
    {S : FnContract.Spec MState} {room : Ffi.State → Prop} (h : S.Strict Open.isa)
    (entry : ∀ a s, (sysv o).Entry p a s → c.pre a → room s → S.entry s.machine)
    (post : ∀ a s t, (sysv o).Entry p a s → c.pre a → room s → S.post s.machine t →
      (∃ r, (sysv o).ResultAt p s { s with machine := t } r) ∧
        ∀ r, (sysv o).ResultAt p s { s with machine := t } r → c.post a (some r)) :
    Contracts.Sat callModel (within ((sysv o).translate p c) room) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.sat_of_strict h entry post

/-- Rung 01 `clamp_i32` as a strict spec, from its certificate via the generic `Cert`. -/
theorem clamp_strict :
    (clampSpec'.restrict (FnContract.RetOutside Open.isa base code.length)).Strict Open.isa :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.clamp_strict

/-- Rung 01 `sat_add_u32` as a strict spec, from its certificate via the generic `Cert`. -/
theorem sat_strict :
    (satSpec.restrict (FnContract.RetOutside Open.isa base code.length)).Strict Open.isa :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.sat_strict

/-- `clamp_i32_sat`, re-derived from the strict spec. -/
theorem clamp_i32_sat_strict (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.clamp_sat_strict o

/-- `sat_add_u32_sat`, re-derived from the strict spec. -/
theorem sat_add_u32_sat_strict (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate satProto satC) (Room base code 0x90)) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.sat_sat_strict o

/-! ## Rung 01 -/

/-- **gcc -O2 `clamp_i32` is System V-correct on the decoded open machine.** -/
theorem clamp_i32_sat (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.clamp_sat o

/-- **gcc -O2 `sat_add_u32` is System V-correct on the decoded open machine.** -/
theorem sat_add_u32_sat (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate satProto satC) (Room base code 0x90)) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.sat_sat o

/-- **`clamp_i32_sat` is not vacuous**: some state meets the translated precondition and the
room (`clamp_i32(5, 0, 3)` placed by the System V plan, the code loaded, return address
`0x401000`), and the System V read-back observes its `callModel` outcome as `3`. -/
theorem clamp_i32_nonvacuous (o : Options) :
    ∃ s, (within ((sysv o).translate clampProto clampC) (Room base code 0x30)).pre s ∧
      ∃ t ∈ callModel s, (sysv o).Observe clampProto s t (some (3 : BitVec 32)) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.NonVacuity.clamp_exists o

/-- **The bridge is not trivially true**: the decoded `clamp_i32` does not satisfy the
System V translation of a mutated contract (`clampIdC`, "return the first argument"). -/
theorem clamp_i32_rejects_id (o : Options) :
    ¬ Contracts.Sat callModel (within ((sysv o).translate clampProto clampIdC) (Room base code 0x30)) :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.NonVacuity.clamp_rejects_id o

/-- `clamp_i32` as the ABI model's typed FFI certificate (`int32` object specs). -/
theorem clamp_i32_ffiRealizes (profile : Profile) :
    Ffi.Realizes (clampProto.ffi profile (SystemV.plan_intPlan profile))
      (fun v => clampSpec v.1 v.2.1 v.2.2.1) (fun _ _ => False) (fun _ _ _ => True)
      (ffiLoadedAt 0x30) Open.ffiExecute :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.clamp_ffiRealizes profile

/-- `sat_add_u32` as the ABI model's typed FFI certificate (`uint32` object specs). -/
theorem sat_add_u32_ffiRealizes (profile : Profile) :
    Ffi.Realizes (satProto.ffi profile (SystemV.plan_intPlan profile))
      (fun v => satAddSpec v.1 v.2.1) (fun _ _ => False) (fun _ _ _ => True)
      (ffiLoadedAt 0x90) Open.ffiExecute :=
  Silmaril.Proofs.Machine.Abi.OpenMachine.sat_ffiRealizes profile

end Silmaril.Machine.Abi.OpenMachine
