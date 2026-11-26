module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
public import Silmaril.Proofs.X86.Concurrency.Bridge.Step
public import Silmaril.Proofs.X86.Concurrency.Bridge.Defined

/-!
# The checker against the real machine: proofs

`tvRunDefined_holds` and `tvRun_real` (header
`Silmaril.X86.Concurrency.Bridge.Thms`). The pieces:

* `chk1_ok`: every form `chk1` accepts is a listed base or atomic form, and a memory form of
  `memStep` or inert (as `kindOf_ok` for the table);
* `tvRunDefined_holds`: the cores a symbolic run of an accepted thread reaches sit at checked
  instructions (`Cir.Tv.tvRun_reach`), so where the real step succeeds the symbolic step is
  defined (`symDefined_of_exec` and `exec_of_accepted`);
* `tvRun_real`: so a real run (`A9Run`) is an `XRun` (`xrun_of_a9run`), and the run-level
  soundness (`Cir.Tv.tvRun_xrun`, any read values) makes it a CIR run of the certificate.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge

open Silmaril.X86 (State)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep)
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (XThread Cert tvRun chk1 fetchAt normActs actVals)
open Silmaril.X86.Concurrency.Cir.TvCfg (XRun)
open Silmaril.X86.Concurrency.Bridge

/-- Every form `chk1` accepts is a listed base or atomic form, and a memory form of `memStep`
or inert. -/
theorem chk1_ok {K Z : List Reg} {nx : Silmaril.X86.Word} {i : Atomic9.Instr} {ops : List Stmt}
    {K' Z' : List Reg} (h : chk1 K Z nx i ops = some (K', Z')) :
    Shaped i ∧ ∀ s n, memForm i = true ∨
      (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = true := by
  unfold chk1 at h
  split at h
  all_goals first
    | (simp at h; done)
    | (refine ⟨by simp [Shaped], fun s n => ?_⟩
       simp [memForm, MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses,
         MemEvent.ext9Accesses, MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv,
         MemEvent.memEv, Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes]
       done)
    | (refine ⟨by simp [Shaped], fun s n => .inl ?_⟩
       split at h
       · rename_i hc
         obtain ⟨-, -, hb, -⟩ := hc
         rename_i op _ _ _ _ _ _ _ _
         cases op <;> simp_all [memForm, Tv.binOf]
       · cases h)

theorem tvRun_len {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K) :
    t.code.length < 2 ^ 64 := by
  unfold tvRun at h
  split at h
  · rename_i hok; exact hok.2
  · cases h

/-- **The symbolic step is defined on accepted straight-line code wherever the real step
succeeds** (the `tvRun` counterpart of `Task.tvCfgDefined`). -/
theorem tvRunDefined_holds {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K) :
    ∀ (acc : List (List XAct)) (s : State), XRun t t.init acc s → s.rip ≠ t.endRip →
      ∀ (m : Memory) (s' : State) (m' : Memory), m.regions = t.regions →
        Loaded m t.base t.code → Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩ → SymDefined t s := by
  intro acc s hx hne m s' m' hR hl hs
  obtain ⟨o, i, n, K₁, Z₁, ops, K₂, Z₂, hrip, ho, hfa, hc⟩ := Tv.tvRun_reach h hx hne
  have hf : t.fetch s = some (i, n) := by
    unfold Silmaril.X86.Litmus.Thread.fetch
    rw [off_of_rip hrip (Nat.lt_trans ho (tvRun_len h))]
    exact hfa
  obtain ⟨hsh, hmem⟩ := chk1_ok hc
  exact symDefined_of_exec hf hR (exec_of_accepted hrip hfa hsh hl hs) (hmem s n)

/-- **The checker against the real machine**: every real run of an accepted thread from its
initial core to the end of its code is an `XRun` whose actions the real memories answer and take,
and a run of the certificate's CIR thread over any domain holding the values read, with the same
actions up to `normActs` and the same final registers outside the clobber set. -/
theorem tvRun_real {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {xs : List SeqStep} {s' : State} (hr : A9Run t t.init xs s') (he : s'.rip = t.endRip) :
    ∃ acc, XRun t t.init acc s' ∧ List.Forall₂ ActsOk acc xs ∧
      ∀ D : List Nat, (∀ v ∈ actVals acc, v ∈ D) →
        ∃ p ∈ run D c.body Regs.zero, normActs acc.flatten = p.1.flatMap Lab.acts ∧
          ∀ r, r ∉ K → s'.read r = p.2 r := by
  obtain ⟨acc, hx, hok⟩ := xrun_of_a9run hr fun acc s₁ hx hne m s₂ m₂ hR hl hs =>
    tvRunDefined_holds h acc s₁ hx hne m s₂ m₂ hR hl hs
  refine ⟨acc, hx, hok, fun D hD => Tv.tvRun_xrun h hx he fun acts hacts a ha hrd => hD _ ?_⟩
  exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_flatten.mpr ⟨acts, hacts, ha⟩, hrd⟩,
    rfl⟩

/-! ## A real run of an 8-byte load reading `2 ^ 32` (non-vacuity) -/

open Silmaril.X86.Concurrency.Cir.Tv (RunEx.qLoad RunEx.qLoadCert)

namespace RunEx

/-- The data page: `2 ^ 32` little-endian at `0x10000`, then zeros. -/
def dataPage : List (BitVec 8) := [0, 0, 0, 0, 1, 0, 0, 0] ++ List.replicate 4088 0

/-- The code page: `qLoad`'s bytes, then zeros. -/
def codePage : List (BitVec 8) := RunEx.qLoad.code ++ List.replicate 4088 0

/-- A one-thread test memory: both pages installed. -/
def mem : Memory := ⟨Silmaril.X86.Litmus.testRegions 1,
  Memory.install (Memory.install ∅ 0x400000 codePage) 0x10000 dataPage⟩

/-- The operand `[0x10000]`. -/
def qMem : Silmaril.X86.Ext.Mem :=
  { base := .none, index := none, disp := 0x10000#32, rip_no_index := by decide }

/-- The core after the load. -/
def post : State :=
  { Silmaril.X86.Ext.Sz.write .q RunEx.qLoad.init .rax
      ((BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [0, 0, 0, 0, 1, 0, 0, 0])).setWidth 64) with
    rip := RunEx.qLoad.init.rip + BitVec.ofNat 64 8 }

theorem dataPage_len : dataPage.length = 4096 := by
  rw [dataPage, List.length_append, List.length_replicate]; rfl

theorem codePage_len : codePage.length = 4096 := by
  rw [codePage, List.length_append, List.length_replicate]; rfl

theorem get_code (i : Nat) (hi : i < 4096) :
    mem.bytes.get? (0x400000 + i) = some (codePage[i]'(by rw [codePage_len]; exact hi)) := by
  show (Memory.install (Memory.install ∅ 0x400000 codePage) 0x10000 dataPage).get? _ = _
  rw [Memory.install_outside _ _ _ _ (.inr (by rw [dataPage_len]; omega)),
    Memory.install_get _ _ _ _ (by rw [codePage_len]; exact hi)]

theorem get_data (i : Nat) (hi : i < 4096) :
    mem.bytes.get? (0x10000 + i) = some (dataPage[i]'(by rw [dataPage_len]; exact hi)) := by
  show (Memory.install (Memory.install ∅ 0x400000 codePage) 0x10000 dataPage).get? _ = _
  rw [Memory.install_get _ _ _ _ (by rw [dataPage_len]; exact hi)]

theorem backed : Backed mem := by
  intro a ha
  simp only [Memory.permits, mem] at ha
  simp [Silmaril.X86.Litmus.testRegions, Silmaril.Process.Region.Contains,
    Silmaril.X86.Litmus.dataBase, Silmaril.X86.Litmus.dataSize,
    Silmaril.Process.Permissions.allows] at ha
  rcases ha with ha | ha
  · have := of_decide_eq_true ha
    have := get_data (a - 0x10000) (by omega)
    rw [show 0x10000 + (a - 0x10000) = a by omega] at this
    rw [this]; rfl
  · have := of_decide_eq_true ha
    have := get_code (a - 0x400000) (by omega)
    rw [show 0x400000 + (a - 0x400000) = a by omega] at this
    rw [this]; rfl

theorem rb_code (n i : Nat) (h : i + n ≤ 4096) :
    Memory.readBacking mem.bytes (0x400000 + i) n = some ((codePage.drop i).take n) := by
  induction n generalizing i with
  | zero => simp [Memory.readBacking]
  | succ n ih =>
    simp only [Memory.readBacking, get_code i (by omega), Option.bind_eq_bind, Option.bind_some]
    rw [show 0x400000 + i + 1 = 0x400000 + (i + 1) by omega, ih (i + 1) (by omega)]
    rw [List.drop_eq_getElem_cons (i := i) (by rw [codePage_len]; omega)]
    rfl

theorem rb_data (n i : Nat) (h : i + n ≤ 4096) :
    Memory.readBacking mem.bytes (0x10000 + i) n = some ((dataPage.drop i).take n) := by
  induction n generalizing i with
  | zero => simp [Memory.readBacking]
  | succ n ih =>
    simp only [Memory.readBacking, get_data i (by omega), Option.bind_eq_bind, Option.bind_some]
    rw [show 0x10000 + i + 1 = 0x10000 + (i + 1) by omega, ih (i + 1) (by omega)]
    rw [List.drop_eq_getElem_cons (i := i) (by rw [dataPage_len]; omega)]
    rfl

theorem loaded : Loaded mem RunEx.qLoad.base RunEx.qLoad.code := by
  simp only [Loaded, Memory.fetchBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  exact rb_code 8 0 (by omega)

theorem read : mem.readBytes 0x10000 8 = some [0, 0, 0, 0, 1, 0, 0, 0] := by
  simp only [Memory.readBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  exact rb_data 8 0 (by omega)

theorem step : Atomic9.step ⟨RunEx.qLoad.init, mem⟩ = some ⟨post, mem⟩ := by
  refine Atomic9.step_of_listed (o := 0) (l := 8)
    (i := .open9 (.ext8 (.base (.load .q .rax qMem))))
    loaded (by decide +kernel) (by decide) (by decide +kernel) ?_
  simp only [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.loadN]
  rw [show (Silmaril.X86.Ext.Mem.addr qMem RunEx.qLoad.init
      (RunEx.qLoad.init.rip + BitVec.ofNat 64 8)).toNat = 0x10000 by decide +kernel,
    show Silmaril.X86.Ext.Sz.q.bytes = 8 from rfl, read]
  rfl

end RunEx

/-- **`tvRun_real` is not vacuous, and reaches past `2 ^ 32`**: a real run
(`A9Run`, on a backed one-thread test memory) of `mov rax, qword [0x10000]`, which `tvRun`
accepts, reads `2 ^ 32`; `tvRun_real` gives a CIR run of the certificate over the values read
with `rax = 2 ^ 32`. -/
theorem tvRun_real_qLoad : ∃ xs s', A9Run RunEx.qLoad RunEx.qLoad.init xs s' ∧
    s'.rip = RunEx.qLoad.endRip ∧ (s'.read .rax).toNat = 2 ^ 32 ∧
    ∃ acc, XRun RunEx.qLoad RunEx.qLoad.init acc s' ∧ List.Forall₂ ActsOk acc xs ∧
      ∃ p ∈ run (actVals acc) RunEx.qLoadCert.body Regs.zero,
        normActs acc.flatten = p.1.flatMap Lab.acts ∧ (p.2 .rax).toNat = 2 ^ 32 := by
  have hacc : tvRun RunEx.qLoad RunEx.qLoadCert = some [] := by decide
  have hr : A9Run RunEx.qLoad RunEx.qLoad.init [⟨RunEx.mem, RunEx.post, RunEx.mem⟩] RunEx.post :=
    .cons _ _ _ _ (by decide +kernel) rfl RunEx.loaded RunEx.backed RunEx.step (.nil _)
  have he : RunEx.post.rip = RunEx.qLoad.endRip := by decide +kernel
  have hv : (RunEx.post.read .rax).toNat = 2 ^ 32 := by decide +kernel
  obtain ⟨acc, hx, hok, hD⟩ := tvRun_real hacc hr he
  obtain ⟨p, hp, hn, hk⟩ := hD (actVals acc) fun _ h => h
  exact ⟨_, _, hr, he, hv, acc, hx, hok, p, hp, hn, by rw [← hk .rax (by simp)]; exact hv⟩

end Silmaril.Proofs.X86.Concurrency.Bridge
