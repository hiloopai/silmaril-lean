module

public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.CatFile
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.HelloNonVacuous
public import Silmaril.Raw.Elf.Link.Dyn.Streams.Rep

/-! # `cat FILE`: the premises of `Verified` are satisfiable

A concrete process for `cat-file-gcc f`: the executable at `b0` holding exactly the loader
relation's image, `libc.so.6`/`ld.so` holding the pinned chunks (`libcF`, `ldF`, as for hello), a
stack with `argc = 2`, `argv = ["", "f"]` (`cfStk`, in `memOfS`), the thread-control block with
guard `0`, and a stdio environment on B's slot representation of streams (`slotRep`: `stdin`,
`stdout`, `stderr` in the first three slots of the library's arena), with allocations succeeding
(`Std.allocates`) and the file `f` holding `hi\n`.

`catFileGcc_premises`: this process meets every premise of `catFileGcc_verified`, and
`catFileGcc_s0` is its conclusion for it: every run copies `hi\n` to stdout and exits 0.
`cfAtMain_sat`: the library's promise at `main` (`World.atMain`, `AtMain`) is met by a memory
holding the three streams (`slotRep`'s encoding) and the COPY-relocated `stdout` variable, so
the world does not make `main`'s entry impossible. (A run reaching that state from `cfs0` is the
loader/start-up part not proved here; see F8's `task_mainLibReach` for sha256sum.) -/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (loadN leBytes)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc (PState Keeps CStr StackRoom)
open Silmaril.Elf.Link.Dyn.Small.NonVacuous
open Silmaril.Elf.Link.DynElf

/-- The operand: `f`. -/
def cfName : List UInt8 := [0x66]

/-- The world: `cat-file f`, where `f` holds `hi\n`. -/
def cfW : Program.World := { argv := [[], cfName], fs := fun _ => .ok [0x68, 0x69, 0x0a] }

/-- The stdio environment: `slotRep` (streams in the arena slots from `A0`), `stdout` and
`stderr` in slots 1 and 2, `errno` at `0x1000` (below the arena), allocations succeed, up to 4 open streams of at most
`S0 - 64` bytes (the slot model's bound). -/
def cfE : Streams.Env where
  S := Streams.Total.slotRep
  stdoutF := BitVec.ofNat 64 (Streams.Total.A0 + Streams.Total.S0)
  stderrF := BitVec.ofNat 64 (Streams.Total.A0 + 2 * Streams.Total.S0)
  fs := cfW.fs
  optindA := 0
  errnoA := 0x1000#64
  maxAllocs := 4
  maxHeap := 0x10000
  maxOpen := 4
  maxFile := Streams.Total.S0 - 64

/-- `stdin` in slot 0. -/
def cfS : Std where
  E := cfE
  stdinF := BitVec.ofNat 64 Streams.Total.A0

/-- The top of the kernel's stack, from `sp0`: `argc = 2`, `argv[0] = sp0 + 32`,
`argv[1] = sp0 + 33`, `NULL`, then the strings `""` and `"f"`. -/
@[irreducible] def cfTop : List Byte :=
  leBytes 2#64 8 ++ leBytes (sp0 + 32#64) 8 ++ leBytes (sp0 + 33#64) 8 ++ leBytes 0#64 8 ++ [0#8, 0x66#8, 0#8]

theorem cfTop_len : cfTop.length = 35 := by unfold cfTop; rfl

/-- The kernel's stack (`sp0 - 4096 … sp0 + 4095`): zeros below `sp0`, `cfTop`, zeros. -/
def cfStk : List Byte := List.replicate 4096 0#8 ++ (cfTop ++ List.replicate 4061 0#8)

theorem cfStk_len : cfStk.length = 8192 := by
  simp only [cfStk, List.length_append, List.length_replicate, cfTop_len]

theorem cfStk_get {j : Nat} (hj : j < 35) : cfStk[4096 + j]? = cfTop[j]? := by
  rw [cfStk, List.getElem?_append_right (by rw [List.length_replicate]; omega), List.length_replicate,
    Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [cfTop_len]; exact hj)]

def cfT : List (Nat × Option Word) := tableOf catFileGcc.slots

set_option maxRecDepth 100000 in
theorem cf_T : catFileGcc.slots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some cfT := by decide +kernel

set_option maxRecDepth 100000 in
theorem cf_tab : tableOk catFileGcc.file catFileGcc.info cfT catFileGcc.layout.size = true := by
  decide +kernel

/-- The memory at `_start`: the image, the stack `cfStk`, the TCB. -/
abbrev cfMem : Memory := memOfS cfStk catFileGcc.file catFileGcc.info cfT catFileGcc.layout.size

/-- The state `_start` is entered with. -/
def cfs0 : PState := sOf cfMem catFileGcc.layout.start (stdinBytes cfW)

/-- The argument area: the `argv` vector and the two strings. -/
def cfArgs (a : Nat) : Prop := sp0.toNat + 8 ≤ a ∧ a < sp0.toNat + 40

set_option maxRecDepth 100000 in
theorem cf_info : finfo catFileGcc.file = some catFileGcc.info := by decide +kernel

set_option maxRecDepth 100000 in
theorem cf_slots : slots [catFileGcc.file, libcF, ldF] false catFileGcc.file catFileGcc.info =
    some catFileGcc.slots := by
  have F := Bin.facts catFileGcc_ok
  have hc := libc_ok
  have hl := ld_ok
  simp only [LibPin.ok, Bool.and_eq_true, beq_iff_eq] at hc hl
  exact slots_of_known (ks := [⟨catFileGcc.file, catFileGcc.info, Hello.exeFacts catFileGcc.refs⟩,
    ⟨libcF, libc.info, libc.facts⟩, ⟨ldF, ld.info, ld.facts⟩]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact Hello.exeKnown_ok F.info F.refs
      · exact ⟨run_sparse hlibcF hc.1, fun e he => Glibc.facts_of hc.2 hlibcF e he⟩
      · exact ⟨run_sparse hldF hl.1, fun e he => Glibc.facts_of hl.2 hldF e he⟩) F.slotsK

set_option maxRecDepth 100000 in
theorem cf_loaded : ExeLoaded [catFileGcc.file, libcF, ldF] [b0, lb0, ldb0] ifn0 false res0 cfMem :=
  ⟨_, _, _, _, _, rfl, rfl, cf_info, fun h => absurd h (by decide), cf_slots, cf_T,
    imageOk_of_tableS (by decide) cf_tab⟩

set_option maxRecDepth 100000 in
theorem cf_placed : Placed catFileGcc b0 lb0 gate0 := by
  constructor <;> (try unfold Crt.Img) <;> decide +kernel

/-- The process world of the concrete process. -/
abbrev cfW0 : Proc.World := world catFileGcc cfS cfW b0 lb0 gate0 (!cfW.stdoutFull) cfArgs fs0

/-- A read of `l` from the top of the stack (`cfTop`) at `sp0 + o`. -/
theorem cf_read {o : Nat} {l : List Byte} (ho : o + l.length ≤ 35)
    (hl : ∀ k < l.length, cfTop[o + k]? = l[k]?) :
    cfMem.readBytes (sp0.toNat + o) l.length = some l := by
  have hn : catFileGcc.layout.size < 2 ^ 32 := by decide
  have := readWith_of_points (mem := cfMem) (acc := .read) (l := l) (a := sp0.toNat + o)
    (by rw [sp0_toNat]; omega) (by rw [sp0_toNat]; omega) (fun k hk => by
      refine ⟨stackS_permits (Or.inl rfl) (by rw [sp0_toNat]; omega) (by rw [sp0_toNat]; omega), ?_⟩
      have := stackS_get (stk := cfStk) (f := catFileGcc.file) (i := catFileGcc.info) (T := cfT) hn cfStk_len
        (k := 4096 + o + k) (by omega)
      rw [show sp0.toNat - 4096 + (4096 + o + k) = sp0.toNat + o + k by rw [sp0_toNat]; omega] at this
      rw [this, show 4096 + o + k = 4096 + (o + k) by omega, cfStk_get (by omega), hl k hk, List.getElem?_eq_getElem hk])
  simpa [Memory.readBytes] using this

/-- A word of the top of the stack (`cfTop`) at `sp0 + o`. -/
theorem cf_read8 {o : Nat} {w : Word} (ho : o + 8 ≤ 35)
    (hl : ∀ k < 8, cfTop[o + k]? = (Silmaril.Machine.LittleEndian.encodeWords [w])[k]?) :
    cfMem.readBytes (sp0.toNat + o) 8 = some (Silmaril.Machine.LittleEndian.encodeWords [w]) := by
  have := cf_read (o := o) (l := Silmaril.Machine.LittleEndian.encodeWords [w])
    (by rw [Silmaril.X86.length_encodeWords_singleton]; exact ho)
    (fun k hk => hl k (by rw [Silmaril.X86.length_encodeWords_singleton] at hk; exact hk))
  rwa [Silmaril.X86.length_encodeWords_singleton] at this

set_option maxRecDepth 100000 in
theorem cf_atStart : AtStart catFileGcc cfW0 cfW b0 cfs0 := by
  have hsp : cfs0.m.core.read .rsp = sp0 := rfl
  have hsz : catFileGcc.layout.size = 0x4020 := by decide
  refine ⟨rfl, rfl, by rw [hsp, sp0_toNat], ?_, ?_, ?_, ⟨0#64, guardS (by decide)⟩⟩
  · refine ⟨by rw [hsp, sp0_toNat]; decide, by rw [hsp, sp0_toNat]; decide, fun a h1 h2 => ?_⟩
    rw [hsp] at h1 h2
    have h3 : a < sp0.toNat + 4096 := by rw [sp0_toNat] at h2 ⊢; omega
    refine ⟨stackS_permits (Or.inl rfl) h1 h3, stackS_permits (Or.inr rfl) h1 h3, ?_⟩
    rintro (h | h | h)
    · simp only [Proc.World.InImage, world, world0, hsz, b0_toNat] at h; rw [sp0_toNat] at h1; omega
    · simp only [world, world0, cfArgs] at h; omega
    · simp only [world, world0, libWords] at h
      rcases h with ⟨v, hv, -, -, hc⟩ | h
      · have : catFileGcc.vars = [⟨nm "stdout", 0x4010, 0x0, true⟩] := rfl
        rw [this, List.mem_singleton] at hv; subst hv; cases hc
      · have : (fs0 + 0x28#64).toNat = fs0.toNat + 0x28 := rfl
        rw [this, fs0_toNat] at h; rw [sp0_toNat] at h1 h2; omega
  · rw [hsp]
    exact cf_read (o := 0) (l := Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 2])
      (by decide) (fun k hk => by
        simp only [Silmaril.X86.length_encodeWords_singleton] at hk
        unfold cfTop; interval_cases k <;> decide +kernel)
  · intro i hi
    have hi2 : i < 2 := by simpa [cfW] using hi
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · have ea : (cfs0.m.core.read .rsp + 8#64 + BitVec.ofNat 64 (8 * 0)).toNat = sp0.toNat + 8 := by
        rw [hsp, sp0_toNat]; rfl
      have ep : (sp0 + 32#64).toNat = sp0.toNat + 32 := by rw [sp0_toNat]; rfl
      refine ⟨sp0 + 32#64, Proc.loadN_of_enc ?_, ⟨by simp [cfW, Streams.ofSpec], ?_⟩, fun k hk => ?_,
        fun j hj => ?_⟩
      · rw [ea]
        exact cf_read8 (o := 8) (by decide) (fun k hk => by unfold cfTop; interval_cases k <;> decide +kernel)
      · rw [ep]
        exact cf_read (o := 32) (l := Streams.ofSpec ([] : List UInt8) ++ [0#8]) (by decide)
          (fun k hk => by
            obtain rfl : k = 0 := by simpa [Streams.ofSpec] using hk
            unfold cfTop; decide +kernel)
      · show cfArgs _; rw [ea]; simp only [cfArgs]; omega
      · show cfArgs _; rw [ep]; simp only [cfArgs]; simp [cfW] at hj; omega
    · have ea : (cfs0.m.core.read .rsp + 8#64 + BitVec.ofNat 64 (8 * 1)).toNat = sp0.toNat + 16 := by
        rw [hsp, sp0_toNat]; rfl
      have ep : (sp0 + 33#64).toNat = sp0.toNat + 33 := by rw [sp0_toNat]; rfl
      refine ⟨sp0 + 33#64, Proc.loadN_of_enc ?_, ⟨by simp [cfW, cfName, Streams.ofSpec], ?_⟩, fun k hk => ?_,
        fun j hj => ?_⟩
      · rw [ea]
        exact cf_read8 (o := 16) (by decide) (fun k hk => by unfold cfTop; interval_cases k <;> decide +kernel)
      · rw [ep]
        exact cf_read (o := 33) (l := Streams.ofSpec cfName ++ [0#8]) (by decide)
          (fun k hk => by simp [Streams.ofSpec, cfName] at hk; unfold cfTop; interval_cases k <;> decide +kernel)
      · show cfArgs _; rw [ea]; simp only [cfArgs]; omega
      · show cfArgs _; rw [ep]; simp only [cfArgs]; simp [cfW, cfName] at hj; omega

/-- `cfS` allocates: four streams of up to `S0 - 64` bytes, and `f` holds three. -/
theorem cf_allocates : Std.allocates cfS := by
  refine ⟨rfl, by decide, fun p fd st h => ?_⟩
  simp only [cfS, cfE, cfW, Streams.openedSt, Option.some.injEq] at h
  subst h
  show _ ≤ Streams.Total.S0 - 64
  simp [Streams.ofSpec, Streams.Total.S0]

set_option maxRecDepth 100000 in
/-- **The premises of `catFileGcc_verified` hold of a concrete process** (one operand, the slot
representation of streams, allocations succeed). -/
theorem catFileGcc_premises :
    Tier.operands 1 cfW ∧ ChunksOf libcF libc.chunks ∧ ChunksOf ldF ld.chunks ∧ cfS.E.fs = cfW.fs ∧
    Std.allocates cfS ∧ ExeLoaded [catFileGcc.file, libcF, ldF] [b0, lb0, ldb0] ifn0 false res0 cfs0.m.memory ∧
    Placed catFileGcc b0 lb0 gate0 ∧
    AtStart catFileGcc (world catFileGcc cfS cfW b0 lb0 gate0 (!cfW.stdoutFull) cfArgs cfs0.m.core.fsBase) cfW
      b0 cfs0 :=
  ⟨⟨rfl, rfl, by decide⟩, hlibcF, hldF, rfl, cf_allocates, cf_loaded, cf_placed, cf_atStart⟩

/-- **`catFileGcc_verified` is about a real process**: from `cfs0`, every run of the world built on
`cfS` halts with `hi\n` on stdout, nothing on stderr, status 0. -/
theorem catFileGcc_s0 :
    Proc.MustQ (world catFileGcc cfS cfW b0 lb0 gate0 (!cfW.stdoutFull) cfArgs cfs0.m.core.fsBase)
      (Observed (catFileSpec cfW)) cfs0 :=
  catFileGcc_verified cfW ⟨rfl, rfl, by decide⟩ libcF ldF hlibcF hldF cfS rfl cf_allocates b0 lb0 ldb0 res0 gate0 ifn0
    cfArgs cfs0 cf_loaded cf_placed cf_atStart

/-! ## `main`'s entry is possible: a memory meeting `AtMain` -/

/-- The arena's three streams are the library's: readable, not writable by the program. -/
def cfPermR : Permissions := ⟨true, false, false⟩

/-- The stdio state at `main`: `stdin` (empty), `stdout` and `stderr` in the first three arena
slots (`slotRep`'s encoding, read-only), and the COPY-relocated `stdout` variable at
`b0 + 0x4010` holding `stdout`'s `FILE` pointer. -/
def cfTm : Memory :=
  ⟨[⟨Streams.Total.A0, 3 * Streams.Total.S0, cfPermR⟩, ⟨b0.toNat + 0x4010, 8, permRW⟩],
    Memory.install (Memory.install (Memory.install (Memory.install ∅ Streams.Total.A0
      (Streams.Total.enc (stdinSt cfW))) (Streams.Total.A0 + Streams.Total.S0) (Streams.Total.enc (outSt 1)))
      (Streams.Total.A0 + 2 * Streams.Total.S0) (Streams.Total.enc (outSt 2)))
      (b0.toNat + 0x4010) (Silmaril.Machine.LittleEndian.encodeWords [cfE.stdoutF])⟩

/-- A state entering `main` with `cfTm`. -/
def cfTs : PState := sOf cfTm catFileGcc.layout.main []

theorem cf_permits {base size : Nat} {p : Permissions} {acc : Access} {a : Nat}
    (hr : (⟨base, size, p⟩ : Region) ∈ cfTm.regions)
    (h1 : base ≤ a) (h2 : a < base + size) (hp : p.allows acc = true) :
    cfTm.permits acc a = true := by
  unfold Memory.permits
  rw [List.any_eq_true]
  exact ⟨_, hr, by simp [Silmaril.Process.Region.Contains, h1, h2, hp]⟩

theorem cfTm_read {a : Nat} {l : List Byte} {base size : Nat} {p : Permissions}
    (hr : (⟨base, size, p⟩ : Region) ∈ cfTm.regions) (hp : p.allows .read = true)
    (h1 : base ≤ a) (h2 : a + l.length ≤ base + size) (hw : a + l.length < 2 ^ 64)
    (hb : ∀ k (hk : k < l.length), cfTm.bytes.get? (a + k) = some (l[k]'hk)) :
    cfTm.readBytes a l.length = some l := by
  have := readWith_of_points (mem := cfTm) (acc := .read) (l := l) (a := a) (by omega) (by omega)
    (fun k hk => ⟨cf_permits hr (by omega) (by omega) hp, hb k hk⟩)
  simpa [Memory.readBytes] using this

/-- The arena's slots are not writable in `cfTm`. -/
theorem cfTm_nw {a : Nat} (h1 : Streams.Total.A0 ≤ a) (h2 : a < Streams.Total.A0 + 3 * Streams.Total.S0) :
    cfTm.permits .write a = false := by
  unfold Memory.permits
  rw [List.any_eq_false]
  intro r hr hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hc1, hc2⟩, hw⟩ := hc
  simp only [cfTm, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp [cfPermR, Silmaril.Process.Permissions.allows] at hw
  · simp only [b0_toNat] at hc1 hc2; simp only [Streams.Total.A0, Streams.Total.S0] at h1 h2; omega

theorem cf_enc_len (st : Streams.St) (h : st.rd = []) : (Streams.Total.enc st).length = 64 := by
  rw [Streams.Total.enc_length, h]; rfl

/-- A stream `st` (nothing unread) of `slotRep` in slot `k < 3`, from its bytes in `cfTm`. -/
theorem cfTm_file {k : Nat} (hk : k < 3) {st : Streams.St} (hv : Streams.Total.Valid st) (hrd : st.rd = [])
    (hb : ∀ j (hj : j < (Streams.Total.enc st).length),
      cfTm.bytes.get? (Streams.Total.A0 + k * Streams.Total.S0 + j) = some ((Streams.Total.enc st)[j]'hj)) :
    Streams.Total.fileR cfTm (BitVec.ofNat 64 (Streams.Total.A0 + k * Streams.Total.S0)) st := by
  have hA : (BitVec.ofNat 64 (Streams.Total.A0 + k * Streams.Total.S0)).toNat =
      Streams.Total.A0 + k * Streams.Total.S0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; unfold Streams.Total.A0 Streams.Total.S0; omega
  have hl := cf_enc_len st hrd
  refine ⟨⟨k, by unfold Streams.Total.KS; omega, hA⟩, hv, ?_, fun j hj => ?_⟩
  · rw [hA, hrd, show 64 + ([] : List Byte).length = (Streams.Total.enc st).length by rw [hl]; rfl]
    exact cfTm_read (base := Streams.Total.A0) (size := 3 * Streams.Total.S0) (p := cfPermR) (by simp [cfTm]) rfl
      (by simp) (by rw [hl]; unfold Streams.Total.A0 Streams.Total.S0; omega)
      (by rw [hl]; unfold Streams.Total.A0 Streams.Total.S0; omega) hb
  · rw [hA]
    rw [hrd] at hj
    exact cfTm_nw (by omega) (by simp at hj; unfold Streams.Total.A0 Streams.Total.S0; omega)

set_option maxRecDepth 100000 in
/-- **`World.atMain` is satisfiable** for the concrete world: `cfTs` meets `AtMain` (the three
streams in `slotRep`'s slots, the COPY-relocated `stdout` variable, `errno` and the streams below
the stack). -/
theorem cfAtMain_sat : AtMain catFileGcc cfS b0 lb0 cfW cfTs := by
  have hb0 : b0.toNat + 0x4010 + 8 < Streams.Total.A0 ∨ Streams.Total.A0 + 3 * Streams.Total.S0 ≤ b0.toNat + 0x4010 := by
    rw [b0_toNat]; unfold Streams.Total.A0 Streams.Total.S0; omega
  have hsl : ∀ k < 3, ∀ j < 64, Streams.Total.A0 + k * Streams.Total.S0 + j < b0.toNat + 0x4010 := by
    intro k hk j hj; rw [b0_toNat]; unfold Streams.Total.A0 Streams.Total.S0; omega
  refine ⟨?_, ⟨?_, rfl⟩, ?_, ?_, ?_, ?_⟩
  · -- stdin, slot 0
    have := cfTm_file (k := 0) (by decide) (st := stdinSt cfW) ⟨rfl, by decide, by decide⟩ rfl (fun j hj => by
      rw [cf_enc_len _ rfl] at hj
      unfold cfTm; dsimp only
      rw [Memory.install_outside _ _ _ _ (Or.inl (by have := hsl 0 (by decide) j hj; omega)),
        Memory.install_outside _ _ _ _ (Or.inl (by unfold Streams.Total.A0 Streams.Total.S0; omega)),
        Memory.install_outside _ _ _ _ (Or.inl (by unfold Streams.Total.A0 Streams.Total.S0; omega)),
        show Streams.Total.A0 + 0 * Streams.Total.S0 + j = Streams.Total.A0 + j by omega,
        Memory.install_get _ _ _ _ (by rw [cf_enc_len _ rfl]; exact hj)])
    exact this
  · -- stdout, slot 1
    exact cfTm_file (k := 1) (by decide) (st := outSt 1) ⟨rfl, by decide, by decide⟩ rfl (fun j hj => by
      rw [cf_enc_len _ rfl] at hj
      unfold cfTm; dsimp only
      rw [Memory.install_outside _ _ _ _ (Or.inl (by have := hsl 1 (by decide) j hj; omega)),
        Memory.install_outside _ _ _ _ (Or.inl (by unfold Streams.Total.A0 Streams.Total.S0; omega)),
        show Streams.Total.A0 + 1 * Streams.Total.S0 + j = (Streams.Total.A0 + Streams.Total.S0) + j by omega,
        Memory.install_get _ _ _ _ (by rw [cf_enc_len _ rfl]; exact hj)])
  · -- stderr, slot 2
    exact cfTm_file (k := 2) (by decide) (st := outSt 2) ⟨rfl, by decide, by decide⟩ rfl (fun j hj => by
      rw [cf_enc_len _ rfl] at hj
      unfold cfTm; dsimp only
      rw [Memory.install_outside _ _ _ _ (Or.inl (by have := hsl 2 (by decide) j hj; omega)),
        show Streams.Total.A0 + 2 * Streams.Total.S0 + j = (Streams.Total.A0 + 2 * Streams.Total.S0) + j by omega,
        Memory.install_get _ _ _ _ (by rw [cf_enc_len _ rfl]; exact hj)])
  · -- the COPY-relocated `stdout`
    intro v hv
    have : catFileGcc.vars = [⟨nm "stdout", 0x4010, 0x0, true⟩] := rfl
    rw [this, List.mem_singleton] at hv
    subst hv
    simp only [Var.addr, ↓reduceIte]
    rw [ite_eq_right_of_eq_false _ _ (by decide)]
    have ea : (b0 + BitVec.ofNat 64 0x4010).toNat = b0.toNat + 0x4010 := by rw [b0_toNat]; rfl
    refine Proc.loadN_of_enc ?_
    rw [ea]
    have := cfTm_read (a := b0.toNat + 0x4010) (l := Silmaril.Machine.LittleEndian.encodeWords [cfE.stdoutF])
      (base := b0.toNat + 0x4010) (size := 8) (p := permRW) (by simp [cfTm]) rfl (le_refl _)
      (by simp) (by simp; rw [b0_toNat]; omega) (fun k hk => by
        unfold cfTm; dsimp only
        rw [Memory.install_get _ _ _ _ hk])
    rw [Silmaril.X86.length_encodeWords_singleton] at this
    exact this
  · show Streams.Total.A0 + Streams.Total.K0 * Streams.Total.S0 + 0x100000 ≤ sp0.toNat
    rw [sp0_toNat]; decide
  · show (0x1000#64 : Word).toNat + 4 ≤ Streams.Total.A0 + Streams.Total.K0 * Streams.Total.S0
    decide

end Silmaril.Elf.Link.Dyn.Program.Examples
