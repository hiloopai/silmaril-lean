module

public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello
public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Basic

/-! # Hello: the premises of `Verified` are satisfiable

A concrete process for `hello-gcc`: the executable at `b0` with exactly the loader relation's
image (`NonVacuous.memOf`), `libc.so.6`/`ld.so` holding the pinned chunks and zeros elsewhere,
a stack with `argc = 1` and `argv[0]` the empty string, the thread-control block with guard 0.
`helloGcc_premises`: it meets every premise of `helloGcc_verified` (chunks, loader relation,
placement, initial state, a stdio environment reading the world's file system), so the theorem
is about at least one process, and `helloGcc_s0` is its conclusion for that process. (An actual
*run* additionally needs a stream representation meeting `World.atMain`, such as B's `slotRep`;
`noStreams` here has no streams, which the premises allow.) -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc (PState Keeps CStr StackRoom)
open Silmaril.Elf.Link.Dyn.Small.NonVacuous

/-- A stream representation with no streams (enough for the premises). -/
def noStreams : Streams.StreamRep where
  file _ _ _ := False
  foot _ _ _ := False
  priv _ _ := False
  foot_priv := fun _ _ _ _ h => h.elim
  lo := 0
  foot_lo := fun _ _ _ _ h => h.elim
  priv_lo := fun _ _ h => h.elim
  priv_local := fun _ _ _ => rfl
  priv_keep := fun _ _ _ => rfl
  local_ := fun _ _ _ _ _ h => h.elim
  flags := fun _ _ _ h => h.elim
  flags1 := fun _ _ _ h => h.elim
  ptrs := fun _ _ _ h => h.elim
  putc := fun _ _ _ _ _ _ h => h.elim

/-- The world: `argv = [""]`, an empty file system, empty stdin. -/
def w0 : Program.World := { argv := [[]], fs := fun _ => .openErr .ENOENT }

/-- The library's environment: no streams, an empty file system, no resources. -/
def noStreamsEnv : Streams.Env where
  S := noStreams
  stdoutF := 0
  stderrF := 0
  fs := fun _ => .openErr .ENOENT
  optindA := 0
  maxAllocs := 0
  maxHeap := 0
  maxOpen := 0
  maxFile := 0

def S0 : Std := { E := noStreamsEnv, stdinF := 0 }

def libcF : Blob := blobOf libc.chunks
def ldF : Blob := blobOf ld.chunks

set_option maxRecDepth 100000 in
theorem hlibcF : ChunksOf libcF libc.chunks := by unfold ChunksOf; decide +kernel
set_option maxRecDepth 100000 in
theorem hldF : ChunksOf ldF ld.chunks := by unfold ChunksOf; decide +kernel

def helloT : List (Nat × Option Word) := tableOf helloGcc.slots
set_option maxRecDepth 100000 in
theorem hello_T : helloGcc.slots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some helloT := by decide +kernel
set_option maxRecDepth 100000 in
theorem hello_tab : tableOk helloGcc.file helloGcc.info helloT helloGcc.layout.size = true := by
  decide +kernel

/-- The memory: the image, stack (with `argc`, `argv`) and TCB of `memOf`. -/
abbrev mem0 : Memory := memOf helloGcc.file helloGcc.info helloT helloGcc.layout.size

def s0 : PState := sOf mem0 helloGcc.layout.start (stdinBytes w0)

/-- The argument area: the `argv` vector and the string. -/
def args0 (a : Nat) : Prop := sp0.toNat + 8 ≤ a ∧ a < sp0.toNat + 24

set_option maxRecDepth 100000 in
theorem tab_bound {f : Blob} {i : Elf.DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (h : tableOk f i T n = true) {ph : Elf.Phdr} (hph : ph ∈ i.phs) (hk : ph.kind = 1) :
    ph.vaddr + ph.memsz ≤ n := by
  have hl : ph ∈ loadsOf i := List.mem_filter.mpr ⟨hph, by simp [hk]⟩
  have := List.all_eq_true.mp h ph hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

set_option maxRecDepth 100000 in
theorem hello_info : finfo helloGcc.file = some helloGcc.info := by decide +kernel

set_option maxRecDepth 100000 in
theorem hello_slots : slots [helloGcc.file, libcF, ldF] false helloGcc.file helloGcc.info = some helloGcc.slots := by
  have F := Bin.facts helloGcc_ok
  have hc := libc_ok
  have hl := ld_ok
  simp only [LibPin.ok, Bool.and_eq_true, beq_iff_eq] at hc hl
  have := slots_of_known (ks := [⟨helloGcc.file, helloGcc.info, Hello.exeFacts helloGcc.refs⟩,
    ⟨libcF, libc.info, libc.facts⟩, ⟨ldF, ld.info, ld.facts⟩]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact Hello.exeKnown_ok F.info F.refs
      · exact ⟨run_sparse hlibcF hc.1, fun e he => Glibc.facts_of hc.2 hlibcF e he⟩
      · exact ⟨run_sparse hldF hl.1, fun e he => Glibc.facts_of hl.2 hldF e he⟩) F.slotsK
  exact this

set_option maxRecDepth 100000 in
theorem hello_img : ImageOk ⟨helloGcc.file, b0⟩ helloGcc.info helloT mem0 := by
  have himg := imageOk_of_table (by decide) hello_tab
  have hs : helloGcc.layout.size = 0x4018 := by decide
  intro ph hph hk v h1 h2
  obtain ⟨hw, hr, hx, hwr, e, he, hs', hv⟩ := himg ph hph hk v h1 h2
  have hb := tab_bound hello_tab hph hk
  have hfar : (b0 + BitVec.ofNat 64 v).toNat < sp0.toNat + 8 := by
    rw [addr_toNat (by rw [b0_toNat]; omega), b0_toNat, sp0_toNat]; omega
  exact ⟨hw, hr, hx, hwr, e, he, hs', hv⟩

set_option maxRecDepth 100000 in
theorem hello_loaded : ExeLoaded [helloGcc.file, libcF, ldF] [b0, lb0, ldb0] ifn0 false res0 mem0 :=
  ⟨_, _, _, _, _, rfl, rfl, hello_info, fun h => absurd h (by decide), hello_slots, hello_T, hello_img⟩

set_option maxRecDepth 100000 in
theorem hello_placed : Placed helloGcc b0 lb0 gate0 := by
  constructor <;> (try unfold Crt.Img) <;> decide +kernel

/-- The process world of the concrete process. -/
abbrev W0 : Proc.World := world helloGcc S0 w0 b0 lb0 gate0 (!w0.stdoutFull) args0 fs0

set_option maxRecDepth 100000 in
theorem hello_atStart : AtStart helloGcc W0 w0 b0 s0 := by
  have hn : helloGcc.layout.size < 2 ^ 32 := by decide
  have hsz : helloGcc.layout.size = 0x4018 := by decide
  have hsp : s0.m.core.read .rsp = sp0 := rfl
  refine ⟨rfl, rfl, by rw [hsp, sp0_toNat], ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hsp, sp0_toNat]; decide, by rw [hsp, sp0_toNat]; decide, fun a h1 h2 => ?_⟩
    rw [hsp] at h1 h2
    have h3 : a < sp0.toNat + 4096 := by rw [sp0_toNat] at h2 ⊢; omega
    refine ⟨by exact stack_permits (Or.inl rfl) h1 h3,
      by exact stack_permits (Or.inr rfl) h1 h3, ?_⟩
    rintro (h | h | h)
    · simp only [Proc.World.InImage, W0, world, world0, hsz, b0_toNat] at h; rw [sp0_toNat] at h1; omega
    · simp only [W0, world, world0, args0] at h; omega
    · simp only [W0, world, world0, libWords] at h
      rcases h with ⟨v, hv, -⟩ | h
      · simp [show helloGcc.vars = [] from rfl] at hv
      · have : (fs0 + 0x28#64).toNat = fs0.toNat + 0x28 := rfl
        rw [this, fs0_toNat] at h; rw [sp0_toNat] at h1 h2; omega
  · rw [hsp]
    show mem0.readBytes sp0.toNat 8 = _
    have := readWith_of_points (mem := memOf helloGcc.file helloGcc.info helloT helloGcc.layout.size)
      (acc := .read) (l := Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 1]) (a := sp0.toNat)
      (by simp [sp0_toNat]) (by simp [sp0_toNat]) (fun k hk => by
        simp only [Silmaril.X86.length_encodeWords_singleton] at hk
        refine ⟨stack_permits (Or.inl rfl) (by rw [sp0_toNat]; omega) (by rw [sp0_toNat]; omega), ?_⟩
        have := stack_get (f := helloGcc.file) (i := helloGcc.info) (T := helloT) hn (k := 4096 + k) (by omega)
        rw [show sp0.toNat - 4096 + (4096 + k) = sp0.toNat + k by rw [sp0_toNat]; omega] at this
        rw [this, stack0_get?]
        simp only [stackByte]
        have h1 : Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 1] =
            [1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by decide
        simp only [h1]
        interval_cases k <;> rfl)
    simpa [Memory.readBytes, w0] using this
  · intro i hi
    have hi0 : i = 0 := by simp [w0] at hi; omega
    subst hi0
    have ea : (s0.m.core.read .rsp + 8#64 + BitVec.ofNat 64 (8 * 0)).toNat = sp0.toNat + 8 := by
      rw [hsp, sp0_toNat]; rfl
    have ep : (sp0 + 16#64).toNat = sp0.toNat + 16 := by rw [sp0_toNat]; rfl
    refine ⟨sp0 + 16#64, Proc.loadN_of_enc ?_, ⟨by simp [w0, Streams.ofSpec], ?_⟩,
      fun k hk => ?_, fun j hj => ?_⟩
    · rw [ea]
      have := readWith_of_points (mem := mem0) (acc := .read)
        (l := Silmaril.Machine.LittleEndian.encodeWords [sp0 + 16#64]) (a := sp0.toNat + 8)
        (by simp [sp0_toNat]) (by simp [sp0_toNat]) (fun k hk => by
          simp only [Silmaril.X86.length_encodeWords_singleton] at hk
          refine ⟨stack_permits (Or.inl rfl) (by rw [sp0_toNat]; omega) (by rw [sp0_toNat]; omega), ?_⟩
          have := stack_get (f := helloGcc.file) (i := helloGcc.info) (T := helloT) hn (k := 4104 + k) (by omega)
          rw [show sp0.toNat - 4096 + (4104 + k) = sp0.toNat + 8 + k by rw [sp0_toNat]; omega] at this
          rw [this, stack0_get?]
          interval_cases k <;> decide +revert)
      show mem0.readBytes _ _ = _
      simpa [Memory.readBytes] using this
    · show mem0.readBytes (sp0 + 16#64).toNat ((Streams.ofSpec ([] : List UInt8)).length + 1) =
        some (Streams.ofSpec ([] : List UInt8) ++ [0])
      rw [ep]
      have := readWith_of_points (mem := memOf helloGcc.file helloGcc.info helloT helloGcc.layout.size)
        (acc := .read) (l := [0#8]) (a := sp0.toNat + 16) (by simp [sp0_toNat]) (by simp [sp0_toNat])
        (fun k hk => by
          simp only [List.length_singleton] at hk
          refine ⟨stack_permits (Or.inl rfl) (by rw [sp0_toNat]; omega) (by rw [sp0_toNat]; omega), ?_⟩
          have := stack_get (f := helloGcc.file) (i := helloGcc.info) (T := helloT) hn (k := 4112 + k)
            (by omega)
          rw [show sp0.toNat - 4096 + (4112 + k) = sp0.toNat + 16 + k by rw [sp0_toNat]; omega] at this
          rw [this, stack0_get?]
          interval_cases k; simp [stackByte])
      simpa [Memory.readBytes, Streams.ofSpec] using this
    · show args0 _; simp only [args0]; rw [ea]; omega
    · show args0 _; simp only [args0]; rw [ep]; simp [w0] at hj; omega
  · show ∃ g, loadN mem0 (fs0 + 40#64) 8 = some g
    exact ⟨0#64, guard0 hn⟩

set_option maxRecDepth 100000 in
/-- **The premises of `helloGcc_verified` hold of a concrete process.** -/
theorem helloGcc_premises :
    Tier.reliable w0 ∧ ChunksOf libcF libc.chunks ∧ ChunksOf ldF ld.chunks ∧ S0.E.fs = w0.fs ∧
    ExeLoaded [helloGcc.file, libcF, ldF] [b0, lb0, ldb0] ifn0 false res0 s0.m.memory ∧
    Placed helloGcc b0 lb0 gate0 ∧
    AtStart helloGcc (world helloGcc S0 w0 b0 lb0 gate0 (!w0.stdoutFull) args0 s0.m.core.fsBase) w0 b0 s0 :=
  ⟨rfl, hlibcF, hldF, rfl, hello_loaded, hello_placed, hello_atStart⟩

/-- **`helloGcc_verified` is about a real process**: from the concrete start state `s0`, every run
of the world built on `S0` halts with `hello, world\n` on stdout, nothing on stderr, status 0. -/
theorem helloGcc_s0 :
    Proc.MustQ (world helloGcc S0 w0 b0 lb0 gate0 (!w0.stdoutFull) args0 s0.m.core.fsBase)
      (Observed (helloSpec w0)) s0 :=
  helloGcc_verified w0 rfl libcF ldF hlibcF hldF S0 rfl trivial b0 lb0 ldb0 res0 gate0 ifn0 args0 s0
    hello_loaded hello_placed hello_atStart

end Silmaril.Elf.Link.Dyn.Program.Examples
