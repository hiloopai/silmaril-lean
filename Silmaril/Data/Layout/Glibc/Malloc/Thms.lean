module

public import Silmaril.Data.Layout.Glibc.Malloc.Defs
public import Silmaril.Data.Layout.Render.Defs
public import Silmaril.Data.Layout.Bits.Thms
public import Silmaril.Data.Layout.Thms
public import Silmaril.Data.Layout.Bytes.Thms

/-!
# glibc 2.39 malloc layouts, checked against DWARF

The DWARF of Ubuntu's `libc6` 2.39-0ubuntu8.9 (`libc6-dbg` separate debug files for the amd64,
arm64, riscv64 and i386 `libc.so.6`; `gdb ptype` and `ptype /o`)
gives, per structure, every member's offset and size and the total size. The amd64, arm64 and
riscv64 dumps are byte-identical.

* `dwarfLp64.*`, `dwarfI386.*`: those tables, transcribed.
* `*_x86_64`, `*_aapcs64`, `*_rv64`: the layouts computed under `sysvX86_64`, `aapcs64` and
  `rv64Lp64` have exactly the DWARF tables and sizes (the last two by `declLayout_aapcs64`,
  `declLayout_rv64Lp64`: AAPCS64 and RISC-V LP64 lay out every declaration as x86-64).
* `*_i386`: the same under `i386Ilp32` (with `NFASTBINS` = 11).
* `ptype_*`: the declarations render exactly as `gdb ptype` prints the compiled structs.
* `Lp64.*`: the concrete layouts (`DeclLayout` values) with their well-formedness, for use as
  the per-version layout record of the allocator models; `Lp64.allocCompose_offsets` checks
  them against hand-written offsets of an allocator model.
* `chunkSizeSpec`: well-formed; `chunksize_of_valid` and the flag readers agree with it.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Glibc.Malloc

/-! `dwarfLp64`: `(member, offset, size)` and total size, from `gdb ptype /o` of the amd64,
arm64 and riscv64 debug files (identical). -/
namespace dwarfLp64
def Chunk : List (String × Nat × Nat) :=
  [("mchunk_prev_size", 0, 8),
    ("mchunk_size", 8, 8),
    ("fd", 16, 8),
    ("bk", 24, 8),
    ("fd_nextsize", 32, 8),
    ("bk_nextsize", 40, 8)]
def ChunkSize : Nat := 48
def State : List (String × Nat × Nat) :=
  [("mutex", 0, 4),
    ("flags", 4, 4),
    ("have_fastchunks", 8, 4),
    ("fastbinsY", 16, 80),
    ("top", 96, 8),
    ("last_remainder", 104, 8),
    ("bins", 112, 2032),
    ("binmap", 2144, 16),
    ("next", 2160, 8),
    ("next_free", 2168, 8),
    ("attached_threads", 2176, 8),
    ("system_mem", 2184, 8),
    ("max_system_mem", 2192, 8)]
def StateSize : Nat := 2200
def Par : List (String × Nat × Nat) :=
  [("trim_threshold", 0, 8),
    ("top_pad", 8, 8),
    ("mmap_threshold", 16, 8),
    ("arena_test", 24, 8),
    ("arena_max", 32, 8),
    ("thp_pagesize", 40, 8),
    ("hp_pagesize", 48, 8),
    ("hp_flags", 56, 4),
    ("n_mmaps", 60, 4),
    ("n_mmaps_max", 64, 4),
    ("max_n_mmaps", 68, 4),
    ("no_dyn_threshold", 72, 4),
    ("mmapped_mem", 80, 8),
    ("max_mmapped_mem", 88, 8),
    ("sbrk_base", 96, 8),
    ("tcache_bins", 104, 8),
    ("tcache_max_bytes", 112, 8),
    ("tcache_count", 120, 8),
    ("tcache_unsorted_limit", 128, 8)]
def ParSize : Nat := 136
def TcacheEntry : List (String × Nat × Nat) :=
  [("next", 0, 8),
    ("key", 8, 8)]
def TcacheEntrySize : Nat := 16
def Tcache : List (String × Nat × Nat) :=
  [("counts", 0, 128),
    ("entries", 128, 512)]
def TcacheSize : Nat := 640
end dwarfLp64

/-! `dwarfI386`: the same for the i386 debug file. -/
namespace dwarfI386
def Chunk : List (String × Nat × Nat) :=
  [("mchunk_prev_size", 0, 4),
    ("mchunk_size", 4, 4),
    ("fd", 8, 4),
    ("bk", 12, 4),
    ("fd_nextsize", 16, 4),
    ("bk_nextsize", 20, 4)]
def ChunkSize : Nat := 24
def State : List (String × Nat × Nat) :=
  [("mutex", 0, 4),
    ("flags", 4, 4),
    ("have_fastchunks", 8, 4),
    ("fastbinsY", 12, 44),
    ("top", 56, 4),
    ("last_remainder", 60, 4),
    ("bins", 64, 1016),
    ("binmap", 1080, 16),
    ("next", 1096, 4),
    ("next_free", 1100, 4),
    ("attached_threads", 1104, 4),
    ("system_mem", 1108, 4),
    ("max_system_mem", 1112, 4)]
def StateSize : Nat := 1116
def Par : List (String × Nat × Nat) :=
  [("trim_threshold", 0, 4),
    ("top_pad", 4, 4),
    ("mmap_threshold", 8, 4),
    ("arena_test", 12, 4),
    ("arena_max", 16, 4),
    ("thp_pagesize", 20, 4),
    ("hp_pagesize", 24, 4),
    ("hp_flags", 28, 4),
    ("n_mmaps", 32, 4),
    ("n_mmaps_max", 36, 4),
    ("max_n_mmaps", 40, 4),
    ("no_dyn_threshold", 44, 4),
    ("mmapped_mem", 48, 4),
    ("max_mmapped_mem", 52, 4),
    ("sbrk_base", 56, 4),
    ("tcache_bins", 60, 4),
    ("tcache_max_bytes", 64, 4),
    ("tcache_count", 68, 4),
    ("tcache_unsorted_limit", 72, 4)]
def ParSize : Nat := 76
def TcacheEntry : List (String × Nat × Nat) :=
  [("next", 0, 4),
    ("key", 4, 4)]
def TcacheEntrySize : Nat := 8
def Tcache : List (String × Nat × Nat) :=
  [("counts", 0, 128),
    ("entries", 128, 256)]
def TcacheSize : Nat := 384
end dwarfI386

theorem nfastbins_lp64 : nfastbins sysvX86_64 = 10 := by decide
theorem nfastbins_i386 : nfastbins i386Ilp32 = 11 := by decide

/-! ## Computed layouts are the DWARF layouts -/

/-- The layout of an `Except` result: its total size and member table. -/
def summary (r : Except String DeclLayout) : Option (Nat × List (String × Nat × Nat)) :=
  r.toOption.map fun L => (L.shape.size, L.table)

theorem chunkLayout_x86_64 : summary (chunkLayout sysvX86_64) = some (dwarfLp64.ChunkSize, dwarfLp64.Chunk) := by
  decide
theorem chunkLayout_i386 : summary (chunkLayout i386Ilp32) = some (dwarfI386.ChunkSize, dwarfI386.Chunk) := by
  decide

theorem stateLayout_x86_64 : summary (stateLayout sysvX86_64) = some (dwarfLp64.StateSize, dwarfLp64.State) := by
  decide
theorem stateLayout_i386 : summary (stateLayout i386Ilp32) = some (dwarfI386.StateSize, dwarfI386.State) := by
  decide

theorem parLayout_x86_64 : summary (parLayout sysvX86_64) = some (dwarfLp64.ParSize, dwarfLp64.Par) := by
  decide
theorem parLayout_i386 : summary (parLayout i386Ilp32) = some (dwarfI386.ParSize, dwarfI386.Par) := by
  decide

theorem tcacheEntryLayout_x86_64 : summary (tcacheEntryLayout sysvX86_64) = some (dwarfLp64.TcacheEntrySize, dwarfLp64.TcacheEntry) := by
  decide
theorem tcacheEntryLayout_i386 : summary (tcacheEntryLayout i386Ilp32) = some (dwarfI386.TcacheEntrySize, dwarfI386.TcacheEntry) := by
  decide

theorem tcacheLayout_x86_64 : summary (tcacheLayout sysvX86_64) = some (dwarfLp64.TcacheSize, dwarfLp64.Tcache) := by
  decide
theorem tcacheLayout_i386 : summary (tcacheLayout i386Ilp32) = some (dwarfI386.TcacheSize, dwarfI386.Tcache) := by
  decide

theorem env_aapcs64 : env aapcs64 = env sysvX86_64 := rfl
theorem env_rv64 : env rv64Lp64 = env sysvX86_64 := rfl

theorem chunkLayout_aapcs64 : chunkLayout aapcs64 = chunkLayout sysvX86_64 :=
  congrFun (declLayout_aapcs64 (env sysvX86_64)) _
theorem chunkLayout_rv64 : chunkLayout rv64Lp64 = chunkLayout sysvX86_64 :=
  congrFun (declLayout_rv64Lp64 (env sysvX86_64)) _

theorem stateLayout_aapcs64 : stateLayout aapcs64 = stateLayout sysvX86_64 :=
  congrFun (declLayout_aapcs64 (env sysvX86_64)) _
theorem stateLayout_rv64 : stateLayout rv64Lp64 = stateLayout sysvX86_64 :=
  congrFun (declLayout_rv64Lp64 (env sysvX86_64)) _

theorem parLayout_aapcs64 : parLayout aapcs64 = parLayout sysvX86_64 :=
  congrFun (declLayout_aapcs64 (env sysvX86_64)) _
theorem parLayout_rv64 : parLayout rv64Lp64 = parLayout sysvX86_64 :=
  congrFun (declLayout_rv64Lp64 (env sysvX86_64)) _

theorem tcacheEntryLayout_aapcs64 : tcacheEntryLayout aapcs64 = tcacheEntryLayout sysvX86_64 :=
  congrFun (declLayout_aapcs64 (env sysvX86_64)) _
theorem tcacheEntryLayout_rv64 : tcacheEntryLayout rv64Lp64 = tcacheEntryLayout sysvX86_64 :=
  congrFun (declLayout_rv64Lp64 (env sysvX86_64)) _

theorem tcacheLayout_aapcs64 : tcacheLayout aapcs64 = tcacheLayout sysvX86_64 :=
  congrFun (declLayout_aapcs64 (env sysvX86_64)) _
theorem tcacheLayout_rv64 : tcacheLayout rv64Lp64 = tcacheLayout sysvX86_64 :=
  congrFun (declLayout_rv64Lp64 (env sysvX86_64)) _

/-! ## As `gdb ptype` prints them -/

theorem ptype_Chunk : (mallocChunk).ptype =
    "type = struct malloc_chunk {\n    size_t mchunk_prev_size;\n    size_t mchunk_size;\n    struct malloc_chunk *fd;\n    struct malloc_chunk *bk;\n    struct malloc_chunk *fd_nextsize;\n    struct malloc_chunk *bk_nextsize;\n}" := by
  decide +kernel

theorem ptype_State : (mallocState 10).ptype =
    "type = struct malloc_state {\n    __libc_lock_t mutex;\n    int flags;\n    int have_fastchunks;\n    mfastbinptr fastbinsY[10];\n    mchunkptr top;\n    mchunkptr last_remainder;\n    mchunkptr bins[254];\n    unsigned int binmap[4];\n    struct malloc_state *next;\n    struct malloc_state *next_free;\n    size_t attached_threads;\n    size_t system_mem;\n    size_t max_system_mem;\n}" := by
  decide +kernel

theorem ptype_Par : (mallocPar).ptype =
    "type = struct malloc_par {\n    unsigned long trim_threshold;\n    size_t top_pad;\n    size_t mmap_threshold;\n    size_t arena_test;\n    size_t arena_max;\n    size_t thp_pagesize;\n    size_t hp_pagesize;\n    int hp_flags;\n    int n_mmaps;\n    int n_mmaps_max;\n    int max_n_mmaps;\n    int no_dyn_threshold;\n    size_t mmapped_mem;\n    size_t max_mmapped_mem;\n    char *sbrk_base;\n    size_t tcache_bins;\n    size_t tcache_max_bytes;\n    size_t tcache_count;\n    size_t tcache_unsorted_limit;\n}" := by
  decide +kernel

theorem ptype_TcacheEntry : (tcacheEntry).ptype =
    "type = struct tcache_entry {\n    struct tcache_entry *next;\n    uintptr_t key;\n}" := by
  decide +kernel

theorem ptype_Tcache : (tcachePerthread).ptype =
    "type = struct tcache_perthread_struct {\n    uint16_t counts[64];\n    tcache_entry *entries[64];\n}" := by
  decide +kernel

theorem ptype_State_i386 : (mallocState (nfastbins i386Ilp32)).ptype =
    "type = struct malloc_state {\n    __libc_lock_t mutex;\n    int flags;\n    int have_fastchunks;\n    mfastbinptr fastbinsY[11];\n    mchunkptr top;\n    mchunkptr last_remainder;\n    mchunkptr bins[254];\n    unsigned int binmap[4];\n    struct malloc_state *next;\n    struct malloc_state *next_free;\n    size_t attached_threads;\n    size_t system_mem;\n    size_t max_system_mem;\n}" := by
  decide +kernel

/-! ## Concrete LP64 layouts -/

/-- The layout of a successful result (an empty struct otherwise). -/
def unwrap : Except String DeclLayout → DeclLayout
  | .ok L => L
  | .error _ => ⟨.struct, "", ⟨0, 1⟩, []⟩

namespace Lp64

/-- `struct malloc_chunk` on x86-64, AArch64 and RISC-V 64. -/
def chunk : DeclLayout := unwrap (chunkLayout sysvX86_64)
/-- `struct malloc_state` (`main_arena`). -/
def state : DeclLayout := unwrap (stateLayout sysvX86_64)
/-- `struct malloc_par` (`mp_`). -/
def par : DeclLayout := unwrap (parLayout sysvX86_64)
/-- `struct tcache_entry`. -/
def tcacheEntry : DeclLayout := unwrap (tcacheEntryLayout sysvX86_64)
/-- `struct tcache_perthread_struct`. -/
def tcache : DeclLayout := unwrap (tcacheLayout sysvX86_64)

theorem chunk_eq : chunkLayout sysvX86_64 = .ok chunk := rfl
theorem state_eq : stateLayout sysvX86_64 = .ok state := rfl
theorem par_eq : parLayout sysvX86_64 = .ok par := rfl
theorem tcacheEntry_eq : tcacheEntryLayout sysvX86_64 = .ok tcacheEntry := rfl
theorem tcache_eq : tcacheLayout sysvX86_64 = .ok tcache := rfl

theorem chunk_wf : chunk.WF := declLayout_wf sysvX86_64_wf chunk_eq
theorem state_wf : state.WF := declLayout_wf sysvX86_64_wf state_eq
theorem par_wf : par.WF := declLayout_wf sysvX86_64_wf par_eq
theorem tcacheEntry_wf : tcacheEntry.WF := declLayout_wf sysvX86_64_wf tcacheEntry_eq
theorem tcache_wf : tcache.WF := declLayout_wf sysvX86_64_wf tcache_eq

/-- Offset of a member (0 if absent; every use below is checked). -/
def off (L : DeclLayout) (name : String) : Nat := (L.offsetOf? name).getD 0

/-- Hand-written x86-64 offsets of an allocator model (arena, `mp_` and tcache fields). -/
theorem allocCompose_offsets :
    ["mutex", "flags", "have_fastchunks", "fastbinsY", "top", "last_remainder", "bins", "binmap",
      "next", "next_free", "attached_threads", "system_mem", "max_system_mem"].map (off state) =
      [0x0, 0x4, 0x8, 0x10, 0x60, 0x68, 0x70, 0x860, 0x870, 0x878, 0x880, 0x888, 0x890] ∧
    state.shape.size = 0x898 ∧
    ["trim_threshold", "top_pad", "mmap_threshold", "arena_test", "arena_max", "thp_pagesize",
      "hp_pagesize", "hp_flags", "n_mmaps", "n_mmaps_max", "max_n_mmaps", "no_dyn_threshold",
      "mmapped_mem", "max_mmapped_mem", "sbrk_base", "tcache_bins", "tcache_max_bytes",
      "tcache_count", "tcache_unsorted_limit"].map (off par) =
      [0x0, 0x8, 0x10, 0x18, 0x20, 0x28, 0x30, 0x38, 0x3c, 0x40, 0x44, 0x48, 0x50, 0x58, 0x60,
        0x68, 0x70, 0x78, 0x80] ∧
    par.shape.size = 0x88 ∧
    ["counts", "entries"].map (off tcache) = [0, 0x80] ∧ tcache.shape.size = 0x280 ∧
    ["mchunk_size", "fd", "bk"].map (off chunk) = [8, 0x10, 0x18] := by
  decide

/-- `malloc_state` has exactly one padding run: the 4 bytes after `have_fastchunks`;
`malloc_par` the 4 bytes after `no_dyn_threshold`. -/
theorem padding : state.padding = [12, 13, 14, 15] ∧ par.padding = [76, 77, 78, 79] ∧
    chunk.padding = [] ∧ tcache.padding = [] := by
  decide +kernel

end Lp64

/-! ## The size field -/

theorem chunkSizeSpec_wf (dm : DataModel) (h : 1 ≤ sizeSz dm) : (chunkSizeSpec dm).WF := by
  refine ⟨?_, ?_⟩
  · intro it hit
    simp only [chunkSizeSpec, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl | rfl | rfl <;> simp only [chunkSizeSpec] <;> omega
  · simp [chunkSizeSpec, BitRange.Disjoint]

theorem get?_size16 (dm : DataModel) (v : Nat) :
    (chunkSizeSpec dm).get? "size16" v = some (BitRange.get ⟨4, 8 * sizeSz dm - 4⟩ v) := by
  simp [WordSpec.get?, WordSpec.item?, chunkSizeSpec]

/-- On a valid size word, `chunksize` is `size16 * 16`. -/
theorem chunksize_of_valid {dm : DataModel} (h : 1 ≤ sizeSz dm) {v : Nat}
    (hv : (chunkSizeSpec dm).Valid v) :
    chunksize v = BitRange.get ⟨4, 8 * sizeSz dm - 4⟩ v * 16 := by
  obtain ⟨hlt, hz⟩ := hv
  have h3 := hz ⟨"MALLOC_ALIGNMENT", ⟨3, 1⟩, .zero⟩ (by simp [chunkSizeSpec]) rfl
  simp only [BitRange.get, Nat.shiftRight_eq_div_pow] at h3 ⊢
  have hw : 2 ^ (8 * sizeSz dm) = 2 ^ (8 * sizeSz dm - 4) * 16 := by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]; congr 1; omega
  have hlt' : v / 2 ^ 4 < 2 ^ (8 * sizeSz dm - 4) := by
    rw [Nat.div_lt_iff_lt_mul (by decide), ← hw]; exact hlt
  rw [Nat.mod_eq_of_lt hlt']
  simp only [chunksize]
  have := Nat.div_add_mod v 16
  have := Nat.div_add_mod v 8
  have : v / 8 % 2 = 0 := by simpa using h3
  have : v / 8 = 2 * (v / 16) + v / 8 % 2 := by omega
  omega

theorem prevInuse_flag (dm : DataModel) (v : Nat) :
    (chunkSizeSpec dm).flag? "PREV_INUSE" v = some (prevInuse v) := by
  simp [WordSpec.flag?, WordSpec.get?, WordSpec.item?, chunkSizeSpec, BitRange.get, prevInuse]

theorem isMmapped_flag (dm : DataModel) (v : Nat) :
    (chunkSizeSpec dm).flag? "IS_MMAPPED" v = some (isMmapped v) := by
  simp [WordSpec.flag?, WordSpec.get?, WordSpec.item?, chunkSizeSpec, BitRange.get, isMmapped,
    Nat.shiftRight_eq_div_pow]

theorem nonMainArena_flag (dm : DataModel) (v : Nat) :
    (chunkSizeSpec dm).flag? "NON_MAIN_ARENA" v = some (nonMainArena v) := by
  simp [WordSpec.flag?, WordSpec.get?, WordSpec.item?, chunkSizeSpec, BitRange.get, nonMainArena,
    Nat.shiftRight_eq_div_pow]


/-! ## Using the lenses on a chunk -/

namespace Lp64

open DeclLayout

variable {M : Type} [ByteMem M]

/-- Writing `fd` of a chunk at `p` (in any byte memory: x86 process memory, Wasm memory)
keeps its size field. -/
theorem write_fd_keeps_size {m m' : M} {p : Nat} {bs : List Byte}
    (h : chunk.write? m p "fd" bs = some m') :
    chunk.read? m' p "mchunk_size" = chunk.read? m p "mchunk_size" :=
  read?_write?_other chunk_wf rfl (by decide) h

/-- Writing `top` of an arena keeps its bins, and the padding after `have_fastchunks`. -/
theorem write_top_keeps {m m' : M} {a : Nat} {bs : List Byte}
    (h : state.write? m a "top" bs = some m') :
    state.read? m' a "bins" = state.read? m a "bins" ∧
      ∀ k ∈ [12, 13, 14, 15], ByteMem.get? m' (a + k) = ByteMem.get? m (a + k) := by
  refine ⟨read?_write?_other state_wf rfl (by decide) h, fun k hk => ?_⟩
  simp only [write?, Option.bind_eq_some_iff] at h
  obtain ⟨f, hf, h⟩ := h
  split at h
  · cases h
    exact get?_writeField_pad (mem_of_field? hf).1
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl <;> decide +kernel) (by assumption)
  · cases h

/-- Setting `PREV_INUSE` keeps the chunk size. -/
theorem set_prevInuse_keeps_size {v v' : Nat}
    (h : (chunkSizeSpec sysvX86_64).set? "PREV_INUSE" v 1 = some v') :
    (chunkSizeSpec sysvX86_64).get? "size16" v' = (chunkSizeSpec sysvX86_64).get? "size16" v :=
  WordSpec.get?_set?_other (chunkSizeSpec_wf _ (by decide)) (by decide) h

end Lp64

end Silmaril.Data.Layout.Glibc.Malloc

/-! ## Designators -/

namespace Silmaril.Data.Layout.Glibc.Malloc.Lp64

/-- `offsetof (struct malloc_state, bins[253])` and `offsetof (struct tcache_perthread_struct,
entries[63])`; `resolve_wf` places every such element inside its structure. -/
theorem designators :
    ((resolve sysvX86_64 (env sysvX86_64) (.struct "malloc_state")
        [.field "bins", .index 253]).toOption.map (·.1),
      (resolve sysvX86_64 (env sysvX86_64) (.struct "tcache_perthread_struct")
        [.field "entries", .index 63]).toOption.map (·.1),
      (resolve sysvX86_64 (env sysvX86_64) (.struct "malloc_state")
        [.field "binmap", .index 3]).toOption.map (·.1)) =
      (some 2136, some 632, some 2156) := by
  decide +kernel

end Silmaril.Data.Layout.Glibc.Malloc.Lp64
