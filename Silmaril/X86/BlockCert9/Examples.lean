module

public import Silmaril.X86.BlockCert9.Thms

/-!
# A function lifted to Bir9, certified and proved on `Open9`: `ilog2_u32`

The C function

```c
int ilog2_u32(uint32_t x) { int r = -1; while (x) { x >>= 1; r++; } return r; }
```

compiled by gcc 13.3 at `-O2` for x86-64 is 22 bytes (gcc turns the loop into `bsr`):

```
+0x00  85 ff                     test %edi,%edi
+0x02  74 0c                     je   +0x10
+0x04  0f bd c7                  bsr  %edi,%eax          (an Ext9 form)
+0x07  c3                        ret
+0x08  0f 1f 84 00 00 00 00 00   nopl 0x0(%rax,%rax,1)   (padding, never run)
+0x10  b8 ff ff ff ff            mov  $0xffffffff,%eax
+0x15  c3                        ret
```

This module states the bytes and three Bir9 listings, lifts each listing to a Bir9 block
(`lifts_*`, `decide +kernel`), checks the listings against the bytes through
`Open9.decode` (`ilog_checked`, `decide +kernel`), proves each block VC over the **pure
Bir9 block** (`Code.run_bir`, then `bir9_simp`), and assembles them into a total System V
contract on `Open9.isa` (`ilog2_total`, `ilog2_contract`). The `bsr` block carries the
zero-source check `chk (nz d) rdi` of the lifter; the annotation `edi ≠ 0` discharges it.

The bytes are written out here; that they are the compiler's output is recorded, not
checked.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert9.Examples

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Bir9 (LInstr Block liftBlock)

set_option linter.unusedSimpArgs false

/-! ## C semantics and contract -/

/-- `ilog2_u32`: `-1` for `0`, `⌊log2 x⌋` otherwise (as an `int`). -/
def ilog2Spec (x : BitVec 32) : BitVec 32 :=
  if x = 0 then 0xffffffff#32 else BitVec.ofNat 32 (Nat.log2 x.toNat)

/-- The low 32 bits of a register. -/
def r32 (r : Reg) (m : MState) : BitVec 32 := (m.core.read r).setWidth 32

/-- The load address. -/
def ilogBase : Word := 0x401430

/-- The code, `[0x401430, 0x401446)`. -/
def ilogCode : List Byte :=
  [0x85, 0xff, 0x74, 0x0c, 0x0f, 0xbd, 0xc7, 0xc3, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
   0xb8, 0xff, 0xff, 0xff, 0xff, 0xc3]

/-- The contract: a leaf function, no memory written, `rax = ilog2_u32(edi)` zero-extended. -/
def ilogSpec : FnContract.Spec MState :=
  leafSpec ilogBase ilogCode 0 fun m t =>
    t.core.read .rax = (ilog2Spec (r32 .rdi m)).setWidth 64

/-! ## Listings and their Bir9 blocks -/

/-- `+0x0`: `test %edi,%edi; je +0x10`. -/
def L0 : List (LInstr × Nat) := [(.ext (.test .d (.reg .rdi) .rdi), 2), (.ext (.jcc8 .e 0x0c), 2)]

/-- `+0x4`: `bsr %edi,%eax; ret`. -/
def L4 : List (LInstr × Nat) := [(.n9 (.bsr .d .rax (.reg .rdi)), 3), (.ext .ret, 1)]

/-- `+0x10`: `mov $0xffffffff,%eax; ret`. -/
def L10 : List (LInstr × Nat) := [(.ext (.movI32 .rax 0xffffffff), 5), (.ext .ret, 1)]

/-- `v0 := e(test32 rdi rdi); rip := v0 ? rip + 0x10 : rip + 0x4`. -/
def I0 : Block :=
  { stmts := [.cond .e (.test 32 (.reg .rdi) (.reg .rdi))], regs := [],
    flags := .test 32 (.reg .rdi) (.reg .rdi),
    rip := .sel (.v 0) (.add .rip (.imm 0x10)) (.add .rip (.imm 0x4)) }

/-- `check edi ≠ 0; v0 := [rsp]; rax := bsr32 rdi; rsp := rsp + 8; rip := v0`. -/
def I4 : Block :=
  { stmts := [.chk (.nz .d) (.reg .rdi) (.imm 0) (.imm 0), .pop (.reg .rsp)],
    regs := [(.rax, .xop (.bsr .d) (.reg .rdi) (.imm 0) (.imm 0)),
      (.rsp, .add (.reg .rsp) (.imm 8))],
    flags := .xop .scan (.imm 0) (.imm 0) (.imm 0), rip := .v 0 }

/-- `v0 := [rsp]; rax := 0xffffffff; rsp := rsp + 8; rip := v0`. -/
def I10 : Block :=
  { stmts := [.pop (.reg .rsp)],
    regs := [(.rax, .imm 0xffffffff), (.rsp, .add (.reg .rsp) (.imm 8))],
    flags := .entry, rip := .v 0 }

theorem lifts0 : liftBlock L0 = some I0 := by decide +kernel
theorem lifts4 : liftBlock L4 = some I4 := by decide +kernel
theorem lifts10 : liftBlock L10 = some I10 := by decide +kernel

/-! ## The certificate -/

/-- Annotations: the entry; at `+0x4` a frame with `edi ≠ 0`; at `+0x10` one with `edi = 0`. -/
def ilogAnn : Nat → MState → MState → Prop
  | 0x0, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory
  | 0x4, m0, m => Frame m0 m ∧ m.core.read .rdi = m0.core.read .rdi ∧ r32 .rdi m0 ≠ 0
  | 0x10, m0, m => Frame m0 m ∧ r32 .rdi m0 = 0
  | _, _, _ => False

def ilogCert : FunCert9 where
  code := ilogCode
  base := ilogBase
  blocks := [⟨0x0, .bir L0⟩, ⟨0x4, .bir L4⟩, ⟨0x10, .bir L10⟩]
  ann := ilogAnn
  measure o _ _ := match o with
    | 0x0 => 1
    | _ => 0

/-- The listings are what `Open9.decode` reads in the code. -/
theorem ilog_checked : ilogCert.checked = true := by decide +kernel

/-- Negative: a listing with `bsf` for the `bsr` bytes is rejected. -/
theorem ilog_bsf_rejected :
    (Code.bir [(.n9 (.bsf .d .rax (.reg .rdi)), 3), (.ext .ret, 1)]).check ilogCode 4 = false := by
  decide +kernel

/-! ## Block VCs, over the Bir9 blocks -/

abbrev ilogQ : MState → MState → Prop := fun m0 t => ilogSpec.Result Open9.isa m0 t

theorem ilog_b0 : ilogCert.BlockVC ilogQ ⟨0x0, .bir L0⟩ := by
  intro m0 m ⟨hm, hab⟩ hrip _
  subst hm
  have hf := Frame.entry hab
  rw [Code.run_bir lifts0]
  by_cases hz : r32 .rdi m = 0
  · have hz' : BitVec.setWidth 32 (m.core.read .rdi) = 0#32 := hz
    bir9_simp [I0, eval_e_test, hz']
    apply FunCert9.next_of ⟨0x10, .bir L10⟩ (by simp [ilogCert])
    · bir9_close [hrip, ilogCert, hz', BitVec.add_assoc]
    · exact ⟨Frame.step hf rfl rfl (fun _ _ => rfl), hz⟩
    · simp [ilogCert]
  · have hz' : ¬ BitVec.setWidth 32 (m.core.read .rdi) = 0#32 := hz
    bir9_simp [I0, eval_e_test, hz']
    apply FunCert9.next_of ⟨0x4, .bir L4⟩ (by simp [ilogCert])
    · bir9_close [hrip, ilogCert, hz', BitVec.add_assoc]
    · exact ⟨Frame.step hf rfl rfl (fun _ _ => rfl), rfl, hz⟩
    · simp [ilogCert]

theorem ilog_b4 : ilogCert.BlockVC ilogQ ⟨0x4, .bir L4⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ _ _
  have h2' : ¬ BitVec.setWidth 32 (m0.core.read .rdi) = 0#32 := h2
  have h2s : ¬ BitVec.setWidth Silmaril.X86.Ext.Sz.d.bits (m.core.read .rdi) =
      0#Silmaril.X86.Ext.Sz.d.bits := by rw [h1]; exact h2'
  rw [Code.run_bir lifts4]
  bir9_simp [I4, h2s, hf.pop]
  refine .inl (Frame.result hf ?_ ?_ ?_ rfl ?_) <;>
    bir9_close [ilogSpec, leafSpec, r32, ilog2Spec, h1, h2', Ext9.bsrIndex_eq_log2 _ h2']

theorem ilog_b10 : ilogCert.BlockVC ilogQ ⟨0x10, .bir L10⟩ := by
  intro m0 m ⟨hf, h1⟩ _ _
  have h1' : BitVec.setWidth 32 (m0.core.read .rdi) = 0#32 := h1
  rw [Code.run_bir lifts10]
  bir9_simp [I10, hf.pop]
  refine .inl (Frame.result hf ?_ ?_ ?_ rfl ?_) <;>
    bir9_close [ilogSpec, leafSpec, r32, ilog2Spec, h1']

theorem ilog_vc : ilogCert.VC ilogQ := by
  simp only [FunCert9.VC, ilogCert, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl)
  exacts [ilog_b0, ilog_b4, ilog_b10]

/-! ## The contract -/

/-- **`ilog2_u32` is totally correct on `Open9`.** -/
theorem ilog2_total : ilogSpec.Total Open9.isa :=
  FunCert9.total ilogSpec (entry := ⟨0x0, .bir L0⟩) (by simp [ilogCert]) ilog_checked ilog_vc
    fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

/-- Its System V function contract. -/
def ilog2_contract : FnContract Open9.isa :=
  ilogCert.contract ilogSpec (entry := ⟨0x0, .bir L0⟩) (by simp [ilogCert]) ilog_checked ilog_vc
    fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

end Silmaril.X86.BlockCert9.Examples
