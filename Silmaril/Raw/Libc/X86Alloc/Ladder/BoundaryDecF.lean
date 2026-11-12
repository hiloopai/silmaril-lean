module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryDecM
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.Raw.Libc.X86Alloc.MemForms
public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryList
public import Silmaril.Raw.Libc.X86Alloc.Loop
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 08 (boundary tags) — the listing of `free`, decoded once -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Boundary

theorem d240 : Silmaril.X86.Ext.decode ((code.drop 240).take 3) =
    some (.test .q (.reg .rdi) .rdi, 3) := by
  decide +kernel
theorem d243 : Silmaril.X86.Ext.decode ((code.drop 243).take 6) =
    some (.jcc .e 0xb6, 6) := by
  decide +kernel
theorem d249 : Silmaril.X86.Ext.decode ((code.drop 249).take 4) =
    some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rdi 0xfffffff0), 4) := by
  decide +kernel
theorem d253 : Silmaril.X86.Ext.decode ((code.drop 253).take 3) =
    some (.mov .q (.reg .rdx) .rdi, 3) := by
  decide +kernel
theorem d256 : Silmaril.X86.Ext.decode ((code.drop 256).take 4) =
    some (.lea .q .rcx (Silmaril.X86.Sep.Insn.memAt .rdi 0xfffffff0), 4) := by
  decide +kernel
theorem d260 : Silmaril.X86.Ext.decode ((code.drop 260).take 7) =
    some (.aluI .q .sub (.reg .rdx) 0x4032d0, 7) := by
  decide +kernel
theorem d267 : Silmaril.X86.Ext.decode ((code.drop 267).take 3) =
    some (.mov .q (.reg .rsi) .rax, 3) := by
  decide +kernel
theorem d270 : Silmaril.X86.Ext.decode ((code.drop 270).take 4) =
    some (.shift .q .shr (.reg .rdx) (.imm 0x4), 4) := by
  decide +kernel
theorem d274 : Silmaril.X86.Ext.decode ((code.drop 274).take 4) =
    some (.shift .q .shr (.reg .rsi) (.imm 0x4), 4) := by
  decide +kernel
theorem d278 : Silmaril.X86.Ext.decode ((code.drop 278).take 3) =
    some (.alu .q .add (.reg .rsi) .rdx, 3) := by
  decide +kernel
theorem d281 : Silmaril.X86.Ext.decode ((code.drop 281).take 7) =
    some (.aluI .q .cmp (.reg .rsi) 0xff, 7) := by
  decide +kernel
theorem d288 : Silmaril.X86.Ext.decode ((code.drop 288).take 2) =
    some (.jcc8 .a 0x42, 2) := by
  decide +kernel
theorem d290 : Silmaril.X86.Ext.decode ((code.drop 290).take 7) =
    some (.cmpI8 (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0x4031c0)) 0x0, 7) := by
  decide +kernel
theorem d297 : Silmaril.X86.Ext.decode ((code.drop 297).take 2) =
    some (.jcc8 .e 0x39, 2) := by
  decide +kernel
theorem d299 : Silmaril.X86.Ext.decode ((code.drop 299).take 3) =
    some (.mov .q (.reg .r10) .rsi, 3) := by
  decide +kernel
theorem d302 : Silmaril.X86.Ext.decode ((code.drop 302).take 4) =
    some (.shift .q .shl (.reg .r10) (.imm 0x4), 4) := by
  decide +kernel
theorem d306 : Silmaril.X86.Ext.decode ((code.drop 306).take 7) =
    some (.load .q .r9 (Silmaril.X86.Sep.Insn.memAt .r10 0x4032d0), 7) := by
  decide +kernel
theorem d313 : Silmaril.X86.Ext.decode ((code.drop 313).take 7) =
    some (.load .q .r8 (Silmaril.X86.Sep.Insn.memAt .r10 0x4032c8), 7) := by
  decide +kernel
theorem d320 : Silmaril.X86.Ext.decode ((code.drop 320).take 3) =
    some (.test .q (.reg .r9) .r9, 3) := by
  decide +kernel
theorem d323 : Silmaril.X86.Ext.decode ((code.drop 323).take 6) =
    some (.jcc .e 0xd7, 6) := by
  decide +kernel
theorem d329 : Silmaril.X86.Ext.decode ((code.drop 329).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .r9 0x8)) .r8, 4) := by
  decide +kernel
theorem d333 : Silmaril.X86.Ext.decode ((code.drop 333).take 3) =
    some (.test .q (.reg .r8) .r8, 3) := by
  decide +kernel
theorem d336 : Silmaril.X86.Ext.decode ((code.drop 336).take 2) =
    some (.jcc8 .e 0x4, 2) := by
  decide +kernel
theorem d338 : Silmaril.X86.Ext.decode ((code.drop 338).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .r8 0x10)) .r9, 4) := by
  decide +kernel
theorem d342 : Silmaril.X86.Ext.decode ((code.drop 342).take 7) =
    some (.movI8 (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0x4031c0)) 0x0, 7) := by
  decide +kernel
theorem d349 : Silmaril.X86.Ext.decode ((code.drop 349).take 7) =
    some (.aluR .q .add .rax (.mem (Silmaril.X86.Sep.Insn.memAt .r10 0x4032c0)), 7) := by
  decide +kernel
theorem d356 : Silmaril.X86.Ext.decode ((code.drop 356).take 3) =
    some (.test .q (.reg .rdx) .rdx, 3) := by
  decide +kernel
theorem d359 : Silmaril.X86.Ext.decode ((code.drop 359).take 2) =
    some (.jcc8 .ne 0x47, 2) := by
  decide +kernel
theorem d361 : Silmaril.X86.Ext.decode ((code.drop 361).take 7) =
    some (.load .q .rsi (ripMem 0x1c00), 7) := by
  decide +kernel
theorem d368 : Silmaril.X86.Ext.decode ((code.drop 368).take 7) =
    some (.movI .q (.reg .r8) 0xffffffff, 7) := by
  decide +kernel
theorem d375 : Silmaril.X86.Ext.decode ((code.drop 375).take 3) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 0x0)) .rax, 3) := by
  decide +kernel
theorem d378 : Silmaril.X86.Ext.decode ((code.drop 378).take 5) =
    some (.mov .q (.mem (idx .rcx .rax (by decide) 0xfffffff8)) .rax, 5) := by
  decide +kernel
theorem d383 : Silmaril.X86.Ext.decode ((code.drop 383).take 4) =
    some (.shift .q .shr (.reg .rax) (.imm 0x4), 4) := by
  decide +kernel
theorem d387 : Silmaril.X86.Ext.decode ((code.drop 387).take 7) =
    some (.movI8 (.mem (Silmaril.X86.Sep.Insn.memAt .rdx 0x4031c0)) 0x1, 7) := by
  decide +kernel
theorem d394 : Silmaril.X86.Ext.decode ((code.drop 394).take 9) =
    some (.movI8 (.mem (idx .r8 .rax (by decide) 0x4030c0)) 0x1, 9) := by
  decide +kernel
theorem d403 : Silmaril.X86.Ext.decode ((code.drop 403).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 0x8)) .rsi, 4) := by
  decide +kernel
theorem d407 : Silmaril.X86.Ext.decode ((code.drop 407).take 8) =
    some (.movI .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 0x10)) 0x0, 8) := by
  decide +kernel
theorem d415 : Silmaril.X86.Ext.decode ((code.drop 415).take 3) =
    some (.test .q (.reg .rsi) .rsi, 3) := by
  decide +kernel
theorem d418 : Silmaril.X86.Ext.decode ((code.drop 418).take 2) =
    some (.jcc8 .e 0x4, 2) := by
  decide +kernel
theorem d420 : Silmaril.X86.Ext.decode ((code.drop 420).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0x10)) .rcx, 4) := by
  decide +kernel
theorem d424 : Silmaril.X86.Ext.decode ((code.drop 424).take 7) =
    some (.mov .q (.mem (ripMem 0x1bc1)) .rcx, 7) := by
  decide +kernel
theorem r431 : (code.drop 431).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d432 : Silmaril.X86.Ext.decode ((code.drop 432).take 7) =
    some (.cmpI8 (.mem (Silmaril.X86.Sep.Insn.memAt .rdx 0x4030bf)) 0x0, 7) := by
  decide +kernel
theorem d439 : Silmaril.X86.Ext.decode ((code.drop 439).take 4) =
    some (.lea .q .r8 (Silmaril.X86.Sep.Insn.memAt .rdx 0xffffffff), 4) := by
  decide +kernel
theorem d443 : Silmaril.X86.Ext.decode ((code.drop 443).take 2) =
    some (.jcc8 .ne 0x13, 2) := by
  decide +kernel
theorem d445 : Silmaril.X86.Ext.decode ((code.drop 445).take 7) =
    some (.load .q .rsi (ripMem 0x1bac), 7) := by
  decide +kernel
theorem d452 : Silmaril.X86.Ext.decode ((code.drop 452).take 2) =
    some (.jmp8 0xb1, 2) := by
  decide +kernel
theorem d464 : Silmaril.X86.Ext.decode ((code.drop 464).take 4) =
    some (.load .q .r9 (Silmaril.X86.Sep.Insn.memAt .rdi 0xffffffe8), 4) := by
  decide +kernel
theorem d468 : Silmaril.X86.Ext.decode ((code.drop 468).take 3) =
    some (.alu .q .sub (.reg .rcx) .r9, 3) := by
  decide +kernel
theorem d471 : Silmaril.X86.Ext.decode ((code.drop 471).take 4) =
    some (.load .q .rdi (Silmaril.X86.Sep.Insn.memAt .rcx 0x10), 4) := by
  decide +kernel
theorem d475 : Silmaril.X86.Ext.decode ((code.drop 475).take 4) =
    some (.load .q .rdx (Silmaril.X86.Sep.Insn.memAt .rcx 0x8), 4) := by
  decide +kernel
theorem d479 : Silmaril.X86.Ext.decode ((code.drop 479).take 3) =
    some (.test .q (.reg .rdi) .rdi, 3) := by
  decide +kernel
theorem d482 : Silmaril.X86.Ext.decode ((code.drop 482).take 2) =
    some (.jcc8 .e 0x4c, 2) := by
  decide +kernel
theorem d484 : Silmaril.X86.Ext.decode ((code.drop 484).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rdi 0x8)) .rdx, 4) := by
  decide +kernel
theorem d488 : Silmaril.X86.Ext.decode ((code.drop 488).take 7) =
    some (.load .q .rsi (ripMem 0x1b81), 7) := by
  decide +kernel
theorem d495 : Silmaril.X86.Ext.decode ((code.drop 495).take 3) =
    some (.test .q (.reg .rdx) .rdx, 3) := by
  decide +kernel
theorem d498 : Silmaril.X86.Ext.decode ((code.drop 498).take 2) =
    some (.jcc8 .e 0x4, 2) := by
  decide +kernel
theorem d500 : Silmaril.X86.Ext.decode ((code.drop 500).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rdx 0x10)) .rdi, 4) := by
  decide +kernel
theorem d504 : Silmaril.X86.Ext.decode ((code.drop 504).take 3) =
    some (.mov .q (.reg .rdx) .rcx, 3) := by
  decide +kernel
theorem d507 : Silmaril.X86.Ext.decode ((code.drop 507).take 8) =
    some (.movI8 (.mem (Silmaril.X86.Sep.Insn.memAt .r8 0x4030c0)) 0x0, 8) := by
  decide +kernel
theorem d515 : Silmaril.X86.Ext.decode ((code.drop 515).take 3) =
    some (.alu .q .add (.reg .rax) .r9, 3) := by
  decide +kernel
theorem d518 : Silmaril.X86.Ext.decode ((code.drop 518).take 7) =
    some (.aluI .q .sub (.reg .rdx) 0x4032c0, 7) := by
  decide +kernel
theorem d525 : Silmaril.X86.Ext.decode ((code.drop 525).take 4) =
    some (.shift .q .shr (.reg .rdx) (.imm 0x4), 4) := by
  decide +kernel
theorem d529 : Silmaril.X86.Ext.decode ((code.drop 529).take 4) =
    some (.lea .q .r8 (Silmaril.X86.Sep.Insn.memAt .rdx 0xffffffff), 4) := by
  decide +kernel
theorem d533 : Silmaril.X86.Ext.decode ((code.drop 533).take 5) =
    some (.jmp 0xffffff5d, 5) := by
  decide +kernel
theorem d544 : Silmaril.X86.Ext.decode ((code.drop 544).take 7) =
    some (.mov .q (.mem (ripMem 0x1b49)) .r8, 7) := by
  decide +kernel
theorem d551 : Silmaril.X86.Ext.decode ((code.drop 551).take 5) =
    some (.jmp 0xffffff21, 5) := by
  decide +kernel
theorem d560 : Silmaril.X86.Ext.decode ((code.drop 560).take 3) =
    some (.mov .q (.reg .rsi) .rdx, 3) := by
  decide +kernel
theorem d563 : Silmaril.X86.Ext.decode ((code.drop 563).take 2) =
    some (.jmp8 0xba, 2) := by
  decide +kernel

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
