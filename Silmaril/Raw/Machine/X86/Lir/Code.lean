module

public import Silmaril.Machine.X86.Lir.Regs.Defs

/-!
# Code generation from Lir to x86-64

`compile A p codeBase` translates a Lir program over physical registers `P`
(for example the output of `Lir.Alloc.spill`) into the bytes of the local
x86-64 model `X86.Ext`, placed at `codeBase`, or reports every reason it cannot
(`Error`).

## Selection

Operations are selected into short fixed sequences that go through the scratch
registers (`Regs.lean`), so a destination may alias any source:

* `add sub and or xor mul`: `mov r11, x; op r11, y; mov d, r11`;
* shifts and rotates: `mov rcx, y; mov r11, x; op r11, cl; mov d, r11`, with the
  32-bit operand size for the `32` forms (which zero-extends the result, as Lir
  requires);
* division and remainder: `mov rax, x; cqo`/`cdq` (signed) or `mov rdx, 0`
  (unsigned); `idiv y`/`div y`; `mov d, rax` or `mov d, rdx`, at the 32-bit
  size for the `32` forms;
* comparisons: `cmp x, y; setcc al; movzx d, al`, at the 32-bit size for
  `cmp32`; `eqz` is `cmp x, 0; sete al; movzx d, al`;
* extensions: MOVSX/MOVZX/MOVSXD, and `mov d32, s32` for `zext32`;
* loads and stores: `movabs r11, offset; add r11, base` and then an access to
  `[r15 + r11]`, with MOVZX/MOVSX/MOVSXD for narrow loads;
* stack slots: `[rsp + 8 n]`;
* `clz`, `ctz`, `popcnt`: LZCNT, TZCNT, POPCNT at 64 or 32 bits (the 32-bit
  forms zero-extend). The model gives these encodings their LZCNT/TZCNT/POPCNT
  meaning, which holds on processors with the corresponding CPUID features
  (`Ext.Instr.requires`); on processors without them, `F3 0F BD`/`BC` execute
  as BSR/BSF and `F3 0F B8` raises #UD, and the correctness theorem does not
  apply to such code there. `usesBitCount` tells whether a program contains
  these operators.

* `mulhu`, `mulhs`: this lowering computes the high half of the 128-bit
  product from the four products of the 32-bit halves
  with 64-bit IMUL, shifts and additions (`mulhuCore`); `mulhs` then subtracts
  `y` if `x < 0` and `x` if `y < 0`, using the masks `x sar 63` and `y sar 63`.

Every Lir operator is compiled. Floating-point instructions (`fop`) are not:
they are reported as errors (`Error.floatOp`), since the model `X86.Ext` has no
XMM state.

## Frames

A function's frame, from its body stack pointer `B` upwards: the slot area
(`8 * nslots` bytes, slot `n` at `B + 8 n`), the save area (nine words, at
`B + 8 * nslots`), padding so that the frame size `F` is `8 (mod 16)`, the four
words pushed by the prologue and the return address. The prologue is

```
mov r11, rsp; sub r11, r14; cmp r11, need; jae +2; ud2   ; stack-limit check
push rbp; push rbx; push r12; push r13; sub rsp, F
mov [save + 8 j], argⱼ ...        ; stage the arguments
mov pⱼ, [save + 8 j] ...          ; move them to the parameter locations
jmp entry
```

where `need = F + 40` also leaves room for the return address of an outgoing
call. The epilogue is `add rsp, F; pop r13; pop r12; pop rbx; pop rbp; ret`.
A call site stores the nine allocatable registers in the save area, loads the
(at most six) arguments into `rdi rsi rdx rcx r8 r9` from the save area or the
slots, executes `call rel32`, reloads the nine registers and moves the (at
most two) results from `rax rdx`. More arguments, parameters, results or
returned values are reported as errors.

## Layout

Code is produced as `AInstr`s, whose jumps and calls name a block or function.
Every `AInstr` has a length independent of the final addresses (`AInstr.len`),
so the layout (`Layout`) is computed first and the displacements (`rel32`) are
filled in afterwards (`encodeAt`). Jump and call targets must exist, and the
program must be shorter than `2^31` bytes, so every displacement fits.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.X86 (Reg Word AluOp Byte)
open Silmaril.Machine

/-! ## Errors -/

/-- Reasons a Lir program is not compiled. -/
inductive Error where
  | tooManyParams (func : Lir.FuncId) (count : Nat)
  | tooManyArgs (func : Lir.FuncId) (count : Nat)
  | tooManyResults (func : Lir.FuncId) (count : Nat)
  | tooManyReturnValues (func : Lir.FuncId) (count : Nat)
  | badLabel (func : Lir.FuncId) (label : Lir.Label)
  | badCallee (func : Lir.FuncId) (callee : Lir.FuncId)
  | frameTooLarge (func : Lir.FuncId)
  | codeTooLarge
  | floatOp (func : Lir.FuncId)
  deriving DecidableEq, Repr

/-! ## Operands -/

/-- `[rsp + d]`. -/
def spMem (d : Nat) : Ext.Mem := Ext.Mem.ofReg .rsp none (BitVec.ofNat 32 d)

/-- `[r15 + r11]`: the linear-memory access of a computed offset. -/
def linMem : Ext.Mem := Ext.Mem.ofReg .r15 (some ⟨.r11, 0, by decide⟩) 0

/-- The argument register of position `j` (`rdi` beyond the sixth, never used
by compiled code). -/
def argRegN (j : Nat) : Reg := if h : j < 6 then argReg ⟨j, h⟩ else .rdi

/-- The result register of position `j` (`rax` beyond the second, never used). -/
def resRegN (j : Nat) : Reg := if h : j < 2 then resReg ⟨j, h⟩ else .rax

/-! ## Frame layout -/

/-- Words of the frame below the pushed registers: slots, the nine-word save
area and padding to an odd number of words. -/
def frameWords (nslots : Nat) : Nat := if (nslots + 9) % 2 = 1 then nslots + 9 else nslots + 10

/-- The frame size `F`, `8 (mod 16)`. -/
def frameSize (nslots : Nat) : Nat := 8 * frameWords nslots

/-- The stack space a function needs below its entry stack pointer: the pushed
registers, the frame and the return address of an outgoing call. -/
def need (nslots : Nat) : Nat := frameSize nslots + 40

/-- The offset of save-area word `k` from the body stack pointer. -/
def saveDisp (nslots k : Nat) : Nat := 8 * nslots + 8 * k

theorem frameSize_mod (nslots : Nat) : frameSize nslots % 16 = 8 := by
  unfold frameSize frameWords; split <;> omega

theorem save_lt_frame (nslots : Nat) {k : Nat} (hk : k < 9) :
    saveDisp nslots k + 8 ≤ frameSize nslots := by
  unfold saveDisp frameSize frameWords; split <;> omega

theorem slot_lt_frame {nslots n : Nat} (hn : n < nslots) : 8 * n + 8 ≤ saveDisp nslots 0 := by
  unfold saveDisp; omega

/-! ## Slots used by a function -/

section Slots

variable {P : Type}

def locSlots (ls : List (Lir.Loc P)) : List Nat :=
  ls.filterMap fun | .reg _ => none | .slot n => some n

def opSlots : Lir.Op P → List Nat
  | .slotGet _ n => [n]
  | .slotSet n _ => [n]
  | _ => []

def instrSlots : Lir.Instr P → List Nat
  | .op o => opSlots o
  | .call _ args results => locSlots args ++ locSlots results
  | .fop .. => []

def termSlots : Lir.Term P → List Nat
  | .ret ls => locSlots ls
  | _ => []

def blockSlots (b : Lir.Block P) : List Nat := b.instrs.flatMap instrSlots ++ termSlots b.term

def funcSlots (fn : Lir.Func P) : List Nat := locSlots fn.params ++ fn.blocks.flatMap blockSlots

/-- One more than the largest slot a function mentions. -/
def nslots (fn : Lir.Func P) : Nat := (funcSlots fn).foldr max 0 + 1

theorem lt_foldr_max {l : List Nat} {n : Nat} (h : n ∈ l) : n < l.foldr max 0 + 1 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem lt_nslots {fn : Lir.Func P} {n : Nat} (h : n ∈ funcSlots fn) : n < nslots fn :=
  lt_foldr_max h

end Slots

/-! ## Abstract instructions -/

/-- An instruction whose jump or call target is still symbolic. -/
inductive AInstr where
  | plain (i : Ext.Instr)
  | jmp (func : Lir.FuncId) (label : Lir.Label)
  | jcc (c : Ext.Cond) (func : Lir.FuncId) (label : Lir.Label)
  | call (func : Lir.FuncId)
  deriving DecidableEq, Repr

/-- The encoded length, independent of the resolved target. -/
def AInstr.len : AInstr → Nat
  | .plain i => (Ext.encode i).length
  | .jmp _ _ => 5
  | .jcc _ _ _ => 6
  | .call _ => 5

def lenOf (l : List AInstr) : Nat := (l.map AInstr.len).sum

@[simp] theorem lenOf_nil : lenOf [] = 0 := rfl
@[simp] theorem lenOf_cons (i : AInstr) (l : List AInstr) : lenOf (i :: l) = i.len + lenOf l := by
  simp [lenOf]
@[simp] theorem lenOf_append (l l' : List AInstr) : lenOf (l ++ l') = lenOf l + lenOf l' := by
  simp [lenOf]

/-- Addresses of blocks and functions. -/
structure Layout where
  func : Lir.FuncId → Nat
  block : Lir.FuncId → Lir.Label → Nat

/-- The displacement from `next` to `target`. -/
def rel32 (target next : Nat) : BitVec 32 := BitVec.ofInt 32 ((target : Int) - next)

def AInstr.resolve (L : Layout) (addr : Nat) : AInstr → Ext.Instr
  | .plain i => i
  | .jmp f l => .jmp (rel32 (L.block f l) (addr + 5))
  | .jcc c f l => .jcc c (rel32 (L.block f l) (addr + 6))
  | .call g => .call (rel32 (L.func g) (addr + 5))

/-- Encode abstract instructions placed at `addr`. -/
def encodeAt (L : Layout) : Nat → List AInstr → List Byte
  | _, [] => []
  | a, i :: is => Ext.encode (i.resolve L a) ++ encodeAt L (a + i.len) is

theorem encode_resolve_length (L : Layout) (a : Nat) (i : AInstr) :
    (Ext.encode (i.resolve L a)).length = i.len := by
  cases i with
  | plain => rfl
  | jmp => rfl
  | jcc c => cases c <;> rfl
  | call => rfl

@[simp] theorem encodeAt_length (L : Layout) (a : Nat) (is : List AInstr) :
    (encodeAt L a is).length = lenOf is := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih => simp [encodeAt, ih, encode_resolve_length]

theorem encodeAt_append (L : Layout) (a : Nat) (xs ys : List AInstr) :
    encodeAt L a (xs ++ ys) = encodeAt L a xs ++ encodeAt L (a + lenOf xs) ys := by
  induction xs generalizing a with
  | nil => simp [encodeAt]
  | cons i is ih => simp [encodeAt, ih, Nat.add_assoc]

/-- Plain instructions encode independently of their address. -/
theorem encodeAt_plain (L : Layout) (a : Nat) (is : List Ext.Instr) :
    encodeAt L a (is.map .plain) = is.flatMap Ext.encode := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih => simp [encodeAt, ih, AInstr.resolve]

theorem lenOf_plain (is : List Ext.Instr) :
    lenOf (is.map .plain) = (is.flatMap Ext.encode).length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [ih, AInstr.len]

/-! ## Selection of operations -/

def Ext.Cond.ofLir : Lir.Cond → Ext.Cond
  | .eq => .e | .ne => .ne | .lts => .l | .ltu => .b | .les => .le | .leu => .be
  | .gts => .g | .gtu => .a | .ges => .ge | .geu => .ae

def selUnop (op : Lir.Unop) (d s : Reg) : List Ext.Instr :=
  match op with
  | .sext8 => [.movx true .q .b d (.reg s)]
  | .sext16 => [.movx true .q .w d (.reg s)]
  | .sext32 => [.movsxd d (.reg s)]
  | .zext8 => [.movx false .q .b d (.reg s)]
  | .zext16 => [.movx false .q .w d (.reg s)]
  | .zext32 => [.mov .d (.reg d) s]
  | .eqz => [.aluI .q .cmp (.reg s) 0, .setcc .e (.reg .rax), .movx false .q .b d (.reg .rax)]
  | .clz => [.bitcount .lzcnt .q d (.reg s)]
  | .ctz => [.bitcount .tzcnt .q d (.reg s)]
  | .popcnt => [.bitcount .popcnt .q d (.reg s)]
  | .clz32 => [.bitcount .lzcnt .d d (.reg s)]
  | .ctz32 => [.bitcount .tzcnt .d d (.reg s)]
  | .popcnt32 => [.bitcount .popcnt .d d (.reg s)]

/-- The operators compiled to LZCNT, TZCNT or POPCNT. -/
def isBitCount : Lir.Unop → Bool
  | .clz | .ctz | .popcnt | .clz32 | .ctz32 | .popcnt32 => true
  | _ => false

def selAlu (o : AluOp) (d x y : Reg) : List Ext.Instr :=
  [.mov .q (.reg .r11) x, .alu .q o (.reg .r11) y, .mov .q (.reg d) .r11]

def selMul (d x y : Reg) : List Ext.Instr :=
  [.mov .q (.reg .r11) x, .imul .q .r11 (.reg y), .mov .q (.reg d) .r11]

def selShift (sz : Ext.Sz) (o : Ext.ShiftOp) (d x y : Reg) : List Ext.Instr :=
  [.mov .q (.reg .rcx) y, .mov .q (.reg .r11) x, .shift sz o (.reg .r11) .cl, .mov .q (.reg d) .r11]

def selDiv (sz : Ext.Sz) (signed rem : Bool) (d x y : Reg) : List Ext.Instr :=
  [.mov sz (.reg .rax) x, if signed then .cxd sz else .movI sz (.reg .rdx) 0,
    .div sz signed (.reg y), .mov .q (.reg d) (if rem then .rdx else .rax)]

def selCmp (sz : Ext.Sz) (c : Ext.Cond) (d x y : Reg) : List Ext.Instr :=
  [.alu sz .cmp (.reg x) y, .setcc c (.reg .rax), .movx false .q .b d (.reg .rax)]

/-- `rax :=` the high 64 bits of the unsigned product of `x` and `y`, from the
32-bit halves `x = a·2³² + b`, `y = c·2³² + e`:
`a·c + (a·e ≫ 32) + (b·c ≫ 32) + ((b·e ≫ 32) + (a·e mod 2³²) + (b·c mod 2³²)) ≫ 32`. -/
def mulhuCore (x y : Reg) : List Ext.Instr :=
  [.mov .q (.reg .rax) x, .shift .q .shr (.reg .rax) (.imm 32),
   .mov .q (.reg .rcx) y, .mov .d (.reg .rcx) .rcx,
   .imul .q .rax (.reg .rcx),
   .mov .q (.reg .r11) x, .mov .d (.reg .r11) .r11,
   .imul .q .r11 (.reg .rcx),
   .shift .q .shr (.reg .r11) (.imm 32),
   .mov .q (.reg .rdx) .rax, .mov .d (.reg .rdx) .rdx,
   .alu .q .add (.reg .r11) .rdx,
   .shift .q .shr (.reg .rax) (.imm 32),
   .mov .q (.reg .rcx) y, .shift .q .shr (.reg .rcx) (.imm 32),
   .mov .q (.reg .rdx) x, .mov .d (.reg .rdx) .rdx,
   .imul .q .rdx (.reg .rcx),
   .shift .q .shr (.reg .rdx) (.imm 32), .alu .q .add (.reg .rax) .rdx,
   .mov .q (.reg .rdx) x, .mov .d (.reg .rdx) .rdx, .imul .q .rdx (.reg .rcx),
   .mov .d (.reg .rdx) .rdx, .alu .q .add (.reg .r11) .rdx,
   .shift .q .shr (.reg .r11) (.imm 32), .alu .q .add (.reg .rax) .r11,
   .mov .q (.reg .rdx) x, .shift .q .shr (.reg .rdx) (.imm 32),
   .imul .q .rdx (.reg .rcx), .alu .q .add (.reg .rax) .rdx]

/-- From the unsigned high product in `rax` to the signed one:
`rax -= (x sar 63) & y; rax -= (y sar 63) & x`. -/
def mulhsFix (x y : Reg) : List Ext.Instr :=
  [.mov .q (.reg .r11) x, .shift .q .sar (.reg .r11) (.imm 63), .alu .q .and (.reg .r11) y,
   .alu .q .sub (.reg .rax) .r11,
   .mov .q (.reg .r11) y, .shift .q .sar (.reg .r11) (.imm 63), .alu .q .and (.reg .r11) x,
   .alu .q .sub (.reg .rax) .r11]

def selBinop (op : Lir.Binop) (d x y : Reg) : List Ext.Instr :=
  match op with
  | .add => selAlu .add d x y
  | .sub => selAlu .sub d x y
  | .and => selAlu .and d x y
  | .or => selAlu .or d x y
  | .xor => selAlu .xor d x y
  | .mul => selMul d x y
  | .shl => selShift .q .shl d x y
  | .shrs => selShift .q .sar d x y
  | .shru => selShift .q .shr d x y
  | .rotl => selShift .q .rol d x y
  | .rotr => selShift .q .ror d x y
  | .shl32 => selShift .d .shl d x y
  | .shrs32 => selShift .d .sar d x y
  | .shru32 => selShift .d .shr d x y
  | .rotl32 => selShift .d .rol d x y
  | .rotr32 => selShift .d .ror d x y
  | .divs => selDiv .q true false d x y
  | .divu => selDiv .q false false d x y
  | .rems => selDiv .q true true d x y
  | .remu => selDiv .q false true d x y
  | .divs32 => selDiv .d true false d x y
  | .divu32 => selDiv .d false false d x y
  | .rems32 => selDiv .d true true d x y
  | .remu32 => selDiv .d false true d x y
  | .cmp c => selCmp .q (Ext.Cond.ofLir c) d x y
  | .cmp32 c => selCmp .d (Ext.Cond.ofLir c) d x y
  | .mulhu => mulhuCore x y ++ [.mov .q (.reg d) .rax]
  | .mulhs => mulhuCore x y ++ mulhsFix x y ++ [.mov .q (.reg d) .rax]

/-- `r11 := base + offset`. -/
def addrSeq (base : Reg) (off : Nat) : List Ext.Instr :=
  [.movabs .r11 (BitVec.ofNat 64 off), .alu .q .add (.reg .r11) base]

def selLoad (w : Lir.Width) (e : Lir.Ext) (d : Reg) : Ext.Instr :=
  match w, e with
  | .b1, .zero => .movx false .q .b d (.mem linMem)
  | .b1, .sign => .movx true .q .b d (.mem linMem)
  | .b2, .zero => .movx false .q .w d (.mem linMem)
  | .b2, .sign => .movx true .q .w d (.mem linMem)
  | .b4, .zero => .load .d d linMem
  | .b4, .sign => .movsxd d (.mem linMem)
  | .b8, _ => .load .q d linMem

def selStore (w : Lir.Width) (s : Reg) : Ext.Instr :=
  match w with
  | .b1 => .store .b (.mem linMem) s
  | .b2 => .store .w (.mem linMem) s
  | .b4 => .mov .d (.mem linMem) s
  | .b8 => .mov .q (.mem linMem) s

section Gen

variable {P : Type} (A : Assign P)

def selOp : Lir.Op P → List Ext.Instr
  | .const d v => [.movabs (A.reg d) v]
  | .move d s => [.mov .q (.reg (A.reg d)) (A.reg s)]
  | .unary op d s => selUnop op (A.reg d) (A.reg s)
  | .binary op d x y => selBinop op (A.reg d) (A.reg x) (A.reg y)
  | .load w e d b off => addrSeq (A.reg b) off ++ [selLoad w e (A.reg d)]
  | .store w b off s => addrSeq (A.reg b) off ++ [selStore w (A.reg s)]
  | .slotGet d n => [.load .q (A.reg d) (spMem (8 * n))]
  | .slotSet n s => [.mov .q (.mem (spMem (8 * n))) (A.reg s)]

/-! ## Calls, returns and frames -/

/-- Store the nine allocatable registers in the save area. -/
def saveAll (ns : Nat) : List Ext.Instr :=
  (List.finRange 9).map fun (k : Fin 9) => .mov .q (.mem (spMem (saveDisp ns k.val))) (allocReg k)

/-- Reload the nine allocatable registers from the save area. -/
def reloadAll (ns : Nat) : List Ext.Instr :=
  (List.finRange 9).map fun (k : Fin 9) => .load .q (allocReg k) (spMem (saveDisp ns k.val))

/-- Load argument `j` from the save area (registers) or its slot. -/
def argLoad (ns j : Nat) : Lir.Loc P → Ext.Instr
  | .reg p => .load .q (argRegN j) (spMem (saveDisp ns (A.idx p)))
  | .slot n => .load .q (argRegN j) (spMem (8 * n))

def argLoads (ns : Nat) : Nat → List (Lir.Loc P) → List Ext.Instr
  | _, [] => []
  | j, l :: ls => argLoad A ns j l :: argLoads ns (j + 1) ls

/-- Move result `j` from its result register to its location. -/
def resStore (j : Nat) : Lir.Loc P → Ext.Instr
  | .reg p => .mov .q (.reg (A.reg p)) (resRegN j)
  | .slot n => .mov .q (.mem (spMem (8 * n))) (resRegN j)

def resStores : Nat → List (Lir.Loc P) → List Ext.Instr
  | _, [] => []
  | j, l :: ls => resStore A j l :: resStores (j + 1) ls

/-- Load returned value `j` into its result register. -/
def retLoad (j : Nat) : Lir.Loc P → Ext.Instr
  | .reg p => .mov .q (.reg (resRegN j)) (A.reg p)
  | .slot n => .load .q (resRegN j) (spMem (8 * n))

def retLoads : Nat → List (Lir.Loc P) → List Ext.Instr
  | _, [] => []
  | j, l :: ls => retLoad A j l :: retLoads (j + 1) ls

/-- The stack-limit check: trap unless `rsp - r14 ≥ need`. -/
def checkSeq (ns : Nat) : List Ext.Instr :=
  [.mov .q (.reg .r11) .rsp, .alu .q .sub (.reg .r11) .r14,
    .aluI .q .cmp (.reg .r11) (BitVec.ofNat 32 (need ns)), .jcc .ae 2, .ud2]

def pushSeq (ns : Nat) : List Ext.Instr :=
  [.push .rbp, .push .rbx, .push .r12, .push .r13,
    .aluI .q .sub (.reg .rsp) (BitVec.ofNat 32 (frameSize ns))]

def epilogue (ns : Nat) : List Ext.Instr :=
  [.aluI .q .add (.reg .rsp) (BitVec.ofNat 32 (frameSize ns)), .pop .r13, .pop .r12, .pop .rbx,
    .pop .rbp, .ret]

/-- Stage the incoming argument registers in the save area. -/
def stageSeq (ns : Nat) : Nat → List (Lir.Loc P) → List Ext.Instr
  | _, [] => []
  | j, _ :: ls => .mov .q (.mem (spMem (saveDisp ns j))) (argRegN j) :: stageSeq ns (j + 1) ls

/-- Move staged argument `j` to parameter location `l`. -/
def paramMove (ns j : Nat) : Lir.Loc P → List Ext.Instr
  | .reg p => [.load .q (A.reg p) (spMem (saveDisp ns j))]
  | .slot n => [.load .q .r11 (spMem (saveDisp ns j)), .mov .q (.mem (spMem (8 * n))) .r11]

def paramMoves (ns : Nat) : Nat → List (Lir.Loc P) → List Ext.Instr
  | _, [] => []
  | j, l :: ls => paramMove A ns j l ++ paramMoves ns (j + 1) ls

/-- The prologue of function `f`. -/
def prologue (f : Lir.FuncId) (fn : Lir.Func P) : List AInstr :=
  (checkSeq (nslots fn) ++ pushSeq (nslots fn) ++ stageSeq (nslots fn) 0 fn.params ++
    paramMoves A (nslots fn) 0 fn.params).map .plain ++ [.jmp f fn.entry]

/-- The code of one Lir instruction. -/
def instrChunk (ns : Nat) : Lir.Instr P → List AInstr
  | .op o => (selOp A o).map .plain
  | .call g args results =>
    (saveAll ns ++ argLoads A ns 0 args).map .plain ++ [.call g] ++
      (reloadAll ns ++ resStores A 0 results).map .plain
  | .fop .. => [.plain .ud2]

/-- The code of a terminator of function `f`. -/
def termChunk (f : Lir.FuncId) (ns : Nat) : Lir.Term P → List AInstr
  | .jump l => [.jmp f l]
  | .branch c l₁ l₂ => [.plain (.test .q (.reg (A.reg c)) (A.reg c)), .jcc .ne f l₁, .jmp f l₂]
  | .ret ls => (retLoads A 0 ls ++ epilogue ns).map .plain
  | .trap => [.plain .ud2]

def blockChunks (f : Lir.FuncId) (ns : Nat) (b : Lir.Block P) : List (List AInstr) :=
  b.instrs.map (instrChunk A ns) ++ [termChunk A f ns b.term]

def blockCode (f : Lir.FuncId) (ns : Nat) (b : Lir.Block P) : List AInstr :=
  (blockChunks A f ns b).flatten

def funcCode (f : Lir.FuncId) (fn : Lir.Func P) : List AInstr :=
  prologue A f fn ++ (fn.blocks.map (blockCode A f (nslots fn))).flatten

def funcCodes (p : Lir.Prog P) : List (List AInstr) := p.funcs.mapIdx (funcCode A)

def progCode (p : Lir.Prog P) : List AInstr := (funcCodes A p).flatten

/-! ## Layout -/

/-- Offset of function `f` in the program. -/
def funcOff (p : Lir.Prog P) (f : Lir.FuncId) : Nat := lenOf ((funcCodes A p).take f).flatten

/-- Offset of block `l` in function `f` (of body `fn`). -/
def blockOff (f : Lir.FuncId) (fn : Lir.Func P) (l : Lir.Label) : Nat :=
  lenOf (prologue A f fn) + lenOf ((fn.blocks.map (blockCode A f (nslots fn))).take l).flatten

/-- Offset of chunk `i` in block `b` of function `f`. -/
def chunkOff (f : Lir.FuncId) (ns : Nat) (b : Lir.Block P) (i : Nat) : Nat :=
  lenOf ((blockChunks A f ns b).take i).flatten

def emptyFunc : Lir.Func P := ⟨[], 0, []⟩
def emptyBlock : Lir.Block P := ⟨[], .trap⟩

def layout (p : Lir.Prog P) (codeBase : Nat) : Layout where
  func g := codeBase + funcOff A p g
  block f l := codeBase + funcOff A p f + blockOff A f ((p.func? f).getD emptyFunc) l

/-- The address of a program point. -/
def pointAddr (p : Lir.Prog P) (codeBase : Nat) (pt : Lir.Point) : Nat :=
  let fn := (p.func? pt.func).getD emptyFunc
  codeBase + funcOff A p pt.func + blockOff A pt.func fn pt.label +
    chunkOff A pt.func (nslots fn) ((fn.blocks[pt.label]?).getD emptyBlock) pt.index

/-! ## Checks -/

def instrErrors (p : Lir.Prog P) (f : Lir.FuncId) : Lir.Instr P → List Error
  | .op _ => []
  | .call g args results =>
    (if args.length ≤ 6 then [] else [.tooManyArgs f args.length]) ++
    (if results.length ≤ 2 then [] else [.tooManyResults f results.length]) ++
    (if g < p.funcs.length then [] else [.badCallee f g])
  | .fop .. => [.floatOp f]

def labelErrors (fn : Lir.Func P) (f : Lir.FuncId) (l : Lir.Label) : List Error :=
  if l < fn.blocks.length then [] else [.badLabel f l]

def termErrors (fn : Lir.Func P) (f : Lir.FuncId) : Lir.Term P → List Error
  | .jump l => labelErrors fn f l
  | .branch _ l₁ l₂ => labelErrors fn f l₁ ++ labelErrors fn f l₂
  | .ret ls => if ls.length ≤ 2 then [] else [.tooManyReturnValues f ls.length]
  | .trap => []

def funcErrors (p : Lir.Prog P) (f : Lir.FuncId) (fn : Lir.Func P) : List Error :=
  (if fn.params.length ≤ 6 then [] else [.tooManyParams f fn.params.length]) ++
  labelErrors fn f fn.entry ++
  (if need (nslots fn) < 2 ^ 31 then [] else [.frameTooLarge f]) ++
  fn.blocks.flatMap fun b => b.instrs.flatMap (instrErrors p f) ++ termErrors fn f b.term

def progErrors (p : Lir.Prog P) : List Error :=
  (p.funcs.mapIdx (funcErrors p)).flatten ++
  (if lenOf (progCode A p) < 2 ^ 31 then [] else [.codeTooLarge])

/-- Whether a program contains an operator compiled to LZCNT, TZCNT or POPCNT,
whose meaning in the model assumes the corresponding CPUID feature. -/
def usesBitCount (p : Lir.Prog P) : Bool :=
  p.funcs.any fun fn => fn.blocks.any fun b => b.instrs.any fun
    | .op (.unary op _ _) => isBitCount op
    | _ => false

/-- The compiled program: its bytes and the layout they were placed with. -/
structure Image where
  code : List Byte
  layout : Layout

/-- Compile a Lir program, placing its code at `codeBase`. -/
def compile (p : Lir.Prog P) (codeBase : Nat) : Except (List Error) Image :=
  match progErrors A p with
  | [] => .ok ⟨encodeAt (layout A p codeBase) codeBase (progCode A p), layout A p codeBase⟩
  | errs => .error errs

end Gen

end Silmaril.X86.Backend
