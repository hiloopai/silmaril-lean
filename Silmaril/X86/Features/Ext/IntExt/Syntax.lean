module

public import Silmaril.X86.Ext.Syntax

/-!
# Integer extensions: syntax

The instruction forms of the `int-ext` lane of the feature-parametric machine
(`Features.Machine`): integer instructions that compilers and bignum code emit
and that the canonical integer machine `X86.Ext` does not decode.

* BMI1 (VEX): ANDN, BEXTR, BLSI, BLSMSK, BLSR.
* BMI2 (VEX): BZHI, MULX, PDEP, PEXT, RORX, SARX, SHLX, SHRX.
* ADX: ADCX, ADOX (`66`/`F3 0F 38 F6`).
* MOVBE (`0F 38 F0`/`F1`), memory forms.
* Baseline forms missing from `X86.Ext`: ADC and SBB in every 32/64-bit ALU
  shape, IMUL with an immediate and one-operand IMUL, TEST r/m, imm32,
  PUSH imm, BSF/BSR, BT/BTS/BTR/BTC, SHLD/SHRD, and the register forms of XADD
  and CMPXCHG.

LZCNT, TZCNT, POPCNT, BSWAP, SETcc, CMOVcc, MUL and DIV are already
instructions of `X86.Ext.Instr` and are not repeated here. Operand sizes are
32 and 64 bits (`Ext.Sz`); memory operands are `Ext.Mem`, with the same
addressing forms (base, index, RIP-relative, base-less, FS) as the integer
machine.

Out of scope: 8- and 16-bit forms, the LOCK prefix and the memory forms of
XADD and CMPXCHG (atomics), CMPXCHG8B/16B, and VEX.L = 1 encodings of the BMI
instructions (which raise #UD); none of these is decoded, so they are outside
the model.
-/

@[expose] public section

namespace Silmaril.X86.Features.IntExt

open Silmaril.X86 (Reg)
open Silmaril.X86.Ext (Sz RM Mem)

/-- ADC and SBB. -/
inductive CarryOp where
  | adc | sbb
  deriving DecidableEq, Repr

/-- BT, BTS, BTR, BTC. -/
inductive BitOp where
  | bt | bts | btr | btc
  deriving DecidableEq, Repr

/-- The count of SHLD/SHRD: CL or an imm8. -/
inductive ShdCount where
  | cl
  | imm (n : BitVec 8)
  deriving DecidableEq, Repr

/-- ADCX (carry in and out through CF) and ADOX (through OF). -/
inductive AdxOp where
  | adcx | adox
  deriving DecidableEq, Repr

/-- The VEX-encoded three-operand GPR instructions. The destination is ModRM
`reg`; the roles of `vvvv` and ModRM `r/m` follow the SDM operand tables:

| op | `reg` | `vvvv` | `r/m` |
| --- | --- | --- | --- |
| ANDN | dst | src1 | src2 (dst = ¬src1 ∧ src2) |
| BEXTR | dst | control | src |
| BZHI | dst | index | src |
| PDEP, PEXT | dst | src | mask |
| SARX, SHLX, SHRX | dst | count | src |
| MULX | high half | low half | src (times EDX/RDX) | -/
inductive Vop where
  | andn | bextr | bzhi | pdep | pext | sarx | shlx | shrx | mulx
  deriving DecidableEq, Repr

/-- BLSR (`/1`), BLSMSK (`/2`), BLSI (`/3`). -/
inductive BlsOp where
  | blsr | blsmsk | blsi
  deriving DecidableEq, Repr

/-- The instructions of the lane. -/
inductive Instr where
  /-- `adc`/`sbb r/m, reg` (`11`/`19 /r`). -/
  | carry (op : CarryOp) (sz : Sz) (dst : RM) (src : Reg)
  /-- `adc`/`sbb reg, r/m` (`13`/`1B /r`). -/
  | carryR (op : CarryOp) (sz : Sz) (dst : Reg) (src : RM)
  /-- `adc`/`sbb r/m, imm32` (`81 /2`/`/3 id`), sign-extended. -/
  | carryI (op : CarryOp) (sz : Sz) (dst : RM) (imm : BitVec 32)
  /-- `adc`/`sbb r/m, imm8` (`83 /2`/`/3 ib`), sign-extended. -/
  | carryI8 (op : CarryOp) (sz : Sz) (dst : RM) (imm : BitVec 8)
  /-- `adc`/`sbb eAX/rAX, imm32` (`15`/`1D id`). -/
  | carryA (op : CarryOp) (sz : Sz) (imm : BitVec 32)
  /-- `imul reg, r/m, imm32` (`69 /r id`). -/
  | imulI (sz : Sz) (dst : Reg) (src : RM) (imm : BitVec 32)
  /-- `imul reg, r/m, imm8` (`6B /r ib`). -/
  | imulI8 (sz : Sz) (dst : Reg) (src : RM) (imm : BitVec 8)
  /-- One-operand signed `imul r/m` (`F7 /5`): EDX:EAX or RDX:RAX. -/
  | imul1 (sz : Sz) (src : RM)
  /-- `test r/m, imm32` (`F7 /0 id`). -/
  | testI (sz : Sz) (dst : RM) (imm : BitVec 32)
  /-- `push imm32` (`68 id`), sign-extended to 64 bits. -/
  | pushI (imm : BitVec 32)
  /-- `push imm8` (`6A ib`), sign-extended to 64 bits. -/
  | pushI8 (imm : BitVec 8)
  /-- BSF (`0F BC /r`, `rev = false`) and BSR (`0F BD /r`, `rev = true`). -/
  | scan (rev : Bool) (sz : Sz) (dst : Reg) (src : RM)
  /-- `bt`/`bts`/`btr`/`btc r/m, reg` (`0F A3`/`AB`/`B3`/`BB /r`). -/
  | bit (op : BitOp) (sz : Sz) (dst : RM) (src : Reg)
  /-- `bt`/`bts`/`btr`/`btc r/m, imm8` (`0F BA /4`–`/7 ib`). -/
  | bitI (op : BitOp) (sz : Sz) (dst : RM) (imm : BitVec 8)
  /-- SHLD (`right = false`: `0F A4 /r ib`, `0F A5 /r`) and SHRD (`0F AC`, `0F AD`). -/
  | shd (right : Bool) (sz : Sz) (dst : RM) (src : Reg) (count : ShdCount)
  /-- `xadd reg, reg` (`0F C1 /r`, `mod = 11`). -/
  | xadd (sz : Sz) (dst src : Reg)
  /-- `cmpxchg reg, reg` (`0F B1 /r`, `mod = 11`). -/
  | cmpxchg (sz : Sz) (dst src : Reg)
  /-- `adcx`/`adox reg, r/m` (`66`/`F3 REX? 0F 38 F6 /r`). -/
  | adx (op : AdxOp) (sz : Sz) (dst : Reg) (src : RM)
  /-- `movbe reg, m` (`0F 38 F0 /r`). -/
  | movbeLoad (sz : Sz) (dst : Reg) (src : Mem)
  /-- `movbe m, reg` (`0F 38 F1 /r`). -/
  | movbeStore (sz : Sz) (dst : Mem) (src : Reg)
  /-- The VEX three-operand forms (`Vop`). -/
  | vop (op : Vop) (sz : Sz) (dst : Reg) (v : Reg) (src : RM)
  /-- BLSR/BLSMSK/BLSI `vvvv, r/m` (`VEX.LZ.0F38 F3 /1`–`/3`); `dst` is `vvvv`. -/
  | bls (op : BlsOp) (sz : Sz) (dst : Reg) (src : RM)
  /-- `rorx reg, r/m, imm8` (`VEX.LZ.F2.0F3A F0 /r ib`). -/
  | rorx (sz : Sz) (dst : Reg) (src : RM) (imm : BitVec 8)
  deriving DecidableEq, Repr

end Silmaril.X86.Features.IntExt
