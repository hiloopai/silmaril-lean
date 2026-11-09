module

public import Silmaril.X86.BlockCert.Ext8.Thms
public import Silmaril.Proofs.X86.BlockCert.Ext8.More

/-!
# More `Ext8` instruction and block-end lemmas (header)

Re-exports `Silmaril.Proofs.X86.BlockCert.Ext8.More`, all in namespace
`Silmaril.X86.BlockCert8`:

* register effects (`Eff`): `not_d`, `lea_q`, `nop_eff`, `and_d_i8`, `add_q_rr`, `xor_q_rr`,
  `xor_d_self`, `movI32_eff`, and `test_zero` (`test x,x` sets ZF iff `x = 0`);
* block ends: `test_je_end`, `test_je8_end` (`test x,x; je`), `cmpi8_jbe_end`
  (`cmp $k,x; jbe`, unsigned `x ≤ k`), `ret_end` (`ret` with a readable return address).

The `mov`/`xor8`/`movzb`/`shr`/`xor m64`/`add imm8` effects and `cmp; jne` ends are in
`BlockCert/Ext8/Thms.lean`.
-/
