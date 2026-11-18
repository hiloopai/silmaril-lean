# AMD64Scalar lift provenance

Assembler: `GNU assembler (GNU Binutils for Debian) 2.44`.
Lifter: `pyvex==9.2.179` / `archinfo==9.2.179`, `ArchAMD64()`,
`opt_level=1`, `strict_block_end=True`, `max_bytes=len(section)`, base `0x1000`.
Input: raw `.text.*` sections of `blocks.s` (not linked programs).

## mov

Bytes: `48 89 f8 eb 00`.
Bytes SHA-256: `054e46873ac17c2db4cc04d8a8378566958eb4f3a08520f13e70dce4a1de4685`.
IRSB text (without trailing newline) SHA-256: `be4e935be9c00a87c2520c640e1fbb5b37b217f79a28d9a8f08cd74a20573a56`.

```text
    1000:	48 89 f8             	mov    rax,rdi
    1003:	eb 00                	jmp    0x1005
```

```text
IRSB {
   t0:Ity_I64 t1:Ity_I64

   00 | ------ IMark(0x1000, 3, 0) ------
   01 | t0 = GET:I64(rdi)
   02 | PUT(rax) = t0
   03 | ------ IMark(0x1003, 2, 0) ------
   NEXT: PUT(rip) = 0x0000000000001005; Ijk_Boring
}
```

## add

Bytes: `48 89 f8 48 01 f0 eb 00`.
Bytes SHA-256: `44d8fa852e31e771cc4e0f7ce084d9db176bdaa575ff13e3c6ef0cdf308492f3`.
IRSB text (without trailing newline) SHA-256: `49ebc613ea46a729ae3ab3ad72c296f44f32237677bcc0d0596d77d68a73c9e0`.

```text
    1000:	48 89 f8             	mov    rax,rdi
    1003:	48 01 f0             	add    rax,rsi
    1006:	eb 00                	jmp    0x1008
```

```text
IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64

   00 | ------ IMark(0x1000, 3, 0) ------
   01 | t3 = GET:I64(rdi)
   02 | ------ IMark(0x1003, 3, 0) ------
   03 | t1 = GET:I64(rsi)
   04 | t0 = Add64(t3,t1)
   05 | PUT(cc_op) = 0x0000000000000004
   06 | PUT(cc_dep1) = t3
   07 | PUT(cc_dep2) = t1
   08 | PUT(rax) = t0
   09 | ------ IMark(0x1006, 2, 0) ------
   NEXT: PUT(rip) = 0x0000000000001008; Ijk_Boring
}
```

## je

Bytes: `48 39 f7 74 04`.
Bytes SHA-256: `91a6cea33cb52b4a1abeb86e46a5f48fcbd6302a4113bca9302725b6bb4f03ac`.
IRSB text (without trailing newline) SHA-256: `594a2d560065c499fc8fc3d97bc9298535ce73c0dc1b24b1a206d2d3f461f2bb`.

```text
    1000:	48 39 f7             	cmp    rdi,rsi
    1003:	74 04                	je     0x1009
```

```text
IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I1 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I1 t12:Ity_I1

   00 | ------ IMark(0x1000, 3, 0) ------
   01 | t2 = GET:I64(rdi)
   02 | t1 = GET:I64(rsi)
   03 | PUT(cc_op) = 0x0000000000000008
   04 | PUT(cc_dep1) = t2
   05 | PUT(cc_dep2) = t1
   06 | PUT(rip) = 0x0000000000001003
   07 | ------ IMark(0x1003, 2, 0) ------
   08 | t11 = CmpEQ64(t2,t1)
   09 | t10 = 1Uto64(t11)
   10 | t8 = t10
   11 | t12 = 64to1(t8)
   12 | t3 = t12
   13 | if (t3) { PUT(rip) = 0x1009; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000001005; Ijk_Boring
}
```

## jne

Bytes: `48 39 f7 75 04`.
Bytes SHA-256: `ec0450f2d2c57889a074be150d18de4fa08c53b992ace8f281a24c79d0123d95`.
IRSB text (without trailing newline) SHA-256: `fe0d43b3f852c58cddd71228178f7a7bb325f31df199cec5e17f83676a024a03`.

```text
    1000:	48 39 f7             	cmp    rdi,rsi
    1003:	75 04                	jne    0x1009
```

```text
IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I1 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I1 t12:Ity_I1

   00 | ------ IMark(0x1000, 3, 0) ------
   01 | t2 = GET:I64(rdi)
   02 | t1 = GET:I64(rsi)
   03 | PUT(cc_op) = 0x0000000000000008
   04 | PUT(cc_dep1) = t2
   05 | PUT(cc_dep2) = t1
   06 | PUT(rip) = 0x0000000000001003
   07 | ------ IMark(0x1003, 2, 0) ------
   08 | t11 = CmpEQ64(t2,t1)
   09 | t10 = 1Uto64(t11)
   10 | t8 = t10
   11 | t12 = 64to1(t8)
   12 | t3 = t12
   13 | if (t3) { PUT(rip) = 0x1005; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000001009; Ijk_Boring
}
```
