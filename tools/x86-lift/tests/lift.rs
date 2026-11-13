//! `lift` on hand-picked encodings: each accepted instruction maps into the
//! model and re-encodes to exactly its own bytes, each refused one is reported
//! with its address, and lengths and fall-through addresses are exact.

use lift_x86::cfg::Flow;
use lift_x86::ext::{Base, Cond, Index, Instr, Mem, RM, Reg, Sz};

/// Bytes from a hex string.
fn from_hex(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd number of hex digits: {s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn lifted_byte_offsets_survive_address_wrap() {
    let raw = [0x90, 0x90, 0xc3];
    let base = u64::MAX - 1;
    let lifted = lift_x86::lift(&raw, base).unwrap();
    assert_eq!(
        lifted.iter().map(|i| i.addr).collect::<Vec<_>>(),
        [base, u64::MAX, 0]
    );
    assert_eq!(
        lifted
            .iter()
            .flat_map(|i| i.bytes.clone())
            .collect::<Vec<_>>(),
        raw
    );
    assert_eq!(lifted[2].next(), 1);
    // A failure after wrap still identifies the original unsupported bytes.
    let bad = [0x90, 0x90, 0x0f, 0xa2];
    assert_eq!(
        lift_x86::lift(&bad, base).unwrap_err().to_string(),
        "0x0: 0fa2 (cpuid): `Cpuid` is not in the Ext model"
    );
}

#[test]
fn byte_test_immediate_encodings_and_lengths() {
    let mem = |base, index, disp| RM::Mem(Mem { base, index, disp });
    let cases = [
        // A REX-extended byte register.
        ("41f6c401", Instr::TestI8(RM::Reg(Reg::R12), 1)),
        // Keep accumulator and group encodings distinct.
        ("f6c080", Instr::TestI8(RM::Reg(Reg::Rax), 0x80)),
        ("a880", Instr::TestA8(0x80)),
        ("40f6c4ff", Instr::TestI8(RM::Reg(Reg::Rsp), 0xff)),
        (
            "f640f080",
            Instr::TestI8(mem(Base::Reg(Reg::Rax), None, 0xfffffff0), 0x80),
        ),
        (
            "43f644a1f0ff",
            Instr::TestI8(
                mem(
                    Base::Reg(Reg::R9),
                    Some(Index {
                        reg: Reg::R12,
                        scale: 2,
                    }),
                    0xfffffff0,
                ),
                0xff,
            ),
        ),
        (
            "64f604252800000080",
            Instr::TestI8(mem(Base::Fs, None, 0x28), 0x80),
        ),
        (
            "f60534120000ff",
            Instr::TestI8(mem(Base::Rip, None, 0x1234), 0xff),
        ),
    ];
    for (hex, expected) in cases {
        let mut raw = from_hex(hex);
        assert_eq!(lift_x86::encode::encode(&expected), raw, "{hex}");
        let next = 0x401df7 + raw.len() as u64;
        raw.push(0xc3);
        let lifted = lift_x86::lift(&raw, 0x401df7).unwrap();
        assert_eq!(lifted.len(), 2);
        assert_eq!(lifted[0].instr, expected);
        assert_eq!(lifted[0].next(), next);
        assert_eq!(lifted[1].addr, next);
        assert_eq!(lifted[1].instr, Instr::Ret);
    }
    for dst in Reg::ALL {
        for imm in [0, 0x7f, 0x80, 0xff] {
            let expected = Instr::TestI8(RM::Reg(dst), imm);
            let mut raw = Vec::new();
            let rex = 0x40 | u8::from(dst.hi());
            if rex != 0x40 || dst.needs_rex_byte() {
                raw.push(rex);
            }
            raw.extend([0xf6, 0xc0 | dst.lo(), imm]);
            assert_eq!(lift_x86::encode::encode(&expected), raw);
            assert_eq!(lift_x86::lift(&raw, 0).unwrap()[0].instr, expected);
        }
    }
    assert_eq!(
        Instr::TestI8(RM::Reg(Reg::R12), 1).lean(),
        ".testI8 (.reg .r12) 0x1"
    );
    assert_eq!(Instr::TestA8(0x80).lean(), ".testA8 0x80");
    assert_eq!(Instr::TestI8(RM::Reg(Reg::Rax), 0).form(), "testI8");
    assert_eq!(Instr::TestA8(0).form(), "testA8");
}

#[test]
fn byte_test_immediate_rejection_controls() {
    for high in 4..=7 {
        let error = lift_x86::lift(&[0xf6, 0xc0 | high, 1], 0)
            .unwrap_err()
            .to_string();
        assert!(error.contains("high-byte register"), "{error}");
    }
    for digit in 1..8 {
        assert!(lift_x86::lift(&[0xf6, 0xc0 | digit << 3, 1], 0).is_err());
    }
    for hex in [
        "40f6c001",
        "48f6c001",
        "66f6c001",
        "40a801",
        "f6800000000001",
    ] {
        let raw = from_hex(hex);
        let error = lift_x86::lift(&raw, 0).unwrap_err().to_string();
        assert!(error.contains("canonical encoding"), "{hex}: {error}");
    }
    for hex in ["f6c0", "41f6c4", "f605", "a8", "f7c001000000"] {
        let raw = from_hex(hex);
        assert!(lift_x86::lift(&raw, 0).is_err(), "{hex}");
    }
}

#[test]
fn mul_register_and_memory_encodings() {
    let mem = |base, index, disp| RM::Mem(Mem { base, index, disp });
    let cases = [
        // Register operands, including the implicit-result registers.
        ("48f7e7", Instr::Mul(Sz::Q, RM::Reg(Reg::Rdi))),
        ("f7e0", Instr::Mul(Sz::D, RM::Reg(Reg::Rax))),
        ("48f7e0", Instr::Mul(Sz::Q, RM::Reg(Reg::Rax))),
        ("f7e2", Instr::Mul(Sz::D, RM::Reg(Reg::Rdx))),
        ("48f7e2", Instr::Mul(Sz::Q, RM::Reg(Reg::Rdx))),
        ("41f7e0", Instr::Mul(Sz::D, RM::Reg(Reg::R8))),
        ("49f7e7", Instr::Mul(Sz::Q, RM::Reg(Reg::R15))),
        ("f720", Instr::Mul(Sz::D, mem(Base::Reg(Reg::Rax), None, 0))),
        (
            "48f76424f0",
            Instr::Mul(Sz::Q, mem(Base::Reg(Reg::Rsp), None, 0xfffffff0)),
        ),
        (
            "4bf764a1f0",
            Instr::Mul(
                Sz::Q,
                mem(
                    Base::Reg(Reg::R9),
                    Some(Index {
                        reg: Reg::R12,
                        scale: 2,
                    }),
                    0xfffffff0,
                ),
            ),
        ),
        (
            "6448f7242528000000",
            Instr::Mul(Sz::Q, mem(Base::Fs, None, 0x28)),
        ),
        (
            "48f72534120000",
            Instr::Mul(Sz::Q, mem(Base::Rip, None, 0x1234)),
        ),
    ];
    for (hex, expected) in cases {
        let mut raw = from_hex(hex);
        assert_eq!(lift_x86::encode::encode(&expected), raw, "{hex}");
        let next = 0x4019f9 + raw.len() as u64;
        raw.push(0xc3);
        let lifted = lift_x86::lift(&raw, 0x4019f9).unwrap();
        assert_eq!(lifted.len(), 2);
        assert_eq!(lifted[0].instr, expected);
        assert_eq!(lifted[0].next(), next);
        assert_eq!(lifted[1].addr, next);
        assert_eq!(lifted[1].instr, Instr::Ret);
    }
    for sz in [Sz::D, Sz::Q] {
        for src in Reg::ALL {
            let expected = Instr::Mul(sz, RM::Reg(src));
            let rex = 0x40 | (u8::from(sz.w()) << 3) | u8::from(src.hi());
            let mut raw = Vec::new();
            if rex != 0x40 {
                raw.push(rex);
            }
            raw.extend([0xf7, 0xe0 | src.lo()]);
            assert_eq!(lift_x86::encode::encode(&expected), raw);
            assert_eq!(lift_x86::lift(&raw, 0).unwrap()[0].instr, expected);
        }
    }
    assert_eq!(
        Instr::Mul(Sz::Q, RM::Reg(Reg::Rdi)).lean(),
        ".mul .q (.reg .rdi)"
    );
    assert_eq!(Instr::Mul(Sz::D, RM::Reg(Reg::Rdx)).form(), "mul");
}

#[test]
fn mul_rejection_and_group_mutation_controls() {
    // No byte/word MUL or signed one-operand IMUL support is inferred.
    for hex in ["f6e0", "66f7e0", "f7e8", "48f7e8", "f7", "48f7", "48f725"] {
        let raw = from_hex(hex);
        assert!(lift_x86::lift(&raw, 0).is_err(), "{hex}");
    }
    for hex in ["40f7e0", "6648f7e0", "f7a000000000"] {
        let raw = from_hex(hex);
        let error = lift_x86::lift(&raw, 0).unwrap_err().to_string();
        assert!(error.contains("canonical encoding"), "{hex}: {error}");
    }
    // Changing /4 to existing /6 remains DIV, never a MUL transcription.
    assert_eq!(
        lift_x86::lift(&[0xf7, 0xf0], 0).unwrap()[0].instr,
        Instr::Div(Sz::D, false, RM::Reg(Reg::Rax))
    );
}

#[test]
fn cmov_register_and_memory_encodings() {
    let mem = |base, index, disp| RM::Mem(Mem { base, index, disp });
    let cases = [
        (
            "490f43d4",
            Instr::Cmov(Sz::Q, Cond::Ae, Reg::Rdx, RM::Reg(Reg::R12)),
        ),
        (
            "440f4dca",
            Instr::Cmov(Sz::D, Cond::Ge, Reg::R9, RM::Reg(Reg::Rdx)),
        ),
        (
            "0f444c24f0",
            Instr::Cmov(
                Sz::D,
                Cond::E,
                Reg::Rcx,
                mem(Base::Reg(Reg::Rsp), None, 0xfffffff0),
            ),
        ),
        (
            "4d0f454c24f0",
            Instr::Cmov(
                Sz::Q,
                Cond::Ne,
                Reg::R9,
                mem(Base::Reg(Reg::R12), None, 0xfffffff0),
            ),
        ),
        (
            "4b0f474ca1f0",
            Instr::Cmov(
                Sz::Q,
                Cond::A,
                Reg::Rcx,
                mem(
                    Base::Reg(Reg::R9),
                    Some(Index {
                        reg: Reg::R12,
                        scale: 2,
                    }),
                    0xfffffff0,
                ),
            ),
        ),
        (
            "64480f4f042528000000",
            Instr::Cmov(Sz::Q, Cond::G, Reg::Rax, mem(Base::Fs, None, 0x28)),
        ),
        (
            "480f4c0534120000",
            Instr::Cmov(Sz::Q, Cond::L, Reg::Rax, mem(Base::Rip, None, 0x1234)),
        ),
    ];
    for (hex, expected) in cases {
        let mut raw = from_hex(hex);
        assert_eq!(lift_x86::encode::encode(&expected), raw, "{hex}");
        let next = 0x401900 + raw.len() as u64;
        raw.push(0xc3);
        let lifted = lift_x86::lift(&raw, 0x401900).unwrap();
        assert_eq!(lifted.len(), 2);
        assert_eq!(lifted[0].instr, expected);
        assert_eq!(lifted[0].next(), next);
        assert_eq!(lifted[1].addr, next);
        assert_eq!(lifted[1].instr, Instr::Ret);
    }
    let first = Instr::Cmov(Sz::Q, Cond::Ae, Reg::Rdx, RM::Reg(Reg::R12));
    assert_eq!(first.lean(), ".cmov .q .ae .rdx (.reg .r12)");
    assert_eq!(first.form(), "cmov");
}

#[test]
fn cmov_all_conditions_widths_and_registers() {
    for sz in [Sz::D, Sz::Q] {
        for code in 0..16 {
            for dst in Reg::ALL {
                for src in Reg::ALL {
                    let expected = Instr::Cmov(sz, Cond::of_code(code), dst, RM::Reg(src));
                    let rex = 0x40
                        | (u8::from(sz.w()) << 3)
                        | (u8::from(dst.hi()) << 2)
                        | u8::from(src.hi());
                    let mut raw = Vec::new();
                    if rex != 0x40 {
                        raw.push(rex);
                    }
                    raw.extend([0x0f, 0x40 | code, 0xc0 | dst.lo() << 3 | src.lo()]);
                    assert_eq!(lift_x86::encode::encode(&expected), raw);
                    let lifted = lift_x86::lift(&raw, 0).unwrap();
                    assert_eq!(lifted.len(), 1);
                    assert_eq!(lifted[0].instr, expected);
                }
            }
        }
    }
}

#[test]
fn cmov_rejection_controls() {
    for hex in ["660f43d4", "40660f43d4", "0f43", "490f43", "490f4305"] {
        let raw = from_hex(hex);
        assert!(lift_x86::lift(&raw, 0).is_err(), "{hex}");
    }
    // Valid machine encodings with redundant REX or an overwide zero
    // displacement still fail the unchanged canonical correspondence check.
    for hex in ["400f43d4", "0f438800000000"] {
        let raw = from_hex(hex);
        let error = lift_x86::lift(&raw, 0).unwrap_err().to_string();
        assert!(error.contains("canonical encoding"), "{hex}: {error}");
    }
}

#[test]
fn byte_cmp_immediate_encodings_and_lengths() {
    let mem = |base, index, disp| RM::Mem(Mem { base, index, disp });
    let cases = [
        // Register and accumulator forms with small and sign-boundary immediates.
        ("80f95c", Instr::CmpI8(RM::Reg(Reg::Rcx), 0x5c)),
        ("3c09", Instr::CmpA8(9)),
        ("80f980", Instr::CmpI8(RM::Reg(Reg::Rcx), 0x80)),
        ("3c5b", Instr::CmpA8(0x5b)),
        // The two accumulator spellings remain distinct canonical forms.
        ("80f880", Instr::CmpI8(RM::Reg(Reg::Rax), 0x80)),
        ("3c80", Instr::CmpA8(0x80)),
        ("4080fcff", Instr::CmpI8(RM::Reg(Reg::Rsp), 0xff)),
        ("4180f87f", Instr::CmpI8(RM::Reg(Reg::R8), 0x7f)),
        (
            "8078f080",
            Instr::CmpI8(mem(Base::Reg(Reg::Rax), None, 0xfffffff0), 0x80),
        ),
        (
            "43807ca1f0ff",
            Instr::CmpI8(
                mem(
                    Base::Reg(Reg::R9),
                    Some(Index {
                        reg: Reg::R12,
                        scale: 2,
                    }),
                    0xfffffff0,
                ),
                0xff,
            ),
        ),
        (
            "64803c252800000000",
            Instr::CmpI8(mem(Base::Fs, None, 0x28), 0),
        ),
        (
            "803d3412000080",
            Instr::CmpI8(mem(Base::Rip, None, 0x1234), 0x80),
        ),
    ];
    for (hex, expected) in cases {
        let mut raw = from_hex(hex);
        assert_eq!(lift_x86::encode::encode(&expected), raw, "{hex}");
        let len = raw.len() as u64;
        raw.push(0xc3);
        let lifted = lift_x86::lift(&raw, 0x401033).unwrap();
        assert_eq!(lifted.len(), 2, "{hex}");
        assert_eq!(lifted[0].instr, expected);
        assert_eq!(lifted[0].len(), len);
        assert_eq!(lifted[1].addr, 0x401033 + len);
        assert_eq!(lifted[1].instr, Instr::Ret);
    }
    // Immediates remain raw bytes, including the signed boundary and -1.
    for reg in Reg::ALL {
        for imm in [0, 0x7f, 0x80, 0xff] {
            let expected = Instr::CmpI8(RM::Reg(reg), imm);
            let lifted = lift_x86::lift(&lift_x86::encode::encode(&expected), 0).unwrap();
            assert_eq!(lifted[0].instr, expected);
        }
    }
    assert_eq!(
        Instr::CmpI8(RM::Reg(Reg::Rcx), 0x80).lean(),
        ".cmpI8 (.reg .rcx) 0x80"
    );
    assert_eq!(Instr::CmpA8(0x80).lean(), ".cmpA8 0x80");
    assert_eq!(Instr::CmpI8(RM::Reg(Reg::Rcx), 0).form(), "cmpI8");
    assert_eq!(Instr::CmpA8(0).form(), "cmpA8");
    let mutation = lift_x86::lift(&[0x80, 0xf9, 0x81], 0).unwrap();
    assert_eq!(mutation[0].instr, Instr::CmpI8(RM::Reg(Reg::Rcx), 0x81));
}

#[test]
fn byte_cmp_immediate_rejection_controls() {
    for high in 4..=7 {
        let error = lift_x86::lift(&[0x80, 0xf8 | high, 1], 0)
            .unwrap_err()
            .to_string();
        assert!(error.contains("high-byte register"), "{error}");
    }
    for hex in [
        "4080f95c",
        "4880f95c",
        "6680f95c",
        "403c01",
        "80b80000000000",
    ] {
        let raw = from_hex(hex);
        let error = lift_x86::lift(&raw, 0).unwrap_err().to_string();
        assert!(error.contains("canonical encoding"), "{hex}: {error}");
    }
    // No other 80 /digit ALU or register/register byte CMP was added.
    for digit in 0..7 {
        assert!(lift_x86::lift(&[0x80, 0xc1 | digit << 3, 1], 0).is_err());
    }
    for hex in ["38c1", "3ac1", "80f9", "3c"] {
        assert!(lift_x86::lift(&from_hex(hex), 0).is_err());
    }
}

#[test]
fn byte_test_encodings_and_exact_lengths() {
    // These are independent x86 encodings, rather than inputs built with the
    // encoder under test.
    let cases: &[(&[u8], Instr)] = &[
        (&[0x84, 0xc9], Instr::Test8(RM::Reg(Reg::Rcx), Reg::Rcx)),
        (
            &[0x40, 0x84, 0xe4],
            Instr::Test8(RM::Reg(Reg::Rsp), Reg::Rsp),
        ),
        (
            &[0x40, 0x84, 0xe0],
            Instr::Test8(RM::Reg(Reg::Rax), Reg::Rsp),
        ),
        (
            &[0x40, 0x84, 0xc4],
            Instr::Test8(RM::Reg(Reg::Rsp), Reg::Rax),
        ),
        (
            &[0x44, 0x84, 0xc1],
            Instr::Test8(RM::Reg(Reg::Rcx), Reg::R8),
        ),
        (
            &[0x41, 0x84, 0xc8],
            Instr::Test8(RM::Reg(Reg::R8), Reg::Rcx),
        ),
        (&[0x45, 0x84, 0xc8], Instr::Test8(RM::Reg(Reg::R8), Reg::R9)),
        (
            &[0x84, 0x08],
            Instr::Test8(
                RM::Mem(Mem {
                    base: Base::Reg(Reg::Rax),
                    index: None,
                    disp: 0,
                }),
                Reg::Rcx,
            ),
        ),
        (
            &[0x84, 0x0c, 0x24],
            Instr::Test8(
                RM::Mem(Mem {
                    base: Base::Reg(Reg::Rsp),
                    index: None,
                    disp: 0,
                }),
                Reg::Rcx,
            ),
        ),
        (
            &[0x46, 0x84, 0x4c, 0xa0, 0xf0],
            Instr::Test8(
                RM::Mem(Mem {
                    base: Base::Reg(Reg::Rax),
                    index: Some(Index {
                        reg: Reg::R12,
                        scale: 2,
                    }),
                    disp: 0xfffffff0,
                }),
                Reg::R9,
            ),
        ),
        (
            &[0x64, 0x84, 0x0c, 0x25, 0x28, 0, 0, 0],
            Instr::Test8(
                RM::Mem(Mem {
                    base: Base::Fs,
                    index: None,
                    disp: 0x28,
                }),
                Reg::Rcx,
            ),
        ),
        (
            &[0x64, 0x44, 0x84, 0x0c, 0xcd, 0x28, 0, 0, 0],
            Instr::Test8(
                RM::Mem(Mem {
                    base: Base::Fs,
                    index: Some(Index {
                        reg: Reg::Rcx,
                        scale: 3,
                    }),
                    disp: 0x28,
                }),
                Reg::R9,
            ),
        ),
        (
            &[0x84, 0x0d, 0x34, 0x12, 0, 0],
            Instr::Test8(
                RM::Mem(Mem {
                    base: Base::Rip,
                    index: None,
                    disp: 0x1234,
                }),
                Reg::Rcx,
            ),
        ),
    ];
    for (raw, expected) in cases {
        assert_eq!(lift_x86::encode::encode(expected), *raw, "{expected:?}");
        // Following with RET catches accidental displacement/immediate bytes
        // or length drift.
        let mut bytes = raw.to_vec();
        bytes.push(0xc3);
        let base = 0x40102f;
        let lifted = lift_x86::lift(&bytes, base).unwrap();
        assert_eq!(lifted.len(), 2, "{raw:02x?}");
        assert_eq!(lifted[0].instr, *expected);
        assert_eq!(lifted[0].bytes, *raw);
        assert_eq!(lifted[0].next(), base + raw.len() as u64);
        assert_eq!(lifted[1].addr, lifted[0].next());
        assert_eq!(lifted[1].instr, Instr::Ret);
        assert_eq!(lifted[1].next(), base + bytes.len() as u64);
    }
    let first = Instr::Test8(RM::Reg(Reg::Rcx), Reg::Rcx);
    assert_eq!(first.lean(), ".test8 (.reg .rcx) .rcx");
    assert_eq!(first.form(), "test8");
}

#[test]
fn byte_test_register_matrix() {
    // Cover both byte fields, particularly the REX change from AH..BH to
    // SPL..DIL and independent REX.R/REX.B extensions to R8B..R15B.
    for dst in Reg::ALL {
        for src in Reg::ALL {
            let instr = Instr::Test8(RM::Reg(dst), src);
            let raw = lift_x86::encode::encode(&instr);
            let lifted = lift_x86::lift(&raw, 0).unwrap();
            assert_eq!(lifted.len(), 1);
            assert_eq!(lifted[0].instr, instr);
        }
    }
}

#[test]
fn byte_test_rejects_high_bytes_and_noncanonical_prefixes() {
    for high in 4..=7 {
        for modrm in [0xc0 | high, 0xc0 | high << 3] {
            let raw = [0x84, modrm];
            let error = lift_x86::lift(&raw, 0x40102f).unwrap_err().to_string();
            assert!(error.contains("high-byte register"), "{raw:02x?}: {error}");
            assert!(error.contains("0x40102f"), "{error}");
        }
    }
    // The same ModRM bytes with REX select low bytes and are covered above.
    // Redundant prefixes are machine-valid, but the canonical decoder must
    // still reject them instead of silently dropping bytes.
    for raw in [
        &[0x40, 0x84, 0xc9][..],
        &[0x48, 0x84, 0xc9],
        &[0x66, 0x84, 0xc9],
    ] {
        let error = lift_x86::lift(raw, 0x40102f).unwrap_err().to_string();
        assert!(error.contains("canonical encoding is 84c9"), "{error}");
    }
    // Wider r/m immediate TEST and truncated instructions remain unsupported.
    for raw in [&[0xf7, 0xc1, 1, 0, 0, 0][..], &[0x84]] {
        assert!(lift_x86::lift(raw, 0x40102f).is_err(), "{raw:02x?}");
    }
}

#[test]
fn gcc_add3_listings() {
    // gcc 13.3.0 at -O0 and -O2 (the flags of tools/c-tv) on
    // `int add3(int a, int b, int c) { int s = a + b; int t = s + c; return t; }`.
    // Each line: offset, length, the Lean term of the instruction.
    let o0 = "554889e5897dec8975e88955e48b55ec8b45e801d08945fc8b55fc8b45e401d08945f88b45f85dc3";
    let want_o0 = "\
0x0 1 .push .rbp
0x1 3 .mov .q (.reg .rbp) .rsp
0x4 3 .mov .d (.mem (Mem.ofReg .rbp none 0xffffffec)) .rdi
0x7 3 .mov .d (.mem (Mem.ofReg .rbp none 0xffffffe8)) .rsi
0xa 3 .mov .d (.mem (Mem.ofReg .rbp none 0xffffffe4)) .rdx
0xd 3 .load .d .rdx (Mem.ofReg .rbp none 0xffffffec)
0x10 3 .load .d .rax (Mem.ofReg .rbp none 0xffffffe8)
0x13 2 .alu .d .add (.reg .rax) .rdx
0x15 3 .mov .d (.mem (Mem.ofReg .rbp none 0xfffffffc)) .rax
0x18 3 .load .d .rdx (Mem.ofReg .rbp none 0xfffffffc)
0x1b 3 .load .d .rax (Mem.ofReg .rbp none 0xffffffe4)
0x1e 2 .alu .d .add (.reg .rax) .rdx
0x20 3 .mov .d (.mem (Mem.ofReg .rbp none 0xfffffff8)) .rax
0x23 3 .load .d .rax (Mem.ofReg .rbp none 0xfffffff8)
0x26 1 .pop .rbp
0x27 1 .ret";
    let o2 = "01f78d0417c3";
    let want_o2 = "\
0x0 2 .alu .d .add (.reg .rdi) .rsi
0x2 3 .lea .d .rax (Mem.ofReg .rdi (some (ix .rdx 0)) 0x0)
0x5 1 .ret";
    for (code, want) in [(o0, want_o0), (o2, want_o2)] {
        let code = from_hex(code);
        let lifted = lift_x86::lift(&code, 0).unwrap();
        let got: Vec<String> = lifted
            .iter()
            .map(|x| format!("{:#x} {} {}", x.addr, x.len(), x.instr.lean()))
            .collect();
        assert_eq!(got.join("\n"), want);
        assert_eq!(lifted.last().unwrap().next(), code.len() as u64);
    }
    assert_eq!(
        lift_x86::lift(&from_hex(o0), 0).unwrap()[2].asm,
        "mov %edi,-0x14(%rbp)"
    );
}

#[test]
fn flow_targets_are_relative_to_the_next_instruction() {
    let base = 0x401000;
    // jmp rel32 -2, jne rel8 -2, call rel32 0, ud2, ret
    let raw = from_hex("e9feffffff75fee8000000000f0bc3");
    let lifted = lift_x86::lift(&raw, base).unwrap();
    let flows: Vec<Flow> = lifted.iter().map(|x| x.flow()).collect();
    assert_eq!(
        flows,
        [
            Flow::Jump(base + 3),
            Flow::Branch(base + 5),
            Flow::Call(base + 12),
            Flow::Halt,
            Flow::Ret,
        ]
    );
    let n = lifted[1].node();
    assert_eq!((n.addr, n.len), (base + 5, 2));
    assert_eq!(n.cfg_targets(), [base + 5, base + 7]);
    assert_eq!(lifted[2].node().cfg_targets(), [base + 12]);
    // Targets wrap modulo 2^64: jmp rel8 -4 at 1.
    let wrapped = lift_x86::lift(&from_hex("ebfc"), 1).unwrap();
    assert_eq!(wrapped[0].flow(), Flow::Jump(u64::MAX));
    assert_eq!(
        lift_x86::lift(&from_hex("90"), 0).unwrap()[0].flow(),
        Flow::Next
    );
}
