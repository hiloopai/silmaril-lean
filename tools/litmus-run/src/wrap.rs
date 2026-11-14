//! The call wrapper around a thread's corpus bytes.
//!
//! A thread runs as `extern "C" fn(regs: *mut [u64; 16])`:
//!
//! ```text
//! push rbx, rbp, r12, r13, r14, r15     ; System V callee-saved registers
//! push rdi                              ; the register-file pointer
//! mov  r, [rdi + 8*r]   for r ≠ rsp, rdi; then mov rdi, [rdi + 56]
//! <the thread's corpus bytes, unchanged and contiguous>
//! push rax
//! mov  rax, [rsp + 8]                   ; the register-file pointer
//! mov  [rax + 8*r], r   for r ≠ rax, rsp
//! pop  rcx ; mov [rax], rcx             ; the test's final rax
//! pop  rdi ; pop r15, r14, r13, r12, rbp, rbx ; ret
//! ```
//!
//! The corpus code has no branches and only absolute memory operands, so it runs unchanged at
//! any code address. The wrapper touches only the thread's own stack and register file, never
//! a litmus location. `rsp` is not a litmus register (the export rejects tests that use it).
//! The bytes are hand-encoded here; a cargo test checks them against GNU `as`.

/// Register numbers loaded before the test (all but `rsp`, with `rdi` last).
const LOAD_ORDER: [u8; 15] = [0, 1, 2, 3, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 7];
/// Register numbers stored after the test through `rax` (all but `rax` and `rsp`).
const STORE_ORDER: [u8; 14] = [1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

/// `mov r64, [base + disp]` (`store = false`) or `mov [base + disp], r64` (`store = true`),
/// with `base` one of `rax`/`rdi` and `disp < 128`. Uses the short form for `disp = 0`, as gas.
fn mov_mem(store: bool, r: u8, base: u8, disp: u8) -> Vec<u8> {
    debug_assert!(base == 0 || base == 7);
    debug_assert!(disp < 128);
    let rex = 0x48 | ((r >> 3) << 2);
    let op = if store { 0x89 } else { 0x8b };
    let reg = (r & 7) << 3;
    if disp == 0 {
        vec![rex, op, reg | base]
    } else {
        vec![rex, op, 0x40 | reg | base, disp]
    }
}

/// The prologue: save callee-saved registers and the pointer, load the register file.
pub fn prologue() -> Vec<u8> {
    let mut v = vec![
        0x53, 0x55, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57, 0x57,
    ];
    for r in LOAD_ORDER {
        v.extend(mov_mem(false, r, 7, 8 * r));
    }
    v
}

/// The epilogue: store the register file, restore, return.
pub fn epilogue() -> Vec<u8> {
    let mut v = vec![0x50, 0x48, 0x8b, 0x44, 0x24, 0x08];
    for r in STORE_ORDER {
        v.extend(mov_mem(true, r, 0, 8 * r));
    }
    v.push(0x59);
    v.extend(mov_mem(true, 1, 0, 0));
    v.extend([
        0x5f, 0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c, 0x5d, 0x5b, 0xc3,
    ]);
    v
}

/// The entry stub for code at a fixed address: the prologue, then `jmp *0(%rip)` through
/// the absolute address that follows it. The stack is as the prologue left it, so the body
/// at `target` ([`body`]) runs with the same frame as in [`function`].
pub fn stub(target: u64) -> Vec<u8> {
    let mut v = prologue();
    v.extend([0xff, 0x25, 0, 0, 0, 0]);
    v.extend(target.to_le_bytes());
    v
}

/// The bytes placed at a fixed address: the corpus bytes, then the epilogue.
pub fn body(code: &[(String, Vec<u8>)]) -> Vec<u8> {
    let mut v = Vec::new();
    for (_, b) in code {
        v.extend_from_slice(b);
    }
    v.extend(epilogue());
    v
}

/// The full function for one thread: prologue, the corpus bytes, epilogue.
pub fn function(code: &[(String, Vec<u8>)]) -> Vec<u8> {
    let mut v = prologue();
    for (_, b) in code {
        v.extend_from_slice(b);
    }
    v.extend(epilogue());
    v
}

/// The wrapper as AT&T text (for the cross-check with GNU `as`).
#[cfg(test)]
pub fn gas_text(body: &str) -> String {
    use crate::corpus::GPR64;
    let mut s = String::from(
        "push %rbx\npush %rbp\npush %r12\npush %r13\npush %r14\npush %r15\npush %rdi\n",
    );
    for r in LOAD_ORDER {
        s.push_str(&format!("mov {}(%rdi), %{}\n", 8 * r, GPR64[r as usize]));
    }
    s.push_str(body);
    s.push_str("push %rax\nmov 8(%rsp), %rax\n");
    for r in STORE_ORDER {
        s.push_str(&format!("mov %{}, {}(%rax)\n", GPR64[r as usize], 8 * r));
    }
    s.push_str("pop %rcx\nmov %rcx, 0(%rax)\npop %rdi\npop %r15\npop %r14\npop %r13\npop %r12\npop %rbp\npop %rbx\nret\n");
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;

    /// Assemble `text` with `as --64` and return the `.text` bytes (objcopy -O binary).
    fn gas(text: &str) -> Vec<u8> {
        let dir = std::env::temp_dir().join(format!("litmus-run-wrap-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let s = dir.join("w.s");
        let o = dir.join("w.o");
        let b = dir.join("w.bin");
        std::fs::write(&s, format!("\t.text\n{text}")).unwrap();
        let st = Command::new("as")
            .args(["--64", "-o"])
            .arg(&o)
            .arg(&s)
            .status()
            .unwrap();
        assert!(st.success());
        let st = Command::new("objcopy")
            .args(["-O", "binary", "-j", ".text"])
            .arg(&o)
            .arg(&b)
            .status()
            .unwrap();
        assert!(st.success());
        let bytes = std::fs::read(&b).unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        bytes
    }

    #[test]
    fn wrapper_matches_gas() {
        let body = "mfence\n";
        let ours = function(&[("mfence".into(), vec![0x0f, 0xae, 0xf0])]);
        assert_eq!(ours, gas(&gas_text(body)));
        // The fixed-address split: stub = prologue + jmp *0(%rip) + target; body + epilogue.
        let full = gas_text(body);
        let (pro, rest) = full.split_at(full.find("mfence").unwrap());
        let stub_text = format!("{pro}jmp *0(%rip)\n.quad 0x401000\n");
        assert_eq!(stub(0x40_1000), gas(&stub_text));
        assert_eq!(
            super::body(&[("mfence".into(), vec![0x0f, 0xae, 0xf0])]),
            gas(rest)
        );
    }
}
