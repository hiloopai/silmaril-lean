module

public import Silmaril.X86.Concurrency.Cir.Rc.Defs
public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs
public import Silmaril.X86.Concurrency.Cir.Rc.Code.Defs

/-!
# Translation validation of the refcount idioms into CIR's derived ops

gcc 13.3.0 `-O2` compiles the library of `examples/litmus-c/rc/rc.c` to

```
rc_clone:    lock add DWORD PTR [rdi], 1                  ; rc_inc, inlined
rc_drop:     lock sub DWORD PTR [rdi], 1 ; je cold ; ret  ; rc_dec, zero flag tested
rc_publish:  mov eax, [rdi+4] ; mov [rsi], eax ; lock sub DWORD PTR [rdi], 1 ; je cold ; ret
rc_share2:   lock add [rdi], 1 ; lock add [rdi], 1 ; lock sub [rdi], 1 ; je cold ; ret
cold:        jmp rc_drop_slow                              ; after the ret: the outlined path
```

Neither of the checkers covers this. The straight-line walk has the clobber set that a
`lock add` needs (CIR's `rmw` names a destination register, x86 writes none), but no branches;
The CFG checker has branches but compares registers exactly and has no locked ALU forms. This
checker (`rcTv`) is the small combination the idioms need:

* a **clobber set** `K`, fixed by the certificate: the scratch registers that CIR's `rmw`
  writes and x86 does not. Registers outside `K` agree;
* the forms (32-bit): `lock add/sub/and/or/xor [m], imm` as `rmw d _ 4 (op o) e c` with `d ∈ K`
  (after which the zero flag is `zfOf o d c`, the CIR expression of the 32-bit result being
  `0`), `mov r, [m]` as `load`, `mov [m], r` as `store`; memory operands `[r + disp]` whose
  registers are not clobbered (`addrX`);
* **exit edges**: a `je rel8` whose target lies beyond the function's `ret` (the cold block,
  which jumps to `rc_drop_slow`) becomes `ite c slow skip` with `c` the zero-flag expression of
  the instruction before it. `slow` is a parameter of the CIR program: the outlined cold path
  is not validated here (it is `free`, the allocator's code), it is a hole that the CSL proof
  fills with `Alloc.free`.

Modes are compared away (`Stmt.demode`), as in the translation validators.
The CIR program of a certificate is
`Stmt.block` of its items, so the four pinned functions validate into exactly `rcInc`,
`rcDrop` and their sequences (`rcDrop_body` etc.).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Rc.Tv

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Concurrency.Cir.Tv (XThread XMem fetchAt binOf)
open Silmaril.X86.Concurrency.Cir.TvCfg (addrX jtarget)

/-- A certificate item: one x86 instruction and its CIR statement, or a `je` out of the code
(the cold path) with its condition. -/
inductive RItem where
  | op (s : Stmt)
  | exit (c : Expr)

/-- A certificate: the clobbered registers and one item per instruction. -/
structure RCert where
  K : List Reg
  items : List RItem

/-- The CIR statement of an item, with the cold path `slow`. -/
def RItem.stmt (slow : Stmt) : RItem → Stmt
  | .op s => s
  | .exit c => .ite c slow .skip

/-- **The CIR program of a certificate**, with the cold path `slow`. -/
def RCert.body (c : RCert) (slow : Stmt) : Stmt := Stmt.block (c.items.map (RItem.stmt slow))

/-- The address of a memory operand with a register base and no index, if no register of it
is clobbered. -/
def addrK (K : List Reg) (a : XMem) : Option Expr :=
  match a.index, addrX a with
  | none, some e => if e.regs.all (· ∉ K) then some e else none
  | _, _ => none

/-- **Check one instruction** against a CIR statement (up to modes): the zero-flag fact after
it, if the check passes. -/
def chkOp (K : List Reg) (i : Atomic9.Instr) (s : Stmt) : Option (Option Expr) :=
  match i, s.demode with
  | .new (.lockAluI .d op a imm), .rmw d .rlx 4 (.op o) e (.lit c) =>
    if d ∈ K ∧ addrK K a = some e ∧ binOf op = some o ∧ c = imm.toNat then some (some (zfOf o d c))
    else none
  | .open9 (.ext8 (.base (.load .d dst a))), .load d .rlx 4 .wb e =>
    if d = dst ∧ addrK K a = some e then some none else none
  | .open9 (.ext8 (.base (.mov .d (.mem a) src))), .store .rlx 4 .wb e (.reg r) =>
    if r = src ∧ src ∉ K ∧ addrK K a = some e then some none else none
  | _, _ => none

/-- **The walk** from offset `o` with the zero-flag fact `zf`: the exit offsets, if every item
checks and the walk ends exactly at the end of the code. -/
def walk (t : XThread) (K : List Reg) : Option Expr → Nat → List RItem → Option (List Nat)
  | _, o, [] => if o = t.code.length then some [] else none
  | zf, o, it :: its =>
    match fetchAt t o with
    | none => none
    | some (i, n) =>
      if 0 < n then
        match it with
        | .op s =>
          match chkOp K i s with
          | some zf' => walk t K zf' (o + n) its
          | none => none
        | .exit c =>
          match i with
          | .open9 (.ext8 (.base (.jcc8 .e rel))) =>
            if zf = some c ∧ t.code.length < jtarget o n rel then
              (walk t K none (o + n) its).map (jtarget o n rel :: ·)
            else none
          | _ => none
      else none

/-- **The checker**: the exit offsets (all beyond the code), or `none`. -/
def rcTv (t : XThread) (c : RCert) : Option (List Nat) :=
  if t.code.length < 2 ^ 64 then walk t c.K none 0 c.items else none

/-! ## The pinned functions -/

/-- An x86 thread of a pinned function, at `0x1000`. -/
def thr (code : List (BitVec 8)) : XThread :=
  ⟨0x1000, code, [], Silmaril.X86.Litmus.initCore 0x1000 []⟩

/-- `[rdi + d]`, as `addrX` writes it. -/
def atRdi (d : Nat) : Expr := .bin .add (.bin .add (.reg .rdi) (.lit 0)) (.lit d)

/-- The scratch register of the certificates. -/
def scratch : Reg := .r11

/-- `rc_clone`: `rcInc`. -/
def cloneCert : RCert := ⟨[scratch], [.op (rcInc scratch (atRdi 0))]⟩

/-- `rc_drop`: `rcDrop`. -/
def dropCert : RCert :=
  ⟨[scratch], [.op (rcDec scratch (atRdi 0)), .exit (isLast scratch)]⟩

/-- `rc_publish`: a relaxed load of the payload, a store to `*out`, then `rcDrop`. -/
def publishCert : RCert :=
  ⟨[scratch], [.op (.load .rax .rlx 4 .wb (atRdi 4)),
    .op (.store .na 4 .wb (.bin .add (.bin .add (.reg .rsi) (.lit 0)) (.lit 0)) (.reg .rax)),
    .op (rcDec scratch (atRdi 0)), .exit (isLast scratch)]⟩

/-- `rc_share2`: two inlined `rcInc`s, then `rcDrop`. -/
def share2Cert : RCert :=
  ⟨[scratch], [.op (rcInc scratch (atRdi 0)), .op (rcInc scratch (atRdi 0)),
    .op (rcDec scratch (atRdi 0)), .exit (isLast scratch)]⟩

/-- The four validated functions: name, bytes, certificate. -/
def all : List (String × List (BitVec 8) × RCert) :=
  [ ("rc_clone", Code.rcClone, cloneCert), ("rc_drop", Code.rcDrop, dropCert),
    ("rc_publish", Code.rcPublish, publishCert), ("rc_share2", Code.rcShare2, share2Cert) ]

/-! ## Mutants -/

/-- `rc_drop` with `je` turned into `jne` (`0x75`): the cold path on every drop but the
last. -/
def dropJne : List (BitVec 8) := Code.bs [0xf0, 0x83, 0x2f, 0x01, 0x75, 0x0a]

/-- `rc_drop` with `lock sub` turned into `lock add`: the count goes up. -/
def dropAdd : List (BitVec 8) := Code.bs [0xf0, 0x83, 0x07, 0x01, 0x74, 0x0a]

/-- `rc_clone` without the `lock` prefix (`add DWORD PTR [rdi], 1`): not atomic. -/
def cloneUnlocked : List (BitVec 8) := Code.bs [0x83, 0x07, 0x01]

/-- `rc_drop` whose `je` goes back into the code (`je` to offset 0). -/
def dropBack : List (BitVec 8) := Code.bs [0xf0, 0x83, 0x2f, 0x01, 0x74, 0xfa]

/-- `rc_clone` adding `2`. -/
def cloneBy2 : List (BitVec 8) := Code.bs [0xf0, 0x83, 0x07, 0x02]

/-- `rc_drop` on `[rsi]` instead of `[rdi]`. -/
def dropRsi : List (BitVec 8) := Code.bs [0xf0, 0x83, 0x2e, 0x01, 0x74, 0x0a]

/-- `rc_drop` without its `je`: the cold path never runs. -/
def dropNoJe : List (BitVec 8) := Code.bs [0xf0, 0x83, 0x2f, 0x01]

end Silmaril.X86.Concurrency.Cir.Rc.Tv
