module

public import Silmaril.X86.Ext.Decode
public import Silmaril.X86.Ext.Lemmas
public import Silmaril.X86.Ext.Machine

/-!
# Decompilation into logic, over `X86.Ext`

This is a Lean port of the *decompilation into logic* design of
`myreen2008decompilation` / `myreen2012decompilation`, adapted to the memory-backed machine of
`Silmaril/X86/Ext/Machine.lean`. It is one of three approaches to x86 function
proofs here; the other two are a separation logic (`Silmaril.X86.Sep`) and an
s2n-bignum-style `ensures`/`MAYCHANGE` specification (`Silmaril.X86.Spec.Ensures`).

## The idea

A piece of machine code is turned into two things:

1. a plain Lean function over the values the code manipulates — non-recursive
   for straight-line code, tail-recursive (or clocked) for a loop — which
   mentions no `State`, no `Memory`, no `exec` and no `step`; and
2. a **certificate theorem** relating a run of the real machine, from an
   ABI-conformant entry state, to that function.

Everything downstream — "this equals `Spec.compress`", "this is the SysV
`right_rot`" — is then a theorem about the plain Lean function. `exec` and
`step` are unfolded exactly once per *instruction form*, in `Ext/Lemmas.lean`
and in `retires_instr` below, not once per instruction *occurrence* and never
again afterwards.

## What this module provides

* `Advances`, the reflexive-transitive closure of retirement, with `trans`.
  This is the glue that sequences per-instruction facts without ever naming a
  step count by hand.
* `Image`, "these bytes are fetchable at this address", with the three lemmas a
  decompiler needs about it: `Image.slice` (take out the bytes of one
  instruction), `Image.append` (`code₁ ++ code₂` splits, which is the code half
  of block composition) and `Image.of_storeN` (a store outside the code leaves
  the code fetchable — the frame property that makes a stack-using function
  tractable).
* `retires_instr`, **the** per-instruction step certificate: one instruction of
  an image retires with the effect `exec` gives it. It is proved once, from
  `step_of_fetch`, and invoked once per instruction occurrence with the
  matching `exec_*` equation from `Ext/Lemmas.lean`. Its two side conditions
  (`hcode`, `hbound`) are `decide`-able for concrete code.
* `returns_ret`, the terminal RET certificate.
* `Retires`, the composable block certificate `∀ m, Pre m → Advances exit m (f m)`,
  with `Retires.trans` (sequencing) and `Retires.mono` (precondition
  weakening). `Advances` is deliberately *functional* rather than relational,
  following `myreen2010separation`'s reformulation: a decompilation produces a
  function, so composition is function composition and no existential is
  introduced at each step.
* `Decompiled`, the shape of a finished decompilation certificate for a leaf
  function: code, an argument projection, the decompiled function, an
  ABI-conformant precondition and a postcondition stated in terms of the
  decompiled function's value.

The worked examples (a straight-line rotate and a copying loop, both from `clang -O0`)
are not part of this library.

## Two senses of "decompilation" live in this directory

`Silmaril/X86/Decompile/` holds two different things that both have a fair
claim to the name, and a reader should know which one they have landed in.

* **This module is decompilation in Myreen's sense** (`myreen2008decompilation`):
  machine code becomes a *tail-recursive logic function* plus a certificate
  triple, so that later proofs never unfold `exec` again. The output is a Lean
  function and a theorem; there is no graph, no recovered C, and no attempt to
  partition `.text`.
* **`Cfg.lean`, `CfgPropose.lean`, `Functions.lean` and `Region.lean`** are
  decompilation in the *binary-analysis* sense: recover a control-flow graph, partition `.text` into functions, check
  compiler output with verified checkers. The output is structure recovered
  from bytes.

They are complements, not rivals, and the natural pipeline runs
binary-analysis first and Myreen second: the CFG recovery is what would
*find* the loop head and the function boundary that `Advances.loop` and
`Image` here take as given. Nothing in this module depends on those, and the
file names do not collide.

## When to use this approach

Reach for decompilation into logic when **the same machine code will be
reasoned about more than once**, or when the specification you are heading for
is an existing Lean function rather than a register-and-memory assertion.

It fits when:

* the target is `compiled code = Spec.compress`, i.e. a functional equality
  against something already in the library. The decompiled function is the
  meeting point: the machine side stops at `rightRotSpec`, the specification
  side starts there, and neither has to know about the other;
* a function is used by several callers or proved against several
  specifications. The certificate is proved once; every consumer reasons about
  the decompiled function, and nothing re-enters `exec`;
* the code is a loop whose shape in logic is obvious (a fold, a `List.map`, a
  tail recursion). `Advances.loop` turns it into exactly that, once;
* you want the proof to survive a recompile of the *same source*: if the
  compiler re-schedules the body, the decompiled function is unchanged and only
  the certificate is redone.

It fits badly when:

* you only ever want the *frame* — "this did not clobber `rbx`, the return
  address is intact". That is strictly more expensive here than in a
  Verbeek-style checker or an s2n-bignum `MAYCHANGE` list, because the frame
  has to be written into `Post` and carried by hand;
* the function is a one-off with no specification to meet, where an
  `ensures`/`MAYCHANGE` triple says everything wanted in a quarter of the
  lines;
* the control flow is irreducible or computed. Nothing here handles indirect
  branches, and `Advances.loop` needs a decreasing measure you can name.

The cost structure is the thing to plan around: the up-front cost is one
`exec_*` equation per *instruction form* (shared across all functions, and
mostly already in `Ext/Lemmas.lean`), and the per-function cost is one
`retires_instr` application per instruction *occurrence* plus the framing
algebra for whatever memory the function touches. For straight-line
register-only code that per-occurrence cost is near-trivial; for `-O0` code
that spills to its frame, the framing algebra dominates and is where any future
automation should go.

## Contrast with a Verbeek-style automatic sanity checker

Verbeek et al. (PLDI 2022) lift compiled x86-64 to Hoare graphs and
prove, *automatically and without a hand-written per-function invariant*,
return-address integrity, bounded control flow and calling-convention
adherence, at the scale of Xen. At function exit the symbolic state is
"cleaned" down to ABI-guaranteed facts, which is also how an unknown callee is
summarised.

The two approaches cut the same contract in different places, and the trade is
quite sharp. A Verbeek-style checker gets the **non-functional half** of the
contract — the frame: the return address was not clobbered, control stayed
inside the function, callee-saved registers came back, the stack pointer was
restored — for *every* function in a large binary, at essentially no per-
function human cost, because the invariant it needs (a region relation plus
"the symbolic state is reachable") is generic and the symbolic executor finds
it. What it cannot get is the **functional half**: it never says that
`right_rot` computes `value >>> count ||| value <<< (32 - count)`, because
nothing in the analysis mentions a specification. Decompilation into logic is
the mirror image. The certificate below delivers the functional half — a plain
Lean function, equal to the reference specification by ordinary reasoning — but
it needs a human to *name* that function, and the frame half (which registers
and which bytes changed) has to be written into `Post` by hand and reproved for
each function.

They compose rather than compete, and the composition is the interesting part.
Each per-instruction `exec_*` equation in `Ext/Lemmas.lean` already carries the
whole effect of the instruction, so the frame facts a Verbeek-style checker
would infer are, in this setting, *available for free at every step* — they are
simply the parts of `exec`'s output that the certificate's `Post` chooses not
to mention. A checker in this repository would therefore be best built as an
automatic producer of the `Post`'s frame conjuncts (for example by running
`Memory.WritesOnly` and the register-disagreement set forward through the same
`Advances` chain), leaving the human to supply only the decompiled function and
its equality with the specification. That would turn the ~40 lines of frame
bookkeeping in `RightRot.lean` into a tactic, and is the obvious next step if
this approach is the one adopted. It is sketch-only here: no checker is
implemented.

Everything in this module is a statement about the handwritten local model of
`Silmaril/X86/Ext`; it is not evidence about hardware.
-/

@[expose] public section

namespace Silmaril.X86.Decompile

open Silmaril.X86 (Byte Word State MState Reg)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run run_zero run_succ run_add)

/-! This namespace sits inside `Silmaril.X86`, which has its own `Instr`,
`encode`, `decode`, `step` and `Outcome` for the register-only subset. Those
names therefore shadow the `Ext` ones, and every reference below to the
extended model is written `Ext.…` explicitly. Nothing here is about the
subset. -/

/-! ## Advancing: the reflexive-transitive closure of retirement

A decompilation never counts instructions. `Advances exit m m'` hides the step
count behind an existential that `Advances.trans` adds for you, so a
fifteen-instruction function is fifteen `Advances.one`s chained with `trans`,
not a `run (stepOpt exit) 15` with an explicit `run_succ` unfolding. -/

/-- The machine retires some number of instructions and reaches `m'`. No
`returned`, `trapped` or faulting outcome occurs along the way: `stepOpt` is
`none` for all of those. -/
def Advances (exit : Word) (m m' : MState) : Prop :=
  ∃ n, run (Ext.stepOpt exit) n m = some m'

@[refl] theorem Advances.rfl (exit : Word) (m : MState) : Advances exit m m := ⟨0, run_zero _ _⟩

theorem Advances.one {exit : Word} {m m' : MState} (h : Ext.stepOpt exit m = some m') :
    Advances exit m m' := ⟨1, by simp only [run_succ, h, Option.bind_some, run_zero]⟩

theorem Advances.trans {exit : Word} {m₁ m₂ m₃ : MState}
    (h₁ : Advances exit m₁ m₂) (h₂ : Advances exit m₂ m₃) : Advances exit m₁ m₃ := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  exact ⟨n + k, by rw [run_add, hn, Option.bind_some, hk]⟩

/-- Extend an advance by one more retirement. This is the form the worked
examples use, left-to-right down the disassembly. -/
theorem Advances.step {exit : Word} {m₁ m₂ m₃ : MState}
    (h : Advances exit m₁ m₂) (hs : Ext.stepOpt exit m₂ = some m₃) : Advances exit m₁ m₃ :=
  h.trans (Advances.one hs)

/-- An advance followed by a RET to the designated exit is a `Returns` run.
This is the only place a decompilation mentions `Ext.Returns`. -/
theorem returns_of_advances {exit : Word} {m mid final : MState}
    (h : Advances exit m mid) (hret : Ext.step exit mid = .returned final) :
    Ext.Returns exit m final := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, mid, hn, hret⟩

/-! ## Code images

`Image code entry memory` is Myreen's `code c` resource: the bytes are present
and executable at `entry`. Unlike the separation-logic reading, it is an
ordinary proposition about `Process.Memory`, and the frame property it needs
(`Image.of_storeN`) is proved rather than built in. -/

/-- The bytes of `code` can be fetched at `entry`. -/
def Image (code : List Byte) (entry : Word) (memory : Memory) : Prop :=
  memory.fetchBytes entry.toNat code.length = some code

/-- An image fits below `2 ^ 64`: the span was permission-checked. -/
theorem Image.bound {code : List Byte} {entry : Word} {memory : Memory}
    (h : Image code entry memory) : entry.toNat + code.length ≤ 2 ^ 64 := by
  have := Memory.readWith_permitted h
  rw [Memory.Permitted, Memory.checkSpan_iff] at this
  exact this.2.1

/-- Every encoding is at least one byte. -/
theorem encode_length_pos (i : Ext.Instr) : 0 < (Ext.encode i).length :=
  (Ext.decode_length (Ext.decode_encode i)).2.1

/-- **Slicing an image.** The bytes of the instruction at offset `off` can be
fetched there on their own. `hcode` and `hbound` are decidable for concrete
`code` and `i`, which is what makes a decompilation's per-instruction side
conditions `by decide`. -/
theorem Image.slice {code : List Byte} {entry : Word} {memory : Memory}
    (h : Image code entry memory) (off : Nat) (i : Ext.Instr)
    (hcode : (code.drop off).take (Ext.encode i).length = Ext.encode i)
    (hbound : off + (Ext.encode i).length ≤ code.length) :
    memory.fetchBytes (entry.toNat + off) (Ext.encode i).length = some (Ext.encode i) := by
  have := Memory.readWith_slice h off (Ext.encode i).length (encode_length_pos i) hbound
  rwa [hcode] at this

/-- **Code composition.** An image of `code₁ ++ code₂` is an image of `code₁` at
`entry` and an image of `code₂` at `entry + code₁.length`. This is the code
half of "decompiling `code₁ ++ code₂` composes"; `Retires.trans` is the
semantic half. -/
theorem Image.append {code₁ code₂ : List Byte} {entry : Word} {memory : Memory}
    (h : Image (code₁ ++ code₂) entry memory)
    (h₁ : 0 < code₁.length) (h₂ : 0 < code₂.length) :
    Image code₁ entry memory ∧
      memory.fetchBytes (entry.toNat + code₁.length) code₂.length = some code₂ := by
  have hlen : (code₁ ++ code₂).length = code₁.length + code₂.length := List.length_append ..
  constructor
  · have hs := Memory.readWith_slice h 0 code₁.length h₁ (by omega)
    rw [Nat.add_zero, List.drop_zero, List.take_left] at hs
    exact hs
  · have hs := Memory.readWith_slice h code₁.length code₂.length h₂ (by omega)
    rw [List.drop_left, List.take_of_length_le (by omega)] at hs
    exact hs

/-- **The code frame.** A write that misses the code leaves the code
fetchable. Without this, a function that uses its stack frame could not fetch
its own next instruction. `Memory.WritesOnly` is what `pushWord`, `popWord` and
`storeN` all expose. -/
theorem Image.of_writesOnly {code : List Byte} {entry : Word} {memory after : Memory}
    {addr len : Nat} (h : Image code entry memory)
    (frame : Memory.WritesOnly memory after addr len)
    (disjoint : entry.toNat + code.length ≤ addr ∨ addr + len ≤ entry.toNat) :
    Image code entry after := by
  show after.readWith .execute entry.toNat code.length = some code
  rw [X86.Memory.readWith_writesOnly frame .execute entry.toNat code.length disjoint]
  exact h

/-- The code frame for a `storeN`, which is the form `exec` produces. -/
theorem Image.of_storeN {code : List Byte} {entry : Word} {memory after : Memory}
    {addr : Word} {k : Nat} {v : Word} (h : Image code entry memory)
    (st : Ext.storeN memory addr k v = some after)
    (disjoint : entry.toNat + code.length ≤ addr.toNat ∨ addr.toNat + k ≤ entry.toNat) :
    Image code entry after :=
  Image.of_writesOnly h (Ext.storeN_writesOnly st) disjoint

/-! ## The per-instruction step certificate

This is the single place where a decompilation touches `fetch` and `step`.
Everything about what the instruction *does* arrives through `hexec`, which in
practice is one of the `exec_*` equations of `Ext/Lemmas.lean` — so each
instruction *form* costs one lemma, once, and each instruction *occurrence*
costs one `retires_instr` application. -/

/-- Within an image, RIP at offset `off` is `entry.toNat + off`: no wraparound,
because the image's span was permission-checked below `2 ^ 64`. -/
theorem rip_at {code : List Byte} {entry : Word} {memory : Memory}
    (h : Image code entry memory) {off : Nat} (hoff : off < code.length) :
    (entry + BitVec.ofNat 64 off).toNat = entry.toNat + off := by
  have hb := h.bound
  have hlt : off < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact Nat.mod_eq_of_lt (by omega)

/-- RIP after an instruction of length `len`, given where it was before. The
bound rules out wraparound; inside an image it always holds, because the
image's span was checked below `2 ^ 64`. -/
theorem rip_step {entry r : Word} {off len : Nat} (h : r.toNat = entry.toNat + off)
    (hlt : entry.toNat + (off + len) < 2 ^ 64) :
    (r + BitVec.ofNat 64 len).toNat = entry.toNat + (off + len) := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64), h,
    Nat.add_assoc]
  exact Nat.mod_eq_of_lt (by omega)

/-! ### Stack arithmetic

A decompiled function's precondition names its frame as a span below the entry
`rsp`; these two lemmas turn that into the per-access facts `exec` asks for. -/

/-- Subtracting a small literal from a word does not wrap. -/
theorem toNat_sub_lit {sp : Word} {k : Nat} (hk : k ≤ sp.toNat) (hlt : k < 2 ^ 64) :
    (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by
  have hsp := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    show 2 ^ 64 - k + sp.toNat = 2 ^ 64 + (sp.toNat - k) by omega, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- A store to a writable span succeeds. `Ext/Semantics.lean` states what a
store *does*; this is the matching "it happens at all". -/
theorem storeN_isSome {memory : Memory} {address : Word} {k : Nat} {v : Word}
    (h : memory.Permitted .write address.toNat k) :
    ∃ after, Ext.storeN memory address k v = some after := by
  refine ⟨{ memory with
    bytes := Memory.install memory.bytes address.toNat (Ext.leBytes v k) }, ?_⟩
  unfold Ext.storeN Memory.writeBytes
  rw [Ext.length_leBytes]
  exact ite_eq_left h

/-- A nonempty sub-span of a permitted span is permitted. -/
theorem permitted_sub {memory : Memory} {access : Process.Access} {address length : Nat}
    (h : memory.Permitted access address length) {off count : Nat}
    (hpos : 0 < count) (hb : off + count ≤ length) :
    memory.Permitted access (address + off) count := by
  rw [Memory.Permitted, Memory.checkSpan_iff] at h ⊢
  obtain ⟨hs, hl, hp⟩ := h
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  have := hp (off + k) (by omega)
  rwa [Nat.add_assoc]

/-- **One instruction retires.** The instruction at offset `off` of an image
fetched at `entry`, reached with RIP at that offset, retires with exactly the
effect `exec` gives it.

The side conditions are: the bytes at `off` are the canonical encoding of `i`
(`hcode`, decidable), the instruction fits inside the code (`hbound`,
decidable), and `i` is not RET (`hne`, decidable) — a RET is the function's
exit and is handled by `returns_ret`. -/
theorem retires_instr {exit : Word} {code : List Byte} {entry : Word} {m : MState}
    (image : Image code entry m.memory) (off : Nat) (i : Ext.Instr)
    (rip : m.core.rip.toNat = entry.toNat + off)
    (hcode : (code.drop off).take (Ext.encode i).length = Ext.encode i)
    (hbound : off + (Ext.encode i).length ≤ code.length)
    (hne : i ≠ .ret)
    {t : State} {after : Memory} (hexec : Ext.exec i m.core m.memory = .ok t after) :
    Ext.stepOpt exit m = some ⟨t, after⟩ := by
  have f := image.slice off i hcode hbound
  rw [← rip] at f
  rw [Ext.stepOpt_eq_some_iff, Ext.step_of_fetch f (Ext.decode_encode i), hexec]
  simp only [hne, false_and, ite_false]

/-- **The exit certificate.** A RET inside the image whose popped target is the
designated `exit` reports `returned`. -/
theorem returns_ret {exit : Word} {code : List Byte} {entry : Word} {m : MState}
    (image : Image code entry m.memory) (off : Nat)
    (rip : m.core.rip.toNat = entry.toNat + off)
    (hcode : (code.drop off).take 1 = [0xC3])
    (hbound : off + 1 ≤ code.length)
    {t : State} {after : Memory} (hexec : Ext.exec .ret m.core m.memory = .ok t after)
    (hexit : t.rip = exit) :
    Ext.step exit m = .returned ⟨t, after⟩ := by
  have henc : Ext.encode Ext.Instr.ret = [0xC3] := by decide
  have hlen : (Ext.encode Ext.Instr.ret).length = 1 := by rw [henc]; rfl
  have f := image.slice off .ret (by rw [hlen, henc]; exact hcode) (by rw [hlen]; exact hbound)
  rw [← rip] at f
  rw [Ext.step_of_fetch f (Ext.decode_encode _), hexec]
  simp only [hexit, and_self, ite_true]

/-! ## Seeing through the state updates `exec` produces

`exec` returns `{ s with rip := … }` or `{ s with flags := …, rip := … }`, which
is a structure literal, not a `State.write`. No `simp` lemma in `Silmaril/X86`
sees through it, so register reads in a decompilation would not reduce. These
do, and they are what makes a certificate's register bookkeeping one `simp`
call per step. -/

@[simp] theorem read_setRip (s : State) (v : Word) (r : Reg) :
    ({ s with rip := v } : State).read r = s.read r := rfl

@[simp] theorem read_setFlagsRip (s : State) (f : X86.Flags) (v : Word) (r : Reg) :
    ({ s with flags := f, rip := v } : State).read r = s.read r := rfl

@[simp] theorem rip_setRip (s : State) (v : Word) : ({ s with rip := v } : State).rip = v := rfl

@[simp] theorem rip_setFlagsRip (s : State) (f : X86.Flags) (v : Word) :
    ({ s with flags := f, rip := v } : State).rip = v := rfl

@[simp] theorem szRead_setRip (sz : Ext.Sz) (s : State) (v : Word) (r : Reg) :
    sz.read ({ s with rip := v } : State) r = sz.read s r := rfl

@[simp] theorem szRead_setFlagsRip (sz : Ext.Sz) (s : State) (f : X86.Flags) (v : Word) (r : Reg) :
    sz.read ({ s with flags := f, rip := v } : State) r = sz.read s r := rfl

@[simp] theorem read_szWrite_same (sz : Ext.Sz) (s : State) (r : Reg) (v : BitVec sz.bits) :
    (sz.write s r v).read r = v.setWidth 64 := by simp [Ext.Sz.write]

@[simp] theorem read_szWrite_other (sz : Ext.Sz) (s : State) (r q : Reg) (v : BitVec sz.bits)
    (h : q ≠ r) : (sz.write s r v).read q = s.read q := Ext.Sz.read_write_other sz s r q v h

@[simp] theorem szRead_szWrite_other (sz sz' : Ext.Sz) (s : State) (r q : Reg)
    (v : BitVec sz'.bits) (h : q ≠ r) : sz.read (sz'.write s r v) q = sz.read s q := by
  simp [Ext.Sz.read, h]

/-- Widening a 32-bit value to 64 bits and reading it back at 32 bits. -/
@[simp] theorem setWidth_roundtrip (x : BitVec Ext.Sz.d.bits) :
    (x.setWidth 64).setWidth Ext.Sz.d.bits = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : Ext.Sz.d.bits ≤ 64), BitVec.setWidth_eq]

/-! ## The loop rule

Straight-line code needs only `Advances.trans`. A loop needs one more rule, and
it is the rule that makes "a loop becomes a tail-recursive logic function" true:
given an invariant indexed by a decreasing measure and a certificate for *one*
iteration, the machine advances from the loop's entry to its exit. The
induction happens here, once, and never again in a decompilation — exactly the
split `myreen2008decompilation` describes.

Note what the rule does *not* mention: no code, no image, no RIP. A loop
certificate is a statement about `Advances` alone, so the same rule serves a
counted loop, a pointer-walking loop and a nested one. -/

/-- **The loop rule.** If one iteration advances the machine from `Inv (n + 1)`
to `Inv n`, then from `Inv n` the machine advances to a state satisfying
`Inv 0`. The measure `n` is the loop's own decreasing quantity — for
`MD5_memcpy` it is `len - i`. -/
theorem Advances.loop {exit : Word} (Inv : Nat → MState → Prop)
    (body : ∀ n m, Inv (n + 1) m → ∃ m', Advances exit m m' ∧ Inv n m') :
    ∀ n m, Inv n m → ∃ m', Advances exit m m' ∧ Inv 0 m' := by
  intro n
  induction n with
  | zero => exact fun m hm => ⟨m, Advances.rfl exit m, hm⟩
  | succ n ih =>
    intro m hm
    obtain ⟨m', hadv, hm'⟩ := body n m hm
    obtain ⟨m'', hadv', hm''⟩ := ih m' hm'
    exact ⟨m'', hadv.trans hadv', hm''⟩

/-- The loop rule followed by an exit certificate: the shape a whole decompiled
loop takes. -/
theorem Advances.loop_returns {exit : Word} (Inv : Nat → MState → Prop)
    (body : ∀ n m, Inv (n + 1) m → ∃ m', Advances exit m m' ∧ Inv n m')
    (fini : ∀ m, Inv 0 m → ∃ final, Ext.Returns exit m final) :
    ∀ n m, Inv n m → ∃ final, Ext.Returns exit m final := by
  intro n m hm
  obtain ⟨m', hadv, hm'⟩ := Advances.loop Inv body n m hm
  obtain ⟨final, n', mid, hrun, hret⟩ := fini m' hm'
  exact ⟨final, returns_of_advances (hadv.trans ⟨n', hrun⟩) hret⟩

/-- An advance followed by a return is a return: this is how a decompiled
function's prologue, loop and epilogue are glued into one `Ext.Returns`. -/
theorem returns_prepend {exit : Word} {m m' final : MState}
    (h : Advances exit m m') (hr : Ext.Returns exit m' final) : Ext.Returns exit m final := by
  obtain ⟨n, mid, hrun, hret⟩ := hr
  exact returns_of_advances (h.trans ⟨n, hrun⟩) hret

/-! ## Reading across a write

`X86.Memory.readWith_writesOnly` frames a read against *one* written interval.
A loop over a buffer writes two that are not adjacent — the buffer and its own
counter slot — so the single-interval form does not compose. `readWith_congr`
is the general statement both specialise to: a read is unaffected by any change
that leaves its own bytes and the region list alone. -/

/-- Two memories that agree on a span's bytes, and on the region list, read the
same there. -/
theorem readWith_congr {before after : Memory} (hr : after.regions = before.regions)
    {access : Process.Access} {start count : Nat}
    (hb : ∀ k < count, after.bytes.get? (start + k) = before.bytes.get? (start + k)) :
    after.readWith access start count = before.readWith access start count := by
  have key : ∀ (c s : Nat), (∀ k < c, after.bytes.get? (s + k) = before.bytes.get? (s + k)) →
      Memory.readBacking after.bytes s c = Memory.readBacking before.bytes s c := by
    intro c
    induction c with
    | zero => intro s _; rfl
    | succ c ih =>
      intro s h
      have hs : after.bytes.get? s = before.bytes.get? s := by
        have := h 0 (by omega); simpa using this
      have htail : ∀ k < c, after.bytes.get? (s + 1 + k) = before.bytes.get? (s + 1 + k) := by
        intro k hk
        have := h (k + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using this
      simp only [Memory.readBacking, Std.ExtHashMap.get?_eq_getElem?] at hs ⊢
      rw [hs, ih (s + 1) htail]
  simp only [Memory.readWith, X86.Memory.checkSpan_congr hr]
  split
  · exact key count start hb
  · rfl

/-- Memory changed only inside two intervals. A loop over a buffer writes the
buffer and its own counter slot, and those are not adjacent, so
`Memory.WritesOnly` cannot describe it. -/
def WritesOnly₂ (before after : Memory) (a la b lb : Nat) : Prop :=
  after.regions = before.regions ∧
    ∀ loc, (loc < a ∨ a + la ≤ loc) → (loc < b ∨ b + lb ≤ loc) →
      after.bytes.get? loc = before.bytes.get? loc

theorem writesOnly₂_of_left {before after : Memory} {a la b lb : Nat}
    (h : Memory.WritesOnly before after a la) : WritesOnly₂ before after a la b lb :=
  ⟨h.1, fun loc h1 _ => h.2 loc h1⟩

theorem writesOnly₂_of_right {before after : Memory} {a la b lb : Nat}
    (h : Memory.WritesOnly before after b lb) : WritesOnly₂ before after a la b lb :=
  ⟨h.1, fun loc _ h2 => h.2 loc h2⟩

theorem writesOnly₂_trans {x y z : Memory} {a la b lb : Nat}
    (h₁ : WritesOnly₂ x y a la b lb) (h₂ : WritesOnly₂ y z a la b lb) :
    WritesOnly₂ x z a la b lb :=
  ⟨h₂.1.trans h₁.1, fun loc h1 h2 => (h₂.2 loc h1 h2).trans (h₁.2 loc h1 h2)⟩

/-- A read that misses both written intervals is unaffected. -/
theorem readWith_writesOnly₂ {before after : Memory} {a la b lb : Nat}
    (frame : WritesOnly₂ before after a la b lb) (access : Process.Access) (start count : Nat)
    (d₁ : start + count ≤ a ∨ a + la ≤ start) (d₂ : start + count ≤ b ∨ b + lb ≤ start) :
    after.readWith access start count = before.readWith access start count :=
  readWith_congr frame.1 (fun k hk => frame.2 (start + k) (by omega) (by omega))

/-- Widening the second of the two written intervals. -/
theorem writesOnly₂_widen_right {before after : Memory} {a la b lb b' lb' : Nat}
    (h : WritesOnly₂ before after a la b lb) (hlo : b' ≤ b) (hhi : b + lb ≤ b' + lb') :
    WritesOnly₂ before after a la b' lb' :=
  ⟨h.1, fun loc h1 h2 => h.2 loc h1 (by omega)⟩

/-- An image survives a two-interval write that misses it. -/
theorem Image.of_writesOnly₂ {code : List Byte} {entry : Word} {memory after : Memory}
    {a la b lb : Nat} (h : Image code entry memory)
    (frame : WritesOnly₂ memory after a la b lb)
    (d₁ : entry.toNat + code.length ≤ a ∨ a + la ≤ entry.toNat)
    (d₂ : entry.toNat + code.length ≤ b ∨ b + lb ≤ entry.toNat) :
    Image code entry after := by
  show after.readWith .execute entry.toNat code.length = some code
  rw [readWith_writesOnly₂ frame .execute entry.toNat code.length d₁ d₂]
  exact h

/-- A load that misses both written intervals is unaffected. -/
theorem loadN_writesOnly₂ {before after : Memory} {a la b lb : Nat}
    (frame : WritesOnly₂ before after a la b lb) (address : Word) (k : Nat)
    (d₁ : address.toNat + k ≤ a ∨ a + la ≤ address.toNat)
    (d₂ : address.toNat + k ≤ b ∨ b + lb ≤ address.toNat) :
    Ext.loadN after address k = Ext.loadN before address k := by
  simp only [Ext.loadN, Memory.readBytes,
    readWith_writesOnly₂ frame .read address.toNat k d₁ d₂]

/-! ## Indexing into a buffer

A loop walks `base + 0, base + 1, …`; these turn that into `Nat` arithmetic,
once, so the disjointness side conditions a loop body generates are `omega`
goals rather than `BitVec` ones. -/

/-- Adding a small literal to a word does not wrap. -/
theorem toNat_add_lit {x : Word} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

/-! ## Composing memory frames

A decompiled function's `Post` says which bytes it may have changed. Each
individual store reports its own `Memory.WritesOnly`; these two lemmas widen
them to the function's declared frame and chain them. -/

/-- A write inside a larger interval is a write to that interval. -/
theorem writesOnly_widen {before after : Memory} {addr len base width : Nat}
    (h : Memory.WritesOnly before after addr len)
    (hlo : base ≤ addr) (hhi : addr + len ≤ base + width) :
    Memory.WritesOnly before after base width :=
  ⟨h.1, fun location outside => h.2 location (by omega)⟩

/-- Two writes to the same interval compose. -/
theorem writesOnly_trans {a b c : Memory} {addr len : Nat}
    (h₁ : Memory.WritesOnly a b addr len) (h₂ : Memory.WritesOnly b c addr len) :
    Memory.WritesOnly a c addr len :=
  ⟨h₂.1.trans h₁.1, fun location outside => (h₂.2 location outside).trans (h₁.2 location outside)⟩

/-! ## `exec` equations `Ext/Lemmas.lean` does not have

`Ext/Lemmas.lean` covers memory operands thoroughly for `mov`, `load` and
`store`, but for the ALU, the compare, the byte move and the immediate move it
has only the *register*-operand forms (`exec_aluR_reg`, `exec_cmpR_reg`,
`exec_mov8_reg`, `exec_movI_reg`). `clang -O0` puts operands in the frame
constantly, so the memory forms are exactly what a decompilation of `-O0` code
needs: `2b 4d f8` (`sub ecx, [rbp-8]`), `3b 45 ec` (`cmp eax, [rbp-20]`),
`8a 14 08` (`mov dl, [rax+rcx]`) and `c7 45 e8 …` (`movl $0, -0x18(%rbp)`) all
occur in the two benchmark functions. The four equations below fill the gap.
They could move to `Ext/Lemmas.lean`. -/

/-- `op r32, [mem]` with a readable operand retires with the ALU result and
flags, leaving memory alone. -/
theorem exec_aluR_mem (sz : Ext.Sz) (op : AluOp) (dst : Reg) (mm : Ext.Mem)
    (s : State) (memory : Memory) (h : op ≠ .cmp) {y : BitVec sz.bits}
    (hy : Ext.readRM sz (.mem mm) s memory
      (s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz op dst (.mem mm)).length) = some y) :
    Ext.exec (.aluR sz op dst (.mem mm)) s memory =
      .ok { sz.write s dst (Ext.AluOp.resultN op (sz.read s dst) y) with
        flags := Ext.AluOp.flagsN op (sz.read s dst) y
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz op dst (.mem mm)).length } memory := by
  simp only [Ext.exec, Ext.aluStepR, hy, h, ite_false, Ext.retire]

/-- `cmp r/m`: the direction-1 compare with a memory second operand sets the
subtraction flags and changes nothing else. -/
theorem exec_cmpR_mem (sz : Ext.Sz) (dst : Reg) (mm : Ext.Mem) (s : State) (memory : Memory)
    {y : BitVec sz.bits}
    (hy : Ext.readRM sz (.mem mm) s memory
      (s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz .cmp dst (.mem mm)).length) = some y) :
    Ext.exec (.aluR sz .cmp dst (.mem mm)) s memory =
      .ok { s with
        flags := Ext.subFlagsN (sz.read s dst) y
        rip := s.rip +
          BitVec.ofNat 64 (Ext.Instr.aluR sz .cmp dst (.mem mm)).length } memory := by
  simp only [Ext.exec, Ext.aluStepR, hy, ite_true, Ext.retire, Ext.AluOp.flagsN]

/-- `mov r8, [mem]`: a byte load that replaces bits 7:0 and keeps bits 63:8. -/
theorem exec_mov8_mem (dst : Reg) (mm : Ext.Mem) (s : State) (memory : Memory) :
    Ext.exec (.mov8 dst (.mem mm)) s memory =
      match Ext.loadN memory
        (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.mov8 dst (.mem mm)).length)) 1 with
      | some v => .ok { Ext.writeByte s dst (v.setWidth 8) with
          rip := s.rip + BitVec.ofNat 64 (Ext.Instr.mov8 dst (.mem mm)).length } memory
      | none => .dataFault := by
  have hb : (Ext.Narrow.b).bytes = 1 := rfl
  simp only [Ext.exec, Ext.readNarrow, hb]
  cases Ext.loadN memory
    (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.mov8 dst (.mem mm)).length)) 1 <;> rfl

/-- `movl $imm, [mem]`: a sign-extended immediate store. -/
theorem exec_movI_mem (sz : Ext.Sz) (mm : Ext.Mem) (imm : BitVec 32) (s : State)
    (memory : Memory) :
    Ext.exec (.movI sz (.mem mm) imm) s memory =
      match Ext.storeN memory
        (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.movI sz (.mem mm) imm).length))
        sz.bytes ((imm.signExtend sz.bits).setWidth 64) with
      | some after => .ok { s with
          rip := s.rip + BitVec.ofNat 64 (Ext.Instr.movI sz (.mem mm) imm).length } after
      | none => .dataFault := by
  simp only [Ext.exec, Ext.writeRM]
  cases Ext.storeN memory
    (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.movI sz (.mem mm) imm).length))
    sz.bytes ((imm.signExtend sz.bits).setWidth 64) <;> rfl

/-! ## Block certificates

A block certificate is the composable unit: "from any state satisfying `Pre`,
the machine retires to `f m`". `Retires.trans` is the sequencing rule, and
together with `Image.append` it is the "decompiling `code₁ ++ code₂` composes"
statement. -/

/-- From every state satisfying `Pre`, the machine retires to exactly `f m`. -/
def Retires (exit : Word) (Pre : MState → Prop) (f : MState → MState) : Prop :=
  ∀ m, Pre m → Advances exit m (f m)

theorem Retires.id (exit : Word) (Pre : MState → Prop) : Retires exit Pre _root_.id :=
  fun m _ => Advances.rfl exit m

/-- **Sequencing.** Two blocks compose when the first block's result satisfies
the second block's precondition; the decompiled function of the whole is the
composition of the two decompiled functions. -/
theorem Retires.trans {exit : Word} {P Q : MState → Prop} {f g : MState → MState}
    (h₁ : Retires exit P f) (h₂ : Retires exit Q g) (hPQ : ∀ m, P m → Q (f m)) :
    Retires exit P (fun m => g (f m)) :=
  fun m hm => (h₁ m hm).trans (h₂ (f m) (hPQ m hm))

/-- Weakening the precondition. -/
theorem Retires.mono {exit : Word} {P Q : MState → Prop} {f : MState → MState}
    (h : Retires exit Q f) (hPQ : ∀ m, P m → Q m) : Retires exit P f :=
  fun m hm => h m (hPQ m hm)

/-- A block certificate closed off by a RET is a `Returns` certificate. -/
theorem Retires.returns {exit : Word} {P : MState → Prop} {f g : MState → MState}
    (h : Retires exit P f) (hret : ∀ m, P m → Ext.step exit (f m) = .returned (g m)) :
    ∀ m, P m → Ext.Returns exit m (g m) :=
  fun m hm => returns_of_advances (h m hm) (hret m hm)

/-! ## The shape of a finished decompilation -/

/-- **A decompilation certificate.**

* `code` is the function's machine code, byte for byte, as ingested from the
  object file.
* `args m` reads the ABI-visible inputs out of an entry state (for System V:
  the argument registers).
* `f` is the decompiled logic function — a plain Lean function over those
  inputs, mentioning no `State`, `Memory`, `exec` or `step`.
* `Pre entry exit m` is the ABI-conformant entry condition: RIP at `entry`, the
  code fetchable there, the return address `exit` at `[rsp]`, the stack and red
  zone available, and whatever domain condition the source function needs.
* `Post v m final` describes the state the machine returns in, in terms of the
  value `v = f (args m)` the decompiled function computes, the entry state `m`
  (for frame conditions such as "`rsp` is the entry `rsp + 8`" and "the
  callee-saved registers came back") and the final state.

`cert` is the certificate theorem. A later proof about this code — "`f` equals
the reference specification", "this `Implements sysv64 …`" — reasons about `f`
and `Post` and never unfolds `exec` or `step` again. That is the whole point of
the construction. -/
structure Decompiled {α β : Type} (code : List Byte)
    (Pre : Word → Word → MState → Prop) (args : MState → α) (f : α → β)
    (Post : β → MState → MState → Prop) : Prop where
  /-- The bytes are exactly a concatenation of canonical encodings: the
  decompiler consumed every byte of `code`, skipped nothing, left nothing over,
  and spelled each instruction the way `encode` spells it (`Ext.Covered`, see
  `Ext/Decode.lean`). A decompilation of bytes the model would have written
  differently would fail this field, not pass it with a different answer. -/
  covered : Ext.Covered code
  /-- Running the real machine from an ABI-conformant entry state returns, and
  the final state is described by the decompiled function applied to the entry
  state's visible inputs. -/
  cert : ∀ entry exit m, Pre entry exit m →
    ∃ final, Ext.Returns exit m final ∧ Post (f (args m)) m final

/-- The certificate, with the `Returns` run and the postcondition split out.
This is the form a caller uses. -/
theorem Decompiled.returns {α β : Type} {code : List Byte}
    {Pre : Word → Word → MState → Prop} {args : MState → α} {f : α → β}
    {Post : β → MState → MState → Prop} (h : Decompiled code Pre args f Post)
    {entry exit : Word} {m : MState} (hm : Pre entry exit m) :
    ∃ final, Ext.Returns exit m final ∧ Post (f (args m)) m final := h.cert entry exit m hm

end Silmaril.X86.Decompile
