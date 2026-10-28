module

public import Silmaril.X86.Ext.Machine

/-!
# Symbolic execution over a loaded code image

Turning "the bytes at RIP are *these* bytes" into "the next state is *this*",
once, generically.

`Silmaril.X86.Ext.Machine` gives a fetch/decode/execute step over
`X86.MState`, and `Returns exit initial final` is an existential over a step
count. Proving a contract about a compiled function means running that step
relation several thousand times, so the unfolding has to be done by a lemma
and a tactic rather than by hand. This module is that layer. It is ISA-generic
within `Ext`: nothing here mentions SHA-256, and it is meant to be shared by
every optimisation level of the `#882` pilot.

## What is here

* `Loaded memory base bytes` — the byte string `bytes` is fetchable as code at
  `base`. One hypothesis covers the whole function, and
  `Loaded.fetchBytes_sub` cuts out the span of any single instruction.
* `step_of_loaded` — the fetch/decode half of a step, discharged from
  `Loaded` plus `RIP = base + off` plus a `decode` fact that `decide` proves.
  This is the lemma that replaces hand-unfolding.
* `Runs exit n initial final` — `n` retirements, as a relation rather than an
  `Option` equation, with `nil`/`cons`/`trans` so that a straight-line block
  composes.
* `Returns.eq_of_run` — **determinism**. `Returns` quantifies existentially
  over the step count, so a contract of the shape `Returns … → Post …` has to
  rule out *other* returning runs. It can: `stepOpt` is `none` at a returning
  state, so a run cannot pass one, and the machine is a function, so the step
  count and the final state are unique. Symbolically executing to the `ret`
  therefore *determines* the final state, and the same execution is the
  witness for a liveness claim.

## How a contract proof uses it

1. Symbolically execute from the entry state to the `ret`, producing
   `Runs exit N initial mid` and `step exit mid = .returned final` for a
   concrete `final`.
2. `Returns.intro` turns that into `Returns exit initial final`, which is the
   liveness witness.
3. `Returns.eq_of_run` turns the contract's *hypothesis*
   `Returns exit initial final'` into `final' = final`, after which the
   postcondition is a statement about the computed state.

Step 1 is the expensive one and is where a loop rule is needed; steps 2 and 3
are this module, and are paid for once.

## Scope

This is a local model of the local model: every lemma is about
`Silmaril.X86.Ext.step` and `Process.Memory` as this repository defines them.
Nothing here is a claim about hardware.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory Access)

/-! ## Sub-spans of a checked read

`Process.Memory.readWith` checks permissions over the whole span and then
reads the backing bytes. A successful read of a long span therefore contains a
successful read of every sub-span, and this is what lets one `Loaded`
hypothesis serve every instruction of a function. -/

/-- A successful checked access contains a successful checked access to each
of its non-empty sub-spans, returning the corresponding slice. -/
theorem readWith_sub {memory : Memory} {access : Access} {address length : Nat}
    {bytes : List Byte} (read : memory.readWith access address length = some bytes)
    {offset len : Nat} (pos : 0 < len) (fits : offset + len ≤ length) :
    memory.readWith access (address + offset) len = some ((bytes.drop offset).take len) :=
  Memory.readWith_sub_range read (by omega) fits

/-- A permitted span contains its sub-spans: the frame, the output buffer and
the code are each permitted as a whole, and every individual access of the
function is a sub-span of one of them. -/
theorem Memory.Permitted.sub {memory : Memory} {access : Access} {address length : Nat}
    (h : memory.Permitted access address length) {start len : Nat} (pos : 0 < len)
    (lower : address ≤ start) (upper : start + len ≤ address + length) :
    memory.Permitted access start len := by
  rw [Silmaril.Process.Memory.Permitted, Memory.checkSpan_iff] at h ⊢
  obtain ⟨hstart, hlimit, hperm⟩ := h
  refine ⟨by omega, by omega, fun offset ho => ?_⟩
  have := hperm (start + offset - address) (by omega)
  rwa [show address + (start + offset - address) = start + offset by omega] at this

/-! ## Stack addresses

Frame slots are named by subtracting a literal from a 64-bit stack pointer.
These two lemmas are what turn that into `Nat` arithmetic, which is what
`Process.Memory` speaks. -/

/-- A `BitVec` subtraction that does not borrow is a `Nat` subtraction. -/
theorem toNat_sub_ofNat {x : Word} {k : Nat} (fits : k ≤ x.toNat) (small : k < 2 ^ 64) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  have hk : (BitVec.ofNat 64 k).toNat = k := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt small
  rw [BitVec.toNat_sub, hk]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  omega

/-! ## A loaded code image -/

/-- The byte string `bytes` is fetchable as code at `base`: one hypothesis
that covers every instruction of a function. -/
def Loaded (memory : Memory) (base : Word) (bytes : List Byte) : Prop :=
  memory.fetchBytes base.toNat bytes.length = some bytes

/-- A loaded image does not run off the top of the address space. This is a
consequence of the permission check, not an extra assumption. -/
theorem Loaded.noWrap {memory : Memory} {base : Word} {bytes : List Byte}
    (h : Loaded memory base bytes) : base.toNat + bytes.length ≤ Silmaril.Process.addressLimit := by
  have := Memory.readWith_permitted h
  rw [Memory.Permitted, Memory.checkSpan_iff] at this
  exact this.2.1

/-- The span of one instruction, cut out of the image. -/
theorem Loaded.fetchBytes_sub {memory : Memory} {base : Word} {bytes : List Byte}
    (h : Loaded memory base bytes) {offset len : Nat} (pos : 0 < len)
    (fits : offset + len ≤ bytes.length) :
    memory.fetchBytes (base.toNat + offset) len = some ((bytes.drop offset).take len) :=
  readWith_sub h pos fits

/-! ## Relocation: splicing bytes into an image

A loaded image is the object's bytes with each relocated field overwritten.
Only the patched bytes change, so every instruction that does not read one of
them decodes from the *literal* object bytes — which is what makes the
`decode` side condition of `step_of_loaded` a closed `decide` goal rather than
a goal depending on the layout. These two lemmas say that, once, for any
patch at any offset; `Sha256O0`'s `patch32` and `Sha256O2`'s are instances.

Both halves are needed, not one: a function's loop bodies and epilogue
normally sit *above* its relocations, so `spliceAt_slice_above` fires as often
as `spliceAt_slice_below`. -/

/-- `bytes` with `patch` written over `patch.length` bytes at `offset`. -/
def spliceAt (bytes : List Byte) (offset : Nat) (patch : List Byte) : List Byte :=
  bytes.take offset ++ patch ++ bytes.drop (offset + patch.length)

/-- Splicing changes nothing before the patch. -/
theorem take_spliceAt (bytes patch : List Byte) {offset : Nat} (fits : offset ≤ bytes.length) :
    (spliceAt bytes offset patch).take offset = bytes.take offset := by
  simp only [spliceAt, List.append_assoc]
  exact List.take_left' (by rw [List.length_take]; omega)

/-- Any slice ending at or before the patch is a slice of the original bytes. -/
theorem spliceAt_slice_below (bytes patch : List Byte) {offset start len : Nat}
    (fits : offset ≤ bytes.length) (below : start + len ≤ offset) :
    ((spliceAt bytes offset patch).drop start).take len = (bytes.drop start).take len := by
  have cut : ∀ l : List Byte,
      (l.drop start).take len = ((l.take offset).drop start).take len := by
    intro l
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
  rw [cut (spliceAt bytes offset patch), cut bytes, take_spliceAt bytes patch fits]

/-- Splicing changes nothing after the patch either. The epilogue of a
function is normally *above* its relocations, so this half is needed as often
as the other. -/
theorem drop_spliceAt_above (bytes patch : List Byte) {offset start : Nat}
    (fits : offset + patch.length ≤ bytes.length) (above : offset + patch.length ≤ start) :
    (spliceAt bytes offset patch).drop start = bytes.drop start := by
  have cut : ∀ (first second : List Byte) (n : Nat), first.length ≤ n →
      (first ++ second).drop n = second.drop (n - first.length) := by
    intro first second n hn
    rw [show n = first.length + (n - first.length) by omega, ← List.drop_drop,
      List.drop_left]
    congr 1
    omega
  have hA : (bytes.take offset ++ patch).length = offset + patch.length := by
    simp only [List.length_append, List.length_take]
    omega
  rw [spliceAt, cut _ _ _ (by rw [hA]; omega), hA, List.drop_drop]
  congr 1
  omega

/-- Any slice starting at or after the patch is a slice of the original
bytes. -/
theorem spliceAt_slice_above (bytes patch : List Byte) {offset start len : Nat}
    (fits : offset + patch.length ≤ bytes.length) (above : offset + patch.length ≤ start) :
    ((spliceAt bytes offset patch).drop start).take len = (bytes.drop start).take len := by
  rw [drop_spliceAt_above bytes patch fits above]

/-! ## Executing an *abstract* image

Stating a block lemma over the concrete relocated byte string puts the whole
literal into the type of **every** step of that block, and the proof term then
outgrows what the kernel will check. Track 3 measured a 50× elaboration swing
on a 459-byte image from abstracting it away; on a 1214-byte one the
difference is between seconds and not finishing.

`PatchOf img source hole patchLen` is the interface a block proof actually
needs: `img` has the same length as the object bytes and decodes the same way
everywhere that does not meet the patched field. A block lemma quantifies over
an abstract `img` satisfying it; the real image is supplied once, at the top,
by `patchOf_spliceAt`. The statements are no weaker — the literal simply never
enters a step's type. -/

/-- `img` is `source` with `patchLen` bytes replaced at `hole`, as far as
decoding is concerned: the same length, and the same instruction at every
offset whose span misses the patch. -/
structure PatchOf (img source : List Byte) (hole patchLen : Nat) : Prop where
  /-- Patching does not change the length. -/
  length : img.length = source.length
  /-- Below the patch, `img` decodes as `source` does. -/
  below : ∀ {offset len : Nat} {instr : Instr}, offset + len ≤ hole →
    decode ((source.drop offset).take len) = some (instr, len) →
    decode ((img.drop offset).take len) = some (instr, len)
  /-- Above it, likewise. -/
  above : ∀ {offset len : Nat} {instr : Instr}, hole + patchLen ≤ offset →
    decode ((source.drop offset).take len) = some (instr, len) →
    decode ((img.drop offset).take len) = some (instr, len)

@[simp] theorem length_spliceAt (source patch : List Byte) {hole : Nat}
    (fits : hole + patch.length ≤ source.length) :
    (spliceAt source hole patch).length = source.length := by
  simp only [spliceAt, List.length_append, List.length_take, List.length_drop]
  omega

/-- A relocated image is a `PatchOf` its object bytes. -/
theorem patchOf_spliceAt (source patch : List Byte) {hole : Nat}
    (fits : hole + patch.length ≤ source.length) :
    PatchOf (spliceAt source hole patch) source hole patch.length where
  length := length_spliceAt source patch fits
  below below decoded := by
    rwa [spliceAt_slice_below source patch (by omega) below]
  above above decoded := by
    rwa [spliceAt_slice_above source patch fits above]

/-- The length side condition of a step, against an abstract image. -/
theorem PatchOf.fits {img source : List Byte} {hole patchLen : Nat}
    (p : PatchOf img source hole patchLen) {offset len : Nat}
    (within : offset + len ≤ source.length) : offset + len ≤ img.length := by
  rw [p.length]
  exact within

/-- A slice that **straddles** the patch: it starts before the patched field
and ends exactly at the end of it. This is the case neither
`spliceAt_slice_below` nor `spliceAt_slice_above` covers, and it is the one a
relocated instruction falls into — the opcode bytes come from the object and
the displacement from the relocation. -/
theorem spliceAt_slice_straddle (bytes patch : List Byte) {offset start : Nat}
    (fits : offset ≤ bytes.length) (hs : start ≤ offset) :
    ((spliceAt bytes offset patch).drop start).take (offset - start + patch.length)
      = (bytes.drop start).take (offset - start) ++ patch := by
  have key : ∀ (l₁ l₂ : List Byte) (n : Nat),
      (l₁ ++ l₂).take (l₁.length + n) = l₁ ++ l₂.take n := by
    intro l₁ l₂ n
    induction l₁ with
    | nil => simp
    | cons a l ih =>
      simp only [List.length_cons, List.cons_append,
        show l.length + 1 + n = l.length + n + 1 by omega, List.take_succ_cons, ih]
  have hA : (bytes.take offset).length = offset := by
    rw [List.length_take]; omega
  rw [spliceAt, List.append_assoc, List.drop_append_of_le_length (by omega)]
  have hlen : ((bytes.take offset).drop start).length = offset - start := by
    rw [List.length_drop, hA]
  rw [show offset - start + patch.length
      = ((bytes.take offset).drop start).length + patch.length from by rw [hlen],
    key, List.take_left, List.drop_take]

/-! ## Addresses inside the image -/

/-- `BitVec.ofNat` is additive, which is what turns "RIP advanced by the
instruction length" into "RIP is the image base plus the next offset". -/
theorem ofNat_add_ofNat (a b : Nat) :
    (BitVec.ofNat 64 a) + (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-- Inside a loaded image, `base + offset` does not wrap, so the machine
address is the arithmetic one. -/
theorem Loaded.toNat_add {memory : Memory} {base : Word} {bytes : List Byte}
    (h : Loaded memory base bytes) {offset : Nat} (inside : offset < bytes.length) :
    (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
  have hwrap := h.noWrap
  rw [Silmaril.Process.addressLimit] at hwrap
  have hbound : offset < 2 ^ 64 :=
    Nat.lt_of_lt_of_le inside (Nat.le_trans (Nat.le_add_left _ _) hwrap)
  have hsum : base.toNat + offset < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left inside _) hwrap
  have hoff : (BitVec.ofNat 64 offset).toNat = offset := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hbound
  rw [BitVec.toNat_add, hoff, Nat.mod_eq_of_lt hsum]

/-- Adding a wrapped negative constant is subtracting: how a sign-extended
negative `disp32` names a frame slot. -/
theorem toNat_add_neg {x : Word} {k : Nat} (pos : 0 < k) (fits : k ≤ x.toNat) :
    (x + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = x.toNat - k := by
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hk : (BitVec.ofNat 64 (2 ^ 64 - k)).toNat = 2 ^ 64 - k := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, hk]
  omega

/-- A non-wrapping constant addition. -/
theorem toNat_add_ofNat {x : Word} {k : Nat} (fits : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  have hk : (BitVec.ofNat 64 k).toNat = k := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt fits]

/-- Two successive constant subtractions are one. -/
theorem sub_sub_ofNat (x : Word) {a b c : Nat} (h : a + b = c) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 c := by
  rw [sub_sub, ofNat_add_ofNat, h]

/-- Undoing part of a constant subtraction: `sub $a,%rsp` then `add $c,%rsp`
leaves `%rsp` at `b` below where it started, when `b + c = a`. -/
theorem sub_add_ofNat (x : Word) {a b c : Nat} (h : b + c = a) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 c = x - BitVec.ofNat 64 b := by
  rw [← sub_sub_ofNat x h, sub_add_cancel]

/-- RIP advancing by an instruction length, as one offset into the image. -/
theorem rip_advance (base : Word) {a b c : Nat} (h : a + b = c) :
    base + BitVec.ofNat 64 a + BitVec.ofNat 64 b = base + BitVec.ofNat 64 c := by
  rw [add_assoc, ofNat_add_ofNat, h]

/-! ## Reading a register through a RIP or flag update

`Ext.exec` finishes with `{ t with rip := next }` and the ALU steps with
`{ t with flags := f }`. Neither touches the register file, and these two
`simp` lemmas are what keep that from obscuring every later register read. -/

@[simp] theorem read_with_rip (s : State) (r : Word) (q : Silmaril.X86.Reg) :
    ({ s with rip := r } : State).read q = s.read q := rfl

/-- `exec` rebuilds the state as an explicit `State.mk`, which hides the
register file from `State.read_write_same`. This puts it back. -/
@[simp] theorem read_mk_regs (s : State) (r : Word) (f : Silmaril.X86.Flags) (fs : Word)
    (q : Silmaril.X86.Reg) : (State.mk s.regs r f fs).read q = s.read q := rfl

@[simp] theorem rip_mk (regs : Silmaril.Machine.RegisterFile Silmaril.X86.Reg Word) (r : Word)
    (f : Silmaril.X86.Flags) (fs : Word) : (State.mk regs r f fs).rip = r := rfl

@[simp] theorem read_with_flags (s : State) (f : Silmaril.X86.Flags) (q : Silmaril.X86.Reg) :
    ({ s with flags := f } : State).read q = s.read q := rfl

@[simp] theorem rip_with_flags (s : State) (f : Silmaril.X86.Flags) :
    ({ s with flags := f } : State).rip = s.rip := rfl

/-! ## One step from the image

`step_of_loaded` is the lemma this module exists for: it discharges the
fetch and decode of a step from the `Loaded` hypothesis and a `decode`
equation on a concrete byte slice, leaving only `exec`. -/

/-- One step of the machine, with the fetch and decode discharged from a
loaded image. The hypothesis `decoded` is a closed statement about a byte
slice, so `decide` proves it. -/
theorem step_of_loaded {exit base : Word} {bytes : List Byte} {m : MState} {offset len : Nat}
    {instr : Instr} (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (instr, len)) :
    step exit m =
      match exec instr m.core m.memory with
      | .ok core memory =>
        if instr = .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault instr
      | .divideError => .divideFault
      | .undefinedCondition c => .undefinedCondition c
      | .trap => .trapped := by
  have pos : 0 < len := (decode_length decoded).2.1
  have hrip : m.core.rip.toNat = base.toNat + offset := by
    rw [at_offset]; exact loaded.toNat_add (by omega)
  refine step_of_fetch (bytes := (bytes.drop offset).take len) ?_ decoded
  rw [hrip]
  exact loaded.fetchBytes_sub pos fits

/-- A retiring step from the image: the form the straight-line tactic chains.
`instr ≠ .ret` is what makes it a retirement rather than a return. -/
theorem stepOpt_of_loaded {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {instr : Instr} {core : State} {memory : Memory}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (instr, len))
    (not_ret : instr ≠ .ret)
    (executed : exec instr m.core m.memory = .ok core memory) :
    stepOpt exit m = some ⟨core, memory⟩ := by
  rw [stepOpt_eq_some_iff, step_of_loaded loaded at_offset fits decoded, executed]
  simp [not_ret]

/-- The returning step: a `ret` whose popped target is the designated exit. -/
theorem step_returned_of_loaded {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {core : State} {memory : Memory}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (Instr.ret, len))
    (executed : exec .ret m.core m.memory = .ok core memory)
    (returns : core.rip = exit) :
    step exit m = .returned ⟨core, memory⟩ := by
  rw [step_of_loaded loaded at_offset fits decoded, executed]
  simp [returns]

/-! ## Describing a successor without naming it

`Ext.stepOpt`'s successors are nested structure updates: a `cmp` yields
`{ { c with flags := … } with rip := … }` and a following `jcc` wraps that
again. A step lemma that returns the successor *term* therefore makes each
step's conclusion contain the previous step's verbatim, and down a chain the
terms compound multiplicatively until the kernel reports "deep recursion" with
every ingredient proved. That is the failure three tracks hit independently.

`stepOpt_push` never had the problem, because it returns an *existential*
successor plus a `Stored` description rather than a `Memory.install` term.
These combinators generalise that discipline to the whole packaged family: a
step lemma's concrete conclusion goes in, and an opaque successor plus
projections for everything the *next* step can ask about — `rip`, the
registers, the flags, the memory — comes out. Each step's conclusion is then
the same size regardless of how long the chain is.

They are stated as wrappers rather than as replacements so that existing call
sites keep working; the opaque form of each packaged lemma is `…` and the
concrete one is `…_mk`.

**If a chain is slow, look at the successor terms, not at the length.** The
symptom is misleading: a run of a dozen instructions that will not elaborate
looks like a depth problem, and it is not. Two causes have been seen, both
fixed by opacity. One is the compounding above. The other is that a successor
carrying `AluOp.flagsN` carries `parityN`, which does not reduce symbolically
**but does try** — the elaborator spends its budget attempting it. Keeping the
flags behind a projection rather than in the term removes the opportunity.

A third member of the same family, and the least discoverable: **`omega` on a
goal containing `2 ^ 64` can push the kernel into deep recursion where
explicit `Nat.mod_eq_of_lt` rewrites cost nothing.** The goal looks small and
the tactic looks appropriate; the certificate is not. If an address
computation will not elaborate, replace `omega` by the `Nat.mod_eq_of_lt`
chain it is trying to find.

A fourth, contributed by the `-O2` track, and the one that reads as a dead
end rather than as a missing hypothesis: **a `Prop`-form index bound does not
rewrite inside `decide`.** Handing `simp` a proof of `i - 16 < 8` leaves the
`decide (i - 16 < 8)` in the goal untouched, so the goal sits there looking
unprovable when all that is missing is the `Bool`-level form. Hand the
comparison over already reduced — `decide_eq_true (by omega : …)` or
`decide_eq_false (by omega : ¬ …)` — and it goes through.

A fifth, and the root cause of every width mismatch either x86 track has hit:
**`rw` leaves a goal of the form `f E k = f E k` unclosed when the two sides
differ only in an implicit width.** `rw`'s closing reflexivity check runs at
*reducible* transparency, and `Sz.d.bits` does not unfold there, so the goal
survives looking like a real mismatch. A trailing `rfl`, which runs at default
transparency, closes every one.

The rule that follows, and the one to reach for first: **cross a width
boundary inside a lemma, exactly once, by `congrArg` on a `show … : BitVec n`
ascription — and never rewrite across it in a chain.** Once the equation is
*stated* at the narrow width the rewrite happens there and `congrArg` lifts it
back, so the chain applies lemmas only by `exact` and defeq absorbs every
mismatch silently. Measured on the clang `-O0` loop-3 body: eighty-six steps
carrying zero width-normalising `show`s and two `rw`s in total. The `-O2`
track reached the same rule from the other side by normalising at the *read*
(`read32 s r := (s.read r).setWidth 32`), which is one crossing at a different
boundary and cheaper when the equations are already written.

The family has one shape: in each case the tactic is the right tactic and the
goal is the right goal, and what has gone wrong is that some term is being
*evaluated* when it should stay symbolic, or is staying symbolic when it needs
to be evaluated. That is the thing to check first when a dozen instructions
will not elaborate. -/

/-- The register file after a step that writes at most `dst`. -/
structure WritesReg (before after : State) (dst : Silmaril.X86.Reg) (value : Word) : Prop where
  /-- The written register holds the new value. -/
  target : after.read dst = value
  /-- Every other register is untouched. -/
  other : ∀ r, r ≠ dst → after.read r = before.read r

/-- The register file is untouched. -/
def SameRegs (before after : State) : Prop := ∀ r, after.read r = before.read r

theorem SameRegs.writesReg {before after : State} (h : SameRegs before after)
    {dst : Silmaril.X86.Reg} : WritesReg before after dst (before.read dst) :=
  ⟨h dst, fun r _ => h r⟩

/-- A step that writes one register and sets the flags, opaquely. -/
theorem opaque_writeReg {exit : Word} {m : MState} {r : Silmaril.X86.Reg} {v : Word}
    {f : Silmaril.X86.Flags} {p : Word}
    (h : stepOpt exit m = some ⟨{ m.core.write r v with flags := f, rip := p }, m.memory⟩) :
    ∃ next, stepOpt exit m = some next ∧ next.core.rip = p ∧
      WritesReg m.core next.core r v ∧ next.core.flags = f ∧ next.memory = m.memory :=
  ⟨_, h, rfl, ⟨by simp, fun q hq => by simp [hq]⟩, rfl, rfl⟩

/-- A step that writes one register and leaves the flags alone, opaquely. -/
theorem opaque_writeReg_noFlags {exit : Word} {m : MState} {r : Silmaril.X86.Reg} {v p : Word}
    (h : stepOpt exit m = some ⟨{ m.core.write r v with rip := p }, m.memory⟩) :
    ∃ next, stepOpt exit m = some next ∧ next.core.rip = p ∧
      WritesReg m.core next.core r v ∧ next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  ⟨_, h, rfl, ⟨by simp, fun q hq => by simp [hq]⟩, rfl, rfl⟩

/-- A step that only sets the flags, opaquely. -/
theorem opaque_flagsOnly {exit : Word} {m : MState} {f : Silmaril.X86.Flags} {p : Word}
    (h : stepOpt exit m = some ⟨{ m.core with flags := f, rip := p }, m.memory⟩) :
    ∃ next, stepOpt exit m = some next ∧ next.core.rip = p ∧
      SameRegs m.core next.core ∧ next.core.flags = f ∧ next.memory = m.memory :=
  ⟨_, h, rfl, fun _ => rfl, rfl, rfl⟩

/-- A step that only moves RIP, opaquely. -/
theorem opaque_ripOnly {exit : Word} {m : MState} {p : Word}
    (h : stepOpt exit m = some ⟨{ m.core with rip := p }, m.memory⟩) :
    ∃ next, stepOpt exit m = some next ∧ next.core.rip = p ∧
      SameRegs m.core next.core ∧ next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  ⟨_, h, rfl, fun _ => rfl, rfl, rfl⟩

/-- A step that writes memory and no register, opaquely. The successor memory
is supplied by the caller (it is already opaque, from `Ext.storeN_isSome`). -/
theorem opaque_storeOnly {exit : Word} {m : MState} {p : Word} {after : Memory}
    (h : stepOpt exit m = some ⟨{ m.core with rip := p }, after⟩) :
    ∃ next, stepOpt exit m = some next ∧ next.core.rip = p ∧
      SameRegs m.core next.core ∧ next.core.flags = m.core.flags ∧ next.memory = after :=
  ⟨_, h, rfl, fun _ => rfl, rfl, rfl⟩

/-- A step that writes one register and memory, opaquely: `PUSH`. -/
theorem opaque_writeRegStore {exit : Word} {m : MState} {r : Silmaril.X86.Reg} {v p : Word}
    {after : Memory}
    (h : stepOpt exit m = some ⟨{ m.core.write r v with rip := p }, after⟩) :
    ∃ next, stepOpt exit m = some next ∧ next.core.rip = p ∧
      WritesReg m.core next.core r v ∧ next.core.flags = m.core.flags ∧
      next.memory = after :=
  ⟨_, h, rfl, ⟨by simp, fun q hq => by simp [hq]⟩, rfl, rfl⟩

/-- A step that writes two registers, opaquely: `POP`. -/
theorem opaque_writeTwo {exit : Word} {m : MState} {r : Silmaril.X86.Reg} {sp v p : Word}
    (h : stepOpt exit m =
      some ⟨{ (m.core.write .rsp sp).write r v with rip := p }, m.memory⟩) :
    ∃ next, stepOpt exit m = some next ∧ next.core.rip = p ∧
      next.core.read r = v ∧ (r ≠ .rsp → next.core.read .rsp = sp) ∧
      (∀ q, q ≠ r → q ≠ .rsp → next.core.read q = m.core.read q) ∧
      next.core.flags = m.core.flags ∧ next.memory = m.memory :=
  ⟨_, h, rfl, by simp, fun hr => by simp [Ne.symm hr], fun q hq hq' => by simp [hq, hq'],
    rfl, rfl⟩

/-- A returning step, opaquely. -/
theorem opaque_returned {exit : Word} {m : MState} {sp p : Word}
    (h : step exit m = .returned ⟨{ m.core.write .rsp sp with rip := p }, m.memory⟩) :
    ∃ final, step exit m = .returned final ∧ final.core.rip = p ∧
      WritesReg m.core final.core .rsp sp ∧ final.core.flags = m.core.flags ∧
      final.memory = m.memory :=
  ⟨_, h, rfl, ⟨by simp, fun q hq => by simp [hq]⟩, rfl, rfl⟩

/-! ## Packaged steps that touch no memory

A register-destination ALU operation and a branch read and write no memory, so
they need neither a permission nor a disjointness fact: **they cannot fault**.
Threading an entry hypothesis through them is wasted work, and the proof terms
are smaller without it.

Each lemma takes the result as an *equation* supplied by the caller rather
than computing it, so that the conclusion arrives in the shape the caller
wants and no normalisation — and so no defeq search over a concrete operand —
happens at the use site. -/

/-- One `op r, imm32` (`81 /digit id`) with a register destination,
`op ≠ cmp`. -/
theorem stepOpt_aluI_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {r : Silmaril.X86.Reg}
    {imm : BitVec 32} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI sz op (.reg r) imm, len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core r) (imm.signExtend sz.bits)).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write r result with
        flags := AluOp.flagsN op (sz.read m.core r) (imm.signExtend sz.bits),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluI sz op (.reg r) imm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM, not_cmp, ite_false,
    writeRM, Option.map_some, retire, Sz.write]

/-- One `op r, imm8` (`83 /digit ib`) with a register destination,
`op ≠ cmp`. This is the form clang `-O0` uses for every index increment. -/
theorem stepOpt_aluI8_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {r : Silmaril.X86.Reg}
    {imm : BitVec 8} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI8 sz op (.reg r) imm, len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core r) (imm.signExtend sz.bits)).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write r result with
        flags := AluOp.flagsN op (sz.read m.core r) (imm.signExtend sz.bits),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluI8 sz op (.reg r) imm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM, not_cmp, ite_false,
    writeRM, Option.map_some, retire, Sz.write]

/-- One `op r, r'` (`03 0B 23 2B 33 3B /r`, the direction-1 form) with both
operands registers, `op ≠ cmp`. -/
theorem stepOpt_aluR_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {dst src : Silmaril.X86.Reg}
    {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluR sz op dst (.reg src), len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core dst) (sz.read m.core src)).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
        flags := AluOp.flagsN op (sz.read m.core dst) (sz.read m.core src),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluR sz op dst (.reg src)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStepR, readRM, not_cmp, ite_false,
    retire, Sz.write]

/-- One `op r/m, r` (`01 09 21 29 31 33 39 /r`, the direction-0 form) with
both operands registers, `op ≠ cmp`. `or %eax,%ecx` is this form. -/
theorem stepOpt_alu_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {dst src : Silmaril.X86.Reg}
    {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.alu sz op (.reg dst) src, len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core dst) (sz.read m.core src)).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
        flags := AluOp.flagsN op (sz.read m.core dst) (sz.read m.core src),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.alu sz op (.reg dst) src).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM, not_cmp, ite_false,
    writeRM, Option.map_some, retire, Sz.write]

/-- One shift or rotate by an immediate with a register destination
(`C1 /digit ib`). Like the ALU forms, it touches no memory. -/
theorem stepOpt_shift_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : ShiftOp} {r : Silmaril.X86.Reg} {n : BitVec 8}
    {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded :
      decode ((bytes.drop offset).take len) = some (.shift sz op (.reg r) (.imm n), len))
    (result_eq : (op.result (sz.read m.core r) (n.toNat % sz.bits)).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write r result with
        flags := op.flags (sz.read m.core r) (n.toNat % sz.bits) m.core.flags,
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.shift sz op (.reg r) (.imm n)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, Count.raw, readRM, writeRM,
    Option.map_some, retire, Sz.write]

/-- One `movsxd r64, r32` (`REX.W 63 /r` with `mod = 11`). -/
theorem stepOpt_movsxd_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {dst src : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movsxd dst (.reg src), len))
    (result_eq : (Sz.d.read m.core src).signExtend 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.movsxd dst (.reg src)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, readRM, Option.map_some, retire]

/-- One `cdqe` (`REX.W 98`): sign-extend `EAX` into `RAX`. clang `-O0` emits
this wherever a C `int` index is used as an address offset. -/
theorem stepOpt_cdqe_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.cxe .q, len))
    (result_eq : (Sz.d.read m.core .rax).signExtend 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write .rax result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.cxe .q).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, retire]

/-- One `jmp rel32`. -/
theorem stepOpt_jmp_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {rel : BitVec 32} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jmp rel, len))
    (target_eq : base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64 = target) :
    stepOpt exit m = some ⟨{ m.core with rip := target }, m.memory⟩ := by
  subst target_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.jmp rel).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl]

/-- One `jcc rel32`, taken or not according to the condition. The hypothesis
`cond` is where `Ext.eval_cmp` and its specialisations are used, and it is
also what rules out a branch on an undefined flag. -/
theorem stepOpt_jcc_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {c : Cond} {rel : BitVec 32} {taken : Bool} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jcc c rel, len))
    (cond : c.eval m.core.flags = some taken)
    (target_eq : (if taken then base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64
      else base + BitVec.ofNat 64 (offset + len)) = target) :
    stepOpt exit m = some ⟨{ m.core with rip := target }, m.memory⟩ := by
  subst target_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.jcc c rel).length = len := (decode_length decoded).1.symm
  cases taken <;> simp [exec, hl, at_offset, rip_advance base rfl, cond]

/-! ## Straight-line runs -/

/-- `Runs exit n initial final`: the machine retires exactly `n` instructions,
reaching `final`. This is `Machine.Execution.run` as a relation, so that a
block composes by `Runs.trans` without `Option` plumbing. -/
def Runs (exit : Word) (n : Nat) (initial final : MState) : Prop :=
  Machine.Execution.run (stepOpt exit) n initial = some final

theorem Runs.nil {exit : Word} (m : MState) : Runs exit 0 m m := rfl

theorem Runs.cons {exit : Word} {n : Nat} {m next final : MState}
    (head : stepOpt exit m = some next) (tail : Runs exit n next final) :
    Runs exit (n + 1) m final := by
  rw [Runs, Machine.Execution.run_succ, head, Option.bind_some]
  exact tail

/-- A single retirement. -/
theorem Runs.one {exit : Word} {m next : MState} (head : stepOpt exit m = some next) :
    Runs exit 1 m next := Runs.cons head (Runs.nil next)

theorem Runs.trans {exit : Word} {n k : Nat} {a b c : MState}
    (first : Runs exit n a b) (second : Runs exit k b c) : Runs exit (n + k) a c := by
  rw [Runs, Machine.Execution.run_add, first, Option.bind_some]
  exact second

/-- A run of a block, appended to one more step at the front: the shape a
forward symbolic-execution tactic produces. -/
theorem Runs.snoc {exit : Word} {n : Nat} {a b c : MState}
    (first : Runs exit n a b) (last : stepOpt exit b = some c) : Runs exit (n + 1) a c :=
  first.trans (Runs.one last)

/-! ## Returning, and why the final state is unique -/

/-- A run and a returning step make a `Returns`. This is also the liveness
witness: executing the function *is* the proof that it returns. -/
theorem Returns.intro {exit : Word} {n : Nat} {initial mid final : MState}
    (run : Runs exit n initial mid) (returned : step exit mid = .returned final) :
    Returns exit initial final := ⟨n, mid, run, returned⟩

/-- A returning state has no retirement, so a run stops there. -/
theorem stepOpt_eq_none_of_returned {exit : Word} {m final : MState}
    (returned : step exit m = .returned final) : stepOpt exit m = none := by
  simp [stepOpt, returned]

/-- No non-empty run leaves a returning state. -/
theorem run_eq_none_of_returned {exit : Word} {m final : MState}
    (returned : step exit m = .returned final) {k : Nat} (pos : 0 < k) :
    Machine.Execution.run (stepOpt exit) k m = none := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Machine.Execution.run_succ, stepOpt_eq_none_of_returned returned]
  rfl

/-- **Determinism of returning.** `Returns` existentially quantifies the step
count, but a run cannot pass a returning state and the machine is a function,
so once one returning run is exhibited every `Returns` from the same initial
state has the same final state.

This is what makes a contract of the shape `Returns … → Post …` provable by
symbolic execution: compute the run once, and the hypothesis collapses to an
equation. -/
theorem Returns.eq_of_run {exit : Word} {n : Nat} {initial mid final other : MState}
    (run : Runs exit n initial mid) (returned : step exit mid = .returned final)
    (h : Returns exit initial other) : other = final := by
  obtain ⟨k, mid', run', returned'⟩ := h
  rcases Nat.lt_trichotomy k n with hlt | heq | hgt
  · exfalso
    have : Machine.Execution.run (stepOpt exit) (k + (n - k)) initial = some mid := by
      rw [show k + (n - k) = n by omega]; exact run
    rw [Machine.Execution.run_add, run', Option.bind_some,
      run_eq_none_of_returned returned' (by omega)] at this
    simp at this
  · subst heq
    rw [Runs] at run
    rw [run'] at run
    cases Option.some.inj run
    rw [returned] at returned'
    exact (Outcome.returned.inj returned').symm
  · exfalso
    have : Machine.Execution.run (stepOpt exit) (n + (k - n)) initial = some mid' := by
      rw [show n + (k - n) = k by omega]; exact run'
    rw [Machine.Execution.run_add, run, Option.bind_some,
      run_eq_none_of_returned returned (by omega)] at this
    simp at this

/-- The packaged form: one symbolic execution to the `ret` settles both
non-vacuity (`Returns` is inhabited) and determinism (it is inhabited once). -/
theorem returns_iff_eq {exit : Word} {n : Nat} {initial mid final : MState}
    (run : Runs exit n initial mid) (returned : step exit mid = .returned final)
    (other : MState) : Returns exit initial other ↔ other = final := by
  refine ⟨Returns.eq_of_run run returned, ?_⟩
  rintro rfl
  exact Returns.intro run returned

/-! ## Comparisons with a register operand

`CMP` writes no register and no memory: it is pure flag computation, so like
the other register-only forms it cannot fault. These three cover the shapes a
loop head uses when its counter lives in a register rather than a stack slot,
which is every optimised build. -/

/-- `cmp r/m, r` with both operands registers (`39 /r`). -/
theorem stepOpt_cmp_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst src : Silmaril.X86.Reg}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.alu sz .cmp (.reg dst) src, len)) :
    stepOpt exit m = some ⟨{ m.core with
        flags := AluOp.flagsN .cmp (sz.read m.core dst) (sz.read m.core src),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.alu sz .cmp (.reg dst) src).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM, ite_true, retire]

/-- `cmp r, imm8` (`83 /7 ib`) with a register operand. -/
theorem stepOpt_cmpI8_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {r : Silmaril.X86.Reg} {imm : BitVec 8}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI8 sz .cmp (.reg r) imm, len)) :
    stepOpt exit m = some ⟨{ m.core with
        flags := AluOp.flagsN .cmp (sz.read m.core r) (imm.signExtend sz.bits),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluI8 sz .cmp (.reg r) imm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM, ite_true, retire]

/-- `cmp r, imm32` (`81 /7 id`) with a register operand. -/
theorem stepOpt_cmpI_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {r : Silmaril.X86.Reg} {imm : BitVec 32}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI sz .cmp (.reg r) imm, len)) :
    stepOpt exit m = some ⟨{ m.core with
        flags := AluOp.flagsN .cmp (sz.read m.core r) (imm.signExtend sz.bits),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluI sz .cmp (.reg r) imm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM, ite_true, retire]

/-! ## A rule: writing no memory means needing nothing

Three independent sightings across three tracks — `prologue_sub` here,
`WWordsRead.succ` and a whole 64-iteration loop trace at `-O2` — make this a
rule rather than a coincidence:

> **A step, or a loop, that writes no memory needs neither a permission nor a
> disjointness hypothesis.**

It cannot fault on a store it does not make, it cannot invalidate a `Loaded`
image, and every memory-shaped field of an invariant is preserved for free.
Such a lemma should take no entry state, no `Region.Disjoint`, and no frame
bound; if one is threaded through anyway it is proof-term weight for nothing,
and Lean's unused-binder linter will say so. Every lemma in this section is an
instance, as are `jmp`, `jcc` and all the comparisons.

The converse is worth stating too: the hypotheses a step lemma genuinely needs
are exactly one per *access* — a permission for each store, a slot fact for
each load — and nothing per instruction. -/

/-! ## More register-only steps

`mov r, r'`, the rel8 branches, `BSWAP` and `INC`/`DEC` on a register. All
read and write no memory, so none of them can fault. -/

/-- `mov r, r'` (`89 /r` with `mod = 11`). `Ext` packaged `mov` to and from
memory but not register to register, which every optimisation level uses
constantly. -/
theorem stepOpt_mov_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst src : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.mov sz (.reg dst) src, len))
    (result_eq : (sz.read m.core src).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.mov sz (.reg dst) src).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, writeRM, retire, Sz.write]

/-- `jmp rel8` (`EB cb`). -/
theorem stepOpt_jmp8_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {rel : BitVec 8} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jmp8 rel, len))
    (target_eq : base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64 = target) :
    stepOpt exit m = some ⟨{ m.core with rip := target }, m.memory⟩ := by
  subst target_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.jmp8 rel).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl]

/-- `jcc rel8` (`70+cc cb`). **Not** an instance of `stepOpt_jcc`, whose
displacement is a `BitVec 32`: every optimised loop backedge is rel8. -/
theorem stepOpt_jcc8_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {c : Cond} {rel : BitVec 8} {taken : Bool} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jcc8 c rel, len))
    (cond : c.eval m.core.flags = some taken)
    (target_eq : (if taken then base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64
      else base + BitVec.ofNat 64 (offset + len)) = target) :
    stepOpt exit m = some ⟨{ m.core with rip := target }, m.memory⟩ := by
  subst target_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.jcc8 c rel).length = len := (decode_length decoded).1.symm
  cases taken <;> simp [exec, hl, at_offset, rip_advance base rfl, cond]

/-- `bswap r` (`0F C8+r`): the byte reversal every optimised build uses where
`-O0` writes four `movzbl`/`shl`/`or` groups. -/
theorem stepOpt_bswap_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.bswap sz dst, len))
    (result_eq : (byteSwap sz (sz.read m.core dst)).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.bswap sz dst).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, retire, Sz.write]

/-- `inc r` / `dec r` (`FF /0`, `FF /1`) on a register. Neither changes CF. -/
theorem stepOpt_incdec_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dec : Bool} {r : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.incdec sz dec (.reg r), len))
    (result_eq : (if dec then sz.read m.core r - 1#sz.bits
      else sz.read m.core r + 1#sz.bits).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write r result with
        flags := if dec then decFlagsN (sz.read m.core r) m.core.flags
          else incFlagsN (sz.read m.core r) m.core.flags,
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.incdec sz dec (.reg r)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, readRM, writeRM, Option.map_some,
    retire, Sz.write]

/-- `not r` (`F7 /2`) on a register. NOT is the one ALU-shaped instruction
that leaves the flags alone. -/
theorem stepOpt_not_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {r : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.unary sz .not (.reg r), len))
    (result_eq : (~~~(sz.read m.core r)).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write r result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.unary sz .not (.reg r)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, readRM, writeRM, retire, Sz.write]

/-- `cmp eAX/rAX, imm32` (`3D id`), the accumulator form. -/
theorem stepOpt_cmpA_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {imm : BitVec 32}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluA sz .cmp imm, len)) :
    stepOpt exit m = some ⟨{ m.core with
        flags := AluOp.flagsN .cmp (sz.read m.core .rax) (imm.signExtend sz.bits),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluA sz .cmp imm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM, ite_true, retire]

/-- One `not r`, with the successor left opaque. -/
theorem stepOpt_not_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {r : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.unary sz .not (.reg r), len))
    (result_eq : (~~~(sz.read m.core r)).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core r result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_not_reg_mk loaded at_offset fits decoded result_eq)

/-- One accumulator `cmp`, with the successor left opaque. -/
theorem stepOpt_cmpA {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {imm : BitVec 32}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluA sz .cmp imm, len)) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = AluOp.flagsN .cmp (sz.read m.core .rax) (imm.signExtend sz.bits) ∧
      next.memory = m.memory :=
  opaque_flagsOnly (stepOpt_cmpA_mk loaded at_offset fits decoded)

/-! ## The opaque forms

The same steps, with the successor existentially bound and described by
projections instead of named by a structure-update term. These are the forms
to chain; the `…_mk` variants above name the successor and are kept for
callers that want it. -/

/-- One `op r, imm32` with a register destination, with the successor left opaque. -/
theorem stepOpt_aluI_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {r : Silmaril.X86.Reg}
    {imm : BitVec 32} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI sz op (.reg r) imm, len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core r) (imm.signExtend sz.bits)).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core r result ∧
      next.core.flags = AluOp.flagsN op (sz.read m.core r) (imm.signExtend sz.bits) ∧
      next.memory = m.memory :=
  opaque_writeReg (stepOpt_aluI_reg_mk loaded at_offset fits decoded not_cmp result_eq)

/-- One `op r, imm8` with a register destination, with the successor left opaque. -/
theorem stepOpt_aluI8_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {r : Silmaril.X86.Reg}
    {imm : BitVec 8} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI8 sz op (.reg r) imm, len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core r) (imm.signExtend sz.bits)).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core r result ∧
      next.core.flags = AluOp.flagsN op (sz.read m.core r) (imm.signExtend sz.bits) ∧
      next.memory = m.memory :=
  opaque_writeReg (stepOpt_aluI8_reg_mk loaded at_offset fits decoded not_cmp result_eq)

/-- One `op r, r'`, the direction-1 form, with the successor left opaque. -/
theorem stepOpt_aluR_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {dst src : Silmaril.X86.Reg}
    {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluR sz op dst (.reg src), len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core dst) (sz.read m.core src)).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = AluOp.flagsN op (sz.read m.core dst) (sz.read m.core src) ∧
      next.memory = m.memory :=
  opaque_writeReg (stepOpt_aluR_reg_mk loaded at_offset fits decoded not_cmp result_eq)

/-- One `op r/m, r`, the direction-0 form, with the successor left opaque. -/
theorem stepOpt_alu_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {dst src : Silmaril.X86.Reg}
    {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.alu sz op (.reg dst) src, len))
    (not_cmp : op ≠ .cmp)
    (result_eq :
      (AluOp.resultN op (sz.read m.core dst) (sz.read m.core src)).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = AluOp.flagsN op (sz.read m.core dst) (sz.read m.core src) ∧
      next.memory = m.memory :=
  opaque_writeReg (stepOpt_alu_reg_mk loaded at_offset fits decoded not_cmp result_eq)

/-- One a shift or rotate by an immediate, with the successor left opaque. -/
theorem stepOpt_shift_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : ShiftOp} {r : Silmaril.X86.Reg} {n : BitVec 8}
    {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded :
      decode ((bytes.drop offset).take len) = some (.shift sz op (.reg r) (.imm n), len))
    (result_eq : (op.result (sz.read m.core r) (n.toNat % sz.bits)).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core r result ∧
      next.core.flags = op.flags (sz.read m.core r) (n.toNat % sz.bits) m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg (stepOpt_shift_reg_mk loaded at_offset fits decoded result_eq)

/-- One `movsxd r64, r32`, with the successor left opaque. -/
theorem stepOpt_movsxd_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {dst src : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movsxd dst (.reg src), len))
    (result_eq : (Sz.d.read m.core src).signExtend 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_movsxd_reg_mk loaded at_offset fits decoded result_eq)

/-- One `cdqe`, with the successor left opaque. -/
theorem stepOpt_cdqe {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.cxe .q, len))
    (result_eq : (Sz.d.read m.core .rax).signExtend 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core .rax result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_cdqe_mk loaded at_offset fits decoded result_eq)

/-- One `jmp rel32`, with the successor left opaque. -/
theorem stepOpt_jmp {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {rel : BitVec 32} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jmp rel, len))
    (target_eq : base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64 = target) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = target ∧
      SameRegs m.core next.core ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_ripOnly (stepOpt_jmp_mk loaded at_offset fits decoded target_eq)

/-- One `jcc rel32`, with the successor left opaque. -/
theorem stepOpt_jcc {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {c : Cond} {rel : BitVec 32} {taken : Bool} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jcc c rel, len))
    (cond : c.eval m.core.flags = some taken)
    (target_eq : (if taken then base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64
      else base + BitVec.ofNat 64 (offset + len)) = target) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = target ∧
      SameRegs m.core next.core ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_ripOnly (stepOpt_jcc_mk loaded at_offset fits decoded cond target_eq)

/-- One comparison with a register operand, successor left opaque. -/
theorem stepOpt_cmp_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst src : Silmaril.X86.Reg}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.alu sz .cmp (.reg dst) src, len)) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = AluOp.flagsN .cmp (sz.read m.core dst) (sz.read m.core src) ∧
      next.memory = m.memory :=
  opaque_flagsOnly (stepOpt_cmp_reg_mk loaded at_offset fits decoded)

/-- One comparison with a register operand, successor left opaque. -/
theorem stepOpt_cmpI8_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {r : Silmaril.X86.Reg} {imm : BitVec 8}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI8 sz .cmp (.reg r) imm, len)) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = AluOp.flagsN .cmp (sz.read m.core r) (imm.signExtend sz.bits) ∧
      next.memory = m.memory :=
  opaque_flagsOnly (stepOpt_cmpI8_reg_mk loaded at_offset fits decoded)

/-- One comparison with a register operand, successor left opaque. -/
theorem stepOpt_cmpI_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {r : Silmaril.X86.Reg} {imm : BitVec 32}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI sz .cmp (.reg r) imm, len)) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = AluOp.flagsN .cmp (sz.read m.core r) (imm.signExtend sz.bits) ∧
      next.memory = m.memory :=
  opaque_flagsOnly (stepOpt_cmpI_reg_mk loaded at_offset fits decoded)

/-- One register-to-register move, with the successor left opaque. -/
theorem stepOpt_mov_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst src : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.mov sz (.reg dst) src, len))
    (result_eq : (sz.read m.core src).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_mov_reg_mk loaded at_offset fits decoded result_eq)

/-- `lea dst, [rip + disp32]`, the small-code-model way to materialise the
address of a `.rodata` object. The result is supplied as an equation so the
caller can discharge the relocation arithmetic — in practice from the layout
constraint that the displacement fits in the signed 32-bit field — rather than
leaving a `signExtend` in every subsequent goal. -/
theorem stepOpt_lea_rip_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {disp : BitVec 32} {dst : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.lea .q dst (Mem.ofRip disp), len))
    (result_eq : base + BitVec.ofNat 64 (offset + len) + disp.signExtend 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.lea .q dst (Mem.ofRip disp)).length = len := (decode_length decoded).1.symm
  have hex : exec (.lea .q dst (Mem.ofRip disp)) m.core m.memory
      = .ok { m.core.write dst (m.core.rip +
            BitVec.ofNat 64 (Instr.lea .q dst (Mem.ofRip disp)).length + disp.signExtend 64) with
          rip := m.core.rip +
            BitVec.ofNat 64 (Instr.lea .q dst (Mem.ofRip disp)).length } m.memory := by
    simp [exec, retire, Mem.addr, Mem.ofRip]
  rw [hex, hl, at_offset, rip_advance base rfl]

/-- `lea dst, [rip + disp32]`, with the successor left opaque. -/
theorem stepOpt_lea_rip {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {disp : BitVec 32} {dst : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.lea .q dst (Mem.ofRip disp), len))
    (result_eq : base + BitVec.ofNat 64 (offset + len) + disp.signExtend 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_lea_rip_mk loaded at_offset fits decoded result_eq)

/-- **A rotate built from two shifts and an `or`.** Compilers without a rotate
idiom — and `clang -O0` in particular — emit `x >>> k ||| x <<< (w - k)` where
the source wrote a rotate. This says that is the rotate, at any width.

Generic on purpose: nothing here is about SHA-256 or about x86. Any image that
rotates will produce this shape. -/
theorem rotateRight_of_shifts {w : Nat} (x : BitVec w) {k : Nat} (h : k < w) :
    (x >>> k) ||| (x <<< (w - k)) = x.rotateRight k := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt h]
  rfl

/-- One rel8 jump, with the successor left opaque. -/
theorem stepOpt_jmp8 {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {rel : BitVec 8} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jmp8 rel, len))
    (target_eq : base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64 = target) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = target ∧
      SameRegs m.core next.core ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_ripOnly (stepOpt_jmp8_mk loaded at_offset fits decoded target_eq)

/-- One rel8 conditional branch, with the successor left opaque. -/
theorem stepOpt_jcc8 {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {c : Cond} {rel : BitVec 8} {taken : Bool} {target : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jcc8 c rel, len))
    (cond : c.eval m.core.flags = some taken)
    (target_eq : (if taken then base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64
      else base + BitVec.ofNat 64 (offset + len)) = target) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = target ∧
      SameRegs m.core next.core ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_ripOnly (stepOpt_jcc8_mk loaded at_offset fits decoded cond target_eq)

/-- One byte reversal, with the successor left opaque. -/
theorem stepOpt_bswap {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.bswap sz dst, len))
    (result_eq : (byteSwap sz (sz.read m.core dst)).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_bswap_mk loaded at_offset fits decoded result_eq)

/-- One increment or decrement, with the successor left opaque. -/
theorem stepOpt_incdec_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dec : Bool} {r : Silmaril.X86.Reg} {result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.incdec sz dec (.reg r), len))
    (result_eq : (if dec then sz.read m.core r - 1#sz.bits
      else sz.read m.core r + 1#sz.bits).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core r result ∧
      next.core.flags = (if dec then decFlagsN (sz.read m.core r) m.core.flags
        else incFlagsN (sz.read m.core r) m.core.flags) ∧
      next.memory = m.memory :=
  opaque_writeReg (stepOpt_incdec_reg_mk loaded at_offset fits decoded result_eq)

end Silmaril.X86.Ext
