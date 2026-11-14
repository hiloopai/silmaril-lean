module

public import Silmaril.Machine.X86.Str9.Defs
public import Silmaril.Machine.X86.Open9.Thms
public import Silmaril.Machine.X86.Safe.Open9.Thms
public import Silmaril.Machine.X86.Sse9.Defs
import Silmaril.Proofs.Machine.X86.Str9.Decode
import Silmaril.Proofs.Machine.X86.Str9.Step

/-!
# `Str9`: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/Machine/X86/Str9/{Decode,Step}.lean`).

**Conservative extension** (AD-6).
* `instExtendsOpen9 : ExtendsOpen9 step` (the class is new, in `Str9/Defs.lean`, C12) and
  `Safe.instExtendsOpenStr9 : Safe.ExtendsOpen step`: every `Open9` (so every `Open`) step is
  a `Str9` step. `run_of_open9`, `reaches_of_open9`: so is every run.
* `step_cases`: every step is an `Open9` step, or (when `Open9` has no step) a string form
  fetched at the program counter.
* `FnContract.toStr9`: every `FnContract Open9.isa` is a `FnContract Str9.isa` with the same
  spec.

**The string laws.**
* `isa`: the machine as a `SegVC.Isa MState` over `Str9.Instr` (law: `step_of_listed`).
* `step_of_listed_str`, `step_of_fetch_str`: a listed string form at the program counter
  that executes is one step.
* `rep_movsq_copy`, `rep_stosq_fill`: **`k + 1` elements are `k + 1` steps**, ending past the
  instruction with `RepDone` (rcx `0`, pointers advanced by `8 (k + 1)`, the rest of the core
  unchanged), the memory being `copyQ`/`fillQ`. Hypotheses: the instruction bytes are fetched
  at RIP and none of them is writable (so a store cannot change the code), `0 < k + 1 < 2^64`.
* `rep_movsq_zero`, `rep_stosq_zero`: `rcx = 0` is one step that only advances RIP.
* `step_movsq_elem`, `step_stosq_elem`, `step_movsb`: single elements.

**Opcode disjointness** (AD-6), by `decide`:
* `table_disjoint_sse9`: `Str9.table` vs `Sse9`'s keys (`sse9Table`, every accepted REX);
  `sse9Table_decodes` checks each of those keys against `Sse9.decodeSse` (with a ModRM byte),
  and `sse_rejects_str` checks that `Sse9.pSse` rejects (`.bad`) each Str9 encoding.
* `table_disjoint_atomic9`: `Str9.table` vs `atomic9Table`, the table of concurrency.md §2.2
  (K1 has not merged; DT2 re-checks against `Atomic9.decode`).
* `decodeStr_none_of_key`: so bytes that begin with any key of such a table are never decoded
  as a string form.

What is **not** claimed: the semantics is a handwritten model of the SDM (DF clear, element
per step), not proved to match hardware; the difftest is . No certificate kind
(`Cert`, `BlockCert`, `Bir`) has string blocks; `seg9` (Z3b) and zlib's per-function proofs
step these forms with `step_of_listed_str` and the run lemmas.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Str9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-! ## Conservative extension -/

/-- **Every `Open9` step is a step.** -/
theorem step_of_open9 {m m' : MState} (h : Open9.step m = some m') : step m = some m' :=
  Silmaril.Proofs.Machine.X86.Str9.step_of_open9 h

/-- **`Str9` extends the open machine over `Ext9`.** -/
instance instExtendsOpen9 : ExtendsOpen9 step := ⟨fun h => step_of_open9 h⟩

/-- **Every step is an `Open9` step, or a string step.** -/
theorem step_cases {m m' : MState} (h : step m = some m') :
    Open9.step m = some m' ∨
      (Open9.step m = none ∧ ∃ i n, fetchStr m.memory m.core.rip.toNat = some (some (i, n)) ∧
        Open.ofResult (execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 n)) = some m') :=
  Silmaril.Proofs.Machine.X86.Str9.step_cases h

theorem run_of_open9 (k : Nat) {a b : MState} (h : run Open9.step k a = some b) :
    run step k a = some b :=
  Silmaril.Proofs.Machine.X86.Str9.run_of_open9 k h

theorem reaches_of_open9 {a b : MState} (h : Reaches Open9.step a b) : Reaches step a b :=
  Silmaril.Proofs.Machine.X86.Str9.reaches_of_open9 h

/-- Safety on `Open9` is safety on `Str9`. -/
theorem safeN_of_open9 {Q : MState → Prop} {n : Nat} {m : MState}
    (h : Safe.SafeN Open9.step Q n m) : Safe.SafeN step Q n m :=
  Safe.safeN_of_refines ExtendsOpen9.ext h

/-! ## The string laws -/

/-- **The fetch form of the string law.** -/
theorem step_of_fetch_str {m : MState} {l : Nat} {w : List Byte} {i : Str} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.Machine.X86.Str9.step_of_fetch_str fetched hdec hx

/-- **The string listing law.** -/
theorem step_of_listed_str {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Str}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.Machine.X86.Str9.step_of_listed_str hl hrip hfit hdec hx

/-- **The listing law of the machine** (`Ext9` instructions and string forms). -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.Machine.X86.Str9.step_of_listed hl hrip hfit hdec hx

/-- **The string machine as a segment-VC instance.** -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa MState where
  Instr := Instr
  instDecEq := inferInstance
  decode := decode
  exec := exec
  core := MState.core
  mem := MState.memory
  upd := fun _ c m => ⟨c, m⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_listed hl hrip hfit hdec hx

@[simp] theorem isa_step : isa.step = step := rfl

/-- A store changes only writable bytes: fetches from a range with no writable byte, and its
non-writability, are kept. -/
theorem fetch_keep {mem mem' : Memory} {a : Word} {k : Nat} {v : Word}
    (h : storeN mem a k v = some mem') {p l : Nat}
    (hro : ∀ o < l, mem.permits .write (p + o) = false) :
    mem'.fetchBytes p l = mem.fetchBytes p l ∧ ∀ o < l, mem'.permits .write (p + o) = false :=
  Silmaril.Proofs.Machine.X86.Str9.fetch_keep h hro

/-- `movsb`: one byte from `[rsi]` to `[rdi]`, both pointers advanced by one. -/
theorem step_movsb {c : State} {mem mem1 : Memory} {v : Word}
    (hf : mem.fetchBytes c.rip.toNat 1 = some Str.movsb.bytes)
    (hl : loadN mem (c.read .rsi) 1 = some v) (hs : storeN mem (c.read .rdi) 1 v = some mem1) :
    step ⟨c, mem⟩ = some ⟨{ (c.write .rsi (c.read .rsi + 1)).write .rdi (c.read .rdi + 1) with
      rip := c.rip + BitVec.ofNat 64 1 }, mem1⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) (i := .movsb) hf (by decide) (by simp only [execStr, hl, hs])

/-- One element of `rep movsq` (`rcx ≠ 0`). -/
theorem step_movsq_elem {c : State} {mem mem1 : Memory} {v : Word}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes) (hc : c.read .rcx ≠ 0)
    (hl : loadN mem (c.read .rsi) 8 = some v) (hs : storeN mem (c.read .rdi) 8 v = some mem1) :
    step ⟨c, mem⟩ = some ⟨{ ((c.write .rsi (c.read .rsi + 8)).write .rdi (c.read .rdi + 8)).write
        .rcx (c.read .rcx - 1) with
      rip := if c.read .rcx - 1 = 0 then c.rip + BitVec.ofNat 64 3 else c.rip }, mem1⟩ :=
  Silmaril.Proofs.Machine.X86.Str9.step_movsq_elem hf hc hl hs

/-- One element of `rep stosq` (`rcx ≠ 0`). -/
theorem step_stosq_elem {c : State} {mem mem1 : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes) (hc : c.read .rcx ≠ 0)
    (hs : storeN mem (c.read .rdi) 8 (c.read .rax) = some mem1) :
    step ⟨c, mem⟩ = some ⟨{ (c.write .rdi (c.read .rdi + 8)).write .rcx (c.read .rcx - 1) with
      rip := if c.read .rcx - 1 = 0 then c.rip + BitVec.ofNat 64 3 else c.rip }, mem1⟩ :=
  Silmaril.Proofs.Machine.X86.Str9.step_stosq_elem hf hc hs

/-- `rep movsq` with `rcx = 0` only advances RIP. -/
theorem rep_movsq_zero {c : State} {mem : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes) (hc : c.read .rcx = 0) :
    step ⟨c, mem⟩ = some ⟨{ c with rip := c.rip + BitVec.ofNat 64 3 }, mem⟩ :=
  Silmaril.Proofs.Machine.X86.Str9.rep_movsq_zero hf hc

/-- `rep stosq` with `rcx = 0` only advances RIP. -/
theorem rep_stosq_zero {c : State} {mem : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes) (hc : c.read .rcx = 0) :
    step ⟨c, mem⟩ = some ⟨{ c with rip := c.rip + BitVec.ofNat 64 3 }, mem⟩ :=
  Silmaril.Proofs.Machine.X86.Str9.rep_stosq_zero hf hc

/-- **`rep movsq` of `k + 1` quadwords is exactly `k + 1` steps**, computing `copyQ`. -/
theorem rep_movsq_copy (k : Nat) {c : State} {mem mem' : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes)
    (hro : ∀ o < 3, mem.permits .write (c.rip.toNat + o) = false)
    (hk : k + 1 < 2 ^ 64) (hc : c.read .rcx = BitVec.ofNat 64 (k + 1))
    (hcopy : copyQ (k + 1) (c.read .rsi) (c.read .rdi) mem = some mem') :
    ∃ c', run step (k + 1) ⟨c, mem⟩ = some ⟨c', mem'⟩ ∧ RepDone true (k + 1) c c' :=
  Silmaril.Proofs.Machine.X86.Str9.rep_movsq_copy k hf hro hk hc hcopy

/-- **`rep stosq` of `k + 1` quadwords is exactly `k + 1` steps**, computing `fillQ`. -/
theorem rep_stosq_fill (k : Nat) {c : State} {mem mem' : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes)
    (hro : ∀ o < 3, mem.permits .write (c.rip.toNat + o) = false)
    (hk : k + 1 < 2 ^ 64) (hc : c.read .rcx = BitVec.ofNat 64 (k + 1))
    (hfill : fillQ (k + 1) (c.read .rax) (c.read .rdi) mem = some mem') :
    ∃ c', run step (k + 1) ⟨c, mem⟩ = some ⟨c', mem'⟩ ∧ RepDone false (k + 1) c c' :=
  Silmaril.Proofs.Machine.X86.Str9.rep_stosq_fill k hf hro hk hc hfill

/-! ## Decoder regressions -/

theorem decodeL_movsb : decodeL [0xA4] = some (.movsb, 1) := by decide
theorem decodeL_repMovsq : decodeL [0xF3, 0x48, 0xA5] = some (.repMovsq, 3) := by decide
theorem decodeL_repStosq : decodeL [0xF3, 0x48, 0xAB] = some (.repStosq, 3) := by decide
theorem decode_repMovsq : decode [0xF3, 0x48, 0xA5] = some (.str .repMovsq, 3) := by decide

/-- `rep movsb` (`F3 A4`), `rep stosb` (`F3 AA`), `movsq` without `rep` (`48 A5`) and a
truncated `F3 48` are not in the subset. -/
theorem decodeL_others_none :
    decodeL [0xF3, 0xA4] = none ∧ decodeL [0xF3, 0xAA] = none ∧ decodeL [0x48, 0xA5] = none ∧
      decodeL [0xF3, 0x48] = none := by decide

/-- Other prefixes and REX bytes are not in the subset: `F3 49 A5`, `F2 48 A5`, `66 A4`, and
a REX before `F3` (`48 F3 A5`). -/
theorem decodeL_prefixes_none :
    decodeL [0xF3, 0x49, 0xA5] = none ∧ decodeL [0xF2, 0x48, 0xA5] = none ∧
      decodeL [0x66, 0xA4] = none ∧ decodeL [0x48, 0xF3, 0xA5] = none := by decide

/-- On a longer slice `decodeL` returns the form's own length (here `3`, not `4`), so a
listing law asking for `some (i, l)` on a slice of length `l` never applies to it. -/
theorem decodeL_trailing : decodeL [0xF3, 0x48, 0xA5, 0x90] = some (.repMovsq, 3) := by decide

/-- An `Ext9` form is still read by `decode` as `Open9`'s (`mov %rdi, %rax`, `48 89 F8`). -/
theorem decode_open9_first :
    (match decode [0x48, 0x89, 0xF8] with
      | some (.open9 _, 3) => true
      | _ => false) = true := by decide

/-! ## Opcode disjointness (AD-6) -/

/-- **`Str9`'s opcode table is disjoint from `Sse9`'s.** -/
theorem table_disjoint_sse9 : TableDisjoint table sse9Table = true := by decide

/-- **`Str9`'s opcode table is disjoint from the planned `Atomic9` table** (concurrency.md
§2.2). -/
theorem table_disjoint_atomic9 : TableDisjoint table atomic9Table = true := by decide

/-- Every key of `sse9Table`, followed by a register ModRM byte, is decoded by `Sse9`. -/
theorem sse9Table_decodes :
    sse9Table.all (fun k => (Sse9.decodeSse (k ++ [0xC0])).isSome) = true := by decide

/-- `Sse9`'s parser rejects (`.bad`, so whatever bytes follow) each `Str9` encoding. -/
theorem sse_rejects_str :
    table.all (fun e => match Sse9.pSse e with | .bad => true | _ => false) = true := by decide

/-- **Bytes that begin with a key of a table disjoint from `Str9.table` are not a string
form** (instances: `sse9Table`, `atomic9Table`). -/
theorem decodeStr_none_of_key {u : List (List Byte)} (hd : TableDisjoint table u = true)
    {k : List Byte} (hk : k ∈ u) {bytes : List Byte} (hp : k <+: bytes) :
    decodeStr bytes = none :=
  Silmaril.Proofs.Machine.X86.Str9.decodeStr_none_of_key hd hk hp

end Silmaril.Machine.X86.Str9

namespace Silmaril.Machine.X86.Safe

/-- `Str9` extends the `Ext8` open machine. -/
instance instExtendsOpenStr9 : ExtendsOpen Silmaril.Machine.X86.Str9.step :=
  ⟨fun h => Silmaril.Machine.X86.Str9.step_of_open9 (Silmaril.Machine.X86.Open9.step_of_open h)⟩

end Silmaril.Machine.X86.Safe

namespace Silmaril.Machine.X86.FnContract

open Silmaril.X86 (MState)

/-- A total spec on `Open9` is total on `Str9`. -/
theorem Spec.Total.toStr9 {S : Spec MState} (h : S.Total Open9.isa) : S.Total Str9.isa :=
  fun s hl ha he => by
    obtain ⟨t, hr, res⟩ := h s hl ha he
    exact ⟨t, Str9.reaches_of_open9 hr, res.silent, res.abi, res.frame, res.post⟩

/-- **Every `Open9` contract is a `Str9` contract.** -/
def toStr9 (C : FnContract Open9.isa) : FnContract Str9.isa :=
  ⟨C.toSpec, C.total.toStr9⟩

@[simp] theorem toStr9_toSpec (C : FnContract Open9.isa) : C.toStr9.toSpec = C.toSpec := rfl

end Silmaril.Machine.X86.FnContract
