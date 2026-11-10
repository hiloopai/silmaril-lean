module

public import Silmaril.X86.Str9.Defs
public import Silmaril.X86.Open9.Thms
import Silmaril.Proofs.X86.Str9.Decode
import Silmaril.Proofs.X86.Str9.Step

/-!
# `Str9`: the machine, its extension of `Open9`, and the string laws

**Conservative extension.**
* `extendsOpen9 : Open9.isa.Extends isa`: every `Open9` step is a `Str9` step
  (`step_of_open9`), hence `run_of_open9`, `reaches_of_open9`; `extendsOpen` composes it
  with `Open9.extendsOpen`.
* `step_eq_open9`: **where `Ext8` or `Ext9` fetches a form, `Str9.step` is `Open9.step`**;
  `step_cases`: every step is an `Open9` step or, where `Open9` has none, a string form
  fetched at the program counter.
* `FnContract.Spec.Total.toStr9`, `FnContract.toStr9` (an instance of `FnContract.lift`):
  **every contract on `Open9.isa` is a contract on `Str9.isa`** with the same spec.

**The string laws.**
* `isa`: the machine as a `SegVC.Isa MState` over `Str9.Instr` (law: `step_of_listed`);
  `step_of_listed_str`, `step_of_fetch_str`: a listed string form at the program counter
  that executes is one step.
* `step_movsb`, `step_movsq_elem`, `step_stosq_elem`: single elements;
  `rep_movsq_zero`, `rep_stosq_zero`: `rcx = 0` is one step that only advances RIP.
* `rep_movsq_copy`, `rep_stosq_fill`: **`k + 1` elements are `k + 1` steps**, ending past
  the instruction with `RepDone` (`rcx = 0`, pointers advanced by `8 (k + 1)`, the rest of the
  core unchanged), the memory being `copyQ`/`fillQ`. Hypotheses: the instruction bytes are
  fetched at RIP and none of them is writable (so a store cannot change the code), and
  `k + 1 < 2^64`.

The decoding and semantic vectors at the end are kernel-checked (`decide`). The semantics
is a handwritten model of the SDM (DF clear, one element per step), not proved to match
hardware.
-/

@[expose] public section

namespace Silmaril.X86.Str9

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-! ## The machine -/

/-- **The listing law of the machine** (`Ext9` instructions and string forms). -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Str9.step_of_listed hl hrip hfit hdec hx

/-- **The string machine as a segment-VC instance.** -/
@[reducible] def isa : SegVC.Isa MState where
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

/-! ## Conservative extension -/

/-- **Every `Open9` step is a step.** -/
theorem step_of_open9 {m m' : MState} (h : Open9.step m = some m') : step m = some m' :=
  Silmaril.Proofs.X86.Str9.step_of_open9 h

/-- **Where `Ext8` or `Ext9` fetches a form, `Str9` is `Open9`.** -/
theorem step_eq_open9 {m : MState}
    (h : Ext8.fetch m.memory m.core.rip.toNat ≠ .inl .undecodable ∨
      Ext9.fetchNew m.memory m.core.rip.toNat ≠ none) :
    step m = Open9.step m :=
  Silmaril.Proofs.X86.Str9.step_eq_open9 h

/-- **Every step is an `Open9` step, or a string step.** -/
theorem step_cases {m m' : MState} (h : step m = some m') :
    Open9.step m = some m' ∨
      (Open9.step m = none ∧ ∃ i n, fetchStr m.memory m.core.rip.toNat = some (some (i, n)) ∧
        Open.ofResult (execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 n)) = some m') :=
  Silmaril.Proofs.X86.Str9.step_cases h

/-- **`Str9` extends the open machine over `Ext9`** on the same states (identity lens). -/
@[reducible] def extendsOpen9 : Open9.isa.Extends isa :=
  .ofStep (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ h => h) step_of_open9

/-- `Str9` extends the open machine over `Ext8`. -/
@[reducible] def extendsOpen : Open.isa.Extends isa := Open9.extendsOpen.trans extendsOpen9

/-- Every `Open9` run is a `Str9` run of the same length. -/
theorem run_of_open9 (k : Nat) {a b : MState} (h : run Open9.step k a = some b) :
    run step k a = some b :=
  extendsOpen9.run k h

/-- Every `Open9` run is a `Str9` run. -/
theorem reaches_of_open9 {a b : MState} (h : Reaches Open9.step a b) : Reaches step a b :=
  extendsOpen9.reaches h

/-! ## The string laws -/

/-- **The fetch form of the string law.** -/
theorem step_of_fetch_str {m : MState} {l : Nat} {w : List Byte} {i : Str} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Str9.step_of_fetch_str fetched hdec hx

/-- **The string listing law.** -/
theorem step_of_listed_str {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Str}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Str9.step_of_listed_str hl hrip hfit hdec hx

/-- The encoding of a form decodes to it, whatever bytes follow. -/
theorem decodeStr_bytes_append (i : Str) (more : List Byte) :
    decodeStr (i.bytes ++ more) = some (i, i.bytes.length) :=
  Silmaril.Proofs.X86.Str9.decodeStr_bytes_append i more

/-- A decoded form is its own encoding, at the front of the bytes. -/
theorem decodeStr_some {bytes : List Byte} {i : Str} {n : Nat}
    (h : decodeStr bytes = some (i, n)) : i.bytes <+: bytes ∧ n = i.bytes.length :=
  Silmaril.Proofs.X86.Str9.decodeStr_some h

/-- A store keeps the bytes fetched from a range with no writable byte, and the
non-writability of that range. -/
theorem fetch_keep {mem mem' : Memory} {a : Word} {k : Nat} {v : Word}
    (h : storeN mem a k v = some mem') {p l : Nat}
    (hro : ∀ o < l, mem.permits .write (p + o) = false) :
    mem'.fetchBytes p l = mem.fetchBytes p l ∧ ∀ o < l, mem'.permits .write (p + o) = false :=
  Silmaril.Proofs.X86.Str9.fetch_keep h hro

/-- `movsb`: one byte from `[rsi]` to `[rdi]`, both pointers advanced by one. -/
theorem step_movsb {c : State} {mem mem1 : Memory} {v : Word}
    (hf : mem.fetchBytes c.rip.toNat 1 = some Str.movsb.bytes)
    (hl : loadN mem (c.read .rsi) 1 = some v) (hs : storeN mem (c.read .rdi) 1 v = some mem1) :
    step ⟨c, mem⟩ = some ⟨movsbCore c (c.rip + BitVec.ofNat 64 1), mem1⟩ :=
  Silmaril.Proofs.X86.Str9.step_movsb hf hl hs

/-- One element of `rep movsq` (`rcx ≠ 0`). -/
theorem step_movsq_elem {c : State} {mem mem1 : Memory} {v : Word}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes) (hc : c.read .rcx ≠ 0)
    (hl : loadN mem (c.read .rsi) 8 = some v) (hs : storeN mem (c.read .rdi) 8 v = some mem1) :
    step ⟨c, mem⟩ = some ⟨elemCore true c (c.rip + BitVec.ofNat 64 3), mem1⟩ :=
  Silmaril.Proofs.X86.Str9.step_movsq_elem hf hc hl hs

/-- One element of `rep stosq` (`rcx ≠ 0`). -/
theorem step_stosq_elem {c : State} {mem mem1 : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes) (hc : c.read .rcx ≠ 0)
    (hs : storeN mem (c.read .rdi) 8 (c.read .rax) = some mem1) :
    step ⟨c, mem⟩ = some ⟨elemCore false c (c.rip + BitVec.ofNat 64 3), mem1⟩ :=
  Silmaril.Proofs.X86.Str9.step_stosq_elem hf hc hs

/-- `rep movsq` with `rcx = 0` only advances RIP. -/
theorem rep_movsq_zero {c : State} {mem : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes) (hc : c.read .rcx = 0) :
    step ⟨c, mem⟩ = some ⟨{ c with rip := c.rip + BitVec.ofNat 64 3 }, mem⟩ :=
  Silmaril.Proofs.X86.Str9.rep_movsq_zero hf hc

/-- `rep stosq` with `rcx = 0` only advances RIP. -/
theorem rep_stosq_zero {c : State} {mem : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes) (hc : c.read .rcx = 0) :
    step ⟨c, mem⟩ = some ⟨{ c with rip := c.rip + BitVec.ofNat 64 3 }, mem⟩ :=
  Silmaril.Proofs.X86.Str9.rep_stosq_zero hf hc

/-- **`rep movsq` of `k + 1` quadwords is exactly `k + 1` steps**, computing `copyQ`. -/
theorem rep_movsq_copy (k : Nat) {c : State} {mem mem' : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes)
    (hro : ∀ o < 3, mem.permits .write (c.rip.toNat + o) = false)
    (hk : k + 1 < 2 ^ 64) (hc : c.read .rcx = BitVec.ofNat 64 (k + 1))
    (hcopy : copyQ (k + 1) (c.read .rsi) (c.read .rdi) mem = some mem') :
    ∃ c', run step (k + 1) ⟨c, mem⟩ = some ⟨c', mem'⟩ ∧ RepDone true (k + 1) c c' :=
  Silmaril.Proofs.X86.Str9.rep_movsq_copy k hf hro hk hc hcopy

/-- **`rep stosq` of `k + 1` quadwords is exactly `k + 1` steps**, computing `fillQ`. -/
theorem rep_stosq_fill (k : Nat) {c : State} {mem mem' : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes)
    (hro : ∀ o < 3, mem.permits .write (c.rip.toNat + o) = false)
    (hk : k + 1 < 2 ^ 64) (hc : c.read .rcx = BitVec.ofNat 64 (k + 1))
    (hfill : fillQ (k + 1) (c.read .rax) (c.read .rdi) mem = some mem') :
    ∃ c', run step (k + 1) ⟨c, mem⟩ = some ⟨c', mem'⟩ ∧ RepDone false (k + 1) c c' :=
  Silmaril.Proofs.X86.Str9.rep_stosq_fill k hf hro hk hc hfill

/-! ## Decoding vectors -/

/-- Each key of `table` is a listed string form of its own length. -/
example : table.all (fun e => match decode e with
    | some (.str _, n) => n == e.length
    | _ => false) = true := by decide

example : decode [0xA4] = some (.str .movsb, 1) := by decide
example : decode [0xF3, 0x48, 0xA5] = some (.str .repMovsq, 3) := by decide
example : decode [0xF3, 0x48, 0xAB] = some (.str .repStosq, 3) := by decide

/-- `rep movsb` (`F3 A4`), `rep stosb` (`F3 AA`), `movsq` without `rep` (`48 A5`), `stosq`
without `rep` (`48 AB`) and a truncated `F3 48` are not in the subset. -/
example : decode [0xF3, 0xA4] = none ∧ decode [0xF3, 0xAA] = none ∧ decode [0x48, 0xA5] = none ∧
    decode [0x48, 0xAB] = none ∧ decode [0xF3, 0x48] = none := by decide

/-- Other prefixes and REX bytes are not in the subset: `F3 49 A5`, `F2 48 A5`, `66 A4`,
`67 A4`, `2E A4`, and a REX before `F3` (`48 F3 A5`). -/
example : decode [0xF3, 0x49, 0xA5] = none ∧ decode [0xF2, 0x48, 0xA5] = none ∧
    decode [0x66, 0xA4] = none ∧ decode [0x67, 0xA4] = none ∧ decode [0x2E, 0xA4] = none ∧
    decode [0x48, 0xF3, 0xA5] = none := by decide

/-- `cmpsb` (`A6`), `repe cmpsq` (`F3 48 A7`), `scasb` (`AE`), `repne scasb` (`F2 AE`),
`lodsb` (`AC`) and `std` (`FD`) are not modelled. -/
example : decode [0xA6] = none ∧ decode [0xF3, 0x48, 0xA7] = none ∧ decode [0xAE] = none ∧
    decode [0xF2, 0xAE] = none ∧ decode [0xAC] = none ∧ decode [0xFD] = none := by decide

/-- On a longer slice `decodeL` returns the form's own length (here `3`, not `4`), so a
listing law asking for `some (i, l)` on a slice of length `l` never applies to it. -/
example : decodeL [0xF3, 0x48, 0xA5, 0x90] = some (.repMovsq, 3) ∧
    decode [0xF3, 0x48, 0xA5, 0x90] = some (.str .repMovsq, 3) := by decide

/-- `Ext9` forms are still read as `Ext9`'s: `mov %rdi, %rax` (`48 89 F8`) and `rep ret`
(`F3 C3`). -/
example : (match decode [0x48, 0x89, 0xF8] with
      | some (.ext9 _, 3) => true
      | _ => false) = true ∧
    decode [0xF3, 0xC3] = some (.ext9 (.new .repRet), 2) := by decide

/-! ## Semantic vectors -/

/-- A core with `rsi = 0x1000`, `rdi = 0x2000`, `rcx = n`, `rax = 0xab`, RIP `0x401000`. -/
private def vcore (n : Word) : State :=
  (((({ regs := fun _ => 0, rip := 0x401000, flags := ⟨none, none, none, none, none, none⟩ } :
    State).write .rsi 0x1000).write .rdi 0x2000).write .rcx n).write .rax 0xab

/-- The last element of `rep movsq` (`rcx = 1`): both pointers advance by 8, `rcx` becomes
`0` and RIP moves past the instruction. -/
example : let c := elemCore true (vcore 1) 0x401003
    c.read .rsi = 0x1008 ∧ c.read .rdi = 0x2008 ∧ c.read .rcx = 0 ∧ c.rip = 0x401003 ∧
      c.read .rax = 0xab := by decide

/-- A middle element (`rcx = 5`): RIP stays on the instruction. -/
example : let c := elemCore true (vcore 5) 0x401003
    c.read .rcx = 4 ∧ c.rip = 0x401000 := by decide

/-- `rep stosq` does not move `rsi`. -/
example : let c := elemCore false (vcore 2) 0x401003
    c.read .rsi = 0x1000 ∧ c.read .rdi = 0x2008 ∧ c.read .rcx = 1 ∧ c.rip = 0x401000 := by decide

/-- `movsb` advances both pointers by one. -/
example : let c := movsbCore (vcore 7) 0x401001
    c.read .rsi = 0x1001 ∧ c.read .rdi = 0x2001 ∧ c.read .rcx = 7 ∧ c.rip = 0x401001 := by decide

/-- The pointers wrap at `2^64`. -/
example : (elemCore true ((vcore 1).write .rdi 0xfffffffffffffffc) 0).read .rdi = 4 := by decide

/-- No mapped memory. -/
private def noMem : Memory := ⟨[], ∅⟩

/-- With no memory mapped, every element faults (no step), and `rcx = 0` only moves RIP. -/
example : ((match execStr .repMovsq (vcore 1) noMem 0x401003 with
      | .dataFault => true | _ => false) &&
    (match execStr .repStosq (vcore 1) noMem 0x401003 with | .dataFault => true | _ => false) &&
    (match execStr .movsb (vcore 1) noMem 0x401001 with | .dataFault => true | _ => false) &&
    (match execStr .repMovsq (vcore 0) noMem 0x401003 with
      | .ok c _ => c.rip == 0x401003 && c.read .rsi == 0x1000 && c.read .rcx == 0
      | _ => false)) = true := by decide

end Silmaril.X86.Str9

namespace Silmaril.X86.FnContract

open Silmaril.X86 (MState)

/-- **A total spec on `Open9` is total on `Str9`.** -/
theorem Spec.Total.toStr9 {S : Spec MState} (h : S.Total Open9.isa) : S.Total Str9.isa :=
  h.lift Str9.extendsOpen9

/-- **Every `Open9` contract is a `Str9` contract** (`FnContract.lift` along
`Str9.extendsOpen9`). -/
def toStr9 (C : FnContract Open9.isa) : FnContract Str9.isa :=
  C.lift Str9.extendsOpen9

@[simp] theorem toStr9_toSpec (C : FnContract Open9.isa) : C.toStr9.toSpec = C.toSpec := rfl

end Silmaril.X86.FnContract
