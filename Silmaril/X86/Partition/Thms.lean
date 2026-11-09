module

public import Silmaril.X86.Partition.Defs
public import Silmaril.X86.Open9.Defs
import Silmaril.Proofs.X86.Partition.Sound

/-!
# What an accepted partition means

The soundness theorems of `check2` are stated for any machine `step` that executes the
listing (`Executes`: from a listed, modelled instruction, in a memory that holds the region,
a step is that instruction's `X86.Ext` or `X86.Ext8` execution). Three machines do:

* `executes_ext8`: the sentinel machine `Ext8.stepOpt exit`, for every exit;
* `executes_open`: the open machine `Open.step`;
* `executes_open9`: the default open machine `Open9.step`. At a listed, modelled instruction
  the `Ext8` fetch succeeds, so `Open9.step` is `Open.step` there (`Open9.step_eq_open`).

`Region.LoadedIn` is inhabited by `Region.load` (`Silmaril.X86.Decompile.Region.loadedIn_load`).
Proofs are in `Silmaril/Proofs/X86/Partition/Sound.lean`.

* `sound_exec`, `sound_step`, `sound_step_open9`: one step from a listed, modelled
  instruction of function `i` lands on an instruction of `i` (any of its ranges), or was a
  call and enters a function, or was a declared tail call and enters a function, or was a
  `ret`.
* `sound_run`: a run of internal steps (no call, `ret`, tail call or unmodelled instruction)
  of an executing machine never leaves the function. This is `Decompile.check_sound_run`
  generalised to range sets, `X86.Ext8` forms and unmodelled instructions.
* `return_site`: after a call to a function not declared `noreturn`, the next instruction
  belongs to the caller.
* `noreturn_no_ret`, `noreturn_modelled`, `noreturn_tailcall`: a `noreturn` function has no
  `ret`, no unmodelled instruction (whose successor nothing constrains), and tail-calls only
  `noreturn` functions. With `sound_exec`, a step from a `noreturn` function stays in it, or
  enters a function by a call, or enters a `noreturn` function by a tail call.
* `entry`, `exported_abi`, `listed`, `slot`, `layout`: entries are owned instructions,
  exported functions carry a platform ABI, the listing is the model's decoding (and the
  unmodelled instructions are exactly where the model's listing decoder fails), padding is
  NOPs, and the layout tiles the region, so range sets of distinct functions are disjoint.

What is **not** claimed: nothing about the successor of an unmodelled instruction (an
indirect `jmp` through a jump table, `syscall`; `Open9` may decode some of these, but the
partition does not look at them); nothing about where a `ret` goes (that is a function
contract, `Silmaril.X86.FnContract`); and an `inferred` convention is recorded data, not
checked. Nor are the `exported` flags or the `abi` tags checked: `check2` sees only the
region's bytes, not the symbol table, so `exported_abi` says that the functions the proposal
*marks* exported carry an ABI tag, and the tag itself constrains nothing until a function
contract uses it.

Every `Abi` is a well-formed `Silmaril.Machine.CallingConvention` (`Abi.wellFormed`), and
`Convention.sysv64` preserves `Silmaril.X86.sysv64.calleeSaved` (`sysv64_preserved`).

A sharded form of `check2` (one kernel `decide` per piece of the region, joined by a
composition lemma) is in `Partition/Shard/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Partition

open Silmaril.X86 (Word MState)
open Silmaril.X86.Decompile (Region Edge)

/-! ## Conventions -/

theorem sysv64_preserved : Convention.sysv64.preserved = Silmaril.X86.sysv64.calleeSaved := rfl

theorem win64_wellFormed : win64Convention.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Every platform ABI is a well-formed calling-convention record. -/
theorem Abi.wellFormed : ∀ a : Abi, a.cc.WellFormed
  | .sysv64 => Silmaril.X86.sysv64_wellFormed
  | .win64 => win64_wellFormed

/-! ## Machines that execute the listing -/

section

variable {r : Region} {p : Proposal} {fuel : Nat}

theorem executes_ext8 (exit : Word) : Executes r p fuel (Silmaril.X86.Ext8.stepOpt exit) :=
  Proofs.X86.Partition.executes_ext8 exit

theorem executes_open : Executes r p fuel Silmaril.X86.Open.step :=
  Proofs.X86.Partition.executes_open

theorem executes_open9 : Executes r p fuel Silmaril.X86.Open9.step :=
  Proofs.X86.Partition.executes_open9

/-! ## Soundness of `check2` -/

/-- **One step**, for an execution of the listed instruction `d` of function `i`. -/
theorem sound_exec (h : check2 r p fuel = none) {m next : MState} {d : D8} {i : Nat}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i) (hrip : m.core.rip.toNat = d.addr)
    (hexec : d.ExecAt m next) :
    InFn r p fuel i next.core.rip.toNat ∨
      (d.item.isCall = true ∧ IsEntry p next.core.rip.toNat) ∨
      (d.addr ∈ p.tailCalls ∧ IsEntry p next.core.rip.toNat) ∨
      d.item = .base .ret :=
  Proofs.X86.Partition.check2_sound_exec h hd hown hrip hexec

/-- **One step** of an executing machine from a listed, modelled instruction. -/
theorem sound_step_of {step : MState → Option MState} (hx : Executes r p fuel step)
    (h : check2 r p fuel = none) {m next : MState} {d : D8} {i : Nat}
    (hload : r.LoadedIn m.memory) (hd : d ∈ listing r p fuel) (hown : p.owner d = some i)
    (hrip : m.core.rip.toNat = d.addr) (hmod : d.item ≠ .unmodelled)
    (hstep : step m = some next) :
    InFn r p fuel i next.core.rip.toNat ∨
      (d.item.isCall = true ∧ IsEntry p next.core.rip.toNat) ∨
      (d.addr ∈ p.tailCalls ∧ IsEntry p next.core.rip.toNat) ∨
      d.item = .base .ret :=
  sound_exec h hd hown hrip (hx hload hd hrip hmod hstep)

/-- **One retirement** of the `Ext8` machine. -/
theorem sound_step (h : check2 r p fuel = none) {exit : Word} {m next : MState}
    {d : D8} {i : Nat} (hload : r.LoadedIn m.memory) (hd : d ∈ listing r p fuel)
    (hown : p.owner d = some i) (hrip : m.core.rip.toNat = d.addr)
    (hmod : d.item ≠ .unmodelled)
    (hstep : Silmaril.X86.Ext8.stepOpt exit m = some next) :
    InFn r p fuel i next.core.rip.toNat ∨
      (d.item.isCall = true ∧ IsEntry p next.core.rip.toNat) ∨
      (d.addr ∈ p.tailCalls ∧ IsEntry p next.core.rip.toNat) ∨
      d.item = .base .ret :=
  sound_step_of (executes_ext8 exit) h hload hd hown hrip hmod hstep

/-- **One step** of the default open machine `Open9`. -/
theorem sound_step_open9 (h : check2 r p fuel = none) {m next : MState}
    {d : D8} {i : Nat} (hload : r.LoadedIn m.memory) (hd : d ∈ listing r p fuel)
    (hown : p.owner d = some i) (hrip : m.core.rip.toNat = d.addr)
    (hmod : d.item ≠ .unmodelled)
    (hstep : Silmaril.X86.Open9.step m = some next) :
    InFn r p fuel i next.core.rip.toNat ∨
      (d.item.isCall = true ∧ IsEntry p next.core.rip.toNat) ∨
      (d.addr ∈ p.tailCalls ∧ IsEntry p next.core.rip.toNat) ∨
      d.item = .base .ret :=
  sound_step_of executes_open9 h hload hd hown hrip hmod hstep

/-- **A run of internal steps never leaves the function**, on any executing machine. -/
theorem sound_run (h : check2 r p fuel = none) {step : MState → Option MState}
    (hx : Executes r p fuel step) {m final : MState} {i : Nat}
    (hat : InFn r p fuel i m.core.rip.toNat)
    (hrun : InternalRun r p fuel i step m final) : InFn r p fuel i final.core.rip.toNat :=
  Proofs.X86.Partition.check2_sound_run h hx hat hrun

theorem return_site (h : check2 r p fuel = none) {d : D8} {i : Nat} {rel : BitVec 32}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i)
    (hi : d.item = .base (.call rel))
    (hnr : ∀ j, p.entryOf ((d.toDecoded (.call rel)).relTarget (rel.signExtend 64)) = some j →
      p.noret j = false) :
    InFn r p fuel i d.next :=
  Proofs.X86.Partition.check2_return_site h hd hown hi hnr

theorem noreturn_no_ret (h : check2 r p fuel = none) {d : D8} {i : Nat}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i) (hnr : p.noret i = true) :
    d.item ≠ .base .ret :=
  Proofs.X86.Partition.check2_noreturn_no_ret h hd hown hnr

theorem noreturn_modelled (h : check2 r p fuel = none) {d : D8} {i : Nat}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i) (hnr : p.noret i = true) :
    d.item ≠ .unmodelled :=
  Proofs.X86.Partition.check2_noreturn_modelled h hd hown hnr

theorem noreturn_tailcall (h : check2 r p fuel = none) {d : D8} {i t : Nat}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i) (hnr : p.noret i = true)
    (he : Edge.jump t ∈ d.edges ∨ Edge.branch t ∈ d.edges) (hout : ¬ InFn r p fuel i t) :
    ∃ j, p.entryOf t = some j ∧ p.noret j = true :=
  Proofs.X86.Partition.check2_noreturn_tailcall h hd hown hnr he hout

theorem entry (h : check2 r p fuel = none) {i : Nat} {f : Fn}
    (hf : p.funcs[i]? = some f) : InFn r p fuel i f.entry :=
  Proofs.X86.Partition.check2_entry h hf

theorem exported_abi (h : check2 r p fuel = none) {f : Fn} (hf : f ∈ p.funcs)
    (hx : f.exported = true) : ∃ a, f.conv = .abi a :=
  Proofs.X86.Partition.check2_exported_abi h hf hx

theorem listed (h : check2 r p fuel = none) {d : D8} (hd : d ∈ listing r p fuel) :
    ∃ off, d.addr = r.base + off ∧ off + d.size ≤ r.bytes.length ∧ 0 < d.size ∧
      (d.item ≠ .unmodelled → decodeAt (r.bytes.drop off) = some (d.item, d.size)) ∧
      (d.item = .unmodelled → decodeAt (r.bytes.drop off) = none) :=
  Proofs.X86.Partition.check2_listed h hd

theorem slot (h : check2 r p fuel = none) {d : D8} (hd : d ∈ listing r p fuel) :
    ∃ s, p.slotOf d = some s ∧ (∀ a b, s = .padding a b → ∃ n, d.item = .base (.nop n)) :=
  Proofs.X86.Partition.check2_slot h hd

theorem layout (h : check2 r p fuel = none) :
    (∀ s ∈ p.layout, r.base ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ r.base + r.bytes.length) ∧
      p.layout.Pairwise (fun s s' => s.stop ≤ s'.start) ∧
      (∀ a, r.base ≤ a → a < r.base + r.bytes.length → ∃ s ∈ p.layout, s.start ≤ a ∧ a < s.stop) ∧
      (∀ s ∈ p.layout, ∀ o, s.owner = some o → o < p.funcs.length) :=
  Proofs.X86.Partition.check2_layout h

/-- An owned instruction lies whole in one of its function's code slots. -/
theorem owner_in_slot {d : D8} {i : Nat} (hown : p.owner d = some i) :
    ∃ a b, Slot.code i a b ∈ p.layout ∧ a ≤ d.addr ∧ d.addr + d.size ≤ b :=
  Proofs.X86.Partition.owner_slot hown

end

end Silmaril.X86.Partition
