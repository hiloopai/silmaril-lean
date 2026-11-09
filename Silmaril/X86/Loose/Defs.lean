module

public import Silmaril.X86.RelIsa.Defs

/-!
# `X86Loose`: the minimal loose x86 specification

A loose specification says, for the instructions of an image, what a step of each may do,
and nothing else. Over **any** state type `σ` with `Views` (the shared containers `State`
and `Memory`):

**Decode tables.** `DEntry Φ` is an exact byte string and its *form* (an instruction of a
form index `Φ`); `DTable Φ := List (DEntry Φ)`. A table is address-free: it says "these byte
strings are these forms" and nothing about where they sit. `AtEntry e c m`: the bytes of `e`
are fetched (execute permission) at `c.rip`.

**Form specifications.** `FormSpec` is what a form promises, at a core, a memory and an
instruction length:

* `unspecified`: where the specification says nothing (hardware may fault or do anything);
* `allows c m l c' m'`: the successor cores and memories it allows elsewhere;
* `allows_fs`: an allowed successor keeps `fsBase`;
* `nonempty`: where it is specified, some successor is allowed.

`FormSpec.sem` is the set of allowed `Ext.Result`s: every result where the form is
unspecified, else the allowed successes. `FormSpec.Tightens F F'`: `F'` allows fewer results
than `F`. `Sigma Φ := Φ → Option FormSpec` is a table of form specifications; `none` is
unspecified (every outcome). Lean reserves `Σ`, so the name is `Sigma`.

**Effect records.** Most forms are described by one record, `Effect`: the successor `rip`,
the registers written (with their values, in order), the registers written with an
unspecified value (`havocRegs`), the flags (`FlagEff`: kept, set to a value, or `undef`:
any value), and the memory read and written. Nothing else changes. `Effect.Admits` is the
successor relation of an effect and `EffSpec` a form given by an effect (with locality in
the memory it reads); `EffSpec.toFormSpec` is its `FormSpec`.

**The machine.** `X86Loose.rel D S V : RelIsa σ`:

* at a state whose `rip` holds the bytes of a `D` entry whose form is specified, a step is
  allowed by **every** such entry's `FormSpec.sem` (an intersection: hardware does one
  thing), and its successor is the view update `V.upd s c' m'` of an allowed success
  (`MatchRes`), so the extended state is kept;
* everywhere else every outcome is allowed, `stop` included;
* the successor of a step is `live`.

`AtSpecified D S V s`: some entry of `D` is at `rip`, its form is specified and not
`unspecified` there; steps from such states are allowed successes (`Loose/Thms.lean`).
-/

@[expose] public section

namespace Silmaril.X86.Loose

open Silmaril.X86 (State Word Byte Flags Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Views Res)

/-! ## Flag effects -/

/-- One flag's effect: kept, set to a value (`none` is the undefined value of the state), or
undefined (`undef`: any value). -/
inductive FlagP where
  | keep
  | set (v : Option Bool)
  | undef
  deriving DecidableEq, Repr

/-- The values a flag may have afterwards, from its value `x` before. -/
def FlagP.Allows : FlagP → Option Bool → Option Bool → Prop
  | .keep, x, y => y = x
  | .set v, _, y => y = v
  | .undef, _, _ => True

/-- One allowed value (`undef` keeps the old value). -/
def FlagP.pick : FlagP → Option Bool → Option Bool
  | .set v, _ => v
  | _, x => x

/-- An exact flag value: `some b` is set, `none` (undefined in the SDM) is `undef`. -/
def FlagP.ofOpt : Option Bool → FlagP
  | some b => .set (some b)
  | none => .undef

/-- The effect on the six status flags. -/
structure FlagEff where
  carry : FlagP := .keep
  parity : FlagP := .keep
  adjust : FlagP := .keep
  zero : FlagP := .keep
  sign : FlagP := .keep
  overflow : FlagP := .keep
  deriving DecidableEq, Repr

/-- Every flag kept. -/
def FlagEff.keepAll : FlagEff := {}

/-- The flags `y` are allowed after the flags `x`. -/
def FlagEff.Allows (f : FlagEff) (x y : Flags) : Prop :=
  f.carry.Allows x.carry y.carry ∧ f.parity.Allows x.parity y.parity ∧
    f.adjust.Allows x.adjust y.adjust ∧ f.zero.Allows x.zero y.zero ∧
    f.sign.Allows x.sign y.sign ∧ f.overflow.Allows x.overflow y.overflow

/-- One allowed value of the flags. -/
def FlagEff.pick (f : FlagEff) (x : Flags) : Flags :=
  ⟨f.carry.pick x.carry, f.parity.pick x.parity, f.adjust.pick x.adjust,
    f.zero.pick x.zero, f.sign.pick x.sign, f.overflow.pick x.overflow⟩

/-- Every flag as in `f`, an undefined (`none`) one any value. -/
def FlagEff.ofFlags (f : Flags) : FlagEff :=
  ⟨.ofOpt f.carry, .ofOpt f.parity, .ofOpt f.adjust, .ofOpt f.zero, .ofOpt f.sign,
    .ofOpt f.overflow⟩

/-! ## Effects -/

/-- **The effect of one instruction** on a given core and memory. -/
structure Effect where
  /-- The successor `rip`. -/
  rip : Word
  /-- Registers written, with their 64-bit values (after any size extension), in order. -/
  regs : List (Reg × Word) := []
  /-- Registers written with an unspecified value. -/
  havocRegs : List Reg := []
  /-- The status flags. -/
  flags : FlagEff := FlagEff.keepAll
  /-- Memory read: `(address, length)` (locality). -/
  reads : List (Nat × Nat) := []
  /-- Memory written, in order: `(address, bytes)`. -/
  writes : List (Nat × List Byte) := []

/-- Apply writes in order; `none` if one of them is not permitted. -/
def writeAll (m : Memory) : List (Nat × List Byte) → Option Memory
  | [] => some m
  | (a, bs) :: ws => (m.writeBytes a bs).bind fun m' => writeAll m' ws

/-- The value of register `r` after the listed writes of `e` (the last write wins). -/
def Effect.regAfter (e : Effect) (c : State) (r : Reg) : Word :=
  match e.regs.reverse.find? (fun p => decide (p.1 = r)) with
  | some p => p.2
  | none => c.read r

/-- **`(c', m')` is a successor of `(c, m)` that `e` allows.** -/
structure Effect.Admits (e : Effect) (c : State) (m : Memory) (c' : State) (m' : Memory) :
    Prop where
  rip : c'.rip = e.rip
  regs : ∀ r, r ∉ e.havocRegs → c'.read r = e.regAfter c r
  flags : e.flags.Allows c.flags c'.flags
  fsBase : c'.fsBase = c.fsBase
  mem : writeAll m e.writes = some m'

/-- One admitted successor core: havoc'd registers `0`, undefined flags kept. -/
def Effect.pickCore (e : Effect) (c : State) : State where
  regs r := if r ∈ e.havocRegs then 0 else e.regAfter c r
  rip := e.rip
  flags := e.flags.pick c.flags
  fsBase := c.fsBase

/-! ## Form specifications -/

/-- **A form's loose semantics.** -/
structure FormSpec where
  /-- Where the spec says nothing: hardware may fault or do anything. -/
  unspecified : State → Memory → Nat → Prop
  /-- The successors allowed where the form is specified. -/
  allows : State → Memory → Nat → State → Memory → Prop
  /-- An allowed successor keeps `fsBase`. -/
  allows_fs : ∀ {c m l c' m'}, allows c m l c' m' → c'.fsBase = c.fsBase
  /-- Where the form is specified, it allows some successor. -/
  nonempty : ∀ {c m l}, ¬ unspecified c m l → ∃ c' m', allows c m l c' m'

/-- The results a form allows on a core and a memory, at instruction length `l`. -/
def FormSpec.sem (F : FormSpec) (c : State) (m : Memory) (l : Nat)
    (res : Silmaril.X86.Ext.Result) : Prop :=
  F.unspecified c m l ∨ ∃ c' m', res = .ok c' m' ∧ F.allows c m l c' m'

/-- `F'` tightens `F`: every result `F'` allows, `F` allows. -/
def FormSpec.Tightens (F F' : FormSpec) : Prop :=
  ∀ c m l res, F'.sem c m l res → F.sem c m l res

/-- Form specifications over a form index `Φ`; `none` is unspecified. -/
abbrev Sigma (Φ : Type) := Φ → Option FormSpec

/-- **A form given by an effect.** -/
structure EffSpec where
  /-- Where the spec says nothing. -/
  unspecified : State → Memory → Nat → Prop
  /-- The effect where the form is specified. -/
  eff : State → Memory → Nat → Effect
  /-- The effect depends on memory only through the bytes it lists as read. -/
  local_reads : ∀ c m m' l,
    (∀ p ∈ (eff c m l).reads, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2) →
      eff c m' l = eff c m l
  /-- Where the form is specified, its writes are permitted. -/
  writes_ok : ∀ c m l, ¬ unspecified c m l → (writeAll m (eff c m l).writes).isSome

/-- A form whose effect is a pure function of the core and the length, writes nothing and is
never unspecified. -/
def EffSpec.ofCore (f : State → Nat → Effect) (hw : ∀ c l, (f c l).writes = []) : EffSpec where
  unspecified _ _ _ := False
  eff c _ l := f c l
  local_reads _ _ _ _ _ := rfl
  writes_ok c m l _ := by simp [hw c l, writeAll]

/-- The value `pick` chooses is allowed. -/
theorem FlagP.allows_pick (p : FlagP) (x : Option Bool) : p.Allows x (p.pick x) := by
  cases p <;> trivial

/-- The flags `pick` chooses are allowed. -/
theorem FlagEff.allows_pick (f : FlagEff) (x : Flags) : f.Allows x (f.pick x) :=
  ⟨FlagP.allows_pick .., FlagP.allows_pick .., FlagP.allows_pick .., FlagP.allows_pick ..,
    FlagP.allows_pick .., FlagP.allows_pick ..⟩

/-- `pickCore` is admitted, with the written memory. -/
theorem Effect.admits_pickCore (e : Effect) (c : State) {m m' : Memory}
    (hm : writeAll m e.writes = some m') : e.Admits c m (e.pickCore c) m' where
  rip := rfl
  regs r hr := by simp [Effect.pickCore, State.read, hr]
  flags := e.flags.allows_pick c.flags
  fsBase := rfl
  mem := hm

/-- **The `FormSpec` of an effect form.** -/
def EffSpec.toFormSpec (F : EffSpec) : FormSpec where
  unspecified := F.unspecified
  allows c m l c' m' := (F.eff c m l).Admits c m c' m'
  allows_fs h := h.fsBase
  nonempty {c m l} hu := by
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 (F.writes_ok c m l hu)
    exact ⟨_, m', Effect.admits_pickCore _ c hm'⟩

/-! ## Decode tables -/

/-- One decode-table entry: the exact instruction bytes and their form. -/
structure DEntry (Φ : Type) where
  bytes : List Byte
  form : Φ
  deriving DecidableEq

/-- A decode table. -/
abbrev DTable (Φ : Type) := List (DEntry Φ)

variable {Φ σ : Type}

/-- The bytes of `e` are fetched (execute permission) at `rip`. -/
def AtEntry (e : DEntry Φ) (c : State) (m : Memory) : Prop :=
  m.fetchBytes c.rip.toNat e.bytes.length = some e.bytes

/-! ## The machine -/

/-- The machine outcome `r` from `s` agrees with the instruction result `res`: a success of
`res` is the outcome, as a view update. -/
def MatchRes (V : Views σ) (s : σ) (r : Res σ) (res : Silmaril.X86.Ext.Result) : Prop :=
  ∀ c m, res = .ok c m → r = .ok (V.upd s c m)

/-- The loose step relation. -/
def X86Loose.step (D : DTable Φ) (S : Sigma Φ) (V : Views σ) (s : σ) (r : Res σ) : Prop :=
  (∀ e ∈ D, AtEntry e (V.core s) (V.mem s) → ∀ F, S e.form = some F →
    ∃ res, F.sem (V.core s) (V.mem s) e.bytes.length res ∧ MatchRes V s r res) ∧
  ∀ t, r = .ok t → V.live t

/-- **The loose machine** of a table and form specifications. -/
def X86Loose.rel (D : DTable Φ) (S : Sigma Φ) (V : Views σ) : RelIsa σ where
  toViews := V
  step := X86Loose.step D S V
  live_step {_ t} _ h := h.2 t rfl

/-- Some entry is at `rip`, its form is specified and not `unspecified` there. -/
def AtSpecified (D : DTable Φ) (S : Sigma Φ) (V : Views σ) (s : σ) : Prop :=
  ∃ e ∈ D, AtEntry e (V.core s) (V.mem s) ∧
    ∃ F, S e.form = some F ∧ ¬ F.unspecified (V.core s) (V.mem s) e.bytes.length

end Silmaril.X86.Loose
