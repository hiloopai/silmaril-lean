module

public import Silmaril.X86.Loose.Defs
public import Silmaril.X86.Ext.Machine

/-!
# Single-span forms of the loose x86 specification

The string forms (`Str9`) have one shape: read at most one memory span, write at most one
memory span, then set some registers, the flags and `rip`. `Span` describes such a form,
and `Span.toEffSpec` is its loose `EffSpec`:

* `rd c l`: the span read (`(address, width)`), if any; its little-endian value `x`
  (`Span.val`, `loadN`) feeds the rest;
* `wr c l x`: the span written (`(address, width, value)`, the low `width` bytes of `value`,
  `storeN`), if any;
* `post c l x`: the successor core (its `rip`, the registers `ws` and, when `setsFlags`, the
  six status flags are read from it; every other register and `fsBase` are kept);
* `extra c l`: a condition, on the core only, under which the form is **unspecified** (for
  example overlapping `rep movsq` ranges).

The form is also unspecified where its read or its write is not permitted (the machine may
fault). Everywhere else exactly one result is allowed: the listed effect.

`Span.run` is the reference executor of a span (`dataFault` where an access is not
permitted). A concrete executor tightens the spec once it is shown equal to `Span.run` and
`Span.Frame` holds.
-/

@[expose] public section

namespace Silmaril.X86.Loose

open Silmaril.X86 (State Word Byte Flags Reg)
open Silmaril.X86.Ext (loadN storeN leBytes)
open Silmaril.Process (Memory)

/-- **A single-span form.** -/
structure Span where
  /-- Unspecified, whatever the memory. -/
  extra : State → Nat → Bool := fun _ _ => false
  /-- The span read: address and width. -/
  rd : State → Nat → Option (Word × Nat)
  /-- The span written, given the value read: address, width and value. -/
  wr : State → Nat → Word → Option (Word × Nat × Word)
  /-- The successor core, given the value read. -/
  post : State → Nat → Word → State
  /-- The registers written (read from `post`). -/
  ws : List Reg
  /-- The status flags are set (read from `post`); otherwise kept. -/
  setsFlags : Bool

namespace Span

/-- The value read (`0` if nothing is read or the read is not permitted). -/
def val (S : Span) (c : State) (m : Memory) (l : Nat) : Word :=
  match S.rd c l with
  | some (a, k) => (loadN m a k).getD 0
  | none => 0

/-- The effect of a span on a given value read. -/
def effOf (S : Span) (c : State) (l : Nat) (x : Word) : Effect where
  rip := (S.post c l x).rip
  regs := S.ws.map fun r => (r, (S.post c l x).read r)
  flags := if S.setsFlags then FlagEff.ofFlags (S.post c l x).flags else FlagEff.keepAll
  reads := (S.rd c l).toList.map fun p => (p.1.toNat, p.2)
  writes := (S.wr c l x).toList.map fun p => (p.1.toNat, leBytes p.2.2 p.2.1)

/-- The effect of a span. -/
def eff (S : Span) (c : State) (m : Memory) (l : Nat) : Effect :=
  S.effOf c l (S.val c m l)

/-- Where the span is unspecified (as a `Bool`). -/
def unspecB (S : Span) (c : State) (m : Memory) (l : Nat) : Bool :=
  S.extra c l ||
    (match S.rd c l with
      | some (a, k) => (loadN m a k).isNone
      | none => false) ||
    (match S.wr c l (S.val c m l) with
      | some (a, k, v) => (storeN m a k v).isNone
      | none => false)

theorem val_congr (S : Span) {c : State} {m m' : Memory} {l : Nat}
    (h : ∀ p ∈ (S.eff c m l).reads, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2) :
    S.val c m' l = S.val c m l := by
  unfold val
  unfold eff effOf at h
  cases hr : S.rd c l with
  | none => rfl
  | some p =>
    obtain ⟨a, k⟩ := p
    simp only [hr, Option.toList_some, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at h
    simp only [loadN, h]

theorem writes_ok (S : Span) (c : State) (m : Memory) (l : Nat)
    (h : ¬ S.unspecB c m l = true) : (writeAll m (S.eff c m l).writes).isSome := by
  unfold unspecB at h
  unfold eff effOf
  cases hw : S.wr c l (S.val c m l) with
  | none => simp [writeAll]
  | some p =>
    obtain ⟨a, k, v⟩ := p
    rw [hw] at h
    simp only [Bool.or_eq_true, not_or] at h
    obtain ⟨-, h⟩ := h
    simp only [Option.isNone_iff_eq_none] at h
    simp only [Option.toList_some, List.map_cons, List.map_nil, writeAll]
    cases hs : storeN m a k v with
    | none => exact absurd (by simpa [storeN] using hs) h
    | some m' =>
      simp only [storeN] at hs
      simp [hs]

/-- **The loose `EffSpec` of a span.** -/
def toEffSpec (S : Span) : EffSpec where
  unspecified c m l := S.unspecB c m l = true
  eff := S.eff
  local_reads c m m' l h := by
    unfold eff
    rw [S.val_congr h]
  writes_ok := S.writes_ok

/-- **The reference executor of a span**: read, write, then the successor core;
`dataFault` where an access is not permitted. -/
def runOf (S : Span) (c : State) (m : Memory) (l : Nat) (x : Word) :
    Silmaril.X86.Ext.Result :=
  match S.wr c l x with
  | some (a, k, v) =>
    match storeN m a k v with
    | some m' => .ok (S.post c l x) m'
    | none => .dataFault
  | none => .ok (S.post c l x) m

/-- The reference executor of a span. -/
def run (S : Span) (c : State) (m : Memory) (l : Nat) : Silmaril.X86.Ext.Result :=
  match S.rd c l with
  | some (a, k) =>
    match loadN m a k with
    | some x => S.runOf c m l x
    | none => .dataFault
  | none => S.runOf c m l 0

/-- The side conditions under which `Span.run` tightens `Span.toEffSpec`: `post` writes no
register outside `ws`, keeps `fsBase`, and keeps the flags unless `setsFlags`. -/
structure Frame (S : Span) (c : State) (l : Nat) : Prop where
  regs : ∀ x r, r ∉ S.ws → (S.post c l x).read r = c.read r
  fsBase : ∀ x, (S.post c l x).fsBase = c.fsBase
  flags : S.setsFlags = false → ∀ x, (S.post c l x).flags = c.flags

end Span

end Silmaril.X86.Loose
