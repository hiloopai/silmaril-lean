module

public import Silmaril.X86.Features.Feature
public import Silmaril.X86.Features.State
public import Silmaril.Machine.Decoder
public import Silmaril.Process.Memory

/-!
# Instruction-set extensions

An `Extension` packages one family of instructions for the feature-parametric
machine (`Features.Machine`):

* `Syntax`: its instruction type, with decidable equality;
* `decoder`: a prefix-code byte decoder satisfying the `Machine.Decoder` laws
  (decoding reads only the consumed bytes; every encoding decodes to itself
  whatever follows);
* `requires`: the features an instruction needs; the machine raises #UD when
  one is missing, as hardware does;
* `exec`: the semantics, given the consumed length, the extended state and the
  memory. It reports a retirement, an architectural fault (`Fault`), or
  `unmodeled`: the model makes no claim, and at the process level any
  continuation is allowed (chaos).

`exec` must advance RIP itself (by the length, or to a branch target).

## Pure register semantics

`Extension.Pure e x` says that `x` retires on every state and memory, leaves
the memory alone, does not read it, and advances RIP by the length: its effect
is a function of the register state. `Result.pure f` builds such a result and
the `Pure.*` lemmas are its kit (`retires`, `ne_fault`, `ne_unmodeled`,
`memory_independent`, `rip`); `Pure.of_eq` shows that an `exec` clause
written with `Result.pure` is pure.

## Adding an extension

1. Put the family under `Silmaril/X86/Features/Ext/<Family>/` with `Syntax.lean`
   (the instruction type, `deriving DecidableEq, Repr`), `Encoding.lean` (an
   encoder, a decoder and the five `Machine.Decoder` laws, packaged as a
   `Machine.Decoder`), `Semantics.lean` (`exec` on `State`/`Memory`, using
   `State.xmm`/`ymm`/`zmm` and `writeXmmLegacy` for legacy SSE,
   `writeXmmVex`/`writeYmmVex`/`writeZmm` for VEX/EVEX) and `Extension.lean`
   (`def ext : Extension`).
2. `requires`: every feature the SDM page lists for the form, e.g. `[.avx2]`
   for VEX.256 `vpshufb`, `[.avx512f, .avx512vl]` for EVEX.128 forms,
   `[.vaes, .avx512f]` for EVEX `vaesenc` on ZMM. The machine raises
   `featureUD` for the first one missing.
3. Prove `Disjoint ext e` against the other extensions it is used with, and
   that the integer decoder rejects its encodings (needed by `step_of_ext`;
   `Ext.parseRaw` returning `.bad` on the encoding's opcode map, with
   `Ext.good_parseRaw.bad`, gives it for every continuation).
4. Use `Result.unmodeled` for anything not modelled (it is chaos); never
   return an arbitrary value.
5. Differential tests: generate vectors by executing the forms for real
   (`scripts/x86-features/gen_vectors.py` shows the pattern) and check them
   with `#guard` through `ext.exec`, plus `decide`/`rfl` theorems on
   representative vectors. `Features.Checks.hexFields` parses the vector
   strings.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.Process (Memory)

/-- An architectural fault an extension instruction can raise. No fault
carries a successor state; nothing changes and RIP addresses the faulting
instruction. -/
inductive Fault where
  /-- #UD for a reason other than a missing feature (for example a reserved
  encoding field, or LOCK on a non-lockable form). -/
  | invalidOpcode
  /-- #GP(0), for example a misaligned 128/256/512-bit aligned operand or a
  reserved MXCSR bit. -/
  | generalProtection
  /-- #XM, an unmasked SIMD floating-point exception, with the MXCSR the
  handler observes. -/
  | simdException (mxcsr : Float.MXCSR)
  /-- #MF, an unmasked pending x87 exception, with the x87 status word the
  handler observes. -/
  | x87Exception (status : BitVec 16)
  /-- #DE. -/
  | divideError
  /-- A data access was not permitted or not backed (#PF/#GP at the process
  level: SIGSEGV). -/
  | dataFault
  deriving DecidableEq, Repr

/-- The result of executing an extension instruction. -/
inductive Result where
  | retired (state : State) (memory : Memory)
  | fault (f : Fault)
  /-- Outside the model: any continuation is allowed. -/
  | unmodeled

/-- An instruction-set extension. -/
structure Extension where
  /-- A name for diagnostics and documentation. -/
  name : String
  Syntax : Type
  [decEq : DecidableEq Syntax]
  decoder : Machine.Decoder Syntax
  requires : Syntax → List Feature
  exec : Syntax → Nat → State → Memory → Result

attribute [instance] Extension.decEq

/-! ## Missing features -/

/-- The first required feature not in `F`. -/
def FeatureSet.missing (F : FeatureSet) : List Feature → Option Feature
  | [] => none
  | f :: fs => if F.has f then F.missing fs else some f

theorem FeatureSet.missing_eq_none_iff {F : FeatureSet} {fs : List Feature} :
    F.missing fs = none ↔ ∀ f ∈ fs, f ∈ F := by
  induction fs with
  | nil => simp [missing]
  | cons f fs ih =>
    unfold missing
    split <;> simp_all [FeatureSet.mem_iff]

theorem FeatureSet.missing_not_mem {F : FeatureSet} {fs : List Feature} {f : Feature}
    (h : F.missing fs = some f) : f ∈ fs ∧ f ∉ F := by
  induction fs with
  | nil => simp [missing] at h
  | cons g fs ih =>
    unfold missing at h
    split at h
    · obtain ⟨h1, h2⟩ := ih h; exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rename_i hg; cases h; simp_all [FeatureSet.mem_iff]

/-- A superset has nothing more missing. -/
theorem FeatureSet.missing_mono {F G : FeatureSet} (hFG : F ⊆ G) {fs : List Feature}
    (h : F.missing fs = none) : G.missing fs = none :=
  missing_eq_none_iff.mpr fun f hf => hFG f (missing_eq_none_iff.mp h f hf)

/-! ## Pure register semantics -/

/-- Retire with the register effect `f`, RIP advanced by `length`, memory unchanged. -/
def Result.pure (f : State → State) (length : Nat) (s : State) (memory : Memory) : Result :=
  .retired ((f s).advance length) memory

namespace Extension

variable (e : Extension)

/-- `x` is a pure register instruction: its result is `Result.pure f` for one
register effect `f` that does not change RIP. -/
def Pure (x : e.Syntax) : Prop :=
  ∃ f : State → State, (∀ s, (f s).rip = s.rip) ∧
    ∀ length s memory, e.exec x length s memory = Result.pure f length s memory

/-- An instruction whose `exec` clause is `Result.pure f` is pure. -/
theorem Pure.of_eq {x : e.Syntax} (f : State → State) (hrip : ∀ s, (f s).rip = s.rip)
    (h : ∀ length s memory, e.exec x length s memory = Result.pure f length s memory) :
    e.Pure x :=
  ⟨f, hrip, h⟩

variable {e}

/-- A pure instruction retires. -/
theorem Pure.retires {x : e.Syntax} (hx : e.Pure x) (length : Nat) (s : State) (memory : Memory) :
    ∃ t, e.exec x length s memory = .retired t memory := by
  obtain ⟨f, -, h⟩ := hx
  exact ⟨_, h length s memory⟩

/-- A pure instruction does not fault and is modelled. -/
theorem Pure.ne_fault {x : e.Syntax} (hx : e.Pure x) (length : Nat) (s : State)
    (memory : Memory) (flt : Fault) : e.exec x length s memory ≠ .fault flt := by
  obtain ⟨t, h⟩ := hx.retires length s memory
  rw [h]; nofun

theorem Pure.ne_unmodeled {x : e.Syntax} (hx : e.Pure x) (length : Nat) (s : State)
    (memory : Memory) : e.exec x length s memory ≠ .unmodeled := by
  obtain ⟨t, h⟩ := hx.retires length s memory
  rw [h]; nofun

/-- A pure instruction's register effect does not depend on memory. -/
theorem Pure.memory_independent {x : e.Syntax} (hx : e.Pure x) (length : Nat) (s : State)
    (m₁ m₂ : Memory) {t₁ t₂ : State} (h₁ : e.exec x length s m₁ = .retired t₁ m₁)
    (h₂ : e.exec x length s m₂ = .retired t₂ m₂) : t₁ = t₂ := by
  obtain ⟨f, -, h⟩ := hx
  rw [h, Result.pure] at h₁ h₂
  cases h₁; cases h₂; rfl

/-- A pure instruction advances RIP by its length. -/
theorem Pure.rip {x : e.Syntax} (hx : e.Pure x) (length : Nat) (s : State) (memory : Memory)
    {t : State} {m : Memory} (h : e.exec x length s memory = .retired t m) :
    t.rip = s.rip + BitVec.ofNat 64 length ∧ m = memory := by
  obtain ⟨f, hrip, hf⟩ := hx
  rw [hf, Result.pure] at h
  cases h
  exact ⟨by simp [hrip], rfl⟩

end Extension

@[simp] theorem Result.pure_eq (f : State → State) (length : Nat) (s : State) (memory : Memory) :
    Result.pure f length s memory = .retired ((f s).advance length) memory := rfl

/-! ## Embeddings between extensions -/

/-- `e` embeds into `e'`: every instruction `e` decodes is decoded by `e'` to an
image that requires the same features and executes the same way. -/
def Extension.Embeds (e e' : Extension) : Prop :=
  ∃ ι : e.Syntax → e'.Syntax,
    (∀ bytes x n, e.decoder.decode bytes = some (x, n) → e'.decoder.decode bytes = some (ι x, n)) ∧
    (∀ x, e'.requires (ι x) = e.requires x) ∧
    (∀ x n s m, e'.exec (ι x) n s m = e.exec x n s m)

theorem Extension.Embeds.refl (e : Extension) : e.Embeds e :=
  ⟨id, fun _ _ _ h => h, fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem Extension.Embeds.trans {e₁ e₂ e₃ : Extension} (h₁ : e₁.Embeds e₂) (h₂ : e₂.Embeds e₃) :
    e₁.Embeds e₃ := by
  obtain ⟨ι, hd, hr, hx⟩ := h₁
  obtain ⟨κ, hd', hr', hx'⟩ := h₂
  exact ⟨κ ∘ ι, fun b x n h => hd' b _ n (hd b x n h), fun x => (hr' _).trans (hr x),
    fun x n s m => (hx' _ n s m).trans (hx x n s m)⟩

/-- Two extensions never decode the same bytes. -/
def Extension.Disjoint (e e' : Extension) : Prop :=
  ∀ bytes, e.decoder.decode bytes = none ∨ e'.decoder.decode bytes = none

/-- Pairwise disjoint extensions (distinct list positions). -/
def Extension.PairwiseDisjoint (exts : List Extension) : Prop :=
  exts.Pairwise Extension.Disjoint

end Silmaril.X86.Features
