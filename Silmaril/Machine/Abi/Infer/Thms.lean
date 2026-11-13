module

public import Silmaril.Machine.Abi.Infer.Defs
import Silmaril.Proofs.Machine.Abi.Infer
/-! # ABI inference: soundness and exactness

* `consistentWith_iff`: the check is three inclusions (reads ⊆ allowed,
  clobbers ∩ callee-saved = ∅, result register always defined).
* `consistentWith_sound`: an accepted summary forces the register discipline
  (`Respects`) on every function it summarises.
* `consistentWith_iff_respects`: for well-formed summaries the check is exact.
* `consistent_iff_respects`, `consistent_sound`: the same for the `sysv64` and
  `ms64` families.
* `mem_infer`: inference returns exactly the consistent candidates up to the
  register bound; `consistent_arity_mono` and `consistent_arity_bound` justify
  stopping at the bound.
* `rcx_not_sysv1`: for the summary `rcxReader` (reads RCX, never RDI) some
  function with that summary breaks the one-argument System V discipline, so
  the summary cannot certify a one-argument System V prototype; it is
  consistent with one-argument Win64. `rcx_read_not_sysv` and
  `rcx_read_not_sysv_respects` generalise this to every summary that reads
  RCX and every System V arity below 4.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Infer

open Silmaril.Machine (CallingConvention)
open Silmaril.X86 (Reg)

section Generic

variable {R : Type} [DecidableEq R]

theorem consistentWith_iff (cc : CallingConvention R) (n : Nat) (returns : Bool) (u : Usage R) :
    consistentWith cc n returns u = true ↔
      (∀ r ∈ u.reads, r ∈ allowed cc n) ∧ (∀ r ∈ u.writes, r ∉ cc.calleeSaved) ∧
        (returns = true → ∀ r ∈ resultReg cc, r ∈ u.defs) :=
  Silmaril.Proofs.Machine.Abi.Infer.consistentWith_iff cc n returns u

/-- Soundness: an accepted summary forces the register discipline. -/
theorem consistentWith_sound {cc : CallingConvention R} {n : Nat} {returns : Bool}
    {u : Usage R} (check : consistentWith cc n returns u = true) {Val E : Type}
    {f : (R → Val) → (R → Val) × E} (summary : Summarizes u f) : Respects cc n returns f :=
  Silmaril.Proofs.Machine.Abi.Infer.sound check summary

/-- Exactness: for a well-formed summary, and a convention whose result register
is not an allowed input, the check accepts iff every function with the summary
respects the discipline. Values and effects are universally quantified in
`Type`; Booleans already suffice for the converse. -/
theorem consistentWith_iff_respects {cc : CallingConvention R} {n : Nat} {returns : Bool}
    {u : Usage R} (wf : ∀ r ∈ u.defs, r ∈ u.writes)
    (resultFree : ∀ r ∈ resultReg cc, r ∉ allowed cc n) :
    consistentWith cc n returns u = true ↔
      ∀ (Val E : Type) (f : (R → Val) → (R → Val) × E), Summarizes u f →
        Respects cc n returns f :=
  ⟨fun check _ _ _ summary => consistentWith_sound check summary,
    fun all => Silmaril.Proofs.Machine.Abi.Infer.complete wf resultFree (all Bool Bool)⟩

end Generic

/-- RAX, the result register of both families, is never an allowed input. -/
theorem resultFree (fam : Family) (n : Nat) :
    ∀ r ∈ resultReg fam.cc, r ∉ allowed fam.cc n := by
  intro r reg inside
  cases fam <;>
  · simp only [resultReg, Family.cc, Silmaril.X86.sysv64, ms64, List.head?_cons,
      Option.mem_def, Option.some.injEq] at reg
    subst reg
    simp only [allowed, List.mem_append, List.mem_singleton] at inside
    rcases inside with (inside | inside) | inside
    · exact absurd (List.mem_of_mem_take inside) (by decide)
    · exact absurd inside (by decide)
    · exact absurd inside (by decide)

theorem consistent_sound {u : Usage Reg} {c : Candidate} (check : consistent u c = true)
    {Val E : Type} {f : (Reg → Val) → (Reg → Val) × E} (summary : Summarizes u f) :
    Respects c.family.cc c.arity c.returns f :=
  consistentWith_sound check summary

theorem consistent_iff_respects {u : Usage Reg} (wf : ∀ r ∈ u.defs, r ∈ u.writes)
    (c : Candidate) :
    consistent u c = true ↔
      ∀ (Val E : Type) (f : (Reg → Val) → (Reg → Val) × E), Summarizes u f →
        Respects c.family.cc c.arity c.returns f :=
  consistentWith_iff_respects wf (resultFree c.family c.arity)

/-- Allowed inputs grow with the arity. -/
theorem allowed_mono {R : Type} (cc : CallingConvention R) {m n : Nat} (le : m ≤ n) :
    ∀ r ∈ allowed cc m, r ∈ allowed cc n := by
  intro r inside
  simp only [allowed, List.mem_append] at inside ⊢
  rcases inside with (inside | inside) | inside
  · exact .inl (.inl ((List.take_prefix_take_left le).subset inside))
  · exact .inl (.inr inside)
  · exact .inr inside

/-- Consistency is upward closed in the arity: unused arguments are allowed. -/
theorem consistent_arity_mono {u : Usage Reg} {fam : Family} {m n : Nat} {returns : Bool}
    (le : m ≤ n) (check : consistent u ⟨fam, m, returns⟩ = true) :
    consistent u ⟨fam, n, returns⟩ = true := by
  obtain ⟨reads, writes, result⟩ := (consistentWith_iff _ _ _ _).1 check
  exact (consistentWith_iff _ _ _ _).2
    ⟨fun r read => allowed_mono _ le r (reads r read), writes, result⟩

/-- Beyond the register bound, extra arguments are on the stack and do not
change consistency. -/
theorem consistent_arity_bound {u : Usage Reg} {fam : Family} {n : Nat} {returns : Bool}
    (le : fam.bound ≤ n) :
    consistent u ⟨fam, n, returns⟩ = consistent u ⟨fam, fam.bound, returns⟩ := by
  have : allowed fam.cc n = allowed fam.cc fam.bound := by
    simp only [allowed, Family.bound, List.take_of_length_le le, List.take_length]
  simp only [consistent, consistentWith, this]

theorem mem_infer (u : Usage Reg) (c : Candidate) :
    c ∈ infer u ↔ c.arity ≤ c.family.bound ∧ consistent u c = true := by
  obtain ⟨fam, n, returns⟩ := c
  simp only [infer, List.mem_filter, List.mem_append, Family.candidates, List.mem_flatMap,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨(⟨k, lt, e | e⟩ | ⟨k, lt, e | e⟩), check⟩ <;>
      (simp only [Candidate.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e) <;>
      exact ⟨by omega, check⟩
  · rintro ⟨le, check⟩
    refine ⟨?_, check⟩
    cases fam <;> cases returns <;> simp_all <;> omega

/-! ## Examples (kernel `decide`) -/

/-- Reads RCX before writing it, never reads RDI, writes RAX. -/
def rcxReader : Usage Reg := ⟨[.rcx], [.rax], [.rax]⟩

/-- Inconsistent with a one-argument System V prototype. -/
theorem rcxReader_not_sysv1 (returns : Bool) :
    consistent rcxReader ⟨.sysv64, 1, returns⟩ = false := by
  cases returns <;> decide

/-- Consistent with one-argument Win64, and with System V only from arity 4. -/
theorem rcxReader_ms64 : consistent rcxReader ⟨.ms64, 1, true⟩ = true := by decide
theorem rcxReader_sysv4 : consistent rcxReader ⟨.sysv64, 4, true⟩ = true := by decide
theorem rcxReader_sysv_min : minArity rcxReader .sysv64 true = some 4 := by decide

/-- Semantically: some function with RCX-reader usage breaks the one-argument
System V discipline. -/
theorem rcx_not_sysv1 (returns : Bool) :
    ¬ ∀ (Val E : Type) (f : (Reg → Val) → (Reg → Val) × E), Summarizes rcxReader f →
        Respects Silmaril.X86.sysv64 1 returns f := by
  intro all
  have := (consistent_iff_respects (by decide) ⟨.sysv64, 1, returns⟩).2 all
  rw [rcxReader_not_sysv1] at this
  exact Bool.false_ne_true this

/-- The general rule: any summary that reads RCX before writing it is
inconsistent with every System V candidate of arity below 4 (RCX is the fourth
System V argument register and not callee-saved). Reading RDI is irrelevant. -/
theorem rcx_read_not_sysv {u : Usage Reg} (read : Reg.rcx ∈ u.reads) {n : Nat} (lt : n < 4)
    (returns : Bool) : consistent u ⟨.sysv64, n, returns⟩ = false := by
  cases h : consistent u ⟨.sysv64, n, returns⟩
  · rfl
  · have inside := ((consistentWith_iff _ _ _ _).1 h).1 _ read
    change Reg.rcx ∈ allowed Silmaril.X86.sysv64 n at inside
    exfalso
    revert inside
    clear h
    rcases n with _ | _ | _ | _ | n
    · decide
    · decide
    · decide
    · decide
    · omega

/-- Semantically: for a well-formed summary that reads RCX, some function with
that summary breaks the System V discipline at every arity below 4. This is a
statement about what the summary can certify; a particular function that reads
RCX but ignores the value may still respect the discipline. -/
theorem rcx_read_not_sysv_respects {u : Usage Reg} (wf : ∀ r ∈ u.defs, r ∈ u.writes)
    (read : Reg.rcx ∈ u.reads) {n : Nat} (lt : n < 4) (returns : Bool) :
    ¬ ∀ (Val E : Type) (f : (Reg → Val) → (Reg → Val) × E), Summarizes u f →
        Respects Silmaril.X86.sysv64 n returns f := by
  intro all
  have := (consistent_iff_respects wf ⟨.sysv64, n, returns⟩).2 all
  rw [rcx_read_not_sysv read lt] at this
  exact Bool.false_ne_true this

/-- A function that clobbers RSI cannot be Win64 (RSI is callee-saved there) but
may be System V. -/
theorem rsiClobber : consistent ⟨[.rdi], [.rsi, .rax], [.rax]⟩ ⟨.ms64, 4, true⟩ = false ∧
    consistent ⟨[.rdi], [.rsi, .rax], [.rax]⟩ ⟨.sysv64, 1, true⟩ = true := by decide

end Silmaril.Machine.Abi.Infer
