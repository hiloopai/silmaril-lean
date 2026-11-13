module

public import Silmaril.Compiler.Mir.Interp.Defs
public import Silmaril.Compile.Category.Lattice
public import Silmaril.Machine.CBackend.Lir.Behaviour.Defs
@[expose] public section

/-!
# The semantics of Mir

A Mir program is the list of units of a link (`Mir.link`). Its meaning is **by definition**
the Lir semantics (`Lir.sem`) of its link: the run of the link's first function (Lir function
`0`, the entry: `Mir.link` keeps what it reaches) on no arguments, over the linear memory of
`Config.memSize` bytes that holds the link's image from `dataBase` and zeros elsewhere. A
program whose link fails, or whose entry takes arguments, has no behaviour (it is not a
program; front ends report the error).

Undefined behaviour is closed upwards (`ubClose`): a run that gets stuck in Lir (an unwritten
register, an access outside the memory, a division by zero) allows every outcome. This is the
reading under which refinement (`Syntax.RefinesOn`) and validity (`Valid`) are the usual
compiler-correctness statements, and under which Mir → Mir passes are compilers at the
identity convention.

`Mir.lang cfg` is the zoo `Language`: interfaces are trivial for now (one closed program);
observations are Lir outcomes (`Lir.Outcome`: the returned values and final memory, the trap
and its memory, divergence, or undefined). `lirLang cfg` is the language of closed Lir
programs over the same memory configuration, and `linkCompiler` is `Mir.link` as a compiler
`Mir.lang cfg ⟶ lirLang cfg` at the identity convention, valid by definition.

`Mir.run` is the executable interpreter: `Mir.link` followed by `Mir.Interp.run` (the
array-based Lir interpreter whose operators are proved equal to Lir's), with no NULL guard
and no depth limit beyond the fuel, so that it decides `beh` up to fuel. `ccomp --interp`
runs the same interpreter with the process's NULL guard (`Silmaril.Compile.Target.interp`).

## Intended theorem (`Mir.run` is adequate)

For a configuration `cfg`, units `us` and fuel `n`: if `run cfg n us = .ok o` and `o` is
`returned vs m`, `trapped m` or `stuck`, then `beh cfg us` contains `returned (vs', m')`,
`trapped m'` or is `Set.univ` respectively, where `vs' = vs.map UInt64.toBitVec` and
`m' = m.toLir`. `Mir.Interp`'s operator lemmas (`unop_eq`, `binop_eq`, `extend_eq`) are
the arithmetic half; the state correspondence is the other half.
-/

namespace Silmaril.Compile.Mir

open Silmaril.Machine
open Silmaril.Compile.Category
open Silmaril.Machine.Behaviour (Outcome)

/-- The outcomes of a Lir run: the returned values and final memory, or the trap and its
memory; Lir has no faults. -/
abbrev LirOutcome : Type := Outcome (List Lir.Word × Lir.Memory) Lir.Memory Empty

/-- Undefined behaviour allows every outcome. -/
def ubClose (B : Set LirOutcome) : Set LirOutcome := {o | o ∈ B ∨ .undefined ∈ B}

theorem subset_ubClose (B : Set LirOutcome) : B ⊆ ubClose B := fun _ h => .inl h

theorem ubClose_mono {B B' : Set LirOutcome} (h : B ⊆ B') : ubClose B ⊆ ubClose B' :=
  fun _ ho => ho.imp (fun h' => h h') (fun h' => h h')

theorem ubClose_of_undefined {B : Set LirOutcome} (h : .undefined ∈ B) : ubClose B = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr h

theorem ubClose_of_not_undefined {B : Set LirOutcome} (h : .undefined ∉ B) : ubClose B = B :=
  Set.ext fun _ => ⟨fun ho => ho.elim id (fun h' => absurd h' h), .inl⟩

theorem ubClose_idem (B : Set LirOutcome) : ubClose (ubClose B) = ubClose B := by
  by_cases h : Outcome.undefined ∈ B
  · rw [ubClose_of_undefined h, ubClose_of_undefined (Set.mem_univ (Outcome.undefined : LirOutcome))]
  · rw [ubClose_of_not_undefined h, ubClose_of_not_undefined h]

/-- The memory configuration of a link: where data and function pointers go, and the size of
the linear memory. -/
structure Config where
  layout : Layout
  memSize : Nat

/-- The initial linear memory of a link: its image from `dataBase`, zeros elsewhere. -/
def initMem (cfg : Config) (l : Linked) : Lir.Memory :=
  ⟨cfg.memSize, fun a =>
    if l.dataBase ≤ a ∧ a < l.dataBase + l.image.size then
      BitVec.ofNat 8 (l.image.get! (a - l.dataBase)).toNat
    else 0⟩

/-- A closed Lir program: code, entry function, arguments and initial memory. -/
structure LirProgram where
  prog : Lir.Prog Nat
  entry : Lir.FuncId
  args : List Lir.Word
  mem : Lir.Memory

/-- The behaviours of a closed Lir program: the outcomes of `Lir.sem` from its start state,
closed under undefined behaviour; none if the start is undefined. -/
def LirProgram.beh (q : LirProgram) : Set LirOutcome :=
  match q.prog.start q.entry q.args q.mem with
  | some s => ubClose {o | (Lir.sem q.prog).Beh s o}
  | none => ∅

/-- The closed Lir program of a link: entry function `0`, no arguments. -/
def toLir (cfg : Config) (l : Linked) : LirProgram := ⟨l.prog, 0, [], initMem cfg l⟩

/-- **The meaning of Mir** (a definition): the behaviours of the closed Lir program of the
link; none if the link fails. -/
def beh (cfg : Config) (us : Array Unit) : Set LirOutcome :=
  match link cfg.layout us with
  | .ok l => (toLir cfg l).beh
  | .error _ => ∅

/-- Mir as a language of the zoo: closed programs (lists of units), observed through their
Lir outcomes. -/
def lang (cfg : Config) : Language.{0} := ⟨PUnit, Array Unit, fun _ => ⟨⟩, LirOutcome, beh cfg⟩

/-- Closed Lir programs as a language of the zoo. -/
def lirLang : Language.{0} := ⟨PUnit, LirProgram, fun _ => ⟨⟩, LirOutcome, LirProgram.beh⟩

/-- `Mir.link` as a compiler to closed Lir programs at the identity of observations. It is
valid by definition: this is the statement that Mir means the Lir semantics of its link. -/
def linkCompiler (cfg : Config) : Compiler (lang cfg) lirLang where
  conv := ⟨id, Eq⟩
  run us := match link cfg.layout us with
    | .ok l => some (toLir cfg l)
    | .error _ => none
  sound us q h := by
    refine (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, ?_, rfl⟩⟩
    change o ∈ beh cfg us
    unfold beh
    split at h
    · rename_i l hl
      cases h
      exact ho
    · cases h

/-- The meaning of Mir is the meaning of its link, as an equation. -/
theorem beh_eq_link (cfg : Config) (us : Array Unit) (l : Linked)
    (h : link cfg.layout us = .ok l) : beh cfg us = (toLir cfg l).beh := by
  simp [beh, h]

/-! ## Determinism -/

/-- A closed Lir program has one behaviour, or (after undefined behaviour) all of them. -/
theorem LirProgram.beh_subsingleton_or_univ (q : LirProgram) :
    q.beh.Subsingleton ∨ q.beh = Set.univ := by
  unfold LirProgram.beh
  split
  · rename_i s _
    by_cases hu : Outcome.undefined ∈ {o | (Lir.sem q.prog).Beh s o}
    · exact .inr (ubClose_of_undefined hu)
    · rw [ubClose_of_not_undefined hu]
      exact .inl fun _ h₁ _ h₂ => Behaviour.Semantics.Beh.unique (Lir.sem_deterministic _) h₁ h₂
  · exact .inl Set.subsingleton_empty

/-- A closed Lir program that starts has a behaviour. -/
theorem LirProgram.beh_nonempty (q : LirProgram) {s : Lir.State Nat}
    (h : q.prog.start q.entry q.args q.mem = some s) : q.beh.Nonempty := by
  unfold LirProgram.beh
  rw [h]
  obtain ⟨o, ho⟩ := Lir.beh_exists (p := q.prog) s
  exact ⟨o, subset_ubClose _ ho⟩

theorem beh_subsingleton_or_univ (cfg : Config) (us : Array Unit) :
    (beh cfg us).Subsingleton ∨ beh cfg us = Set.univ := by
  unfold beh
  split
  · exact LirProgram.beh_subsingleton_or_univ _
  · exact .inl Set.subsingleton_empty

/-- Mir is deterministic on every program without undefined behaviour. -/
theorem deterministicOn_safe (cfg : Config) :
    (lang cfg).syntax.DeterministicOn {us | beh cfg us ≠ Set.univ} (beh cfg) :=
  fun us hus => (beh_subsingleton_or_univ cfg us).resolve_right hus

/-! ## The executable interpreter -/

/-- The image of a link in the interpreter's memory. -/
def Interp.initMem (cfg : Config) (l : Linked) : Interp.Mem :=
  Interp.Mem.ofImage cfg.memSize l.dataBase l.image

/-- **The Mir interpreter**: link, then run the entry function on no arguments for at most
`fuel` steps (no NULL guard, no depth limit beyond the fuel). -/
def run (cfg : Config) (fuel : Nat) (us : Array Unit) : Except String Interp.Outcome := do
  let l ← match link cfg.layout us with
    | .ok l => pure l
    | .error e => throw e.message
  let code := Interp.load l.prog
  let m ← Interp.start code 0 [] (Interp.initMem cfg l)
  return Interp.run code { guard := 0, maxDepth := fuel + 1 } fuel m

end Silmaril.Compile.Mir
