module

public import Silmaril.Machine.Vex.X86.MovJump.Defs
public import Silmaril.Machine.Vex.Validate.Thms
public import Silmaril.Machine.Region.X86.Thms
public import Silmaril.Semantics.Region.Simulation.Thms

public section

namespace Silmaril.Machine.Vex.AMD64Scalar.MovJump.Proofs

open Silmaril.Semantics.Region
open Silmaril.X86 (MState State)
open Silmaril.X86.Decompile
open Silmaril.X86.Ext
open Silmaril.Machine.Region.X86 (system system_determinate system_retire)

theorem decode (fragment : Fragment) : fragment.code.decode? 2 = some fragment.listing := by
  have movBytes : encode mov = [0x48, 0x89, 0xf8] := rfl
  have jmpBytes : encode (.jmp8 fragment.displacement) = [0xeb, fragment.displacement] := rfl
  have first := decode_encode_append mov (encode (.jmp8 fragment.displacement))
  rw [movBytes, jmpBytes] at first
  change X86.Ext.decode [0x48#8, 0x89#8, 0xf8#8, 0xeb#8, fragment.displacement] = some (mov, 3) at first
  have second := decode_encode (.jmp8 fragment.displacement)
  rw [jmpBytes] at second
  change X86.Ext.decode [0xeb#8, fragment.displacement] = some (.jmp8 fragment.displacement, 2) at second
  simp [Fragment.code, Fragment.listing, Region.decode?, Region.decode, movBytes, jmpBytes,
    decodeFrom, first, second]
  rfl

theorem jumpNat (fragment : Fragment) (guard : fragment.Guard) :
    fragment.jumpPC.toNat = fragment.base.toNat + 3 := by
  have bound := guard.noWrap
  rw [Fragment.jumpPC, BitVec.toNat_add, show (3 : Word).toNat = 3 from rfl, Nat.mod_eq_of_lt]
  omega

private theorem startsNe (fragment : Fragment) (guard : fragment.Guard) : fragment.jumpPC ≠ fragment.base := by
  intro equal
  have jump := jumpNat fragment guard
  rw [equal] at jump
  omega

theorem simpleExit (fragment : Fragment) (guard : fragment.Guard) {input : Input}
    (entry : input.rip = fragment.base) :
    FirstExit fragment.simple fragment.support input [] (fragment.block.run input) := by
  have advancePC : (advance input).rip = fragment.jumpPC := by simp [advance, Fragment.jumpPC, entry]
  have first : fragment.simple.step input [] (advance input) := ⟨rfl, by simp [Fragment.step?, entry]⟩
  have second : fragment.simple.step (advance input) [] (fragment.block.run input) := by
    refine ⟨rfl, ?_⟩
    simp only [Fragment.step?, advancePC, ite_eq_right (startsNe fragment guard)]
    rfl
  exact .step (.inl (congrArg BitVec.toNat entry)) first
    (.leave (.inr (congrArg BitVec.toNat advancePC)) second guard.leaves)

@[expose] def realizes (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word) :
    Realizes fragment.simple (system ret) where
  relates := fragment.Related completion
  pc := fun ⟨same, _⟩ => congrArg (fun input : Input => input.rip.toNat) same
  step := by
    rintro small full es next ⟨same, loaded⟩ ⟨rfl, smallStep⟩
    subst small
    change fragment.step? (project completion full) = some next at smallStep
    by_cases atMov : (project completion full).rip = fragment.base
    · rw [Fragment.step?, ite_eq_left atMov, Option.some.injEq] at smallStep
      subst next
      let final : MState := ⟨{ full.core.write .rax (full.core.read .rdi) with rip := full.core.rip + 3 },
        full.memory⟩
      have fetch := Region.decode?_fetch (decode fragment) loaded
        (d := ⟨fragment.base.toNat, mov, 3⟩) (by simp [Fragment.listing])
      have addr : full.core.rip = fragment.base := atMov
      refine ⟨final, system_retire (addr ▸ fetch) ?_ (by simp [mov]), ?_, loaded⟩
      · simp [final, mov, exec, retire, writeRM, Sz.write]
        rfl
      · simp [final, advance, project, X86.Op.step, State.read_write_other]
    · rw [Fragment.step?, ite_eq_right atMov] at smallStep
      by_cases atJump : (project completion full).rip = fragment.jumpPC
      · rw [ite_eq_left atJump, Option.some.injEq] at smallStep
        subst next
        let final : MState := ⟨{ full.core with rip := fragment.target }, full.memory⟩
        have fetch := Region.decode?_fetch (decode fragment) loaded
          (d := ⟨fragment.base.toNat + 3, .jmp8 fragment.displacement, 2⟩) (by simp [Fragment.listing])
        have jump : full.core.rip = fragment.jumpPC := atJump
        have addr := (congrArg BitVec.toNat jump).trans (jumpNat fragment guard)
        refine ⟨final, system_retire (addr ▸ fetch) ?_ (by simp), rfl, loaded⟩
        simp [final, exec, Fragment.target, jump]
        rfl
      · simp [atJump] at smallStep

theorem fullExit (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {input : Input} {initial : MState} (entry : input.rip = fragment.base)
    (related : fragment.Related completion input initial) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      fragment.Related completion (fragment.block.run input) final := by
  obtain ⟨final, run, output⟩ := (realizes fragment guard completion ret).firstExit
    (simpleExit fragment guard entry) related
  exact ⟨final, run.completes (system_determinate ret), output⟩

theorem smallGuard (fragment : Fragment) (guard : fragment.Guard) {input : Input}
    (entry : input.rip = fragment.base) :
    ExitsNormally fragment.simple fragment.support input [] (fragment.block.run input) := by
  have det : Determinate fragment.simple :=
    ⟨fun left right => ⟨left.1.trans right.1.symm, Option.some.inj (left.2.symm.trans right.2)⟩,
      fun {_ _ _ stop} _ => nomatch stop⟩
  exact (simpleExit fragment guard entry).completes det

theorem entryWP (fragment : Fragment) (guard : fragment.Guard) (Q : Nat → List Empty → Input → Prop)
    (input : Input) : fragment.entryWP Q input ↔
    input.rip = fragment.base ∧ Q fragment.target.toNat [] (fragment.block.run input) := by
  constructor
  · rintro ⟨entry, safe⟩
    exact ⟨entry, safe.1 input [] _ rfl (simpleExit fragment guard entry)⟩
  · rintro ⟨entry, post⟩
    refine ⟨entry, ⟨?_, ?_⟩⟩
    · intro s es out equal run
      subst s
      obtain ⟨rfl, rfl⟩ := (smallGuard fragment guard entry).unique es out run
      exact post
    · intro _ _ _ stop _ _ _
      exact nomatch stop

theorem wpNoUB (fragment : Fragment) (Q : Nat → List Empty → Input → Prop) :
    NoUB fragment.simple (fragment.entryWP Q) fragment.support (fun _ => False) (fun _ => False) :=
  noUB_of_wp (fun _ ub => ub.elim) (fun _ admits => ⟨admits.2.1, fun _ _ _ stop _ _ _ => nomatch stop⟩)

theorem wpContract (fragment : Fragment) (guard : fragment.Guard) (Q : Nat → List Empty → Input → Prop) :
    TotalHoare fragment.simple (fragment.entryWP Q) fragment.support Q (fun _ _ _ => False) :=
  ⟨(wp_iff Q (fun _ _ _ => False)).mpr (fun _ admits => admits.2),
    fun _ admits => (smallGuard fragment guard admits.1).finishes⟩

theorem transferWP (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    (Q : Nat → List Empty → Input → Prop) {admit : MState → Prop}
    {ubStop : Silmaril.X86.Ext.Outcome → Prop}
    (initial : ∀ full, admit full → fragment.code.LoadedIn full.memory ∧ fragment.entryWP Q (project completion full)) :
    NoUB (system ret) admit fragment.support (fun _ => False) ubStop ∧
    TotalHoare (system ret) admit fragment.support (fun label es full => Q label es (project completion full))
      (fun stop _ _ => ubStop stop) := by
  have transfer := (realizes fragment guard completion ret).transferContract (system_determinate ret)
    (wpNoUB fragment Q) (wpContract fragment guard Q)
    (fun _ admits => .inl (congrArg BitVec.toNat admits.1))
    (fun full admits => let ⟨load, pre⟩ := initial full admits; ⟨_, pre, rfl, load⟩) (ubFullStop := ubStop)
  refine ⟨transfer.1, ⟨⟨?_, transfer.2.1.1.2⟩, transfer.2.1.2⟩⟩
  intro state es out admits run
  obtain ⟨_, ⟨rfl, _⟩, post⟩ := transfer.2.1.1.1 state es out admits run
  exact post

theorem scalarDecode (fragment : Fragment) :
    X86.decode fragment.base fragment.bytes = .ok fragment.block := by
  have imm : BitVec.ofNat 8 (UInt8.ofNat fragment.displacement.toNat).toNat = fragment.displacement := by
    simp
  change Except.map (X86.prepend .movRdiToRax fragment.base)
    (X86.finish fragment.jumpPC [] (.jmp (X86.relative8 (fragment.jumpPC + 2)
      (UInt8.ofNat fragment.displacement.toNat)))) = .ok fragment.block
  rw [X86.relative8, imm]
  rfl

theorem postcondition (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {input : Input} {initial : MState} (entry : input.rip = fragment.base)
    (related : fragment.Related completion input initial) (property : List Empty → Input → Prop)
    (proved : property [] (fragment.block.run input)) :
    (∃ final, ExitsNormally (system ret) fragment.support initial [] final) ∧
    ∀ trace final, FirstExit (system ret) fragment.support initial trace final →
      property trace (project completion final) := by
  obtain ⟨final, normal, output⟩ := fullExit fragment guard completion ret entry related
  refine ⟨⟨final, normal⟩, ?_⟩
  intro trace next run
  obtain ⟨rfl, rfl⟩ := normal.unique trace next run
  rwa [← output.1]

theorem regionSound (fragment : Fragment) (guard : fragment.Guard) (ret : Word) :
    Sound (system ret) (fun initial => initial.core.rip = fragment.base ∧ fragment.code.LoadedIn initial.memory)
      fragment.support (· = fragment.target.toNat) := by
  intro initial trace final ⟨entry, loaded⟩ run
  have result := postcondition fragment guard false ret entry ⟨rfl, loaded⟩
    (fun _ out => out.rip.toNat = fragment.target.toNat) rfl
  exact result.2 trace final run

theorem validatedExit (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {raw : Raw.Block} {pair : Pair} (accepted : validate fragment.base fragment.bytes raw = .ok pair)
    {initial : MState} (entry : initial.core.rip = fragment.base) (loaded : fragment.code.LoadedIn initial.memory) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      pair.target.run (project completion initial) = .ok (project completion final) := by
  have cert := validate_certifies accepted
  have source : pair.source = fragment.block := Except.ok.inj (cert.decoded.symm.trans (scalarDecode fragment))
  obtain ⟨final, normal, output⟩ := fullExit fragment guard completion ret entry ⟨rfl, loaded⟩
  refine ⟨final, normal, ?_⟩
  rw [translation_runs cert.translates _ entry, source, output.1]

theorem validatedBeh (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {raw : Raw.Block} {pair : Pair} (accepted : validate fragment.base fragment.bytes raw = .ok pair)
    {initial : MState} (entry : initial.core.rip = fragment.base) (loaded : fragment.code.LoadedIn initial.memory) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      ∀ outcome, (targetSem pair.target).Beh (project completion initial) outcome ↔
        outcome = .returned (project completion final) := by
  obtain ⟨final, normal, runs⟩ := validatedExit fragment guard completion ret accepted entry loaded
  refine ⟨final, normal, fun outcome => ?_⟩
  rw [targetSem, boundary_beh]
  simp [runs, Except.toOption]

end Silmaril.Machine.Vex.AMD64Scalar.MovJump.Proofs
