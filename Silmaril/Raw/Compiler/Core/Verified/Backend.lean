module

public import Silmaril.Compiler.Core.Backend.Defs
public import Silmaril.Machine.X86.Lir.Behaviour.Defs
public import Silmaril.X86.Ext.Regions

/-! # The backend bridge: machine observations are observations of Lir behaviours

`artifactOf_sound` is the target half of every `Verified.compile` proof. For a linked
program `l` with `Backend.artifactOf l = .ok a`, every observation `o` of the loaded
artifact (`Spec.MachineBeh`, on a machine satisfying `Spec.Loaded`) is

* exhaustion; or
* comes from a Lir run of `l.prog` from `__ccomp_start` on the initial linear memory
  `a.lmem args` that gets stuck (source undefined behaviour, for the translation to account
  for); or
* the crt0 observation `LirObs b o` of a Lir behaviour `b` of that run: a return of `v`
  exits with `v mod 256`, a trap reads the exit/abort word and status from the control
  block of the final Lir memory, divergence diverges; the output is the output buffer of
  the final Lir memory (`StdoutOf`).

So a Core→Lir translation proves `Spec.SoundSpec` by showing that the Lir behaviours of
`__ccomp_start` are allowed by the Core program, without looking at x86-64.

The proof composes `Lir.Alloc.spill_refines` (spilling with `firstK 7`) and
`X86.Backend.compile_refines`, and reads the control block through `MemRel` once the
machine memory is known to keep its regions (`Ext.beh_returned_regions`,
`Ext.beh_trapped_regions`). The stack-check sites of the artifact are the backend's
(`artifactOf` refuses requirements above `maxStackNeed`, which the observation would cap).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified

open Silmaril.Machine
open Silmaril.X86.Backend (Space MemRel)
open Spec Backend

/-! ## The observation of a Lir memory -/

/-- The 8-byte little-endian word of a Lir memory at `addr` (`Spec.lword` on the linear
memory). -/
def memWord (lm : Lir.Memory) (addr : Nat) : Nat :=
  leNat (List.ofFn fun i : Fin 8 => lm.bytes (addr + i))

/-- The output buffer of a Lir memory (control words 6 and 3), when it lies in the
memory. -/
def memStdout? (lm : Lir.Memory) : Option (List UInt8) :=
  let addr := memWord lm (ctlAddr + 48)
  let len := memWord lm (ctlAddr + 24)
  if addr + len ≤ lm.size then
    some ((List.ofFn fun i : Fin len => lm.bytes (addr + i)).map fun b => b.toNat.toUInt8)
  else none

/-- `out` is what the startup code writes for the final Lir memory `lm`: its output
buffer, when that lies in the linear memory. -/
def StdoutOf (lm : Lir.Memory) (out : List UInt8) : Prop :=
  ∀ x, memStdout? lm = some x → out = x

/-- The observation of a trap (not exhaustion) with final Lir memory `lm` and output
`out`: after the runtime's `exit` (word 5 = 1) the status of word 4, after `abort`
(word 5 = 2) SIGABRT, otherwise the trap. -/
def trapObs (lm : Lir.Memory) (out : List UInt8) : Obs :=
  let kind := memWord lm (ctlAddr + 40)
  if kind = 1 then .exit (memWord lm (ctlAddr + 32) % 256) out
  else if kind = 2 then .abort out
  else .trap out

/-- The observations crt0 can make of a Lir behaviour of `__ccomp_start`. -/
def LirObs : Lir.Behavior → Obs → Prop
  | .returned vs lm, o => ∃ k out, o = .exit k out ∧
      (∀ v, vs.head? = some v → k = v.toNat % 256) ∧ StdoutOf lm out
  | .trapped lm, o => ∃ out, o = trapObs lm out ∧ StdoutOf lm out
  | .stuck, _ => False
  | .diverges, o => o = .diverges

/-! ## Reading the linear memory from the machine -/

section Read

variable {S : Space} {n : Nat} (hv : S.Valid n) {lm : Lir.Memory} {m : Process.Memory}
  (hreg : m.regions = S.regions n) (hm : MemRel S lm m)
include hv hreg hm

theorem lword_eq {addr : Nat} (hin : addr + 8 ≤ lm.size) :
    Spec.lword S m addr = memWord lm addr := by
  simp only [Spec.lword, X86.Backend.readBytes_lin hv hreg hm hin, Option.map_some,
    Option.getD_some, memWord]

theorem stdoutOf_rel (hctl : ctlAddr + 56 ≤ lm.size) : StdoutOf lm (Spec.stdoutOf S m) := by
  intro x hx
  simp only [memStdout?] at hx
  split at hx
  · rename_i hin
    cases hx
    simp only [Spec.stdoutOf, lword_eq hv hreg hm (addr := ctlAddr + 48) (by omega),
      lword_eq hv hreg hm (addr := ctlAddr + 24) (by omega),
      X86.Backend.readBytes_lin hv hreg hm hin, Option.getD_some]
  · cases hx

theorem observe_trapped {t : X86.MState} (ht : t.memory = m) (hctl : ctlAddr + 56 ≤ lm.size) :
    LirObs (.trapped lm) (Spec.observe S (.trapped t)) := by
  subst ht
  refine ⟨Spec.stdoutOf S t.memory, ?_, stdoutOf_rel hv hreg hm hctl⟩
  simp only [Spec.observe, trapObs, lword_eq hv hreg hm (addr := ctlAddr + 40) (by omega),
    lword_eq hv hreg hm (addr := ctlAddr + 32) (by omega)]

end Read

/-! ## The bridge -/

theorem sites_eq {sites : List (Nat × Nat)} (h : sites.all (·.2 ≤ maxStackNeed) = true) :
    sites.map (fun (x, n) => (x, min n maxStackNeed)) = sites := by
  rw [List.all_eq_true] at h
  conv => rhs; rw [← List.map_id sites]
  refine List.map_congr_left fun ⟨x, k⟩ hx => ?_
  have := h _ hx
  simp only [decide_eq_true_eq] at this
  simp [Nat.min_eq_left this]

/-- **The backend bridge.** Every observation of the loaded artifact of a link is
exhaustion, or comes from the Lir run of `__ccomp_start` on the artifact's initial linear
memory: that run gets stuck, or it has a behaviour that crt0 observes as `o`. -/
theorem artifactOf_sound {l : Mir.Linked} {a : Artifact} (h : artifactOf l = .ok a)
    {S : Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0) {saved : X86.Reg → X86.Word}
    {init : X86.State} {args : List String} {o : Obs} (hb : MachineBeh a S exit E0 saved init args o) :
    ∃ start s, l.funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some start ∧
      l.prog.start start [BitVec.ofNat 64 args.length, BitVec.ofNat 64 a.argBase]
        (a.lmem args) = some s ∧
      (o = .exhausted ∨ Lir.Behaves l.prog s .stuck ∨
        ∃ b, Lir.Behaves l.prog s b ∧ LirObs b o) := by
  unfold artifactOf at h
  split at h
  · cases h
  rename_i img hc
  split at h
  · cases h
  rename_i start hstart
  split at h
  · cases h
  split at h
  · cases h
  rename_i henter
  split at h
  · cases h
  rename_i hsites
  have ha := Except.ok.inj h
  have hcode : a.code = img.code := by rw [← ha]
  have hentry : a.entry = img.layout.func start := by rw [← ha]
  have hcb : a.codeBase = codeBase := by rw [← ha]
  have hmem : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize := by rw [← ha]
  have hsites' : a.sites = X86.Backend.stackSites (lower l) img.layout := by
    rw [← ha]
    exact sites_eq (by simpa using hsites)
  obtain ⟨s, hs⟩ : ∃ s, l.prog.start start
      [BitVec.ofNat 64 args.length, BitVec.ofNat 64 a.argBase] (a.lmem args) = some s := by
    cases hf : l.prog.funcs[start]? with
    | none => simp [hf] at henter
    | some f =>
      have hp : f.params.length = 2 := by simpa [hf] using henter
      obtain ⟨p, q, hp⟩ := List.length_eq_two.mp hp
      exact ⟨⟨⟨start, f.entry, 0⟩,
        (Lir.Frame.empty.write p (BitVec.ofNat 64 args.length)).write q
          (BitVec.ofNat 64 a.argBase), [], a.lmem args⟩,
        by simp [Lir.Prog.start, Lir.Prog.enter, Lir.Prog.func?, hf, hp, Lir.Frame.writeAll]⟩
  refine ⟨start, s, hstart, hs, ?_⟩
  by_cases hsafe : (Lir.sem l.prog).Safe s
  swap
  · exact .inr (.inl ((Lir.beh_iff_behaves (b := .stuck)).mp (Classical.not_not.mp hsafe)))
  -- spilling
  obtain ⟨t, ht, -⟩ := Lir.Alloc.spill_start (Lir.Alloc.firstK_valid 7) hs
  have hspill := Lir.Alloc.spill_refines (Lir.Alloc.firstK_valid 7) (p := l.prog)
  have hI : ∃ f args mem, l.prog.start f args mem = some s ∧
      (Lir.Alloc.spill (Lir.Alloc.firstK 7) l.prog).start f args mem = some t :=
    ⟨start, [BitVec.ofNat 64 args.length, BitVec.ofNat 64 a.argBase], a.lmem args, hs, ht⟩
  have hsafe_t : (Lir.sem (lower l)).Safe t := hspill.safe hI hsafe
  -- the x86-64 backend
  have hc' : X86.Backend.compile assign (lower l) S.codeBase = .ok img := by
    rw [hl.codeBase, hcb]
    exact hc
  have hvalid : S.Valid img.code.length := hcode ▸ hl.valid
  have hexit : exit.toNat < S.codeBase ∨ S.codeBase + img.code.length ≤ exit.toNat :=
    hcode ▸ hl.exit_out
  have hR := X86.Backend.compile_refines assign (lower l) S hc' hvalid exit E0 saved hl.e0_hi
    hl.e0_lo hl.align hexit
  obtain ⟨-, hcodeE, hLE⟩ := X86.Backend.compile_ok hc'
  obtain ⟨out, hout, rfl⟩ := hb
  rw [hsites', hcode, hentry] at hout
  have hout0 := hout
  rw [hcodeE, hLE] at hout
  have hctl : ∀ lm' : Lir.Memory, lm'.size = S.memSize → ctlAddr + 56 ≤ lm'.size := by
    intro lm' h
    rw [h, hl.memSize, hmem]
    decide
  obtain ⟨o', ho', hrel⟩ := hR _ t
    ⟨a.lmem args, start, [BitVec.ofNat 64 args.length, BitVec.ofNat 64 a.argBase],
      init, hl.memSize.symm, ht, rfl⟩ hsafe_t out hout
  obtain ⟨o'', ho'', hrel'⟩ := hspill t s hI hsafe o' ho'
  obtain rfl : o' = o'' := Behaviour.Outcome.Rel.strict_id_iff.mp hrel'
  cases out with
  | returned final =>
    obtain ⟨⟨vs, lm'⟩, rfl, hfin⟩ := Behaviour.Outcome.Rel.returned_left hrel
    refine .inr (.inr ⟨.returned vs lm', (Lir.beh_iff_behaves (b := .returned vs lm')).mp ho'', ?_⟩)
    have hreg : final.memory.regions = S.regions img.code.length :=
      X86.Ext.beh_returned_regions hout0
    refine ⟨_, _, rfl, fun v hv => ?_, stdoutOf_rel hvalid hreg hfin.mem (hctl _ hfin.mem.1)⟩
    cases vs with
    | nil => cases hv
    | cons v' vs =>
      cases hv
      exact congrArg (fun w : X86.Word => w.toNat % 256) (hfin.vals 0 (by simp))
  | trapped tt =>
    cases o' <;> simp [Behaviour.Outcome.Rel] at hrel
    rename_i lm'
    refine .inr (.inr ⟨.trapped lm', (Lir.beh_iff_behaves (b := .trapped lm')).mp ho'', ?_⟩)
    have hreg : tt.memory.regions = S.regions img.code.length := X86.Ext.beh_trapped_regions hout0
    exact observe_trapped hvalid hreg hrel rfl (hctl _ hrel.1)
  | faulted φ =>
    cases o' <;> simp [Behaviour.Outcome.Rel] at hrel
    rename_i e
    exact e.elim
  | undefined =>
    obtain rfl := Behaviour.Outcome.Rel.undefined_left.mp hrel
    exact absurd ho' hsafe_t
  | exhausted => exact .inl rfl
  | diverges =>
    cases o' <;> simp [Behaviour.Outcome.Rel] at hrel
    exact .inr (.inr ⟨.diverges, (Lir.beh_iff_behaves (b := .diverges)).mp ho'', rfl⟩)

end Silmaril.Compile.Core.Verified
