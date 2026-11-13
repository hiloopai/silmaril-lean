module

public import Silmaril.Compiler.Core.Verified.OpsLink.Defs
public import Silmaril.Compiler.Core.Verified.LoopSim.Defs

/-! # The link of a `main` with several blocks

`link blocks` is the whole linked program of a `main` compiled to a control-flow graph: one Lir
function, `__ccomp_start`, whose blocks are `blocks` (entry block 0); it takes `argc` and
`argv` in registers 1 and 2. The control block and the initial image are those of
`OpsLink.link`.

`exit_obs`: crt0 observes a return of `w` with the initial linear memory as `exit (w mod 256)`
with no output. `link_sound`: when the Lir run of the entry either is related to a Core state
reached from the start whose `Sim.AllowedFrom` covers every Lir behaviour and whose stuck runs
reach undefined behaviour, or Core can reach undefined behaviour, every observation of the
artifact is allowed by the document (`Spec.Allowed`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopLink

open Silmaril.Cerberus
open Silmaril.Machine
open Spec Backend
open Relation

/-- `__ccomp_start(argc, argv)` with the given blocks. -/
def startFunc (blocks : List (Lir.Block Mir.Reg)) : Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0, blocks := blocks }

/-- The linked program of a `main` with the given blocks. -/
def link (blocks : List (Lir.Block Mir.Reg)) : Mir.Linked where
  prog := ⟨[startFunc blocks]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

theorem link_funcs (blocks : List (Lir.Block Mir.Reg)) :
    (link blocks).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

/-- The entry state: block 0, `argc` and `argv` in registers 1 and 2. -/
theorem link_start (blocks : List (Lir.Block Mir.Reg)) (argc argv : Lir.Word) (mem : Lir.Memory) :
    (link blocks).prog.start 0 [argc, argv] mem =
      some ⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩ := rfl

theorem link_block (blocks : List (Lir.Block Mir.Reg)) (l : Lir.Label) :
    (link blocks).prog.block? 0 l = blocks[l]? := rfl

/-- A return of `w` with the initial linear memory is observed as `exit (w mod 256) []`. -/
theorem exit_obs {blocks : List (Lir.Block Mir.Reg)} {a : Artifact}
    (h : artifactOf (link blocks) = .ok a) {args : List String} {w : Lir.Word} {o : Obs}
    (obs : LirObs (.returned [w] (a.lmem args)) o) : o = .exit (w.toNat % 256) [] := by
  have himg : a.image = .empty := by
    rw [(ConstLink.artifact_layout h).2.2]; rfl
  obtain ⟨k, out, rfl, hk, hout⟩ := obs
  have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) :
      memWord (a.lmem args) addr = 0 := by
    apply ConstLink.memWord_zero
    intro i
    apply ConstLink.lmem_bytes_empty himg
    rw [(ConstLink.artifact_layout h).1]
    have := i.isLt
    omega
  rw [hk w rfl, ConstLink.stdoutOf_zero (hzero (ctlAddr + 24) (by decide))
    (hzero (ctlAddr + 48) (by decide)) hout]

/-- The entry state of the artifact run with `args`. -/
def entryState (a : Artifact) (args : List String) : Lir.State Mir.Reg :=
  ⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 (BitVec.ofNat 64 args.length)).set 2 (BitVec.ofNat 64 a.argBase), [],
    a.lmem args⟩

/-- **The link is correct** when the entry run is related to Core. -/
theorem link_sound {blocks : List (Lir.Block Mir.Reg)} {a : Artifact}
    (h : artifactOf (link blocks) = .ok a) {doc : Codec.Document} {args : List String}
    (entry : CoreUB doc args ∨ ∃ initial labels c, coreStart doc args = .ok (initial, labels) ∧
      ReflTransGen (coreStep doc.file labels) initial c ∧
      (∀ b o, Lir.Behaves (link blocks).prog (entryState a args) b → LirObs b o →
        Sim.AllowedFrom doc.file labels c o) ∧
      (Lir.Behaves (link blocks).prog (entryState a args) .stuck → Sim.UBFrom doc.file labels c))
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) : Allowed doc args o := by
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  rw [link_start] at hs
  cases hs
  rcases entry with ub | ⟨initial, labels, c, hinit, reach, beh, stuck⟩
  · exact .inr (.inl ub)
  rcases ho with ho | hstuck | ⟨b, hb, hobs⟩
  · exact .inl ho
  · exact Sim.AllowedFrom.allowed hinit reach (.inr (.inl (stuck hstuck)))
  · exact Sim.AllowedFrom.allowed hinit reach (beh b o hb hobs)

end Silmaril.Compile.Core.Verified.LoopLink
