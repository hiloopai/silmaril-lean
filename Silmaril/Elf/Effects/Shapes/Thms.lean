module

public import Silmaril.Elf.Effects.Shapes.Defs
public import Silmaril.Elf.Effects.Thms
import Silmaril.Proofs.Elf.Effects.Shapes

/-!
# Effect shapes from checked certificates

A row proves `CertOk D X loc P esc v L` (by `decide`, plus a `CodeAt` row per block):
`P` checked with the function `v` and the escapes as roots, `L` a listed node set closed under
`P`'s edges, holding the roots and not `unresolved`. Then:

* `callGraphSub_of_cert`: the calls stay in `P`'s graph (`CallGraphSub`);
* `syscallSet_of_cert`, `noSpawn_of_cert`, `noNetwork_of_cert`, `noExec_of_cert`,
  `foreignCalls_of_cert`: the effect shapes, from a decidable test of every node of `L`
  (`Node.okB` with the import summaries `summ`);
* `noSpawn_of_callGraph`, `syscallSet_of_callGraph`: the same from `CallGraphSub` and a
  statement on the reachable nodes;
* `syscallSet_mono`: a larger set.

Every shape is over every admissible world (`Admissible`), whose flow law, kernel, library,
indirect-branch and return frames are hypotheses of the world, not of the row.
-/

@[expose] public section

namespace Silmaril.Elf.Effects.Shapes

open Silmaril.Project (Value)
open Silmaril.X86.Flow (FlowDec UMach)
open Silmaril.Elf.Shapes (file)

variable {σ V : Type}

theorem callGraphSub_of_cert {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) :
    CallGraphSub J D X loc P esc :=
  Silmaril.Proofs.Elf.Effects.Shapes.callGraphSub h

/-- **`no_spawn` from a call graph** whose reachable nodes do not spawn. -/
theorem noSpawn_of_callGraph {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {summ : Summ} (hG : CallGraphSub J D X loc P esc)
    (hN : ∀ v, Func.At ⟨file X, loc⟩ v → ∀ n, P.reach v esc n → n.SysOk summ (notIn spawnNrs)) :
    NoSpawn J D X loc P esc summ :=
  Silmaril.Proofs.Elf.Effects.Shapes.syscalls hG hN

/-- **A system-call set from a call graph.** -/
theorem syscallSet_of_callGraph {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {summ : Summ} {S : List Nat} (hG : CallGraphSub J D X loc P esc)
    (hN : ∀ v, Func.At ⟨file X, loc⟩ v → ∀ n, P.reach v esc n → n.SysOk summ (· ∈ S)) :
    SyscallSet J D X loc P esc summ S :=
  Silmaril.Proofs.Elf.Effects.Shapes.syscalls hG hN

theorem syscallSet_of_cert {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) {summ : Summ}
    {S : List Nat} (hok : L.all (Node.okB summ S.contains) = true) :
    SyscallSet J D X loc P esc summ S :=
  syscallSet_of_callGraph (callGraphSub_of_cert h) fun w hw n hn =>
    sysOk_mono (Silmaril.Proofs.Elf.Effects.Shapes.okOfList h hok w hw n hn) (by simp)

theorem noSpawn_of_cert {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) {summ : Summ}
    (hok : L.all (Node.okB summ fun k => !spawnNrs.contains k) = true) :
    NoSpawn J D X loc P esc summ :=
  noSpawn_of_callGraph (callGraphSub_of_cert h) fun w hw n hn =>
    sysOk_mono (Silmaril.Proofs.Elf.Effects.Shapes.okOfList h hok w hw n hn) (by simp [notIn])

theorem noNetwork_of_cert {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) {summ : Summ}
    (hok : L.all (Node.okB summ fun k => !netNrs.contains k) = true) :
    NoNetwork J D X loc P esc summ :=
  Silmaril.Proofs.Elf.Effects.Shapes.syscalls (callGraphSub_of_cert h) fun w hw n hn =>
    sysOk_mono (Silmaril.Proofs.Elf.Effects.Shapes.okOfList h hok w hw n hn) (by simp [notIn])

theorem noExec_of_cert {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) {summ : Summ}
    (hok : L.all (Node.okB summ fun k => !execNrs.contains k) = true) :
    NoExec J D X loc P esc summ :=
  Silmaril.Proofs.Elf.Effects.Shapes.syscalls (callGraphSub_of_cert h) fun w hw n hn =>
    sysOk_mono (Silmaril.Proofs.Elf.Effects.Shapes.okOfList h hok w hw n hn) (by simp [notIn])

theorem foreignCalls_of_cert {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) :
    ForeignCalls J D X loc P esc (importsOf L) :=
  Silmaril.Proofs.Elf.Effects.Shapes.foreignCalls h

/-- **A larger set.** -/
theorem syscallSet_mono {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {summ : Summ} {S S' : List Nat} (h : SyscallSet J D X loc P esc summ S)
    (hle : ∀ n ∈ S, n ∈ S') : SyscallSet J D X loc P esc summ S' := by
  intro v hv W base s₀ hA es y hr e he n hn
  exact sysOk_mono (h v hv W base s₀ hA es y hr e he n hn) hle

end Silmaril.Elf.Effects.Shapes
