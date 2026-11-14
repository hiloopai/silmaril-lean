module

public import Silmaril.Elf.Effects.Defs
import Silmaril.Proofs.Elf.Effects.Sound
import Silmaril.Proofs.Elf.Effects.Derived

/-!
# Effects of x86 code: soundness of certificates, and effects from reachable nodes

* `sound`: **in the `Setting`, every run from the entry covers its calls, imports, system calls
  and unknown steps by `N`** (`ReachIn`). Proved for any machine and stable decoder: the machine
  enters only through the flow law (`Setting.law`). `task_sound` discharges `Task.sound`.
* `sound_str9`: the single-threaded `Str9` machine, under the open flow law
  `Task.flowLaw_str9`.
* `codeLoaded_of`: the `CodeLoaded` field from `CodeAt` rows of every block, the placement and
  `CodeStable`.
* `reaches_mem`, `reaches_mono`, `reach_mono`: reachability against a listed, closed node set
  (decidable: `CallGraph.closedB`), monotonicity in the graph and in the node set.
* `syscalls_of_reach`, `foreign_of_reach`, `okB_sound`, `sysOk_mono`: effects read off the nodes.
* `check_union`: composition; the union of two checked certificates is checked.
-/

@[expose] public section

namespace Silmaril.Elf.Effects

open Silmaril.X86 (Word MState)
open Silmaril.X86.Flow (FlowDec FlowLaw)
open Silmaril.X86.Link (Blob)

variable {σ : Type}

/-- **Soundness of a checked certificate.** -/
theorem sound {W : World σ} {D : FlowDec} {base : Word} {P : Cert} {esc : List Nat} {entry : Nat}
    {keep : σ → Prop} {s₀ : σ} {N : Node → Prop} (hS : Setting W D base P esc entry keep s₀ N) :
    ReachIn W D base keep s₀ N :=
  Silmaril.Proofs.Elf.Effects.sound hS

theorem task_sound : Task.sound := fun _ _ _ _ _ _ _ _ _ hS => sound hS

/-- **Soundness on the single-threaded `Str9` machine**, given its flow law. -/
theorem sound_str9 (hlaw : Silmaril.X86.Flow.Task.flowLaw_str9) {W : World MState} {base : Word}
    {P : Cert} {esc : List Nat} {entry : Nat} {keep : MState → Prop} {s₀ : MState}
    {N : Node → Prop} (hJ : W.J = Silmaril.X86.Flow.str9)
    (hS : FlowLaw W.J Silmaril.X86.Flow.X64.dec → Setting W Silmaril.X86.Flow.X64.dec base P esc entry keep s₀ N) :
    ReachIn W Silmaril.X86.Flow.X64.dec base keep s₀ N :=
  sound (hS (hJ ▸ hlaw))

/-- **The code is loaded**, from `CodeAt` rows, the placement and code stability. -/
theorem codeLoaded_of {W : World σ} {D : FlowDec} {F : Blob} {base : Word} {P : Cert}
    {keep : σ → Prop} {s₀ : σ}
    (hcode : ∀ f C, (f, C) ∈ P.fns → ∀ b ∈ C.blocks, Link.ElfBind.CodeAt F b.start b.bytes)
    (hp : Link.ElfBind.Placement F base) (hs : CodeStable W D F base keep s₀) :
    CodeLoaded W D base P keep s₀ :=
  Silmaril.Proofs.Elf.Effects.codeLoaded_of hcode hp hs

/-- Reachable nodes are in a listed set closed under the edges and holding the roots. -/
theorem reaches_mem {G : CallGraph} {roots L : List Node} (hc : G.closedB L = true)
    (hr : ∀ n ∈ roots, n ∈ L) {n : Node} (h : G.Reaches roots n) : n ∈ L :=
  Silmaril.Proofs.Elf.Effects.reaches_mem hc hr h

/-- Reachability is monotone in the graph. -/
theorem reaches_mono {G H : CallGraph} (hle : G.Le H) {roots : List Node} {n : Node}
    (h : G.Reaches roots n) : H.Reaches roots n :=
  Silmaril.Proofs.Elf.Effects.reaches_mono hle h

/-- `ReachIn` is monotone in the node set. -/
theorem reach_mono {W : World σ} {D : FlowDec} {base : Word} {keep : σ → Prop} {s₀ : σ}
    {N N' : Node → Prop} (h : ReachIn W D base keep s₀ N) (hle : ∀ n, N n → N' n) :
    ReachIn W D base keep s₀ N' :=
  Silmaril.Proofs.Elf.Effects.reach_mono h hle

/-- **Effects from reachable nodes.** -/
theorem syscalls_of_reach {W : World σ} {D : FlowDec} {base : Word} {keep : σ → Prop} {s₀ : σ}
    {N : Node → Prop} {summ : Summ} {ok : Nat → Prop} (h : ReachIn W D base keep s₀ N)
    (hN : ∀ n, N n → n.SysOk summ ok) : SyscallsOk W D base keep s₀ summ ok :=
  Silmaril.Proofs.Elf.Effects.syscalls_of_reach h hN

/-- **`no_spawn` from reachable nodes.** -/
theorem noSpawn_of_reach {W : World σ} {D : FlowDec} {base : Word} {keep : σ → Prop} {s₀ : σ}
    {N : Node → Prop} {summ : Summ} (h : ReachIn W D base keep s₀ N)
    (hN : ∀ n, N n → n.SysOk summ (notIn spawnNrs)) : SyscallsOk W D base keep s₀ summ (notIn spawnNrs) :=
  syscalls_of_reach h hN

/-- **Imports from reachable nodes.** -/
theorem foreign_of_reach {W : World σ} {D : FlowDec} {base : Word} {keep : σ → Prop} {s₀ : σ}
    {N : Node → Prop} {I : Ref → Prop} (h : ReachIn W D base keep s₀ N)
    (hN : ∀ r, N (.ext r) → I r) : ForeignIn W D base keep s₀ I :=
  Silmaril.Proofs.Elf.Effects.foreign_of_reach h hN

theorem okB_sound {summ : Summ} {ok : Nat → Bool} {n : Node} (h : n.okB summ ok = true) :
    n.SysOk summ (fun k => ok k = true) :=
  Silmaril.Proofs.Elf.Effects.okB_sound h

theorem sysOk_mono {summ : Summ} {ok ok' : Nat → Prop} {n : Node} (h : n.SysOk summ ok)
    (hle : ∀ k, ok k → ok' k) : n.SysOk summ ok' :=
  Silmaril.Proofs.Elf.Effects.sysOk_mono h hle

/-- **Composition**: two checked certificates give a checked union. -/
theorem check_union {D : FlowDec} {P Q : Cert} {r₁ r₂ : List Nat} (hP : P.check D r₁ = true)
    (hQ : Q.check D r₂ = true) : (P.union Q).check D (r₁ ++ r₂) = true :=
  Silmaril.Proofs.Elf.Effects.check_union hP hQ

end Silmaril.Elf.Effects
