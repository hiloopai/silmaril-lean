module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core.Glob
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core.Mem

/-!
# The tool's frame machine against Core 3.0 `Step`: results

The header of `Defs`. **Proved**, for every profile and host of silmaril-lean's Core 3.0 `Step`,
the straight-line instructions of the frame machine, from a Core frame whose locals are the
machine's (`localsF`), with the machine's operands as value instructions (`stackA`), under any
code after them:

* `pure_core`: every pure instruction `pexec` runs (`nop`, `drop`, `local.get/set/tee`, `i32`
  constants, unary, binary, test and comparison operators); `div_trap_core`: a binary operator
  the machine traps on traps in Core;
* `global_get_core`, `global_set_core`: `global.get` and `global.set` on a store whose globals
  hold the machine's (`GlobalsAre`), which `global.set` keeps;
* `load_core`, `store_core`: `i32.load` and `i32.store` at an **aligned**, in-bounds address of
  a `cap`-byte memory whose aligned words are the machine's (`MemAre`), which `store` keeps
  (a four-byte store leaves the other aligned words); `load_oob_core`, `store_oob_core`: past
  `cap` bytes Core traps, as the bounded machine `stepB` does.

**Open** (`Task.machine_core`, frozen): the control instructions (`call`, `return`, `if`,
falling off the end) and the alignment of the asyncified program's accesses, assembled into a
simulation from the Core call of a function. **Conditional on it**: `call_done_core` and
`call_trap_core`, one export call of the asyncified program on the bounded machine (one round of
the host protocol of `tgtStepB`) and the Core call agree on results, final globals and memory,
and traps.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type}

/-- **A pure instruction of the machine is a Core 3.0 run.** -/
theorem pure_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) {i : Instr} {ls ops ls' ops' : List W}
    (h : pexec i ls ops = some (ls', ops')) (rest : List Admin) :
    Execution.Core.Steps Pf host ⟨s, localsF f ls, stackA ops ++ .plain i :: rest⟩
      ⟨s, localsF f ls', stackA ops' ++ rest⟩ :=
  pexec_core s f h rest

/-- A division the machine traps on traps in Core 3.0. -/
theorem div_trap_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (ls ops : List W) (op : IntBinOp) (y x : W)
    {e : Numerics.IntTrap} (hb : Numerics.intBinOp .i32 op x y = .error e) (rest : List Admin) :
    Step Pf host ⟨s, localsF f ls, stackA (y :: x :: ops) ++ .plain (.intBinOp .i32 op) :: rest⟩
      ⟨s, localsF f ls, stackA ops ++ .trap :: rest⟩ :=
  pexec_div_trap s f ls ops op y x hb rest

/-- `global.get` reads the machine's global. -/
theorem global_get_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin) {ls ops gs : List W}
    (hg : GlobalsAre s f gs) (g : GlobalIdx) {v : W} (hv : gs[g.value.val]? = some v) :
    Execution.Core.Steps Pf host ⟨s, localsF f ls, stackA ops ++ .plain (.globalGet g) :: rest⟩
      ⟨s, localsF f ls, stackA (v :: ops) ++ rest⟩ :=
  run_gget s f rest hg g hv

/-- `global.set` writes the machine's global. -/
theorem global_set_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin) {ls ops gs : List W}
    (hg : GlobalsAre s f gs) (g : GlobalIdx) (v : W) (hlt : g.value.val < gs.length) :
    ∃ a gi, s.global? f g = some (a, gi) ∧
      GlobalsAre (s.setGlobal a (Val.i32 v)) f (gs.set g.value.val v) ∧
      Execution.Core.Steps Pf host
        ⟨s, localsF f ls, stackA (v :: ops) ++ .plain (.globalSet g) :: rest⟩
        ⟨s.setGlobal a (Val.i32 v), localsF f ls, stackA ops ++ rest⟩ :=
  run_gset s f rest hg g v hlt

/-- **`i32.load` at an aligned address in bounds loads the machine's word.** -/
theorem load_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin) {ls ops : List W}
    {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (x : W) (arg : MemArg)
    (ha : (x.toNat + arg.offset.val) % 4 = 0) (hcap : x.toNat + arg.offset.val + 4 ≤ cap) :
    Execution.Core.Steps Pf host
      ⟨s, localsF f ls, stackA (x :: ops) ++ .plain (.intLoad .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF f ls, stackA (mem (x.toNat + arg.offset.val) :: ops) ++ rest⟩ :=
  run_load s f rest hM x arg ha hcap

/-- **`i32.store` at an aligned address in bounds stores the machine's word.** -/
theorem store_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin) {ls ops : List W}
    {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (v x : W) (arg : MemArg)
    (ha : (x.toNat + arg.offset.val) % 4 = 0) (hcap : x.toNat + arg.offset.val + 4 ≤ cap) :
    ∃ s', MemAre s' f (upd mem (x.toNat + arg.offset.val) v) cap ∧
      (∀ g, s'.global? f g = s.global? f g) ∧ s'.funcs = s.funcs ∧
      Execution.Core.Steps Pf host
        ⟨s, localsF f ls, stackA (v :: x :: ops) ++ .plain (.intStore .i32 none ⟨0⟩ arg) :: rest⟩
        ⟨s', localsF f ls, stackA ops ++ rest⟩ :=
  run_store s f rest hM v x arg ha hcap

/-- `i32.load` past the memory traps in Core. -/
theorem load_oob_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin) {ls ops : List W}
    {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (x : W) (arg : MemArg)
    (hcap : cap < x.toNat + arg.offset.val + 4) :
    Step Pf host
      ⟨s, localsF f ls, stackA (x :: ops) ++ .plain (.intLoad .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF f ls, stackA ops ++ .trap :: rest⟩ :=
  run_load_oob s f rest hM x arg hcap

/-- `i32.store` past the memory traps in Core. -/
theorem store_oob_core (Pf : Profile) (host : HostSemantics H) (s : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin) {ls ops : List W}
    {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (v x : W) (arg : MemArg)
    (hcap : cap < x.toNat + arg.offset.val + 4) :
    Step Pf host
      ⟨s, localsF f ls, stackA (v :: x :: ops) ++ .plain (.intStore .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF f ls, stackA ops ++ .trap :: rest⟩ :=
  run_store_oob s f rest hM v x arg hcap

/-! ## Conditional on the open target -/

theorem bsteps_core {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env}
    {R : Cfg → Config H → Prop}
    (hnext : ∀ c C c', R c C → stepB cap E c = .next c' →
      ∃ C', Execution.Core.Steps Pf host C C' ∧ R c' C') {c c' : Cfg} (h : BSteps cap E c c') :
    ∀ {C}, R c C → ∃ C', Execution.Core.Steps Pf host C C' ∧ R c' C' := by
  induction h with
  | refl c => exact fun hR => ⟨_, .refl, hR⟩
  | cons hs _ ih =>
    intro C hR
    obtain ⟨C₁, h₁, hR₁⟩ := hnext _ _ _ hR hs
    obtain ⟨C₂, h₂, hR₂⟩ := ih hR₁
    exact ⟨C₂, h₁.trans h₂, hR₂⟩

/-- **Conditional on `Task.machine_core`**: an export call of the asyncified program that the
bounded machine runs to a return is a Core 3.0 call that returns the same values, with a store
holding the machine's final globals and memory. -/
theorem call_done_core (ht : Task.machine_core) (Pf : Profile) (host : HostSemantics H)
    (P : Prog) (hP : P.WF) (cap : Nat) (h4 : cap % 4 = 0) (hsb : P.sb + 4 * P.frameWords ≤ cap)
    (h32 : cap < 2 ^ 32) :
    ∃ R : Cfg → Config H → Prop,
      ∀ (e : Nat) (fd : FnDef) (args : List W) (s : Store H) (mi : ModuleInst) (gs : List W)
        (mem : Nat → W) (c c' : Cfg) (vs : List W),
        HoldsProg s mi (asyncifyProg P) → P.imps.length ≤ e →
        (asyncifyProg P).fns[e - P.imps.length]? = some fd → args.length = fd.nparams →
        GlobalsAre s ⟨[], mi⟩ gs → MemAre s ⟨[], mi⟩ mem cap →
        BSteps cap (asyncifyProg P) ⟨[entry e fd args], gs, mem⟩ c →
        stepB cap (asyncifyProg P) c = .done vs c' →
        ∃ C s', R c C ∧ Execution.Core.Steps Pf host
            ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩ C ∧
          Execution.Core.Steps Pf host C ⟨s', C.frame, stackA vs⟩ ∧
          HoldsProg s' C.frame.module (asyncifyProg P) ∧ GlobalsAre s' C.frame c'.globals ∧
          MemAre s' C.frame c'.mem cap := by
  obtain ⟨R, hinit, hnext, hdone, -⟩ := ht (H := H) Pf host P hP cap h4 hsb h32
  refine ⟨R, fun e fd args s mi gs mem c c' vs hH he hfd ha hg hm hs hd => ?_⟩
  obtain ⟨C, hC, hR⟩ := bsteps_core hnext hs (hinit e fd args s mi gs mem hH he hfd ha hg hm)
  obtain ⟨s', h1, h2, h3, h4⟩ := hdone _ _ _ _ hR hd
  exact ⟨C, s', hR, hC, h1, h2, h3, h4⟩

/-- **Conditional on `Task.machine_core`**: a trap of the bounded machine in an export call is a
trap of the Core 3.0 call. -/
theorem call_trap_core (ht : Task.machine_core) (Pf : Profile) (host : HostSemantics H)
    (P : Prog) (hP : P.WF) (cap : Nat) (h4 : cap % 4 = 0) (hsb : P.sb + 4 * P.frameWords ≤ cap)
    (h32 : cap < 2 ^ 32) (e : Nat) (fd : FnDef) (args : List W) (s : Store H) (mi : ModuleInst)
    (gs : List W) (mem : Nat → W) (c : Cfg) (hH : HoldsProg s mi (asyncifyProg P))
    (he : P.imps.length ≤ e) (hfd : (asyncifyProg P).fns[e - P.imps.length]? = some fd)
    (ha : args.length = fd.nparams) (hg : GlobalsAre s ⟨[], mi⟩ gs)
    (hm : MemAre s ⟨[], mi⟩ mem cap) (hs : BSteps cap (asyncifyProg P) ⟨[entry e fd args], gs, mem⟩ c)
    (ht' : stepB cap (asyncifyProg P) c = .trap) :
    ∃ C', Execution.Core.Steps Pf host
        ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩ C' ∧
      C'.code = [.trap] := by
  obtain ⟨R, hinit, hnext, -, htrap⟩ := ht (H := H) Pf host P hP cap h4 hsb h32
  obtain ⟨C, hC, hR⟩ := bsteps_core hnext hs (hinit e fd args s mi gs mem hH he hfd ha hg hm)
  obtain ⟨C', h1, h2⟩ := htrap _ _ hR ht'
  exact ⟨C', hC.trans h1, h2⟩

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.store_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms store_core

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.pure_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pure_core

end Silmaril.Wasm.FX.Asyncify.Tool
