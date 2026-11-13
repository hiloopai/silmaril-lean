module

public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Thms
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Init
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Env

/-!
# The bounded frame machine against Core 3.0 `Step`: whole export calls

The header of `Defs`; proofs in `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.*`. **Proved**, for
every profile and host of silmaril-lean's Core 3.0 `Step`:

* `crel_step` (`…CoreSim.Sim`): every step of the bounded machine `stepB` from a configuration
  in the relation `CRel` is matched by Core steps (`CMatch`): `call` (Core `call`, `call_ref`
  with the callee's `frame`/`label`), `return` (`return` through the labels of open arms and the
  frame), `if` (`if`, `block`, a `label 0`), falling off the end of an arm (`label` with no
  values) or of a body (`label`, `frame` with the result count), straight-line instructions,
  division traps and accesses past the memory (Core traps, and the trap reaches the top);
* `envOk_asyncify` (`…CoreSim.Env`): the asyncified program of a well-formed source passes the
  checker, so its word accesses are aligned (at `sp` or `0` plus a multiple of 4, with `sp` a
  multiple of 4) and its arms balanced;
* `machine_core_env`: the simulation from the Core call of a function, for any program that
  passes the checker; `machine_core_ginv`: for `asyncifyProg P` of a well-formed `P`. These are
  `Task.machine_core` with one more hypothesis on the initial globals, `GInv gs` (two globals,
  `sp` a multiple of 4), and without the hypotheses on `cap`;
* `call_done_core'`, `call_trap_core'`: `call_done_core` and `call_trap_core` without
  `Task.machine_core`, under `GInv gs`.

**`Task.machine_core` as frozen is not proved, and is false as stated** (not formalized): it
quantifies over every initial `gs`, also over an unaligned `sp`. For a body that only restores
and returns a local (one function, no statements, tail `local.get 0`, `F = 2`), `gs = [2, 9]`,
`cap = 12`, a byte memory of zeros and a word memory with `mem 1 = 7`, the machine returns `[7]`
(`sp := 1`, `local 0 := mem 1`) while Core loads the bytes at address 1 and returns `[0]`; the
`done` clause would need a Core run to `[7]`. The protocol only uses `sp = SB + 4 F k`, so
`GInv` holds at every call of the target system (`Prog.tGlobals`, then `state := 2`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

variable {H : Type}

/-- **The simulation of a checked program from the Core call of a function.** -/
theorem machine_core_env (Pf : Profile) (host : HostSemantics H) (E : Env) (hE : EnvOk E)
    (cap : Nat) :
    ∃ R : Cfg → Config H → Prop,
      (∀ (e : Nat) (fd : FnDef) (args : List W) (s : Store H) (mi : ModuleInst) (gs : List W)
          (mem : Nat → W), HoldsProg s mi E → E.imps.length ≤ e → e < 2 ^ 32 →
          E.fns[e - E.imps.length]? = some fd → args.length = fd.nparams →
          GlobalsAre s ⟨[], mi⟩ gs → MemAre s ⟨[], mi⟩ mem cap → GInv gs →
          R ⟨[entry e fd args], gs, mem⟩
            ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩) ∧
      (∀ c C c', R c C → stepB cap E c = .next c' →
          ∃ C', Execution.Core.Steps Pf host C C' ∧ R c' C') ∧
      (∀ c C vs c', R c C → stepB cap E c = .done vs c' →
          ∃ s', Execution.Core.Steps Pf host C ⟨s', C.frame, stackA vs⟩ ∧
            HoldsProg s' C.frame.module E ∧ GlobalsAre s' C.frame c'.globals ∧
            MemAre s' C.frame c'.mem cap) ∧
      (∀ c C, R c C → stepB cap E c = .trap →
          ∃ C', Execution.Core.Steps Pf host C C' ∧ C'.code = [.trap]) := by
  refine ⟨fun c C => ∃ mi s Z, C.frame = ⟨[], mi⟩ ∧
      Execution.Core.Steps Pf host C ⟨s, ⟨[], mi⟩, Z⟩ ∧ CRel cap E mi c s Z, ?_, ?_, ?_, ?_⟩
  · intro e fd args s mi gs mem hH he he32 hfd ha hg hm hG
    obtain ⟨h1, h2⟩ := crel_init (Pf := Pf) (host := host) hE hH he he32 hfd ha hg hm hG
    exact ⟨mi, s, _, rfl, h1, h2⟩
  · intro c C c' ⟨mi, s, Z, _, hC, hR⟩ hs
    have hm : CMatch Pf host cap E mi s Z (.next c') := hs ▸ crel_step hR
    obtain ⟨s', Z', h1, h2⟩ := hm
    exact ⟨_, hC.trans h1, mi, s', Z', rfl, .refl, h2⟩
  · intro c C vs c' ⟨mi, s, Z, hf, hC, hR⟩ hs
    have hm : CMatch Pf host cap E mi s Z (.done vs c') := hs ▸ crel_step hR
    obtain ⟨s', h1, hH, hG, hM, -⟩ := hm
    rw [hf]
    exact ⟨s', hC.trans h1, hH, hG, hM⟩
  · intro c C ⟨mi, s, Z, _, hC, hR⟩ hs
    have hm : CMatch Pf host cap E mi s Z .trap := hs ▸ crel_step hR
    obtain ⟨C', h1, h2⟩ := hm
    exact ⟨C', hC.trans h1, h2⟩

theorem fid_lt {P : Prog} (hP : P.WF) {e : Nat} {fd : FnDef} (he : P.imps.length ≤ e)
    (hfd : (asyncifyProg P).fns[e - P.imps.length]? = some fd) : e < 2 ^ 32 := by
  have hb := (Silmaril.Wasm.FX.Asyncify.Tool.Prog.wf_bounds hP).1
  have hl : e - P.imps.length < (asyncifyProg P).fns.length :=
    (List.getElem?_eq_some_iff.1 hfd).1
  have hl' : (asyncifyProg P).fns.length = P.fns.length := List.length_map ..
  omega

/-- **`Task.machine_core` for initial globals with `GInv`, proved.** The bounded machine runs
the asyncified program of a well-formed source as Core 3.0 does, from the Core call of a
function, when the initial globals are two with `sp` a multiple of 4. -/
theorem machine_core_ginv (Pf : Profile) (host : HostSemantics H) (P : Prog) (hP : P.WF)
    (cap : Nat) :
    ∃ R : Cfg → Config H → Prop,
      (∀ (e : Nat) (fd : FnDef) (args : List W) (s : Store H) (mi : ModuleInst) (gs : List W)
          (mem : Nat → W), HoldsProg s mi (asyncifyProg P) → P.imps.length ≤ e →
          (asyncifyProg P).fns[e - P.imps.length]? = some fd → args.length = fd.nparams →
          GlobalsAre s ⟨[], mi⟩ gs → MemAre s ⟨[], mi⟩ mem cap → GInv gs →
          R ⟨[entry e fd args], gs, mem⟩
            ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩) ∧
      (∀ c C c', R c C → stepB cap (asyncifyProg P) c = .next c' →
          ∃ C', Execution.Core.Steps Pf host C C' ∧ R c' C') ∧
      (∀ c C vs c', R c C → stepB cap (asyncifyProg P) c = .done vs c' →
          ∃ s', Execution.Core.Steps Pf host C ⟨s', C.frame, stackA vs⟩ ∧
            HoldsProg s' C.frame.module (asyncifyProg P) ∧ GlobalsAre s' C.frame c'.globals ∧
            MemAre s' C.frame c'.mem cap) ∧
      (∀ c C, R c C → stepB cap (asyncifyProg P) c = .trap →
          ∃ C', Execution.Core.Steps Pf host C C' ∧ C'.code = [.trap]) := by
  obtain ⟨R, hi, hn, hd, ht⟩ := machine_core_env Pf host (asyncifyProg P) (envOk_asyncify hP) cap
  exact ⟨R, fun e fd args s mi gs mem hH he hfd ha hg hm hG =>
    hi e fd args s mi gs mem hH he (fid_lt hP he hfd) hfd ha hg hm hG, hn, hd, ht⟩

/-- **One export call that the bounded machine runs to a return is a Core 3.0 call** returning
the same values, with a store holding the machine's final globals and memory. -/
theorem call_done_core' (Pf : Profile) (host : HostSemantics H) (P : Prog) (hP : P.WF)
    (cap : Nat) :
    ∃ R : Cfg → Config H → Prop,
      ∀ (e : Nat) (fd : FnDef) (args : List W) (s : Store H) (mi : ModuleInst) (gs : List W)
        (mem : Nat → W) (c c' : Cfg) (vs : List W),
        HoldsProg s mi (asyncifyProg P) → P.imps.length ≤ e →
        (asyncifyProg P).fns[e - P.imps.length]? = some fd → args.length = fd.nparams →
        GlobalsAre s ⟨[], mi⟩ gs → MemAre s ⟨[], mi⟩ mem cap → GInv gs →
        BSteps cap (asyncifyProg P) ⟨[entry e fd args], gs, mem⟩ c →
        stepB cap (asyncifyProg P) c = .done vs c' →
        ∃ C s', R c C ∧ Execution.Core.Steps Pf host
            ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩ C ∧
          Execution.Core.Steps Pf host C ⟨s', C.frame, stackA vs⟩ ∧
          HoldsProg s' C.frame.module (asyncifyProg P) ∧ GlobalsAre s' C.frame c'.globals ∧
          MemAre s' C.frame c'.mem cap := by
  obtain ⟨R, hinit, hnext, hdone, -⟩ := machine_core_ginv (H := H) Pf host P hP cap
  refine ⟨R, fun e fd args s mi gs mem c c' vs hH he hfd ha hg hm hG hs hd => ?_⟩
  obtain ⟨C, hC, hR⟩ := bsteps_core hnext hs (hinit e fd args s mi gs mem hH he hfd ha hg hm hG)
  obtain ⟨s', h1, h2, h3, h4⟩ := hdone _ _ _ _ hR hd
  exact ⟨C, s', hR, hC, h1, h2, h3, h4⟩

/-- **A trap of the bounded machine in an export call is a trap of the Core 3.0 call.** -/
theorem call_trap_core' (Pf : Profile) (host : HostSemantics H) (P : Prog) (hP : P.WF)
    (cap : Nat) (e : Nat) (fd : FnDef) (args : List W) (s : Store H) (mi : ModuleInst)
    (gs : List W) (mem : Nat → W) (c : Cfg) (hH : HoldsProg s mi (asyncifyProg P))
    (he : P.imps.length ≤ e) (hfd : (asyncifyProg P).fns[e - P.imps.length]? = some fd)
    (ha : args.length = fd.nparams) (hg : GlobalsAre s ⟨[], mi⟩ gs)
    (hm : MemAre s ⟨[], mi⟩ mem cap) (hG : GInv gs)
    (hs : BSteps cap (asyncifyProg P) ⟨[entry e fd args], gs, mem⟩ c)
    (ht' : stepB cap (asyncifyProg P) c = .trap) :
    ∃ C', Execution.Core.Steps Pf host
        ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩ C' ∧
      C'.code = [.trap] := by
  obtain ⟨R, hinit, hnext, -, htrap⟩ := machine_core_ginv (H := H) Pf host P hP cap
  obtain ⟨C, hC, hR⟩ := bsteps_core hnext hs (hinit e fd args s mi gs mem hH he hfd ha hg hm hG)
  obtain ⟨C', h1, h2⟩ := htrap _ _ hR ht'
  exact ⟨C', hC.trans h1, h2⟩

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.machine_core_ginv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms machine_core_ginv

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.call_done_core'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms call_done_core'

end Silmaril.Wasm.FX.Asyncify.Tool
