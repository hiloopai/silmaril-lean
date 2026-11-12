module

public import Silmaril.Wasm.FX.Asyncify.Tool.Bounded.Defs
public import Silmaril.Wasm.Execution.Core.Step

/-!
# The tool's frame machine against silmaril-lean's Core 3.0 `Step`

The frame machine (`Silmaril.Wasm.FX.Asyncify.Tool.Machine`) keeps machine words (`W`) in lists:
operands top first, locals in index order. A Core 3.0 configuration keeps values: operands as
value instructions, bottom first, and locals as `some v` in its frame. This module states the
correspondence for the straight-line part of the machine and the open target for the rest.

* `stackA ops`: the operand stack `ops` (top first) as Core value instructions (bottom first).
* `localsF f ls`: the Core frame `f` with locals `ls` (all `i32`, all set).
* `GlobalsAre s f gs`: global `g` of frame `f` holds `i32 gs[g]`, at pairwise distinct
  addresses.
* `MemAre s f mem cap`: memory 0 has `cap` bytes, whose aligned words are those of `mem`.
* `HoldsProg s mi E`: the store holds the defined functions of `E` in module instance `mi`.
* `Task.machine_core`: the open target (frozen, not proved) that the bounded machine
  (`stepB`, `Silmaril.Wasm.FX.Asyncify.Tool.Bounded`) runs the asyncified program of a well-formed
  source as Core 3.0 `Step` does, by a simulation from the Core call of a function.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-- The operand stack `ops` (top first) as Core value instructions (bottom first). -/
def stackA (ops : List W) : List Admin := vals (ops.reverse.map Val.i32)

/-- The Core frame `f` with the locals `ls`. -/
def localsF (f : Silmaril.Wasm.Execution.Core.Frame) (ls : List W) :
    Silmaril.Wasm.Execution.Core.Frame :=
  { f with locals := ls.map fun w => some (Val.i32 w) }

/-- A global index from a number. -/
def gidx (g : Nat) : GlobalIdx := ⟨Fin.ofNat _ g⟩

/-- The globals of frame `f` in store `s` hold `gs`, at pairwise distinct addresses. -/
def GlobalsAre {H : Type} (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (gs : List W) :
    Prop :=
  gs.length < 2 ^ 32 ∧
    (∀ g (h : g < gs.length), ∃ a gi, s.global? f (gidx g) = some (a, gi) ∧
      gi.value = Val.i32 gs[g] ∧ gi.type.mutability = .var) ∧
    (∀ g g' a a' gi gi', s.global? f (gidx g) = some (a, gi) →
      s.global? f (gidx g') = some (a', gi') → g < gs.length → g' < gs.length → a = a' → g = g')

/-- A function index from a number. -/
def fidx (f : Nat) : FuncIdx := ⟨Fin.ofNat _ f⟩

/-- Memory 0 of frame `f` has `cap` bytes, and every aligned word in it is the word of `mem`
there (little endian). -/
def MemAre {H : Type} (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (mem : Nat → W)
    (cap : Nat) : Prop :=
  ∃ ma mi, s.mem? f ⟨0⟩ = some (ma, mi) ∧ mi.bytes.size = cap ∧
    ∀ a, a % 4 = 0 → a + 4 ≤ cap → Silmaril.Wasm.Execution.Memory.load mi.bytes a 4 = some (mem a)

/-- The store holds the defined functions of `E` in module instance `mi`, at the function
indices after the imports. -/
def HoldsProg {H : Type} (s : Store H) (mi : ModuleInst) (E : Env) : Prop :=
  ∀ j fd, E.fns[j]? = some fd → ∃ a fi ty ps rs, mi.funcs[E.imps.length + j]? = some a ∧
    s.funcs[a]? = some fi ∧ fi.module = mi ∧
    fi.code = .wasm ⟨ty, List.replicate fd.nlocals .i32, fd.body⟩ ∧
    Expand fi.type (.func ps rs) ∧ ps.length = fd.nparams ∧ rs.length = fd.nres

/-- Silmaril.Wasm.Execution.Core.Steps of the bounded machine, each a `next`. -/
inductive BSteps (cap : Nat) (E : Env) : Cfg → Cfg → Prop where
  | refl (c : Cfg) : BSteps cap E c c
  | cons {c c₁ c₂ : Cfg} : stepB cap E c = .next c₁ → BSteps cap E c₁ c₂ → BSteps cap E c c₂

/-- **Open target** (frozen, not proved): the bounded frame machine runs the asyncified program
of a well-formed source as Core 3.0 does. There is a relation `R` between machine and Core
configurations such that

* (`init`) the entry frame of a defined function, with globals `gs` and memory `mem`, is related
  to the Core call of that function in a store that holds the program in module instance `mi`
  and holds `gs` and `mem` (aligned words of a `cap`-byte memory);
* (`next`) every machine step is matched by Core steps;
* (`done`) a return of the bottom frame is matched by Core steps to the returned values, in a
  store that holds the program and the machine's final globals and memory;
* (`trap`) a machine trap is matched by Core steps to a trap.

The straight-line instructions are proved in `Silmaril.Wasm.FX.Asyncify.Tool.Core.Thms`; what is
open is the rest: frames (`call`, `return`, falling off the end), `if` (a label in Core, an arm
spliced into the code by the machine), and the word memory against Core's bytes (true for
the asyncified program because all of its accesses are aligned words). -/
def Task.machine_core : Prop :=
  ∀ {H : Type} (Pf : Profile) (host : HostSemantics H) (P : Prog) (_ : P.WF) (cap : Nat),
    cap % 4 = 0 → P.sb + 4 * P.frameWords ≤ cap → cap < 2 ^ 32 →
    ∃ R : Cfg → Config H → Prop,
      (∀ (e : Nat) (fd : FnDef) (args : List W) (s : Store H) (mi : ModuleInst) (gs : List W)
          (mem : Nat → W), HoldsProg s mi (asyncifyProg P) → P.imps.length ≤ e →
          (asyncifyProg P).fns[e - P.imps.length]? = some fd → args.length = fd.nparams →
          GlobalsAre s ⟨[], mi⟩ gs → MemAre s ⟨[], mi⟩ mem cap →
          R ⟨[entry e fd args], gs, mem⟩
            ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩) ∧
      (∀ c C c', R c C → stepB cap (asyncifyProg P) c = .next c' →
          ∃ C', Execution.Core.Steps Pf host C C' ∧ R c' C') ∧
      (∀ c C vs c', R c C → stepB cap (asyncifyProg P) c = .done vs c' →
          ∃ s', Execution.Core.Steps Pf host C ⟨s', C.frame, stackA vs⟩ ∧
            HoldsProg s' C.frame.module (asyncifyProg P) ∧ GlobalsAre s' C.frame c'.globals ∧
            MemAre s' C.frame c'.mem cap) ∧
      (∀ c C, R c C → stepB cap (asyncifyProg P) c = .trap →
          ∃ C', Execution.Core.Steps Pf host C C' ∧ C'.code = [.trap])

end Silmaril.Wasm.FX.Asyncify.Tool
