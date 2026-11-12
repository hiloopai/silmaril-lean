module

public import Silmaril.Wasm.Auto.EquivLoop.Defs
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Mathlib.Order.WellFounded
import Silmaril.Proofs.Wasm.Auto.EquivLoop.X

/-!
# Loop equivalence: results

For the notions of `Silmaril.Wasm.Auto.Equiv.Defs` (proofs in
`Silmaril/Proofs/Wasm/Auto/EquivLoop/Total`):

* `acc_of_tsafe`: a totally safe configuration is accessible for the converse of the step
  relation (no infinite run; uses choice through Mathlib's
  `not_acc_iff_exists_descending_chain`);
* `tsafe_reach`, `tsafe_and_hwp`: totally safe runs reach their exits; total and partial facts
  combine;
* **`tsafe_loop_congr`**, **`CEquiv.loopT`**: the lockstep loop congruence for **total
  correctness**, by induction on the accessibility of the left loop's runs (the next iteration's
  loop configuration is reachable in at least one step), hence `CEquiv` (both readings) of two
  loops whose bodies are `CEquiv` and typed at their back edges (`KeepsBr0`).

**Loops under a state invariant** (`Silmaril.Wasm.Auto.EquivLoop.Defs`, proofs in
`Silmaril/Proofs/Wasm/Auto/EquivLoop/{Inv,X}`):

* `safe_loop_congrI`, `tsafe_loop_congrI`, **`LoopEquivI.of_body`**: the same congruence with the
  typed frame replaced by any invariant `I` of the store and frame that the bodies keep at their
  back edges (`KeepsBr0I`), both readings;
* `bodyEquivI_of_segEquivX`: the extended checker's `SegEquivX` (memory, globals, traps) is a
  body equivalence under `XInv`;
* `XCtx.rebase`, `rebase_ok`: the state after a type-preserving symbolic run is again a typed
  context; `keepsBr0I_of_check`: `do … while` bodies accepted by `brIfBodyOkX` keep `XInv`;
* **`loopEquivX`**: **loops with memory and globals**: `checkX`-equivalent `do … while` bodies give
  equivalent loops in every typed context.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivLoop

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.EquivLoop` -/

section
-- from Silmaril/Proofs/Wasm/Auto/EquivLoop/Inv.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivLoop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv

theorem BodyEquivI.symm {I : SInv} {a b : List Instr} (h : BodyEquivI I a b) : BodyEquivI I b a :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.BodyEquivI.symm (I := I) (a := a) (b := b) (h := h)

theorem KeepsBr0I.of_equiv {I : SInv} {a b : List Instr} (hk : KeepsBr0I I a)
    (h : BodyEquivI I a b) : KeepsBr0I I b :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.KeepsBr0I.of_equiv (I := I) (a := a) (b := b) (hk := hk) (h := h)

/-- **Löb induction for the loop congruence under an invariant.** -/
theorem safe_loop_congrI {H : Type} {P : Profile} {host : HostSemantics H} {I : SInv}
    {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : BodyEquivI I a b) (hk : KeepsBr0I I a) (n : Nat) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      I s f → NoFuncTop us → HWP P host s f (vals us ++ [.plain (.loop bt a)]) Q →
      Safe P host Q n ⟨s, f, vals us ++ [.plain (.loop bt b)]⟩ :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.safe_loop_congrI (H := H) (P := P) (host := host) (I := I)
    (a := a) (b := b) (bt := bt) (hbt := hbt) (h := h) (hk := hk) (n := n)

/-- **The loop congruence under an invariant, total correctness.** -/
theorem tsafe_loop_congrI {H : Type} {P : Profile} {host : HostSemantics H} {I : SInv}
    {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : BodyEquivI I a b) (hk : KeepsBr0I I a) (c : Config H)
    (hacc : Acc (Relation.TransGen (StepBack P host)) c) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      c = ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩ → I s f → NoFuncTop us →
      TSafe P host Q c → TSafe P host Q ⟨s, f, vals us ++ [.plain (.loop bt b)]⟩ :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.tsafe_loop_congrI (H := H) (P := P) (host := host) (I := I)
    (a := a) (b := b) (bt := bt) (hbt := hbt) (h := h) (hk := hk) (c := c) (hacc := hacc)

/-- **Loops under an invariant**: equivalent bodies that keep the invariant at their back edges
give equivalent loops, in both readings. -/
theorem LoopEquivI.of_body {I : SInv} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : BodyEquivI I a b) (hk : KeepsBr0I I a) : LoopEquivI I bt a b :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.LoopEquivI.of_body (I := I) (a := a) (b := b) (bt := bt)
    (hbt := hbt) (h := h) (hk := hk)

end

section
-- from Silmaril/Proofs/Wasm/Auto/EquivLoop/Total.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv Silmaril.Wasm.Auto.EquivLoop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

theorem acc_of_tsafe {H : Type} {P : Profile} {host : HostSemantics H} {Q : Post H} {c : Config H}
    (h : TSafe P host Q c) : Acc (StepBack P host) c :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.acc_of_tsafe (H := H) (P := P) (host := host) (Q := Q) (c := c)
    (h := h)

theorem tsafe_reach {H : Type} {P : Profile} {host : HostSemantics H} {Q : Post H} {c : Config H}
    (h : TSafe P host Q c) :
    ∀ c₀, Steps P host c₀ c →
      TSafe P host (fun s f o => Q s f o ∧ ∃ code, Exits o code ∧ Steps P host c₀ ⟨s, f, code⟩) c :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.tsafe_reach (H := H) (P := P) (host := host) (Q := Q) (c := c)
    (h := h)

theorem tsafe_and_hwp {H : Type} {P : Profile} {host : HostSemantics H} {Q Q' : Post H}
    {c : Config H} (h : TSafe P host Q c) :
    HWP P host c.store c.frame c.code Q' → TSafe P host (fun s f o => Q s f o ∧ Q' s f o) c :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.tsafe_and_hwp (H := H) (P := P) (host := host) (Q := Q)
    (Q' := Q') (c := c) (h := h)

theorem steps_label {H : Type} {P : Profile} {host : HostSemantics H} {n : Nat} {cont : List Instr}
    {us : List Val} {c c' : Config H}
    (hs : Steps P host c c') :
    Steps P host ⟨c.store, c.frame, vals us ++ [.label n cont c.code]⟩
      ⟨c'.store, c'.frame, vals us ++ [.label n cont c'.code]⟩ :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.steps_label (H := H) (P := P) (host := host) (n := n)
    (cont := cont) (us := us) (c := c) (c' := c') (hs := hs)

/-- **The loop congruence for total correctness**, by induction on the accessibility of the
left loop's runs. -/
theorem tsafe_loop_congr {H : Type} {P : Profile} {host : HostSemantics H} {lt : List IntType}
    {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) (c : Config H)
    (hacc : Acc (Relation.TransGen (StepBack P host)) c) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      c = ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩ → TypedFrame lt f → NoFuncTop us →
      TSafe P host Q c → TSafe P host Q ⟨s, f, vals us ++ [.plain (.loop bt b)]⟩ :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.tsafe_loop_congr (H := H) (P := P) (host := host) (lt := lt)
    (a := a) (b := b) (bt := bt) (hbt := hbt) (h := h) (hk := hk) (c := c) (hacc := hacc)

/-- **Loops in both readings** (no parameters): equivalent bodies, typed at their back edges,
give equivalent loops. -/
theorem _root_.Silmaril.Wasm.Auto.Equiv.CEquiv.loopT {lt st : List IntType} {a b : List Instr}
    {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) :
    CEquiv lt st [.loop bt a] [.loop bt b] :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.CEquiv.loopT (lt := lt) (st := st) (a := a) (b := b) (bt := bt)
    (hbt := hbt) (h := h) (hk := hk)

end

section
-- from Silmaril/Proofs/Wasm/Auto/EquivLoop/X.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivLoop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv (NoFuncTop wp_exit_post wp_step_inv)
open Silmaril.Wasm.Auto.Equiv (Env)
open Silmaril.Wasm.Auto.Equiv

/-- **`SegEquivX` is a body equivalence under `XInv`.** -/
theorem bodyEquivI_of_segEquivX {lt gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : SegEquivX lt [] gt mem a b) : BodyEquivI (XInv lt gt mem) a b :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.bodyEquivI_of_segEquivX (lt := lt) (gt := gt) (mem := mem)
    (a := a) (b := b) (h := h)

/-- **Rebasing**: the state after a symbolic run that keeps the types is a typed context. -/
theorem rebase_ok {H : Type} {lt gt : List IntType} {mem : Bool} {c : XCtx H}
    (hc : c.Ok lt [] gt mem)
    {A : XState} (hl : A.locals.map Prod.fst = lt) (hg : A.globs.map Prod.fst = gt) :
    (c.rebase mem A).Ok lt [] gt mem :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.rebase_ok (H := H) (lt := lt) (gt := gt) (mem := mem) (c := c)
    (hc := hc) (A := A) (hl := hl) (hg := hg)

/-- **`do … while` bodies keep `XInv` at their back edges.** -/
theorem keepsBr0I_of_check {lt gt : List IntType} {mem : Bool} {c : List Instr} (l : LabelIdx)
    (hok : brIfBodyOkX lt gt mem c = true) : KeepsBr0I (XInv lt gt mem) (c ++ [.brIf l]) :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.keepsBr0I_of_check (lt := lt) (gt := gt) (mem := mem) (c := c)
    (l := l) (hok := hok)

/-- **Loops with memory and globals**: two `do … while` loops whose straight-line bodies are
`checkX`-equivalent (memory `0` and the globals `gt` included) and whose first body passes
`brIfBodyOkX` are equivalent, in both readings, in every typed context. -/
theorem loopEquivX {lt gt : List IntType} {mem : Bool} {c d : List Instr} {bt : BlockType}
    (l : LabelIdx) (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : checkX lt [] gt mem c d = true) (hok : brIfBodyOkX lt gt mem c = true) :
    LoopEquivI (XInv lt gt mem) bt (c ++ [.brIf l]) (d ++ [.brIf l]) :=
  Silmaril.Proofs.Wasm.Auto.EquivLoop.loopEquivX (lt := lt) (gt := gt) (mem := mem) (c := c) (d := d)
    (bt := bt) (l := l) (hbt := hbt) (h := h) (hok := hok)

end

end Silmaril.Wasm.Auto.EquivLoop

